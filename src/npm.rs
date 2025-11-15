// Copyright 2018-2025 the Deno authors. All rights reserved. MIT license.

use std::borrow::Cow;

use capacity_builder::CapacityDisplay;
use capacity_builder::StringAppendable;
use capacity_builder::StringType;
use deno_error::JsError;
use monch::*;
use thiserror::Error;

use serde::Deserialize;
use serde::Serialize;
use url::Url;

use crate::CowVec;
use crate::PackageTag;
use crate::common::logical_and;
use crate::common::logical_or;
use crate::common::primitive;
use crate::common::primitive_kind;
use crate::common::qualifier;
use crate::package::PackageKind;
use crate::package::PackageNv;
use crate::package::PackageNvReference;
use crate::package::PackageNvReferenceParseError;
use crate::package::PackageReq;
use crate::package::PackageReqReference;
use crate::package::PackageReqReferenceParseError;
use crate::range_set_or_tag::RangeOrInvalid;

use super::Partial;
use super::RangeSetOrTag;
use super::Version;
use super::VersionRange;
use super::VersionRangeSet;
use super::VersionReq;
use super::XRange;

pub fn is_valid_npm_tag(value: &str) -> bool {
  if value.trim().is_empty() {
    return false;
  }

  // a valid tag is anything that doesn't get url encoded
  // https://github.com/npm/npm-package-arg/blob/103c0fda8ed8185733919c7c6c73937cfb2baf3a/lib/npa.js#L399-L401
  value
    .chars()
    .all(|c| c.is_alphanumeric() || matches!(c, '-' | '_' | '.' | '~'))
}

// A lot of the below is a re-implementation of parts of https://github.com/npm/node-semver
// which is Copyright (c) Isaac Z. Schlueter and Contributors (ISC License)

#[derive(Error, Debug, Clone, JsError)]
#[class(type)]
#[error("Invalid npm version")]
pub struct NpmVersionParseError {
  #[source]
  pub(crate) source: ParseErrorFailureError,
}

impl NpmVersionParseError {
  /// Message of the error excluding the code snippet.
  pub fn message(&self) -> &str {
    &self.source.message
  }
}

pub fn parse_npm_version(text: &str) -> Result<Version, NpmVersionParseError> {
  let text = text.trim();
  with_failure_handling(|input| {
    let (input, _) = maybe(ch('='))(input)?; // skip leading =
    let (input, _) = skip_whitespace(input)?;
    let (input, _) = maybe(ch('v'))(input)?; // skip leading v
    let (input, _) = skip_whitespace(input)?;
    let (input, major) = nr(input)?;
    let (input, _) = ch('.')(input)?;
    let (input, minor) = nr(input)?;
    let (input, _) = ch('.')(input)?;
    let (input, patch) = nr(input)?;
    let (input, q) = maybe(qualifier)(input)?;
    let q = q.unwrap_or_default();

    Ok((
      input,
      Version {
        major,
        minor,
        patch,
        pre: q.pre,
        build: q.build,
      },
    ))
  })(text)
  .map_err(|err| NpmVersionParseError { source: err })
}

#[derive(Error, Debug, Clone, JsError, PartialEq, Eq)]
#[class(type)]
#[error("Invalid version requirement")]
pub struct NpmVersionReqParseError {
  #[source]
  pub source: ParseErrorFailureError,
}

pub fn parse_npm_version_req(
  text: &str,
) -> Result<VersionReq, NpmVersionReqParseError> {
  let text = text.trim();
  with_failure_handling(|input| {
    map(inner, |inner| {
      VersionReq::from_raw_text_and_inner(
        crate::SmallStackString::from_str(input),
        inner,
      )
    })(input)
  })(text)
  .map_err(|err| NpmVersionReqParseError { source: err })
}

// https://github.com/npm/node-semver/tree/4907647d169948a53156502867ed679268063a9f#range-grammar
// range-set  ::= range ( logical-or range ) *
// logical-or ::= ( ' ' ) * '||' ( ' ' ) *
// range      ::= hyphen | simple ( ' ' simple ) * | ''
// hyphen     ::= partial ' - ' partial
// simple     ::= primitive | partial | tilde | caret
// primitive  ::= ( '<' | '>' | '>=' | '<=' | '=' ) partial
// partial    ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
// xr         ::= 'x' | 'X' | '*' | nr
// nr         ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
// tilde      ::= '~' partial
// caret      ::= '^' partial
// qualifier  ::= ( '-' pre )? ( '+' build )?
// pre        ::= parts
// build      ::= parts
// parts      ::= part ( '.' part ) *
// part       ::= nr | [-0-9A-Za-z]+

// range-set ::= range ( logical-or range ) *
fn inner(input: &str) -> ParseResult<'_, RangeSetOrTag> {
  if input.is_empty() {
    return Ok((
      input,
      RangeSetOrTag::RangeSet(VersionRangeSet(CowVec::from([
        VersionRange::all(),
      ]))),
    ));
  }

  let (input, mut ranges) = separated_list(
    |text| RangeOrInvalid::parse(text, range),
    logical_or,
  )(input)?;

  if ranges.len() == 1 {
    match ranges.remove(0) {
      RangeOrInvalid::Invalid(invalid) => {
        if is_valid_npm_tag(invalid.text) {
          return Ok((
            input,
            RangeSetOrTag::Tag(PackageTag::from_str(invalid.text)),
          ));
        } else {
          return Err(invalid.failure);
        }
      }
      RangeOrInvalid::Range(range) => {
        // add it back
        ranges.push(RangeOrInvalid::Range(range));
      }
    }
  }

  let ranges = ranges
    .into_iter()
    .filter_map(|r| r.into_range().ok().flatten())
    .collect::<CowVec<_>>();
  Ok((input, RangeSetOrTag::RangeSet(VersionRangeSet(ranges))))
}

// range ::= hyphen | simple ( ' ' simple ) * | ''
fn range(input: &str) -> ParseResult<'_, VersionRange> {
  or(
    map(hyphen, |hyphen| VersionRange {
      start: hyphen.start.as_lower_bound(),
      end: hyphen.end.as_upper_bound(),
    }),
    map(separated_list(simple, range_separator), |ranges| {
      let mut final_range = VersionRange::all();
      for range in ranges {
        final_range = final_range.clamp(&range);
      }
      final_range
    }),
  )(input)
}

fn range_separator(input: &str) -> ParseResult<'_, ()> {
  fn comma(input: &str) -> ParseResult<'_, ()> {
    map(delimited(skip_whitespace, ch(','), skip_whitespace), |_| ())(input)
  }

  or3(map(logical_and, |_| ()), comma, map(whitespace, |_| ()))(input)
}

#[derive(Debug, Clone)]
struct Hyphen {
  start: Partial,
  end: Partial,
}

// hyphen ::= partial ' - ' partial
fn hyphen(input: &str) -> ParseResult<'_, Hyphen> {
  let (input, first) = partial(input)?;
  let (input, _) = whitespace(input)?;
  let (input, _) = tag("-")(input)?;
  let (input, _) = whitespace(input)?;
  let (input, second) = partial(input)?;
  Ok((
    input,
    Hyphen {
      start: first,
      end: second,
    },
  ))
}

fn skip_whitespace_or_v(input: &str) -> ParseResult<'_, ()> {
  map(
    pair(skip_whitespace, pair(maybe(ch('v')), skip_whitespace)),
    |_| (),
  )(input)
}

// simple ::= primitive | partial | tilde | caret
fn simple(input: &str) -> ParseResult<'_, VersionRange> {
  or4(
    map(preceded(tilde, partial), |partial| {
      partial.as_tilde_version_range()
    }),
    map(preceded(caret, partial), |partial| {
      partial.as_caret_version_range()
    }),
    map(primitive(partial), |primitive| {
      primitive.into_version_range()
    }),
    map(partial, |partial| partial.as_equal_range()),
  )(input)
}

fn tilde(input: &str) -> ParseResult<'_, ()> {
  fn raw_tilde(input: &str) -> ParseResult<'_, ()> {
    map(
      pair(
        terminated(or(tag("~>"), tag("~")), skip_while(|c| c == '=')),
        skip_whitespace_or_v,
      ),
      |_| (),
    )(input)
  }

  or(
    preceded(terminated(primitive_kind, whitespace), raw_tilde),
    raw_tilde,
  )(input)
}

fn caret(input: &str) -> ParseResult<'_, ()> {
  fn raw_caret(input: &str) -> ParseResult<'_, ()> {
    map(
      pair(
        terminated(tag("^"), skip_while(|c| c == '=')),
        skip_whitespace_or_v,
      ),
      |_| (),
    )(input)
  }

  or(
    preceded(terminated(primitive_kind, whitespace), raw_caret),
    raw_caret,
  )(input)
}

// partial ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
fn partial(input: &str) -> ParseResult<'_, Partial> {
  let (input, _) = maybe(ch('v'))(input)?; // skip leading v
  crate::common::partial(xr)(input)
}

// xr ::= 'x' | 'X' | '*' | nr
fn xr(input: &str) -> ParseResult<'_, XRange> {
  or(
    map(or3(tag("x"), tag("X"), tag("*")), |_| XRange::Wildcard),
    map(nr, XRange::Val),
  )(input)
}

// nr ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
fn nr(input: &str) -> ParseResult<'_, u64> {
  // we do loose parsing to support people doing stuff like 01.02.03
  let (input, result) =
    if_not_empty(substring(skip_while(|c| c.is_ascii_digit())))(input)?;
  let val = match result.parse::<u64>() {
    Ok(val) => val,
    Err(err) => {
      return ParseError::fail(
        input,
        format!("Error parsing '{result}' to u64.\n\n{err:#}"),
      );
    }
  };
  Ok((input, val))
}

/// A reference to an npm package's name, version constraint, and potential sub path.
/// This contains all the information found in an npm specifier.
///
/// This wraps PackageReqReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, CapacityDisplay)]
pub struct NpmPackageReqReference(PackageReqReference);

impl<'a> StringAppendable<'a> for &'a NpmPackageReqReference {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut capacity_builder::StringBuilder<'a, TString>,
  ) {
    builder.append("npm:");
    builder.append(&self.0);
  }
}

impl NpmPackageReqReference {
  pub fn new(inner: PackageReqReference) -> Self {
    Self(inner)
  }

  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, PackageReqReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(
    specifier: &str,
  ) -> Result<Self, PackageReqReferenceParseError> {
    PackageReqReference::from_str(specifier, PackageKind::Npm).map(Self)
  }

  pub fn req(&self) -> &PackageReq {
    &self.0.req
  }

  pub fn sub_path(&self) -> Option<&str> {
    self.0.sub_path.as_deref()
  }

  pub fn into_inner(self) -> PackageReqReference {
    self.0
  }
}

/// An npm package name and version with a potential subpath.
///
/// This wraps PackageNvReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(
  Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, CapacityDisplay,
)]
pub struct NpmPackageNvReference(PackageNvReference);

impl NpmPackageNvReference {
  pub fn new(inner: PackageNvReference) -> Self {
    Self(inner)
  }

  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, PackageNvReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(nv: &str) -> Result<Self, PackageNvReferenceParseError> {
    PackageNvReference::from_str(nv, PackageKind::Npm).map(Self)
  }

  pub fn as_specifier(&self) -> Url {
    self.0.as_specifier(PackageKind::Npm)
  }

  pub fn nv(&self) -> &PackageNv {
    &self.0.nv
  }

  pub fn sub_path(&self) -> Option<&str> {
    self.0.sub_path.as_deref()
  }

  pub fn into_inner(self) -> PackageNvReference {
    self.0
  }
}

impl<'a> StringAppendable<'a> for &'a NpmPackageNvReference {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut capacity_builder::StringBuilder<'a, TString>,
  ) {
    builder.append("npm:");
    builder.append(&self.0);
  }
}

impl Serialize for NpmPackageNvReference {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for NpmPackageNvReference {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let text: Cow<'de, str> = Deserialize::deserialize(deserializer)?;
    match Self::from_str(&text) {
      Ok(req) => Ok(req),
      Err(err) => Err(serde::de::Error::custom(err)),
    }
  }
}

#[cfg(test)]
mod tests {
  use pretty_assertions::assert_eq;
  use std::cmp::Ordering;

  use crate::WILDCARD_VERSION_REQ;

  use super::*;

  struct NpmVersionReqTester(VersionReq);

  impl NpmVersionReqTester {
    fn new(text: &str) -> Self {
      Self(parse_npm_version_req(text).unwrap())
    }

    fn matches(&self, version: &str) -> bool {
      self.0.matches(&parse_npm_version(version).unwrap())
    }
  }

  #[test]
  pub fn npm_version_req_with_v() {
    assert!(parse_npm_version_req("v1.0.0").is_ok());
  }

  #[test]
  pub fn npm_version_req_exact() {
    let tester = NpmVersionReqTester::new("2.1.2");
    assert!(!tester.matches("2.1.1"));
    assert!(tester.matches("2.1.2"));
    assert!(!tester.matches("2.1.3"));

    let tester = NpmVersionReqTester::new("2.1.2 || 2.1.5");
    assert!(!tester.matches("2.1.1"));
    assert!(tester.matches("2.1.2"));
    assert!(!tester.matches("2.1.3"));
    assert!(!tester.matches("2.1.4"));
    assert!(tester.matches("2.1.5"));
    assert!(!tester.matches("2.1.6"));
  }

  #[test]
  pub fn npm_version_req_minor() {
    let tester = NpmVersionReqTester::new("1.1");
    assert!(!tester.matches("1.0.0"));
    assert!(tester.matches("1.1.0"));
    assert!(tester.matches("1.1.1"));
    assert!(!tester.matches("1.2.0"));
    assert!(!tester.matches("1.2.1"));
  }

  #[test]
  pub fn npm_version_req_ranges() {
    let tester = NpmVersionReqTester::new(
      ">= 2.1.2 < 3.0.0 || 5.x || ignored-invalid-range || $#$%^#$^#$^%@#$%SDF|||",
    );
    assert!(!tester.matches("2.1.1"));
    assert!(tester.matches("2.1.2"));
    assert!(tester.matches("2.9.9"));
    assert!(!tester.matches("3.0.0"));
    assert!(tester.matches("5.0.0"));
    assert!(tester.matches("5.1.0"));
    assert!(!tester.matches("6.1.0"));
  }

  #[test]
  pub fn npm_version_req_and_range() {
    let tester = NpmVersionReqTester::new(">= 1.2 && <= 2.0.0");
    assert!(!tester.matches("1.1.9"));
    assert!(tester.matches("1.2.2"));
    assert!(tester.matches("1.2.0"));
    assert!(tester.matches("1.9.9"));
    assert!(!tester.matches("2.1.1"));
    assert!(!tester.matches("2.0.1"));
  }

  #[test]
  pub fn npm_version_req_comma_range() {
    let tester = NpmVersionReqTester::new(">= 1.2, <= 2.0.0");
    assert!(!tester.matches("1.1.9"));
    assert!(tester.matches("1.2.2"));
    assert!(tester.matches("1.2.0"));
    assert!(tester.matches("1.9.9"));
    assert!(!tester.matches("2.1.1"));
    assert!(!tester.matches("2.0.1"));
  }

  #[test]
  pub fn npm_version_req_with_tag() {
    let req = parse_npm_version_req("latest").unwrap();
    assert_eq!(req.tag(), Some("latest"));
  }

  #[test]
  pub fn npm_version_req_prerelease() {
    let tester = NpmVersionReqTester::new("^1.0.0-beta-7");
    assert!(tester.matches("1.0.0-beta-7"));
    let tester = NpmVersionReqTester::new("^0.0.1-beta-7");
    assert!(tester.matches("0.0.1-beta-7"));
  }

  #[test]
  pub fn npm_version_req_0_version() {
    let tester = NpmVersionReqTester::new("^0.0.0-beta-7");
    assert!(tester.matches("0.0.0-beta-7"));
  }

  macro_rules! assert_cmp {
    ($a:expr, $b:expr, $expected:expr) => {
      assert_eq!(
        $a.cmp(&$b),
        $expected,
        "expected {} to be {:?} {}",
        $a,
        $expected,
        $b
      );
    };
  }

  macro_rules! test_compare {
    ($a:expr, $b:expr, $expected:expr) => {
      let a = parse_npm_version($a).unwrap();
      let b = parse_npm_version($b).unwrap();
      assert_cmp!(a, b, $expected);
    };
  }

  #[test]
  fn version_compare() {
    test_compare!("1.2.3", "2.3.4", Ordering::Less);
    test_compare!("1.2.3", "1.2.4", Ordering::Less);
    test_compare!("1.2.3", "1.2.3", Ordering::Equal);
    test_compare!("1.2.3", "1.2.2", Ordering::Greater);
    test_compare!("1.2.3", "1.1.5", Ordering::Greater);
  }

  #[test]
  fn version_compare_equal() {
    // https://github.com/npm/node-semver/blob/bce42589d33e1a99454530a8fd52c7178e2b11c1/test/fixtures/equality.js
    let fixtures = &[
      ("1.2.3", "v1.2.3"),
      ("1.2.3", "=1.2.3"),
      ("1.2.3", "v 1.2.3"),
      ("1.2.3", "= 1.2.3"),
      ("1.2.3", " v1.2.3"),
      ("1.2.3", " =1.2.3"),
      ("1.2.3", " v 1.2.3"),
      ("1.2.3", " = 1.2.3"),
      ("1.2.3-0", "v1.2.3-0"),
      ("1.2.3-0", "=1.2.3-0"),
      ("1.2.3-0", "v 1.2.3-0"),
      ("1.2.3-0", "= 1.2.3-0"),
      ("1.2.3-0", " v1.2.3-0"),
      ("1.2.3-0", " =1.2.3-0"),
      ("1.2.3-0", " v 1.2.3-0"),
      ("1.2.3-0", " = 1.2.3-0"),
      ("1.2.3-1", "v1.2.3-1"),
      ("1.2.3-1", "=1.2.3-1"),
      ("1.2.3-1", "v 1.2.3-1"),
      ("1.2.3-1", "= 1.2.3-1"),
      ("1.2.3-1", " v1.2.3-1"),
      ("1.2.3-1", " =1.2.3-1"),
      ("1.2.3-1", " v 1.2.3-1"),
      ("1.2.3-1", " = 1.2.3-1"),
      ("1.2.3-beta", "v1.2.3-beta"),
      ("1.2.3-beta", "=1.2.3-beta"),
      ("1.2.3-beta", "v 1.2.3-beta"),
      ("1.2.3-beta", "= 1.2.3-beta"),
      ("1.2.3-beta", " v1.2.3-beta"),
      ("1.2.3-beta", " =1.2.3-beta"),
      ("1.2.3-beta", " v 1.2.3-beta"),
      ("1.2.3-beta", " = 1.2.3-beta"),
      ("1.2.3-beta+build", " = 1.2.3-beta+otherbuild"),
      ("1.2.3+build", " = 1.2.3+otherbuild"),
      ("1.2.3-beta+build", "1.2.3-beta+otherbuild"),
      ("1.2.3+build", "1.2.3+otherbuild"),
      ("  v1.2.3+build", "1.2.3+otherbuild"),
    ];
    for (a, b) in fixtures {
      test_compare!(a, b, Ordering::Equal);
    }
  }

  #[test]
  fn version_comparisons_test() {
    // https://github.com/npm/node-semver/blob/bce42589d33e1a99454530a8fd52c7178e2b11c1/test/fixtures/comparisons.js
    let fixtures = &[
      ("0.0.0", "0.0.0-foo"),
      ("0.0.1", "0.0.0"),
      ("1.0.0", "0.9.9"),
      ("0.10.0", "0.9.0"),
      ("0.99.0", "0.10.0"),
      ("2.0.0", "1.2.3"),
      ("v0.0.0", "0.0.0-foo"),
      ("v0.0.1", "0.0.0"),
      ("v1.0.0", "0.9.9"),
      ("v0.10.0", "0.9.0"),
      ("v0.99.0", "0.10.0"),
      ("v2.0.0", "1.2.3"),
      ("0.0.0", "v0.0.0-foo"),
      ("0.0.1", "v0.0.0"),
      ("1.0.0", "v0.9.9"),
      ("0.10.0", "v0.9.0"),
      ("0.99.0", "v0.10.0"),
      ("2.0.0", "v1.2.3"),
      ("1.2.3", "1.2.3-asdf"),
      ("1.2.3", "1.2.3-4"),
      ("1.2.3", "1.2.3-4-foo"),
      ("1.2.3-5-foo", "1.2.3-5"),
      ("1.2.3-5", "1.2.3-4"),
      ("1.2.3-5-foo", "1.2.3-5-Foo"),
      ("3.0.0", "2.7.2+asdf"),
      ("1.2.3-a.10", "1.2.3-a.5"),
      ("1.2.3-a.b", "1.2.3-a.5"),
      ("1.2.3-a.b", "1.2.3-a"),
      ("1.2.3-a.b.c.10.d.5", "1.2.3-a.b.c.5.d.100"),
      ("1.2.3-r2", "1.2.3-r100"),
      ("1.2.3-r100", "1.2.3-R2"),
    ];
    for (a, b) in fixtures {
      let a = parse_npm_version(a).unwrap();
      let b = parse_npm_version(b).unwrap();
      assert_cmp!(a, b, Ordering::Greater);
      assert_cmp!(b, a, Ordering::Less);
      assert_cmp!(a, a, Ordering::Equal);
      assert_cmp!(b, b, Ordering::Equal);
    }
  }

  #[test]
  fn range_parse() {
    // https://github.com/npm/node-semver/blob/4907647d169948a53156502867ed679268063a9f/test/fixtures/range-parse.js
    let fixtures = &[
      // note: some of these tests previously used a `-0` pre-release (see link),
      // but I removed them because it didn't seem relevant
      ("1.0.0 - 2.0.0", ">=1.0.0 <=2.0.0"),
      ("1 - 2", ">=1.0.0 <3.0.0"),
      ("1.0 - 2.0", ">=1.0.0 <2.1.0"),
      ("1.0.0", "1.0.0"),
      (">=*", "*"),
      ("", "*"),
      ("*", "*"),
      ("*", "*"),
      (">=1.0.0", ">=1.0.0"),
      (">1.0.0", ">1.0.0"),
      ("<=2.0.0", "<=2.0.0"),
      ("1", ">=1.0.0 <2.0.0"),
      ("<=2.0.0", "<=2.0.0"),
      ("<=2.0.0", "<=2.0.0"),
      ("<2.0.0", "<2.0.0"),
      ("<2.0.0", "<2.0.0"),
      (">= 1.0.0", ">=1.0.0"),
      (">=  1.0.0", ">=1.0.0"),
      (">=   1.0.0", ">=1.0.0"),
      ("> 1.0.0", ">1.0.0"),
      (">  1.0.0", ">1.0.0"),
      ("<=   2.0.0", "<=2.0.0"),
      ("<= 2.0.0", "<=2.0.0"),
      ("<=  2.0.0", "<=2.0.0"),
      ("<    2.0.0", "<2.0.0"),
      ("<\t2.0.0", "<2.0.0"),
      (">=0.1.97", ">=0.1.97"),
      (">=0.1.97", ">=0.1.97"),
      ("0.1.20 || 1.2.4", "0.1.20||1.2.4"),
      (">=0.2.3 || <0.0.1", ">=0.2.3||<0.0.1"),
      (">=0.2.3 || <0.0.1", ">=0.2.3||<0.0.1"),
      (">=0.2.3 || <0.0.1", ">=0.2.3||<0.0.1"),
      ("||", "*"),
      ("2.x.x", ">=2.0.0 <3.0.0"),
      ("1.2.x", ">=1.2.0 <1.3.0"),
      ("1.2.x || 2.x", ">=1.2.0 <1.3.0||>=2.0.0 <3.0.0"),
      ("1.2.x || 2.x", ">=1.2.0 <1.3.0||>=2.0.0 <3.0.0"),
      ("x", "*"),
      ("2.*.*", ">=2.0.0 <3.0.0"),
      ("1.2.*", ">=1.2.0 <1.3.0"),
      ("1.2.* || 2.*", ">=1.2.0 <1.3.0||>=2.0.0 <3.0.0"),
      ("*", "*"),
      ("2", ">=2.0.0 <3.0.0"),
      ("2.3", ">=2.3.0 <2.4.0"),
      ("~2.4", ">=2.4.0 <2.5.0"),
      ("~2.4", ">=2.4.0 <2.5.0"),
      ("~>3.2.1", ">=3.2.1 <3.3.0"),
      ("~1", ">=1.0.0 <2.0.0"),
      ("~>1", ">=1.0.0 <2.0.0"),
      ("~> 1", ">=1.0.0 <2.0.0"),
      ("~>=1", ">=1.0.0 <2.0.0"),
      ("~>==1", ">=1.0.0 <2.0.0"),
      ("~1.0", ">=1.0.0 <1.1.0"),
      ("~ 1.0", ">=1.0.0 <1.1.0"),
      ("~=1.0", ">=1.0.0 <1.1.0"),
      ("~==1.0", ">=1.0.0 <1.1.0"),
      ("^0", "<1.0.0"),
      ("^ 1", ">=1.0.0 <2.0.0"),
      ("^0.1", ">=0.1.0 <0.2.0"),
      ("^1.0", ">=1.0.0 <2.0.0"),
      ("^1.2", ">=1.2.0 <2.0.0"),
      ("^0.0.1", ">=0.0.1 <0.0.2"),
      ("^0.0.1-beta", ">=0.0.1-beta <0.0.2"),
      ("^0.1.2", ">=0.1.2 <0.2.0"),
      ("^1.2.3", ">=1.2.3 <2.0.0"),
      ("^1.2.3-beta.4", ">=1.2.3-beta.4 <2.0.0"),
      ("^=1.0.0", ">=1.0.0 <2.0.0"),
      ("^==1.0.0", ">=1.0.0 <2.0.0"),
      ("<1", "<1.0.0"),
      ("< 1", "<1.0.0"),
      (">=1", ">=1.0.0"),
      (">= 1", ">=1.0.0"),
      ("<1.2", "<1.2.0"),
      ("< 1.2", "<1.2.0"),
      ("1", ">=1.0.0 <2.0.0"),
      ("^ 1.2 ^ 1", ">=1.2.0 <2.0.0 >=1.0.0"),
      ("1.2 - 3.4.5", ">=1.2.0 <=3.4.5"),
      ("1.2.3 - 3.4", ">=1.2.3 <3.5.0"),
      ("1.2 - 3.4", ">=1.2.0 <3.5.0"),
      (">1", ">=2.0.0"),
      (">1.2", ">=1.3.0"),
      (">X", "<0.0.0"),
      ("<X", "<0.0.0"),
      ("<x <* || >* 2.x", "<0.0.0"),
      (">x 2.x || * || <x", "*"),
      (">01.02.03", ">1.2.3"),
      ("~1.2.3beta", ">=1.2.3-beta <1.3.0"),
      (">=09090", ">=9090.0.0"),
    ];
    for (range_text, expected) in fixtures {
      let range = parse_npm_version_req(range_text).unwrap();
      let expected_range = parse_npm_version_req(expected).unwrap();
      assert_eq!(
        range.inner(),
        expected_range.inner(),
        "failed for {} and {}",
        range_text,
        expected
      );
    }
  }

  #[test]
  fn range_satisfies() {
    // https://github.com/npm/node-semver/blob/4907647d169948a53156502867ed679268063a9f/test/fixtures/range-include.js
    let fixtures = &[
      ("1.0.0 - 2.0.0", "1.2.3"),
      ("^1.2.3+build", "1.2.3"),
      ("^1.2.3+build", "1.3.0"),
      ("1.2.3-pre+asdf - 2.4.3-pre+asdf", "1.2.3"),
      ("1.2.3pre+asdf - 2.4.3-pre+asdf", "1.2.3"),
      ("1.2.3-pre+asdf - 2.4.3pre+asdf", "1.2.3"),
      ("1.2.3pre+asdf - 2.4.3pre+asdf", "1.2.3"),
      ("1.2.3-pre+asdf - 2.4.3-pre+asdf", "1.2.3-pre.2"),
      ("1.2.3-pre+asdf - 2.4.3-pre+asdf", "2.4.3-alpha"),
      ("1.2.3+asdf - 2.4.3+asdf", "1.2.3"),
      ("1.0.0", "1.0.0"),
      (">=*", "0.2.4"),
      ("", "1.0.0"),
      ("*", "1.2.3"),
      ("*", "v1.2.3"),
      (">=1.0.0", "1.0.0"),
      (">=1.0.0", "1.0.1"),
      (">=1.0.0", "1.1.0"),
      (">1.0.0", "1.0.1"),
      (">1.0.0", "1.1.0"),
      ("<=2.0.0", "2.0.0"),
      ("<=2.0.0", "1.9999.9999"),
      ("<=2.0.0", "0.2.9"),
      ("<2.0.0", "1.9999.9999"),
      ("<2.0.0", "0.2.9"),
      (">= 1.0.0", "1.0.0"),
      (">=  1.0.0", "1.0.1"),
      (">=   1.0.0", "1.1.0"),
      ("> 1.0.0", "1.0.1"),
      (">  1.0.0", "1.1.0"),
      ("<=   2.0.0", "2.0.0"),
      ("<= 2.0.0", "1.9999.9999"),
      ("<=  2.0.0", "0.2.9"),
      ("<    2.0.0", "1.9999.9999"),
      ("<\t2.0.0", "0.2.9"),
      (">=0.1.97", "v0.1.97"),
      (">=0.1.97", "0.1.97"),
      ("0.1.20 || 1.2.4", "1.2.4"),
      (">=0.2.3 || <0.0.1", "0.0.0"),
      (">=0.2.3 || <0.0.1", "0.2.3"),
      (">=0.2.3 || <0.0.1", "0.2.4"),
      ("||", "1.3.4"),
      ("2.x.x", "2.1.3"),
      ("1.2.x", "1.2.3"),
      ("1.2.x || 2.x", "2.1.3"),
      ("1.2.x || 2.x", "1.2.3"),
      ("x", "1.2.3"),
      ("2.*.*", "2.1.3"),
      ("1.2.*", "1.2.3"),
      ("1.2.* || 2.*", "2.1.3"),
      ("1.2.* || 2.*", "1.2.3"),
      ("*", "1.2.3"),
      ("2", "2.1.2"),
      ("2.3", "2.3.1"),
      ("~0.0.1", "0.0.1"),
      ("~0.0.1", "0.0.2"),
      ("~x", "0.0.9"),   // >=2.4.0 <2.5.0
      ("~2", "2.0.9"),   // >=2.4.0 <2.5.0
      ("~2.4", "2.4.0"), // >=2.4.0 <2.5.0
      ("~2.4", "2.4.5"),
      ("~>3.2.1", "3.2.2"), // >=3.2.1 <3.3.0,
      ("~1", "1.2.3"),      // >=1.0.0 <2.0.0
      ("~>1", "1.2.3"),
      ("~> 1", "1.2.3"),
      ("~1.0", "1.0.2"), // >=1.0.0 <1.1.0,
      ("~ 1.0", "1.0.2"),
      ("~ 1.0.3", "1.0.12"),
      ("~ 1.0.3alpha", "1.0.12"),
      (">=1", "1.0.0"),
      (">= 1", "1.0.0"),
      ("<1.2", "1.1.1"),
      ("< 1.2", "1.1.1"),
      ("~v0.5.4-pre", "0.5.5"),
      ("~v0.5.4-pre", "0.5.4"),
      ("=0.7.x", "0.7.2"),
      ("<=0.7.x", "0.7.2"),
      (">=0.7.x", "0.7.2"),
      ("<=0.7.x", "0.6.2"),
      ("~1.2.1 >=1.2.3", "1.2.3"),
      ("~1.2.1 =1.2.3", "1.2.3"),
      ("~1.2.1 1.2.3", "1.2.3"),
      ("~1.2.1 >=1.2.3 1.2.3", "1.2.3"),
      ("~1.2.1 1.2.3 >=1.2.3", "1.2.3"),
      ("~1.2.1 1.2.3", "1.2.3"),
      (">=1.2.1 1.2.3", "1.2.3"),
      ("1.2.3 >=1.2.1", "1.2.3"),
      (">=1.2.3 >=1.2.1", "1.2.3"),
      (">=1.2.1 >=1.2.3", "1.2.3"),
      (">=1.2", "1.2.8"),
      ("^1.2.3", "1.8.1"),
      ("^0.1.2", "0.1.2"),
      ("^0.1", "0.1.2"),
      ("^0.0.1", "0.0.1"),
      ("^1.2", "1.4.2"),
      ("^1.2 ^1", "1.4.2"),
      ("^1.2.3-alpha", "1.2.3-pre"),
      ("^1.2.0-alpha", "1.2.0-pre"),
      ("^0.0.1-alpha", "0.0.1-beta"),
      ("^0.0.1-alpha", "0.0.1"),
      ("^0.1.1-alpha", "0.1.1-beta"),
      ("^x", "1.2.3"),
      ("x - 1.0.0", "0.9.7"),
      ("x - 1.x", "0.9.7"),
      ("1.0.0 - x", "1.9.7"),
      ("1.x - x", "1.9.7"),
      ("<=7.x", "7.9.9"),
      // additional tests
      ("1.0.0-alpha.13", "1.0.0-alpha.13"),
      (">1.0.0-beta.1 <=1.1.0", "1.0.0"),
      (">1.0.0-beta.1 <=1.1.0", "1.0.0-beta.2"),
      (">1.0.0-beta.1 <=1.1.0", "1.1.0"),
      ("1 - 2.0.0-beta.2", "2.0.0-beta.1"),
    ];
    for (req_text, version_text) in fixtures {
      let req = parse_npm_version_req(req_text).unwrap();
      let version = parse_npm_version(version_text).unwrap();
      assert!(
        req.matches(&version),
        "Checking {version_text} satisfies {req_text}"
      );
    }
  }

  #[test]
  fn range_not_satisfies() {
    let fixtures = &[
      ("1.0.0 - 2.0.0", "2.2.3"),
      ("1.2.3+asdf - 2.4.3+asdf", "1.2.3-pre.2"),
      ("1.2.3+asdf - 2.4.3+asdf", "2.4.3-alpha"),
      ("^1.2.3+build", "2.0.0"),
      ("^1.2.3+build", "1.2.0"),
      ("^1.2.3", "1.2.3-pre"),
      ("^1.2", "1.2.0-pre"),
      (">1.2", "1.3.0-beta"),
      ("<=1.2.3", "1.2.3-beta"),
      ("^1.2.3", "1.2.3-beta"),
      ("=0.7.x", "0.7.0-asdf"),
      (">=0.7.x", "0.7.0-asdf"),
      ("<=0.7.x", "0.7.0-asdf"),
      ("1", "1.0.0beta"),
      ("<1", "1.0.0beta"),
      ("< 1", "1.0.0beta"),
      ("1.0.0", "1.0.1"),
      (">=1.0.0", "0.0.0"),
      (">=1.0.0", "0.0.1"),
      (">=1.0.0", "0.1.0"),
      (">1.0.0", "0.0.1"),
      (">1.0.0", "0.1.0"),
      ("<=2.0.0", "3.0.0"),
      ("<=2.0.0", "2.9999.9999"),
      ("<=2.0.0", "2.2.9"),
      ("<2.0.0", "2.9999.9999"),
      ("<2.0.0", "2.2.9"),
      (">=0.1.97", "v0.1.93"),
      (">=0.1.97", "0.1.93"),
      ("0.1.20 || 1.2.4", "1.2.3"),
      (">=0.2.3 || <0.0.1", "0.0.3"),
      (">=0.2.3 || <0.0.1", "0.2.2"),
      ("2.x.x", "1.1.3"),
      ("2.x.x", "3.1.3"),
      ("1.2.x", "1.3.3"),
      ("1.2.x || 2.x", "3.1.3"),
      ("1.2.x || 2.x", "1.1.3"),
      ("2.*.*", "1.1.3"),
      ("2.*.*", "3.1.3"),
      ("1.2.*", "1.3.3"),
      ("1.2.* || 2.*", "3.1.3"),
      ("1.2.* || 2.*", "1.1.3"),
      ("2", "1.1.2"),
      ("2.3", "2.4.1"),
      ("~0.0.1", "0.1.0-alpha"),
      ("~0.0.1", "0.1.0"),
      ("~2.4", "2.5.0"), // >=2.4.0 <2.5.0
      ("~2.4", "2.3.9"),
      ("~>3.2.1", "3.3.2"), // >=3.2.1 <3.3.0
      ("~>3.2.1", "3.2.0"), // >=3.2.1 <3.3.0
      ("~1", "0.2.3"),      // >=1.0.0 <2.0.0
      ("~>1", "2.2.3"),
      ("~1.0", "1.1.0"), // >=1.0.0 <1.1.0
      ("<1", "1.0.0"),
      (">=1.2", "1.1.1"),
      ("1", "2.0.0beta"),
      ("~v0.5.4-beta", "0.5.4-alpha"),
      ("=0.7.x", "0.8.2"),
      (">=0.7.x", "0.6.2"),
      ("<0.7.x", "0.7.2"),
      ("<1.2.3", "1.2.3-beta"),
      ("=1.2.3", "1.2.3-beta"),
      (">1.2", "1.2.8"),
      ("^0.0.1", "0.0.2-alpha"),
      ("^0.0.1", "0.0.2"),
      ("^1.2.3", "2.0.0-alpha"),
      ("^1.2.3", "1.2.2"),
      ("^1.2", "1.1.9"),
      ("*", "v1.2.3-foo"),
      ("^1.0.0", "2.0.0-rc1"),
      ("1 - 2", "2.0.0-pre"),
      ("1 - 2", "1.0.0-pre"),
      ("1.0 - 2", "1.0.0-pre"),
      ("1.1.x", "1.0.0-a"),
      ("1.1.x", "1.1.0-a"),
      ("1.1.x", "1.2.0-a"),
      ("1.x", "1.0.0-a"),
      ("1.x", "1.1.0-a"),
      ("1.x", "1.2.0-a"),
      (">=1.0.0 <1.1.0", "1.1.0"),
      (">=1.0.0 <1.1.0", "1.1.0-pre"),
      (">=1.0.0 <1.1.0-pre", "1.1.0-pre"),
      // additional tests
      (">1.0.0-beta.1 <=1.1.0", "1.0.0-beta.1"),
      (">1.0.0-beta.1 <=1.1.0", "1.1.0-beta.1"),
    ];

    for (req_text, version_text) in fixtures {
      let req = parse_npm_version_req(req_text).unwrap();
      let version = parse_npm_version(version_text).unwrap();
      assert!(
        !req.matches(&version),
        "Checking {req_text} not satisfies {version_text}"
      );
    }
  }

  #[test]
  fn range_primitive_kind_beside_caret_or_tilde_with_whitespace() {
    // node semver should have enforced strictness, but it didn't
    // and so we end up with a system that acts this way
    let fixtures = &[
      (">= ^1.2.3", "1.2.3", true),
      (">= ^1.2.3", "1.2.4", true),
      (">= ^1.2.3", "1.9.3", true),
      (">= ^1.2.3", "2.0.0", false),
      (">= ^1.2.3", "1.2.2", false),
      // this is considered the same as the above by node semver
      ("> ^1.2.3", "1.2.3", true),
      ("> ^1.2.3", "1.2.4", true),
      ("> ^1.2.3", "1.9.3", true),
      ("> ^1.2.3", "2.0.0", false),
      ("> ^1.2.3", "1.2.2", false),
      // this is also considered the same
      ("< ^1.2.3", "1.2.3", true),
      ("< ^1.2.3", "1.2.4", true),
      ("< ^1.2.3", "1.9.3", true),
      ("< ^1.2.3", "2.0.0", false),
      ("< ^1.2.3", "1.2.2", false),
      // same with this
      ("<= ^1.2.3", "1.2.3", true),
      ("<= ^1.2.3", "1.2.4", true),
      ("<= ^1.2.3", "1.9.3", true),
      ("<= ^1.2.3", "2.0.0", false),
      ("<= ^1.2.3", "1.2.2", false),
      // now try a ~, which should work the same as above, but for ~
      ("<= ~1.2.3", "1.2.3", true),
      ("<= ~1.2.3", "1.2.4", true),
      ("<= ~1.2.3", "1.9.3", false),
      ("<= ~1.2.3", "2.0.0", false),
      ("<= ~1.2.3", "1.2.2", false),
    ];

    for (req_text, version_text, satisfies) in fixtures {
      let req = parse_npm_version_req(req_text).unwrap();
      let version = parse_npm_version(version_text).unwrap();
      assert_eq!(
        req.matches(&version),
        *satisfies,
        "Checking {} {} satisfies {}",
        req_text,
        if *satisfies { "true" } else { "false" },
        version_text
      );
    }
  }

  #[test]
  fn range_primitive_kind_beside_caret_or_tilde_no_whitespace() {
    let fixtures = &[
      ">=^1.2.3", ">^1.2.3", "<^1.2.3", "<=^1.2.3", ">=~1.2.3", ">~1.2.3",
      "<~1.2.3", "<=~1.2.3",
    ];

    for req_text in fixtures {
      // when it has no space, this is considered invalid
      // by node semver so we should error
      assert!(parse_npm_version_req(req_text).is_err());
    }
  }

  #[test]
  fn parse_npm_package_req_ref() {
    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      }),
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test@1").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".into(),
          version_req: VersionReq::parse_from_specifier("1").unwrap(),
        },
        sub_path: None,
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test@~1.1/sub_path")
        .unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".into(),
          version_req: VersionReq::parse_from_specifier("~1.1").unwrap(),
        },
        sub_path: Some("sub_path".into()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".into()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test@^1.2").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".into(),
          version_req: VersionReq::parse_from_specifier("^1.2").unwrap(),
        },
        sub_path: None,
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test@~1.1/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".into(),
          version_req: VersionReq::parse_from_specifier("~1.1").unwrap(),
        },
        sub_path: Some("sub_path".into()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".into()),
      })
    );

    let err = NpmPackageReqReference::from_str("npm:@package").unwrap_err();
    match err {
      PackageReqReferenceParseError::Invalid(err) => assert!(matches!(
        err.source,
        crate::package::PackageReqPartsParseError::InvalidPackageName
      )),
      _ => unreachable!(),
    }

    // missing version req
    let err = NpmPackageReqReference::from_str("npm:package@").unwrap_err();
    match err {
      PackageReqReferenceParseError::Invalid(err) => match err.source {
        crate::package::PackageReqPartsParseError::SpecifierVersionReq(err) => {
          assert_eq!(err.source.message, "Empty version constraint.");
        }
        _ => unreachable!(),
      },
      _ => unreachable!(),
    }

    // should parse leading slash
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/@package/test/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".into()),
      })
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/test").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      })
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/test/").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".into(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      })
    );

    // should error for no name
    match NpmPackageReqReference::from_str("npm:/").unwrap_err() {
      PackageReqReferenceParseError::Invalid(err) => assert!(matches!(
        err.source,
        crate::package::PackageReqPartsParseError::NoPackageName
      )),
      _ => unreachable!(),
    }
    match NpmPackageReqReference::from_str("npm://test").unwrap_err() {
      PackageReqReferenceParseError::Invalid(err) => assert!(matches!(
        err.source,
        crate::package::PackageReqPartsParseError::NoPackageName
      )),
      _ => unreachable!(),
    }

    // path with `@` shouldn't error
    assert_eq!(
      NpmPackageReqReference::from_str("npm:package@^5.0.0-beta.35/@some/path")
        .unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "package".into(),
          version_req: VersionReq::parse_from_specifier("^5.0.0-beta.35")
            .unwrap(),
        },
        sub_path: Some("@some/path".into()),
      }),
    );
  }

  #[test]
  fn package_nv_ref() {
    let package_nv_ref =
      NpmPackageNvReference::from_str("npm:package@1.2.3/test").unwrap();
    assert_eq!(
      package_nv_ref,
      NpmPackageNvReference(PackageNvReference {
        nv: PackageNv {
          name: "package".into(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: Some("test".into())
      })
    );
    assert_eq!(
      package_nv_ref.as_specifier().as_str(),
      "npm:/package@1.2.3/test"
    );

    // no path
    let package_nv_ref =
      NpmPackageNvReference::from_str("npm:package@1.2.3").unwrap();
    assert_eq!(
      package_nv_ref,
      NpmPackageNvReference(PackageNvReference {
        nv: PackageNv {
          name: "package".into(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: None
      })
    );
    assert_eq!(package_nv_ref.as_specifier().as_str(), "npm:/package@1.2.3");
  }

  #[test]
  fn zero_version_with_pre_release_matches() {
    {
      let req = parse_npm_version_req("<1.0.0-0").unwrap();
      assert!(req.matches(&Version::parse_from_npm("0.0.0").unwrap()));
      assert!(!req.matches(&Version::parse_from_npm("0.0.0-pre").unwrap()));
    }
    {
      let req = parse_npm_version_req("<1.0.0").unwrap();
      assert!(req.matches(&Version::parse_from_npm("0.0.0").unwrap()));
      assert!(!req.matches(&Version::parse_from_npm("0.0.0-pre").unwrap()));
    }
    {
      let req = parse_npm_version_req("^0").unwrap();
      assert!(req.matches(&Version::parse_from_npm("0.0.0").unwrap()));
      assert!(!req.matches(&Version::parse_from_npm("0.0.0-pre").unwrap()));
    }
    {
      let req = parse_npm_version_req("*").unwrap();
      assert!(req.matches(&Version::parse_from_npm("0.0.0").unwrap()));
      assert!(!req.matches(&Version::parse_from_npm("0.0.0-pre").unwrap()));
    }
  }

  #[test]
  fn test_is_valid_npm_tag() {
    assert_eq!(is_valid_npm_tag("latest"), true);
    assert_eq!(is_valid_npm_tag(""), false);
    assert_eq!(is_valid_npm_tag("SD&*($#&%*(#*$%"), false);
  }
}
