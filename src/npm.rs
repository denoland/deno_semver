// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use std::cmp::Ordering;

use monch::*;
use thiserror::Error;

use serde::Deserialize;
use serde::Serialize;
use url::Url;

use crate::package::PackageKind;
use crate::package::PackageNv;
use crate::package::PackageNvReference;
use crate::package::PackageNvReferenceParseError;
use crate::package::PackageReq;
use crate::package::PackageReqReference;
use crate::package::PackageReqReferenceParseError;

use super::Partial;
use super::RangeSetOrTag;
use super::Version;
use super::VersionBoundKind;
use super::VersionRange;
use super::VersionRangeSet;
use super::VersionReq;
use super::XRange;

#[derive(Debug, Error)]
#[error("Invalid npm package id '{text}'. {message}")]
pub struct NpmPackageIdDeserializationError {
  message: String,
  text: String,
}

/// A resolved unique identifier for an npm package. This contains
/// the resolved name, version, and peer dependency resolution identifiers.
#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NpmPackageId {
  pub nv: PackageNv,
  pub peer_dependencies: Vec<NpmPackageId>,
}

// Custom debug implementation for more concise test output
impl std::fmt::Debug for NpmPackageId {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.as_serialized())
  }
}

impl NpmPackageId {
  pub fn as_serialized(&self) -> String {
    self.as_serialized_with_level(0)
  }

  fn as_serialized_with_level(&self, level: usize) -> String {
    // WARNING: This should not change because it's used in the lockfile
    let mut result = format!(
      "{}@{}",
      if level == 0 {
        self.nv.name.to_string()
      } else {
        self.nv.name.replace('/', "+")
      },
      self.nv.version
    );
    for peer in &self.peer_dependencies {
      // unfortunately we can't do something like `_3` when
      // this gets deep because npm package names can start
      // with a number
      result.push_str(&"_".repeat(level + 1));
      result.push_str(&peer.as_serialized_with_level(level + 1));
    }
    result
  }

  pub fn from_serialized(
    id: &str,
  ) -> Result<Self, NpmPackageIdDeserializationError> {
    use monch::*;

    fn parse_name(input: &str) -> ParseResult<&str> {
      if_not_empty(substring(move |input| {
        for (pos, c) in input.char_indices() {
          // first character might be a scope, so skip it
          if pos > 0 && c == '@' {
            return Ok((&input[pos..], ()));
          }
        }
        ParseError::backtrace()
      }))(input)
    }

    fn parse_version(input: &str) -> ParseResult<&str> {
      if_not_empty(substring(skip_while(|c| c != '_')))(input)
    }

    fn parse_name_and_version(input: &str) -> ParseResult<(String, Version)> {
      let (input, name) = parse_name(input)?;
      let (input, _) = ch('@')(input)?;
      let at_version_input = input;
      let (input, version_str) = parse_version(input)?;
      match parse_npm_version_no_error_handling(version_str) {
        Ok((version_parse_input, version)) => {
          if !version_parse_input.is_empty() {
            // should never happen where the parse_input still has text
            let parsed_len = version_str.len() - version_parse_input.len();
            Err(ParseError::Failure(
              ParseErrorFailure::new_for_trailing_input(&input[parsed_len..]),
            ))
          } else {
            Ok((input, (name.to_string(), version)))
          }
        }
        Err(err) => {
          let message = match &err {
            ParseError::Backtrace => "Unexpected character.",
            ParseError::Failure(err) => err.message.as_str(),
          };
          Err(ParseError::Failure(ParseErrorFailure {
            input: at_version_input,
            message: format!("Invalid npm version. {}", message),
          }))
        }
      }
    }

    fn parse_level_at_level<'a>(
      level: usize,
    ) -> impl Fn(&'a str) -> ParseResult<'a, ()> {
      fn parse_level(input: &str) -> ParseResult<usize> {
        let level = input.chars().take_while(|c| *c == '_').count();
        Ok((&input[level..], level))
      }

      move |input| {
        let (input, parsed_level) = parse_level(input)?;
        if parsed_level == level {
          Ok((input, ()))
        } else {
          ParseError::backtrace()
        }
      }
    }

    fn parse_peers_at_level<'a>(
      level: usize,
    ) -> impl Fn(&'a str) -> ParseResult<'a, Vec<NpmPackageId>> {
      move |mut input| {
        let mut peers = Vec::new();
        while let Ok((level_input, _)) = parse_level_at_level(level)(input) {
          input = level_input;
          let peer_result = parse_id_at_level(level)(input)?;
          input = peer_result.0;
          peers.push(peer_result.1);
        }
        Ok((input, peers))
      }
    }

    fn parse_id_at_level<'a>(
      level: usize,
    ) -> impl Fn(&'a str) -> ParseResult<'a, NpmPackageId> {
      move |input| {
        let (input, (name, version)) = parse_name_and_version(input)?;
        let name = if level > 0 {
          name.replace('+', "/")
        } else {
          name
        };
        let (input, peer_dependencies) =
          parse_peers_at_level(level + 1)(input)?;
        Ok((
          input,
          NpmPackageId {
            nv: PackageNv { name, version },
            peer_dependencies,
          },
        ))
      }
    }

    with_failure_handling(parse_id_at_level(0))(id).map_err(|err| {
      NpmPackageIdDeserializationError {
        message: format!("{err:#}"),
        text: id.to_string(),
      }
    })
  }
}

impl Ord for NpmPackageId {
  fn cmp(&self, other: &Self) -> Ordering {
    match self.nv.cmp(&other.nv) {
      Ordering::Equal => self.peer_dependencies.cmp(&other.peer_dependencies),
      ordering => ordering,
    }
  }
}

impl PartialOrd for NpmPackageId {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

pub fn is_valid_npm_tag(value: &str) -> bool {
  // a valid tag is anything that doesn't get url encoded
  // https://github.com/npm/npm-package-arg/blob/103c0fda8ed8185733919c7c6c73937cfb2baf3a/lib/npa.js#L399-L401
  value
    .chars()
    .all(|c| c.is_alphanumeric() || matches!(c, '-' | '_' | '.' | '~'))
}

// A lot of the below is a re-implementation of parts of https://github.com/npm/node-semver
// which is Copyright (c) Isaac Z. Schlueter and Contributors (ISC License)

#[derive(Error, Debug, Clone)]
#[error("Invalid npm version. {source}")]
pub struct NpmVersionParseError {
  #[source]
  pub(crate) source: ParseErrorFailureError,
}

pub fn parse_npm_version(text: &str) -> Result<Version, NpmVersionParseError> {
  let text = text.trim();
  with_failure_handling(parse_npm_version_no_error_handling)(text)
    .map_err(|err| NpmVersionParseError { source: err })
}

pub(crate) fn parse_npm_version_no_error_handling(
  input: &str,
) -> ParseResult<Version> {
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
}

#[derive(Error, Debug, Clone)]
#[error("Invalid npm version requirement. {source}")]
pub struct NpmVersionReqParseError {
  #[source]
  source: ParseErrorFailureError,
}

pub fn parse_npm_version_req(
  text: &str,
) -> Result<VersionReq, NpmVersionReqParseError> {
  let text = text.trim();
  with_failure_handling(|input| {
    map(inner, |inner| {
      VersionReq::from_raw_text_and_inner(input.to_string(), inner)
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
fn inner(input: &str) -> ParseResult<RangeSetOrTag> {
  if input.is_empty() {
    return Ok((
      input,
      RangeSetOrTag::RangeSet(VersionRangeSet(vec![VersionRange::all()])),
    ));
  }

  let (input, mut ranges) =
    separated_list(range_or_invalid, logical_or)(input)?;

  if ranges.len() == 1 {
    match ranges.remove(0) {
      RangeOrInvalid::Invalid(invalid) => {
        if is_valid_npm_tag(invalid.text) {
          return Ok((input, RangeSetOrTag::Tag(invalid.text.to_string())));
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
    .filter_map(|r| r.into_range())
    .collect::<Vec<_>>();
  Ok((input, RangeSetOrTag::RangeSet(VersionRangeSet(ranges))))
}

enum RangeOrInvalid<'a> {
  Range(VersionRange),
  Invalid(InvalidRange<'a>),
}

impl<'a> RangeOrInvalid<'a> {
  pub fn into_range(self) -> Option<VersionRange> {
    match self {
      RangeOrInvalid::Range(r) => {
        if r.is_none() {
          None
        } else {
          Some(r)
        }
      }
      RangeOrInvalid::Invalid(_) => None,
    }
  }
}

struct InvalidRange<'a> {
  failure: ParseError<'a>,
  text: &'a str,
}

fn range_or_invalid(input: &str) -> ParseResult<RangeOrInvalid> {
  let range_result =
    map_res(map(range, RangeOrInvalid::Range), |result| match result {
      Ok((input, range)) => {
        let is_end = input.is_empty() || logical_or(input).is_ok();
        if is_end {
          Ok((input, range))
        } else {
          ParseError::backtrace()
        }
      }
      Err(err) => Err(err),
    })(input);
  match range_result {
    Ok(result) => Ok(result),
    Err(failure) => {
      let (input, text) = invalid_range(input)?;
      Ok((
        input,
        RangeOrInvalid::Invalid(InvalidRange { failure, text }),
      ))
    }
  }
}

fn invalid_range(input: &str) -> ParseResult<&str> {
  let end_index = input.find("||").unwrap_or(input.len());
  let text = input[..end_index].trim();
  Ok((&input[end_index..], text))
}

// range ::= hyphen | simple ( ' ' simple ) * | ''
fn range(input: &str) -> ParseResult<VersionRange> {
  or(
    map(hyphen, |hyphen| VersionRange {
      start: hyphen.start.as_lower_bound(),
      end: hyphen.end.as_upper_bound(),
    }),
    map(separated_list(simple, whitespace), |ranges| {
      let mut final_range = VersionRange::all();
      for range in ranges {
        final_range = final_range.clamp(&range);
      }
      final_range
    }),
  )(input)
}

#[derive(Debug, Clone)]
struct Hyphen {
  start: Partial,
  end: Partial,
}

// hyphen ::= partial ' - ' partial
fn hyphen(input: &str) -> ParseResult<Hyphen> {
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

// logical-or ::= ( ' ' ) * '||' ( ' ' ) *
fn logical_or(input: &str) -> ParseResult<&str> {
  delimited(skip_whitespace, tag("||"), skip_whitespace)(input)
}

fn skip_whitespace_or_v(input: &str) -> ParseResult<()> {
  map(
    pair(skip_whitespace, pair(maybe(ch('v')), skip_whitespace)),
    |_| (),
  )(input)
}

// simple ::= primitive | partial | tilde | caret
fn simple(input: &str) -> ParseResult<VersionRange> {
  or4(
    map(preceded(tilde, partial), |partial| {
      partial.as_tilde_version_range()
    }),
    map(preceded(caret, partial), |partial| {
      partial.as_caret_version_range()
    }),
    map(primitive, |primitive| {
      let partial = primitive.partial;
      match primitive.kind {
        PrimitiveKind::Equal => partial.as_equal_range(),
        PrimitiveKind::GreaterThan => {
          partial.as_greater_than(VersionBoundKind::Exclusive)
        }
        PrimitiveKind::GreaterThanOrEqual => {
          partial.as_greater_than(VersionBoundKind::Inclusive)
        }
        PrimitiveKind::LessThan => {
          partial.as_less_than(VersionBoundKind::Exclusive)
        }
        PrimitiveKind::LessThanOrEqual => {
          partial.as_less_than(VersionBoundKind::Inclusive)
        }
      }
    }),
    map(partial, |partial| partial.as_equal_range()),
  )(input)
}

fn tilde(input: &str) -> ParseResult<()> {
  fn raw_tilde(input: &str) -> ParseResult<()> {
    map(pair(or(tag("~>"), tag("~")), skip_whitespace_or_v), |_| ())(input)
  }

  or(
    preceded(terminated(primitive_kind, whitespace), raw_tilde),
    raw_tilde,
  )(input)
}

fn caret(input: &str) -> ParseResult<()> {
  fn raw_caret(input: &str) -> ParseResult<()> {
    map(pair(ch('^'), skip_whitespace_or_v), |_| ())(input)
  }

  or(
    preceded(terminated(primitive_kind, whitespace), raw_caret),
    raw_caret,
  )(input)
}

#[derive(Debug, Clone, Copy)]
enum PrimitiveKind {
  GreaterThan,
  LessThan,
  GreaterThanOrEqual,
  LessThanOrEqual,
  Equal,
}

#[derive(Debug, Clone)]
struct Primitive {
  kind: PrimitiveKind,
  partial: Partial,
}

fn primitive(input: &str) -> ParseResult<Primitive> {
  let (input, kind) = primitive_kind(input)?;
  let (input, _) = skip_whitespace(input)?;
  let (input, partial) = partial(input)?;
  Ok((input, Primitive { kind, partial }))
}

fn primitive_kind(input: &str) -> ParseResult<PrimitiveKind> {
  or5(
    map(tag(">="), |_| PrimitiveKind::GreaterThanOrEqual),
    map(tag("<="), |_| PrimitiveKind::LessThanOrEqual),
    map(ch('<'), |_| PrimitiveKind::LessThan),
    map(ch('>'), |_| PrimitiveKind::GreaterThan),
    map(ch('='), |_| PrimitiveKind::Equal),
  )(input)
}

// partial ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
fn partial(input: &str) -> ParseResult<Partial> {
  let (input, _) = maybe(ch('v'))(input)?; // skip leading v
  let (input, major) = xr()(input)?;
  let (input, maybe_minor) = maybe(preceded(ch('.'), xr()))(input)?;
  let (input, maybe_patch) = if maybe_minor.is_some() {
    maybe(preceded(ch('.'), xr()))(input)?
  } else {
    (input, None)
  };
  let (input, qual) = if maybe_patch.is_some() {
    maybe(qualifier)(input)?
  } else {
    (input, None)
  };
  let qual = qual.unwrap_or_default();
  Ok((
    input,
    Partial {
      major,
      minor: maybe_minor.unwrap_or(XRange::Wildcard),
      patch: maybe_patch.unwrap_or(XRange::Wildcard),
      pre: qual.pre,
      build: qual.build,
    },
  ))
}

// xr ::= 'x' | 'X' | '*' | nr
fn xr<'a>() -> impl Fn(&'a str) -> ParseResult<'a, XRange> {
  or(
    map(or3(tag("x"), tag("X"), tag("*")), |_| XRange::Wildcard),
    map(nr, XRange::Val),
  )
}

// nr ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
fn nr(input: &str) -> ParseResult<u64> {
  // we do loose parsing to support people doing stuff like 01.02.03
  let (input, result) =
    if_not_empty(substring(skip_while(|c| c.is_ascii_digit())))(input)?;
  let val = match result.parse::<u64>() {
    Ok(val) => val,
    Err(err) => {
      return ParseError::fail(
        input,
        format!("Error parsing '{result}' to u64.\n\n{err:#}"),
      )
    }
  };
  Ok((input, val))
}

#[derive(Debug, Clone, Default)]
struct Qualifier {
  pre: Vec<String>,
  build: Vec<String>,
}

// qualifier ::= ( '-' pre )? ( '+' build )?
fn qualifier(input: &str) -> ParseResult<Qualifier> {
  let (input, pre_parts) = maybe(pre)(input)?;
  let (input, build_parts) = maybe(build)(input)?;
  Ok((
    input,
    Qualifier {
      pre: pre_parts.unwrap_or_default(),
      build: build_parts.unwrap_or_default(),
    },
  ))
}

// pre ::= parts
fn pre(input: &str) -> ParseResult<Vec<String>> {
  preceded(maybe(ch('-')), parts)(input)
}

// build ::= parts
fn build(input: &str) -> ParseResult<Vec<String>> {
  preceded(ch('+'), parts)(input)
}

// parts ::= part ( '.' part ) *
fn parts(input: &str) -> ParseResult<Vec<String>> {
  if_not_empty(map(separated_list(part, ch('.')), |text| {
    text.into_iter().map(ToOwned::to_owned).collect()
  }))(input)
}

// part ::= nr | [-0-9A-Za-z]+
fn part(input: &str) -> ParseResult<&str> {
  // nr is in the other set, so don't bother checking for it
  if_true(
    take_while(|c| c.is_ascii_alphanumeric() || c == '-'),
    |result| !result.is_empty(),
  )(input)
}

/// A reference to an npm package's name, version constraint, and potential sub path.
/// This contains all the information found in an npm specifier.
///
/// This wraps PackageReqReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NpmPackageReqReference(PackageReqReference);

impl std::fmt::Display for NpmPackageReqReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "npm:{}", self.0)
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
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
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

impl std::fmt::Display for NpmPackageNvReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "npm:{}", self.0)
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
    let text = String::deserialize(deserializer)?;
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

  #[test]
  fn serialize_npm_package_id() {
    let id = NpmPackageId {
      nv: PackageNv::from_str("pkg-a@1.2.3").unwrap(),
      peer_dependencies: vec![
        NpmPackageId {
          nv: PackageNv::from_str("pkg-b@3.2.1").unwrap(),
          peer_dependencies: vec![
            NpmPackageId {
              nv: PackageNv::from_str("pkg-c@1.3.2").unwrap(),
              peer_dependencies: vec![],
            },
            NpmPackageId {
              nv: PackageNv::from_str("pkg-d@2.3.4").unwrap(),
              peer_dependencies: vec![],
            },
          ],
        },
        NpmPackageId {
          nv: PackageNv::from_str("pkg-e@2.3.1").unwrap(),
          peer_dependencies: vec![NpmPackageId {
            nv: PackageNv::from_str("pkg-f@2.3.1").unwrap(),
            peer_dependencies: vec![],
          }],
        },
      ],
    };

    // this shouldn't change because it's used in the lockfile
    let serialized = id.as_serialized();
    assert_eq!(serialized, "pkg-a@1.2.3_pkg-b@3.2.1__pkg-c@1.3.2__pkg-d@2.3.4_pkg-e@2.3.1__pkg-f@2.3.1");
    assert_eq!(NpmPackageId::from_serialized(&serialized).unwrap(), id);
  }

  #[test]
  fn parse_npm_package_id() {
    #[track_caller]
    fn run_test(input: &str) {
      let id = NpmPackageId::from_serialized(input).unwrap();
      assert_eq!(id.as_serialized(), input);
    }

    run_test("pkg-a@1.2.3");
    run_test("pkg-a@1.2.3_pkg-b@3.2.1");
    run_test(
      "pkg-a@1.2.3_pkg-b@3.2.1__pkg-c@1.3.2__pkg-d@2.3.4_pkg-e@2.3.1__pkg-f@2.3.1",
    );

    #[track_caller]
    fn run_error_test(input: &str, message: &str) {
      let err = NpmPackageId::from_serialized(input).unwrap_err();
      assert_eq!(format!("{:#}", err), message);
    }

    run_error_test(
      "asdf",
      "Invalid npm package id 'asdf'. Unexpected character.
  asdf
  ~",
    );
    run_error_test(
      "asdf@test",
      "Invalid npm package id 'asdf@test'. Invalid npm version. Unexpected character.
  test
  ~",
    );
    run_error_test(
      "pkg@1.2.3_asdf@test",
      "Invalid npm package id 'pkg@1.2.3_asdf@test'. Invalid npm version. Unexpected character.
  test
  ~",
    );
  }

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
  pub fn npm_version_req_with_tag() {
    let req = parse_npm_version_req("latest").unwrap();
    assert_eq!(req.tag(), Some("latest"));
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
      ("1.0.0 - 2.0.0", ">=1.0.0 <=2.0.0"),
      ("1 - 2", ">=1.0.0 <3.0.0-0"),
      ("1.0 - 2.0", ">=1.0.0 <2.1.0-0"),
      ("1.0.0", "1.0.0"),
      (">=*", "*"),
      ("", "*"),
      ("*", "*"),
      ("*", "*"),
      (">=1.0.0", ">=1.0.0"),
      (">1.0.0", ">1.0.0"),
      ("<=2.0.0", "<=2.0.0"),
      ("1", ">=1.0.0 <2.0.0-0"),
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
      ("2.x.x", ">=2.0.0 <3.0.0-0"),
      ("1.2.x", ">=1.2.0 <1.3.0-0"),
      ("1.2.x || 2.x", ">=1.2.0 <1.3.0-0||>=2.0.0 <3.0.0-0"),
      ("1.2.x || 2.x", ">=1.2.0 <1.3.0-0||>=2.0.0 <3.0.0-0"),
      ("x", "*"),
      ("2.*.*", ">=2.0.0 <3.0.0-0"),
      ("1.2.*", ">=1.2.0 <1.3.0-0"),
      ("1.2.* || 2.*", ">=1.2.0 <1.3.0-0||>=2.0.0 <3.0.0-0"),
      ("*", "*"),
      ("2", ">=2.0.0 <3.0.0-0"),
      ("2.3", ">=2.3.0 <2.4.0-0"),
      ("~2.4", ">=2.4.0 <2.5.0-0"),
      ("~2.4", ">=2.4.0 <2.5.0-0"),
      ("~>3.2.1", ">=3.2.1 <3.3.0-0"),
      ("~1", ">=1.0.0 <2.0.0-0"),
      ("~>1", ">=1.0.0 <2.0.0-0"),
      ("~> 1", ">=1.0.0 <2.0.0-0"),
      ("~1.0", ">=1.0.0 <1.1.0-0"),
      ("~ 1.0", ">=1.0.0 <1.1.0-0"),
      ("^0", "<1.0.0-0"),
      ("^ 1", ">=1.0.0 <2.0.0-0"),
      ("^0.1", ">=0.1.0 <0.2.0-0"),
      ("^1.0", ">=1.0.0 <2.0.0-0"),
      ("^1.2", ">=1.2.0 <2.0.0-0"),
      ("^0.0.1", ">=0.0.1 <0.0.2-0"),
      ("^0.0.1-beta", ">=0.0.1-beta <0.0.2-0"),
      ("^0.1.2", ">=0.1.2 <0.2.0-0"),
      ("^1.2.3", ">=1.2.3 <2.0.0-0"),
      ("^1.2.3-beta.4", ">=1.2.3-beta.4 <2.0.0-0"),
      ("<1", "<1.0.0-0"),
      ("< 1", "<1.0.0-0"),
      (">=1", ">=1.0.0"),
      (">= 1", ">=1.0.0"),
      ("<1.2", "<1.2.0-0"),
      ("< 1.2", "<1.2.0-0"),
      ("1", ">=1.0.0 <2.0.0-0"),
      ("^ 1.2 ^ 1", ">=1.2.0 <2.0.0-0 >=1.0.0"),
      ("1.2 - 3.4.5", ">=1.2.0 <=3.4.5"),
      ("1.2.3 - 3.4", ">=1.2.3 <3.5.0-0"),
      ("1.2 - 3.4", ">=1.2.0 <3.5.0-0"),
      (">1", ">=2.0.0"),
      (">1.2", ">=1.3.0"),
      (">X", "<0.0.0-0"),
      ("<X", "<0.0.0-0"),
      ("<x <* || >* 2.x", "<0.0.0-0"),
      (">x 2.x || * || <x", "*"),
      (">01.02.03", ">1.2.3"),
      ("~1.2.3beta", ">=1.2.3-beta <1.3.0-0"),
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
    ];
    for (req_text, version_text) in fixtures {
      let req = parse_npm_version_req(req_text).unwrap();
      let version = parse_npm_version(version_text).unwrap();
      assert!(
        req.matches(&version),
        "Checking {req_text} satisfies {version_text}"
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
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      }),
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test@1").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".to_string(),
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
          name: "@package/test".to_string(),
          version_req: VersionReq::parse_from_specifier("~1.1").unwrap(),
        },
        sub_path: Some("sub_path".to_string()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".to_string()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test@^1.2").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".to_string(),
          version_req: VersionReq::parse_from_specifier("^1.2").unwrap(),
        },
        sub_path: None,
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test@~1.1/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".to_string(),
          version_req: VersionReq::parse_from_specifier("~1.1").unwrap(),
        },
        sub_path: Some("sub_path".to_string()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".to_string()),
      })
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package")
        .err()
        .unwrap()
        .to_string(),
      "Invalid package specifier 'npm:@package'. Did not contain a valid package name."
    );

    // should parse leading slash
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/@package/test/sub_path").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".to_string()),
      })
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/test").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      })
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/test/").unwrap(),
      NpmPackageReqReference::new(PackageReqReference {
        req: PackageReq {
          name: "test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      })
    );

    // should error for no name
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/")
        .err()
        .unwrap()
        .to_string(),
      "Invalid package specifier 'npm:/'. Did not contain a package name."
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm://test")
        .err()
        .unwrap()
        .to_string(),
      "Invalid package specifier 'npm://test'. Did not contain a package name."
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
          name: "package".to_string(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: Some("test".to_string())
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
          name: "package".to_string(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: None
      })
    );
    assert_eq!(package_nv_ref.as_specifier().as_str(), "npm:/package@1.2.3");
  }
}
