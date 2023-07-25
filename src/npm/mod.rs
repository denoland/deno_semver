// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use std::cmp::Ordering;

use monch::*;
use once_cell::sync::Lazy;
use thiserror::Error;

use serde::Deserialize;
use serde::Serialize;
use url::Url;

/// Specifier that points to the wildcard version.
pub static WILDCARD_VERSION_REQ: Lazy<VersionReq> =
  Lazy::new(|| VersionReq::parse_from_specifier("*").unwrap());

pub use self::specifier::NpmVersionReqSpecifierParseError;

use super::Partial;
use super::RangeSetOrTag;
use super::Version;
use super::VersionBoundKind;
use super::VersionRange;
use super::VersionRangeSet;
use super::VersionReq;
use super::XRange;

pub(super) mod specifier;

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

#[derive(Debug, Error, Clone)]
#[error("Invalid npm package name and version reference '{text}'. {message}")]
pub struct NpmPackageNvReferenceParseError {
  pub message: String,
  pub text: String,
}

/// A npm package name and version with a potential subpath.
#[derive(
  Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Serialize, Deserialize,
)]
pub struct NpmPackageNvReference {
  pub nv: NpmPackageNv,
  pub sub_path: Option<String>,
}

impl NpmPackageNvReference {
  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, NpmPackageNvReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(nv: &str) -> Result<Self, NpmPackageNvReferenceParseError> {
    use monch::*;

    fn sub_path(input: &str) -> ParseResult<&str> {
      let (input, _) = ch('/')(input)?;
      Ok(("", input))
    }

    fn parse_ref(input: &str) -> ParseResult<NpmPackageNvReference> {
      let (input, _) = tag("npm:")(input)?;
      let (input, nv) = parse_nv(input)?;
      let (input, maybe_sub_path) = maybe(sub_path)(input)?;
      Ok((
        input,
        NpmPackageNvReference {
          nv,
          sub_path: maybe_sub_path.map(ToOwned::to_owned),
        },
      ))
    }

    with_failure_handling(parse_ref)(nv).map_err(|err| {
      NpmPackageNvReferenceParseError {
        message: format!("{err:#}"),
        text: nv.to_string(),
      }
    })
  }

  pub fn as_specifier(&self) -> Url {
    let version_text = self.nv.version.to_string();
    let capacity = 4
      + self.nv.name.len()
      + 1
      + version_text.len()
      + self.sub_path.as_ref().map(|p| p.len() + 1).unwrap_or(0);
    let mut text = String::with_capacity(capacity);
    text.push_str("npm:");
    text.push_str(&self.nv.name);
    text.push('@');
    text.push_str(&version_text);
    if let Some(sub_path) = &self.sub_path {
      text.push('/');
      text.push_str(sub_path);
    }
    debug_assert_eq!(text.len(), capacity);
    Url::parse(&text).unwrap()
  }
}

impl std::fmt::Display for NpmPackageNvReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if let Some(sub_path) = &self.sub_path {
      write!(f, "npm:{}/{}", self.nv, sub_path)
    } else {
      write!(f, "npm:{}", self.nv)
    }
  }
}

#[derive(Debug, Error, Clone)]
#[error("Invalid npm package name and version '{text}'. {message}")]
pub struct NpmPackageNvParseError {
  pub message: String,
  pub text: String,
}

#[derive(
  Clone, PartialOrd, Ord, PartialEq, Eq, Hash, Serialize, Deserialize,
)]
pub struct NpmPackageNv {
  pub name: String,
  pub version: Version,
}

impl std::fmt::Debug for NpmPackageNv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // when debugging, it's easier to compare this
    write!(f, "{}@{}", self.name, self.version)
  }
}

impl std::fmt::Display for NpmPackageNv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}@{}", self.name, self.version)
  }
}

impl NpmPackageNv {
  #[allow(clippy::should_implement_trait)]
  pub fn from_str(nv: &str) -> Result<Self, NpmPackageNvParseError> {
    monch::with_failure_handling(parse_nv)(nv).map_err(|err| {
      NpmPackageNvParseError {
        message: format!("{err:#}"),
        text: nv.to_string(),
      }
    })
  }

  pub fn scope(&self) -> Option<&str> {
    if self.name.starts_with('@') && self.name.contains('/') {
      self.name.split('/').next()
    } else {
      None
    }
  }
}

fn parse_nv(input: &str) -> monch::ParseResult<NpmPackageNv> {
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
    if_not_empty(substring(skip_while(|c| !matches!(c, '_' | '/'))))(input)
  }

  let (input, name) = parse_name(input)?;
  let (input, _) = ch('@')(input)?;
  let at_version_input = input;
  let (input, version) = parse_version(input)?;
  match Version::parse_from_npm(version) {
    Ok(version) => Ok((
      input,
      NpmPackageNv {
        name: name.to_string(),
        version,
      },
    )),
    Err(err) => ParseError::fail(at_version_input, format!("{err:#}")),
  }
}

#[derive(Error, Debug, Clone)]
pub enum NpmPackageReqReferenceParseError {
  #[error("Not an npm specifier.")]
  NotNpmSpecifier,
  #[error("Not a valid package: {0}")]
  InvalidPackage(String),
  #[error("Invalid npm specifier '{specifier}'. {source:#}")]
  Invalid {
    specifier: String,
    #[source]
    source: VersionReqPartsParseError,
  },
  #[error("Invalid package specifier 'npm:{current}'. Did you mean to write 'npm:{suggested}'?")]
  InvalidPathWithVersion { current: String, suggested: String },
}

/// A reference to an npm package's name, version constraint, and potential sub path.
///
/// This contains all the information found in an npm specifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NpmPackageReqReference {
  pub req: NpmPackageReq,
  pub sub_path: Option<String>,
}

impl NpmPackageReqReference {
  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, NpmPackageReqReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(
    specifier: &str,
  ) -> Result<Self, NpmPackageReqReferenceParseError> {
    let original_text = specifier;
    let specifier = match specifier.strip_prefix("npm:") {
      Some(s) => {
        // Strip leading slash, which might come from import map
        s.strip_prefix('/').unwrap_or(s)
      }
      None => {
        // don't allocate a string here and instead use a static string
        // because this is hit a lot when a url is not an npm specifier
        return Err(NpmPackageReqReferenceParseError::NotNpmSpecifier);
      }
    };
    let parts = specifier.split('/').collect::<Vec<_>>();
    let name_part_len = if specifier.starts_with('@') { 2 } else { 1 };
    if parts.len() < name_part_len {
      return Err(NpmPackageReqReferenceParseError::InvalidPackage(
        specifier.to_string(),
      ));
    }
    let name_parts = &parts[0..name_part_len];
    let req = match NpmPackageReq::parse_from_parts(name_parts) {
      Ok(pkg_req) => pkg_req,
      Err(err) => {
        return Err(NpmPackageReqReferenceParseError::Invalid {
          specifier: original_text.to_string(),
          source: err,
        });
      }
    };
    let sub_path = if parts.len() == name_parts.len() {
      None
    } else {
      let sub_path = parts[name_part_len..].join("/");
      if sub_path.is_empty() {
        None
      } else {
        Some(sub_path)
      }
    };

    if let Some(sub_path) = &sub_path {
      if let Some(at_index) = sub_path.rfind('@') {
        let (new_sub_path, version) = sub_path.split_at(at_index);
        return Err(NpmPackageReqReferenceParseError::InvalidPathWithVersion {
          current: format!("{req}/{sub_path}"),
          suggested: format!("{req}{version}/{new_sub_path}"),
        });
      }
    }

    Ok(NpmPackageReqReference { req, sub_path })
  }
}

impl std::fmt::Display for NpmPackageReqReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if let Some(sub_path) = &self.sub_path {
      write!(f, "npm:{}/{}", self.req, sub_path)
    } else {
      write!(f, "npm:{}", self.req)
    }
  }
}

#[derive(Error, Debug, Clone)]
pub enum VersionReqPartsParseError {
  #[error("Did not contain a package name.")]
  NoPackageName,
  #[error("Invalid version requirement. {source:#}")]
  VersionReq {
    #[source]
    source: NpmVersionReqSpecifierParseError,
  },
}

#[derive(Error, Debug, Clone)]
#[error("Invalid npm package requirement '{text}'. {source:#}")]
pub struct NpmPackageReqParseError {
  pub text: String,
  #[source]
  pub source: VersionReqPartsParseError,
}

/// The name and version constraint component of an `NpmPackageReqReference`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct NpmPackageReq {
  pub name: String,
  pub version_req: VersionReq,
}

impl std::fmt::Display for NpmPackageReq {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}@{}", self.name, self.version_req)
  }
}

impl NpmPackageReq {
  #[allow(clippy::should_implement_trait)]
  pub fn from_str(text: &str) -> Result<Self, NpmPackageReqParseError> {
    let parts = text.split('/').collect::<Vec<_>>();
    match NpmPackageReq::parse_from_parts(&parts) {
      Ok(req) => Ok(req),
      Err(err) => Err(NpmPackageReqParseError {
        text: text.to_string(),
        source: err,
      }),
    }
  }

  fn parse_from_parts(
    name_parts: &[&str],
  ) -> Result<Self, VersionReqPartsParseError> {
    assert!(!name_parts.is_empty()); // this should be provided the result of a string split
    let last_name_part = &name_parts[name_parts.len() - 1];
    let (name, version_req) = if let Some(at_index) = last_name_part.rfind('@')
    {
      let version = &last_name_part[at_index + 1..];
      let last_name_part = &last_name_part[..at_index];
      let version_req = VersionReq::parse_from_specifier(version)
        .map_err(|err| VersionReqPartsParseError::VersionReq { source: err })?;
      let name = if name_parts.len() == 1 {
        last_name_part.to_string()
      } else {
        format!("{}/{}", name_parts[0], last_name_part)
      };
      (name, Some(version_req))
    } else {
      (name_parts.join("/"), None)
    };
    if name.is_empty() {
      Err(VersionReqPartsParseError::NoPackageName)
    } else {
      Ok(Self {
        name,
        version_req: version_req
          .unwrap_or_else(|| WILDCARD_VERSION_REQ.clone()),
      })
    }
  }
}

impl Serialize for NpmPackageReq {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for NpmPackageReq {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let text = String::deserialize(deserializer)?;
    match NpmPackageReq::from_str(&text) {
      Ok(req) => Ok(req),
      Err(err) => Err(serde::de::Error::custom(err)),
    }
  }
}

impl PartialOrd for NpmPackageReq {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

// Sort the package requirements alphabetically then the version
// requirement in a way that will lead to the least number of
// duplicate packages (so sort None last since it's `*`), but
// mostly to create some determinism around how these are resolved.
impl Ord for NpmPackageReq {
  fn cmp(&self, other: &Self) -> Ordering {
    fn cmp_specifier_version_req(a: &VersionReq, b: &VersionReq) -> Ordering {
      match a.tag() {
        Some(a_tag) => match b.tag() {
          Some(b_tag) => b_tag.cmp(a_tag), // sort descending
          None => Ordering::Less,          // prefer a since tag
        },
        None => {
          match b.tag() {
            Some(_) => Ordering::Greater, // prefer b since tag
            None => {
              // At this point, just sort by text descending.
              // We could maybe be a bit smarter here in the future.
              b.to_string().cmp(&a.to_string())
            }
          }
        }
      }
    }

    match self.name.cmp(&other.name) {
      Ordering::Equal => {
        panic!("STOP");
        cmp_specifier_version_req(&self.version_req, &other.version_req)
      }
      ordering => ordering,
    }
  }
}

#[cfg(test)]
mod tests {
  use pretty_assertions::assert_eq;
  use std::cmp::Ordering;

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
  fn npm_package_nv_ref() {
    let package_nv_ref =
      NpmPackageNvReference::from_str("npm:package@1.2.3/test").unwrap();
    assert_eq!(
      package_nv_ref,
      NpmPackageNvReference {
        nv: NpmPackageNv {
          name: "package".to_string(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: Some("test".to_string())
      }
    );
    assert_eq!(
      package_nv_ref.as_specifier().as_str(),
      "npm:package@1.2.3/test"
    );

    // no path
    let package_nv_ref =
      NpmPackageNvReference::from_str("npm:package@1.2.3").unwrap();
    assert_eq!(
      package_nv_ref,
      NpmPackageNvReference {
        nv: NpmPackageNv {
          name: "package".to_string(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: None
      }
    );
    assert_eq!(package_nv_ref.as_specifier().as_str(), "npm:package@1.2.3");
  }

  #[test]
  fn parse_npm_package_req_ref() {
    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test@1").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "@package/test".to_string(),
          version_req: VersionReq::parse_from_specifier("1").unwrap(),
        },
        sub_path: None,
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test@~1.1/sub_path")
        .unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "@package/test".to_string(),
          version_req: VersionReq::parse_from_specifier("~1.1").unwrap(),
        },
        sub_path: Some("sub_path".to_string()),
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test/sub_path").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".to_string()),
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test@^1.2").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "test".to_string(),
          version_req: VersionReq::parse_from_specifier("^1.2").unwrap(),
        },
        sub_path: None,
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:test@~1.1/sub_path").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "test".to_string(),
          version_req: VersionReq::parse_from_specifier("~1.1").unwrap(),
        },
        sub_path: Some("sub_path".to_string()),
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package/test/sub_path").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".to_string()),
      }
    );

    assert_eq!(
      NpmPackageReqReference::from_str("npm:@package")
        .err()
        .unwrap()
        .to_string(),
      "Not a valid package: @package"
    );

    // should parse leading slash
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/@package/test/sub_path").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "@package/test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: Some("sub_path".to_string()),
      }
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/test").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      }
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/test/").unwrap(),
      NpmPackageReqReference {
        req: NpmPackageReq {
          name: "test".to_string(),
          version_req: WILDCARD_VERSION_REQ.clone(),
        },
        sub_path: None,
      }
    );

    // should error for no name
    assert_eq!(
      NpmPackageReqReference::from_str("npm:/")
        .err()
        .unwrap()
        .to_string(),
      "Invalid npm specifier 'npm:/'. Did not contain a package name."
    );
    assert_eq!(
      NpmPackageReqReference::from_str("npm://test")
        .err()
        .unwrap()
        .to_string(),
      "Invalid npm specifier 'npm://test'. Did not contain a package name."
    );
  }

  #[test]
  fn serialize_deserialize_package_req() {
    let package_req = NpmPackageReq::from_str("test@^1.0").unwrap();
    let json = serde_json::to_string(&package_req).unwrap();
    assert_eq!(json, "\"test@^1.0\"");
    let result = serde_json::from_str::<NpmPackageReq>(&json).unwrap();
    assert_eq!(result, package_req);
  }

  #[test]
  fn sorting_package_reqs() {
    fn cmp_req(a: &str, b: &str) -> Ordering {
      let a = NpmPackageReq::from_str(a).unwrap();
      let b = NpmPackageReq::from_str(b).unwrap();
      a.cmp(&b)
    }

    // sort by name
    assert_eq!(cmp_req("a", "b@1"), Ordering::Less);
    assert_eq!(cmp_req("b@1", "a"), Ordering::Greater);
    // prefer non-wildcard
    assert_eq!(cmp_req("a", "a@1"), Ordering::Greater);
    assert_eq!(cmp_req("a@1", "a"), Ordering::Less);
    // prefer tag
    assert_eq!(cmp_req("a@tag", "a"), Ordering::Less);
    assert_eq!(cmp_req("a", "a@tag"), Ordering::Greater);
    // sort tag descending
    assert_eq!(cmp_req("a@latest-v1", "a@latest-v2"), Ordering::Greater);
    assert_eq!(cmp_req("a@latest-v2", "a@latest-v1"), Ordering::Less);
    // sort version req descending
    assert_eq!(cmp_req("a@1", "a@2"), Ordering::Greater);
    assert_eq!(cmp_req("a@2", "a@1"), Ordering::Less);
  }
}
