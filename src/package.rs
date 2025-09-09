// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use capacity_builder::CapacityDisplay;
use capacity_builder::StringAppendable;
use capacity_builder::StringBuilder;
use capacity_builder::StringType;
use deno_error::JsError;
use monch::ParseErrorFailure;
use serde::Deserialize;
use serde::Serialize;
use std::borrow::Cow;
use std::cmp::Ordering;
use thiserror::Error;
use url::Url;

use crate::RangeSetOrTag;
use crate::Version;
use crate::VersionBoundKind;
use crate::VersionRange;
use crate::VersionRangeSet;
use crate::VersionReq;
use crate::VersionReqSpecifierParseError;
use crate::WILDCARD_VERSION_REQ;
use crate::npm::NpmVersionReqParseError;
use crate::range::RangeBound;
use crate::range::VersionBound;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum PackageKind {
  Jsr,
  Npm,
}

impl PackageKind {
  pub fn scheme_with_colon(self) -> &'static str {
    match self {
      Self::Jsr => "jsr:",
      Self::Npm => "npm:",
    }
  }
}

#[derive(Error, Debug, Clone, JsError, PartialEq, Eq)]
pub enum PackageReqReferenceParseError {
  #[class(type)]
  #[error("Not {} specifier", .0.scheme_with_colon())]
  NotExpectedScheme(PackageKind),
  #[class(inherit)]
  #[error(transparent)]
  Invalid(Box<PackageReqReferenceInvalidParseError>),
  #[class(inherit)]
  #[error(transparent)]
  InvalidPathWithVersion(Box<PackageReqReferenceInvalidWithVersionParseError>),
}

#[derive(Error, Debug, Clone, JsError, PartialEq, Eq)]
#[class(type)]
#[error("Invalid package specifier '{specifier}'")]
pub struct PackageReqReferenceInvalidParseError {
  pub specifier: String,
  #[source]
  pub source: PackageReqPartsParseError,
}

#[derive(Error, Debug, Clone, JsError, PartialEq, Eq)]
#[class(type)]
#[error("Invalid package specifier '{0}{1}'. Did you mean to write '{0}{2}'? If not, add a version requirement to the specifier.", .kind.scheme_with_colon(), current, suggested)]
pub struct PackageReqReferenceInvalidWithVersionParseError {
  pub kind: PackageKind,
  pub current: String,
  pub suggested: String,
}

/// A reference to a package's name, version constraint, and potential sub path.
///
/// This contains all the information found in a package specifier other than
/// what kind of package specifier it was.
#[derive(Clone, Debug, PartialEq, Eq, Hash, CapacityDisplay)]
pub struct PackageReqReference {
  pub req: PackageReq,
  pub sub_path: Option<PackageSubPath>,
}

impl<'a> StringAppendable<'a> for &'a PackageReqReference {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    builder.append(&self.req);
    if let Some(sub_path) = &self.sub_path {
      builder.append('/');
      builder.append(sub_path);
    }
  }
}

impl PackageReqReference {
  #[allow(clippy::should_implement_trait)]
  pub(crate) fn from_str(
    specifier: &str,
    kind: PackageKind,
  ) -> Result<Self, PackageReqReferenceParseError> {
    let original_text = specifier;
    let input = match specifier.strip_prefix(kind.scheme_with_colon()) {
      Some(input) => input,
      None => {
        // this is hit a lot when a url is not the expected scheme
        // so ensure nothing heavy occurs before this
        return Err(PackageReqReferenceParseError::NotExpectedScheme(kind));
      }
    };
    let (req, sub_path) = match PackageReq::parse_with_path_strict(input) {
      Ok(pkg_req) => pkg_req,
      Err(err) => {
        return Err(PackageReqReferenceParseError::Invalid(Box::new(
          PackageReqReferenceInvalidParseError {
            specifier: original_text.to_string(),
            source: err,
          },
        )));
      }
    };
    let sub_path = if sub_path.is_empty() || sub_path == "/" {
      None
    } else {
      Some(PackageSubPath::from_str(sub_path))
    };

    if let Some(sub_path) = &sub_path
      && req.version_req.version_text() == "*"
      && let Some(at_index) = sub_path.rfind('@')
    {
      let (new_sub_path, version) = sub_path.split_at(at_index);
      return Err(PackageReqReferenceParseError::InvalidPathWithVersion(
        Box::new(PackageReqReferenceInvalidWithVersionParseError {
          kind,
          current: format!("{req}/{sub_path}"),
          suggested: format!("{req}{version}/{new_sub_path}"),
        }),
      ));
    }

    Ok(Self { req, sub_path })
  }
}

#[derive(Error, Debug, Clone, JsError, PartialEq, Eq)]
pub enum PackageReqPartsParseError {
  #[class(type)]
  #[error("Did not contain a package name")]
  NoPackageName,
  #[class(type)]
  #[error("Did not contain a valid package name")]
  InvalidPackageName,
  #[class(type)]
  #[error(
    "Packages in the format <scope>/<name> must start with an '@' symbol"
  )]
  MissingAtSymbol,
  #[class(inherit)]
  #[error(transparent)]
  SpecifierVersionReq(VersionReqSpecifierParseError),
  #[class(inherit)]
  #[error(transparent)]
  NpmVersionReq(NpmVersionReqParseError),
}

#[derive(Error, Debug, Clone, JsError)]
#[class(type)]
#[error("Invalid package requirement '{text}'")]
pub struct PackageReqParseError {
  pub text: String,
  #[source]
  pub source: PackageReqPartsParseError,
}

pub type PackageName = crate::StackString;
pub type PackageSubPath = crate::SmallStackString;

/// The name and version constraint component of an `PackageReqReference`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, CapacityDisplay)]
pub struct PackageReq {
  pub name: PackageName,
  pub version_req: VersionReq,
}

impl<'a> StringAppendable<'a> for &'a PackageReq {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    if self.version_req.version_text() == "*" {
      // do not write out the version requirement when it's the wildcard version
      builder.append(&self.name);
    } else {
      builder.append(&self.name);
      builder.append('@');
      builder.append(&self.version_req.raw_text);
    }
  }
}

impl PackageReq {
  #[allow(clippy::should_implement_trait)]
  pub fn from_str(text: &str) -> Result<Self, PackageReqParseError> {
    Self::from_str_inner(text, Self::parse_with_path_strict)
  }

  pub fn from_str_loose(text: &str) -> Result<Self, PackageReqParseError> {
    Self::from_str_inner(text, Self::parse_with_path_loose)
  }

  fn from_str_inner(
    text: &str,
    parse_with_path: impl FnOnce(
      &str,
    )
      -> Result<(Self, &str), PackageReqPartsParseError>,
  ) -> Result<Self, PackageReqParseError> {
    fn inner(
      text: &str,
      parse_with_path: impl FnOnce(
        &str,
      ) -> Result<
        (PackageReq, &str),
        PackageReqPartsParseError,
      >,
    ) -> Result<PackageReq, PackageReqPartsParseError> {
      let (req, path) = parse_with_path(text)?;
      if !path.is_empty() {
        return Err(PackageReqPartsParseError::SpecifierVersionReq(
          VersionReqSpecifierParseError {
            source: ParseErrorFailure::new(
              &text[text.len() - path.len() - 1..],
              "Unexpected character '/'",
            )
            .into_error(),
          },
        ));
      }
      Ok(req)
    }

    match inner(text, parse_with_path) {
      Ok(req) => Ok(req),
      Err(err) => Err(PackageReqParseError {
        text: text.to_string(),
        source: if !text.starts_with('@') && text.contains('/') {
          PackageReqPartsParseError::MissingAtSymbol
        } else {
          err
        },
      }),
    }
  }

  fn parse_with_path_strict(
    text: &str,
  ) -> Result<(Self, &str), PackageReqPartsParseError> {
    PackageReq::parse_with_path(text, |version| {
      VersionReq::parse_from_specifier(version)
        .map_err(PackageReqPartsParseError::SpecifierVersionReq)
    })
  }

  fn parse_with_path_loose(
    text: &str,
  ) -> Result<(Self, &str), PackageReqPartsParseError> {
    PackageReq::parse_with_path(text, |version| {
      VersionReq::parse_from_npm(version)
        .map_err(PackageReqPartsParseError::NpmVersionReq)
    })
  }

  fn parse_with_path(
    input: &str,
    parse_version_req: impl FnOnce(
      &str,
    )
      -> Result<VersionReq, PackageReqPartsParseError>,
  ) -> Result<(Self, &str), PackageReqPartsParseError> {
    // Strip leading slash, which might come from import map
    let input = input.strip_prefix('/').unwrap_or(input);
    // parse the first name part
    let (first_part, input) = input.split_once('/').unwrap_or((input, ""));
    if first_part.is_empty() {
      return Err(PackageReqPartsParseError::NoPackageName);
    }
    // if it starts with an @, parse the second name part
    let (maybe_scope, last_name_part, sub_path) = if first_part.starts_with('@')
    {
      let (second_part, input) = input.split_once('/').unwrap_or((input, ""));
      if second_part.is_empty() {
        return Err(PackageReqPartsParseError::InvalidPackageName);
      }
      (Some(first_part), second_part, input)
    } else {
      (None, first_part, input)
    };

    let (last_name_part, version_req) = if let Some((last_name_part, version)) =
      last_name_part.rsplit_once('@')
    {
      (last_name_part, Some(parse_version_req(version)?))
    } else {
      (last_name_part, None)
    };
    Ok((
      Self {
        name: match maybe_scope {
          Some(scope) => {
            let mut text = PackageName::with_capacity(
              scope.len() + 1 + last_name_part.len(),
            );
            text.push_str(scope);
            text.push('/');
            text.push_str(last_name_part);
            text
          }
          None => last_name_part.into(),
        },
        version_req: version_req
          .unwrap_or_else(|| WILDCARD_VERSION_REQ.clone()),
      },
      sub_path,
    ))
  }

  /// Outputs a normalized string representation of the package requirement.
  pub fn to_string_normalized(&self) -> crate::StackString {
    StringBuilder::build(|builder| {
      builder.append(&self.name);
      builder.append('@');
      builder.append(self.version_req.inner());
    })
    .unwrap()
  }
}

impl Serialize for PackageReq {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string_normalized())
  }
}

impl<'de> Deserialize<'de> for PackageReq {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let text: Cow<'de, str> = Deserialize::deserialize(deserializer)?;
    match Self::from_str_loose(&text) {
      Ok(req) => Ok(req),
      Err(err) => Err(serde::de::Error::custom(err)),
    }
  }
}

impl PartialOrd for PackageReq {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

// Sort the package requirements alphabetically then the version
// requirement in a way that will lead to the least number of
// duplicate packages (so sort None last since it's `*`), but
// mostly to create some determinism around how these are resolved.
impl Ord for PackageReq {
  fn cmp(&self, other: &Self) -> Ordering {
    // don't bother implementing Ord/PartialOrd on the lower level items
    // because it's not so useful and it causes them to have a `.clamp()` method
    // for Ord instead of their own defined methods
    fn cmp_version_range(a: &VersionRange, b: &VersionRange) -> Ordering {
      fn cmp_range_bound(
        a: &RangeBound,
        b: &RangeBound,
        cmp_version_bound: impl Fn(&VersionBound, &VersionBound) -> Ordering,
      ) -> Ordering {
        match (a, b) {
          (RangeBound::Unbounded, RangeBound::Unbounded) => Ordering::Equal,
          (RangeBound::Unbounded, RangeBound::Version(_)) => Ordering::Greater,
          (RangeBound::Version(_), RangeBound::Unbounded) => Ordering::Less,
          (RangeBound::Version(a), RangeBound::Version(b)) => {
            cmp_version_bound(a, b)
          }
        }
      }

      fn cmp_version_bound_kind_start(
        a: VersionBoundKind,
        b: VersionBoundKind,
      ) -> Ordering {
        match (a, b) {
          (VersionBoundKind::Inclusive, VersionBoundKind::Inclusive)
          | (VersionBoundKind::Exclusive, VersionBoundKind::Exclusive) => {
            Ordering::Equal
          }
          (VersionBoundKind::Exclusive, VersionBoundKind::Inclusive) => {
            Ordering::Less
          }
          (VersionBoundKind::Inclusive, VersionBoundKind::Exclusive) => {
            Ordering::Greater
          }
        }
      }

      fn cmp_range_bound_start(a: &RangeBound, b: &RangeBound) -> Ordering {
        cmp_range_bound(a, b, |a, b| {
          // prefer higher versions first
          match b.version.cmp(&a.version) {
            Ordering::Equal => cmp_version_bound_kind_start(a.kind, b.kind),
            ordering => ordering,
          }
        })
      }

      fn cmp_range_bound_end(a: &RangeBound, b: &RangeBound) -> Ordering {
        cmp_range_bound(a, b, |a, b| {
          // prefer lower versions first
          match a.version.cmp(&b.version) {
            Ordering::Equal => cmp_version_bound_kind_start(b.kind, a.kind), // reversed
            ordering => ordering,
          }
        })
      }

      match cmp_range_bound_start(&a.start, &b.start) {
        Ordering::Equal => cmp_range_bound_end(&a.end, &b.end),
        ordering => ordering,
      }
    }

    fn cmp_version_range_set(
      a: &VersionRangeSet,
      b: &VersionRangeSet,
    ) -> Ordering {
      for (a_item, b_item) in a.0.iter().zip(b.0.iter()) {
        match cmp_version_range(a_item, b_item) {
          Ordering::Equal => continue,
          ordering => return ordering,
        }
      }

      // prefer the one with the least number of items
      a.0.len().cmp(&b.0.len())
    }

    fn cmp_specifier_version_req(a: &VersionReq, b: &VersionReq) -> Ordering {
      // ignore the raw text as it's only for displaying to the user
      match a.inner() {
        RangeSetOrTag::Tag(a_tag) => {
          match b.inner() {
            RangeSetOrTag::Tag(b_tag) => b_tag.cmp(a_tag), // sort descending
            RangeSetOrTag::RangeSet(_) => Ordering::Less, // prefer 'a' since tag
          }
        }
        RangeSetOrTag::RangeSet(a_set) => {
          match b.inner() {
            RangeSetOrTag::Tag(_) => Ordering::Greater, // prefer 'b' since tag
            RangeSetOrTag::RangeSet(b_set) => {
              cmp_version_range_set(a_set, b_set)
            }
          }
        }
      }
    }

    // compare the name, then the version req
    match self.name.cmp(&other.name) {
      Ordering::Equal => {
        cmp_specifier_version_req(&self.version_req, &other.version_req)
      }
      ordering => ordering,
    }
  }
}

#[derive(Debug, Error, Clone, JsError)]
#[class(type)]
#[error("Invalid package name and version reference '{text}'. {message}")]
pub struct PackageNvReferenceParseError {
  pub message: String,
  pub text: String,
}

/// A package name and version with a potential subpath.
#[derive(
  Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash, CapacityDisplay,
)]
pub struct PackageNvReference {
  pub nv: PackageNv,
  pub sub_path: Option<PackageSubPath>,
}

impl PackageNvReference {
  #[allow(clippy::should_implement_trait)]
  pub(crate) fn from_str(
    nv: &str,
    kind: PackageKind,
  ) -> Result<Self, PackageNvReferenceParseError> {
    use monch::*;

    fn sub_path(input: &str) -> ParseResult<'_, &str> {
      let (input, _) = ch('/')(input)?;
      Ok(("", input))
    }

    fn parse_ref<'a>(
      kind: PackageKind,
    ) -> impl Fn(&'a str) -> ParseResult<'a, PackageNvReference> {
      move |input| {
        let (input, _) = tag(kind.scheme_with_colon())(input)?;
        let (input, _) = maybe(ch('/'))(input)?;
        let (input, nv) = parse_nv(input)?;
        let (input, maybe_sub_path) = maybe(sub_path)(input)?;
        Ok((
          input,
          PackageNvReference {
            nv,
            sub_path: maybe_sub_path.map(PackageSubPath::from_str),
          },
        ))
      }
    }

    with_failure_handling(parse_ref(kind))(nv).map_err(|err| {
      PackageNvReferenceParseError {
        message: format!("{err:#}"),
        text: nv.to_string(),
      }
    })
  }

  pub(crate) fn as_specifier(&self, kind: PackageKind) -> Url {
    let text = StringBuilder::<String>::build(|builder| {
      builder.append(kind.scheme_with_colon());
      builder.append('/');
      builder.append(&self.nv.name);
      builder.append('@');
      builder.append(&self.nv.version);
      if let Some(sub_path) = &self.sub_path {
        builder.append('/');
        builder.append(sub_path);
      }
    })
    .unwrap();
    Url::parse(&text).unwrap()
  }
}

impl<'a> StringAppendable<'a> for &'a PackageNvReference {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    builder.append(&self.nv);
    if let Some(sub_path) = &self.sub_path {
      builder.append('/');
      builder.append(sub_path);
    }
  }
}

#[derive(Debug, Error, Clone, JsError)]
#[class(type)]
#[error("Invalid package name and version '{text}'. {message}")]
pub struct PackageNvParseError {
  pub message: String,
  pub text: String,
}

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash, CapacityDisplay)]
pub struct PackageNv {
  pub name: PackageName,
  pub version: Version,
}

impl std::fmt::Debug for PackageNv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // when debugging, it's easier to compare this
    write!(f, "{}@{}", self.name, self.version)
  }
}

impl<'a> StringAppendable<'a> for &'a PackageNv {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    builder.append(&self.name);
    builder.append('@');
    builder.append(&self.version);
  }
}

impl Serialize for PackageNv {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for PackageNv {
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

impl PackageNv {
  #[allow(clippy::should_implement_trait)]
  pub fn from_str(nv: &str) -> Result<Self, PackageNvParseError> {
    monch::with_failure_handling(parse_nv)(nv).map_err(|err| {
      PackageNvParseError {
        message: format!("{err:#}"),
        text: nv.to_string(),
      }
    })
  }

  pub fn scope(&self) -> Option<&str> {
    if self.name.starts_with('@') {
      self.name.as_str().split('/').next()
    } else {
      None
    }
  }

  /// Converts the package nv into a package requirement.
  pub fn into_req(self) -> PackageReq {
    PackageReq {
      name: self.name,
      version_req: self.version.into_req(),
    }
  }
}

fn parse_nv(input: &str) -> monch::ParseResult<'_, PackageNv> {
  use monch::*;

  fn parse_name(input: &str) -> ParseResult<'_, &str> {
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

  fn parse_version(input: &str) -> ParseResult<'_, &str> {
    if_not_empty(substring(skip_while(|c| !matches!(c, '_' | '/'))))(input)
  }

  let (input, name) = parse_name(input)?;
  let (input, _) = ch('@')(input)?;
  let at_version_input = input;
  let (input, version) = parse_version(input)?;
  match Version::parse_from_npm(version) {
    Ok(version) => Ok((
      input,
      PackageNv {
        name: name.into(),
        version,
      },
    )),
    Err(err) => ParseError::fail(at_version_input, format!("{err:#}")),
  }
}

#[cfg(test)]
mod test {
  use std::cmp::Ordering;

  use crate::package::PackageReq;

  #[test]
  fn serialize_deserialize_package_req() {
    let package_req = PackageReq::from_str("test@^1.0").unwrap();
    let json = serde_json::to_string(&package_req).unwrap();
    assert_eq!(json, "\"test@1\"");
    let result = serde_json::from_str::<PackageReq>(&json).unwrap();
    assert_eq!(result, package_req);
  }

  #[test]
  fn sorting_package_reqs() {
    fn cmp_req(a: &str, b: &str) -> Ordering {
      let a = PackageReq::from_str_loose(a).unwrap();
      let b = PackageReq::from_str_loose(b).unwrap();
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
    // prefer lower upper bound
    assert_eq!(cmp_req("a@3", "a@3.0.0"), Ordering::Greater);
    // prefer higher lower bound
    assert_eq!(cmp_req("a@>=3.0.0", "a@>3.0.0"), Ordering::Greater);
    assert_eq!(cmp_req("a@>=3.0.0", "a@>=3.0.0"), Ordering::Equal);
    assert_eq!(cmp_req("a@>3.0.0", "a@>=3.0.0"), Ordering::Less);
    // prefer lower upper bound (you end up with an intersection of both)
    assert_eq!(cmp_req("a@>=3.0.0 <=4", "a@>=3.0.0 <4"), Ordering::Greater);
    assert_eq!(cmp_req("a@>=3.0.0 <=4", "a@>=3.0.0 <=4"), Ordering::Equal);
    assert_eq!(cmp_req("a@>=3.0.0 <4", "a@>=3.0.0 <=4"), Ordering::Less);
    assert_eq!(cmp_req("a@>=3.0.0 <3.5", "a@>=3.0.0 <3.6"), Ordering::Less);
    // prefer one with less items when equal up to a point
    assert_eq!(cmp_req("a@>=3 || 4.x", "a@>=3 || 4.x"), Ordering::Equal);
    assert_eq!(
      cmp_req("a@>=3 || 4.x", "a@>=3 || 4.x || 5.x"),
      Ordering::Less
    );
    assert_eq!(
      cmp_req("a@>=3 || 4.x || 5.x", "a@>=3 || 4.x"),
      Ordering::Greater
    );
  }

  #[test]
  fn missing_at_symbol() {
    let err = PackageReq::from_str("scope/name").unwrap_err();
    assert!(
      matches!(
        err.source,
        crate::package::PackageReqPartsParseError::MissingAtSymbol
      ),
      "{:#}",
      err
    );
  }
}
