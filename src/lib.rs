// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

#![deny(clippy::print_stderr)]
#![deny(clippy::print_stdout)]

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::Hash;

use capacity_builder::CapacityDisplay;
use capacity_builder::StringAppendable;
use capacity_builder::StringBuilder;
use capacity_builder::StringType;
use once_cell::sync::Lazy;
use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;

pub mod jsr;
pub mod npm;
pub mod package;
mod range;
mod specifier;
mod string;

/// A smaller two-byte vector.
pub type CowVec<T> = ecow::EcoVec<T>;
pub use string::SmallStackString;
pub use string::StackString;

pub use self::specifier::VersionReqSpecifierParseError;

pub use self::range::Partial;
pub use self::range::RangeBound;
pub use self::range::VersionBound;
pub use self::range::VersionBoundKind;
pub use self::range::VersionRange;
pub use self::range::VersionRangeSet;
pub use self::range::XRange;

/// Specifier that points to the wildcard version.
pub static WILDCARD_VERSION_REQ: Lazy<VersionReq> =
  Lazy::new(|| VersionReq::parse_from_specifier("*").unwrap());

#[derive(Error, Debug, Clone, deno_error::JsError)]
#[class(type)]
#[error("Invalid version")]
pub struct VersionParseError {
  #[source]
  source: monch::ParseErrorFailureError,
}

pub type VersionPreOrBuild = SmallStackString;

#[derive(Clone, Debug, PartialEq, Eq, Default, Hash, CapacityDisplay)]
pub struct Version {
  pub major: u64,
  pub minor: u64,
  pub patch: u64,
  pub pre: CowVec<VersionPreOrBuild>,
  pub build: CowVec<VersionPreOrBuild>,
}

impl<'a> StringAppendable<'a> for &'a Version {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    builder.append(self.major);
    builder.append('.');
    builder.append(self.minor);
    builder.append('.');
    builder.append(self.patch);
    if !self.pre.is_empty() {
      builder.append('-');
      for (i, part) in self.pre.iter().enumerate() {
        if i > 0 {
          builder.append('.');
        }
        builder.append(part);
      }
    }
    if !self.build.is_empty() {
      builder.append('+');
      for (i, part) in self.build.iter().enumerate() {
        if i > 0 {
          builder.append('.');
        }
        builder.append(part);
      }
    }
  }
}

impl Serialize for Version {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for Version {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let text: Cow<'de, str> = Deserialize::deserialize(deserializer)?;
    match Version::parse_standard(&text) {
      Ok(version) => Ok(version),
      Err(err) => Err(serde::de::Error::custom(err)),
    }
  }
}

impl Version {
  /// Parse a version.
  pub fn parse_standard(text: &str) -> Result<Version, VersionParseError> {
    // re-use npm's loose version parsing
    Self::parse_from_npm(text)
      .map_err(|err| VersionParseError { source: err.source })
  }

  /// Parse a version from npm.
  pub fn parse_from_npm(
    text: &str,
  ) -> Result<Version, npm::NpmVersionParseError> {
    npm::parse_npm_version(text)
  }

  /// Creates a version requirement that's pinned to this version.
  pub fn into_req(self) -> VersionReq {
    VersionReq {
      raw_text: self.to_custom_string(),
      inner: RangeSetOrTag::RangeSet(VersionRangeSet(CowVec::from([
        VersionRange {
          start: RangeBound::Version(VersionBound {
            kind: VersionBoundKind::Inclusive,
            version: self.clone(),
          }),
          end: RangeBound::Version(VersionBound {
            kind: VersionBoundKind::Inclusive,
            version: self,
          }),
        },
      ]))),
    }
  }
}

impl std::cmp::PartialOrd for Version {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl std::cmp::Ord for Version {
  fn cmp(&self, other: &Self) -> Ordering {
    let cmp_result = self.major.cmp(&other.major);
    if cmp_result != Ordering::Equal {
      return cmp_result;
    }

    let cmp_result = self.minor.cmp(&other.minor);
    if cmp_result != Ordering::Equal {
      return cmp_result;
    }

    let cmp_result = self.patch.cmp(&other.patch);
    if cmp_result != Ordering::Equal {
      return cmp_result;
    }

    // only compare the pre-release and not the build as node-semver does
    if self.pre.is_empty() && other.pre.is_empty() {
      Ordering::Equal
    } else if !self.pre.is_empty() && other.pre.is_empty() {
      Ordering::Less
    } else if self.pre.is_empty() && !other.pre.is_empty() {
      Ordering::Greater
    } else {
      let mut i = 0;
      loop {
        let a = self.pre.get(i);
        let b = other.pre.get(i);
        if a.is_none() && b.is_none() {
          return Ordering::Equal;
        }

        // https://github.com/npm/node-semver/blob/4907647d169948a53156502867ed679268063a9f/internal/identifiers.js
        let a = match a {
          Some(a) => a,
          None => return Ordering::Less,
        };
        let b = match b {
          Some(b) => b,
          None => return Ordering::Greater,
        };

        // prefer numbers
        if let Ok(a_num) = a.parse::<u64>() {
          if let Ok(b_num) = b.parse::<u64>() {
            let cmp_result = a_num.cmp(&b_num);
            if cmp_result != Ordering::Equal {
              return cmp_result;
            }
          } else {
            return Ordering::Less;
          }
        } else if b.parse::<u64>().is_ok() {
          return Ordering::Greater;
        }

        let cmp_result = a.cmp(b);
        if cmp_result != Ordering::Equal {
          return cmp_result;
        }
        i += 1;
      }
    }
  }
}

pub(crate) fn is_valid_tag(value: &str) -> bool {
  // we use the same rules as npm tags
  npm::is_valid_npm_tag(value)
}

pub type PackageTag = SmallStackString;

#[derive(
  Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, CapacityDisplay,
)]
pub enum RangeSetOrTag {
  RangeSet(VersionRangeSet),
  Tag(PackageTag),
}

impl<'a> StringAppendable<'a> for &'a RangeSetOrTag {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    match self {
      RangeSetOrTag::RangeSet(range_set) => builder.append(range_set),
      RangeSetOrTag::Tag(tag) => builder.append(tag),
    }
  }
}

impl RangeSetOrTag {
  pub fn intersects(&self, other: &RangeSetOrTag) -> bool {
    match (self, other) {
      (RangeSetOrTag::RangeSet(a), RangeSetOrTag::RangeSet(b)) => {
        a.intersects_set(b)
      }
      (RangeSetOrTag::RangeSet(_), RangeSetOrTag::Tag(_))
      | (RangeSetOrTag::Tag(_), RangeSetOrTag::RangeSet(_)) => false,
      (RangeSetOrTag::Tag(a), RangeSetOrTag::Tag(b)) => a == b,
    }
  }
}

/// A version constraint.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VersionReq {
  raw_text: SmallStackString,
  inner: RangeSetOrTag,
}

impl PartialEq for VersionReq {
  fn eq(&self, other: &Self) -> bool {
    self.inner == other.inner
  }
}

impl Eq for VersionReq {}

impl Hash for VersionReq {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.inner.hash(state);
  }
}

impl VersionReq {
  /// Creates a version requirement without examining the raw text.
  pub fn from_raw_text_and_inner(
    raw_text: SmallStackString,
    inner: RangeSetOrTag,
  ) -> Self {
    Self { raw_text, inner }
  }

  pub fn parse_from_specifier(
    specifier: &str,
  ) -> Result<Self, VersionReqSpecifierParseError> {
    specifier::parse_version_req_from_specifier(specifier)
  }

  pub fn parse_from_npm(
    text: &str,
  ) -> Result<Self, npm::NpmVersionReqParseError> {
    npm::parse_npm_version_req(text)
  }

  /// The underlying `RangeSetOrTag`.
  pub fn inner(&self) -> &RangeSetOrTag {
    &self.inner
  }

  /// Gets if this version requirement overlaps another one.
  pub fn intersects(&self, other: &VersionReq) -> bool {
    self.inner.intersects(&other.inner)
  }

  pub fn tag(&self) -> Option<&str> {
    match &self.inner {
      RangeSetOrTag::RangeSet(_) => None,
      RangeSetOrTag::Tag(tag) => Some(tag.as_str()),
    }
  }

  pub fn range(&self) -> Option<&VersionRangeSet> {
    match &self.inner {
      RangeSetOrTag::RangeSet(range_set) => Some(range_set),
      RangeSetOrTag::Tag(_) => None,
    }
  }

  pub fn matches(&self, version: &Version) -> bool {
    match &self.inner {
      RangeSetOrTag::RangeSet(range_set) => range_set.satisfies(version),
      RangeSetOrTag::Tag(_) => panic!(
        "programming error: cannot use matches with a tag: {}",
        self.raw_text
      ),
    }
  }

  pub fn version_text(&self) -> &str {
    &self.raw_text
  }

  /// Outputs a normalized string representation of the version requirement.
  pub fn to_string_normalized(&self) -> String {
    self.inner().to_string()
  }
}

impl fmt::Display for VersionReq {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}", &self.raw_text)
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn serialize_deserialize() {
    // should deserialize and serialize with loose parsing
    let text = "= v 1.2.3-pre.other+build.test";
    let version: Version =
      serde_json::from_str(&format!("\"{text}\"")).unwrap();
    let serialized_version = serde_json::to_string(&version).unwrap();
    assert_eq!(serialized_version, "\"1.2.3-pre.other+build.test\"");
  }

  #[test]
  fn version_req_intersects() {
    let version = |text: &str| VersionReq::parse_from_npm(text).unwrap();

    // overlapping requirements
    {
      let req_1_0_0 = version("1.0.0");
      let req_caret_1 = version("^1");
      assert!(req_1_0_0.intersects(&req_caret_1)); // Both represent the 1.0.0 version.
    }
    {
      let req_1_to_3 = version(">=1 <=3");
      let req_2_to_4 = version(">=2 <=4");
      assert!(req_1_to_3.intersects(&req_2_to_4)); // They overlap in the 2.0.0 - 3.0.0 range.
    }

    // non-overlapping requirements
    {
      let req_lt_1 = version("<1");
      let req_gte_1 = version(">=1");
      assert!(!req_lt_1.intersects(&req_gte_1)); // One is less than 1.0.0, the other is 1.0.0 or greater.
    }
    {
      let req_2_to_3 = version(">=2 <3");
      let req_gte_3 = version(">=3");
      assert!(!req_2_to_3.intersects(&req_gte_3)); // Non-overlapping.
    }
    {
      let req_1_incl_2_excl = version("^1");
      let req_2_incl_unbounded = version(">=2");
      assert!(!req_1_incl_2_excl.intersects(&req_2_incl_unbounded));
    }

    // more specific requirements
    {
      let req_1_2_3 = version("1.2.3");
      let req_1_2_x = version("1.2.x");
      assert!(req_1_2_3.intersects(&req_1_2_x)); // both represent the 1.2.3 version.
    }
    {
      let req_tilde_1_2_3 = version("~1.2.3");
      let req_1_4_0 = version("1.4.0");
      assert!(!req_tilde_1_2_3.intersects(&req_1_4_0)); // no overlap with 1.4.0.
    }

    // wildcards
    {
      let req_star = version("*");
      let req_1_0_0 = version("1.0.0");
      let req_gte_1 = version(">=1");
      assert!(req_star.intersects(&req_1_0_0)); // the '*' allows any version.
      assert!(req_star.intersects(&req_gte_1)); // again, '*' allows any version.
    }
  }

  #[test]
  fn version_req_eq() {
    let p1 = VersionReq::parse_from_specifier("1").unwrap();
    let p2 = VersionReq::parse_from_specifier("1.x").unwrap();
    assert_eq!(p1, p2);
  }

  #[test]
  fn version_cmp() {
    fn cmp(v1: &str, v2: &str) -> Ordering {
      let v1 = Version::parse_standard(v1).unwrap();
      let v2 = Version::parse_standard(v2).unwrap();
      v1.cmp(&v2)
    }

    assert_eq!(cmp("1.0.0", "1.0.0-pre"), Ordering::Greater);
    assert_eq!(cmp("0.0.0", "0.0.0-pre"), Ordering::Greater);
    assert_eq!(cmp("0.0.0-a", "0.0.0-b"), Ordering::Less);
    assert_eq!(cmp("0.0.0-a", "0.0.0-a"), Ordering::Equal);
    assert_eq!(cmp("2.0.0-rc.3.0.5", "2.0.0-rc.3.0.6"), Ordering::Less);
    assert_eq!(cmp("2.0.0-rc.3.0.5", "2.0.0-rc.3.1.0"), Ordering::Less);
    assert_eq!(cmp("2.0.0-rc.3.1.0", "2.0.0-rc.3.0.5"), Ordering::Greater);
    assert_eq!(cmp("2.0.0-rc.3.1.0", "2.0.0-rc.3.1.0"), Ordering::Equal);
    assert_eq!(cmp("2.0.0-rc.3.0.5", "2.0.0"), Ordering::Less);
    assert_eq!(cmp("2.0.0-rc.3.0.5", "2.1.0"), Ordering::Less);
    assert_eq!(cmp("2.0.0", "2.0.0-rc.3.0.5"), Ordering::Greater);
  }

  #[test]
  fn version_req_from_version() {
    let version = Version::parse_from_npm("1.2.3").unwrap();
    let version_req = version.into_req();

    assert!(!version_req.matches(&Version::parse_from_npm("1.2.2").unwrap()));
    assert!(version_req.matches(&Version::parse_from_npm("1.2.3").unwrap()));
    assert!(!version_req.matches(&Version::parse_from_npm("1.2.4").unwrap()));
  }
}
