// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use std::cmp::Ordering;
use std::fmt;
use std::hash::Hash;

use once_cell::sync::Lazy;
use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;

pub mod jsr;
pub mod npm;
pub mod package;
mod range;
mod specifier;

pub use self::specifier::VersionReqSpecifierParseError;

pub use self::range::Partial;
pub use self::range::VersionBoundKind;
pub use self::range::VersionRange;
pub use self::range::VersionRangeSet;
pub use self::range::XRange;

/// Specifier that points to the wildcard version.
pub static WILDCARD_VERSION_REQ: Lazy<VersionReq> =
  Lazy::new(|| VersionReq::parse_from_specifier("*").unwrap());

#[derive(Error, Debug, Clone)]
#[error("Invalid version. {source}")]
pub struct VersionParseError {
  #[source]
  source: monch::ParseErrorFailureError,
}

#[derive(Clone, Debug, PartialEq, Eq, Default, Hash)]
pub struct Version {
  pub major: u64,
  pub minor: u64,
  pub patch: u64,
  pub pre: Vec<String>,
  pub build: Vec<String>,
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
    let text = String::deserialize(deserializer)?;
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
}

impl fmt::Display for Version {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
    if !self.pre.is_empty() {
      write!(f, "-")?;
      for (i, part) in self.pre.iter().enumerate() {
        if i > 0 {
          write!(f, ".")?;
        }
        write!(f, "{part}")?;
      }
    }
    if !self.build.is_empty() {
      write!(f, "+")?;
      for (i, part) in self.build.iter().enumerate() {
        if i > 0 {
          write!(f, ".")?;
        }
        write!(f, "{part}")?;
      }
    }
    Ok(())
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
            return a_num.cmp(&b_num);
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RangeSetOrTag {
  RangeSet(VersionRangeSet),
  Tag(String),
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
  raw_text: String,
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
    raw_text: String,
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

  #[deprecated(note = "check for range first, then use satisfies")]
  pub fn matches(&self, version: &Version) -> bool {
    match &self.inner {
      RangeSetOrTag::RangeSet(range_set) => range_set.satisfies(version),
      // It's not safe to use `.matches()` with a VersionReq because the tag
      // might not be resolved yet. We might want to create a `ResolvedVersionReq`
      // that has the tag resolved or think of something better here
      RangeSetOrTag::Tag(_) => panic!(
        "programming error: cannot use matches with a tag: {}",
        self.raw_text
      ),
    }
  }

  pub fn version_text(&self) -> &str {
    &self.raw_text
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
}
