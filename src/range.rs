// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use std::cmp::Ordering;

use serde::Deserialize;
use serde::Serialize;

use super::Version;

/// Collection of ranges.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VersionRangeSet(pub Vec<VersionRange>);

impl VersionRangeSet {
  pub fn satisfies(&self, version: &Version) -> bool {
    self.0.iter().any(|r| r.satisfies(version))
  }

  /// Gets if this set overlaps the other set.
  pub fn intersects_set(&self, other: &VersionRangeSet) -> bool {
    self
      .0
      .iter()
      .any(|a| other.0.iter().any(|b| a.intersects_range(b)))
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RangeBound {
  Version(VersionBound),
  Unbounded, // matches everything
}

impl RangeBound {
  pub fn inclusive(version: Version) -> Self {
    Self::version(VersionBoundKind::Inclusive, version)
  }

  pub fn exclusive(version: Version) -> Self {
    Self::version(VersionBoundKind::Exclusive, version)
  }

  pub fn version(kind: VersionBoundKind, version: Version) -> Self {
    Self::Version(VersionBound::new(kind, version))
  }

  pub fn clamp_start(&self, other: &RangeBound) -> RangeBound {
    match &self {
      RangeBound::Unbounded => other.clone(),
      RangeBound::Version(self_bound) => RangeBound::Version(match &other {
        RangeBound::Unbounded => self_bound.clone(),
        RangeBound::Version(other_bound) => {
          match self_bound.version.cmp(&other_bound.version) {
            Ordering::Greater => self_bound.clone(),
            Ordering::Less => other_bound.clone(),
            Ordering::Equal => match self_bound.kind {
              VersionBoundKind::Exclusive => self_bound.clone(),
              VersionBoundKind::Inclusive => other_bound.clone(),
            },
          }
        }
      }),
    }
  }

  pub fn clamp_end(&self, other: &RangeBound) -> RangeBound {
    match &self {
      RangeBound::Unbounded => other.clone(),
      RangeBound::Version(self_bound) => {
        RangeBound::Version(match other {
          RangeBound::Unbounded => self_bound.clone(),
          RangeBound::Version(other_bound) => {
            match self_bound.version.cmp(&other_bound.version) {
              // difference with above is the next two lines are switched
              Ordering::Greater => other_bound.clone(),
              Ordering::Less => self_bound.clone(),
              Ordering::Equal => match self_bound.kind {
                VersionBoundKind::Exclusive => self_bound.clone(),
                VersionBoundKind::Inclusive => other_bound.clone(),
              },
            }
          }
        })
      }
    }
  }

  pub fn has_pre_with_exact_major_minor_patch(
    &self,
    version: &Version,
  ) -> bool {
    if let RangeBound::Version(self_version) = &self {
      if !self_version.version.pre.is_empty()
        && self_version.version.major == version.major
        && self_version.version.minor == version.minor
        && self_version.version.patch == version.patch
      {
        return true;
      }
    }
    false
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum VersionBoundKind {
  Inclusive,
  Exclusive,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VersionBound {
  pub kind: VersionBoundKind,
  pub version: Version,
}

impl VersionBound {
  pub fn new(kind: VersionBoundKind, version: Version) -> Self {
    Self { kind, version }
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VersionRange {
  pub start: RangeBound,
  pub end: RangeBound,
}

impl VersionRange {
  pub fn all() -> VersionRange {
    VersionRange {
      start: RangeBound::Unbounded,
      end: RangeBound::Unbounded,
    }
  }

  pub fn none() -> VersionRange {
    VersionRange {
      start: RangeBound::Version(VersionBound {
        kind: VersionBoundKind::Inclusive,
        version: Version::default(),
      }),
      end: RangeBound::Version(VersionBound {
        kind: VersionBoundKind::Exclusive,
        version: Version::default(),
      }),
    }
  }

  /// If this range won't match anything.
  pub fn is_none(&self) -> bool {
    if let RangeBound::Version(end) = &self.end {
      end.kind == VersionBoundKind::Exclusive
        && end.version.major == 0
        && end.version.minor == 0
        && end.version.patch == 0
    } else {
      false
    }
  }

  pub fn satisfies(&self, version: &Version) -> bool {
    let satisfies = self.min_satisfies(version) && self.max_satisfies(version);
    if satisfies && !version.pre.is_empty() {
      // check either side of the range has a pre and same version
      self.start.has_pre_with_exact_major_minor_patch(version)
        || self.end.has_pre_with_exact_major_minor_patch(version)
    } else {
      satisfies
    }
  }

  fn min_satisfies(&self, version: &Version) -> bool {
    match &self.start {
      RangeBound::Unbounded => true,
      RangeBound::Version(bound) => match version.cmp(&bound.version) {
        Ordering::Less => false,
        Ordering::Equal => bound.kind == VersionBoundKind::Inclusive,
        Ordering::Greater => true,
      },
    }
  }

  fn max_satisfies(&self, version: &Version) -> bool {
    match &self.end {
      RangeBound::Unbounded => true,
      RangeBound::Version(bound) => match version.cmp(&bound.version) {
        Ordering::Less => true,
        Ordering::Equal => bound.kind == VersionBoundKind::Inclusive,
        Ordering::Greater => false,
      },
    }
  }

  pub fn clamp(&self, range: &VersionRange) -> VersionRange {
    let start = self.start.clamp_start(&range.start);
    let end = self.end.clamp_end(&range.end);
    let start = match start {
      RangeBound::Unbounded => start,
      // clamp the start range to the end when greater
      RangeBound::Version(_) => start.clamp_end(&end),
    };
    VersionRange { start, end }
  }

  /// Gets if this range overlaps the provided version.
  pub fn intersects_version(&self, other_version: &Version) -> bool {
    match &self.start {
      RangeBound::Unbounded => match &self.end {
        RangeBound::Unbounded => true,
        RangeBound::Version(end) => match other_version.cmp(&end.version) {
          Ordering::Less => true,
          Ordering::Equal => end.kind == VersionBoundKind::Inclusive,
          Ordering::Greater => false,
        },
      },
      RangeBound::Version(start) => match other_version.cmp(&start.version) {
        Ordering::Less => false,
        Ordering::Equal => start.kind == VersionBoundKind::Inclusive,
        Ordering::Greater => match &self.end {
          RangeBound::Unbounded => true,
          RangeBound::Version(end) => match other_version.cmp(&end.version) {
            Ordering::Less => true,
            Ordering::Equal => end.kind == VersionBoundKind::Inclusive,
            Ordering::Greater => false,
          },
        },
      },
    }
  }

  /// Gets if this range overlaps the provided range at any point.
  pub fn intersects_range(&self, other_range: &VersionRange) -> bool {
    fn is_less_than_or_equal(a: &VersionBound, b: &VersionBound) -> bool {
      // note: we've picked the bounds "exclusive 3.0.0" and "inclusive 3.0.0" to always
      // return false for the purposes of this function and that's why this is internal
      // code. Due to this scenario, I don't believe it would make sense to move this
      // to a PartialOrd or Ord impl
      match a.kind {
        VersionBoundKind::Inclusive => match b.kind {
          VersionBoundKind::Inclusive => {
            matches!(
              a.version.cmp(&b.version),
              Ordering::Less | Ordering::Equal
            )
          }
          VersionBoundKind::Exclusive => match a.version.cmp(&b.version) {
            Ordering::Equal => false,
            ordering => matches!(ordering, Ordering::Less | Ordering::Equal),
          },
        },
        VersionBoundKind::Exclusive => match b.kind {
          VersionBoundKind::Inclusive => match a.version.cmp(&b.version) {
            Ordering::Equal => false,
            ordering => matches!(ordering, Ordering::Less | Ordering::Equal),
          },
          VersionBoundKind::Exclusive => match a.version.cmp(&b.version) {
            Ordering::Equal => false,
            ordering => matches!(ordering, Ordering::Less | Ordering::Equal),
          },
        },
      }
    }

    use RangeBound::*;

    match (&self.start, &self.end, &other_range.start, &other_range.end) {
      // either range is entirely unbounded
      (Unbounded, Unbounded, _, _) | (_, _, Unbounded, Unbounded) => true,
      // first range is unbounded on the left
      (Unbounded, Version(self_end), Version(range_start), _) => {
        is_less_than_or_equal(range_start, self_end)
      }
      // first range is unbounded on the right
      (Version(self_start), Unbounded, _, Version(range_end)) => {
        is_less_than_or_equal(self_start, range_end)
      }
      // second range is unbounded on the left
      (Version(self_start), _, Unbounded, Version(range_end)) => {
        is_less_than_or_equal(self_start, range_end)
      }
      // second range is unbounded on the right
      (_, Version(self_end), Version(range_start), Unbounded) => {
        is_less_than_or_equal(range_start, self_end)
      }
      // both versions are unbounded on the left
      (Unbounded, Version(self_end), Unbounded, Version(range_end)) => {
        is_less_than_or_equal(range_end, self_end)
      }
      // both versions are unbounded on the right
      (Version(self_start), Unbounded, Version(range_start), Unbounded) => {
        is_less_than_or_equal(self_start, range_start)
      }
      // Compare exact VersionBounds for both ranges
      (
        Version(self_start),
        Version(self_end),
        Version(range_start),
        Version(range_end),
      ) => {
        is_less_than_or_equal(self_start, range_end)
          && is_less_than_or_equal(range_start, self_end)
      }
    }
  }
}

/// A range that could be a wildcard or number value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum XRange {
  Wildcard,
  Val(u64),
}

/// A partial version.
#[derive(Debug, Clone)]
pub struct Partial {
  pub major: XRange,
  pub minor: XRange,
  pub patch: XRange,
  pub pre: Vec<String>,
  pub build: Vec<String>,
}

impl Partial {
  pub fn as_tilde_version_range(&self) -> VersionRange {
    // tilde ranges allow patch-level changes
    let end = match self.major {
      XRange::Wildcard => return VersionRange::all(),
      XRange::Val(major) => match self.minor {
        XRange::Wildcard => Version {
          major: major + 1,
          minor: 0,
          patch: 0,
          pre: Vec::new(),
          build: Vec::new(),
        },
        XRange::Val(minor) => Version {
          major,
          minor: minor + 1,
          patch: 0,
          pre: Vec::new(),
          build: Vec::new(),
        },
      },
    };
    VersionRange {
      start: self.as_lower_bound(),
      end: RangeBound::exclusive(end),
    }
  }

  pub fn as_caret_version_range(&self) -> VersionRange {
    // partial ranges allow patch and minor updates, except when
    // leading parts are < 1 in which case it will only bump the
    // first non-zero or patch part
    let end = match self.major {
      XRange::Wildcard => return VersionRange::all(),
      XRange::Val(major) => {
        let next_major = Version {
          major: major + 1,
          ..Default::default()
        };
        if major > 0 {
          next_major
        } else {
          match self.minor {
            XRange::Wildcard => next_major,
            XRange::Val(minor) => {
              let next_minor = Version {
                minor: minor + 1,
                ..Default::default()
              };
              if minor > 0 {
                next_minor
              } else {
                match self.patch {
                  XRange::Wildcard => next_minor,
                  XRange::Val(patch) => Version {
                    patch: patch + 1,
                    ..Default::default()
                  },
                }
              }
            }
          }
        }
      }
    };
    VersionRange {
      start: self.as_lower_bound(),
      end: RangeBound::Version(VersionBound {
        kind: VersionBoundKind::Exclusive,
        version: end,
      }),
    }
  }

  pub fn as_lower_bound(&self) -> RangeBound {
    RangeBound::inclusive(Version {
      major: match self.major {
        XRange::Val(val) => val,
        XRange::Wildcard => 0,
      },
      minor: match self.minor {
        XRange::Val(val) => val,
        XRange::Wildcard => 0,
      },
      patch: match self.patch {
        XRange::Val(val) => val,
        XRange::Wildcard => 0,
      },
      pre: self.pre.clone(),
      build: self.build.clone(),
    })
  }

  pub fn as_upper_bound(&self) -> RangeBound {
    let mut end = Version::default();
    let mut kind = VersionBoundKind::Inclusive;
    match self.patch {
      XRange::Wildcard => {
        end.minor += 1;
        kind = VersionBoundKind::Exclusive;
      }
      XRange::Val(val) => {
        end.patch = val;
      }
    }
    match self.minor {
      XRange::Wildcard => {
        end.minor = 0;
        end.major += 1;
        kind = VersionBoundKind::Exclusive;
      }
      XRange::Val(val) => {
        end.minor += val;
      }
    }
    match self.major {
      XRange::Wildcard => {
        return RangeBound::Unbounded;
      }
      XRange::Val(val) => {
        end.major += val;
      }
    }

    if kind == VersionBoundKind::Inclusive {
      end.pre = self.pre.clone();
    }

    RangeBound::version(kind, end)
  }

  pub fn as_equal_range(&self) -> VersionRange {
    let major = match self.major {
      XRange::Wildcard => {
        return self.as_greater_range(VersionBoundKind::Inclusive)
      }
      XRange::Val(val) => val,
    };
    let minor = match self.minor {
      XRange::Wildcard => {
        return self.as_greater_range(VersionBoundKind::Inclusive)
      }
      XRange::Val(val) => val,
    };
    let patch = match self.patch {
      XRange::Wildcard => {
        return self.as_greater_range(VersionBoundKind::Inclusive)
      }
      XRange::Val(val) => val,
    };
    let version = Version {
      major,
      minor,
      patch,
      pre: self.pre.clone(),
      build: self.build.clone(),
    };
    VersionRange {
      start: RangeBound::inclusive(version.clone()),
      end: RangeBound::inclusive(version),
    }
  }

  pub fn as_greater_than(
    &self,
    mut start_kind: VersionBoundKind,
  ) -> VersionRange {
    let major = match self.major {
      XRange::Wildcard => match start_kind {
        VersionBoundKind::Inclusive => return VersionRange::all(),
        VersionBoundKind::Exclusive => return VersionRange::none(),
      },
      XRange::Val(major) => major,
    };
    let mut start = Version::default();

    if start_kind == VersionBoundKind::Inclusive {
      start.pre = self.pre.clone();
    }

    start.major = major;
    match self.minor {
      XRange::Wildcard => {
        if start_kind == VersionBoundKind::Exclusive {
          start_kind = VersionBoundKind::Inclusive;
          start.major += 1;
        }
      }
      XRange::Val(minor) => {
        start.minor = minor;
      }
    }
    match self.patch {
      XRange::Wildcard => {
        if start_kind == VersionBoundKind::Exclusive {
          start_kind = VersionBoundKind::Inclusive;
          start.minor += 1;
        }
      }
      XRange::Val(patch) => {
        start.patch = patch;
      }
    }

    VersionRange {
      start: RangeBound::version(start_kind, start),
      end: RangeBound::Unbounded,
    }
  }

  pub fn as_less_than(&self, mut end_kind: VersionBoundKind) -> VersionRange {
    let major = match self.major {
      XRange::Wildcard => match end_kind {
        VersionBoundKind::Inclusive => return VersionRange::all(),
        VersionBoundKind::Exclusive => return VersionRange::none(),
      },
      XRange::Val(major) => major,
    };
    let mut end = Version {
      major,
      ..Default::default()
    };
    match self.minor {
      XRange::Wildcard => {
        if end_kind == VersionBoundKind::Inclusive {
          end.major += 1;
        }
        end_kind = VersionBoundKind::Exclusive;
      }
      XRange::Val(minor) => {
        end.minor = minor;
      }
    }
    match self.patch {
      XRange::Wildcard => {
        if end_kind == VersionBoundKind::Inclusive {
          end.minor += 1;
        }
        end_kind = VersionBoundKind::Exclusive;
      }
      XRange::Val(patch) => {
        end.patch = patch;
      }
    }
    if end_kind == VersionBoundKind::Inclusive {
      end.pre = self.pre.clone();
    }
    VersionRange {
      // doesn't include 0.0.0 pre-release versions
      start: RangeBound::Version(VersionBound {
        kind: VersionBoundKind::Inclusive,
        version: Version::default(),
      }),
      end: RangeBound::version(end_kind, end),
    }
  }

  pub fn as_greater_range(&self, start_kind: VersionBoundKind) -> VersionRange {
    let major = match self.major {
      XRange::Wildcard => return VersionRange::all(),
      XRange::Val(major) => major,
    };
    let mut start = Version::default();
    let mut end = Version::default();
    start.major = major;
    end.major = major;
    match self.patch {
      XRange::Wildcard => {
        if self.minor != XRange::Wildcard {
          end.minor += 1;
        }
      }
      XRange::Val(patch) => {
        start.patch = patch;
        end.patch = patch;
      }
    }
    match self.minor {
      XRange::Wildcard => {
        end.major += 1;
      }
      XRange::Val(minor) => {
        start.minor = minor;
        end.minor += minor;
      }
    }
    let end_kind = if start_kind == VersionBoundKind::Inclusive && start == end
    {
      VersionBoundKind::Inclusive
    } else {
      VersionBoundKind::Exclusive
    };
    VersionRange {
      start: RangeBound::version(start_kind, start),
      end: RangeBound::version(end_kind, end),
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn test_version_range_intersects_version() {
    let v1 = Version::parse_standard("1.0.0").unwrap();
    let v1_5 = Version::parse_standard("1.5.0").unwrap();
    let v2 = Version::parse_standard("2.0.0").unwrap();
    let v3 = Version::parse_standard("3.0.0").unwrap();
    let v0_5 = Version::parse_standard("0.5.0").unwrap();
    let range_1_incl_2_incl = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "1.0.0"),
      end: version_bound(VersionBoundKind::Inclusive, "2.0.0"),
    };
    let range_1_incl_2_excl = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "1.0.0"),
      end: version_bound(VersionBoundKind::Exclusive, "2.0.0"),
    };
    let range_1_excl_2_incl = VersionRange {
      start: version_bound(VersionBoundKind::Exclusive, "1.0.0"),
      end: version_bound(VersionBoundKind::Inclusive, "2.0.0"),
    };
    let range_unbounded_2_incl = VersionRange {
      start: RangeBound::Unbounded,
      end: version_bound(VersionBoundKind::Inclusive, "2.0.0"),
    };
    let range_1_incl_unbounded = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "1.0.0"),
      end: RangeBound::Unbounded,
    };

    assert!(range_1_incl_2_incl.intersects_version(&v1));
    assert!(range_1_incl_2_incl.intersects_version(&v2));
    assert!(range_1_incl_2_excl.intersects_version(&v1_5));
    assert!(!range_1_incl_2_excl.intersects_version(&v2));
    assert!(!range_1_excl_2_incl.intersects_version(&v1));
    assert!(range_unbounded_2_incl.intersects_version(&v0_5));
    assert!(range_1_incl_unbounded.intersects_version(&v1));
    assert!(range_1_incl_unbounded.intersects_version(&v3));
  }

  #[test]
  fn test_version_range_intersects_range() {
    let range_1_incl_2_incl = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "1.0.0"),
      end: version_bound(VersionBoundKind::Inclusive, "2.0.0"),
    };
    let range_1_incl_3_excl = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "1.0.0"),
      end: version_bound(VersionBoundKind::Exclusive, "3.0.0"),
    };
    let range_2_incl_3_incl = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "2.0.0"),
      end: version_bound(VersionBoundKind::Inclusive, "3.0.0"),
    };
    let range_3_incl_unbounded = VersionRange {
      start: version_bound(VersionBoundKind::Inclusive, "3.0.0"),
      end: RangeBound::Unbounded,
    };
    let range_unbounded_2_excl = VersionRange {
      start: RangeBound::Unbounded,
      end: version_bound(VersionBoundKind::Exclusive, "2.0.0"),
    };
    let range_2_excl_3_excl = VersionRange {
      start: version_bound(VersionBoundKind::Exclusive, "2.0.0"),
      end: version_bound(VersionBoundKind::Exclusive, "3.0.0"),
    };
    let range_3_excl_4_incl = VersionRange {
      start: version_bound(VersionBoundKind::Exclusive, "3.0.0"),
      end: version_bound(VersionBoundKind::Inclusive, "4.0.0"),
    };

    // overlapping cases
    assert!(range_1_incl_2_incl.intersects_range(&range_1_incl_3_excl));
    assert!(range_1_incl_3_excl.intersects_range(&range_2_incl_3_incl));
    assert!(range_3_incl_unbounded.intersects_range(&range_2_incl_3_incl));
    assert!(range_1_incl_2_incl.intersects_range(&range_unbounded_2_excl));

    // non-overlapping cases
    assert!(!range_1_incl_2_incl.intersects_range(&range_3_incl_unbounded));
    assert!(!range_unbounded_2_excl.intersects_range(&range_2_incl_3_incl));
    assert!(!range_unbounded_2_excl.intersects_range(&range_3_incl_unbounded));
    assert!(!range_2_excl_3_excl.intersects_range(&range_3_excl_4_incl));
  }

  fn version_bound(kind: VersionBoundKind, ver: &str) -> RangeBound {
    RangeBound::Version(VersionBound {
      kind,
      version: Version::parse_standard(ver).unwrap(),
    })
  }
}
