// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use std::cmp::Ordering;

use capacity_builder::FastDisplay;
use capacity_builder::StringAppendable;
use capacity_builder::StringBuilder;
use capacity_builder::StringType;
use serde::Deserialize;
use serde::Serialize;

use super::Version;

/// Collection of ranges.
#[derive(
  Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, FastDisplay,
)]
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

impl<'a> StringAppendable<'a> for &'a VersionRangeSet {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    match self.0.len() {
      0 => builder.append('*'),
      _ => {
        for (i, range) in self.0.iter().enumerate() {
          if i > 0 {
            builder.append(" || ");
          }
          builder.append(range);
        }
      }
    }
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

#[derive(
  Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize, FastDisplay,
)]
pub struct VersionRange {
  pub start: RangeBound,
  pub end: RangeBound,
}

impl<'a> StringAppendable<'a> for &'a VersionRange {
  fn append_to_builder<TString: StringType>(
    self,
    builder: &mut StringBuilder<'a, TString>,
  ) {
    fn matches_tilde(start: &Version, end: &Version) -> bool {
      if !end.build.is_empty() || !end.pre.is_empty() {
        return false;
      }

      if start.major != end.major {
        return false;
      }

      if start.minor == end.minor {
        end.patch == start.patch && !start.pre.is_empty()
      } else {
        let Some(one_minor_higher) = start.minor.checked_add(1) else {
          return false;
        };
        // ~0.1.2 is equivalent to >=0.1.2 <0.2.0
        // ~1.2.3 is equivalent to >=1.2.3 <1.3.0
        end.minor == one_minor_higher && end.patch == 0
      }
    }

    fn matches_caret(start: &Version, end: &Version) -> bool {
      if !end.build.is_empty() || !end.pre.is_empty() {
        return false;
      }

      if start.major == 0 {
        // ~0.0.x is different than ^0.0.x, so handle that
        if start.minor == 0 && end.minor == 0 {
          let Some(one_patch_higher) = start.patch.checked_add(1) else {
            return false;
          };
          return end.patch == one_patch_higher;
        }
        return false; // it will always use normalize to tilde in this case
      }

      let Some(one_major_higher) = start.major.checked_add(1) else {
        return false;
      };
      // ^1.2.3 is equivalent to >=1.2.3 <2.0.0
      end.major == one_major_higher && end.minor == 0 && end.patch == 0
    }

    fn is_zero_version(version: &Version) -> bool {
      version.major == 0
        && version.minor == 0
        && version.patch == 0
        && version.pre.is_empty()
        && version.build.is_empty()
    }

    match &self.start {
      RangeBound::Unbounded => match &self.end {
        RangeBound::Unbounded => builder.append('*'),
        RangeBound::Version(end) => match end.kind {
          VersionBoundKind::Inclusive => {
            builder.append("<=");
            builder.append(&end.version);
          }
          VersionBoundKind::Exclusive => {
            builder.append('<');
            builder.append(&end.version);
          }
        },
      },
      RangeBound::Version(start) => match &self.end {
        RangeBound::Unbounded => match start.kind {
          VersionBoundKind::Inclusive => {
            builder.append(">=");
            builder.append(&start.version);
          }
          VersionBoundKind::Exclusive => {
            builder.append('>');
            builder.append(&start.version);
          }
        },
        RangeBound::Version(end) => match (start.kind, end.kind) {
          (VersionBoundKind::Inclusive, VersionBoundKind::Inclusive) => {
            if start.version == end.version {
              builder.append(&start.version);
            } else if is_zero_version(&start.version) {
              builder.append("<=");
              builder.append(&end.version);
            } else {
              builder.append(">=");
              builder.append(&start.version);
              builder.append(" <=");
              builder.append(&end.version);
            }
          }
          (VersionBoundKind::Inclusive, VersionBoundKind::Exclusive) => {
            if end.version.patch == 0
              && start.version.patch == 0
              && end.version.pre.is_empty()
              && end.version.build.is_empty()
              && start.version.pre.is_empty()
              && start.version.build.is_empty()
            {
              // check if we can write out `^1.0.0` as `1`
              if end.version.minor == 0 && start.version.minor == 0 {
                if let Some(one_major_higher) =
                  start.version.major.checked_add(1)
                {
                  if end.version.major == one_major_higher {
                    builder.append(start.version.major);
                    return;
                  }
                }
              } else if start.version.major == end.version.major {
                // check if we can write out `~1.1.0` as `1.1`
                if let Some(one_minor_higher) =
                  start.version.minor.checked_add(1)
                {
                  if end.version.minor == one_minor_higher {
                    builder.append(start.version.major);
                    builder.append('.');
                    builder.append(start.version.minor);
                    return;
                  }
                }
              }
            }

            if matches_tilde(&start.version, &end.version) {
              builder.append('~');
              builder.append(&start.version);
            } else if matches_caret(&start.version, &end.version) {
              builder.append('^');
              builder.append(&start.version);
            } else if is_zero_version(&start.version) {
              builder.append('<');
              builder.append(&end.version);
            } else {
              builder.append(">=");
              builder.append(&start.version);
              builder.append(" <");
              builder.append(&end.version);
            }
          }
          (VersionBoundKind::Exclusive, VersionBoundKind::Inclusive) => {
            builder.append('>');
            builder.append(&start.version);
            builder.append(" <=");
            builder.append(&end.version);
          }
          (VersionBoundKind::Exclusive, VersionBoundKind::Exclusive) => {
            builder.append('>');
            builder.append(&start.version);
            builder.append(" <");
            builder.append(&end.version);
          }
        },
      },
    }
  }
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

        if !self.pre.is_empty() && start_kind == VersionBoundKind::Exclusive {
          start.pre = self.pre.clone();
        }
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

        if !self.pre.is_empty() && end_kind == VersionBoundKind::Exclusive {
          end.pre = self.pre.clone();
        }
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
  use crate::npm::parse_npm_version_req;

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

  #[test]
  fn range_set_or_tag_display() {
    #[track_caller]
    fn run_test(input: &str, expected: &str) {
      let version_req = parse_npm_version_req(input).unwrap();
      let output = version_req.inner().to_string();
      assert_eq!(output, expected);
      let reparsed = parse_npm_version_req(&output).unwrap();
      assert_eq!(reparsed.inner(), version_req.inner());
    }

    // Basic caret and tilde tests
    run_test("^0.0.1", "^0.0.1");
    run_test("^0.1.0", "0.1"); // normalizes

    // Zero major, minor, patch
    run_test("1.0.0", "1.0.0");
    run_test("1", "1");
    run_test("1.0", "1.0");
    run_test("1.2", "1.2");
    run_test("1.2.0", "1.2.0");
    run_test("^1.0.0", "1");
    run_test("~1.0.0", "1.0");
    run_test("1.1.0 - 3.1.0", ">=1.1.0 <=3.1.0");

    // Exact
    run_test("1.2.3", "1.2.3");

    // More complex caret tests
    run_test("^0.2.3", "~0.2.3"); // normalizes
    run_test("^2.3.4", "^2.3.4");

    // More complex tilde tests
    run_test("~0.2.3", "~0.2.3");
    run_test("~2.3.4", "~2.3.4");

    // Exact versions and simple ranges
    run_test("2.3.4", "2.3.4");
    run_test(">2.3.4", ">2.3.4");
    run_test(">=2.3.4", ">=2.3.4");
    run_test("<2.3.4", "<2.3.4");
    run_test("<=2.3.4", "<=2.3.4");

    // Pre-release version tests
    run_test("^1.0.0-beta.1", "^1.0.0-beta.1");
    run_test("~1.0.0-beta.1", "~1.0.0-beta.1");
    run_test("1.0.0-beta.1", "1.0.0-beta.1");

    // Build metadata tests
    run_test("1.0.0+build123", "1.0.0+build123");
    run_test("^1.0.0+build123", "^1.0.0+build123");
    run_test("~1.0.0+build123", "~1.0.0+build123");

    // More edge cases with zero major versions
    run_test("^0.0.2", "^0.0.2");
    run_test("^0.0.0", "^0.0.0");
    run_test("^0.0.0-pre", "^0.0.0-pre");
    run_test("0.0.1", "0.0.1");

    // Wildcard ranges
    run_test("*", "*");
    run_test(">=1.0.0 <2.0.0", "1"); // normalizes

    // Testing exact zero versions with pre-releases
    run_test("0.0.0-alpha", "0.0.0-alpha");
    run_test("^0.0.0-alpha", "^0.0.0-alpha");

    // Caret and tilde with pre-release and build metadata
    run_test("^1.0.0-beta.1+build123", "^1.0.0-beta.1+build123");
    run_test("~1.0.0-beta.1+build123", "~1.0.0-beta.1+build123");

    // Exact pre-release versions with build metadata
    run_test("1.0.0-beta.1+build123", "1.0.0-beta.1+build123");

    // Ranges with different inclusive/exclusive combinations
    run_test(">1.0.0-beta.1 <=1.1.0", ">1.0.0-beta.1 <=1.1.0");
    run_test(">1.0.0 <1.1.0", ">1.0.0 <1.1.0");

    // Pre-release with tilde normalization
    run_test("^0.2.3-beta.1", "~0.2.3-beta.1"); // normalizes

    // Pre-release with zero major and complex range
    run_test("^0.0.2-alpha", "^0.0.2-alpha");
    run_test("~0.0.2-alpha", "~0.0.2-alpha");

    // Greater than pre-release version
    run_test(">1.0.0-beta.1", ">1.0.0-beta.1");

    // Less than pre-release version
    run_test("<1.0.0-beta.1", "<1.0.0-beta.1");

    // Or conditions
    run_test("1 || 2 || 3", "1 || 2 || 3");
  }
}
