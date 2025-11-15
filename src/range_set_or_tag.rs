use capacity_builder::CapacityDisplay;
use capacity_builder::StringAppendable;
use capacity_builder::StringBuilder;
use capacity_builder::StringType;
use serde::Deserialize;
use serde::Serialize;

use crate::CowVec;
use crate::SmallStackString;
use crate::StackString;
use crate::VersionRangeSet;

pub type PackageTag = SmallStackString;

#[derive(Clone, Debug, PartialEq, Eq, Hash, CapacityDisplay)]
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

impl Serialize for RangeSetOrTag {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_custom_string::<StackString>())
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
