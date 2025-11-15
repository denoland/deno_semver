use capacity_builder::CapacityDisplay;
use capacity_builder::StringAppendable;
use capacity_builder::StringBuilder;
use capacity_builder::StringType;
use monch::*;
use serde::Deserialize;
use serde::Serialize;

use crate::CowVec;
use crate::Partial;
use crate::SmallStackString;
use crate::StackString;
use crate::VersionRange;
use crate::VersionRangeSet;
use crate::XRange;
use crate::common::logical_or;
use crate::common::primitive;
use crate::npm::is_valid_npm_tag;

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

impl<'de> Deserialize<'de> for RangeSetOrTag {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let s = String::deserialize(deserializer)?;
    let result = with_failure_handling(Self::parse)(&s);
    result
      .map_err(|err| serde::de::Error::custom(format!("{}", err)))
  }
}

impl RangeSetOrTag {
pub(crate) fn parse(input: &str) -> ParseResult<'_, RangeSetOrTag> {
  if input.is_empty() {
    return Ok((
      input,
      RangeSetOrTag::RangeSet(VersionRangeSet(CowVec::from([
        VersionRange::all(),
      ]))),
    ));
  }

  let (input, mut ranges) =
    separated_list(|text| RangeOrInvalid::parse(text, range), logical_or)(input)?;

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
    .map(|r| r.into_range())
    .filter_map(|r| r.transpose())
    .collect::<Result<CowVec<_>, _>>()?;
  Ok((input, RangeSetOrTag::RangeSet(VersionRangeSet(ranges))))
}

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


pub(crate) enum RangeOrInvalid<'a> {
  Range(VersionRange),
  Invalid(InvalidRange<'a>),
}

impl<'a> RangeOrInvalid<'a> {
  pub fn into_range(self) -> Result<Option<VersionRange>, ParseError<'a>> {
    match self {
      RangeOrInvalid::Range(r) => {
        if r.is_none() {
          Ok(None)
        } else {
          Ok(Some(r))
        }
      }
      RangeOrInvalid::Invalid(invalid) => Err(invalid.failure),
    }
  }

  pub fn parse(
    input: &'a str,
    parse_range: impl Fn(&'a str) -> ParseResult<'a, VersionRange>,
  ) -> ParseResult<'a, RangeOrInvalid<'a>> {
    let range_result =
      map_res(map(parse_range, Self::Range), |result| match result {
        Ok((input, range)) => {
          let is_end = input.is_empty() || input.trim_start().starts_with("||");
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
}

pub(crate) struct InvalidRange<'a> {
  pub failure: ParseError<'a>,
  pub text: &'a str,
}

fn invalid_range(input: &str) -> ParseResult<&str> {
  let end_index = input.find("||").unwrap_or(input.len());
  let (text, input) = input.split_at(end_index);
  let text = text.trim();
  Ok((input, text))
}

// range ::= simple ( ' ' simple )
fn range(input: &str) -> ParseResult<VersionRange> {
  map(separated_list(simple, whitespace), |ranges| {
    let mut final_range = VersionRange::all();
    for range in ranges {
      final_range = final_range.clamp(&range);
    }
    final_range
  })
  (input)
}

// simple ::= primitive | partial | tilde | caret
fn simple(input: &str) -> ParseResult<VersionRange> {
  or4(
    map(preceded(ch('~'), partial), |partial| {
      partial.as_tilde_version_range()
    }),
    map(preceded(ch('^'), partial), |partial| {
      partial.as_caret_version_range()
    }),
    map(primitive(partial), |primitive| {
      primitive.into_version_range()
    }),
    map(partial, |partial| partial.as_equal_range()),
  )(input)
}

// partial ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
fn partial(input: &str) -> ParseResult<Partial> {
  crate::common::partial(xr)(input)
}

// xr ::= '*' | nr
fn xr(input: &str) -> ParseResult<'_, XRange> {
  or(
    map(tag("*"), |_| XRange::Wildcard),
    map(nr, XRange::Val),
  )(input)
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