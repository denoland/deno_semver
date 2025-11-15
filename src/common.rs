// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use monch::*;

use crate::CowVec;
use crate::Partial;
use crate::VersionBoundKind;
use crate::VersionPreOrBuild;
use crate::VersionRange;
use crate::XRange;

// logical-or ::= ( ' ' ) * '||' ( ' ' ) *
pub fn logical_or(input: &str) -> ParseResult<&str> {
  delimited(skip_whitespace, tag("||"), skip_whitespace)(input)
}

// logical-and ::= ( ' ' ) * '&&' ( ' ' ) *
pub fn logical_and(input: &str) -> ParseResult<&str> {
  delimited(skip_whitespace, tag("&&"), skip_whitespace)(input)
}

// partial ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
pub fn partial<'a>(
  xr: impl Fn(&'a str) -> ParseResult<'a, XRange>,
) -> impl Fn(&'a str) -> ParseResult<'a, Partial> {
  move |input| {
    let (input, major) = xr(input)?;
    let (input, maybe_minor) = maybe(preceded(ch('.'), &xr))(input)?;
    let (input, maybe_patch) = if maybe_minor.is_some() {
      maybe(preceded(ch('.'), &xr))(input)?
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
}

#[derive(Debug, Clone, Default)]
pub struct Qualifier {
  pub pre: CowVec<VersionPreOrBuild>,
  pub build: CowVec<VersionPreOrBuild>,
}

// qualifier ::= ( '-' pre )? ( '+' build )?
pub fn qualifier(input: &str) -> ParseResult<Qualifier> {
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
fn pre(input: &str) -> ParseResult<CowVec<VersionPreOrBuild>> {
  preceded(maybe(ch('-')), parts)(input)
}

// build ::= parts
fn build(input: &str) -> ParseResult<CowVec<VersionPreOrBuild>> {
  preceded(ch('+'), parts)(input)
}

// parts ::= part ( '.' part ) *
fn parts(input: &str) -> ParseResult<CowVec<VersionPreOrBuild>> {
  if_true(
    map(separated_list(part, ch('.')), |text| {
      text
        .into_iter()
        .map(VersionPreOrBuild::from_str)
        .collect::<CowVec<_>>()
    }),
    |items| !items.is_empty(),
  )(input)
}

// part ::= nr | [-0-9A-Za-z]+
fn part(input: &str) -> ParseResult<&str> {
  // nr is in the other set, so don't bother checking for it
  if_true(
    take_while(|c| c.is_ascii_alphanumeric() || c == '-'),
    |result| !result.is_empty(),
  )(input)
}

#[derive(Debug, Clone, Copy)]
pub enum PrimitiveKind {
  GreaterThan,
  LessThan,
  GreaterThanOrEqual,
  LessThanOrEqual,
  Equal,
}

pub fn primitive_kind(input: &str) -> ParseResult<PrimitiveKind> {
  or5(
    map(tag(">="), |_| PrimitiveKind::GreaterThanOrEqual),
    map(tag("<="), |_| PrimitiveKind::LessThanOrEqual),
    map(ch('<'), |_| PrimitiveKind::LessThan),
    map(ch('>'), |_| PrimitiveKind::GreaterThan),
    map(ch('='), |_| PrimitiveKind::Equal),
  )(input)
}

#[derive(Debug, Clone)]
pub struct Primitive {
  pub kind: PrimitiveKind,
  pub partial: Partial,
}

impl Primitive {
  pub fn into_version_range(self) -> VersionRange {
    let partial = self.partial;
    match self.kind {
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
  }
}

pub fn primitive<'a>(
  partial: impl Fn(&'a str) -> ParseResult<'a, Partial>,
) -> impl Fn(&'a str) -> ParseResult<'a, Primitive> {
  move |input| {
    let (input, kind) = primitive_kind(input)?;
    let (input, _) = skip_whitespace(input)?;
    let (input, partial) = partial(input)?;
    Ok((input, Primitive { kind, partial }))
  }
}
