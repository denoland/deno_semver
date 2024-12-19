// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use std::borrow::Borrow;
use std::ops::Deref;

use capacity_builder::StringAppendable;
use capacity_builder::StringType;
use serde::Deserialize;
use serde::Serialize;

macro_rules! shared {
  ($ident:ident) => {
    impl $ident {
      #[inline(always)]
      pub fn from_cow(cow: std::borrow::Cow<str>) -> Self {
        match cow {
          std::borrow::Cow::Borrowed(s) => Self::from_str(s),
          std::borrow::Cow::Owned(s) => Self::from_string(s),
        }
      }

      #[inline(always)]
      pub fn as_str(&self) -> &str {
        self.0.as_str()
      }

      #[inline(always)]
      pub fn push(&mut self, c: char) {
        self.0.push(c);
      }

      #[inline(always)]
      pub fn push_str(&mut self, s: &str) {
        self.0.push_str(s);
      }

      #[inline(always)]
      pub fn to_string(&self) -> String {
        self.0.to_string()
      }
    }

    impl std::fmt::Display for $ident {
      #[inline(always)]
      fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
      }
    }

    impl Deref for $ident {
      type Target = str;

      #[inline(always)]
      fn deref(&self) -> &Self::Target {
        self.0.as_str()
      }
    }

    impl Borrow<str> for $ident {
      #[inline(always)]
      fn borrow(&self) -> &str {
        self.as_str()
      }
    }

    impl AsRef<std::path::Path> for $ident {
      fn as_ref(&self) -> &std::path::Path {
        std::path::Path::new(self.0.as_str())
      }
    }

    impl PartialEq<str> for $ident {
      #[inline(always)]
      fn eq(&self, other: &str) -> bool {
        self.0.as_str() == other
      }
    }

    impl PartialEq<&str> for $ident {
      #[inline(always)]
      fn eq(&self, other: &&str) -> bool {
        self.0.as_str() == *other
      }
    }

    impl PartialEq<String> for $ident {
      #[inline(always)]
      fn eq(&self, other: &String) -> bool {
        self.0.as_str() == other
      }
    }

    impl PartialEq<&String> for $ident {
      #[inline(always)]
      fn eq(&self, other: &&String) -> bool {
        self.0.as_str() == other.as_str()
      }
    }

    impl PartialEq<$ident> for str {
      #[inline(always)]
      fn eq(&self, other: &$ident) -> bool {
        self == other.0
      }
    }

    impl PartialEq<$ident> for &str {
      #[inline(always)]
      fn eq(&self, other: &$ident) -> bool {
        *self == other.0
      }
    }

    impl PartialEq<$ident> for String {
      #[inline(always)]
      fn eq(&self, other: &$ident) -> bool {
        self.as_str() == other.0.as_str()
      }
    }

    impl PartialEq<&$ident> for String {
      #[inline(always)]
      fn eq(&self, other: &&$ident) -> bool {
        self.as_str() == other.0.as_str()
      }
    }

    impl<'a> StringAppendable<'a> for &'a $ident {
      #[inline(always)]
      fn append_to_builder<TString: capacity_builder::StringType>(
        self,
        builder: &mut capacity_builder::StringBuilder<'a, TString>,
      ) {
        builder.append(self.0.as_str())
      }
    }
  };
}

/// A 24 byte string that uses the stack when < 24 bytes.
#[derive(
  Debug,
  Default,
  Clone,
  PartialOrd,
  Ord,
  PartialEq,
  Eq,
  Hash,
  Serialize,
  Deserialize,
)]
pub struct StackString(hipstr::HipStr<'static>);

shared!(StackString);

impl StackString {
  #[inline(always)]
  pub fn with_capacity(size: usize) -> Self {
    Self(hipstr::HipStr::with_capacity(size))
  }

  #[inline(always)]
  pub fn from_static(s: &'static str) -> Self {
    Self(hipstr::HipStr::from_static(s))
  }

  /// Creates a `StackString` from a `&str`.
  #[inline(always)]
  pub fn from_str(s: &str) -> Self {
    Self(hipstr::HipStr::from(s))
  }

  /// Creates a `StackString` from a `String`.
  ///
  /// Generally you don't want to end up with a `String` in the first
  /// place, which is why this struct doesn't implement `From<String>`
  #[inline(always)]
  pub fn from_string(s: String) -> Self {
    Self(hipstr::HipStr::from(s))
  }

  pub fn replace(&self, from: &str, to: &str) -> Self {
    // hipstr currently doesn't have a targeted replace method
    Self(self.0.replace(from, to).into())
  }

  pub fn into_string(self) -> String {
    self.0.into()
  }
}

impl StringType for StackString {
  type MutType = hipstr::HipStr<'static>;

  #[inline(always)]
  fn with_capacity(
    size: usize,
  ) -> Result<Self::MutType, std::collections::TryReserveError> {
    Ok(hipstr::HipStr::with_capacity(size))
  }

  #[inline(always)]
  fn from_mut(inner: Self::MutType) -> Self {
    Self(inner)
  }
}

// Note: Do NOT implement `From<String>` in order to discourage its use
// because we shouldn't end up with a `String` in the first place.

// It would be nice to only implement this for 'static strings, but unfortunately
// rust has trouble giving nice error messages when trying to do that and requiring
// having to write `StackString::from_str` in test code instead of `"something".into()`
// is not very nice.
impl From<&str> for StackString {
  #[inline(always)]
  fn from(s: &str) -> Self {
    Self(hipstr::HipStr::from(s))
  }
}

/// A 16 byte string that uses the stack when < 16 bytes.
#[derive(
  Debug,
  Default,
  Clone,
  PartialOrd,
  Ord,
  PartialEq,
  Eq,
  Hash,
  Serialize,
  Deserialize,
)]
pub struct SmallStackString(ecow::EcoString);

shared!(SmallStackString);

impl SmallStackString {
  #[inline(always)]
  pub fn from_static(s: &'static str) -> Self {
    Self(ecow::EcoString::from(s))
  }

  #[inline(always)]
  pub fn with_capacity(size: usize) -> Self {
    Self(ecow::EcoString::with_capacity(size))
  }

  /// Creates a `SmallStackString` from a `&str`.
  #[inline(always)]
  pub fn from_str(s: &str) -> Self {
    Self(ecow::EcoString::from(s))
  }

  /// Creates a `SmallStackString` from a `String`.
  ///
  /// Generally you don't want to end up with a `String` in the first
  /// place, which is why this struct doesn't implement `From<String>`
  #[inline(always)]
  pub fn from_string(s: String) -> Self {
    Self(ecow::EcoString::from(s))
  }

  pub fn replace(&self, from: &str, to: &str) -> Self {
    Self(self.0.replace(from, to))
  }

  pub fn into_string(self) -> String {
    self.0.into()
  }
}

impl StringType for SmallStackString {
  type MutType = ecow::EcoString;

  #[inline(always)]
  fn with_capacity(
    size: usize,
  ) -> Result<Self::MutType, std::collections::TryReserveError> {
    Ok(ecow::EcoString::with_capacity(size))
  }

  #[inline(always)]
  fn from_mut(inner: Self::MutType) -> Self {
    Self(inner)
  }
}

// Note: Do NOT implement `From<String>` in order to discourage its use
// because we shouldn't end up with a `String` in the first place.

// It would be nice to only implement this for 'static strings, but unfortunately
// rust has trouble giving nice error messages when trying to do that and requiring
// having to write `SmallStackString::from_str` in test code instead of `"something".into()`
// is not very nice.
impl From<&str> for SmallStackString {
  #[inline(always)]
  fn from(s: &str) -> Self {
    Self(ecow::EcoString::from(s))
  }
}
