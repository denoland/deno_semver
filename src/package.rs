use serde::Deserialize;
use serde::Serialize;
use thiserror::Error;
use url::Url;

use crate::Version;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum PackageKind {
  Npm,
}

#[derive(Debug, Error, Clone)]
#[error("Invalid package name and version reference '{text}'. {message}")]
pub struct PackageNvReferenceParseError {
  pub message: String,
  pub text: String,
}

/// A package name and version with a potential subpath.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct PackageNvReference {
  pub kind: PackageKind,
  pub nv: PackageNv,
  pub sub_path: Option<String>,
}

impl PackageNvReference {
  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, PackageNvReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(nv: &str) -> Result<Self, PackageNvReferenceParseError> {
    use monch::*;

    fn sub_path(input: &str) -> ParseResult<&str> {
      let (input, _) = ch('/')(input)?;
      Ok(("", input))
    }

    fn parse_ref(input: &str) -> ParseResult<PackageNvReference> {
      let (input, _) = tag("npm:")(input)?;
      let (input, nv) = parse_nv(input)?;
      let (input, maybe_sub_path) = maybe(sub_path)(input)?;
      Ok((
        input,
        PackageNvReference {
          kind: PackageKind::Npm,
          nv,
          sub_path: maybe_sub_path.map(ToOwned::to_owned),
        },
      ))
    }

    with_failure_handling(parse_ref)(nv).map_err(|err| {
      PackageNvReferenceParseError {
        message: format!("{err:#}"),
        text: nv.to_string(),
      }
    })
  }

  pub fn as_specifier(&self) -> Url {
    let version_text = self.nv.version.to_string();
    let capacity = 5 /* npm:/ */
      + self.nv.name.len()
      + 1 /* @ */
      + version_text.len()
      + self.sub_path.as_ref().map(|p| p.len() + 1 /* slash  */).unwrap_or(0);
    let mut text = String::with_capacity(capacity);
    text.push_str("npm:/");
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

impl std::fmt::Display for PackageNvReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    if let Some(sub_path) = &self.sub_path {
      write!(f, "npm:{}/{}", self.nv, sub_path)
    } else {
      write!(f, "npm:{}", self.nv)
    }
  }
}

impl Serialize for PackageNvReference {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for PackageNvReference {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: serde::Deserializer<'de>,
  {
    let text = String::deserialize(deserializer)?;
    match Self::from_str(&text) {
      Ok(req) => Ok(req),
      Err(err) => Err(serde::de::Error::custom(err)),
    }
  }
}

#[derive(Debug, Error, Clone)]
#[error("Invalid package name and version '{text}'. {message}")]
pub struct PackageNvParseError {
  pub message: String,
  pub text: String,
}

#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct PackageNv {
  pub name: String,
  pub version: Version,
}

impl std::fmt::Debug for PackageNv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // when debugging, it's easier to compare this
    write!(f, "{}@{}", self.name, self.version)
  }
}

impl std::fmt::Display for PackageNv {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}@{}", self.name, self.version)
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
    let text = String::deserialize(deserializer)?;
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
      self.name.split('/').next()
    } else {
      None
    }
  }
}

fn parse_nv(input: &str) -> monch::ParseResult<PackageNv> {
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
      PackageNv {
        name: name.to_string(),
        version,
      },
    )),
    Err(err) => ParseError::fail(at_version_input, format!("{err:#}")),
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn package_nv_ref() {
    let package_nv_ref =
      PackageNvReference::from_str("npm:package@1.2.3/test").unwrap();
    assert_eq!(
      package_nv_ref,
      PackageNvReference {
        kind: PackageKind::Npm,
        nv: PackageNv {
          name: "package".to_string(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: Some("test".to_string())
      }
    );
    assert_eq!(
      package_nv_ref.as_specifier().as_str(),
      "npm:/package@1.2.3/test"
    );

    // no path
    let package_nv_ref =
      PackageNvReference::from_str("npm:package@1.2.3").unwrap();
    assert_eq!(
      package_nv_ref,
      PackageNvReference {
        kind: PackageKind::Npm,
        nv: PackageNv {
          name: "package".to_string(),
          version: Version::parse_from_npm("1.2.3").unwrap(),
        },
        sub_path: None
      }
    );
    assert_eq!(package_nv_ref.as_specifier().as_str(), "npm:/package@1.2.3");
  }
}
