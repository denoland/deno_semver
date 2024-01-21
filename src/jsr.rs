// Copyright 2018-2023 the Deno authors. All rights reserved. MIT license.

use serde::Deserialize;
use serde::Serialize;
use url::Url;

use crate::package::PackageKind;
use crate::package::PackageNv;
use crate::package::PackageNvReference;
use crate::package::PackageNvReferenceParseError;
use crate::package::PackageReq;
use crate::package::PackageReqReference;
use crate::package::PackageReqReferenceParseError;

/// A reference to a JSR package's name, version constraint, and potential sub path.
/// This contains all the information found in an npm specifier.
///
/// This wraps PackageReqReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct JsrPackageReqReference(PackageReqReference);

impl std::fmt::Display for JsrPackageReqReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "jsr:{}", self.0)
  }
}

impl JsrPackageReqReference {
  pub fn new(inner: PackageReqReference) -> Self {
    Self(inner)
  }

  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, PackageReqReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(
    specifier: &str,
  ) -> Result<Self, PackageReqReferenceParseError> {
    PackageReqReference::from_str(specifier, PackageKind::Jsr).map(Self)
  }

  pub fn req(&self) -> &PackageReq {
    &self.0.req
  }

  pub fn sub_path(&self) -> Option<&str> {
    self.0.sub_path.as_deref()
  }

  pub fn into_inner(self) -> PackageReqReference {
    self.0
  }
}

/// An JSR package name and version with a potential subpath.
///
/// This wraps PackageNvReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct JsrPackageNvReference(PackageNvReference);

impl JsrPackageNvReference {
  pub fn new(inner: PackageNvReference) -> Self {
    Self(inner)
  }

  pub fn from_specifier(
    specifier: &Url,
  ) -> Result<Self, PackageNvReferenceParseError> {
    Self::from_str(specifier.as_str())
  }

  #[allow(clippy::should_implement_trait)]
  pub fn from_str(nv: &str) -> Result<Self, PackageNvReferenceParseError> {
    PackageNvReference::from_str(nv, PackageKind::Jsr).map(Self)
  }

  pub fn as_specifier(&self) -> Url {
    self.0.as_specifier(PackageKind::Jsr)
  }

  pub fn nv(&self) -> &PackageNv {
    &self.0.nv
  }

  pub fn sub_path(&self) -> Option<&str> {
    self.0.sub_path.as_deref()
  }

  pub fn into_inner(self) -> PackageNvReference {
    self.0
  }
}

impl std::fmt::Display for JsrPackageNvReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "jsr:{}", self.0)
  }
}

impl Serialize for JsrPackageNvReference {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for JsrPackageNvReference {
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

/// A package constraint for a JSR dependency which could be from npm or JSR.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JsrDepPackageReq {
  pub kind: PackageKind,
  pub req: PackageReq,
}

impl std::fmt::Display for JsrDepPackageReq {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}{}", self.kind.scheme_with_colon(), self.req)
  }
}

impl JsrDepPackageReq {
  pub fn jsr(req: PackageReq) -> Self {
    Self {
      kind: PackageKind::Jsr,
      req,
    }
  }

  pub fn npm(req: PackageReq) -> Self {
    Self {
      kind: PackageKind::Npm,
      req,
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn jsr_req_ref() {
    {
      let req_ref = JsrPackageReqReference::from_specifier(
        &Url::parse("jsr:/foo").unwrap(),
      )
      .unwrap();
      assert_eq!(req_ref.req().name, "foo");
      assert_eq!(req_ref.req().version_req.to_string(), "*");
      assert_eq!(req_ref.sub_path(), None);
    }
    {
      let req_ref =
        JsrPackageReqReference::from_str("jsr:foo@1/mod.ts").unwrap();
      assert_eq!(req_ref.req().name, "foo");
      assert_eq!(req_ref.req().version_req.to_string(), "1");
      assert_eq!(req_ref.sub_path(), Some("mod.ts"));
    }
    {
      let req_ref =
        JsrPackageReqReference::from_str("jsr:@scope/foo@^1.0.0/mod.ts")
          .unwrap();
      assert_eq!(req_ref.req().name, "@scope/foo");
      assert_eq!(req_ref.req().version_req.to_string(), "^1.0.0");
      assert_eq!(req_ref.sub_path(), Some("mod.ts"));
    }
  }

  #[test]
  fn jsr_nv_ref() {
    {
      let nv_ref = JsrPackageNvReference::from_specifier(
        &Url::parse("jsr:/foo@1.0.0").unwrap(),
      )
      .unwrap();
      assert_eq!(nv_ref.nv().name, "foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), None);
      assert_eq!(nv_ref.as_specifier().as_str(), "jsr:/foo@1.0.0");
    }
    {
      let nv_ref =
        JsrPackageNvReference::from_str("jsr:foo@1.0.0/mod.ts").unwrap();
      assert_eq!(nv_ref.nv().name, "foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), Some("mod.ts"));
      assert_eq!(nv_ref.as_specifier().as_str(), "jsr:/foo@1.0.0/mod.ts");
    }
    {
      let nv_ref =
        JsrPackageNvReference::from_str("jsr:@scope/foo@1.0.0/mod.ts").unwrap();
      assert_eq!(nv_ref.nv().name, "@scope/foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), Some("mod.ts"));
      assert_eq!(
        nv_ref.as_specifier().as_str(),
        "jsr:/@scope/foo@1.0.0/mod.ts"
      );
    }
  }

  #[test]
  fn jsr_dep_package_req_display() {
    assert_eq!(
      JsrDepPackageReq::jsr(PackageReq::from_str("b@1").unwrap()).to_string(),
      "jsr:b@1"
    );
    assert_eq!(
      JsrDepPackageReq::npm(PackageReq::from_str("c@1").unwrap()).to_string(),
      "npm:c@1"
    );
  }
}
