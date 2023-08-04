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

/// A reference to a Deno package's name, version constraint, and potential sub path.
/// This contains all the information found in an npm specifier.
///
/// This wraps PackageReqReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DenoPackageReqReference(PackageReqReference);

impl std::fmt::Display for DenoPackageReqReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "deno:{}", self.0)
  }
}

impl DenoPackageReqReference {
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
    PackageReqReference::from_str(specifier, PackageKind::Deno).map(Self)
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

/// An npm package name and version with a potential subpath.
///
/// This wraps PackageNvReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct DenoPackageNvReference(PackageNvReference);

impl DenoPackageNvReference {
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
    PackageNvReference::from_str(nv, PackageKind::Deno).map(Self)
  }

  pub fn as_specifier(&self) -> Url {
    self.0.as_specifier(PackageKind::Deno)
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

impl std::fmt::Display for DenoPackageNvReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "deno:{}", self.0)
  }
}

impl Serialize for DenoPackageNvReference {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for DenoPackageNvReference {
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

/// A reference to an workspace package's name, version constraint, and potential sub path.
/// This contains all the information found in a workspace specifier.
///
/// This wraps PackageReqReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkspacePackageReqReference(PackageReqReference);

impl std::fmt::Display for WorkspacePackageReqReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "workspace:{}", self.0)
  }
}

impl WorkspacePackageReqReference {
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
    PackageReqReference::from_str(specifier, PackageKind::Workspace).map(Self)
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

/// A workspace package name and version with a potential subpath.
///
/// This wraps PackageNvReference in order to prevent accidentally
/// mixing this with other schemes.
#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub struct WorkspacePackageNvReference(PackageNvReference);

impl WorkspacePackageNvReference {
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
    PackageNvReference::from_str(nv, PackageKind::Workspace).map(Self)
  }

  pub fn as_specifier(&self) -> Url {
    self.0.as_specifier(PackageKind::Workspace)
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

impl std::fmt::Display for WorkspacePackageNvReference {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "workspace:{}", self.0)
  }
}

impl Serialize for WorkspacePackageNvReference {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: serde::Serializer,
  {
    serializer.serialize_str(&self.to_string())
  }
}

impl<'de> Deserialize<'de> for WorkspacePackageNvReference {
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

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn deno_req_ref() {
    {
      let req_ref = DenoPackageReqReference::from_specifier(
        &Url::parse("deno:/foo").unwrap(),
      )
      .unwrap();
      assert_eq!(req_ref.req().name, "foo");
      assert_eq!(req_ref.req().version_req.to_string(), "*");
      assert_eq!(req_ref.sub_path(), None);
    }
    {
      let req_ref =
        DenoPackageReqReference::from_str("deno:foo@1/mod.ts").unwrap();
      assert_eq!(req_ref.req().name, "foo");
      assert_eq!(req_ref.req().version_req.to_string(), "1");
      assert_eq!(req_ref.sub_path(), Some("mod.ts"));
    }
    {
      let req_ref =
        DenoPackageReqReference::from_str("deno:@scope/foo@^1.0.0/mod.ts")
          .unwrap();
      assert_eq!(req_ref.req().name, "@scope/foo");
      assert_eq!(req_ref.req().version_req.to_string(), "^1.0.0");
      assert_eq!(req_ref.sub_path(), Some("mod.ts"));
    }
  }

  #[test]
  fn deno_nv_ref() {
    {
      let nv_ref = DenoPackageNvReference::from_specifier(
        &Url::parse("deno:/foo@1.0.0").unwrap(),
      )
      .unwrap();
      assert_eq!(nv_ref.nv().name, "foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), None);
      assert_eq!(nv_ref.as_specifier().as_str(), "deno:/foo@1.0.0");
    }
    {
      let nv_ref =
        DenoPackageNvReference::from_str("deno:foo@1.0.0/mod.ts").unwrap();
      assert_eq!(nv_ref.nv().name, "foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), Some("mod.ts"));
      assert_eq!(nv_ref.as_specifier().as_str(), "deno:/foo@1.0.0/mod.ts");
    }
    {
      let nv_ref =
        DenoPackageNvReference::from_str("deno:@scope/foo@1.0.0/mod.ts")
          .unwrap();
      assert_eq!(nv_ref.nv().name, "@scope/foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), Some("mod.ts"));
      assert_eq!(
        nv_ref.as_specifier().as_str(),
        "deno:/@scope/foo@1.0.0/mod.ts"
      );
    }
  }

  #[test]
  fn workspace_req_ref() {
    {
      let req_ref = WorkspacePackageReqReference::from_specifier(
        &Url::parse("workspace:/foo").unwrap(),
      )
      .unwrap();
      assert_eq!(req_ref.req().name, "foo");
      assert_eq!(req_ref.req().version_req.to_string(), "*");
      assert_eq!(req_ref.sub_path(), None);
    }
    {
      let req_ref =
        WorkspacePackageReqReference::from_str("workspace:foo@1/mod.ts")
          .unwrap();
      assert_eq!(req_ref.req().name, "foo");
      assert_eq!(req_ref.req().version_req.to_string(), "1");
      assert_eq!(req_ref.sub_path(), Some("mod.ts"));
    }
    {
      let req_ref = WorkspacePackageReqReference::from_str(
        "workspace:@scope/foo@^1.0.0/mod.ts",
      )
      .unwrap();
      assert_eq!(req_ref.req().name, "@scope/foo");
      assert_eq!(req_ref.req().version_req.to_string(), "^1.0.0");
      assert_eq!(req_ref.sub_path(), Some("mod.ts"));
    }
  }

  #[test]
  fn workspace_nv_ref() {
    {
      let nv_ref = WorkspacePackageNvReference::from_specifier(
        &Url::parse("workspace:/foo@1.0.0").unwrap(),
      )
      .unwrap();
      assert_eq!(nv_ref.nv().name, "foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), None);
      assert_eq!(nv_ref.as_specifier().as_str(), "workspace:/foo@1.0.0");
    }
    {
      let nv_ref =
        WorkspacePackageNvReference::from_str("workspace:foo@1.0.0/mod.ts")
          .unwrap();
      assert_eq!(nv_ref.nv().name, "foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), Some("mod.ts"));
      assert_eq!(
        nv_ref.as_specifier().as_str(),
        "workspace:/foo@1.0.0/mod.ts"
      );
    }
    {
      let nv_ref = WorkspacePackageNvReference::from_str(
        "workspace:@scope/foo@1.0.0/mod.ts",
      )
      .unwrap();
      assert_eq!(nv_ref.nv().name, "@scope/foo");
      assert_eq!(nv_ref.nv().version.to_string(), "1.0.0");
      assert_eq!(nv_ref.sub_path(), Some("mod.ts"));
      assert_eq!(
        nv_ref.as_specifier().as_str(),
        "workspace:/@scope/foo@1.0.0/mod.ts"
      );
    }
  }
}
