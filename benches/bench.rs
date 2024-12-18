fn main() {
  // Run registered benchmarks.
  divan::main();
}

mod package_req {
  use deno_semver::package::PackageReq;

  #[divan::bench]
  fn from_str_loose() -> usize {
    PackageReq::from_str_loose("@deno/std@0.100.0")
      .unwrap()
      .name
      .len()
  }

  #[divan::bench]
  fn to_string_normalized() -> usize {
    PackageReq::from_str_loose("@deno/std@0.100.0")
      .unwrap()
      .to_string_normalized()
      .len()
  }
}

mod version {
  use deno_semver::Version;

  #[divan::bench]
  fn to_string() -> usize {
    version().to_string().len()
  }

  #[divan::bench]
  fn to_string_display() -> usize {
    format!("{}", version()).len()
  }

  fn version() -> Version {
    Version::parse_from_npm("1.1.1-pre").unwrap()
  }
}

mod version_req {
  use deno_semver::VersionReq;

  #[divan::bench]
  fn to_string() -> usize {
    version_req().to_string().len()
  }

  #[divan::bench]
  fn to_string_display() -> usize {
    format!("{}", version_req()).len()
  }

  #[divan::bench]
  fn to_string_normalized() -> usize {
    version_req().to_string_normalized().len()
  }

  fn version_req() -> VersionReq {
    VersionReq::parse_from_npm("^1.1.1-pre").unwrap()
  }
}
