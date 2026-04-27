fn main() {
  // Run registered benchmarks.
  divan::main();
}

mod package_req {
  use deno_semver::package::PackageReq;

  #[divan::bench(sample_size = 1000)]
  fn from_str_loose() -> usize {
    PackageReq::from_str_loose("@deno/std@0.100.0")
      .unwrap()
      .name
      .len()
  }

  #[divan::bench(sample_size = 1000)]
  fn to_string_normalized() -> usize {
    PackageReq::from_str_loose("@deno/std@0.100.0")
      .unwrap()
      .to_string_normalized()
      .len()
  }
}

mod version {
  use deno_semver::Version;

  #[divan::bench(sample_size = 1000)]
  fn to_string() -> usize {
    version().to_string().len()
  }

  #[divan::bench(sample_size = 1000)]
  fn to_string_display() -> usize {
    format!("{}", version()).len()
  }

  fn version() -> Version {
    Version::parse_from_npm("1.1.1-pre").unwrap()
  }
}

mod version_req {
  use deno_semver::VersionReq;

  #[divan::bench(sample_size = 1000)]
  fn to_string() -> usize {
    version_req().to_string().len()
  }

  #[divan::bench(sample_size = 1000)]
  fn to_string_display() -> usize {
    format!("{}", version_req()).len()
  }

  #[divan::bench(sample_size = 1000)]
  fn to_string_normalized() -> usize {
    version_req().to_string_normalized().len()
  }

  fn version_req() -> VersionReq {
    VersionReq::parse_from_npm("^1.1.1-pre").unwrap()
  }
}

mod parse_npm_version_req {
  use deno_semver::VersionReq;

  #[divan::bench(sample_size = 1000)]
  fn caret_simple() -> usize {
    VersionReq::parse_from_npm("^1.2.3")
      .unwrap()
      .version_text()
      .len()
  }

  #[divan::bench(sample_size = 1000)]
  fn caret_pre_build() -> usize {
    VersionReq::parse_from_npm("^1.2.3-beta.1+build.42")
      .unwrap()
      .version_text()
      .len()
  }

  #[divan::bench(sample_size = 1000)]
  fn hyphen_range() -> usize {
    VersionReq::parse_from_npm("1.2.3 - 2.3.4")
      .unwrap()
      .version_text()
      .len()
  }

  #[divan::bench(sample_size = 1000)]
  fn or_chain() -> usize {
    VersionReq::parse_from_npm("^1.2.3 || ~2.3.4 || >=3.0.0 <4.0.0")
      .unwrap()
      .version_text()
      .len()
  }

  #[divan::bench(sample_size = 1000)]
  fn anded_range() -> usize {
    VersionReq::parse_from_npm(">=1.2.3 <2.0.0")
      .unwrap()
      .version_text()
      .len()
  }
}

mod parse_npm_version {
  use deno_semver::Version;

  #[divan::bench(sample_size = 1000)]
  fn simple() -> u64 {
    Version::parse_from_npm("1.2.3").unwrap().major
  }

  #[divan::bench(sample_size = 1000)]
  fn pre_build() -> u64 {
    Version::parse_from_npm("1.2.3-beta.1.alpha+build.42")
      .unwrap()
      .major
  }
}
