fn main() {
  // Run registered benchmarks.
  divan::main();
}

mod package_req {
  use deno_semver::package::PackageReq;

  #[divan::bench]
  fn from_str_loose() -> usize {
    let mut i = 0;
    for _ in 0..1000 {
      i += PackageReq::from_str_loose("@deno/std@0.100.0")
        .unwrap()
        .name
        .len();
    }
    i
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
