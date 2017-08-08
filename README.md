# IO-Context

[![Build Status](https://travis-ci.org/Thomasdezeeuw/io-context.svg?branch=master)](https://travis-ci.org/Thomasdezeeuw/io-context)
[![Build status](https://ci.appveyor.com/api/projects/status/bfmk3m0a4n43dh6l?svg=true)](https://ci.appveyor.com/project/Thomasdezeeuw/io-context)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](https://opensource.org/licenses/MIT)
[![Crates.io](https://img.shields.io/crates/v/io-context.svg)](https://crates.io/crates/io-context)
[![Docs](https://docs.rs/io-context/badge.svg)](https://docs.rs/io-context)

A context that carries a deadline, cancelation signals and request scoped values
across API boundaries and between processes.

This is heavily inspired by [Go's context package].

See the [API documentation] for more.

[API documentation]: https://docs.rs/io-context
[Go's context package]: https://golang.org/pkg/context/

## License

Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or https://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
