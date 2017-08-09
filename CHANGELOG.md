# v0.2.0

* Documentation improvements.
* Dual license under Apache Version 2.0 and MIT.
* Make values allocation optional (if no values are added to a Context is will
  not make an allocation for them).
* Changed the `CancelFunc` type to `CancelSignal` struct. This removes the need
  for an allocation.
* Implemented the `Debug` trait for `Context`.
* Add `DoneReason.into_error` method.
* Shrink values when freezing the context.
* Increase test coverage.

# v0.1.0

Initial release.
