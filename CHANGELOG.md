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
* added `ContextFuture`; a `Future`/`Stream`/`Sink` wrapper.
* added `Context.add_boxed_value`; reusing a `Box`ed value in adding it to the
  context.
* Added `Context.is_done`; return an `Result` rather then `Some`.

# v0.1.0

Initial release.
