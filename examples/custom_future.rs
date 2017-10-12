// Copyright 2017 Thomas de Zeeuw
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// used, copied, modified, or distributed except according to those terms.

#[cfg(feature = "context-future")]
extern crate futures;
extern crate io_context;

#[cfg(feature = "context-future")]
fn main() {
    use io_context::{Context, ContextFuture, DoneReason};
    use futures::{Async, Future};
    use futures::future::poll_fn;

    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();

    let future = poll_fn::<(), DoneReason, _>(|| {
        println!("future called!");
        Ok(Async::Ready(()))
    });

    let wrapper_future = ContextFuture::new_future(ctx, future);
    cancel_signal.cancel();

    match wrapper_future.wait() {
        Ok(()) => panic!("future completed unexpectedly"),
        Err(err) => println!("error calling future: {}", err),
    }
}

#[cfg(not(feature = "context-future"))]
fn main() {
    panic!("enable the `context-future` feature, by running `--features context-future`");
}
