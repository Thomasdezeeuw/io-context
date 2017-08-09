// Copyright 2017 Thomas de Zeeuw
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// used, copied, modified, or distributed except according to those terms.

extern crate futures;
extern crate hyper;
extern crate io_context;
extern crate tokio_core;

use std::io;
use std::time::Duration;

use futures::{Future, Poll};
use hyper::client::{Client, FutureResponse};
use io_context::Context;
use tokio_core::reactor::Core;

fn main() {
    let background_ctx = Context::background().freeze();
    let mut core = Core::new().unwrap();
    let handle = core.handle();

    let client = Client::new(&handle);
    let future = {
        let mut ctx = Context::create_child(&background_ctx);
        // TODO: increase this duration to actual make a http request.
        ctx.add_timeout(Duration::from_millis(10));
        let uri = "http://example.com".parse().unwrap();
        let request_future = client.get(uri);
        MyFuture::new(ctx, request_future)
    };

    match core.run(future) {
        Ok(response) => println!("Got response: {:?}", response),
        Err(err) => println!("Encountered an error: {}", err),
    }
}

/// `MyFuture` wraps a context and a hyper future.
struct MyFuture {
    ctx: Context,
    inner: FutureResponse,
}

impl MyFuture {
    fn new(ctx: Context, future: FutureResponse) -> MyFuture {
        MyFuture {
            ctx: ctx,
            inner: future,
        }
    }
}

impl Future for MyFuture {
    type Item = hyper::Response;
    type Error = hyper::Error;
    fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
        // Check if we need to stop this future.
        if let Some(reason) = self.ctx.done() {
            // This is a bit ugly, but the `hyper::Error` can be created from an
            // `io::Error`, not from an `context::DoneReason`. So this the
            // intermediate `io:Error` is required.
            return Err(Into::<io::Error>::into(reason).into());
        }

        self.inner.poll()
    }
}
