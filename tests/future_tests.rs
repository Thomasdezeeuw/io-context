// Copyright 2017 Thomas de Zeeuw
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// used, copied, modified, or distributed except according to those terms.

extern crate io_context;
extern crate futures;

use std::{io, fmt, mem};
use std::error::Error;

use io_context::*;
use futures::{stream, future, Async, AsyncSink, Poll, StartSend};

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}
fn assert_debug<T: fmt::Debug>() {}
fn assert_size<T>(want: usize) {
    assert_eq!(mem::size_of::<T>(), want);
}

#[test]
fn assertions() {
    assert_send::<ContextFuture<u8>>();
    assert_sync::<ContextFuture<u8>>();
    assert_debug::<ContextFuture<u8>>();
    assert_size::<ContextFuture<u8>>(mem::size_of::<Context>() + 8);
}

#[test]
fn future() {
    use futures::Future;
    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();
    let mut future = ContextFuture::new_future(ctx, future::ok(1));
    cancel_signal.cancel();
    assert_eq!(future.poll(), Err(DoneReason::Canceled));

    let ctx = Context::background();
    let mut future = ContextFuture::new_future::<_, io::Error>(ctx, future::ok(1));
    assert!(future.poll().is_ok());
}

#[test]
fn stream() {
    use futures::Stream;
    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();
    let stream = stream::iter(vec![Ok(1), Ok(2), Ok(3)]);
    let mut stream = ContextFuture::new_stream(ctx, stream);

    assert_eq!(stream.poll(), Ok(Async::Ready(Some(1))));
    assert_eq!(stream.poll(), Ok(Async::Ready(Some(2))));
    cancel_signal.cancel();
    assert_eq!(stream.poll(), Err(DoneReason::Canceled));
}

#[test]
fn sink() {
    use futures::Sink;
    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();

    struct Discard;

    impl Sink for Discard {
        type SinkItem = u8;
        type SinkError = io::Error;

        fn start_send(&mut self, _item: Self::SinkItem) -> StartSend<Self::SinkItem, Self::SinkError> {
            Ok(AsyncSink::Ready)
        }

        fn poll_complete(&mut self) -> Poll<(), Self::SinkError> {
            Ok(Async::Ready(()))
        }
    }

    let mut sink = ContextFuture::new_sink(ctx, Discard);

    assert!(sink.start_send(1).is_ok());
    assert!(sink.poll_complete().is_ok());
    cancel_signal.cancel();
    assert_eq!(sink.poll_complete().unwrap_err().description(),
        Into::<io::Error>::into(DoneReason::Canceled).description());
}
