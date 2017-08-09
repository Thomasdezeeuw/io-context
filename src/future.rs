// Copyright 2017 Thomas de Zeeuw
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// used, copied, modified, or distributed except according to those terms.

use std::fmt;

use futures::{Poll, Future, Stream, Sink, StartSend};

use super::{Context, DoneReason};

/// `ContextFuture` is a wrapper type for the [`futures`] crate's [`Future`],
/// [`Stream`] or [`Sink`]. On every poll call of the future/stream/sink it will
/// check if the [`Context`] is [`done`] first.
///
/// [`futures`]: https://docs.rs/futures/*/futures/
/// [`Future`]: https://docs.rs/futures/*/futures/future/trait.Future.html
/// [`Stream`]: https://docs.rs/futures/*/futures/stream/trait.Stream.html
/// [`Sink`]: https://docs.rs/futures/*/futures/sink/trait.Sink.html
/// [`Context`]: struct.Context.html
/// [`done`]: struct.Context.html#method.done
pub struct ContextFuture<T> {
    ctx: Context,
    inner: T,
}

impl<T> ContextFuture<T> {
    /// Wrap a future.
    pub fn new_future<I, E>(ctx: Context, future: T) -> ContextFuture<T>
        where T: Future<Item=I, Error=E>,
              E: From<DoneReason>,
    {
        ContextFuture {
            ctx: ctx,
            inner: future,
        }
    }

    /// Wrap a stream.
    pub fn new_stream<I, E>(ctx: Context, stream: T) -> ContextFuture<T>
        where T: Stream<Item=I, Error=E>,
              E: From<DoneReason>,
    {
        ContextFuture {
            ctx: ctx,
            inner: stream,
        }
    }

    /// Wrap a sink.
    pub fn new_sink<I, E>(ctx: Context, sink: T) -> ContextFuture<T>
        where T: Sink<SinkItem=I, SinkError=E>,
              E: From<DoneReason>,
    {
        ContextFuture {
            ctx: ctx,
            inner: sink,
        }
    }

    // TODO: add `get_ref`, `get_mut`, `into_inner`? Returning T?

    /// Check if the context is done.
    fn done<E>(&self) -> Result<(), E> where E: From<DoneReason> {
        if let Some(reason) = self.ctx.done() {
            Err(reason.into())
        } else {
            Ok(())
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for ContextFuture<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ContextFuture")
            .field("ctx", &self.ctx)
            .field("inner", &self.inner)
            .finish()
    }
}

impl<F, I, E> Future for ContextFuture<F>
    where F: Future<Item=I, Error=E>,
          E: From<DoneReason>,
{
    type Item = F::Item;
    type Error = F::Error;

    fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
        self.done().and_then(|_| self.inner.poll())
    }
}

impl<S, I, E> Stream for ContextFuture<S>
    where S: Stream<Item=I, Error=E>,
          E: From<DoneReason>,
{
    type Item = S::Item;
    type Error = S::Error;

    fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
        self.done().and_then(|_| self.inner.poll())
    }
}

impl<S, I, E> Sink for ContextFuture<S>
    where S: Sink<SinkItem=I, SinkError=E>,
          E: From<DoneReason>,
{
    type SinkItem = S::SinkItem;
    type SinkError = S::SinkError;

    fn start_send(&mut self, item: Self::SinkItem) -> StartSend<Self::SinkItem, Self::SinkError> {
        self.done().and_then(|_| self.inner.start_send(item))
    }

    fn poll_complete(&mut self) -> Poll<(), Self::SinkError> {
        self.done().and_then(|_| self.inner.poll_complete())
    }

    fn close(&mut self) -> Poll<(), Self::SinkError> {
        self.done().and_then(|_| self.inner.close())
    }
}
