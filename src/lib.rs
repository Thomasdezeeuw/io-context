// Copyright 2017 Thomas de Zeeuw
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// used, copied, modified, or distributed except according to those terms.

//! This crate defines a [`Context`], which carries deadlines, cancelations
//! signals and request scoped values across API boundaries.
//!
//! Incoming server requests should create a request specific `Context` from the
//! [`background context`]. While outgoing requests to servers should accept a
//! `Context` in there methods to allow for cancelation and deadlines. A chain
//! of funtions calls for handling a request should propagate the `Context`,
//! optionally adding their own deadlines or cancelation signals. As demostrated
//! in the example below.
//!
//! [`Context`]: struct.Context.html
//! [`background context`]: struct.Context.html#method.background
//!
//! ```
//! # extern crate io_context;
//! # use io_context::Context;
//! # use std::io;
//! fn main() {
//!     // First create our background context. To this context we could add
//!     // signal handling, e.g. when the user pressed ctrl-c.
//!     let mut ctx = Context::background();
//!     // This signal should be canceled once ctrl-c is pressed.
//!     let cancel_signal = ctx.add_cancel_signal();
//!     let ctx = ctx.freeze();
//!     loop {
//!         // Create a context for our request. This will copy any deadlines
//!         // and cancelation signals from the background context into the
//!         // request specific one.
//!         //
//!         // However adding a deadline or cancelation signal to the client
//!         // will not after the background context.
//!         let request_ctx = Context::create_child(&ctx);
//!
//!         // Read a request.
//!         let request = read_request();
//!         // Pass the request context along with the request to the request
//!         // handler.
//!         let response = handle_request(request_ctx, request).unwrap();
//!         println!("got response: {:?}", response);
//!         # break; // Don't loop forever while testing.
//!     }
//! }
//! #
//! # #[derive(Debug)]
//! # struct Request;
//! # #[derive(Debug)]
//! # struct Response;
//! #
//! # fn read_request() -> Request {
//! #     Request
//! # }
//!
//! fn handle_request(ctx: Context, request: Request) -> io::Result<Response> {
//!     // Check if the context's deadline was exceeded, or if the context was
//!     // canceled.
//!     if let Some(reason) = ctx.done() {
//!         // For convience `DoneReason`, returned by `Context.done`, can be
//!         // converted into an `io::Error`.
//!         return Err(reason.into());
//!     }
//!
//!     // Make request to an external server, passing our request context.
//!     make_http_request(ctx, "https://api.example.com".to_owned())
//! }
//!
//! // An outgoing request should accept a `Context` as first parameter.
//! fn make_http_request(ctx: Context, url: String) -> io::Result<Response> {
//!     // Again checking the context is done.
//!     if let Some(reason) = ctx.done() {
//!         return Err(reason.into());
//!     }
//!     // Here any deadlines should be added to the HTTP request, using
//!     // `context.deadline` method to retrieve it.
//!
//!     // But we'll fake the response here, for the sake of simplicity.
//!     Ok(Response)
//! }
//! ```
//!
//! Contexts should not stored in structs. Instead functions and methods that
//! need a context should accept it as first parameter. For more conventions see
//! the [`Context convention`] documentation. A possible exception for this is a
//! struct that implements a [`Future`], which represents the state of that
//! future.
//!
//! [`Context convention`]: struct.Context.html#conventions
//! [`Future`]: https://docs.rs/futures/*/futures/future/trait.Future.html
//!
//! # Usage
//!
//! In the `main` function of the program a background context should be
//! created, which is used in creating all child (request specific) contexts.
//!
//! Request deadlines can be added using the [`add_deadline`] and [`add_timeout`]
//! methods defined on [`Context`]. While cancelation signals can be added using
//! the [`add_cancel_signal`] method. Request scoped values, e.g. a request id,
//! can be added using the [`add_value`] method. For examples see below and the
//! documentation of different linked methods.
//!
//! [`add_deadline`]: struct.Context.html#method.add_deadline
//! [`add_timeout`]: struct.Context.html#method.add_timeout
//! [`add_cancel_signal`]: struct.Context.html#method.add_cancel_signal
//! [`add_value`]: struct.Context.html#method.add_value
//!
//! ```
//! # extern crate io_context;
//! # use io_context::Context;
//! fn main() {
//!     // Create a background context.
//!     let mut ctx = Context::background();
//!
//!     // Add cancelation to the context. We can use this to respond to a
//!     // kill signal from the user, e.g. when pressing ctrl-c.
//!     let cancel_signal = ctx.add_cancel_signal();
//!
//!     // ... Some time later when we received a kill signal.
//!     cancel_signal.cancel(); // Now the context and it's children will be canceled.
//! }
//! ```
//!
//! ## In libraries
//!
//! Libraries should accept contexts in their API, the convention is to accept
//! it as first parameter in all methods and functions that need it. Do not
//! store a context in a struct. For more conventions see the [`Context
//! convention`] documentation.
//!
//! ```
//! # extern crate io_context;
//! # use io_context::Context;
//! use std::io;
//! use std::time::Duration;
//!
//! struct Connection { /* Some fields. */ }
//!
//! impl Connection {
//!     // This executes some long runnning operation.
//!     fn execute_operation(&self, ctx: Context, input: &[u8]) -> io::Result<()> {
//!         // Do step 1 of the work.
//!         work_step_1(input);
//!
//!         // Check if the context is done, e.g. if the deadline has exceeded.
//!         if let Some(reason) = ctx.done() {
//!             return Err(reason.into());
//!         }
//!
//!         // Do some more work.
//!         work_step_2();
//!
//!         // Check the context again.
//!         if let Some(reason) = ctx.done() {
//!             rollback();
//!             return Err(reason.into());
//!         }
//!
//!         // More work, etc.
//!         work_step_3();
//!
//!         // Of course we can have even more preciese control if we pass the
//!         // context to our work functions as well, that is omitted in this
//!         // example.
//!
//!         Ok(())
//!     }
//! }
//!
//! fn main() {
//!     let mut ctx = Context::background();
//!     ctx.add_timeout(Duration::from_secs(5));
//!     let ctx = ctx.freeze();
//!
//!     // We create a new child context just for the specific operation. Any
//!     // deadlines or cancelation signals added to the parent will be added
//!     // to the child context as well. However any deadlines or cancelation
//!     // signals added to the child will not affect the parent.
//!     let mut child_ctx = Context::create_child(&ctx);
//!     child_ctx.add_timeout(Duration::from_secs(1));
//!
//!     // Now we execute the operation, while controlling it's deadline. We
//!     // could also add a cancelation signal so we could stop it from another
//!     // thread (or future), see `Context.add_cancel_signal`.
//!     let connection = Connection{};
//!     connection.execute_operation(child_ctx, b"some input").unwrap();
//! }
//! # fn work_step_1(_: &[u8]) {}
//! # fn work_step_2() {}
//! # fn work_step_3() {}
//! # fn rollback() {}
//! ```
//!
//! ## When should a Context be used?
//!
//! A `Context` is mainly useful if an operation is long running. As a rule of
//! thumb; if an operation is less then 10 milliseconds it is not worth it to
//! add a `Context` to the operation.
//!
//! Examples of when adding a `Context` is worth it:
//!
//! * Any operation which involve any kind of I/O (network, disk or otherwise).
//! * Any operation which support cancelation or timeouts already.
//! * Long looping operations which process input in batches.
//!
//! The common theme in the example operations above is the fact that they all
//! could be or are long running. If you, both as a developer and user of your
//! application, would like more control over these kind of operations the use
//! of a `Context` is a good fit.

use std::{fmt, io};
use std::any::Any;
use std::collections::HashMap;
use std::error::Error;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

/// A context that carries a deadline, cancelation signals and request scoped
/// values across API boundaries and between processes.
///
/// A cancelation signal can be added using the [`add_cancel_signal`] method.
/// Deadlines and timeouts can be added using the [`add_deadline`] and
/// [`add_timeout`] methods. While [`add_value`] adds a value to the context.
///
/// For more information and examples see the crate level documentation.
///
/// [`add_cancel_signal`]: struct.Context.html#method.add_cancel_signal
/// [`add_deadline`]: struct.Context.html#method.add_deadline
/// [`add_timeout`]: struct.Context.html#method.add_timeout
/// [`add_value`]: struct.Context.html#method.add_value
///
/// # Child contexts
///
/// A child context can be created by using the [`freeze`] method on the parent
/// context, and then using the [`create_child`] method to create a child
/// context. This should be done on a per request basis. This way each request
/// has each own deadline and can be canceled if the connection is closed.
///
/// Any cancelation signals, deadlines, timeouts and values from the parent
/// context will be shared between all the child contexts and all it's children,
/// and it's children's children, etc. So if a parent context is canceled so
/// are all it's children.
///
/// However adding or changing anything (like adding values or cancelation
/// signals) on a child context will not affect the parent context. See the
/// example below.
///
/// [`freeze`]: struct.Context.html#method.freeze
/// [`create_child`]: struct.Context.html#method.create_child
///
/// ```
/// # extern crate io_context;
/// # use io_context::Context;
/// fn main() {
///     // First create our parent context.
///     let mut parent_ctx = Context::background();
///     // We can use this `cancel_all` signal to handle ctrl-c.
///     let parent_cancel_signal = parent_ctx.add_cancel_signal();
///     // Now we freeze the parent context so it can be used to create child
///     // contexts.
///     let parent_ctx = parent_ctx.freeze();
///
///     // Create child context from the parent context.
///     let mut child_ctx = Context::create_child(&parent_ctx);
///     // Add a cancel signal to the child context.
///     let child_cancel_signal = child_ctx.add_cancel_signal();
///
///     // Oh no! the connection was closed, now we need to cancel the child
///     // context. This will only cancel the child context.
///     child_cancel_signal.cancel();
///     assert!(child_ctx.done().is_some());
///     assert!(parent_ctx.done().is_none()); // Parent context is still going strong.
///
///     // Now the user pressed ctrl-c and we'll cancel the parent context and
///     // it's child context.
///     parent_cancel_signal.cancel();
///     assert!(child_ctx.done().is_some());
///     assert!(parent_ctx.done().is_some());
/// }
/// ```
///
/// # Conventions
///
/// The context name is often shortend to `ctx` in code as seen in all the
/// examples throughout the documentation of this crate. In documentation
/// however the full word "context" is used.
///
/// Another convention is that the context is the first parameter of a function
/// (after `self`), so it's easier to see if an API supports the context. See
/// [`get_value`] for an example of this.
///
/// Contexts should not stored in structs, that is anti-pattern. Instead
/// functions and methods that need a context should accept it as first
/// parameter. This is also why `Context` does not implement common traits like
/// [`Debug`] and [`Hash`] etc.
///
/// [`get_value`]: struct.Context.html#method.get_value
/// [`Debug`]: https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html
/// [`Hash`]: https://doc.rust-lang.org/nightly/core/hash/trait.Hash.html
pub struct Context {
    /// An optional parent context. Only a context created with
    /// `Context::background` will have this set to `None`.
    parent: Option<Arc<Context>>,
    /// Wether or not this context is canceled. After this is set to false it
    /// can't be set to true after. An `Arc` is needed because the context can
    /// create multiple `CancelSignal`s.
    canceled: Arc<AtomicBool>,
    /// An optional deadline.
    deadline: Option<Instant>,
    /// A collection of read only values stored in this context.
    values: Option<HashMap<&'static str, Box<Any + Send + Sync>>>,
}

impl Context {
    /// Create an empty background context. It has no deadline or cancelation
    /// signals attached to it. It should be used as the top-level context of
    /// which children should be derived on a per request basis. See the [`crate
    /// documentation`] for a detailed example.
    ///
    /// [`crate documentation`]: index.html
    pub fn background() -> Context {
        Context {
            parent: None,
            canceled: Arc::new(AtomicBool::new(false)),
            deadline: None,
            values: None,
        }
    }

    /// Add cancelation to the context. The signalthat is returned will cancel
    /// the context and it's children once called (see [`cancel`]). A single
    /// context can have multiple cancelation signals, after executing a
    /// cancelation the other signals will have no effect.
    ///
    /// [`cancel`]: struct.CancelSignal.html#method.cancel
    pub fn add_cancel_signal(&mut self) -> CancelSignal {
        let canceled = Arc::clone(&self.canceled);
        CancelSignal::new(canceled)
    }

    /// Add a deadline to the context. If the current deadline is sooner then
    /// the provided deadline this method does nothing.
    ///
    /// See [`done`] for example usage.
    ///
    /// [`done`]: struct.Context.html#method.done
    pub fn add_deadline(&mut self, deadline: Instant) {
        match self.deadline {
            Some(current_deadline) if current_deadline < deadline => (),
            _ => self.deadline = Some(deadline),
        }
    }

    /// A convience method to add a deadline to the context which is the current
    /// time plus the `timeout`.
    ///
    /// See [`done`] for example usage.
    ///
    /// [`done`]: struct.Context.html#method.done
    pub fn add_timeout(&mut self, timeout: Duration) {
        self.add_deadline(Instant::now() + timeout)
    }

    /// Add a value to the context. It overwrites any previously set values with
    /// the same key. Because of this it's advised to keep `key` private in a
    /// library or module, see [`get_value`] for more.
    ///
    /// [`get_value`]: struct.Context.html#method.get_value
    pub fn add_value<V>(&mut self, key: &'static str, value: V)
        where V: Any + Send + Sync + Sized,
    {
        if let Some(ref mut values) = self.values {
            // TODO: what if `V` is already boxed, can be reuse to box somehow?
            values.insert(key, Box::new(value));
        } else {
            self.values = Some(HashMap::new());
            self.add_value(key, value)
        }
    }

    /// Get the deadline for this operation, if any. This is mainly useful for
    /// checking if a long job should be started or not, e.g. if a job takes 5
    /// seconds to execute and only 1 second is left on the deadline we're
    /// better of skipping the job entirely.
    ///
    /// If you only want to check if the deadline was exceeded use [`done`]
    /// instead. Because this also checks if the context was canceled.
    ///
    /// [`done`]: struct.Context.html#method.done
    pub fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// Check if the context is done. If it returns `None` the operation may
    /// proceed. But if it returns something the operation should be stopped,
    /// this is the case if the context was canceled or if the deadline is
    /// exceeded.
    ///
    /// ## Example
    ///
    /// ```
    /// # extern crate io_context;
    /// # use io_context::Context;
    /// # fn do_some_work() {}
    /// use std::time::Duration;
    ///
    /// fn main() {
    ///     let mut ctx = Context::background();
    ///     ctx.add_timeout(Duration::from_secs(5));
    ///     loop {
    ///         // Do some work.
    ///         do_some_work();
    ///
    ///         // Check if the context deadline is exceeded, or if it was
    ///         // canceled.
    ///         if let Some(reason) = ctx.done() {
    ///             println!("Stopping work because: {}", reason);
    ///             break;
    ///         }
    ///         # break;
    ///     }
    /// }
    /// ```
    pub fn done(&self) -> Option<DoneReason> {
        match self.deadline {
            Some(deadline) if deadline <= Instant::now() => Some(DoneReason::DeadlineExceeded),
            // TODO: see if we can relax the ordering.
            _ if self.canceled.load(Ordering::SeqCst) => Some(DoneReason::Canceled),
            _ => match self.parent {
                Some(ref parent_ctx) => parent_ctx.done(),
                _ => None,
            },
        }
    }

    /// Get a value from the context. If no value is stored in the `Context`
    /// under the provided `key`, or if the stored value doesn't have type `V`,
    /// this will return `None`.
    ///
    /// Rather then letting the user of a library retrieve a value from the
    /// `Context` manually, a library or module should define `add_to_context`
    /// and `get_from_context` functions, like in the example below.
    ///
    /// ## Example
    ///
    /// In a library or module.
    ///
    /// ```
    /// # extern crate io_context;
    /// # use io_context::Context;
    /// # fn main() {} // To let the example compile.
    /// # pub type RequestId = u64;
    /// // The key used in `Context`. This should be private.
    /// const REQUEST_ID_KEY: &'static str = "MY_LIBRARY_REQUEST_ID_KEY";
    ///
    /// /// Add a `RequestId` to the provided `Context`.
    /// pub fn add_request_id(ctx: &mut Context, request_id: RequestId) {
    ///     ctx.add_value(REQUEST_ID_KEY, request_id)
    /// }
    ///
    /// /// Retrieve a `RequestId` from the provided `Context`.
    /// pub fn get_request_id(ctx: &Context) -> Option<&RequestId> {
    ///     ctx.get_value(REQUEST_ID_KEY)
    /// }
    /// ```
    ///
    /// In the application code.
    ///
    /// ```
    /// # extern crate io_context;
    /// # use io_context::Context;
    /// # pub type RequestId = u64;
    /// # pub fn add_request_id(_ctx: &mut Context, _request_id: RequestId) {}
    /// # pub fn get_request_id(_ctx: &Context) -> Option<RequestId> { Some(123) }
    /// fn main() {
    ///     // Create our new context.
    ///     let mut ctx = Context::background();
    ///     // Add our `RequestId` to it.
    ///     add_request_id(&mut ctx, 123);
    ///     // Retrieve our `RequestId` later on.
    ///     assert_eq!(get_request_id(&ctx), Some(123));
    /// }
    /// ```
    pub fn get_value<V>(&self, key: &'static str) -> Option<&V>
        where V: Any + Send + Sync + Sized,
    {
        if let Some(ref values) = self.values {
            match values.get(&key) {
                Some(value) => {
                    let value: &Any = &**value;
                    return value.downcast_ref::<V>();
                },
                _ => (),
            }
        }
        match self.parent {
            Some(ref parent_ctx) => parent_ctx.get_value(key),
            _ => None,
        }
    }

    /// Freeze the `Context` so it can be used to create child contexts, see
    /// [`create_child`]. The parent context can no longer be modified after
    /// it's frozen and can only be used to create children.
    ///
    /// See the [`Context`] documentation for an example.
    ///
    /// [`create_child`]: struct.Context.html#method.create_child
    /// [`Context`]: struct.Context.html#child-contexts
    pub fn freeze(mut self) -> Arc<Context> {
        if let Some(ref mut values) = self.values {
            values.shrink_to_fit();
        }
        Arc::new(self)
    }

    /// Create a new child from a frozen `Context`, see [`freeze`].
    ///
    /// See the [`Context`] documentation for an example.
    ///
    /// [`freeze`]: struct.Context.html#method.freeze
    /// [`Context`]: struct.Context.html#child-contexts
    pub fn create_child(parent_ctx: &Arc<Context>) -> Context {
        Context {
            parent: Some(Arc::clone(parent_ctx)),
            canceled: Arc::new(AtomicBool::new(false)),
            deadline: parent_ctx.deadline,
            values: None,
        }
    }
}

/// A cancelation signal, see [`Context.add_cancel_signal`]. See the crate
/// documentation for an example.
///
/// [`Context.add_cancel_signal`]: struct.Context.html#method.add_cancel_signal
/// [`crate documentation`]: index.html
pub struct CancelSignal {
    /// A reference to the canceled value of a context.
    canceled: Arc<AtomicBool>,
}

impl CancelSignal {
    /// Create a new `CancelSignal`.
    fn new(canceled: Arc<AtomicBool>) -> CancelSignal {
        CancelSignal {
            canceled: canceled,
        }
    }

    /// Cancel the context.
    pub fn cancel(self) {
        // TODO: see if we can relax the ordering.
        self.canceled.store(true, Ordering::SeqCst);
    }
}

/// The reason why a context was stopped, see [`Context.done`]. This "error"
/// can be turned into an [`io::Error`] by using the [`Into`] trait.
///
/// [`Context.done`]: struct.Context.html#method.done
/// [`io::Error`]: https://doc.rust-lang.org/nightly/std/io/struct.Error.html
/// [`Into`]: https://doc.rust-lang.org/nightly/core/convert/trait.Into.html
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum DoneReason {
    /// The deadline was exceeded.
    DeadlineExceeded,

    /// The context was canceled.
    Canceled,
}

impl Error for DoneReason {
    fn description(&self) -> &str {
        use self::DoneReason::*;
        match *self {
            DeadlineExceeded => "context deadline exceeded",
            Canceled => "context canceled",
        }
    }
}

impl fmt::Display for DoneReason {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.pad(self.description())
    }
}

impl Into<io::Error> for DoneReason {
    fn into(self) -> io::Error {
        use self::DoneReason::*;
        let kind = match self {
            DeadlineExceeded => io::ErrorKind::TimedOut,
            Canceled => io::ErrorKind::Other,
        };
        io::Error::new(kind, self.description())
    }
}
