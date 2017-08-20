// Copyright 2017 Thomas de Zeeuw
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// used, copied, modified, or distributed except according to those terms.

extern crate io_context;

use std::{fmt, io, mem, thread};
use std::time::{Duration, Instant};

use io_context::*;

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}
fn assert_debug<T: fmt::Debug>() {}
fn assert_size<T>(want: usize) {
    assert_eq!(mem::size_of::<T>(), want);
}

#[test]
fn assertions() {
    assert_send::<Context>();
    assert_sync::<Context>();
    assert_debug::<Context>();
    // The `time::Instant` has a different size on Linux.
    #[cfg(target_os="linux")]
    let time_size = 16;
    #[cfg(not(target_os="linux"))]
    let time_size = 8;
    #[cfg(target_pointer_width="64")]
    let want = 64 + time_size;
    #[cfg(target_pointer_width="32")]
    let want = 48 + time_size;
    assert_size::<Context>(want);

    assert_send::<DoneReason>();
    assert_sync::<DoneReason>();
    assert_debug::<DoneReason>();
    assert_size::<DoneReason>(1);
}

#[test]
fn canceling_context() {
    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();
    assert_eq!(ctx.done(), None);
    assert_eq!(ctx.is_done(), Ok(()));

    cancel_signal.cancel();
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.is_done(), Err(DoneReason::Canceled));
}

#[test]
fn canceling_context_twice_does_nothing() {
    let mut ctx = Context::background();
    let cancel_signal1 = ctx.add_cancel_signal();
    let cancel_signal2 = ctx.add_cancel_signal();
    assert_eq!(ctx.done(), None);

    cancel_signal1.cancel();
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
    cancel_signal2.cancel();
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
}

#[test]
fn canceling_child_should_not_affect_parent() {
    let ctx = Context::background().freeze();
    let mut child_ctx = Context::create_child(&ctx);
    let cancel_signal = child_ctx.add_cancel_signal();
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel_signal.cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), None);
}

#[test]
fn canceling_child_should_not_affect_parent_add_cancel_signal() {
    let mut ctx = Context::background();
    ctx.add_cancel_signal();
    let ctx = ctx.freeze();
    let mut child_ctx = Context::create_child(&ctx);
    let cancel_signal = child_ctx.add_cancel_signal();
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel_signal.cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), None);
}

#[test]
fn canceling_parent_should_affect_child() {
    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();
    let ctx = ctx.freeze();
    let child_ctx = Context::create_child(&ctx);
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel_signal.cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
}

#[test]
fn canceling_parent_should_affect_child_add_cancel_signal() {
    let mut ctx = Context::background();
    let cancel_signal = ctx.add_cancel_signal();
    let ctx = ctx.freeze();
    let mut child_ctx = Context::create_child(&ctx);
    child_ctx.add_cancel_signal();
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel_signal.cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
}

#[test]
fn canceling_child_should_affect_not_sibling() {
    let ctx = Context::background().freeze();
    let mut child_ctx1 = Context::create_child(&ctx);
    let mut child_ctx2 = Context::create_child(&ctx);
    let cancel_signal1 = child_ctx1.add_cancel_signal();
    let cancel_signal2 = child_ctx2.add_cancel_signal();
    assert_eq!(ctx.done(), None);
    assert_eq!(child_ctx1.done(), None);
    assert_eq!(child_ctx2.done(), None);

    cancel_signal1.cancel();
    assert_eq!(ctx.done(), None);
    assert_eq!(child_ctx1.done(), Some(DoneReason::Canceled));
    assert_eq!(child_ctx2.done(), None);

    cancel_signal2.cancel();
    assert_eq!(ctx.done(), None);
    assert_eq!(child_ctx1.done(), Some(DoneReason::Canceled));
    assert_eq!(child_ctx2.done(), Some(DoneReason::Canceled));
}

#[test]
fn adding_a_deadline_to_the_context() {
    let timeout = Duration::from_millis(20);
    let mut ctx = Context::background();
    assert!(ctx.deadline().is_none());
    let want = Instant::now() + timeout;
    ctx.add_timeout(timeout);
    assert_eq!(ctx.done(), None);
    if let Some(got) = ctx.deadline() {
        let difference = got.duration_since(want);
        assert!(difference < Duration::from_millis(1));
    } else {
        panic!("expected a deadline, but didn't got one");
    }

    thread::sleep(timeout);
    assert_eq!(ctx.done(), Some(DoneReason::DeadlineExceeded));
}

#[test]
fn adding_a_later_deadline_should_not_overwrite() {
    let timeout1 = Duration::from_millis(20);
    let timeout2 = Duration::from_millis(200);
    let mut ctx = Context::background();
    ctx.add_timeout(timeout1);
    ctx.add_timeout(timeout2); // Shouldn't overwrite, since it's later.
    assert_eq!(ctx.done(), None);
    assert!(ctx.deadline().is_some());

    thread::sleep(timeout1);
    assert_eq!(ctx.done(), Some(DoneReason::DeadlineExceeded));
}

#[test]
fn adding_a_ealier_deadline_should_overwrite() {
    let timeout1 = Duration::from_millis(200);
    let timeout2 = Duration::from_millis(20);
    let mut ctx = Context::background();
    ctx.add_timeout(timeout1);
    ctx.add_timeout(timeout2); // Should overwrite, since it's earlier.
    assert_eq!(ctx.done(), None);
    assert!(ctx.deadline().is_some());

    thread::sleep(timeout2);
    assert_eq!(ctx.done(), Some(DoneReason::DeadlineExceeded));
}

#[test]
fn adding_simple_values_to_the_context() {
    static KEY_1: &'static str = "key 1";
    let value_1: String = "some string".to_owned();

    static KEY_2: &'static str = "key 2";
    let value_2: u64 = 10;

    let mut ctx = Context::background();
    assert!(ctx.get_value::<String>(KEY_1).is_none());
    assert!(ctx.get_value::<u8>(KEY_2).is_none());

    ctx.add_value(KEY_1, value_1.clone());
    ctx.add_value(KEY_2, value_2);
    assert_eq!(ctx.get_value(KEY_1), Some(&value_1));
    assert_eq!(ctx.get_value(KEY_2), Some(&value_2));
}

#[test]
fn adding_complex_values_to_the_context() {
    static REQUEST_ID_KEY: &'static str = "request_id";
    #[derive(Debug, Clone, Eq, PartialEq)]
    struct RequestId { uuid: String };
    let request_id = RequestId{ uuid: "some unique key".to_owned() };

    static USER_ID_KEY: &'static str = "user_id";
    #[derive(Debug, Copy, Clone, Eq, PartialEq)]
    struct UserId { id: u64 };
    let user_id = UserId{ id: 123 };

    let mut ctx = Context::background();
    assert!(ctx.get_value::<u8>(REQUEST_ID_KEY).is_none());
    assert!(ctx.get_value::<String>(USER_ID_KEY).is_none());

    ctx.add_value(REQUEST_ID_KEY, request_id.clone());
    ctx.add_value(USER_ID_KEY, user_id);
    assert_eq!(ctx.get_value(REQUEST_ID_KEY), Some(&request_id));
    assert_eq!(ctx.get_value(USER_ID_KEY), Some(&user_id));
}

#[test]
fn retrieving_values_from_parent_context() {
    static KEY_1: &'static str = "key 1";
    let value_1: String = "some string".to_owned();

    static KEY_2: &'static str = "key 2";
    let value_2: u64 = 10;

    let mut parent_ctx = Context::background();
    assert!(parent_ctx.get_value::<String>(KEY_1).is_none());
    assert!(parent_ctx.get_value::<u8>(KEY_2).is_none());

    parent_ctx.add_value(KEY_1, value_1.clone());
    let parent_ctx = parent_ctx.freeze();

    let mut child_ctx = Context::create_child(&parent_ctx);
    child_ctx.add_value(KEY_2, value_2);

    assert_eq!(parent_ctx.get_value(KEY_1), Some(&value_1));
    assert_eq!(parent_ctx.get_value::<u8>(KEY_2), None);
    assert_eq!(child_ctx.get_value(KEY_1), Some(&value_1));
    assert_eq!(child_ctx.get_value(KEY_2), Some(&value_2));
}

#[test]
fn retrieving_a_value_with_an_incorrect_type_should_not_work() {
    static KEY_1: &'static str = "key 1";
    let value_1: String = "some string".to_owned();

    let mut ctx = Context::background();
    ctx.add_value(KEY_1, value_1.clone());

    assert_eq!(ctx.get_value::<u8>(KEY_1), None);
    assert_eq!(ctx.get_value(KEY_1), Some(&value_1));
}

#[test]
fn adding_values_should_overwrite_the_old_one() {
    static KEY_1: &'static str = "key 1";
    let value_1: String = "some string".to_owned();
    let value_2: u64 = 10;

    let mut parent_ctx = Context::background();
    parent_ctx.add_value(KEY_1, value_1);
    parent_ctx.add_value(KEY_1, value_2);

    assert_eq!(parent_ctx.get_value(KEY_1), Some(&value_2));
}

#[test]
fn adding_values_should_not_overwrite_parent_context_values() {
    static KEY_1: &'static str = "key 1";
    let value_1: String = "some string".to_owned();
    let value_2: u64 = 10;

    let mut parent_ctx = Context::background();
    parent_ctx.add_value(KEY_1, value_1.clone());
    let parent_ctx = parent_ctx.freeze();

    let mut child_ctx = Context::create_child(&parent_ctx);
    child_ctx.add_value(KEY_1, value_2);

    assert_eq!(parent_ctx.get_value(KEY_1), Some(&value_1));
    assert_eq!(child_ctx.get_value(KEY_1), Some(&value_2));
}

#[test]
fn creating_a_long_family_line_should_work() {
    let parent_ctx = Context::background().freeze();
    let mut child_ctx = Context::create_child(&parent_ctx).freeze();
    for _ in 0..100 {
        child_ctx = Context::create_child(&child_ctx).freeze();
        assert!(child_ctx.deadline().is_none()); // Make sure the loops run.
    }
}

#[test]
fn creating_alot_of_children_from_a_single_parent_should_work() {
    let parent_ctx = Context::background().freeze();
    for _ in 0..100 {
        let child = Context::create_child(&parent_ctx);
        assert!(child.deadline().is_none()); // Make sure the loops run.
    }
}

#[test]
fn concurrent_usage() {
    const KEY: &'static str = "key 1";
    const VALUE: u64 = 123;

    let mut background_ctx = Context::background();
    background_ctx.add_timeout(Duration::from_millis(20));
    background_ctx.add_value(KEY, VALUE);
    let background_ctx = background_ctx.freeze();

    let child_ctx1 = Context::create_child(&background_ctx);
    let child_ctx2 = Context::create_child(&background_ctx);

    let handle1 = thread::spawn(move || {
        let mut ctx = child_ctx1;
        assert_eq!(ctx.get_value(KEY), Some(&VALUE));
        ctx.add_deadline(Instant::now());

        match ctx.done() {
            Some(DoneReason::DeadlineExceeded) => return,
            _ => panic!("context deadline not exceeded"),
        }
    });

    let handle2 = thread::spawn(move || {
        let mut ctx = child_ctx2;
        assert_eq!(ctx.get_value(KEY), Some(&VALUE));
        ctx.add_cancel_signal().cancel();

        match ctx.done() {
            Some(DoneReason::Canceled) => return,
            _ => panic!("context was not cancelled"),
        }
    });

    assert!(handle1.join().is_ok());
    assert!(handle2.join().is_ok());
}

#[test]
fn done_reason() {
    assert_eq!(DoneReason::DeadlineExceeded.to_string(), "context deadline exceeded".to_owned());
    assert_eq!(DoneReason::Canceled.to_string(), "context canceled".to_owned());
    assert_eq!(Into::<io::Error>::into(DoneReason::DeadlineExceeded).to_string(), "context deadline exceeded".to_owned());
    assert_eq!(Into::<io::Error>::into(DoneReason::Canceled).to_string(), "context canceled".to_owned());

    enum IoErrorWrapper {
        Io(io::Error),
    }

    impl From<io::Error> for IoErrorWrapper {
        fn from(err: io::Error) -> Self {
            IoErrorWrapper::Io(err)
        }
    }

    impl fmt::Display for IoErrorWrapper {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match *self {
                IoErrorWrapper::Io(ref err) => write!(f, "IoErrorWrapper({})", err),
            }
        }
    }

    assert_eq!(DoneReason::Canceled.into_error::<IoErrorWrapper>().to_string(),
        "IoErrorWrapper(context canceled)".to_owned());
}
