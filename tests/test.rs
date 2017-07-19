extern crate io_context;

use std::{io, mem, thread};
use std::time::Duration;

use io_context::*;

fn assert_send<T: Send>() {}
fn assert_sync<T: Sync>() {}
fn assert_size<T>(want: usize) {
    assert_eq!(mem::size_of::<T>(), want);
}

#[test]
fn assertions() {
    assert_send::<Context>();
    assert_sync::<Context>();
    // TODO: fix this:
    //assert_size::<Context>(72);

    assert_send::<DoneReason>();
    assert_sync::<DoneReason>();
    assert_size::<DoneReason>(1);
}

#[test]
fn canceling_context() {
    let mut ctx = Context::background();
    let cancel = ctx.add_cancel_signal();
    assert_eq!(ctx.done(), None);

    cancel();
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
}

#[test]
fn canceling_child_should_not_affect_parent() {
    let ctx = Context::background().freeze();
    let mut child_ctx = Context::create_child(&ctx);
    let cancel = child_ctx.add_cancel_signal();
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), None);
}

#[test]
fn canceling_child_should_not_affect_parent_add_cancel_signal() {
    let mut ctx = Context::background();
    ctx.add_cancel_signal();
    let ctx = ctx.freeze();
    let mut child_ctx = Context::create_child(&ctx);
    let cancel = child_ctx.add_cancel_signal();
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), None);
}

#[test]
fn canceling_parent_should_affect_child() {
    let mut ctx = Context::background();
    let cancel = ctx.add_cancel_signal();
    let ctx = ctx.freeze();
    let child_ctx = Context::create_child(&ctx);
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
}

#[test]
fn canceling_parent_should_affect_child_add_cancel_signal() {
    let mut ctx = Context::background();
    let cancel = ctx.add_cancel_signal();
    let ctx = ctx.freeze();
    let mut child_ctx = Context::create_child(&ctx);
    child_ctx.add_cancel_signal();
    assert_eq!(child_ctx.done(), None);
    assert_eq!(ctx.done(), None);

    cancel();
    assert_eq!(child_ctx.done(), Some(DoneReason::Canceled));
    assert_eq!(ctx.done(), Some(DoneReason::Canceled));
}

#[test]
fn adding_a_deadline_to_the_context() {
    let timeout = Duration::from_millis(20);
    let mut ctx = Context::background();
    // TODO: better testing of the returned deadline.
    assert!(ctx.deadline().is_none());
    ctx.add_timeout(timeout);
    assert_eq!(ctx.done(), None);
    assert!(ctx.deadline().is_some());

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
fn done_reason() {
    assert_eq!(DoneReason::DeadlineExceeded.to_string(), "context deadline exceeded".to_owned());
    assert_eq!(DoneReason::Canceled.to_string(), "context canceled".to_owned());
    assert_eq!(Into::<io::Error>::into(DoneReason::DeadlineExceeded).to_string(), "context deadline exceeded".to_owned());
    assert_eq!(Into::<io::Error>::into(DoneReason::Canceled).to_string(), "context canceled".to_owned());
}
