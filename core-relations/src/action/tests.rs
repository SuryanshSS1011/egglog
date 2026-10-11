use crate::{
    action::mask::{IterResult, ValueSource},
    pool::{PoolSet, with_pool_set},
};

use super::mask::{Mask, MaskIter};

#[test]
fn mask_iter() {
    let ps = PoolSet::default();
    let offs = Vec::from_iter(0..100);
    let mut mask = Mask::new(0..100, &ps);
    let mut res = Vec::new();
    mask.iter(&offs).for_each(|x| res.push(*x));
    assert_eq!(offs, res);
}

#[test]
fn mask_iter_zip() {
    let ps = PoolSet::default();
    let offs1 = Vec::from_iter(0..100);
    let offs2 = Vec::from_iter(100..200);
    let mut mask = Mask::new(0..100, &ps);
    let mut res = Vec::new();
    mask.iter(&offs1)
        .zip(&offs2)
        .for_each(|(x, y)| res.push((*x, *y)));
    assert_eq!(
        Vec::from_iter(offs1.iter().copied().zip(offs2.iter().copied())),
        res
    );
}

#[test]
fn mask_iter_dyn() {
    let ps = PoolSet::default();
    let mut mask = Mask::new(0..3, &ps);
    let mut iter_dyn = mask.iter_dynamic(
        with_pool_set(|x| x.get_pool()),
        vec![
            ValueSource::Const(1),
            ValueSource::Slice(&[1, 3, 5]),
            ValueSource::Const(1),
            ValueSource::Slice(&[2, 4, 6]),
        ]
        .into_iter(),
    );
    match iter_dyn.get_at(2) {
        IterResult::Item(item) => {
            let v = item.as_slice();
            assert_eq!(v, [1, 5, 1, 6])
        }
        _ => unreachable!(),
    }
}

#[test]
fn retain() {
    let ps = PoolSet::default();
    let offs = Vec::from_iter(0..100);
    let mut mask = Mask::new(0..100, &ps);
    mask.iter(&offs).retain(|x| *x % 2 == 0);
    let mut got = Vec::new();
    mask.iter(&offs).for_each(|x| got.push(*x));
    assert_eq!(
        Vec::from_iter(offs.iter().copied().filter(|x| *x % 2 == 0)),
        got
    );
}

#[test]
fn fill_vec() {
    let ps = PoolSet::default();
    let offs = Vec::from_iter(0..100);
    let mut mask = Mask::new(0..100, &ps);
    let mut out = Vec::new();
    mask.iter(&offs).fill_vec(
        &mut out,
        || i32::MAX,
        |row, x| {
            assert_eq!(row, *x as usize);
            if *x % 2 == 0 { Some(*x) } else { None }
        },
    );
    // We should filter the mas for the entries for which we returned 'None'
    let mut got = Vec::new();
    mask.iter(&offs).for_each(|x| got.push(*x));
    assert_eq!(
        Vec::from_iter(offs.iter().copied().filter(|x| *x % 2 == 0)),
        got
    );

    assert_eq!(out.len(), 100);

    // The vector itself should have i32::MAX in for the odd indexes.
    for (i, x) in out.iter().copied().enumerate() {
        if i.is_multiple_of(2) {
            assert_eq!(x, i as i32);
        } else {
            assert_eq!(x, i32::MAX);
        }
    }
}

#[test]
fn test_early_stop_initial_state() {
    empty_execution_state!(state);
    assert!(!state.should_stop());
}

#[test]
fn test_early_stop_trigger() {
    empty_execution_state!(state);
    assert!(!state.should_stop());

    state.trigger_early_stop();

    assert!(state.should_stop());
}

#[test]
fn test_early_stop_shared_across_clones() {
    empty_execution_state!(state1);
    let state2 = state1.clone();

    assert!(!state1.should_stop());
    assert!(!state2.should_stop());

    state1.trigger_early_stop();

    assert!(state1.should_stop());
    assert!(state2.should_stop());
}

#[test]
fn test_early_stop_multiple_clones() {
    empty_execution_state!(state1);
    let state2 = state1.clone();
    let state3 = state2.clone();

    assert!(!state1.should_stop());
    assert!(!state2.should_stop());
    assert!(!state3.should_stop());

    state2.trigger_early_stop();

    assert!(state1.should_stop());
    assert!(state2.should_stop());
    assert!(state3.should_stop());
}

#[test]
fn sparse_mutation_buffers_preserve_notifications_fresh_handles_and_drop_flush() {
    use super::{MutationBuffer, MutationBuffers, TableId, Value};
    use crate::numeric_id::NumericId;
    use egglog_concurrency::NotificationList;
    use std::sync::{Arc, Mutex};

    #[derive(Default)]
    struct Buffered {
        staged: Vec<(bool, Vec<Value>)>,
        flushed: Arc<Mutex<Vec<(bool, Vec<Value>)>>>,
    }
    impl MutationBuffer for Buffered {
        fn stage_insert(&mut self, row: &[Value]) {
            self.staged.push((true, row.to_vec()));
        }
        fn stage_remove(&mut self, row: &[Value]) {
            self.staged.push((false, row.to_vec()));
        }
        fn fresh_handle(&self) -> Box<dyn MutationBuffer> {
            Box::new(Self {
                staged: Vec::new(),
                flushed: Arc::clone(&self.flushed),
            })
        }
    }
    impl Drop for Buffered {
        fn drop(&mut self) {
            self.flushed.lock().unwrap().append(&mut self.staged);
        }
    }

    let notifications = NotificationList::default();
    let table = TableId::new(40_000);
    let flushed = Arc::new(Mutex::new(Vec::new()));
    let mut original = MutationBuffers::new(&notifications, Default::default());
    original.lazy_init(table, || {
        Box::new(Buffered {
            staged: Vec::new(),
            flushed: Arc::clone(&flushed),
        })
    });
    original.stage_insert(table, &[]);
    original.lazy_init(table, || panic!("existing buffer must be reused"));
    original.stage_remove(table, &[]);
    assert_eq!(notifications.reset().as_slice(), &[table]);
    assert!(flushed.lock().unwrap().is_empty());
    // Storage is independent of the registry id, including for cloned handles.
    assert!(original.buffers.capacity() < 16);
    let mut cloned = original.clone();
    cloned.stage_insert(table, &[]);
    assert_eq!(notifications.reset().as_slice(), &[table]);
    drop(cloned);
    assert_eq!(*flushed.lock().unwrap(), vec![(true, vec![])]);
    drop(original);
    assert_eq!(
        *flushed.lock().unwrap(),
        vec![(true, vec![]), (true, vec![]), (false, vec![])]
    );
}
