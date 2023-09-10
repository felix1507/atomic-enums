#![cfg_attr(not(test), no_std)]

use core::{
    fmt::Debug,
    marker::PhantomData,
    sync::atomic::{AtomicU16, Ordering},
};

pub use atomic_enum_derive::Atomize;

pub trait Atomize: Into<u16> + From<u16> {}

pub struct AtomicEnum<E>(AtomicU16, PhantomData<E>);

impl<E: Atomize> AtomicEnum<E> {
    pub fn new(v: E) -> Self {
        Self(AtomicU16::new(v.into()), PhantomData)
    }

    pub fn set(&self, v: E, order: Ordering) {
        self.0.store(v.into(), order)
    }

    pub fn get(&self, order: Ordering) -> E {
        self.0.load(order).into()
    }

    pub fn compare_exchange(
        &self,
        current: E,
        new: E,
        success: Ordering,
        failure: Ordering,
    ) -> Result<E, E> {
        match self
            .0
            .compare_exchange(current.into(), new.into(), success, failure)
        {
            Ok(v) => Ok(v.into()),
            Err(v) => Err(v.into()),
        }
    }
}

impl<E: Atomize + Debug> Debug for AtomicEnum<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("AtomicEnum")
            .field(&E::from(self.0.load(core::sync::atomic::Ordering::Acquire)))
            .finish()
    }
}

#[macro_export]
macro_rules! gen_atomic_enum {
    ($name:ident: $($val:ident = $num:expr),*) => {
        #[derive(Debug, atomic_enum::Atomize)]
        #[repr(u16)]
        enum $name {
            $(
                $val = $num,
            )*
            UnknownField = u16::MAX,
        }
    };
}
