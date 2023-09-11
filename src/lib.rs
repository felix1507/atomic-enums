#![cfg_attr(not(test), no_std)]
//! This crate provides an `AtomicEnum`.
//! This can only be used with enumerations in which the individual fields are assigned `u16` values.
//! 
//! The `gen_atomic_enum!` macro is provided which can be used to create a valid enumeration.
use core::{
    fmt::Debug,
    marker::PhantomData,
    sync::atomic::{AtomicU16, Ordering},
};

pub use atomic_enum_derive::Atomize;

/// The trait needs to be implemented for enumeration which shall be used with `AtomicEnum`.
/// Additionally the traits `Into<u16>` and `From<u16>` have to be implemented.
/// 
/// An derive macro is implemented, make shure that you have a field with the name `UnknownField`
/// is constructed!
pub trait Atomize: Into<u16> + From<u16> {}


/// Stores a atomic enumeration.
/// ## Generic Parameters
/// - `E`
///   -  `E` must implement the trait `Atomize` and with it, the traits `From<u16> + Inti<u16>`
/// ## Example Usage
/// ```
/// // TODO
/// ```
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


