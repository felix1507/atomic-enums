#![feature(prelude_import)]
#![no_std]
//! This crate provides an `AtomicEnum`.
//! This can only be used with C like enumerations.
//!
//! The `gen_atomic_enum!` macro is provided which can be used to create a valid enumeration.
#[prelude_import]
use core::prelude::rust_2021::*;
#[macro_use]
extern crate core;
#[macro_use]
extern crate compiler_builtins;
use core::fmt::Debug;
use core::marker::PhantomData;
use core::sync::atomic::{self, Ordering};
/// The trait must be implemented for enumerations which shall be used with an `AtomicEnum`.
/// Additionally the traits `Into<u16>` and `TryFrom<u16>` have to be implemented.
pub trait Atomize<T>: TryFrom<T> + Into<T> {}
/// This trait must be implemented for the underlying atomic type.
///
/// The trait is already implemented for:
/// - `AtomicU8`
/// - `AtomicU16`
/// - `AtomicU32`
/// - `AtomicU64` with the `u64` feature.
/// - `AtomicUsize` with the `usize` feature.
pub trait AtomicOps<T> {
    fn atomic_new(v: T) -> Self;
    fn atomic_load(&self, order: Ordering) -> T;
    fn atomic_store(&self, v: T, order: Ordering);
    fn atomic_swap(&self, v: T, order: Ordering) -> T;
    fn atomic_compare_exchange(
        &self,
        curr: T,
        new: T,
        success: Ordering,
        failure: Ordering,
    ) -> Result<T, T>;
}
/// The `AtomicEnum` is used to store values of an C like enumeration in
/// an atomic type.
pub struct AtomicEnum<E, A, U>(A, PhantomData<E>, PhantomData<U>);
impl<E, A, U> AtomicEnum<E, A, U>
where
    E: TryFrom<U> + Into<U>,
    A: AtomicOps<U>,
    U: Copy,
{
    /// Create a new atomic enumeration.
    ///
    /// ## Params
    /// - v: The value with which the enumeration is to be initialized
    ///
    /// ## Returns
    /// A new `AtomicEnum`
    ///
    /// ## Example
    /// ```
    /// use atomic_enums::{gen_atomic_enum, AtomicEnumU32};
    ///
    /// gen_atomic_enum!(State, u32:
    ///     Running: 2
    ///     Paused: 3
    /// );
    ///
    /// impl TryFrom<u32> for State {
    ///     type Error = ();
    ///
    ///     fn try_from(v: u32) -> Result<Self, Self::Error> {
    ///         match v {
    ///             2 => Ok(Self::Running),
    ///             3 => Ok(Self::Paused),
    ///             _ => Err(()),
    ///         }
    ///     }
    /// }
    ///
    /// let state = AtomicEnumU32::new(State::Running);
    ///  /* Do whatever you want to do... */
    /// ```
    pub fn new(v: E) -> Self {
        Self(A::atomic_new(v.into()), PhantomData, PhantomData)
    }
    /// Load the currently stored value of the atomic enum
    ///
    /// The following is copyed from the offical documentation of [`atomic::AtomicU32`].
    ///
    /// *`load` takes an [`Ordering`] argument which describes the memory ordering of this operation.
    /// Possible values are [`Ordering::SeqCst`], [`Ordering::Acquire`] and [`Ordering::Relaxed`].*
    ///
    ///  ## Panics
    ///
    /// *Panics if `order` is [`Ordering::Release`] or [`Ordering::AcqRel`].*
    ///
    /// ## Example
    /// ```
    /// use atomic_enums::{gen_atomic_enum, AtomicEnumU32};
    ///
    /// use core::sync::atomic::Ordering::Relaxed;
    ///
    /// gen_atomic_enum!(State, u32:
    ///     Running: 2
    ///     Paused: 3
    /// );
    ///
    /// impl TryFrom<u32> for State {
    ///     type Error = ();
    ///
    ///     fn try_from(v: u32) -> Result<Self, Self::Error> {
    ///         match v {
    ///             2 => Ok(Self::Running),
    ///             3 => Ok(Self::Paused),
    ///             _ => Err(()),
    ///         }
    ///     }
    /// }
    ///
    /// let state = AtomicEnumU32::new(State::Paused);
    ///
    /// assert_eq!(state.load(Relaxed).unwrap(), State::Paused);
    /// ```
    pub fn load(&self, order: Ordering) -> Option<E> {
        match self.0.atomic_load(order).try_into() {
            Ok(e) => Some(e),
            Err(_) => None,
        }
    }
    /// Store the passed value in the atomic enumeration
    ///
    /// The following is copyed from the offical documentation of [`atomic::AtomicU32::store`].
    ///
    /// `store` takes an [`Ordering`] argument which describes the memory ordering of this operation.
    ///
    /// *Possible values are [`Ordering::SeqCst`], [`Ordering::Release`] and [`Ordering::Relaxed`].*
    ///
    /// ## Panics
    ///
    /// *Panics if `order` is [`Ordering::Acquire`] or [`Ordering::AcqRel`].*
    ///
    /// ## Example
    /// ```
    /// use atomic_enums::{gen_atomic_enum, AtomicEnumU32};
    ///
    /// use core::sync::atomic::Ordering::Relaxed;
    ///
    /// gen_atomic_enum!(State, u32:
    ///     Running: 2
    ///     Paused: 3
    /// );
    ///
    /// impl TryFrom<u32> for State {
    ///     type Error = ();
    ///
    ///     fn try_from(v: u32) -> Result<Self, Self::Error> {
    ///         match v {
    ///             2 => Ok(Self::Running),
    ///             3 => Ok(Self::Paused),
    ///             _ => Err(()),
    ///         }
    ///     }
    /// }
    ///
    /// let state = AtomicEnumU32::new(State::Paused);
    ///
    /// state.store(State::Running, Relaxed);
    ///
    /// assert_eq!(state.load(Relaxed).unwrap(), State::Running);
    /// ```
    pub fn store(&self, val: E, order: Ordering) {
        self.0.atomic_store(val.into(), order)
    }
    /// Stores the passed enum value and returns the previous value.
    ///
    /// The following is copyed from the offical documentation of [`atomic::AtomicU32::swap`].
    ///
    /// *`swap` takes an [`Ordering`] argument which describes the memory ordering
    /// of this operation. All ordering modes are possible. Note that using
    /// [`Ordering::Acquire`] makes the store part of this operation [`Ordering::Relaxed`], and
    /// using [`Ordering::Release`] makes the load part [`Ordering::Relaxed`].*
    ///
    /// ## Example
    /// ```
    /// use atomic_enums::{gen_atomic_enum, AtomicEnumU32};
    ///
    /// use core::sync::atomic::Ordering::Relaxed;
    ///
    /// gen_atomic_enum!(State, u32:
    ///     Running: 2
    ///     Paused: 3
    /// );
    ///
    /// impl TryFrom<u32> for State {
    ///     type Error = ();
    ///
    ///     fn try_from(v: u32) -> Result<Self, Self::Error> {
    ///         match v {
    ///             2 => Ok(Self::Running),
    ///             3 => Ok(Self::Paused),
    ///             _ => Err(()),
    ///         }
    ///     }
    /// }
    ///
    /// let state = AtomicEnumU32::new(State::Paused);
    ///
    /// assert_eq!(state.swap(State::Running, Relaxed).unwrap(), State::Paused);
    /// assert_eq!(state.load(Relaxed).unwrap(), State::Running);
    /// ```
    pub fn swap(&self, val: E, order: Ordering) -> Option<E> {
        match self.0.atomic_swap(val.into(), order).try_into() {
            Ok(en) => Some(en),
            Err(_) => None,
        }
    }
    /// Stores the `new` value, if the `current` value ist equal to the currently stored value.
    ///
    /// The following is copyed from the offical documentation of [`atomic::AtomicU32::compare_exchange`].
    ///
    /// *The return value is a result indicating whether the new value was written and
    /// containing the previous value. On success this value is guaranteed to be equal to
    /// `current`.*
    ///
    /// *`compare_exchange` takes two [`Ordering`] arguments to describe the memory
    /// ordering of this operation. `success` describes the required ordering for the
    /// read-modify-write operation that takes place if the comparison with `current` succeeds.
    /// `failure` describes the required ordering for the load operation that takes place when
    /// the comparison fails. Using [`Ordering::Acquire`] as success ordering makes the store part
    /// of this operation [`Ordering::Relaxed`], and using [`Ordering::Release`] makes the successful load
    /// [`Ordering::Relaxed`].
    /// The failure ordering can only be [`Ordering::SeqCst`], [`Ordering::Acquire`] or [`Ordering::Relaxed`].*
    ///
    /// ## Example
    /// ```
    /// use atomic_enums::{gen_atomic_enum, AtomicEnumU32};
    ///
    /// use core::sync::atomic::Ordering::Relaxed;
    ///
    /// gen_atomic_enum!(State, u32:
    ///     Running: 2
    ///     Paused: 3
    /// );
    ///
    /// impl TryFrom<u32> for State {
    ///     type Error = ();
    ///
    ///     fn try_from(v: u32) -> Result<Self, Self::Error> {
    ///         match v {
    ///             2 => Ok(Self::Running),
    ///             3 => Ok(Self::Paused),
    ///             _ => Err(()),
    ///         }
    ///     }
    /// }
    ///
    /// let state = AtomicEnumU32::new(State::Paused);
    ///
    /// let mut result = state.compare_exchange(
    ///     State::Paused,
    ///     State::Running,
    ///     Relaxed,
    ///     Relaxed,
    /// );
    /// assert_eq!(result.unwrap().unwrap(), State::Paused);
    ///
    /// result = state.compare_exchange(
    ///     State::Paused,
    ///     State::Running,
    ///     Relaxed,
    ///     Relaxed,
    /// );
    ///
    /// assert_eq!(result.unwrap_err().unwrap(), State::Running);
    /// ```
    pub fn compare_exchange(
        &self,
        current: E,
        new: E,
        success: Ordering,
        failure: Ordering,
    ) -> Result<Option<E>, Option<E>> {
        match self
            .0
            .atomic_compare_exchange(current.into(), new.into(), success, failure)
        {
            Ok(v) => {
                match v.try_into() {
                    Ok(e) => Ok(Some(e)),
                    Err(_) => Ok(None),
                }
            }
            Err(v) => {
                match v.try_into() {
                    Ok(e) => Err(Some(e)),
                    Err(_) => Err(None),
                }
            }
        }
    }
}
impl<E, A, U> Debug for AtomicEnum<E, A, U>
where
    E: TryFrom<U> + Into<U> + Debug,
    A: AtomicOps<U>,
    U: Copy,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut dbg_info = f.debug_tuple("AtomicEnum");
        let tmp = self.load(Ordering::Relaxed);
        match tmp {
            Some(v) => dbg_info.field(&v),
            None => dbg_info.field(&"Invalid value!"),
        };
        dbg_info.finish()
    }
}
pub type AtomicEnumU8<E> = AtomicEnum<E, atomic::AtomicU8, u8>;
impl AtomicOps<u8> for atomic::AtomicU8 {
    fn atomic_new(v: u8) -> Self {
        Self::new(v)
    }
    fn atomic_compare_exchange(
        &self,
        curr: u8,
        new: u8,
        success: Ordering,
        failure: Ordering,
    ) -> Result<u8, u8> {
        self.compare_exchange(curr, new, success, failure)
    }
    fn atomic_load(&self, order: Ordering) -> u8 {
        self.load(order)
    }
    fn atomic_store(&self, v: u8, order: Ordering) {
        self.store(v, order)
    }
    fn atomic_swap(&self, v: u8, order: Ordering) -> u8 {
        self.swap(v, order)
    }
}
pub type AtomicEnumU16<E> = AtomicEnum<E, atomic::AtomicU16, u16>;
impl AtomicOps<u16> for atomic::AtomicU16 {
    fn atomic_new(v: u16) -> Self {
        Self::new(v)
    }
    fn atomic_compare_exchange(
        &self,
        curr: u16,
        new: u16,
        success: Ordering,
        failure: Ordering,
    ) -> Result<u16, u16> {
        self.compare_exchange(curr, new, success, failure)
    }
    fn atomic_load(&self, order: Ordering) -> u16 {
        self.load(order)
    }
    fn atomic_store(&self, v: u16, order: Ordering) {
        self.store(v, order)
    }
    fn atomic_swap(&self, v: u16, order: Ordering) -> u16 {
        self.swap(v, order)
    }
}
pub type AtomicEnumU32<E> = AtomicEnum<E, atomic::AtomicU32, u32>;
impl AtomicOps<u32> for atomic::AtomicU32 {
    fn atomic_new(v: u32) -> Self {
        Self::new(v)
    }
    fn atomic_compare_exchange(
        &self,
        curr: u32,
        new: u32,
        success: Ordering,
        failure: Ordering,
    ) -> Result<u32, u32> {
        self.compare_exchange(curr, new, success, failure)
    }
    fn atomic_load(&self, order: Ordering) -> u32 {
        self.load(order)
    }
    fn atomic_store(&self, v: u32, order: Ordering) {
        self.store(v, order)
    }
    fn atomic_swap(&self, v: u32, order: Ordering) -> u32 {
        self.swap(v, order)
    }
}
pub type AtomicEnumUsize<E> = AtomicEnum<E, atomic::AtomicUsize, usize>;
impl AtomicOps<usize> for atomic::AtomicUsize {
    fn atomic_new(v: usize) -> Self {
        Self::new(v)
    }
    fn atomic_compare_exchange(
        &self,
        curr: usize,
        new: usize,
        success: Ordering,
        failure: Ordering,
    ) -> Result<usize, usize> {
        self.compare_exchange(curr, new, success, failure)
    }
    fn atomic_load(&self, order: Ordering) -> usize {
        self.load(order)
    }
    fn atomic_store(&self, v: usize, order: Ordering) {
        self.store(v, order)
    }
    fn atomic_swap(&self, v: usize, order: Ordering) -> usize {
        self.swap(v, order)
    }
}
pub type AtomicEnumU64<E> = AtomicEnum<E, atomic::AtomicU64, u64>;
impl AtomicOps<u64> for atomic::AtomicU64 {
    fn atomic_new(v: u64) -> Self {
        Self::new(v)
    }
    fn atomic_compare_exchange(
        &self,
        curr: u64,
        new: u64,
        success: Ordering,
        failure: Ordering,
    ) -> Result<u64, u64> {
        self.compare_exchange(curr, new, success, failure)
    }
    fn atomic_load(&self, order: Ordering) -> u64 {
        self.load(order)
    }
    fn atomic_store(&self, v: u64, order: Ordering) {
        self.store(v, order)
    }
    fn atomic_swap(&self, v: u64, order: Ordering) -> u64 {
        self.swap(v, order)
    }
}
mod tests {
    use core::{marker::PhantomData, sync::atomic::Ordering::Relaxed};
    use paste::item;
    use super::*;
    fn init_enum<A: AtomicOps<U>, U>(val: U) -> AtomicEnum<TestEnum, A, U> {
        AtomicEnum {
            0: A::atomic_new(val),
            1: PhantomData,
            2: PhantomData,
        }
    }
    enum TestEnum {
        Init = 1,
        Idle = 2,
        Running = 3,
        Stopped = 4,
    }
    #[automatically_derived]
    impl ::core::fmt::Debug for TestEnum {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::write_str(
                f,
                match self {
                    TestEnum::Init => "Init",
                    TestEnum::Idle => "Idle",
                    TestEnum::Running => "Running",
                    TestEnum::Stopped => "Stopped",
                },
            )
        }
    }
    #[automatically_derived]
    impl ::core::clone::Clone for TestEnum {
        #[inline]
        fn clone(&self) -> TestEnum {
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for TestEnum {}
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for TestEnum {}
    #[automatically_derived]
    impl ::core::cmp::PartialEq for TestEnum {
        #[inline]
        fn eq(&self, other: &TestEnum) -> bool {
            let __self_tag = ::core::intrinsics::discriminant_value(self);
            let __arg1_tag = ::core::intrinsics::discriminant_value(other);
            __self_tag == __arg1_tag
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralEq for TestEnum {}
    #[automatically_derived]
    impl ::core::cmp::Eq for TestEnum {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {}
    }
    impl TryFrom<u8> for TestEnum {
        type Error = ();
        fn try_from(value: u8) -> Result<Self, Self::Error> {
            match value {
                1 => Ok(Self::Init),
                2 => Ok(Self::Idle),
                3 => Ok(Self::Running),
                4 => Ok(Self::Stopped),
                _ => Err(()),
            }
        }
    }
    impl From<TestEnum> for u8 {
        fn from(value: TestEnum) -> Self {
            value as Self
        }
    }
    impl TryFrom<u16> for TestEnum {
        type Error = ();
        fn try_from(value: u16) -> Result<Self, Self::Error> {
            match value {
                1 => Ok(Self::Init),
                2 => Ok(Self::Idle),
                3 => Ok(Self::Running),
                4 => Ok(Self::Stopped),
                _ => Err(()),
            }
        }
    }
    impl From<TestEnum> for u16 {
        fn from(value: TestEnum) -> Self {
            value as Self
        }
    }
    impl TryFrom<u32> for TestEnum {
        type Error = ();
        fn try_from(value: u32) -> Result<Self, Self::Error> {
            match value {
                1 => Ok(Self::Init),
                2 => Ok(Self::Idle),
                3 => Ok(Self::Running),
                4 => Ok(Self::Stopped),
                _ => Err(()),
            }
        }
    }
    impl From<TestEnum> for u32 {
        fn from(value: TestEnum) -> Self {
            value as Self
        }
    }
    impl TryFrom<u64> for TestEnum {
        type Error = ();
        fn try_from(value: u64) -> Result<Self, Self::Error> {
            match value {
                1 => Ok(Self::Init),
                2 => Ok(Self::Idle),
                3 => Ok(Self::Running),
                4 => Ok(Self::Stopped),
                _ => Err(()),
            }
        }
    }
    impl From<TestEnum> for u64 {
        fn from(value: TestEnum) -> Self {
            value as Self
        }
    }
}
