#![cfg_attr(not(test), no_std)]
//! This crate provides an `AtomicEnum`.
//! This can only be used with C like enumerations.
//!
//! The `gen_atomic_enum!` macro is provided which can be used to create a valid enumeration.
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
    /// *Panics if `order` is [`Acquire`] or [`AcqRel`].*
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

    pub fn swap(&self, val: E, order: Ordering) -> Option<E> {
        match self.0.atomic_swap(val.into(), order).try_into() {
            Ok(en) => Some(en),
            Err(_) => None,
        }
    }

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
            Ok(v) => match v.try_into() {
                Ok(e) => Ok(Some(e)),
                Err(_) => Ok(None),
            },
            Err(v) => match v.try_into() {
                Ok(e) => Err(Some(e)),
                Err(_) => Err(None),
            },
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

/// This macro can be used to generate a C like enumeration,
/// which automaticly implements `impl From<YourStruct> for <youre base type> { ... }` and `Atomize`.
/// You must implement the trait `impl TryFrom<youre base type> for YourStruct` to use the enumeration.
///
/// ## Params
/// 1. The name, which the enumeration
/// 2. The underlying type ([`u8`], [`u16`], [`u32`], [`u64`], [`usize`])
/// 3. List of, `EnumerationField`: `number`
///
/// ## Example
/// ```
/// use atomic_enums::gen_atomic_enum;
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
/// assert_eq!(State::Running as u32, 2);
/// assert_eq!(State::Paused as u32, 3);
/// ```
#[macro_export]
macro_rules! gen_atomic_enum {
    ($name:ident, $b_ty:ty: $($val:ident: $num:expr)*) => {
        #[repr($b_ty)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum $name {
            $(
                $val = $num,
            )*
        }

        impl From<$name> for $b_ty {
            fn from(value: $name) -> Self {
                value as $b_ty
            }
        }

        impl atomic_enums::Atomize<$b_ty> for $name {}
    };
}

macro_rules! gen_atomic_ops_impls {
    ($($at:ty, $typ:ty, $name:ident)*) => {
        $(
            pub type $name<E> = AtomicEnum<E, $at, $typ>;

            impl AtomicOps<$typ> for $at {
                fn atomic_new(v: $typ) -> Self {
                    Self::new(v)
                }

                fn atomic_compare_exchange(&self, curr: $typ, new: $typ, success: Ordering, failure: Ordering) -> Result<$typ, $typ> {
                    self.compare_exchange(curr, new, success, failure)
                }

                fn atomic_load(&self, order: Ordering) -> $typ {
                    self.load(order)
                }

                fn atomic_store(&self, v: $typ, order: Ordering) {
                    self.store(v, order)
                }

                fn atomic_swap(&self, v: $typ, order: Ordering) -> $typ {
                    self.swap(v, order)
                }
            }
        )*
    };
}

gen_atomic_ops_impls!(
    atomic::AtomicU8, u8, AtomicEnumU8
    atomic::AtomicU16, u16, AtomicEnumU16
    atomic::AtomicU32, u32, AtomicEnumU32
);

#[cfg(feature = "usize")]
gen_atomic_ops_impls!(atomic::AtomicUsize, usize, AtomicEnumUsize);

#[cfg(feature = "u64")]
gen_atomic_ops_impls!(atomic::AtomicU64, u64, AtomicEnumU64);

#[cfg(test)]
mod tests {
    use core::{
        marker::PhantomData,
        sync::atomic::{self, Ordering::Relaxed},
    };

    use paste::item;

    use super::*;

    macro_rules! gen_tests {
        ($($bty:ty, $aty:ty, $abasety:ty)*) => {
            $(
                impl TryFrom<$bty> for TestEnum {
                    type Error = ();

                    fn try_from(value: $bty) -> Result<Self, Self::Error> {
                        match value {
                            1 => Ok(Self::Init),
                            2 => Ok(Self::Idle),
                            3 => Ok(Self::Running),
                            4 => Ok(Self::Stopped),
                            _ => Err(())
                        }
                    }
                }

                impl From<TestEnum> for $bty {
                    fn from(value: TestEnum) -> Self {
                        value as Self
                    }
                }

                item!{
                    #[test]
                    fn [<new_$bty>]() {
                        let new_enum = $aty::new(TestEnum::Init);

                        assert_eq!(new_enum.0.load(Relaxed), TestEnum::Init.into());
                    }

                    #[test]
                    fn [<load_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(TestEnum::Idle.into());

                        let result = test_enum.load(Relaxed);
                        assert!(result.is_some(), "Must return Some(TestEnum::Idle)");

                        let result = result.unwrap();
                        assert_eq!(result, TestEnum::Idle);
                    }

                    #[test]
                    fn [<store_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(TestEnum::Stopped.into());

                        test_enum.store(TestEnum::Idle, Relaxed);

                        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Idle.into());
                    }

                    #[test]
                    fn [<cmp_exc_false_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(TestEnum::Running.into());

                        let result =
                            test_enum.compare_exchange(TestEnum::Idle, TestEnum::Running, Relaxed, Relaxed);
                        assert!(result.is_err());

                        let result = result.unwrap_err();
                        assert!(result.is_some());

                        let result = result.unwrap();
                        assert_eq!(result, TestEnum::Running);

                        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Running.into())
                    }

                    #[test]
                    fn [<cmp_exc_true_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(TestEnum::Running.into());

                        let result =
                            test_enum.compare_exchange(TestEnum::Running, TestEnum::Idle, Relaxed, Relaxed);
                        assert!(result.is_ok());

                        let result = result.unwrap();
                        assert!(result.is_some());

                        let result = result.unwrap();
                        assert_eq!(result, TestEnum::Running);

                        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Idle.into());
                    }

                    #[test]
                    fn [<swap_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(TestEnum::Init.into());

                        let result = test_enum.swap(TestEnum::Stopped, Relaxed);

                        assert!(result.is_some());

                        let result = result.unwrap();
                        assert_eq!(result, TestEnum::Init);

                        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Stopped.into());
                    }

                    #[test]
                    fn [<load_invalid_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(32);

                        let result = test_enum.load(Relaxed);

                        assert!(result.is_none());
                    }

                    #[test]
                    fn [<swap_comp_invalid_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(255);

                        let result = test_enum.swap(TestEnum::Running, Relaxed);

                        assert!(result.is_none());
                        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Running.into());
                    }

                    #[test]
                    fn [<compare_exchange_false_invalid_$bty>]() {
                        let test_enum: $aty<TestEnum> = init_enum(64);

                        let result = test_enum.compare_exchange(TestEnum::Running, TestEnum::Idle, Relaxed, Relaxed);

                        assert!(result.is_err());
                        assert!(result.unwrap_err().is_none());
                    }
                }
            )*
        };
    }

    fn init_enum<A: AtomicOps<U>, U>(val: U) -> AtomicEnum<TestEnum, A, U> {
        AtomicEnum {
            0: A::atomic_new(val),
            1: PhantomData,
            2: PhantomData,
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum TestEnum {
        Init = 1,
        Idle = 2,
        Running = 3,
        Stopped = 4,
    }

    gen_tests!(
        u8, AtomicEnumU8, atomic::AtomicU8
        u16, AtomicEnumU16, atomic::AtomicU16
        u32, AtomicEnumU32, atomic::AtomicU32
    );

    #[cfg(feature = "u64")]
    gen_tests!(u64, AtomicEnumU64, atomic::AtomicU64);

    #[cfg(feature = "usize")]
    gen_tests!(usize, AtomicEnumUsize, atomic::AtomicUsize);
}
