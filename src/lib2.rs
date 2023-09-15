use core::marker::PhantomData;
use core::sync::atomic::{self, Ordering};

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

pub struct AtomicEnum<E, A, U>(A, PhantomData<E>, PhantomData<U>);

impl<E, A, U> AtomicEnum<E, A, U>
where
    E: TryFrom<U> + Into<U>,
    A: AtomicOps<U>,
    U: Copy,
{
    pub fn new(v: E) -> Self {
        Self(A::atomic_new(v.into()), PhantomData, PhantomData)
    }

    pub fn load(&self, order: Ordering) -> Option<E> {
        match self.0.atomic_load(order).try_into() {
            Ok(e) => Some(e),
            Err(_) => None,
        }
    }

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

#[cfg(test)]
mod tests {
    use core::{
        marker::PhantomData,
        sync::atomic::{self, Ordering::Relaxed},
    };

    use paste::item;

    use super::*;

    macro_rules! gen_tests {
        ($($bty:ty, $aty:ty)*) => {
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
            )*
        };
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum TestEnum {
        Init = 1,
        Idle = 2,
        Running = 3,
        Stopped = 4,
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

    #[test]
    fn u8_new() {
        let new_enum = AtomicEnumU8::new(TestEnum::Init);

        assert_eq!(new_enum.0.load(Relaxed), TestEnum::Init.into());
    }

    #[test]
    fn u8_load() {
        let test_enum: AtomicEnumU8<TestEnum> = AtomicEnumU8 {
            0: atomic::AtomicU8::new(TestEnum::Idle.into()),
            1: PhantomData,
            2: PhantomData,
        };

        let result = test_enum.load(Relaxed);
        assert!(result.is_some(), "Must return Some(TestEnum::Idle)");

        let result = result.unwrap();
        assert_eq!(result, TestEnum::Idle);
    }

    #[test]
    fn u8_store() {
        let test_enum: AtomicEnumU8<TestEnum> = AtomicEnumU8 {
            0: atomic::AtomicU8::new(TestEnum::Stopped.into()),
            1: PhantomData,
            2: PhantomData,
        };

        test_enum.store(TestEnum::Idle, Relaxed);

        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Idle.into());
    }

    #[test]
    fn u8_cmp_exc_false() {
        let test_enum: AtomicEnumU8<TestEnum> = AtomicEnumU8 {
            0: atomic::AtomicU8::new(TestEnum::Running.into()),
            1: PhantomData,
            2: PhantomData,
        };

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
    fn u8_cmp_exc_true() {
        let test_enum: AtomicEnumU8<TestEnum> = AtomicEnumU8 {
            0: atomic::AtomicU8::new(TestEnum::Running.into()),
            1: PhantomData,
            2: PhantomData,
        };

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
    fn u8_swap() {
        let test_enum: AtomicEnumU8<TestEnum> = AtomicEnumU8 {
            0: atomic::AtomicU8::new(TestEnum::Init.into()),
            1: PhantomData,
            2: PhantomData,
        };

        let result = test_enum.swap(TestEnum::Stopped, Relaxed);

        assert!(result.is_some());

        let result = result.unwrap();
        assert_eq!(result, TestEnum::Init);

        assert_eq!(test_enum.0.load(Relaxed), TestEnum::Stopped.into());
    }
}
