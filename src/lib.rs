//! # heapless-bytes
//!
//! Newtype around heapless byte Vec with efficient serde.

#![cfg_attr(not(test), no_std)]
#![allow(clippy::result_unit_err)]

use core::{
    cmp::Ordering,
    fmt::{self, Debug},
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
};

use heapless::{
    vec::{OwnedVecStorage, Vec as UpstreamVec, VecInner as UpstreamVecInner, ViewVecStorage},
    CapacityError,
};

type VecInner<T, S> = UpstreamVecInner<T, usize, S>;
type Vec<T, const N: usize> = UpstreamVec<T, N, usize>;

use serde::{
    de::{Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
};
use storage::BytesStorage;

mod storage {
    use super::{BytesInner, BytesView};
    use heapless::vec::{OwnedVecStorage, VecStorage, ViewVecStorage};

    /// Trait defining how data for a Byte buffer is stored.
    ///
    /// There's two implementations available:
    ///
    /// - [`OwnedStorage`]: stores the data in an array whose size is known at compile time.
    /// - [`ViewStorage`]: stores the data in an unsized slice
    ///
    /// This allows [`BytesInner`] to be generic over either sized or unsized storage. The [`heapless-bytes`](crate)
    /// crate contains a [`BytesInner`] struct that's generic on [`BytesStorage`],
    /// and two type aliases for convenience:
    ///
    /// - [`String<N>`](crate::string::String) = `StringInner<OwnedStorage<u8, N>>`
    /// - [`StringView<T>`](crate::string::StringView) = `StringInner<ViewStorage<u8>>`
    ///
    /// `String` can be unsized into `StrinsgView`, either by unsizing coercions such as `&mut String -> &mut StringView` or
    /// `Box<String> -> Box<StringView>`, or explicitly with [`.as_view()`](crate::string::String::as_view) or [`.as_mut_view()`](crate::string::String::as_mut_view).
    ///
    /// This trait is sealed, so you cannot implement it for your own types. You can only use
    /// the implementations provided by this crate.
    ///
    /// [`StringInner`]: super::StringInner
    /// [`String`]: super::String
    /// [`OwnedStorage`]: super::OwnedStorage
    /// [`ViewStorage`]: super::ViewStorage
    pub trait BytesStorage: BytesStorageSealed {}
    pub trait BytesStorageSealed: VecStorage<u8> {
        fn as_byte_view(this: &BytesInner<Self>) -> &BytesView
        where
            Self: BytesStorage;
        fn as_byte_mut_view(this: &mut BytesInner<Self>) -> &mut BytesView
        where
            Self: BytesStorage;
    }

    impl<const N: usize> BytesStorage for OwnedVecStorage<u8, N> {}
    impl<const N: usize> BytesStorageSealed for OwnedVecStorage<u8, N> {
        fn as_byte_view(this: &BytesInner<Self>) -> &BytesView
        where
            Self: BytesStorage,
        {
            this
        }
        fn as_byte_mut_view(this: &mut BytesInner<Self>) -> &mut BytesView
        where
            Self: BytesStorage,
        {
            this
        }
    }

    impl BytesStorage for ViewVecStorage<u8> {}

    impl BytesStorageSealed for ViewVecStorage<u8> {
        fn as_byte_view(this: &BytesInner<Self>) -> &BytesView
        where
            Self: BytesStorage,
        {
            this
        }
        fn as_byte_mut_view(this: &mut BytesInner<Self>) -> &mut BytesView
        where
            Self: BytesStorage,
        {
            this
        }
    }
}

pub type OwnedBytesStorage<const N: usize> = OwnedVecStorage<u8, N>;
pub type ViewBytesStorage = ViewVecStorage<u8>;

pub struct BytesInner<S: BytesStorage + ?Sized> {
    bytes: VecInner<u8, S>,
}

pub type Bytes<const N: usize> = BytesInner<OwnedBytesStorage<N>>;
pub type BytesView = BytesInner<ViewBytesStorage>;

pub type Bytes8 = Bytes<8>;
pub type Bytes16 = Bytes<16>;
pub type Bytes32 = Bytes<32>;
pub type Bytes64 = Bytes<64>;

impl<const N: usize> Clone for Bytes<N> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
        }
    }
}

impl<S: BytesStorage + ?Sized> Eq for BytesInner<S> {}
impl<S: BytesStorage + ?Sized> Ord for BytesInner<S> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.bytes.cmp(&other.bytes)
    }
}

#[cfg(feature = "heapless-0.9")]
impl<const N: usize, const M: usize> From<Vec<u8, M>> for Bytes<N> {
    fn from(vec: Vec<u8, M>) -> Self {
        Bytes { bytes: vec }.increase_capacity()
    }
}

#[cfg(feature = "heapless-0.9")]
impl<const N: usize, const M: usize> From<Bytes<M>> for Vec<u8, N> {
    fn from(value: Bytes<M>) -> Self {
        value.increase_capacity().bytes
    }
}

impl<const N: usize> TryFrom<&[u8]> for Bytes<N> {
    type Error = CapacityError;
    fn try_from(value: &[u8]) -> Result<Self, CapacityError> {
        Ok(Self {
            bytes: Vec::from_slice(value)?,
        })
    }
}

impl<const N: usize> Default for Bytes<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> Bytes<N> {
    /// Construct a new, empty `Bytes<N>`.
    pub const fn new() -> Self {
        Self { bytes: Vec::new() }
    }
    /// Get the capacity of the buffer.
    ///
    /// Always equal to the `N` const generic.
    pub const fn const_capacity(&self) -> usize {
        N
    }

    /// Copy the contents of this `Bytes` instance into a new instance with a higher capacity.
    ///
    /// ```
    /// # use heapless_bytes::Bytes;
    /// let bytes32: Bytes<32> = Bytes::from([0; 32]);
    /// let bytes64: Bytes<64> = bytes32.increase_capacity();
    /// assert_eq!(bytes64.len(), 32);
    /// assert_eq!(bytes64.capacity(), 64);
    /// ```
    ///
    /// Decreasing the capacity causes a compiler error:
    /// ```compile_fail
    /// # use heapless_bytes::Bytes;
    /// let bytes32: Bytes<32> = Bytes::from([0; 32]);
    /// let bytes16: Bytes<16> = bytes32.increase_capacity();
    /// ```
    pub fn increase_capacity<const M: usize>(&self) -> Bytes<M> {
        let () = AssertLessThanEq::<N, M>::ASSERT;
        let mut bytes = Vec::new();
        // bytes has length 0 and capacity M, self has length N, N <= M, so this can never panic
        bytes.extend_from_slice(self.as_slice()).unwrap();
        Bytes { bytes }
    }

    /// Get a "view" to the Buffer with the `N` const generic erased
    pub fn as_view(&self) -> &BytesView {
        self
    }

    /// Get a mutable "view" to the Buffer with the `N` const generic erased
    pub fn as_mut_view(&mut self) -> &mut BytesView {
        self
    }
}

impl<S: BytesStorage + ?Sized> BytesInner<S> {
    pub fn as_ptr(&self) -> *const u8 {
        self.bytes.as_ptr()
    }

    /// Returns a raw pointer to the vector’s buffer, which may be mutated through
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        self.bytes.as_mut_ptr()
    }

    /// Extracts a slice containing the entire buffer.
    pub fn as_slice(&self) -> &[u8] {
        self.bytes.as_slice()
    }

    /// Extracts a mutable slice containing the entire buffer.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.bytes.as_mut_slice()
    }

    /// Get the capacity of the buffer.
    ///
    /// Always equal to the `N` const generic.
    pub fn capacity(&self) -> usize {
        self.bytes.capacity()
    }

    /// Clear the buffer, making it empty
    pub fn clear(&mut self) {
        self.bytes.clear()
    }

    /// Extends the buffer from an iterator.
    ///
    /// # Panic
    ///
    /// Panics if the buffer cannot hold all elements of the iterator.
    #[deprecated(
        since = "0.4.0",
        note = "Panics when out of capacity, use try_extend instead"
    )]
    pub fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        self.bytes.extend(iter)
    }

    /// Extends the buffer from an iterator.
    ///
    /// Returns [`Err`] if out of capacity
    pub fn try_extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) -> Result<(), ()> {
        for b in iter {
            self.push(b)?;
        }
        Ok(())
    }

    /// Extend the buffer with the contents of a slice
    pub fn extend_from_slice(&mut self, other: &[u8]) -> Result<(), CapacityError> {
        self.bytes.extend_from_slice(other)
    }

    /// Removes the last byte from the buffer and returns it, or `None` if it's empty
    pub fn pop(&mut self) -> Option<u8> {
        self.bytes.pop()
    }

    /// Appends a byte to the back of the collection
    pub fn push(&mut self, byte: u8) -> Result<(), ()> {
        self.bytes.push(byte).map_err(drop)
    }

    /// Removes the last byte from the buffer and returns it
    ///
    /// # Safety
    ///
    /// This assumes the buffer to have at least one element.
    pub unsafe fn pop_unchecked(&mut self) -> u8 {
        unsafe { self.bytes.pop_unchecked() }
    }

    /// Appends a byte to the back of the buffer
    ///
    /// # Safety
    ///
    /// This assumes the buffer is not full.
    pub unsafe fn push_unchecked(&mut self, byte: u8) {
        unsafe {
            self.bytes.push_unchecked(byte);
        }
    }

    /// Shortens the buffer, keeping the first `len` elements and dropping the rest.
    pub fn truncate(&mut self, len: usize) {
        self.bytes.truncate(len)
    }

    /// Resizes the buffer in-place so that len is equal to new_len.
    ///
    /// If new_len is greater than len, the buffer is extended by the
    /// difference, with each additional slot filled with `value`. If
    /// `new_len` is less than `len`, the buffer is simply truncated.
    ///
    /// See also [`resize_zero`](Self::resize_zero).
    pub fn resize(&mut self, new_len: usize, value: u8) -> Result<(), CapacityError> {
        self.bytes.resize(new_len, value)
    }

    /// Resizes the buffer in-place so that len is equal to new_len.
    ///
    /// If new_len is greater than len, the buffer is extended by the
    /// difference, with each additional slot filled with `0`. If
    /// `new_len` is less than `len`, the buffer is simply truncated.
    pub fn resize_zero(&mut self, new_len: usize) -> Result<(), CapacityError> {
        self.bytes.resize_default(new_len)
    }

    /// Forces the length of the buffer to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type. Normally changing the length of a buffer
    /// is done using one of the safe operations instead, such as
    /// [`truncate`], [`resize`], [`extend`], or [`clear`].
    ///
    /// [`truncate`]: Self::truncate
    /// [`resize`]: Self::resize
    /// [`extend`]: core::iter::Extend
    /// [`clear`]: Self::clear
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`capacity()`].
    /// - The elements at `old_len..new_len` must be initialized.
    ///
    /// [`capacity()`]: Self::capacity
    ///
    pub unsafe fn set_len(&mut self, new_len: usize) {
        self.bytes.set_len(new_len)
    }

    /// Removes a byte  from the buffer and returns it.
    ///
    /// The removed byte is replaced by the last byte of the vector.
    ///
    /// This does not preserve ordering, but is *O*(1).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn swap_remove(&mut self, index: usize) -> u8 {
        self.bytes.swap_remove(index)
    }

    /// Removes a byte  from the buffer and returns it.
    ///
    /// The removed byte is replaced by the last byte of the vector.
    ///
    /// This does not preserve ordering, but is *O*(1).
    ///
    /// # Safety
    ///
    /// `index` must not be out of bounds.
    pub unsafe fn swap_remove_unchecked(&mut self, index: usize) -> u8 {
        unsafe { self.bytes.swap_remove_unchecked(index) }
    }

    /// Returns true if the buffer is full
    pub fn is_full(&self) -> bool {
        self.bytes.is_full()
    }

    /// Returns true if the buffer is empty
    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    /// Returns `true` if `needle` is a prefix of the buffer.
    ///
    /// Always returns `true` if `needle` is an empty slice.
    pub fn starts_with(&self, needle: &[u8]) -> bool {
        self.bytes.starts_with(needle)
    }

    /// Returns `true` if `needle` is a suffix of the buffer.
    ///
    /// Always returns `true` if `needle` is an empty slice.
    pub fn ends_with(&self, needle: &[u8]) -> bool {
        self.bytes.ends_with(needle)
    }

    /// Inserts a byte at position `index` within the buffer, shifting all
    /// bytes after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, value: u8) -> Result<(), ()> {
        self.bytes.insert(index, value).map_err(drop)
    }

    /// Removes and return the byte at position `index` within the buffer, shifting all
    /// bytes after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    pub fn remove(&mut self, index: usize) -> u8 {
        self.bytes.remove(index)
    }

    /// Retains only the bytes specified by the predicate.
    ///
    /// In other words, remove all bytes `b` for which `f(&b)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    pub fn retain(&mut self, f: impl FnMut(&u8) -> bool) {
        self.bytes.retain(f)
    }
    /// Retains only the bytes specified by the predicate, passing a mutable reference to it.
    ///
    /// In other words, remove all bytes `b` for which `f(&mut b)` returns `false`.
    /// This method operates in place, visiting each element exactly once in the
    /// original order, and preserves the order of the retained elements.
    pub fn retain_mut(&mut self, f: impl FnMut(&mut u8) -> bool) {
        self.bytes.retain_mut(f)
    }

    pub fn resize_to_capacity(&mut self) {
        self.bytes.resize_default(self.bytes.capacity()).ok();
    }

    /// Low-noise conversion between lengths.
    ///
    /// For an infaillible version when `M` is known to be larger than `N`, see [`increase_capacity`](Self::increase_capacity)
    pub fn resize_capacity<const M: usize>(&self) -> Result<Bytes<M>, CapacityError> {
        Bytes::try_from(&**self)
    }
}

/// Construct a `Bytes<N>` instance from an array with `N` elements.
///
/// Currently, the array is copied, but a more efficient implementation could be used in the
/// future.
///
/// ```
/// # use heapless_bytes::Bytes;
/// let bytes: Bytes<3> = Bytes::from([0, 1, 2]);
/// ```
///
/// Length mismatches cause a compiler error:
/// ```compile_fail
/// # use heapless_bytes::Bytes;
/// let bytes: Bytes<3> = Bytes::from([0, 1]);  // does not compile
/// ```
/// ```compile_fail
/// # use heapless_bytes::Bytes;
/// let bytes: Bytes<3> = Bytes::from([0, 1, 2, 3]);  // does not compile
/// ```
impl<const N: usize> From<[u8; N]> for Bytes<N> {
    fn from(bytes: [u8; N]) -> Self {
        Self::from(&bytes)
    }
}

struct AssertLessThanEq<const I: usize, const J: usize>;

impl<const I: usize, const J: usize> AssertLessThanEq<I, J> {
    const ASSERT: () = assert!(I <= J, "Cannot convert infallibly between two arrays when the capacity of the new array is not sufficient");
}

/// Construct a `Bytes<N>` instance by copying from an array with `N` or less elements.
///
/// ```
/// # use heapless_bytes::Bytes;
/// let bytes: Bytes<3> = Bytes::from(&[0, 1, 2]);
/// let shorter_bytes: Bytes<3> = Bytes::from(&[0, 1]);
/// ```
///
/// Overlong input data causes a compiler error:
/// ```compile_fail
/// # use heapless_bytes::Bytes;
/// let bytes: Bytes<3> = Bytes::from(&[0, 1, 2, 3]);  // does not compile
/// ```
impl<const N: usize, const M: usize> From<&[u8; M]> for Bytes<N> {
    fn from(data: &[u8; M]) -> Self {
        let () = AssertLessThanEq::<M, N>::ASSERT;
        let mut bytes = Vec::new();
        // vec has length 0 and capacity N, bytes has length M, M <= N, so this can never panic
        bytes.extend_from_slice(data).unwrap();
        Bytes { bytes }
    }
}

impl<S: BytesStorage + ?Sized> Debug for BytesInner<S> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: There has to be a better way :'-)

        use core::ascii::escape_default;
        f.write_str("b'")?;
        for byte in &self.bytes {
            write!(f, "{}", escape_default(*byte))?;
        }
        f.write_str("'")?;
        Ok(())
    }
}

impl<S: BytesStorage + ?Sized> AsRef<[u8]> for BytesInner<S> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<S: BytesStorage + ?Sized> AsMut<[u8]> for BytesInner<S> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}

impl<S: BytesStorage + ?Sized> Deref for BytesInner<S> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

impl<S: BytesStorage + ?Sized> DerefMut for BytesInner<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bytes
    }
}

impl<Rhs, S: BytesStorage + ?Sized> PartialEq<Rhs> for BytesInner<S>
where
    Rhs: ?Sized + AsRef<[u8]>,
{
    fn eq(&self, other: &Rhs) -> bool {
        self.as_ref().eq(other.as_ref())
    }
}

impl<Rhs, S: BytesStorage + ?Sized> PartialOrd<Rhs> for BytesInner<S>
where
    Rhs: ?Sized + AsRef<[u8]>,
{
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl<S: BytesStorage + ?Sized> Hash for BytesInner<S> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

#[derive(Clone)]
pub struct IntoIter<const N: usize> {
    inner: <Vec<u8, N> as IntoIterator>::IntoIter,
}

impl<const N: usize> Iterator for IntoIter<N> {
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }
}

impl<const N: usize> IntoIterator for Bytes<N> {
    type Item = u8;
    type IntoIter = IntoIter<N>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.bytes.into_iter(),
        }
    }
}

impl<'a, S: BytesStorage + ?Sized> IntoIterator for &'a BytesInner<S> {
    type Item = &'a u8;
    type IntoIter = <&'a [u8] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bytes.iter()
    }
}

impl<'a, S: BytesStorage + ?Sized> IntoIterator for &'a mut BytesInner<S> {
    type Item = &'a mut u8;
    type IntoIter = <&'a mut [u8] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bytes.iter_mut()
    }
}

impl<S: BytesStorage + ?Sized> Serialize for BytesInner<S> {
    fn serialize<SER>(&self, serializer: SER) -> Result<SER::Ok, SER::Error>
    where
        SER: Serializer,
    {
        serializer.serialize_bytes(self)
    }
}

impl<S: BytesStorage + ?Sized> core::fmt::Write for BytesInner<S> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.bytes.write_str(s)
    }
    fn write_char(&mut self, s: char) -> fmt::Result {
        self.bytes.write_char(s)
    }
    fn write_fmt(&mut self, s: core::fmt::Arguments<'_>) -> fmt::Result {
        self.bytes.write_fmt(s)
    }
}

impl<'de, const N: usize> Deserialize<'de> for Bytes<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<const N: usize>;

        impl<'de, const N: usize> Visitor<'de> for ValueVisitor<N> {
            type Value = Bytes<N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence of bytes")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Bytes::try_from(v).map_err(|_: CapacityError| E::invalid_length(v.len(), &self))
            }

            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::SeqAccess<'de>,
            {
                use serde::de::Error;

                let mut this = Bytes::new();
                while let Some(byte) = seq.next_element()? {
                    this.push(byte)
                        .map_err(|()| A::Error::invalid_length(this.len(), &self))?;
                }
                Ok(this)
            }
        }

        deserializer.deserialize_bytes(ValueVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_test::{assert_tokens, Token};

    #[test]
    fn serde() {
        let mut bytes = Bytes::<0>::new();
        assert!(bytes.push(1).is_err());
        assert_tokens(&bytes, &[Token::Bytes(&[])]);

        let mut bytes = Bytes::<16>::new();
        bytes.push(1).unwrap();
        assert_tokens(&bytes, &[Token::Bytes(&[1])]);
        assert!(bytes.extend_from_slice(&[2; 16]).is_err());
        assert_eq!(&*bytes, &[1]);
        assert!(bytes.extend_from_slice(&[2; 15]).is_ok());
        assert_eq!(&*bytes, &[1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
        assert_tokens(
            &bytes,
            &[Token::Bytes(&[
                1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            ])],
        );
    }

    #[test]
    fn display() {
        assert_eq!(
            r"b'\x00abcde\n'",
            format!(
                "{:?}",
                Bytes::<10>::try_from(b"\0abcde\n".as_slice())
                    .unwrap()
                    .as_view()
            )
        );
    }

    #[test]
    fn from() {
        let _: Bytes<10> = [0; 10].into();
        let _: Bytes<10> = (&[0; 8]).into();
        #[cfg(feature = "heapless-0.9")]
        let _: Bytes<10> = Vec::<u8, 10>::new().into();
        #[cfg(feature = "heapless-0.9")]
        let _: Bytes<10> = Vec::<u8, 9>::new().into();
    }
}
