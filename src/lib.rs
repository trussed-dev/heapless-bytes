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
    ptr,
};

use heapless::Vec;

use serde::{
    de::{Deserialize, Deserializer, Visitor},
    ser::{Serialize, Serializer},
};

#[derive(Clone, Default, Eq)]
pub struct Bytes<const N: usize> {
    bytes: Vec<u8, N>,
}

pub type Bytes8 = Bytes<8>;
pub type Bytes16 = Bytes<16>;
pub type Bytes32 = Bytes<32>;
pub type Bytes64 = Bytes<64>;

impl<const N: usize> From<Vec<u8, N>> for Bytes<N> {
    fn from(vec: Vec<u8, N>) -> Self {
        Self { bytes: vec }
    }
}

impl<const N: usize> Bytes<N> {
    /// Construct a new, empty `Bytes<N>`.
    pub fn new() -> Self {
        Bytes::from(Vec::new())
    }

    // /// Construct a new, empty `Bytes<N>` with the specified capacity.
    // pub fn with_capacity(cap: usize) -> Self {
    //     Bytes<N>::from(Vec::with_capacity(cap))
    // }

    /// Wrap existing bytes in a `Bytes<N>`.
    pub fn from<T: Into<Vec<u8, N>>>(bytes: T) -> Self {
        Bytes {
            bytes: bytes.into(),
        }
    }

    /// Unwraps the Vec<u8, N>, same as `into_vec`.
    pub fn into_inner(self) -> Vec<u8, N> {
        self.bytes
    }

    /// Unwraps the Vec<u8, N>, same as `into_inner`.
    pub fn into_vec(self) -> Vec<u8, N> {
        self.bytes
    }

    /// Returns an immutable slice view.
    // Add as inherent method as it's annoying to import AsSlice.
    pub fn as_slice(&self) -> &[u8] {
        self.bytes.as_ref()
    }

    /// Returns a mutable slice view.
    // Add as inherent method as it's annoying to import AsSlice.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        self.bytes.as_mut()
    }

    /// Low-noise conversion between lengths.
    ///
    /// We can't implement TryInto since it would clash with blanket implementations.
    pub fn try_convert_into<const M: usize>(&self) -> Result<Bytes<M>, ()> {
        Bytes::<M>::from_slice(self)
    }

    // pub fn try_from_slice(slice: &[u8]) -> core::result::Result<Self, ()> {
    //     let mut bytes = Vec::<u8, N>::new();
    //     bytes.extend_from_slice(slice)?;
    //     Ok(Self::from(bytes))
    // }

    pub fn from_slice(slice: &[u8]) -> core::result::Result<Self, ()> {
        let mut bytes = Vec::<u8, N>::new();
        bytes.extend_from_slice(slice)?;
        Ok(Self::from(bytes))
    }

    /// Some APIs offer an interface of the form `f(&mut [u8]) -> Result<usize, E>`,
    /// with the contract that the Ok-value signals how many bytes were written.
    ///
    /// This constructor allows wrapping such interfaces in a more ergonomic way,
    /// returning a Bytes willed using `f`.
    ///
    /// It seems it's not possible to do this as an actual `TryFrom` implementation.
    pub fn try_from<E>(
        f: impl FnOnce(&mut [u8]) -> core::result::Result<usize, E>,
    ) -> core::result::Result<Self, E> {
        let mut data = Self::new();
        data.resize_to_capacity();
        let result = f(&mut data);

        result.map(|count| {
            data.resize_default(count).unwrap();
            data
        })
    }

    // pub fn try_from<'a, E>(
    //     f: impl FnOnce(&'a mut [u8]) -> core::result::Result<&'a mut [u8], E>
    // )
    //     -> core::result::Result<Self, E>
    // {
    //     let mut data = Self::new();
    //     data.resize_to_capacity();
    //     let result = f(&mut data);

    //     result.map(|count| {
    //         data.resize_default(count).unwrap();
    //         data
    //     })
    // }

    // cf. https://internals.rust-lang.org/t/add-vec-insert-slice-at-to-insert-the-content-of-a-slice-at-an-arbitrary-index/11008/3
    pub fn insert_slice_at(&mut self, slice: &[u8], at: usize) -> core::result::Result<(), ()> {
        let l = slice.len();
        let before = self.len();

        // make space
        self.bytes.resize_default(before + l)?;

        // move back existing
        let raw: &mut [u8] = &mut self.bytes;
        raw.copy_within(at..before, at + l);

        // insert slice
        raw[at..][..l].copy_from_slice(slice);

        Ok(())
    }

    pub fn insert(&mut self, index: usize, item: u8) -> Result<(), u8> {
        self.insert_slice_at(&[item], index).map_err(|_| item)
    }

    pub fn remove(&mut self, index: usize) -> Result<u8, ()> {
        if index < self.len() {
            unsafe { Ok(self.remove_unchecked(index)) }
        } else {
            Err(())
        }
    }

    pub(crate) unsafe fn remove_unchecked(&mut self, index: usize) -> u8 {
        // the place we are taking from.
        let p = self.bytes.as_mut_ptr().add(index);

        // copy it out, unsafely having a copy of the value on
        // the stack and in the vector at the same time.
        let ret = ptr::read(p);

        // shift everything down to fill in that spot.
        ptr::copy(p.offset(1), p, self.len() - index - 1);

        self.resize_default(self.len() - 1).unwrap();
        ret
    }

    pub fn resize_default(&mut self, new_len: usize) -> core::result::Result<(), ()> {
        self.bytes.resize_default(new_len)
    }

    pub fn resize_to_capacity(&mut self) {
        self.bytes.resize_default(self.bytes.capacity()).ok();
    }

    /// Fallible conversion into differently sized byte buffer.
    pub fn to_bytes<const M: usize>(&self) -> Result<Bytes<M>, ()> {
        Bytes::<M>::from_slice(self)
    }

    #[cfg(feature = "cbor")]
    pub fn from_serialized<T>(t: &T) -> Self
    where
        T: Serialize,
    {
        let mut vec = Vec::<u8, N>::new();
        vec.resize_default(N).unwrap();
        let buffer = vec.deref_mut();

        let writer = serde_cbor::ser::SliceWrite::new(buffer);
        let mut ser = serde_cbor::Serializer::new(writer)
            .packed_format()
            // .pack_starting_with(1)
            // .pack_to_depth(1)
        ;
        t.serialize(&mut ser).unwrap();
        let writer = ser.into_inner();
        let size = writer.bytes_written();
        vec.resize_default(size).unwrap();
        Self::from(vec)
    }
}

// impl<N, E, F> TryFrom<F> for Bytes<N>
// where
//     N: ArrayLength<u8>,
//     F: FnOnce(&mut [u8]) -> Result<usize, E>,
// {
//     type Error = E;

//     fn try_from(f: F) -> Result<Self, Self::Error>  {

//         let mut data = Self::new();
//         data.resize_to_capacity();
//         let result = f(&mut data);

//         result.map(|count| {
//             data.resize_default(count).unwrap();
//             data
//         })
//     }
// }

impl<const N: usize> Debug for Bytes<N> {
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

impl<const N: usize> AsRef<[u8]> for Bytes<N> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<const N: usize> AsMut<[u8]> for Bytes<N> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}

impl<const N: usize> Deref for Bytes<N> {
    type Target = Vec<u8, N>;

    fn deref(&self) -> &Self::Target {
        &self.bytes
    }
}

impl<const N: usize> DerefMut for Bytes<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.bytes
    }
}

// impl Borrow<Bytes> for Bytes<N> {
//     fn borrow(&self) -> &Bytes {
//         Bytes::new(&self.bytes)
//     }
// }

// impl BorrowMut<Bytes> for Bytes<N> {
//     fn borrow_mut(&mut self) -> &mut Bytes {
//         unsafe { &mut *(&mut self.bytes as &mut [u8] as *mut [u8] as *mut Bytes) }
//     }
// }

impl<Rhs, const N: usize> PartialEq<Rhs> for Bytes<N>
where
    Rhs: ?Sized + AsRef<[u8]>,
{
    fn eq(&self, other: &Rhs) -> bool {
        self.as_ref().eq(other.as_ref())
    }
}

impl<Rhs, const N: usize> PartialOrd<Rhs> for Bytes<N>
where
    Rhs: ?Sized + AsRef<[u8]>,
{
    fn partial_cmp(&self, other: &Rhs) -> Option<Ordering> {
        self.as_ref().partial_cmp(other.as_ref())
    }
}

impl<const N: usize> Hash for Bytes<N> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bytes.hash(state);
    }
}

impl<const N: usize> IntoIterator for Bytes<N> {
    type Item = u8;
    type IntoIter = <Vec<u8, N> as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bytes.into_iter()
    }
}

impl<'a, const N: usize> IntoIterator for &'a Bytes<N> {
    type Item = &'a u8;
    type IntoIter = <&'a [u8] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bytes.iter()
    }
}

impl<'a, const N: usize> IntoIterator for &'a mut Bytes<N> {
    type Item = &'a mut u8;
    type IntoIter = <&'a mut [u8] as IntoIterator>::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.bytes.iter_mut()
    }
}

impl<const N: usize> Serialize for Bytes<N> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_bytes(self)
    }
}

// TODO: can we delegate to Vec<u8, N> deserialization instead of reimplementing?
impl<'de, const N: usize> Deserialize<'de> for Bytes<N> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct ValueVisitor<const N: usize>;

        impl<'de, const N: usize> Visitor<'de> for ValueVisitor<N> {
            type Value = Bytes<N>;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a sequence")
            }

            fn visit_bytes<E>(self, v: &[u8]) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                if v.len() > N {
                    // hprintln!("error! own size: {}, data size: {}", N::to_usize(), v.len()).ok();
                    // return Err(E::invalid_length(values.capacity() + 1, &self))?;
                    return Err(E::invalid_length(v.len(), &self))?;
                }
                let mut buf: Vec<u8, N> = Vec::new();
                // avoid unwrapping even though redundant
                match buf.extend_from_slice(v) {
                    Ok(()) => {}
                    Err(()) => {
                        // hprintln!("error! own size: {}, data size: {}", N::to_usize(), v.len()).ok();
                        // return Err(E::invalid_length(values.capacity() + 1, &self))?;
                        return Err(E::invalid_length(v.len(), &self))?;
                    }
                }
                Ok(Bytes::<N>::from(buf))
            }
        }

        deserializer.deserialize_bytes(ValueVisitor)
    }
}

#[cfg(test)]
mod tests_serde {
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
        assert_eq!(&**bytes, &[1]);
        assert!(bytes.extend_from_slice(&[2; 15]).is_ok());
        assert_eq!(&**bytes, &[1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]);
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
            format!("{:?}", Bytes::<10>::from_slice(b"\0abcde\n").unwrap())
        );
    }
}

#[cfg(test)]
#[cfg(feature = "cbor")]
mod tests {
    use super::*;

    #[test]
    fn test_client_data_hash() {
        let mut minimal = [
            0x50u8, 0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39, 0x30, 0x41, 0x42, 0x43,
            0x44, 0x45, 0x46,
        ];

        let client_data_hash: Bytes<17> = serde_cbor::de::from_mut_slice(&mut minimal).unwrap();

        assert_eq!(client_data_hash, b"1234567890ABCDEF");
    }
}
