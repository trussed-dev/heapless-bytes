use crate::storage::BytesStorage;
use bytes::{buf::UninitSlice, BufMut};
use heapless::LenType;

unsafe impl<S: BytesStorage + ?Sized, LenT: LenType> BufMut for crate::BytesInner<LenT, S> {
    fn remaining_mut(&self) -> usize {
        self.capacity() - self.len()
    }
    unsafe fn advance_mut(&mut self, cnt: usize) {
        self.set_len(cnt);
    }
    fn chunk_mut(&mut self) -> &mut UninitSlice {
        // SAFETY: add is safe because once the length is added is less than the buffer and therefore
        // always in the "allocation" bounds
        let ptr = unsafe { self.bytes.as_mut_ptr().add(self.len()) };
        let len = self.capacity() - self.len();
        unsafe { UninitSlice::from_raw_parts_mut(ptr, len) }
    }
}

#[cfg(test)]
mod tests {
    use crate::{Bytes, BytesView};
    use bytes::BufMut;

    #[test]
    #[should_panic]
    fn buf_mut_advance_mut_out_of_bounds() {
        let mut bytes: Bytes<8> = Bytes::new();
        unsafe { bytes.advance_mut(9) };
    }

    #[test]
    fn buf_mut_remaining_mut() {
        let mut bytes: Bytes<8> = Bytes::new();
        assert_eq!(bytes.remaining_mut(), 8);
        bytes.push(42).unwrap();
        assert_eq!(bytes.remaining_mut(), 7);
    }

    #[test]
    fn buf_mut_chunk_mut() {
        let mut bytes: Bytes<8> = Bytes::new();
        assert_eq!(bytes.chunk_mut().len(), 8);
        unsafe { bytes.advance_mut(1) };
        assert_eq!(bytes.chunk_mut().len(), 7);
    }

    #[test]
    #[should_panic]
    fn view_buf_mut_advance_mut_out_of_bounds() {
        let mut bytes: Bytes<8> = Bytes::new();
        let bytes: &mut BytesView = &mut bytes;
        unsafe { bytes.advance_mut(9) };
    }

    #[test]
    fn view_buf_mut_remaining_mut() {
        let mut bytes: Bytes<8> = Bytes::new();
        let bytes: &mut BytesView = &mut bytes;
        assert_eq!(bytes.remaining_mut(), 8);
        bytes.push(42).unwrap();
        assert_eq!(bytes.remaining_mut(), 7);
    }

    #[test]
    fn view_buf_mut_chunk_mut() {
        let mut bytes: Bytes<8> = Bytes::new();
        let bytes: &mut BytesView = &mut bytes;
        assert_eq!(bytes.chunk_mut().len(), 8);
        unsafe { bytes.advance_mut(1) };
        assert_eq!(bytes.chunk_mut().len(), 7);
    }
}
