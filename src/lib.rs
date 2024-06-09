use core::slice;
use std::{
    cmp::Ordering,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ops::{Index, IndexMut},
    ptr::{self, NonNull},
};

/// An allocator for `T` objects, with a block index of `N` bytes.
///
/// If `N` is 1, then `blocks_capacity` will be `u8::MAX`.
/// If `N` is 2, then `blocks_capacity` will be `u16::MAX`.
pub struct OrderedPoolAllocator<'buf, T, const N: usize = { mem::size_of::<usize>() }> {
    physical_block_indices_ptr: *mut [u8; N],
    virtual_block_indices_ptr: *mut [u8; N],
    physical_blocks_ptr: *mut MaybeUninit<T>,
    blocks_len: usize,
    deallocated_blocks_len: usize,
    blocks_capacity: usize,
    _marker: PhantomData<&'buf MaybeUninit<T>>,
}

impl<'buf, T, const N: usize> OrderedPoolAllocator<'buf, T, N> {
    pub fn new_in(buf: &'buf mut [u8]) -> Self {
        let blocks_capacity = usize::MAX
            .min(2usize.pow(8).pow(N as u32) - 1)
            .min(buf.len() / (2 * mem::size_of::<[u8; N]>() + mem::size_of::<MaybeUninit<T>>()));

        unsafe {
            Self {
                physical_block_indices_ptr: buf.as_mut_ptr().cast(),
                virtual_block_indices_ptr: buf
                    .as_mut_ptr()
                    .add(blocks_capacity * mem::size_of::<[u8; N]>())
                    .cast(),
                physical_blocks_ptr: buf
                    .as_mut_ptr()
                    .add(2 * blocks_capacity * mem::size_of::<[u8; N]>())
                    .cast(),
                blocks_len: 0,
                deallocated_blocks_len: 0,
                blocks_capacity,
                _marker: PhantomData,
            }
        }
    }

    /// Allocates a block and returns a pointer to the block.
    ///
    /// This method will always prioritize reallocating an existing deallocated block over allocating
    /// a new block.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if the returned pointer points to an uninitialized instance of `T` when the allocator is dropped.
    pub unsafe fn allocate(&mut self) -> Result<NonNull<T>, AllocError> {
        let physical_block_index = match self.deallocated_blocks_len {
            0 if self.is_full() => return Err(AllocError),
            0 => self.blocks_len,
            _ => {
                let last_deallocated_physical_block_index = Self::bytes_to_usize(unsafe {
                    self.physical_block_indices_ptr
                        .add(self.blocks_capacity - self.deallocated_blocks_len)
                });

                self.deallocated_blocks_len -= 1;
                last_deallocated_physical_block_index
            }
        };

        let virtual_block_index = self.blocks_len;
        self.blocks_len += 1;

        unsafe {
            self.physical_block_indices_ptr
                .add(virtual_block_index)
                .write(Self::usize_to_bytes(physical_block_index));

            self.virtual_block_indices_ptr
                .add(physical_block_index)
                .write(Self::usize_to_bytes(virtual_block_index));

            Ok(NonNull::new_unchecked(
                self.physical_blocks_ptr.add(physical_block_index).cast(),
            ))
        }
    }

    /// Deallocates the block at the specified pointer.
    ///
    /// Side effect: swaps the virtual block indices of the specified block with the last allocated virtual block.
    ///
    /// # Safety
    ///
    /// Behavior is undefined if any of the following conditions are violated:
    ///
    /// * `ptr` must point to an instance of `T` allocated by this allocator.
    ///
    /// * `ptr` must not point to an instance of `T` that has already been dropped or deallocated by this allocator.
    pub unsafe fn deallocate(&mut self, ptr: NonNull<T>) {
        if self.is_empty() {
            return;
        }

        let physical_block_index =
            ptr.as_ptr().offset_from(self.physical_blocks_ptr.cast()) as usize;

        let virtual_block_index =
            Self::bytes_to_usize(self.virtual_block_indices_ptr.add(physical_block_index));

        let last_allocated_virtual_block_index = self.blocks_len - 1;

        unsafe {
            let last_allocated_physical_block_index = Self::bytes_to_usize(
                self.physical_block_indices_ptr
                    .add(last_allocated_virtual_block_index),
            );

            ptr::swap(
                self.physical_block_indices_ptr.add(virtual_block_index),
                self.physical_block_indices_ptr
                    .add(last_allocated_virtual_block_index),
            );

            self.virtual_block_indices_ptr
                .add(last_allocated_physical_block_index)
                .write(Self::usize_to_bytes(virtual_block_index));
        }

        let deallocated_virtual_block_index =
            self.blocks_capacity - self.deallocated_blocks_len - 1;

        unsafe {
            self.physical_block_indices_ptr
                .add(deallocated_virtual_block_index)
                .write(Self::usize_to_bytes(physical_block_index));
        }

        self.blocks_len -= 1;
        self.deallocated_blocks_len += 1;

        ptr.as_ptr().drop_in_place();
    }

    pub const fn len(&self) -> usize {
        self.blocks_len
    }

    pub const fn capacity(&self) -> usize {
        self.blocks_capacity
    }

    pub const fn is_empty(&self) -> bool {
        self.blocks_len == 0
    }

    pub const fn is_full(&self) -> bool {
        self.blocks_len == self.blocks_capacity
    }

    pub fn sort_unstable_by<F>(&mut self, mut compare: F)
    where
        F: FnMut(&MaybeUninit<T>, &MaybeUninit<T>) -> Ordering,
    {
        let blocks_len = self.blocks_len;
        let physical_blocks_ptr = self.physical_blocks_ptr;

        unsafe {
            slice::from_raw_parts_mut(self.physical_block_indices_ptr, self.blocks_capacity)
                [..blocks_len]
                .sort_unstable_by(|a, b| {
                    compare(
                        &*physical_blocks_ptr.add(Self::bytes_to_usize(a.as_ptr().cast())),
                        &*physical_blocks_ptr.add(Self::bytes_to_usize(b.as_ptr().cast())),
                    )
                });

            for virtual_block_index in 0..blocks_len {
                let physical_block_index =
                    Self::bytes_to_usize(self.physical_block_indices_ptr.add(virtual_block_index));

                self.virtual_block_indices_ptr
                    .add(physical_block_index)
                    .write(Self::usize_to_bytes(virtual_block_index))
            }
        }
    }

    fn bytes_to_usize(block_index: *const [u8; N]) -> usize {
        if N == mem::size_of::<usize>() {
            unsafe { return usize::from_le_bytes(*block_index.cast()) }
        }

        let mut buf = [0u8; mem::size_of::<usize>()];

        unsafe {
            ptr::copy_nonoverlapping(
                block_index.cast(),
                buf.as_mut_ptr(),
                N.min(mem::size_of::<usize>()),
            )
        }

        usize::from_le_bytes(buf)
    }

    fn usize_to_bytes(block_index: usize) -> [u8; N] {
        if N == mem::size_of::<usize>() {
            unsafe { return *block_index.to_le_bytes().as_ptr().cast() }
        }

        let mut buf = [0u8; N];

        unsafe {
            ptr::copy_nonoverlapping(
                block_index.to_le_bytes().as_mut_ptr(),
                buf.as_mut_ptr(),
                N.min(mem::size_of::<usize>()),
            )
        }

        buf
    }
}

impl<T, const N: usize> Index<usize> for OrderedPoolAllocator<'_, T, N> {
    type Output = MaybeUninit<T>;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            let physical_block_index =
                Self::bytes_to_usize(self.physical_block_indices_ptr.add(index));

            &*self.physical_blocks_ptr.add(physical_block_index)
        }
    }
}

impl<T, const N: usize> IndexMut<usize> for OrderedPoolAllocator<'_, T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe {
            let physical_block_index =
                Self::bytes_to_usize(self.physical_block_indices_ptr.add(index));

            &mut *self.physical_blocks_ptr.add(physical_block_index)
        }
    }
}

impl<T, const N: usize> Drop for OrderedPoolAllocator<'_, T, N> {
    fn drop(&mut self) {
        for i in 0..self.blocks_len {
            unsafe {
                let physical_block_index =
                    Self::bytes_to_usize(self.physical_block_indices_ptr.add(i));

                self.physical_blocks_ptr
                    .add(physical_block_index)
                    .cast::<T>()
                    .drop_in_place()
            }
        }
    }
}

#[derive(Debug)]
pub struct AllocError;

#[cfg(test)]
mod tests {
    use rand::{rngs::ThreadRng, Rng};

    use super::*;

    #[repr(transparent)]
    struct SecureU32(u32);

    impl Drop for SecureU32 {
        fn drop(&mut self) {
            self.0 = 0;
        }
    }

    #[test]
    fn allocate_and_deallocate() {
        unsafe {
            let mut buf = [0u8; 128];
            let mut sut = OrderedPoolAllocator::<u32, 1>::new_in(&mut buf);

            assert_eq!(0, sut.len());
            assert_eq!(21, sut.capacity());
            assert_eq!(true, sut.is_empty());
            assert_eq!(false, sut.is_full());

            for (i, value) in [2, 3, 1].into_iter().enumerate() {
                sut.allocate().unwrap_unchecked().as_ptr().write(value);
                assert_eq!(value, sut[i].assume_init())
            }

            assert_eq!(3, sut.len());
            assert_eq!(false, sut.is_empty());

            let ptr = NonNull::new_unchecked(sut[0].as_mut_ptr());
            sut.deallocate(ptr);
            assert_eq!(2, sut.len());

            for (i, value) in [1, 3].into_iter().enumerate() {
                assert_eq!(value, sut[i].assume_init())
            }

            sut.allocate().unwrap_unchecked().as_ptr().write(2);
            assert_eq!(3, sut.len());

            for (i, value) in [1, 3, 2].into_iter().enumerate() {
                assert_eq!(value, sut[i].assume_init())
            }
        }
    }

    #[test]
    fn allocate_and_deallocate_at_scale() {
        unsafe fn allocate(sut: &mut OrderedPoolAllocator<SecureU32, 1>, value: u32) {
            let ptr = sut.allocate().unwrap_unchecked();
            assert_eq!(0, ptr.as_ref().0);
            ptr.as_ptr().write(SecureU32(value))
        }

        unsafe fn deallocate(sut: &mut OrderedPoolAllocator<SecureU32, 1>, rng: &mut ThreadRng) {
            let i = rng.gen_range(0..sut.len());
            let ptr = NonNull::new_unchecked(sut[i].as_mut_ptr());
            sut.deallocate(ptr);
            assert_eq!(0, ptr.as_ref().0)
        }

        unsafe {
            let mut buf = [0u8; 128];
            let mut sut = OrderedPoolAllocator::<SecureU32, 1>::new_in(&mut buf);
            let mut rng = rand::thread_rng();

            for _ in 0..20_000_000 {
                if sut.is_empty() {
                    allocate(&mut sut, u32::MAX)
                } else if sut.is_full() {
                    deallocate(&mut sut, &mut rng)
                } else if rng.gen_bool(0.5) {
                    allocate(&mut sut, u32::MAX)
                } else {
                    deallocate(&mut sut, &mut rng)
                }
            }
        }
    }

    #[test]
    fn sort_unstable_by() {
        unsafe {
            let mut buf = [0u8; 128];
            let mut sut = OrderedPoolAllocator::<u32, 1>::new_in(&mut buf);

            for value in [2, 3, 1] {
                sut.allocate().unwrap_unchecked().as_ptr().write(value)
            }

            sut.sort_unstable_by(|a, b| a.assume_init_ref().cmp(b.assume_init_ref()));

            for (i, value) in [1, 2, 3].into_iter().enumerate() {
                assert_eq!(value, sut[i].assume_init())
            }

            let ptr = NonNull::new_unchecked(sut[0].as_mut_ptr());
            sut.deallocate(ptr);

            for (i, value) in [3, 2].into_iter().enumerate() {
                assert_eq!(value, sut[i].assume_init())
            }

            sut.allocate().unwrap_unchecked().as_ptr().write(4);

            for (i, value) in [3, 2, 4].into_iter().enumerate() {
                assert_eq!(value, sut[i].assume_init())
            }

            sut.sort_unstable_by(|a, b| a.assume_init_ref().cmp(b.assume_init_ref()));

            for (i, value) in [2, 3, 4].into_iter().enumerate() {
                assert_eq!(value, sut[i].assume_init())
            }
        }
    }

    #[test]
    fn drop() {
        unsafe {
            let mut buf = [0u8; 128];
            let mut sut = OrderedPoolAllocator::<SecureU32, 1>::new_in(&mut buf);

            let ptr = sut.allocate().unwrap_unchecked();
            ptr.as_ptr().write(SecureU32(u32::MAX));

            mem::drop(sut);

            assert_eq!(0, ptr.as_ref().0)
        }
    }
}
