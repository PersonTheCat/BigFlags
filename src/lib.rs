pub struct BigFlag {
    data: Box<[usize]>,
    capacity: usize,
}

/// The number of bits inside of one `usize` number. [`BigFlag`] is designed
/// around this value, which may vary depending on the compile target. This
/// is a performance optimization which is intended mostly to avoid unnecessary
/// casting. In practice, this does matter.
pub const POINTER_WIDTH: usize = 8 * std::mem::size_of();

/// Represents a 1 in the highest position supported by usize. Useful for shift
/// operations and bit comparisons.
pub const HIGHEST_BIT: usize = 1 << (POINTER_WIDTH - 1);

impl BigFlag {
    /// Generates a new [`BigFlag`] instance with the specified capacity.
    /// In the case of BigFlags, `capacity` refers to the highest number
    /// which the data may contain, not the length of the data or how many
    /// elements will be stored in it. `0` will always be the lowest value
    /// it can represent and there is no internal offset to increase it.
    ///
    /// There are checked functions associated with this object which
    /// compare the index being set or retrieved against `capacity`.
    /// However, it is not actually possible to shrink these data down to
    /// the size of `capacity` in bits. As such, the actual size of these
    /// data will be the first multiple of `POINTER_WIDTH` in bits above it.
    ///
    /// [`BigFlag`]: crate::BigFlag
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// const LEN: usize = 63;
    /// let mut bf = BigFlag::new(LEN);
    ///
    /// // Treat the data as an array of numbers.
    /// for i in (0..LEN).step_by(2) {
    ///     bf.set(i);
    /// }
    /// // Keep track of various bitflags.
    /// assert!(bf.read(0, 0b101010101010101)) // culled
    /// ```
    pub fn new(capacity: usize) -> Self {
        Self {
            data: Box::from(vec![0; 1 + (capacity / POINTER_WIDTH)]),
            capacity,
        }
    }

    /// This function is a variant of the main constructor, [`new`]. Unlike
    /// `new`, [`from_raw`] accepts the raw data being stored in the object.
    /// In other words, `data` is an array of bitflags being concatenated
    /// into a single object. `capacity` is assumed to be the exact number
    /// of bits inside of each value in `data`.
    ///
    /// [`new`]: #method.new
    /// [`from_raw`]: #method.from_raw
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// const FLAG_ONE: usize = 0b0100;
    /// const FLAG_TWO: usize = 0b0010;
    /// const OVERLAP: usize = 0b0101;
    ///
    /// let vec = vec![FLAG_ONE | FLAG_TWO, OVERLAP];
    /// let bf = BigFlag::from_raw(vec);
    ///
    /// assert!(bf.read(0, FLAG_ONE | FLAG_TWO));
    /// assert!(bf.read(1, OVERLAP));
    /// ```
    pub fn from_raw(data: Vec<usize>) -> Self {
        Self {
            capacity: data.len() * POINTER_WIDTH,
            data: Box::from(data),
        }
    }

    /// Use this function to safely check whether a value is stored at
    /// the given index inside of this object. The promise made by this
    /// function is that it will never access data outside of the real
    /// space allocated for this object and that it will never read beyond
    /// the expected capacity defined in the constructor.
    ///
    /// In some cases, it may be preferable to defer to the unchecked
    /// variant of this function, [`get_unchecked`], when operating on a
    /// known range of indices. This will provide a small boost in terms
    /// of performance. In most cases, the time saved will be negligible.
    /// However, the tests indicate that it is significant when operating
    /// on large sets of data.
    ///
    /// [`get_unchecked`]: #method.get_unchecked
    #[inline]
    pub fn get(&self, num: usize) -> bool {
        if num > self.capacity {
            return false;
        }
        // SAFETY: the capacity check guarantees we aren't reading
        // out of bounds. This avoids any redundant checks.
        unsafe { self.get_unchecked(num) }
    }

    /// Use this function to insert a flag at the given index inside of
    /// this object. As with [`get`] and [`unset`], this function is
    /// guaranteed to never access unintended space in memory. Likewise,
    /// you may prefer [`set_unchecked`] in cases where you are operating
    /// on a valid range of indices and wish to gain a small boost in
    /// performance.
    ///
    /// # Panics
    ///
    /// This is the first in a line of methods that panics when `num` is
    /// greater than `capacity`.
    ///
    /// [`get`]: #method.get
    /// [`unset`]: #method.unset
    /// [`set_unchecked`]: #method.set_unchecked
    #[inline]
    pub fn set(&mut self, num: usize) {
        if num > self.capacity {
            panic!("out of range: {} > {}", num, self.capacity);
        }
        // SAFETY: see `get` for why this is safe.
        unsafe { self.set_unchecked(num) }
    }

    /// This function is the counterpart to [`set`] which will guarantee
    /// that the given index does not contain a value.
    ///
    /// [`set`]: #method.set
    #[inline]
    pub fn unset(&mut self, num: usize) {
        if num > self.capacity {
            panic!("out of range: {} > {}", num, self.capacity);
        }
        // SAFETY: see `get` for why this is safe.
        unsafe { self.unset_unchecked(num) }
    }

    /// This function is a variant of [`get`] which works not by reading a
    /// single value as an index of bits, but by treating each bit in the
    /// number as a flag. The result is true only if each flag is present
    /// in the data at the given offset.
    ///
    /// [`get`]: #method.get
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.set(1);
    /// bf.set(2);
    /// bf.set(3);
    ///
    /// assert!(bf.read(0, 0b111))
    /// ```
    #[inline]
    pub fn read(&self, offset: usize, flags: usize) -> bool {
        if offset * POINTER_WIDTH + self.capacity % POINTER_WIDTH > self.capacity {
            return false;
        }
        // SAFETY: comparing the flags and offset against
        // capacity also guarantees that we are safe.
        unsafe { self.read_unchecked(offset, flags) }
    }

    /// This function is a variant of [`set`] which works much like [`read`]
    /// in that it operates on the individual bits inside of `flags`, rather
    /// than treating the number as an index. The result of this operation is
    /// that each 1 in `flags` will also be stored inside of the data.
    ///
    /// [`set`]: #method.set
    /// [`read`]: #method.read
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.write(0, 0b111);
    ///
    /// assert!(bf.get(1));
    /// assert!(bf.get(2));
    /// assert!(bf.get(3));
    /// ```
    #[inline]
    pub fn write(&mut self, offset: usize, flags: usize) {
        if offset * POINTER_WIDTH + self.capacity % POINTER_WIDTH > self.capacity {
            panic!("out of range: range > {}", self.capacity);
        }
        // SAFETY: see `read` for why this is safe.
        unsafe { self.write_unchecked(offset, flags) }
    }

    /// This function is a variant of [`unset`]. As it with [`read`] and
    /// [`write`], it operates on the individual bits inside of `flags`
    /// instead of treating the number as an index. The result is that
    /// each 1 inside of `flags` will be erased from the data.
    ///
    /// [`unset`]: #method.unset
    /// [`read`]: #method.read
    /// [`write`]: #method.write
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.set(1);
    /// bf.set(2);
    /// bf.erase(0, 0b11);
    ///
    /// assert!(!bf.get(1));
    /// assert!(!bf.get(2));
    /// ```
    #[inline]
    pub fn erase(&mut self, offset: usize, flags: usize) {
        if offset * POINTER_WIDTH + self.capacity % POINTER_WIDTH > self.capacity {
            panic!("out of range: range > {}", self.capacity);
        }
        // SAFETY: see `write` for why this is safe.
        unsafe { self.erase_unchecked(offset, flags) }
    }

    /// This function is the unchecked variant of [`get`]. It is equivalent
    /// in function, but excludes a boundary check to verify its safety.
    /// This can be useful when operating on known ranges of vaues. However,
    /// it will result in undefined behavior when used incorrectly and thus
    /// may violate the principle of memory safety in Rust.
    ///
    /// # Safety
    ///
    /// Calling this function where `num` is greater than the size of
    /// `self.data` is *[undefined behavior]*. See [`Slice.get_unchecked`]
    /// for more information.
    ///
    /// [`get`]: #method.get
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    /// [`Slice.get_unchecked`]: https://doc.rust-lang.org/std/primitive.slice.html#method.get_unchecked
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// const LEN: usize = 10;
    /// let mut bf = BigFlag::new(LEN);
    ///
    /// unsafe {
    ///     for i in 0..=LEN {
    ///         bf.set_unchecked(i);
    ///     }
    ///     assert!(bf.get_unchecked(LEN));
    /// }
    /// ```
    #[inline]
    pub unsafe fn get_unchecked(&self, num: usize) -> bool {
        let index = num / POINTER_WIDTH;
        let shift = num % POINTER_WIDTH;
        self.read_unchecked(index, 1 << shift)
    }

    /// Stores a single bit by index with no checks as to whether it will
    /// overflow, read out of bounds, or divide by zero.
    ///
    /// # Safety
    ///
    /// Calling this function where `num` is greater than the size of
    /// `self.data` will result in undefined behavior. See [`get_unchecked`].
    ///
    /// [`get_unchecked`]: #method.get_unchecked
    #[inline]
    pub unsafe fn set_unchecked(&mut self, num: usize) {
        let index = num / POINTER_WIDTH;
        let shift = num % POINTER_WIDTH;
        self.write_unchecked(index, 1 << shift)
    }

    /// Erases a single bit by index with no checks as to whether it will
    /// overflow, read out of bounds, or divide by zero.
    ///
    /// # Safety
    ///
    /// Calling this function where `num` is greater than the size of
    /// `self.data` will result in undefined behavior. See [`get_unchecked`].
    ///
    /// [`get_unchecked`]: #method.get_unchecked
    #[inline]
    pub unsafe fn unset_unchecked(&mut self, num: usize) {
        let index = num / POINTER_WIDTH;
        let shift = num % POINTER_WIDTH;
        self.erase_unchecked(index, 1 << shift)
    }

    /// This function is a raw binary `&` operation which reads a series
    /// of flags at the given offset in memory. It will return `true` if
    /// every flag inside of `flags` is also present in the data.
    ///
    /// # Safety
    ///
    /// Calling this function where `offset` is greater than the size of
    /// `self.data` will result in undefined behavior. See [`get_unchecked`].
    ///
    /// [`get_unchecked`]: #method.get_unchecked
    #[inline]
    pub unsafe fn read_unchecked(&self, offset: usize, flags: usize) -> bool {
        *self.data.get_unchecked(offset) & flags > 0
    }

    /// This function is a raw binary `|` operation which writes a series
    /// of flags at the given offset in memory.
    ///
    /// # Safety
    ///
    /// Calling this function where `offset` is greater than the size of
    /// `self.data` will result in undefined behavior. See [`get_unchecked`].
    ///
    /// [`get_unchecked`]: #method.get_unchecked
    #[inline]
    pub unsafe fn write_unchecked(&mut self, offset: usize, flags: usize) {
        *self.data.get_unchecked_mut(offset) |= flags;
    }

    /// This function is a raw binary `& !` operation which erases a series
    /// of flags at the given offset in memory.
    ///
    /// # Safety
    ///
    /// Calling this function where `offset` is greater than the size of
    /// `self.data` will result in undefined behavior. See [`get_unchecked`].
    ///
    /// [`get_unchecked`]: #method.get_unchecked
    #[inline]
    pub unsafe fn erase_unchecked(&mut self, offset: usize, flags: usize) {
        *self.data.get_unchecked_mut(offset) &= !flags;
    }

    /// This function is the first in a series of methods which accesses the
    /// first set of flags inside of the data. It is provided here because it
    /// is the single single implementation of [`read_unchecked`] which is
    /// always guaranteed to be safe, as the size of `self.data` is defined
    /// as being `>= 1` in the constructor. This will provide a performance
    /// boost to users treating this object as a standard series of flags.
    ///
    /// # Safety
    ///
    /// This function is guaranteed to be safe because `0 < self.data.len()`
    ///
    /// [`read_unchecked`]: #method.read_unchecked
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.write(0, 0b1111);
    ///
    /// assert!(bf.read_first(0b1111));
    /// ```
    #[inline]
    pub fn read_first(&self, flags: usize) -> bool {
        // SAFETY: 0 is always in bounds.
        unsafe { self.read_unchecked(0, flags) }
    }

    /// As with [`read_first`], this function is provided as convenience and
    /// performance boost to users treating this object as a standard series
    /// of bit flags, or who wish to access exclusively the first set of
    /// data within it. See [`read_first`] for more information.
    ///
    /// Unlike its counterpart, this function may write flags into unintended
    /// space, where the index of the highest bit is `> self.capacity`, which
    /// can affect the intended use case for this object. This operation isn't
    /// specifically *unsafe*, however. It is currently included here as a
    /// trial pending evaluation.
    ///
    /// [`read_first`]: #method.read_first
    #[inline]
    pub fn write_first(&mut self, flags: usize) {
        // SAFETY: see `read_first`.
        unsafe { self.write_unchecked(0, flags) }
    }

    /// As with [`read_first`], this function is provided as convenience and
    /// performance boost to users treating this object as a standard series
    /// of bit flags, or who wish to access exclusively the first set of
    /// data within it. See [`read_first`] for more information.
    ///
    /// Unlike its counterpart, this function may write flags into unintended
    /// space, where the index of the highest bit is `> self.capacity`, which
    /// can affect the intended use case for this object. This operation is
    /// specifically *unsafe*, however. It is currently included here as a
    /// trial pending evaluation.
    ///
    /// [`read_first`]: #method.read_first
    #[inline]
    pub fn erase_first(&mut self, flags: usize) {
        // SAFETY: see `read_first`.
        unsafe { self.erase_unchecked(0, flags) }
    }

    /// Returns whether every possible flag has been set, up to and no higher
    /// than `capacity`.
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// const LEN: usize = 63;
    /// let mut bf = BigFlag::new(LEN);
    /// for i in 0..LEN {
    ///     bf.set(i);
    /// }
    ///
    /// assert!(bf.all());
    /// ```
    pub fn all(&self) -> bool {
        let last = self.data.len() - 1;
        for &i in &self.data[0..last] {
            if i != usize::MAX {
                return false;
            }
        }
        let num = self.data[last];
        let len = self.capacity % POINTER_WIDTH + 1;
        num == usize::MAX >> POINTER_WIDTH - len
    }

    /// Determines whether any flag has been set, ignoring any extraneous data
    /// after `capacity`.
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.set(31);
    ///
    /// assert!(bf.any());
    /// ```
    pub fn any(&self) -> bool {
        let last = self.data.len() - 1;
        for &i in &self.data[0..last] {
            if i > 0 {
                return true;
            }
        }
        let num = self.data[last];
        let len = self.capacity % POINTER_WIDTH + 1;
        num << POINTER_WIDTH - len > 0
    }

    /// Indicates whether these data contain no flags whatsoever.
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let bf = BigFlag::new(63);
    ///
    /// assert!(bf.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        !self.any()
    }

    /// Erases every flag set inside of the array.
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.set(31);
    /// assert!(bf.any());
    /// bf.clear();
    /// assert!(bf.is_empty());
    /// ```
    pub fn clear(&mut self) {
        for i in &mut *self.data {
            *i = 0;
        }
    }

    /// Returns the highest value these data may hold, or effectively its length.
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// const LEN: usize = 63;
    /// let bf = BigFlag::new(LEN);
    ///
    /// assert_eq!(bf.len(), LEN);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.capacity
    }

    /// Returns a new [`BigFlagIter`], an iterator of boolean values referring
    /// to the data in this array.
    #[inline]
    pub fn iter(&self) -> BigFlagIter {
        BigFlagIter::new(&self)
    }

    /// Returns a new [`BigFlagIndices`], an iterator of usize indices referring
    /// to the data in this array.
    #[inline]
    pub fn indices(&self) -> BigFlagIndices {
        BigFlagIndices::new(&self)
    }

    /// Accepts a consumer operating on each individual usize index flagged inside
    /// of this array. While calling this function is more efficient than using
    /// [`indices`], it does provide redundant functionality and thus is included
    /// here as a trial pending evaluation.
    ///
    /// [`indices`]: #method.indices
    ///
    /// # Examples
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    /// bf.set(10);
    /// bf.set(20);
    ///
    /// let mut vec = Vec::new();
    /// bf.for_each(|i| vec.push(i));
    ///
    /// assert!(vec.contains(&10));
    /// assert!(vec.contains(&20))
    /// ```
    pub fn for_each<F: FnMut(usize)>(&self, mut f: F) {
        for i in 0..self.data.len() {
            let data = unsafe { *self.data.get_unchecked(i) };
            for j in 0..POINTER_WIDTH {
                if data & (1 << j) > 0 {
                    f(i * POINTER_WIDTH + j)
                }
            }
        }
    }

    /// Expands the accepted size of these data by the given amount.
    ///
    /// # Example
    /// ```
    /// use big_flags::BigFlag;
    ///
    /// let mut bf = BigFlag::new(63);
    ///
    /// // You shouldn't be able to write > 63.
    /// let result = std::panic::catch_unwind(|| bf.set(127));
    /// assert!(result.is_err());
    ///
    /// // Growing the data first will guarantee
    /// // that enough space has been allocated.
    /// bf.grow(64);
    /// bf.set(127);
    /// assert!(bf.get(127));
    /// ```
    pub fn grow(&mut self, amount: usize) {
        if self.capacity % POINTER_WIDTH + amount <= POINTER_WIDTH {
            self.capacity += amount;
            return;
        }
        let mut data_vec = self.data.to_vec();
        data_vec.append(&mut vec![0; amount / POINTER_WIDTH]);
        self.data = Box::from(data_vec);
        self.capacity += amount;
    }

    /// This function is the opposite of [`grow`] in that it *reduces* the
    /// accepted size of these data by `amount`.
    ///
    /// [`grow`]: #method.grow
    pub fn shrink(&mut self, amount: usize) {
        let mut data_vec = self.data.to_vec();
        while data_vec.len() > amount / POINTER_WIDTH {
            data_vec.remove(data_vec.len() - 1);
        }
        self.data = Box::from(data_vec);
        self.capacity -= amount;
    }

    /// This function is a variant of [`grow`] and [`shrink`] in that it can
    /// grow or shrink the data to the size of `capacity`.
    ///
    /// [`shrink`]: #method.shrink
    /// [`grow`]: #method.grow
    pub fn set_capacity(&mut self, capacity: usize) {
        if capacity == self.capacity {
            return;
        } else if capacity > self.capacity {
            self.grow(capacity - self.capacity);
        } else {
            self.shrink(self.capacity - capacity);
        }
    }

    /// This value represents the number of bits contained within a single
    /// [`usize`] number. It may be useful for any functions calculating
    /// memory offsets or flag indices. It is exposed here as a convenience
    /// to external implementors.
    pub const fn get_pointer_width() -> usize {
        POINTER_WIDTH
    }

    /// This value represents the highest single bit that can exist inside
    /// of a [`usize`] number. It may be useful for any functions performing
    /// shift operations or tracking comparators. It is exposed here as a
    /// convenience to external implementors.
    pub const fn get_highest_bit() -> usize {
        HIGHEST_BIT
    }
}

/// This implementation is intended for converting raw slices of `usize`
/// numbers into a bitflag array with flags at the corresponding *indices*.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let arr = [100, 200, 300];
/// let bf = BigFlag::from(&arr[0..]);
///
/// assert!(bf.get(100));
/// assert!(bf.get(200));
/// assert!(bf.get(300));
/// ```
impl From<&[usize]> for BigFlag {
    fn from(slice: &[usize]) -> Self {
        let max = *slice.iter().max().unwrap_or(&0);
        let mut bf = BigFlag::new(max);
        slice.iter().for_each(|i| unsafe { bf.set_unchecked(*i) });
        bf
    }
}

/// This implementation is intended for converting raw vectors of `usize`
/// numbers into a bitflag array with flags at the corresponding *indices*.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let vec = vec![400, 500, 600];
/// let bf = BigFlag::from(&vec);
///
/// assert!(bf.get(400));
/// assert!(bf.get(500));
/// assert!(bf.get(600));
/// ```
impl From<&Vec<usize>> for BigFlag {
    fn from(vec: &Vec<usize>) -> Self {
        Self::from(vec.as_slice())
    }
}

/// This implementation is intended for converting raw slices of booleans
/// into individual bits contained within a bitflag array.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let arr = [true, false, true];
/// let bf = BigFlag::from(&arr[0..]);
///
/// assert!(bf.get(0));
/// assert!(!bf.get(1));
/// assert!(bf.get(2))
/// ```
impl From<&[bool]> for BigFlag {
    fn from(slice: &[bool]) -> Self {
        let mut bf = BigFlag::new(slice.len());
        slice.iter().enumerate().for_each(|(i, b)| {
            if *b {
                unsafe { bf.set_unchecked(i) }
            }
        });
        bf
    }
}

/// This implementation is intended for converting raw vectors of booleans
/// into individual bits contained within a bitflag array.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let vec = vec![true, false, true];
/// let bf = BigFlag::from(&vec);
///
/// assert!(bf.get(0));
/// assert!(!bf.get(1));
/// assert!(bf.get(2))
/// ```
impl From<&Vec<bool>> for BigFlag {
    fn from(vec: &Vec<bool>) -> Self {
        Self::from(vec.as_slice())
    }
}

/// This implementation is intended for converting the individual bits inside
/// of one `usize` number into an array of bitflags.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let bf = BigFlag::from(0b101);
///
/// assert!(bf.get(0));
/// assert!(!bf.get(1));
/// assert!(bf.get(2));
/// ```
impl From<usize> for BigFlag {
    fn from(num: usize) -> Self {
        Self {
            capacity: POINTER_WIDTH - 1,
            data: Box::from([num]),
        }
    }
}

/// This implementation provides a quick way to convert this bitflag array
/// back into an array of standard boolean values.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let bf = BigFlag::from(0b101);
/// let booleans: Vec<bool> = bf.into();
///
/// assert_eq!(booleans, vec![true, false, true]);
/// ```
impl Into<Vec<bool>> for BigFlag {
    fn into(self) -> Vec<bool> {
        self.iter().collect()
    }
}

/// This implementation provides a quick way to convert this bitflag array
/// into an array of its indices.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let bf = BigFlag::from(0b101);
/// let indices: Vec<usize> = bf.into();
///
/// assert_eq!(indices, vec![0, 2]);
/// ```
impl Into<Vec<usize>> for BigFlag {
    fn into(self) -> Vec<usize> {
        self.indices().collect()
    }
}

/// This struct provides all of the necessary data for iterating over each
/// boolean flag inside of a [`BigFlag`] object.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let mut bf = BigFlag::new(2);
/// bf.set(0);
/// bf.set(2);
///
/// let mut iter = bf.iter();
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), Some(false));
/// assert_eq!(iter.next(), Some(true));
/// assert_eq!(iter.next(), None);
/// ```
pub struct BigFlagIter<'a> {
    storage: &'a [usize],
    idx: usize,
    data: usize,
    cmp: usize,
    end: usize,
}

impl<'a> BigFlagIter<'a> {
    fn new(bf: &'a BigFlag) -> Self {
        Self {
            idx: 0,
            data: *bf.data.get(0).unwrap_or(&0),
            cmp: 1,
            end: 1 << (bf.capacity % POINTER_WIDTH + 1),
            storage: &bf.data,
        }
    }
}

impl<'a> Iterator for BigFlagIter<'a> {
    type Item = bool;

    fn next(&mut self) -> Option<bool> {
        if self.cmp == self.end && self.idx == self.storage.len() - 1 {
            return None;
        }
        let b = self.data & self.cmp > 0;
        if self.cmp == HIGHEST_BIT {
            self.cmp = 1;
            self.idx += 1;
            self.data = self.storage[self.idx];
        } else {
            self.cmp <<= 1;
        }
        Some(b)
    }
}

/// This struct provides all of the necessary data for iterating over each
/// index flagged inside of a [`BigFlag`] object, thus allowing it act as
/// an array of integers.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let mut bf = BigFlag::new(10);
/// bf.set(5);
/// bf.set(10);
///
/// let mut iter = bf.indices();
/// assert_eq!(iter.next(), Some(5));
/// assert_eq!(iter.next(), Some(10));
/// assert_eq!(iter.next(), None);
/// ```
pub struct BigFlagIndices<'a> {
    storage: &'a [usize],
    idx: usize,
    data: usize,
    cmp: usize,
    end: usize,
    val: usize,
}

impl<'a> BigFlagIndices<'a> {
    fn new(bf: &'a BigFlag) -> Self {
        Self {
            data: *bf.data.get(0).unwrap_or(&0),
            end: bf.capacity + 1,
            storage: &bf.data,
            cmp: 1,
            idx: 0,
            val: 0,
        }
    }
}

impl<'a> Iterator for BigFlagIndices<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<usize> {
        loop {
            if self.val == self.end {
                return None;
            }
            let flag = self.data & self.cmp > 0;
            let ret = self.val;
            self.val += 1;
            if self.cmp == HIGHEST_BIT {
                self.cmp = 1;
                self.idx += 1;
                self.data = self.storage[self.idx];
            } else {
                self.cmp <<= 1;
            }
            if flag {
                return Some(ret);
            }
        }
    }
}

/// This implementation allows values contained within a [`BigFlag`]
/// array to be accessed by index. Because the values are not stored
/// in memory as booleans, this operation cannot be mutable and thus
/// no implementation of [`MutIndex`] is provided.
///
/// # Examples
/// ```
/// use big_flags::BigFlag;
///
/// let mut bf = BigFlag::new(10);
/// bf.set(5);
/// bf.set(10);
///
/// assert!(bf[5]);
/// assert!(bf[10]);
/// assert!(!bf[0]);
/// ```
impl std::ops::Index<usize> for BigFlag {
    type Output = bool;

    #[inline]
    fn index(&self, index: usize) -> &bool {
        if self.get(index) {
            &true
        } else {
            &false
        }
    }
}

// impl std::ops::Index<std::ops::Range<usize>> for BigFlag {
//     type Output = BigFlagSlice;
//
//     fn index(&self, index: std::ops::Range<usize>) -> BigFlagRange {
//         BigFlagRange {
//
//         }
//     }
// }

pub struct BigFlagRange {
    ptr: *const BigFlag,
    rng: std::ops::Range<usize>,
}

impl BigFlagRange {

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rw() {
        let mut bf = BigFlag::new(200);
        // Test r/w on boundaries
        bf.set(0);
        bf.set(200);
        assert!(bf.get(0));
        assert!(bf.get(200));
        // Test erasing data
        bf.unset(0);
        bf.unset(200);
        assert!(!bf.get(0));
        assert!(!bf.get(200));
        // Test odd numbers in between
        bf.set(13);
        bf.set(59);
        bf.set(173);
        assert!(bf.get(13));
        assert!(bf.get(59));
        assert!(bf.get(173));
        // Test numbers that were never set.
        assert!(!bf.get(25));
        assert!(!bf.get(75));
        assert!(!bf.get(125));
        bf.set(126);
        assert!(bf[126])
    }

    #[test]
    fn test_rw_raw() {
        const LEN: usize = 15;
        let mut bf = BigFlag::new(LEN);

        for i in (0..LEN).step_by(2) {
            bf.set(i);
        }
        assert!(bf.read(0, 0b101010101010101)); // culled
        bf.write(0, 0b11111);
        assert!(bf.read(0, 0b11111));

        bf.clear();
        bf.write(0, 0b1011);
        assert!(bf.get(0));
        assert!(bf.get(1));
        assert!(bf.get(3));

        bf.clear();
        bf.write(0, 2 | 4);
        assert!(bf.read(0, 2 | 4))
    }

    #[test]
    fn test_rw_large() {
        let mut bf = BigFlag::new(100_000);
        for &v in &[50, 10_000, 25_000, 99_999] {
            assert!(!bf.get(v));
            bf.set(v);
            assert!(bf.get(v));
        }
    }

    #[test]
    fn test_iter() {
        let mut bf = BigFlag::new(200);
        let values = [29, 137, 181];
        for &v in &values {
            bf.set(v);
        }
        let count = bf
            .iter()
            .enumerate()
            .filter(|(i, _)| values.contains(i))
            .count();
        assert_eq!(values.len(), count);
    }

    #[test]
    fn test_indices() {
        let mut bf = BigFlag::new(200);
        let values = vec![61, 109, 197];
        for &v in &values {
            bf.set(v);
        }
        assert_eq!(values, bf.indices().collect::<Vec<usize>>());
    }

    #[test]
    fn test_from() {
        let numbers = vec![3, 5, 17];
        let booleans = vec![true, false, true];
        let bf_n = BigFlag::from(&numbers);
        let bf_b = BigFlag::from(&booleans);
        for &i in &numbers {
            assert!(bf_n.get(i));
        }
        for (i, &b) in booleans.iter().enumerate() {
            assert_eq!(bf_b.get(i), b);
        }
    }

    #[test]
    fn test_grow_shrink() {
        let mut bf = BigFlag::new(63);
        bf.set(63);
        bf.set_capacity(255);
        bf.set(127);
        assert!(bf.get(63));
        assert!(bf.get(127));
        bf.set_capacity(63);
        assert!(bf.get(63));
        assert!(!bf.get(127));
        bf.grow(1);
        bf.set(64);
        assert!(bf.get(64));
    }

    #[test]
    fn test_all() {
        const LEN: usize = 321;
        let mut bf = BigFlag::new(LEN);
        for i in 0..=LEN {
            bf.set(i);
        }
        assert!(bf.all());
        bf.unset(LEN);
        assert!(!bf.all());
    }

    #[test]
    fn test_any() {
        let mut bf = BigFlag::new(1337);
        // The array starts off empty.
        assert!(bf.is_empty());
        // Set a random number in the middle.
        bf.set(1000);
        assert!(bf.any());
        bf.unset(1000);
        // Make sure the end is getting read.
        bf.set(1337);
        assert!(bf.any());
        bf.unset(1337);
        // Use unsafe code to set > capacity.
        unsafe { bf.set_unchecked(1338) }
        // We're expecting this number to actually be there.
        unsafe { assert!(bf.get_unchecked(1338)) }
        // But it should be ignored in safe code.
        assert!(bf.is_empty());
    }
}

#[cfg(all(test))]
mod performance_tests {
    use crate::BigFlag;
    use bitvec::order::LocalBits;
    use bitvec::prelude::*;
    use bitvec::vec::BitVec;
    use rand::seq::SliceRandom;
    use rand::thread_rng;
    use std::fmt::{Debug, Display};
    use std::ops::{AddAssign, DivAssign};
    use std::time::{Duration, Instant};

    const ZERO: Duration = Duration::from_millis(0);
    const TEST_SIZE: usize = 10_000;
    const NUM_TESTS: u32 = 100;

    #[derive(Debug)]
    struct PerformanceResults {
        /// [`BigFlag`] (safe)
        bfs: Duration,
        /// [`BigFlag`] (unsafe)
        bfu: Duration,
        /// [`BitVec`]
        bv: Duration,
        /// [`Vec<T>`]
        vc: Duration,
        /// [`Vec<T>`] (binary search)
        vb: Duration,
    }

    impl PerformanceResults {
        fn empty() -> Self {
            Self::new(ZERO, ZERO, ZERO, ZERO, ZERO)
        }

        fn new(bfs: Duration, bfu: Duration, bv: Duration, vc: Duration, vb: Duration) -> Self {
            Self { bfs, bfu, bv, vc, vb }
        }

        fn test_construction() -> Self {
            let bf = time((), |_| {
                BigFlag::new(TEST_SIZE);
            });
            let bv = time((), |_| {
                <BitVec<LocalBits, usize>>::with_capacity(TEST_SIZE);
            });
            let vc = time((), |_| {
                <Vec<usize>>::with_capacity(TEST_SIZE);
            });
            PerformanceResults::new(bf, bf, bv, vc, vc)
        }

        fn test_write() -> (PerformanceData, Self) {
            let mut data = PerformanceData::new();
            let bfs = time(&mut data, |d| {
                for &i in d.nums.iter() {
                    d.bf.set(i);
                }
            });
            let bfu = time(&mut data, |d| unsafe {
                for &i in d.nums.iter() {
                    d.bf.set_unchecked(i);
                }
            });
            let bv = time(&mut data, |d| {
                for &i in d.nums.iter() {
                    d.bv.set(i, true);
                }
            });
            let vc = time(&mut data, |d| {
                for &i in d.nums.iter() {
                    d.vc.push(i);
                }
            });
            let vb = time(&mut data, |d| {
                for &i in d.nums.iter() {
                    binary_insert(&mut d.vb, i);
                }
            });
            (data, PerformanceResults::new(bfs, bfu, bv, vc, vb))
        }

        fn test_read(mut data: PerformanceData) -> Self {
            data.nums.shuffle(&mut thread_rng());
            let bfs = time(&mut data, |d| {
                d.nums.iter().for_each(|i| {
                    d.bf.get(*i);
                })
            });
            let bfu = time(&mut data, |d| unsafe {
                d.nums.iter().for_each(|i| {
                    d.bf.get_unchecked(*i);
                })
            });
            let bv = time(&mut data, |d| {
                d.nums.iter().for_each(|i| {
                    d.bv.get(*i);
                })
            });
            let vc = time(&mut data, |d| {
                d.nums.iter().for_each(|i| {
                    d.vc.contains(i);
                })
            });
            let vb = time(&mut data, |d| {
                d.nums.iter().for_each(|i| {
                    d.vb.binary_search(i).unwrap();
                })
            });
            PerformanceResults::new(bfs, bfu, bv, vc, vb)
        }

        fn test_all() -> Self {
            // Different set of numbers for reading and writing.
            // Rule out any effect that optimization might be having.
            let w_usize = get_randoms();
            let r_usize = get_randoms();

            let bfs = time((&r_usize, &w_usize), |(r, w)| {
                let mut bf: BigFlag = BigFlag::new(TEST_SIZE);
                for &i in w.iter() {
                    bf.set(i);
                }
                for &i in r.iter() {
                    bf.get(i);
                }
            });
            let bfu = time((&r_usize, &w_usize), |(r, w)| unsafe {
                let mut bf: BigFlag = BigFlag::new(TEST_SIZE);
                for &i in w.iter() {
                    bf.set_unchecked(i);
                }
                for &i in r.iter() {
                    bf.get_unchecked(i);
                }
            });
            let bv = time((&r_usize, &w_usize), |(r, w)| {
                let mut bv: BitVec = bitvec![Lsb0, usize; 0; TEST_SIZE + 1];
                for &i in w.iter() {
                    bv.set(i, true);
                }
                for &i in r.iter() {
                    bv.get(i);
                }
            });
            let vc = time((&r_usize, &w_usize), |(r, w)| {
                let mut vc: Vec<usize> = Vec::with_capacity(TEST_SIZE);
                for &i in w.iter() {
                    vc.push(i);
                }
                for &i in r.iter() {
                    vc.contains(&i);
                }
            });
            let vb = time((&r_usize, &w_usize), |(r, w)| {
                let mut vb: Vec<usize> = Vec::with_capacity(TEST_SIZE);
                for &i in w.iter() {
                    binary_insert(&mut vb, i);
                }
                for &i in r.iter() {
                    vb.binary_search(&i).unwrap();
                }
            });
            PerformanceResults::new(bfs, bfu, bv, vc, vb)
        }
    }

    fn time<T, F: FnMut(T)>(t: T, mut f: F) -> Duration {
        let time = Instant::now();
        f(t);
        time.elapsed()
    }

    fn binary_insert<T: Display + Ord>(vec: &mut Vec<T>, element: T) {
        match vec.binary_search(&element) {
            Err(pos) => vec.insert(pos, element),
            Ok(_) => panic!("element was already in array: {}", element),
        }
    }

    fn get_randoms() -> Vec<usize> {
        let mut nums: Vec<usize> = (1..TEST_SIZE).collect();
        nums.shuffle(&mut thread_rng());
        nums
    }

    impl AddAssign<PerformanceResults> for PerformanceResults {
        fn add_assign(&mut self, rhs: Self) {
            self.bfs += rhs.bfs;
            self.bfu += rhs.bfu;
            self.bv += rhs.bv;
            self.vc += rhs.vc;
            self.vb += rhs.vb;
        }
    }

    impl DivAssign<u32> for PerformanceResults {
        fn div_assign(&mut self, rhs: u32) {
            self.bfs /= rhs;
            self.bfu /= rhs;
            self.bv /= rhs;
            self.vc /= rhs;
            self.vb /= rhs;
        }
    }

    struct PerformanceData {
        bf: BigFlag,
        bv: BitVec,
        vc: Vec<usize>,
        vb: Vec<usize>,
        nums: Vec<usize>,
    }

    impl PerformanceData {
        fn new() -> Self {
            let mut nums: Vec<usize> = (1..=TEST_SIZE).collect();
            nums.shuffle(&mut thread_rng());
            Self {
                bf: BigFlag::new(TEST_SIZE),
                bv: bitvec![Lsb0, usize; 0; TEST_SIZE + 1],
                vc: Vec::with_capacity(TEST_SIZE + 1),
                vb: Vec::with_capacity(TEST_SIZE + 1),
                nums,
            }
        }
    }

    #[test]
    #[ignore]
    fn test_performance() {
        let mut construct = PerformanceResults::empty();
        let mut write = PerformanceResults::empty();
        let mut read = PerformanceResults::empty();
        let mut all = PerformanceResults::empty();

        for _ in 0..NUM_TESTS {
            let c = PerformanceResults::test_construction();
            let (d, w) = PerformanceResults::test_write();
            let r = PerformanceResults::test_read(d);
            let a = PerformanceResults::test_all();
            construct += c;
            write += w;
            read += r;
            all += a;
        }
        construct /= NUM_TESTS;
        write /= NUM_TESTS;
        read /= NUM_TESTS;
        all /= NUM_TESTS;

        println!("Test size: {}", TEST_SIZE);
        println!(
            "Construction tested {} times:  {:>6.2?}",
            NUM_TESTS, construct
        );
        println!("Write ops tested {} times:     {:>6.2?}", NUM_TESTS, write);
        println!("Read ops tested {} times:      {:>6.2?}", NUM_TESTS, read);
        println!("All ops tested {} times:       {:>6.2?}", NUM_TESTS, all);
    }
}
