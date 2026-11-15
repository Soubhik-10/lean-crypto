//! Borrowed, fixed-size reads from the serialized signature.

// Reads only fixed-size fields, without materializing a 7.7 KB signature struct.
pub(crate) struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    pub(crate) const fn new(signature: &'a [u8]) -> Self {
        Self(signature)
    }

    pub(crate) fn take<const N: usize>(&mut self) -> Option<&'a [u8; N]> {
        let (field, remaining) = self.0.split_first_chunk::<N>()?;
        self.0 = remaining;
        Some(field)
    }

    pub(crate) const fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}
