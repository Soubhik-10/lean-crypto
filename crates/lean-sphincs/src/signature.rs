//! Borrowed, fixed-size reads from the serialized signature.

// Reads only fixed-size fields, without materializing a 7.7 KB signature struct.
pub(crate) struct Reader<'a>(&'a [u8]);

impl<'a> Reader<'a> {
    pub(crate) const fn new(bytes: &'a [u8]) -> Self {
        Self(bytes)
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

// Serialize exactly the complete output chunks, retaining any partial tail.
// As with zip(chunks_exact_mut, nodes), a shorter side ends the traversal.
pub(crate) fn write_nodes<const N: usize>(output: &mut [u8], nodes: &[alloy_primitives::B128; N]) {
    let mut i = 0;
    while i < N && i < output.len() / crate::params::NODE_BYTES {
        let at = i * crate::params::NODE_BYTES;
        output[at..at + crate::params::NODE_BYTES].copy_from_slice(nodes[i].as_slice());
        i += 1;
    }
}
