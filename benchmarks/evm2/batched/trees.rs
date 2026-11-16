use super::*;

pub(super) struct Tree {
    pub(super) levels: Vec<Vec<Digest>>,
}

impl Tree {
    pub(super) fn root(&self) -> Digest {
        self.levels.last().unwrap()[0]
    }
}

pub(super) fn merkle(
    pk_seed: &PkSeed,
    leaves: Vec<Digest>,
    address: impl Fn(usize, usize) -> Adrs,
) -> Tree {
    let mut levels = vec![leaves];
    while levels.last().unwrap().len() > 1 {
        let children = levels.last().unwrap();
        let mut parents = vec![[0; N]; children.len() / 2];
        hash_batch::<80>(
            parents.len(),
            |j, input| {
                image(
                    pk_seed,
                    &address(levels.len(), j),
                    children[2 * j..2 * j + 2].as_flattened(),
                    input,
                );
            },
            &mut parents,
        );
        levels.push(parents);
    }
    Tree { levels }
}

pub(super) fn xmss(pk_seed: &PkSeed, seed: &B256, key: &OtsKey) -> Tree {
    let leaves = (0..1 << LAYER_HEIGHTS[key.layer])
        .map(|leaf| wots::public_leaf(pk_seed, seed, &OtsKey { leaf, ..*key }))
        .collect();
    merkle(pk_seed, leaves, |height, index| {
        key.tree_adrs()
            .with_type(TREE)
            .with_tree_height(height as u32)
            .with_tree_index(index as u32)
    })
}
