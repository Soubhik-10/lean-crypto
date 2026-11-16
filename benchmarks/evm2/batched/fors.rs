use super::*;

fn address(index: u64, tree: usize, height: usize, node: usize) -> Adrs {
    OtsKey::of_index(0, index)
        .adrs(FORS_TREE)
        .with_tree_height(height as u32)
        .with_tree_index(((tree << (FORS_HEIGHT - height)) + node) as u32)
}

fn key(pk_seed: &PkSeed, index: u64, roots: &[Digest; FORS_TREES]) -> Digest {
    th_digests(pk_seed, &OtsKey::of_index(0, index).adrs(FORS_ROOTS), roots)
}

pub(super) fn open(
    pk_seed: &PkSeed,
    seed: &B256,
    index: u64,
    leaves: &[usize; FORS_TREES],
    output: &mut [u8],
) -> Digest {
    let mut roots = [[0; N]; FORS_TREES];
    for tree in 0..FORS_TREES {
        let mut secrets = vec![[0; N]; 1 << FORS_HEIGHT];
        hash_batch::<80>(
            secrets.len(),
            |j, input| {
                let adrs = OtsKey::of_index(0, index)
                    .adrs(FORS_PRF)
                    .with_tree_index(((tree << FORS_HEIGHT) + j) as u32);
                image(pk_seed, &adrs, &seed.0, input);
            },
            &mut secrets,
        );
        let mut nodes = vec![[0; N]; secrets.len()];
        hash_batch::<64>(
            nodes.len(),
            |j, input| {
                image(pk_seed, &address(index, tree, 0, j), &secrets[j], input);
            },
            &mut nodes,
        );
        let levels = trees::merkle(pk_seed, nodes, |height, node| {
            address(index, tree, height, node)
        });
        roots[tree] = levels.root();
        let selected = leaves[tree];
        let opening = &mut output[tree * (FORS_HEIGHT + 1) * N..][..(FORS_HEIGHT + 1) * N];
        opening[..N].copy_from_slice(&secrets[selected]);
        for z in 0..FORS_HEIGHT {
            opening[(z + 1) * N..(z + 2) * N]
                .copy_from_slice(&levels.levels[z][(selected >> z) ^ 1]);
        }
    }
    key(pk_seed, index, &roots)
}

pub(super) fn recover(
    pk_seed: &PkSeed,
    index: u64,
    leaves: &[usize; FORS_TREES],
    signature: &[u8],
) -> Digest {
    let mut nodes = [[0; N]; FORS_TREES];
    let opening = |tree: usize| &signature[tree * (FORS_HEIGHT + 1) * N..][..(FORS_HEIGHT + 1) * N];
    hash_batch::<64>(
        FORS_TREES,
        |tree, input| {
            image(
                pk_seed,
                &address(index, tree, 0, leaves[tree]),
                &opening(tree)[..N],
                input,
            );
        },
        &mut nodes,
    );
    for height in 1..=FORS_HEIGHT {
        let previous = nodes;
        hash_batch::<80>(
            FORS_TREES,
            |tree, input| {
                let sibling = &opening(tree)[height * N..(height + 1) * N];
                let mut children = [0; 2 * N];
                let right = (leaves[tree] >> (height - 1)) & 1 != 0;
                let at = if right { N } else { 0 };
                children[at..at + N].copy_from_slice(&previous[tree]);
                children[N - at..2 * N - at].copy_from_slice(sibling);
                image(
                    pk_seed,
                    &address(index, tree, height, leaves[tree] >> height),
                    &children,
                    input,
                );
            },
            &mut nodes,
        );
    }
    key(pk_seed, index, &nodes)
}
