# Pinned conformance data

Source: `ethereum/EthLib`, commit
`03547dd83f298a63e6dcceff0a0b75f6142490aa`, under
`tests/cryptography/sphincs`.

Upstream license: CC0-1.0. These are attributed test data, not Rust implementation
code. The known-answer cases pin independent reference outputs.

| File | Operation | Cases |
| --- | --- | ---: |
| `key_gen.json` | Public-key derivation | 4 |
| `sign.json` | Deterministic signing | 5 |
| `ethlib.json` | Verification | 26 |

Each JSON file preserves the hex inputs and expected output of its upstream
YAML cases. `null` means a malformed input length. Seed, public-key and message
lengths are enforced by the public API's Alloy `B256` types; the verifier rejects
an incorrect signature length with `false`.

`SHA256SUMS` records SHA-256 digests of the original YAML bytes before
normalization. Regenerate all 35 cases deterministically with:

```sh
python scripts/sync_vectors.py
```

The importer deliberately accepts only the pinned schemas and needs no
third-party Python packages. A revision change requires an explicit source change
and conformance review.
