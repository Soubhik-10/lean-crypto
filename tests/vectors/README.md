# EthLib conformance data

Source: `ethereum/EthLib`, commit
`03547dd83f298a63e6dcceff0a0b75f6142490aa`, directory
`tests/cryptography/sphincs/verify`.

Upstream license: CC0-1.0. These fixtures are attributed test data, not Rust
implementation code. The `verify_valid_known_answer` fixture is EthLib's
independent known-answer case; the other valid cases include a zero message
and a zero seed.

`ethlib.json` preserves the hex inputs and expected result of each of the 26
upstream YAML cases. `null` means the input has a malformed length. The Rust
API rejects an invalid signature length with `false`; public-key and message
lengths are enforced by its Alloy `B256` argument types.

`SHA256SUMS` records SHA-256 digests of the original downloaded YAML bytes,
before normalization. Regenerate deterministically with:

```sh
python scripts/sync_vectors.py
```

The importer deliberately accepts only this pinned YAML schema and requires
no third-party Python packages. Changing the reference revision requires an
explicit source change and a new conformance review.
