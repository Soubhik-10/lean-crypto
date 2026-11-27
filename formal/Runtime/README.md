# Observable standard-library formatting model

The four Lean files under this directory extend the pinned Aeneas
standard-library interface for the SPHINCS `SignError` API. They retain captured
formatting arguments, formatter options, writer state, partial output on failure,
and nested pretty-print indentation. Width uses its effective numeric value;
absent width (`None`) and explicit zero width (`Some 0`) have identical rendering
behavior for these methods. This model identifies their effective widths; it does
not prove those two Rust `Option` values are equal or interchangeable for arbitrary
formatting programs.
The stock interface erases these values and cannot express the required
observable-output contracts.

From the repository root, prepare the runtime with:

```sh
python3 -I scripts/prepare_rust_runtime.py --runtime /absolute/path/to/runtime --stdlib-model
```

Preparation preserves the stock pinned runtime, installs only the explicit
four-file allowlist into a separate `stdlib-model` build, and recompiles its
importers. A model manifest records both original and replacement source hashes.
The source gate validates that manifest and both source trees, then recompiles
all generated SPHINCS bodies unchanged against the observable model. See the
[complete source-verification workflow](../README.md#production-sphincs-source-verification).
The completed `b82f2a78` source audit passed in all five configurations. See the
[detailed guide](../docs/verification.md#formatting-and-errors) for the current
verification status and the observable-model boundary.

The modules in [`RustCrypto/Formatting`](../RustCrypto/Formatting), in the
unchanged namespace `RustCrypto.ErrorFormatting`, prove the extracted
Display, Debug, Clone, PartialEq, Eq and Error supertrait behavior. Output
contracts cover all 256 layer values, ordinary and alternate Debug, arbitrary
supported formatter options/writers, and retained partial output when a writer
fails. The compiler-generated SPHINCS formatting template is proved against the
model interpreter.

This is an explicit trusted model of the Rust standard-library formatting
contract, not a verification of its unsafe implementation. It was reviewed
against Rust `1.97.1` and the extraction compiler `nightly-2026-09-17`
(`1.100.0-nightly`); their template encoding agrees. Malformed templates are
outside `fmt::Arguments`' unsafe validity contract. The pinned extraction does
not include Rust's default `Error::source` body; that body remains a
standard-library boundary and has no extracted theorem here. These formatting
proofs make no compiler, machine-code, security or side-channel claim.

The replacements for `Core/Fmt.lean`, `Scalar/Display.lean` and
`Scalar/Fmt.lean` modify the pinned Aeneas sources under the
[Apache 2.0 license](LICENSE-APACHE). The changes retain observable values
and writer effects through the new `Core/FmtModel.lean` model described above.
