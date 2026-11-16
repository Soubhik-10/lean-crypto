"""Seed all fuzz targets from the repository's pinned CC0 known-answer data."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / "fuzz/corpus")
    parser.add_argument("--full-signing-corpus", action="store_true",
                        help="include extra signing seeds for campaigns longer than ten minutes")
    args = parser.parse_args()
    counts = {}

    def put(target, name, data):
        directory = args.out / target
        directory.mkdir(parents=True, exist_ok=True)
        (directory / ("seed-" + name)).write_bytes(data)
        counts[target] = counts.get(target, 0) + 1

    def decode(value):
        return bytes.fromhex(value.removeprefix("0x"))

    vectors = json.loads((ROOT / "tests/vectors/ethlib.json").read_text(encoding="utf-8"))
    for index, case in enumerate(v for v in vectors if v["expected"] is True):
        key, message, signature = (decode(case[name]) for name in ("public_key", "message", "signature"))
        assert (len(key), len(message), len(signature)) == (32, 32, 7740)
        wire = key + message + signature
        put("verify_wire", f"valid-{index}", wire)
        put("verify_wire", f"extended-{index}", wire + b"\x00")
        for length in [0, 15, 16, 4239, 4240, 5395, 5396, 6551, 6552, 7739]:
            put("verify_wire", f"truncated-{index}-{length}", key + message + signature[:length])
        put("mutate_valid", f"valid-{index}", bytes([index]))
        for offset in [0, 15, 16, 191, 4239, 4240, 4243, 4244, 5268, 5395, 5396, 5400, 6424, 6551, 6552, 6556, 7580, 7739]:
            put("mutate_valid", f"field-{index}-{offset}", bytes([index, 0]) + offset.to_bytes(2, "little") + b"\x01")
        for kind in range(1, 8):
            put("mutate_valid", f"edit-{index}-{kind}", bytes([index, kind, 0, 0, 255]))

    signs = json.loads((ROOT / "tests/vectors/sign.json").read_text(encoding="utf-8"))
    for index, case in enumerate(v for v in signs if v["expected"] is not None):
        if index == 0 or args.full_signing_corpus:
            put("sign_differential", f"known-{index}", decode(case["seed"]) + decode(case["message"]))
    put("sign_differential", "short-1", b"\x00")
    if not args.full_signing_corpus:
        print(json.dumps(counts, sort_keys=True))
        return
    for value in [0, 1, 127, 128, 170, 255]:
        put("sign_differential", f"repeated-{value}", bytes([value]) * 32 + bytes([255 - value]) * 32)
    for bit in [0, 1, 7, 8, 63, 127, 128, 191, 248, 255]:
        seed = bytearray(32)
        seed[bit // 8] = 1 << (bit % 8)
        put("sign_differential", f"single-bit-{bit}", bytes(seed) + bytes(range(32)))
    for length in [0, 1, 31, 32, 63]:
        put("sign_differential", f"short-{length}", bytes(length))
    print(json.dumps(counts, sort_keys=True))


if __name__ == "__main__":
    main()
