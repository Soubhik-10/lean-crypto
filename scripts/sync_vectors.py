"""Fetch pinned CC0 signature vectors and normalize the documented YAML schema."""

import hashlib
import json
from pathlib import Path
import re
from urllib.request import Request, urlopen

REVISION = "03547dd83f298a63e6dcceff0a0b75f6142490aa"
ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = {
    "verify": {"public_key", "message", "signature"},
    "key_gen": {"seed"},
    "sign": {"seed", "message"},
}


def fetch(url):
    with urlopen(Request(url, headers={"User-Agent": "lean-sphincs-vectors"}), timeout=30) as response:
        return response.read()


def main():
    destination = ROOT / "crates" / "lean-sphincs" / "tests" / "vectors"
    destination.mkdir(parents=True, exist_ok=True)
    checksums = []
    for operation, schema in SCHEMAS.items():
        source = f"tests/cryptography/sphincs/{operation}"
        entries = json.loads(fetch(
            f"https://api.github.com/repos/ethereum/EthLib/contents/{source}?ref={REVISION}"
        ))
        cases = []
        for entry in sorted(entries, key=lambda item: item["name"]):
            if entry["type"] != "dir":
                continue
            path = f"{source}/{entry['name']}/data.yaml"
            raw = fetch(f"https://raw.githubusercontent.com/ethereum/EthLib/{REVISION}/{path}")
            text = raw.decode().replace("\r\n", "\n")
            fields = dict(re.findall(r"^  ([a-z_]+): '(0x[0-9a-f]*)'$", text, re.M))
            output = re.search(r"^output: (true|false|null|'0x[0-9a-f]*')$", text, re.M)
            if set(fields) != schema or output is None:
                raise ValueError(f"Unexpected fixture schema: {path}")
            value = output[1]
            expected = value[1:-1] if value.startswith("'") else json.loads(value)
            cases.append({"name": entry["name"], **fields, "expected": expected})
            checksums.append(f"{hashlib.sha256(raw).hexdigest()}  {path}\n")
        filename = "ethlib.json" if operation == "verify" else f"{operation}.json"
        (destination / filename).write_text(json.dumps(cases, indent=2) + "\n", encoding="utf-8", newline="\n")
        print(f"Imported {len(cases)} {operation} cases from EthLib {REVISION}")
    (destination / "SHA256SUMS").write_text("".join(checksums), encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
