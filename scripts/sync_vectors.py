"""Fetch pinned CC0 EthLib vectors and normalize their simple YAML schema to JSON."""

import hashlib
import json
from pathlib import Path
import re
from urllib.request import Request, urlopen

REVISION = "03547dd83f298a63e6dcceff0a0b75f6142490aa"
ROOT = Path(__file__).resolve().parents[1]
SOURCE = "tests/cryptography/sphincs/verify"


def fetch(url):
    with urlopen(Request(url, headers={"User-Agent": "lean-sphincs-vectors"}), timeout=30) as response:
        return response.read()


def main():
    entries = json.loads(fetch(
        f"https://api.github.com/repos/ethereum/EthLib/contents/{SOURCE}?ref={REVISION}"
    ))
    cases = []
    checksums = []
    for entry in sorted(entries, key=lambda item: item["name"]):
        if entry["type"] != "dir":
            continue
        path = f"{SOURCE}/{entry['name']}/data.yaml"
        raw = fetch(f"https://raw.githubusercontent.com/ethereum/EthLib/{REVISION}/{path}")
        # This intentionally accepts only the pinned fixture schema, not general YAML.
        text = raw.decode().replace("\r\n", "\n")
        fields = dict(re.findall(r"^  (public_key|message|signature): '(0x[0-9a-f]*)'$", text, re.M))
        output = re.search(r"^output: (true|false|null)$", text, re.M)
        if set(fields) != {"public_key", "message", "signature"} or output is None:
            raise ValueError(f"Unexpected fixture schema: {path}")
        cases.append({"name": entry["name"], **fields, "expected": json.loads(output[1])})
        checksums.append(f"{hashlib.sha256(raw).hexdigest()}  {path}\n")
    destination = ROOT / "tests" / "vectors"
    destination.mkdir(parents=True, exist_ok=True)
    (destination / "ethlib.json").write_text(json.dumps(cases, indent=2) + "\n", encoding="utf-8", newline="\n")
    (destination / "SHA256SUMS").write_text("".join(checksums), encoding="utf-8", newline="\n")
    print(f"Imported {len(cases)} verification cases from EthLib {REVISION}")


if __name__ == "__main__":
    main()
