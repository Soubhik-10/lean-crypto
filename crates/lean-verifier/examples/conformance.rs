//! Development-only bridge for the pinned Lean fixture and wire differential drivers.
//! Compiles the production VM source; arbitrary programs are not exposed by the library API.
extern crate alloc;

use std::io::{BufRead, Write};

#[allow(dead_code, clippy::needless_range_loop, clippy::too_many_arguments)]
#[path = "../src/vm/mod.rs"]
mod vm;

use vm::{Bytecode, E, K, Proof, merkle::MerklePath};

struct Reader<'a>(&'a [u8]);
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, rest) = self.0.split_at_checked(n)?;
        self.0 = rest;
        Some(head)
    }
    fn u32(&mut self) -> Option<usize> {
        Some(u32::from_le_bytes(self.take(4)?.try_into().ok()?) as usize)
    }
    fn u64(&mut self) -> Option<u64> {
        Some(u64::from_le_bytes(self.take(8)?.try_into().ok()?))
    }
    fn phases(&mut self) -> Option<Vec<Vec<MerklePath>>> {
        let mut phases = Vec::new();
        for _ in 0..self.u32()? {
            let mut paths = Vec::new();
            for _ in 0..self.u32()? {
                let leaf_index = self.u64()?;
                let n = self.u32()?;
                let leaf = self
                    .take(n.checked_mul(8)?)?
                    .chunks_exact(8)
                    .map(|b| K(u64::from_le_bytes(b.try_into().unwrap())))
                    .collect();
                let n = self.u32()?;
                let siblings = self
                    .take(n.checked_mul(32)?)?
                    .chunks_exact(32)
                    .map(|b| b.try_into().unwrap())
                    .collect();
                paths.push(MerklePath {
                    leaf_index,
                    leaf,
                    siblings,
                });
            }
            phases.push(paths);
        }
        Some(phases)
    }
}

fn structured(stream: &[u8], phases: &[u8]) -> Option<Proof> {
    if !stream.len().is_multiple_of(16) {
        return None;
    }
    let stream = stream
        .chunks_exact(16)
        .map(|b| {
            E::new(
                u64::from_le_bytes(b[..8].try_into().unwrap()),
                u64::from_le_bytes(b[8..].try_into().unwrap()),
            )
        })
        .collect();
    let mut input = Reader(phases);
    let merkle_openings = input.phases()?;
    if !input.0.is_empty() {
        return None;
    }
    // Structured mutations can give unrelated paths. Recompute every root and
    // mark inconsistent phases invalid; never trust a root from fixture bytes.
    let merkle_roots = merkle_openings
        .iter()
        .map(|paths| {
            if paths.iter().any(|p| p.siblings.len() > 64) {
                return None;
            }
            let root = paths.first()?.root();
            paths.iter().all(|p| p.root() == root).then_some(root)
        })
        .collect();
    Some(Proof {
        stream,
        merkle_openings,
        merkle_roots,
    })
}

fn from_plain(bytes: &[u8]) -> Option<Proof> {
    let mut input = Reader(bytes);
    let count = input.u32()?;
    let stream = input.take(count.checked_mul(16)?)?;
    structured(stream, input.0)
}

fn put_u32(out: &mut Vec<u8>, n: usize) {
    out.extend(
        u32::try_from(n)
            .expect("fixture count fits u32")
            .to_le_bytes(),
    );
}
fn plain(proof: &Proof) -> Vec<u8> {
    let mut out = Vec::new();
    put_u32(&mut out, proof.stream.len());
    for e in &proof.stream {
        out.extend(e.c0.to_le_bytes());
        out.extend(e.c1.to_le_bytes());
    }
    put_u32(&mut out, proof.merkle_openings.len());
    for paths in &proof.merkle_openings {
        put_u32(&mut out, paths.len());
        for p in paths {
            out.extend(p.leaf_index.to_le_bytes());
            put_u32(&mut out, p.leaf.len());
            for k in &p.leaf {
                out.extend(k.0.to_le_bytes());
            }
            put_u32(&mut out, p.siblings.len());
            for h in &p.siblings {
                out.extend(h);
            }
        }
    }
    out
}
fn read(path: &str) -> Result<Vec<u8>, String> {
    std::fs::read(path).map_err(|e| format!("{path}: {e}"))
}
fn write(path: &str, bytes: &[u8]) -> Result<(), String> {
    std::fs::write(path, bytes).map_err(|e| format!("{path}: {e}"))
}
fn run(args: &[&str]) -> Result<String, String> {
    match args {
        ["decode", input, output] => {
            let bytes = read(input)?;
            let Some(proof) = Proof::from_bytes(&bytes) else {
                return Ok("none".into());
            };
            write(output, &plain(&proof))?;
            Ok(if proof.to_bytes() == bytes {
                "some reencode-ok"
            } else {
                "some reencode-differs"
            }
            .into())
        }
        ["encode", input, output] => {
            let Some(proof) = from_plain(&read(input)?) else {
                return Ok("malformed".into());
            };
            let bytes = proof.to_bytes();
            write(output, &bytes)?;
            Ok(if Proof::from_bytes(&bytes).as_ref() == Some(&proof) {
                "encoded roundtrip-ok"
            } else {
                "encoded roundtrip-differs"
            }
            .into())
        }
        ["vector", output] => {
            let rows = [[0, 0, 1], [0, 2, 3], [0, 0, 4], [0, 5, 0]];
            let leaves: Vec<_> = rows
                .iter()
                .map(|r| vm::merkle::hash_leaf(&r.map(K)).0)
                .collect();
            let parents: Vec<_> = leaves
                .chunks_exact(2)
                .map(|p| vm::merkle::hash_pair(&p[0], &p[1]).0)
                .collect();
            let proof = Proof {
                stream: vec![E::new(1, 2)],
                merkle_openings: vec![
                    [3, 1, 3]
                        .into_iter()
                        .map(|i| MerklePath {
                            leaf_index: i as u64,
                            leaf: rows[i].map(K).to_vec(),
                            siblings: vec![leaves[i ^ 1], parents[(i / 2) ^ 1]],
                        })
                        .collect(),
                ],
                merkle_roots: vec![Some(vm::merkle::hash_pair(&parents[0], &parents[1]))],
            };
            let bytes = proof.to_bytes();
            assert_eq!(Proof::from_bytes(&bytes), Some(proof));
            write(output, &bytes)?;
            Ok(format!("vector {}", bytes.len()))
        }
        paths if paths.len() == 3 || paths.len() == 4 => {
            let files: Vec<_> = paths.iter().map(|p| read(p)).collect::<Result<_, _>>()?;
            if !files[0].len().is_multiple_of(8) || files[1].len() != 32 {
                return Ok("reject input shape".into());
            }
            let words: Vec<_> = files[0]
                .chunks_exact(8)
                .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
                .collect();
            let proof = if files.len() == 3 {
                Proof::from_bytes(&files[2])
            } else {
                structured(&files[2], &files[3])
            };
            let Some(proof) = proof else {
                return Ok("reject encoding".into());
            };
            let result = Bytecode::new(&words, None).and_then(|bytecode| {
                vm::verify_execution(&bytecode, files[1].as_slice().try_into().unwrap(), &proof)
            });
            Ok(match result {
                Ok(_) => "accept".into(),
                Err(e) => format!("reject {e:?}"),
            })
        }
        _ => Err("expected a wire command or three/four verification files".into()),
    }
}
fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args == ["--batch"] {
        let mut out = std::io::stdout().lock();
        for line in std::io::stdin().lock().lines() {
            let line = line.expect("read fixture command");
            if !line.is_empty() {
                // A panic or I/O error is a failing process, never a successful rejection.
                writeln!(
                    out,
                    "{}",
                    run(&line.split('\t').collect::<Vec<_>>()).expect("fixture command")
                )
                .expect("write verdict");
                out.flush().expect("flush verdict");
            }
        }
    } else {
        println!(
            "{}",
            run(&args.iter().map(String::as_str).collect::<Vec<_>>()).expect("fixture command")
        );
    }
}
