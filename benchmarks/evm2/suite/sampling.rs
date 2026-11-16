use serde::Serialize;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

pub struct Case<'a> {
    pub name: String,
    pub work_items: u64,
    pub operation: Box<dyn FnMut(usize) + 'a>,
}

#[derive(Clone, Serialize)]
pub struct Sample {
    pub index: usize,
    pub order: usize,
    pub iterations: u64,
    pub work_items: u64,
    pub elapsed_ns: u64,
    pub started_unix_ns: u64,
    pub ns_per_op: f64,
}

#[derive(Clone, Serialize)]
pub struct Measurement {
    pub name: String,
    pub work_items_per_iteration: u64,
    pub calibrated_iterations: u64,
    pub samples: Vec<Sample>,
}

fn batch(case: &mut Case<'_>, iterations: u64, offset: usize) -> Duration {
    let start = Instant::now();
    for index in 0..iterations {
        (case.operation)((index as usize).wrapping_add(offset));
    }
    start.elapsed()
}

fn next_random(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

pub fn measure(
    cases: &mut [Case<'_>],
    sample_count: usize,
    sample_ms: u64,
    warmup_ms: u64,
    seed: u64,
    mut checkpoint: impl FnMut(&[Measurement]),
) -> Vec<Measurement> {
    let mut result = Vec::with_capacity(cases.len());
    let sample_time = Duration::from_millis(sample_ms);
    for case in cases.iter_mut() {
        let warm = Instant::now();
        let mut offset = 0usize;
        while warm.elapsed() < Duration::from_millis(warmup_ms) {
            (case.operation)(offset);
            offset = offset.wrapping_add(1);
        }
        let mut iterations = 1u64;
        while batch(case, iterations, 0) < sample_time {
            iterations = iterations
                .checked_mul(2)
                .expect("calibration iteration overflow");
            assert!(iterations <= 1 << 40, "calibration failed");
        }
        eprintln!("calibrated {}: {iterations} iterations", case.name);
        result.push(Measurement {
            name: case.name.clone(),
            work_items_per_iteration: case.work_items,
            calibrated_iterations: iterations,
            samples: Vec::with_capacity(sample_count),
        });
    }
    let mut order: Vec<_> = (0..cases.len()).collect();
    let mut state = seed.max(1);
    for sample in 0..sample_count {
        for index in (1..order.len()).rev() {
            let other = next_random(&mut state) as usize % (index + 1);
            order.swap(index, other);
        }
        for (position, &index) in order.iter().enumerate() {
            let iterations = result[index].calibrated_iterations;
            let work_items = iterations.checked_mul(cases[index].work_items).unwrap();
            let started_unix_ns = u64::try_from(
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_nanos(),
            )
            .unwrap();
            let elapsed = batch(&mut cases[index], iterations, sample);
            let elapsed_ns = u64::try_from(elapsed.as_nanos()).expect("sample exceeded u64 ns");
            result[index].samples.push(Sample {
                index: sample,
                order: position,
                iterations,
                work_items,
                elapsed_ns,
                started_unix_ns,
                ns_per_op: elapsed_ns as f64 / work_items as f64,
            });
            if position % 16 == 0 {
                eprintln!(
                    "sample {}/{sample_count}: {}",
                    sample + 1,
                    cases[index].name
                );
            }
        }
        checkpoint(&result);
    }
    result
}
