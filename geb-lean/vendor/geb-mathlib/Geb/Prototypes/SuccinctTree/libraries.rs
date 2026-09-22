// Copyright (c) 2026 Terence Rokop. Apache-2.0; see LICENSE.
// Static indexes only. Constructors and exhaustive query checks are outside timings.
use std::{hint::black_box, time::Instant};
use sux::{bal_paren::JacobsonBalParen, bits::BitVec, traits::BalParen};
use vers_vecs::{BitVec as VersBits, BpTree};

fn median(mut f: impl FnMut() -> usize) -> f64 {
    black_box(f());
    let mut times = Vec::new();
    for _ in 0..7 {
        let start = Instant::now();
        black_box(f());
        times.push(start.elapsed().as_secs_f64());
    }
    times.sort_by(f64::total_cmp);
    times[3]
}
fn main() {
    let nodes: usize = std::env::args().nth(1).unwrap_or("4194304".into()).parse().unwrap();
    assert!((32..=1 << 24).contains(&nodes));
    println!("library,shape,nodes,queries,median_seconds,reported_heap_bytes");
    for shape in ["star", "chain", "nested"] {
        // All shapes are single trees. Nested has a root with chains of <= 31 nodes.
        let mut bits = vec![true];
        match shape {
            "chain" => { bits.resize(nodes, true); bits.resize(2 * nodes - 1, false); }
            "star" => for _ in 1..nodes { bits.extend([true, false]); },
            _ => {
                let mut left = nodes - 1;
                while left > 0 {
                    let k = left.min(31);
                    bits.extend(std::iter::repeat_n(true, k));
                    bits.extend(std::iter::repeat_n(false, k));
                    left -= k;
                }
            }
        }
        bits.push(false);
        let mut expected = vec![0; bits.len()];
        let mut stack = Vec::new();
        let mut opens = Vec::with_capacity(nodes);
        let mut vb = VersBits::new();
        for (i, &bit) in bits.iter().enumerate() {
            vb.append_bit(u64::from(bit));
            if bit { stack.push(i); opens.push(i); }
            else { expected[stack.pop().unwrap()] = i; }
        }
        assert!(stack.is_empty());
        let sb: BitVec = bits.into_iter().collect();
        let vers = BpTree::<512>::from_bit_vector(vb);
        let sux = JacobsonBalParen::new(sb);
        for &i in &opens {
            assert_eq!(vers.close(i), Some(expected[i]));
            assert_eq!(sux.find_close(i), Some(expected[i]));
        }
        let mut seed = 7919u64;
        let queries: Vec<_> = (0..100_000).map(|_| {
            seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
            opens[seed as usize % opens.len()]
        }).collect();
        let vt = median(|| queries.iter().map(|&i| vers.close(black_box(i)).unwrap()).sum());
        let st = median(|| queries.iter().map(|&i| sux.find_close(black_box(i)).unwrap()).sum());
        println!("vers-vecs,{shape},{nodes},{},{vt:.9},{}", queries.len(), vers.heap_size());
        // ponytail: use no extra memory-profiler dependency; blank is unmeasured, not zero.
        println!("sux,{shape},{nodes},{},{st:.9},", queries.len());
    }
}
