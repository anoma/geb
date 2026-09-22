// Copyright (c) 2026 Terence Rokop. Apache-2.0; see LICENSE.
// Standalone experiment, not a wire format or presheaf recognizer.
// rustc -O --edition=2021 bench.rs -o /tmp/geb-tree-bench
// rustc -O --edition=2021 --test bench.rs -o /tmp/geb-tree-tests
// Run with input bytes and optional maximum scan workers (1, 2, 4, or 8; default 2).
// Summary composition: Navarro and Sadakane, TALG 10(3), 2014.
// Workload mixes adapted from YCSB's workload A/B and hotspot parameters:
// https://github.com/brianfrankcooper/YCSB/tree/master/workloads
use std::{collections::HashSet, hint::black_box, sync::Arc, time::Instant};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Summary { total: i64, minimum: i64 }
impl Summary {
    fn append(self, b: Self) -> Self {
        Self { total: self.total + b.total, minimum: self.minimum.min(self.total + b.minimum) }
    }
}
fn scalar(data: &[u8]) -> Summary {
    let mut s = Summary::default();
    for &byte in data {
        for bit in 0..8 {
            s.total += if byte >> bit & 1 == 1 { 1 } else { -1 };
            s.minimum = s.minimum.min(s.total);
        }
    }
    s
}
fn table() -> [Summary; 256] { std::array::from_fn(|b| scalar(&[b as u8])) }
fn scan(data: &[u8], tab: &[Summary; 256]) -> Summary {
    data.iter().fold(Summary::default(), |s, b| s.append(tab[*b as usize]))
}
fn parallel(data: &[u8], tab: &[Summary; 256], threads: usize) -> Summary {
    std::thread::scope(|scope| {
        let tasks: Vec<_> = data.chunks(data.len().div_ceil(threads).max(1))
            .map(|chunk| scope.spawn(move || scan(chunk, tab))).collect();
        tasks.into_iter().fold(Summary::default(), |s, t| s.append(t.join().unwrap()))
    })
}

type Tree = Arc<Node>;
enum Kind { Leaf(Box<[u8]>), Branch(Tree, Tree) }
struct Node { len: usize, height: u32, summary: Summary, kind: Kind }
fn leaf(data: &[u8], tab: &[Summary; 256]) -> Tree {
    assert!(!data.is_empty() && data.len() <= i64::MAX as usize / 8);
    Arc::new(Node { len: data.len(), height: 1, summary: scan(data, tab),
        kind: Kind::Leaf(data.into()) })
}
fn branch(l: Tree, r: Tree) -> Tree {
    let len = l.len.checked_add(r.len).unwrap();
    assert!(len <= i64::MAX as usize / 8);
    Arc::new(Node { len, height: 1 + l.height.max(r.height),
        summary: l.summary.append(r.summary), kind: Kind::Branch(l, r) })
}
fn children(t: &Tree) -> (&Tree, &Tree) {
    match &t.kind { Kind::Branch(l, r) => (l, r), _ => unreachable!() }
}
fn balance(l: Tree, r: Tree) -> Tree {
    if l.height > r.height + 1 {
        let (ll, lr) = children(&l);
        if ll.height >= lr.height { branch(ll.clone(), branch(lr.clone(), r)) }
        else {
            let (a, b) = children(lr);
            branch(branch(ll.clone(), a.clone()), branch(b.clone(), r))
        }
    } else if r.height > l.height + 1 {
        let (rl, rr) = children(&r);
        if rr.height >= rl.height { branch(branch(l, rl.clone()), rr.clone()) }
        else {
            let (a, b) = children(rl);
            branch(branch(l, a.clone()), branch(b.clone(), rr.clone()))
        }
    } else { branch(l, r) }
}
fn join(l: Tree, r: Tree) -> Tree {
    if l.height > r.height + 1 {
        let (ll, lr) = children(&l);
        balance(ll.clone(), join(lr.clone(), r))
    } else if r.height > l.height + 1 {
        let (rl, rr) = children(&r);
        balance(join(l, rl.clone()), rr.clone())
    } else { branch(l, r) }
}
fn concat(l: Option<Tree>, r: Option<Tree>) -> Option<Tree> {
    match (l, r) { (Some(l), Some(r)) => Some(join(l, r)), (l, None) => l, (None, r) => r }
}
fn build(data: &[u8], page: usize, tab: &[Summary; 256]) -> Tree {
    assert!(page > 0);
    if data.len() <= page { leaf(data, tab) }
    else {
        let middle = data.len().div_ceil(page).div_ceil(2) * page;
        branch(build(&data[..middle], page, tab), build(&data[middle..], page, tab))
    }
}
fn get(t: &Tree, i: usize) -> u8 {
    assert!(i < t.len);
    match &t.kind {
        Kind::Leaf(data) => data[i],
        Kind::Branch(l, r) => if i < l.len { get(l, i) } else { get(r, i-l.len) },
    }
}
fn update(t: &Tree, i: usize, value: u8, tab: &[Summary; 256]) -> Tree {
    assert!(i < t.len);
    match &t.kind {
        Kind::Leaf(data) => { let mut data = data.to_vec(); data[i] = value; leaf(&data, tab) }
        Kind::Branch(l, r) => if i < l.len { branch(update(l, i, value, tab), r.clone()) }
            else { branch(l.clone(), update(r, i-l.len, value, tab)) },
    }
}
fn split(t: &Tree, i: usize, tab: &[Summary; 256]) -> (Option<Tree>, Option<Tree>) {
    assert!(i <= t.len);
    if i == 0 { return (None, Some(t.clone())); }
    if i == t.len { return (Some(t.clone()), None); }
    match &t.kind {
        Kind::Leaf(data) => (Some(leaf(&data[..i], tab)), Some(leaf(&data[i..], tab))),
        Kind::Branch(l, r) => if i < l.len {
            let (a, b) = split(l, i, tab); (a, concat(b, Some(r.clone())))
        } else {
            let (a, b) = split(r, i-l.len, tab); (concat(Some(l.clone()), a), b)
        },
    }
}
// ponytail: byte-aligned splices and no underfilled-leaf coalescing; add bit spans
// and an occupancy invariant before claiming a succinct dynamic representation.
fn splice(t: &Tree, start: usize, removed: usize, inserted: Option<Tree>,
          tab: &[Summary; 256]) -> Option<Tree> {
    assert!(start <= t.len && removed <= t.len-start);
    let (left, tail) = split(t, start, tab);
    let right = tail.and_then(|tail| split(&tail, removed, tab).1);
    concat(concat(left, inserted), right)
}
fn range(t: &Tree, start: usize, end: usize, tab: &[Summary; 256]) -> Summary {
    assert!(start <= end && end <= t.len);
    if start == 0 && end == t.len { return t.summary; }
    match &t.kind {
        Kind::Leaf(data) => scan(&data[start..end], tab),
        Kind::Branch(l, r) => {
            let a = if start < l.len { range(l, start, end.min(l.len), tab) }
                else { Summary::default() };
            let b = if end > l.len { range(r, start.saturating_sub(l.len), end-l.len, tab) }
                else { Summary::default() };
            a.append(b)
        }
    }
}
// Find the first zero excess after an opening, using cached summaries to skip blocks.
fn hit(t: &Tree, start: usize, depth: &mut i64) -> Option<usize> {
    if start >= t.len * 8 { return None; }
    if start == 0 && *depth + t.summary.minimum > 0 {
        *depth += t.summary.total; return None;
    }
    match &t.kind {
        Kind::Leaf(data) => {
            for i in start..data.len()*8 {
                *depth += if data[i/8] >> (i%8) & 1 == 1 { 1 } else { -1 };
                if *depth == 0 { return Some(i); }
            }
            None
        }
        Kind::Branch(l, r) => hit(l, start, depth).or_else(||
            hit(r, start.saturating_sub(l.len*8), depth).map(|i| i + l.len*8)),
    }
}
fn closing(t: &Tree, open: usize) -> Option<usize> {
    if open >= t.len*8 || get(t, open/8) >> (open%8) & 1 == 0 { return None; }
    hit(t, open+1, &mut 1)
}
// Requested bytes reachable from the supplied roots, counting shared nodes once.
// Excludes other roots, the input buffer, the lookup table, allocator metadata,
// allocation rounding, thread stacks, temporary allocations and the HashSet used here.
fn live_bytes(roots: &[Tree]) -> usize {
    fn visit(t: &Tree, seen: &mut HashSet<*const Node>) -> usize {
        if !seen.insert(Arc::as_ptr(t)) { return 0; }
        std::mem::size_of::<Node>() + 2*std::mem::size_of::<usize>() + match &t.kind {
            Kind::Leaf(data) => data.len(),
            Kind::Branch(l, r) => visit(l, seen) + visit(r, seen),
        }
    }
    let mut seen = HashSet::new();
    roots.len()*std::mem::size_of::<Tree>() + roots.iter().map(|t| visit(t, &mut seen)).sum::<usize>()
}
fn rng(state: &mut u64) -> u64 {
    *state ^= *state << 13; *state ^= *state >> 7; *state ^= *state << 17; *state
}
fn positions(n: usize, count: usize, hot: bool) -> Vec<usize> {
    let mut seed = 0x139bc5e1;
    (0..count).map(|i| (rng(&mut seed) as usize) %
        if hot && i%5 != 0 { (n/5).max(1) } else { n }).collect()
}
fn measure<T>(mut f: impl FnMut() -> T) -> f64 {
    black_box(f());
    let mut samples = Vec::new();
    for _ in 0..7 {
        let t = Instant::now(); black_box(f()); samples.push(t.elapsed().as_secs_f64());
    }
    samples.sort_by(f64::total_cmp); samples[3]
}
fn report(name: &str, n: usize, page: usize, ops: usize, seconds: f64, live: usize) {
    println!("{name},{n},{page},{ops},{seconds:.9},{live}");
}
fn main() {
    let n: usize = std::env::args().nth(1).map(|s| s.parse().unwrap()).unwrap_or(1<<20);
    let max_threads: usize = std::env::args().nth(2).map(|s| s.parse().unwrap()).unwrap_or(2);
    assert!((1024..=1<<28).contains(&n) && n%2 == 0);
    assert!([1,2,4,8].contains(&max_threads));
    let tab = table();
    println!("operation,input_bytes,page_bytes,operations,median_seconds,live_requested_bytes");
    for (shape, data) in [("star", vec![0x55; n]),
        ("chain", [vec![255;n/2],vec![0;n/2]].concat()),
        ("nested", vec![0x0f;n])] {
        let expect = scalar(&data);
        assert_eq!(scan(&data,&tab), expect);
        report(&format!("scalar_{shape}"),n,0,1,measure(||scalar(black_box(&data))),n);
        report(&format!("table8_{shape}"),n,0,1,measure(||scan(black_box(&data),&tab)),n);
        for p in [2,4,8].into_iter().filter(|p| *p <= max_threads) {
            assert_eq!(parallel(&data,&tab,p),expect);
            report(&format!("parallel{p}_{shape}"),n,0,1,measure(||parallel(black_box(&data),&tab,p)),n);
        }
    }
    let data=vec![0x55;n]; // Four empty rose-tree roots per byte; a balanced forest.
    let ops=1000;
    for page in [256,1024,4096] {
        let root=build(&data,page,&tab);
        let bytes=live_bytes(&[root.clone()]);
        report("build",n,page,1,measure(||build(black_box(&data),page,&tab)),bytes);
        let pos=positions(n,ops,false);
        report("read",n,page,ops,measure(||pos.iter().map(|i|get(&root,*i) as u64).sum::<u64>()),bytes);
        report("find_close",n,page,ops,measure(||pos.iter().map(|i|closing(&root,i*8).unwrap()).sum::<usize>()),bytes);
        report("range_4k_summary",n,page,ops,measure(||pos.iter().map(|i|
            range(&root,*i,(*i+4096).min(n),&tab).total).sum::<i64>()),bytes);
        for hot in [false,true] {
            let pos=positions(n,ops,hot);
            for write_every in [2,20] {
                let run=|| {
                    let mut roots=vec![root.clone()]; let mut checksum=0u64;
                    for (j,&i) in pos.iter().enumerate() {
                        if j%write_every==0 {
                            let next=update(roots.last().unwrap(),i,if j%4==0 {0x33} else {0x55},&tab);
                            roots.push(next);
                        } else { checksum+=get(roots.last().unwrap(),i) as u64; }
                    }
                    black_box(checksum); roots
                };
                let roots=run();
                report(&format!("mix{}_{}",100/write_every,if hot {"hot"} else {"uniform"}),
                    n,page,ops,measure(run),live_bytes(&roots));
            }
        }
        let run=|| {
            let mut roots=vec![root.clone()];
            for (j,&i) in pos.iter().enumerate() {
                let old=roots.last().unwrap();
                let next=if j%2==0 {splice(old,i,0,Some(leaf(&[0x55],&tab)),&tab)}
                    else {splice(old,i,1,None,&tab)};
                roots.push(next.unwrap());
            }
            roots
        };
        let roots=run();
        report("splice_history",n,page,ops,measure(run),live_bytes(&roots));
        // Branching from an old version, not just appending to one version chain.
        let branch_run=||pos.iter().map(|i|update(&root,*i,0x33,&tab)).collect::<Vec<_>>();
        report("branch_history",n,page,ops,measure(branch_run),live_bytes(&branch_run()));
    }
    let pos=positions(n,ops,false);
    // Flat immutable baseline retains every update, under the same 50/50 mix.
    let run=|| {
        let mut roots=vec![data.clone()]; let mut checksum=0u64;
        for (j,&i) in pos.iter().enumerate() {
            if j%2==0 { let mut next=roots.last().unwrap().clone(); next[i]=0x33; roots.push(next); }
            else { checksum+=roots.last().unwrap()[i] as u64; }
        }
        black_box(checksum); roots
    };
    // ponytail: cap flat history at 2 MiB inputs to avoid >1 GiB retained allocations.
    if n<=1<<21 { report("flat_mix50_uniform",n,0,ops,measure(run),(ops/2+1)*n); }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn flatten(t: &Tree) -> Vec<u8> {
        match &t.kind { Kind::Leaf(b)=>b.to_vec(), Kind::Branch(l,r)=>[flatten(l),flatten(r)].concat() }
    }
    fn valid(t: &Tree) {
        match &t.kind {
            Kind::Leaf(b)=>assert_eq!(t.len,b.len()),
            Kind::Branch(l,r)=> {
                assert!(l.height.abs_diff(r.height)<=1); valid(l); valid(r);
                assert_eq!(t.height,1+l.height.max(r.height)); assert_eq!(t.len,l.len+r.len);
            }
        }
        assert_eq!(t.summary,scalar(&flatten(t)));
    }
    #[test]
    fn exhaustive_summaries_and_navigation() {
        let tab=table();
        for w in 0u32..65536 {
            let bytes=(w as u16).to_le_bytes(); let t=build(&bytes,1,&tab);
            assert_eq!(scan(&bytes,&tab),scalar(&bytes));
            assert_eq!(t.summary,scalar(&bytes));
            for i in 0..16 {
                let expected=if w>>i&1==0 {None} else {
                    let mut d=1;
                    (i+1..16).find(|j| { d+=if w>>j&1==1 {1} else {-1}; d==0 })
                };
                assert_eq!(closing(&t,i),expected);
            }
        }
    }
    #[test]
    fn persistent_edits_against_flat_oracle() {
        let tab=table(); let mut seed=815;
        let mut histories=vec![(build(&[0x55;63],8,&tab),vec![0x55;63])];
        for k in 0..1500 {
            let version=rng(&mut seed) as usize%histories.len();
            let (old,flat)=&histories[version]; let mut expected=flat.clone();
            let pos=rng(&mut seed) as usize%(flat.len()+1);
            let removed=(rng(&mut seed) as usize%9).min(flat.len()-pos);
            let added:Vec<u8>=(0..(k%7)).map(|_|rng(&mut seed) as u8).collect();
            let insert=if added.is_empty(){None}else{Some(build(&added,8,&tab))};
            let result=splice(old,pos,removed,insert,&tab);
            expected.splice(pos..pos+removed,added);
            assert_eq!(flatten(old),*flat);
            if let Some(t)=result {
                valid(&t); assert_eq!(flatten(&t),expected);
                let i=rng(&mut seed) as usize%t.len;
                let end=(i+7).min(t.len);
                assert_eq!(range(&t,i,end,&tab),scalar(&expected[i..end]));
                assert_eq!(get(&t,i),expected[i]);
                let u=update(&t,i,37,&tab); expected[i]=37; valid(&u);
                assert_eq!(flatten(&u),expected); histories.push((u,expected));
            } else { assert!(expected.is_empty()); }
        }
        for (t,flat) in histories { assert_eq!(flatten(&t),flat); }
    }
}
