#!/usr/bin/env python3
"""Check the generated-word reduction and measure whole-process wall times.

Usage: python3 runtimes.py CPU_BINARY GPU_BINARY HVM4_BINARY
The first two are compiled from summary.bend; HVM4 reads summary.hvm.
All executables are passed explicitly; no tool download or compilation happens here.
"""
import csv
from pathlib import Path
import re
import statistics
import subprocess
import sys
import time


def reference(depth, seed):
    if depth == 0:
        total = minimum = 0
        for bit in range(24):
            total += 1 if seed >> bit & 1 else -1
            minimum = min(minimum, total)
        return total, minimum
    a, amin = reference(depth - 1, (seed * 1664525 + 7271263) & 0xFFFFFF)
    b, bmin = reference(depth - 1, (seed * 5918261 + 1) & 0xFFFFFF)
    return a + b, min(amin, a + bmin)


def main():
    cpu, gpu, hvm4 = sys.argv[1:]
    writer = csv.writer(sys.stdout)
    writer.writerow(["runtime", "depth", "total", "minimum", "median_wall_seconds", "samples"])
    source = Path(__file__).with_name("summary.hvm")
    for label, command, depth in [("hvm2-cpu", [cpu], 16), ("hvm2-cuda", [gpu], 16),
                                  ("hvm4", [hvm4, str(source), "-s"], 12)]:
        expected = reference(depth, 7919)
        samples = []
        for sample in range(4):  # One warm-up process, then three timed processes.
            start = time.perf_counter()
            result = subprocess.run(command, check=True, capture_output=True, text=True, timeout=60)
            elapsed = time.perf_counter() - start
            pattern = r"#S\{(\d+),(\d+)\}" if label == "hvm4" else r"Result: \(([+-]?\d+) ([+-]?\d+)\)"
            match = re.search(pattern, result.stdout)
            assert match, result.stdout + result.stderr
            actual = tuple(int(x) for x in match.groups())
            if label == "hvm4":
                actual = tuple(x if x < 2**31 else x - 2**32 for x in actual)
            assert actual == expected, (label, actual, expected)
            if sample:
                samples.append(elapsed)
        writer.writerow([label, depth, *expected, f"{statistics.median(samples):.6f}", 3])
        sys.stdout.flush()


if __name__ == "__main__":
    main()
