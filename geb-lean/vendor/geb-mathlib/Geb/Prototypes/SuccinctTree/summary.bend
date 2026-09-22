# Copyright (c) 2026 Terence Rokop. Apache-2.0; see LICENSE.
# Generated-word summary reduction, not input ingestion or a typechecker.
# Bits are LSB first. Signed summaries stay within I24 for depth <= 18.
# The seed changes along each branch; no stored input tree is required.
def word_summary(bits, word, total, minimum):
  switch bits:
    case 0:
      return (total, minimum)
    case _:
      if (word & 1) == 1:
        next = total + +1
      else:
        next = total - +1
      if next < minimum:
        lower = next
      else:
        lower = minimum
      return word_summary(bits - 1, word >> 1, next, lower)

def summary(depth, seed):
  switch depth:
    case 0:
      return word_summary(24, seed, +0, +0)
    case _:
      (a, amin) = summary(depth - 1, seed * 1664525 + 7271263)
      (b, bmin) = summary(depth - 1, seed * 5918261 + 1)
      if amin < a + bmin:
        lower = amin
      else:
        lower = a + bmin
      return (a + b, lower)

def main():
  return summary(16, 7919)
