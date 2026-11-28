import Mathlib

/-!
# Popcount monotonicity for OEIS A324608

Source: https://oeis.org/A324608 and https://oeis.org/A308092
Credit: @etaubman

Matthew Scroggs proved Peter Kagey's conjecture in June 2019:
https://www.mscroggs.co.uk/blog/65

The sequence A308092 starts with 1, 2. Write the terms in binary and
concatenate them. Their sum through position n is the value of the first n
bits of this stream. Appending a bit b to the prefix p gives 2*p+b, so the
next term is p+b. The queue stores the suffix of the stream waiting to be
read. After the first two terms the prefix is binary 11 and the queue is 0.
The Lean indexing below starts at zero (OEIS starts at one).
-/

namespace OMA.S_oeis_a324608

def nextBit (queue : List ℕ) : ℕ :=
  if queue.head? = some 1 then 1 else 0

def state : ℕ → ℕ × List ℕ
  | 0 => (3, [0])
  | n + 1 =>
    let s := state n
    let b := nextBit s.2
    (2 * s.1 + b, s.2.drop 1 ++ (Nat.digits 2 (s.1 + b)).reverse)

def term : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => (state n).1 + nextBit (state n).2

def ones (x : ℕ) : ℕ := (Nat.digits 2 x).count 1

theorem main : Monotone (fun n => ones (term n)) := by
  sorry

end OMA.S_oeis_a324608
