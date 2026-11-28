import Mathlib

/-!
# A083942: Positions of breadth-first-wise encodings (A002542) of the complete binary trees (A084107) in A014486.

Source: https://oeis.org/A083942
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

## The conjecture

OEIS A083942 (offset 0, DATA `0, 1, 8, 625, 13402696, 19720133460129649`), FORMULA line:

> Conjecture: a(n) = Sum_{k=1..2^n-1} A000108(k). - Alexander Adamchuk, Nov 10 2007

where A000108 are the Catalan numbers (Mathlib's `catalan`).

The entry has a second conjecture by Adamchuk on the same day, `a(n) = A014138(2^n-2)` for
`n > 0`. With the present indexing of A014138 (offset 0, `A014138(n) = Sum_{k=1..n} A000108(k)`,
DATA `0, 1, 3, 8, 22, ...`) it reads `a(2) = A014138(2) = 3`, whereas `a(2) = 8`. So it is
the first conjecture written against an older offset of A014138. It is not stated here, because
as written it is false for a reason that has nothing to do with the mathematics.

## Modelling choices

* A014486 lists, in increasing order, the totally balanced numbers: numbers whose binary
  expansion has as many 0's as 1's and in which, reading from the most significant bit to the
  least significant one, the number of 0's never exceeds the number of 1's. `0` (empty
  expansion) is the first term. `TB x` is this property, read on `(Nat.digits 2 x).reverse`
  (most significant digit first).
* A080300 is the global ranking function: the position of `x` in A014486 (0 if `x` is not in
  A014486). Positions start at 0, as the offset of A014486 is 0. For a totally balanced `x`, its
  position is `Nat.count TB x`, the number of totally balanced numbers below `x`.
* The breadth-first encoding of the complete binary tree of depth `n` (`n` levels of internal
  nodes, `2^n - 1` of them) is `1^(2^n-1) 0^(2^n-1)` in binary. Its value is
  `c n = 2^(2^(n+1)-2) - 2^(2^n-1)` (`0, 2, 56, 16256, ...` for `n = 0, 1, 2, 3`). This is
  A002542(n+1) in the present indexing of A002542 (offset 1, `a(n) = 2^(2^n-2) - 2^(2^(n-1)-1)`).
  The entry's FORMULA `a(n) = A080300(A002542(n))` predates that offset. With `c n` the
  definition `a n = A080300 (c n)` reproduces the DATA line (`a 0 = 0`, `a 1 = 1`, `a 2 = 8`,
  `a 3 = 625`).
* The conjecture is stated for `n ≥ 1` (for `n = 0` the sum is empty and `a 0 = 0` holds
  trivially; Adamchuk's companion conjecture says `n > 0`).
-/

namespace OMA.S_oeis_a083942

/-- Totally balanced: the binary expansion (most significant bit first) has as many 0's as 1's,
and no prefix has more 0's than 1's (prefixes longer than the expansion are the whole
expansion, so only lengths up to the number of digits need checking). -/
def TB (x : ℕ) : Prop :=
  ((Nat.digits 2 x).reverse.count 0 = (Nat.digits 2 x).reverse.count 1) ∧
    ∀ i ≤ (Nat.digits 2 x).length,
      ((Nat.digits 2 x).reverse.take i).count 0 ≤ ((Nat.digits 2 x).reverse.take i).count 1

instance : DecidablePred TB := fun x => by
  unfold TB
  infer_instance

/-- A080300: the position of `x` in A014486 (positions start at 0), or 0 if `x` is not there. -/
def A080300 (x : ℕ) : ℕ := if TB x then Nat.count TB x else 0

/-- The breadth-first encoding `1^(2^n-1) 0^(2^n-1)` of the complete binary tree of depth `n`. -/
def c (n : ℕ) : ℕ := 2 ^ (2 ^ (n + 1) - 2) - 2 ^ (2 ^ n - 1)

/-- A083942. -/
def a (n : ℕ) : ℕ := A080300 (c n)

/-- Alexander Adamchuk's conjecture (Nov 10 2007): `a(n) = Sum_{k=1..2^n-1} A000108(k)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (2 ^ n - 1), catalan k := by
  sorry

end OMA.S_oeis_a083942
