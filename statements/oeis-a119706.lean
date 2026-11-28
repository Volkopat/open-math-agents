import Mathlib

/-!
# A119706: Total length of longest runs of 1's in all bitstrings of length n.

Source: https://oeis.org/A119706
Credit: @esracummings31-blip

Conjecture (R. J. Mathar, Jun 05 2025): a(n) = A102712(n+1) - 2^n,
where A102712(m) is the sum of the largest parts of all compositions of m.

Encoding: a bitstring of length `n` is a `List.Vector Bool n` (`true` = 1).
Its maximal runs of 1's are the pieces of `w.splitOn false`
(the maximal blocks of consecutive `true`s, with empty pieces between adjacent `false`s),
so the length of the longest run of 1's is the maximum length of these pieces
(0 if there is no 1). Compositions of `m` are Mathlib's `Composition m`.
Offsets: A119706 has offset 1, so the conjecture is stated for `n ≥ 1`.
-/

namespace OMA.S_oeis_a119706

/-- Length of the longest run of `true`s (1's) in a bitstring. -/
def longestRun (w : List Bool) : ℕ := ((w.splitOn false).map List.length).foldr max 0

/-- A119706: total length of longest runs of 1's in all bitstrings of length `n`. -/
def a (n : ℕ) : ℕ := ∑ v : List.Vector Bool n, longestRun v.toList

/-- Largest part of a composition (0 for the empty composition). -/
def largestPart {m : ℕ} (c : Composition m) : ℕ := c.blocks.foldr max 0

/-- A102712: sum of largest parts of all compositions of `m`. -/
def A102712 (m : ℕ) : ℕ := ∑ c : Composition m, largestPart c

theorem main : ∀ n : ℕ, 1 ≤ n → a n = A102712 (n + 1) - 2 ^ n := by
  sorry

end OMA.S_oeis_a119706
