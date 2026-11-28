import Mathlib

/-!
# A239907: Let cn(n,k) denote the number of times 11..1 (k 1's) appears in the binary
representation of n; a(n) = n - cn(n,1) + cn(n,2) - cn(n,3) + cn(n,4) - ... .

Source: https://oeis.org/A239907
Credit: @bnb9001

Offset 0: 0, 0, 1, 2, 3, 3, 5, 5, 7, ... Occurrences are counted with overlaps, by their starting
bit position (`Nat.testBit`); no run of 1's in n is longer than n, so the alternating sum stops at
k = n. A035263 is the parity of the 2-adic valuation of 2n, and
A329320(n) = Sum_{k=0..floor(log_2(n))} 1 - A035263(1 + floor(n/2^k)).

Conjecture (Mikhail Kurkov, Oct 13 2021): a(n) = n - A329320(n) for n >= 0.
-/

namespace OMA.S_oeis_a239907

open Finset

/-- `cn(n,k)`: the number of occurrences of `k` consecutive 1's in the binary representation of
`n` (counted by starting bit position; positions `≥ n` carry no 1's since `n < 2^n`). -/
def cn (n k : ℕ) : ℕ := ((range n).filter (fun i => ∀ j < k, n.testBit (i + j))).card

/-- A239907: `a(n) = n - cn(n,1) + cn(n,2) - cn(n,3) + ...` (runs are at most `n` long). -/
def a (n : ℕ) : ℤ := (n : ℤ) - ∑ k ∈ Icc 1 n, (-1) ^ (k + 1) * (cn n k : ℤ)

/-- A035263: parity of the 2-adic valuation of `2n`. -/
def A035263 (n : ℕ) : ℕ := (padicValNat 2 n + 1) % 2

/-- A329320: `a(n) = Sum_{k=0..floor(log_2(n))} 1 - A035263(1 + floor(n/2^k))`. -/
def A329320 (n : ℕ) : ℕ := ∑ k ∈ range (Nat.log 2 n + 1), (1 - A035263 (1 + n / 2 ^ k))

/-- Kurkov's conjecture: `a(n) = n - A329320(n)` for all `n`. -/
theorem main : ∀ n : ℕ, a n = (n : ℤ) - (A329320 n : ℤ) := by
  sorry

end OMA.S_oeis_a239907
