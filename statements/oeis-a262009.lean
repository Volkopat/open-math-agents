import Mathlib

/-!
# A262009: the 2-adic valuation of Hanna's divisor sum Sum_{d|n} 2^(d^2) n^2/d^2

Source: https://oeis.org/A262009
Credit: @ivillar

Paul D. Hanna's sequence a(n) = Sum_{d|n} 2^(d^2) * n^2/d^2 (offset 1) is the logarithmic
derivative of A262008. The entry records two conjectures:
A037227(a(n)) = 2*A037227(n) + 1, and a(n) = 2^A037227(n) * d for some odd d,
where A037227(n) = 2*m + 1 when n = 2^m * k with k odd.

Formalization notes:
* `n ^ 2 / d ^ 2` is an exact division for every divisor `d` of `n`.
* A037227(n) is written `2 * padicValNat 2 n + 1` (its formula a(n) = 2*A007814(n) + 1).
-/

namespace OMA.S_oeis_a262009

/-- A037227: `2*m + 1` where `2^m` is the largest power of 2 dividing `n`. -/
def A037227 (n : ℕ) : ℕ := 2 * padicValNat 2 n + 1

/-- A262009: `a(n) = Sum_{d|n} 2^(d^2) * n^2/d^2`. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, 2 ^ (d ^ 2) * (n ^ 2 / d ^ 2)

/-- Both conjectures in A262009, for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    A037227 (a n) = 2 * A037227 n + 1 ∧ ∃ d : ℕ, Odd d ∧ a n = 2 ^ A037227 n * d := by
  sorry

end OMA.S_oeis_a262009
