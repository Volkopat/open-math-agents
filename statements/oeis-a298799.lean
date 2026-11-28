import Mathlib

/-!
# A298799: Expansion of (1-27*x)^(-1/9).

Source: https://oeis.org/A298799
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a298799

/-- The OEIS sequence with `a(n) = (3^n/n!) * ∏_{k=0}^{n-1} (9*k + 1)`. -/
def a (n : ℕ) : ℕ :=
  (3 ^ n * ∏ k ∈ Finset.range n, (9 * k + 1)) / Nat.factorial n

/-- The exceptional indices in Peter Bala's conjecture. -/
def excluded (p n : ℕ) : Prop :=
  ∃ m k : ℕ, m ≤ (p - 1) / 9 ∧ 1 ≤ k ∧ k ≤ (p - 1) / 9 ∧ n = m * p + k

/-- Peter Bala's conjecture: if `p` is a prime congruent to `1` modulo `9`, then
`a(p*n)` is congruent to `a(n)` modulo `p^2` for every positive non-exceptional `n`. -/
theorem main :
    ∀ p n : ℕ, p.Prime → p ≡ 1 [MOD 9] → 0 < n → ¬ excluded p n →
      a (p * n) ≡ a n [MOD p ^ 2] := by
  sorry

end OMA.S_oeis_a298799
