import Mathlib

/-!
# A282289: Expansion of (Sum_{p prime, k>=2} x^(p^k))^4.

Source: https://oeis.org/A282289
Credit: @EmircanEsen

Conjecture (OEIS A282289): a(n) > 0 for all n > 27.

Formalization notes:
* The coefficient `a n` of `x^n` in `(∑_{p prime, k ≥ 2} x^(p^k))^4` counts the ordered
  quadruples `(q₁, q₂, q₃, q₄)` of prime powers `qᵢ = pᵢ^kᵢ` with `kᵢ ≥ 2` and
  `q₁ + q₂ + q₃ + q₄ = n` (example: `a 28 = 8`). Here `a n` is the number of such quadruples,
  as a function `Fin 4 → ℕ`. Every entry is at most `n`, so the set is finite and `Set.ncard`
  gives its size.
* `a n > 0` means that `n` is a sum of four prime powers with exponent at least `2`.
-/

namespace OMA.S_oeis_a282289

/-- `q = p^k` for a prime `p` and an exponent `k ≥ 2`. -/
def IsHigherPrimePower (q : ℕ) : Prop := ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ q = p ^ k

/-- A282289: the number of ordered quadruples of prime powers `p^k`, `k ≥ 2`, summing to `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {q : Fin 4 → ℕ | (∀ i, IsHigherPrimePower (q i)) ∧ ∑ i, q i = n}.ncard

/-- For every `n > 27`, `a n > 0`. -/
theorem main : ∀ n : ℕ, 27 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a282289
