import Mathlib.NumberTheory.Bernoulli

namespace OMA.S_oeis_a326579

/-- Carmichael numbers: composite integers `n ≥ 2` satisfying `a^n ≡ a (mod n)` for all `a : ℕ`. -/
def IsCarmichael (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n]

/-- Korselt numbers: integers `n > 1` that are squarefree and satisfy `(p - 1) ∣ (n - 1)` for every
prime factor `p` of `n`. -/
def IsKorselt (n : ℕ) : Prop :=
  1 < n ∧ Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- Conjecture (OEIS A326579): for every `n > 1`,
`denominator(B_{n-1}) = n * denominator(n * B_{n-1}) ↔ IsKorselt n ↔ n.Prime ∨ IsCarmichael n`. -/
theorem main :
    ∀ n : ℕ, 1 < n →
      (((bernoulli (n - 1)).den = n * ((n : ℚ) * bernoulli (n - 1)).den ↔ IsKorselt n) ∧
       (IsKorselt n ↔ n.Prime ∨ IsCarmichael n)) := by
  sorry

end OMA.S_oeis_a326579
