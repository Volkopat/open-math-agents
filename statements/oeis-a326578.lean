import Mathlib.NumberTheory.Bernoulli

namespace OMA.S_oeis_a326578

/-- OEIS A326578: `a(n) = n^2 * denominator(n * B_{n-1}) / denominator(B_{n-1})`. -/
def A326578 (n : ℕ) : ℕ :=
  n ^ 2 * ((n : ℚ) * bernoulli (n - 1)).den / (bernoulli (n - 1)).den

/-- Carmichael numbers: composite integers `n ≥ 2` satisfying `a^n ≡ a (mod n)` for all `a : ℕ`. -/
def IsCarmichael (n : ℕ) : Prop :=
  2 ≤ n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a ^ n ≡ a [MOD n]

/-- Conjecture (OEIS A326578): if `n` is a Carmichael number, then `A326578(n) = n`. -/
theorem main : ∀ n : ℕ, IsCarmichael n → A326578 n = n := by
  sorry

end OMA.S_oeis_a326578
