import Mathlib

/-!
# OEIS A003401: reciprocal sum of constructible polygon orders

Source: https://oeis.org/A003401
`A003401` lists the `n ≥ 1` with `φ(n)` a power of `2` (the regular `n`-gon is constructible
for `n ≥ 3`): 1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 17, …. From the entry (Shevelev, Noe):
if the only Fermat primes are `F₀, …, F₄`, then
`∑_{n ≥ 1} 1/a(n) = 2 ∏_{k=0}^{4} (1 + 1/F_k) = 4869735552/1431655765`.
`main` states this implication.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a003401

/-- The Fermat number `F k = 2^(2^k) + 1`. -/
def F (k : ℕ) : ℕ := 2 ^ 2 ^ k + 1

/-- Membership in A003401: `n ≥ 1` and `φ n` is a power of `2`. -/
def InA003401 (n : ℕ) : Prop := 1 ≤ n ∧ ∃ j : ℕ, n.totient = 2 ^ j

theorem main :
    (∀ k : ℕ, 5 ≤ k → ¬ (F k).Prime) →
      HasSum (fun n : {n : ℕ // InA003401 n} => (1 : ℝ) / (n : ℕ))
        (2 * ∏ k ∈ Finset.range 5, (1 + 1 / (F k : ℝ))) ∧
      2 * ∏ k ∈ Finset.range 5, (1 + 1 / (F k : ℝ)) = 4869735552 / 1431655765 := by
  sorry

end OMA.S_oeis_a003401
