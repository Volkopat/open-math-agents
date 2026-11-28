import Mathlib

/-!
# A new n-conjecture

Source: https://mathoverflow.net/questions/365019
For `P > 1` with prime factorisation `∏ pᵢ^aᵢ` let `h(P) = min aᵢ`, and `h(1) = +∞`.
Conjecture (asker): if `P₁, …, Pₙ` are pairwise coprime positive integers, then
`min {h(P₁), …, h(Pₙ), h(P₁ + ⋯ + Pₙ)} ≤ n + 1`.

Conventions. `h` takes values in `ℕ∞`; `h P` is the minimum of the exponents
`P.factorization p` over the prime factors `p` of `P` (`⊤` for `P = 1`). `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_365019

/-- `h(P) = min` of the exponents in the factorisation of `P`, `⊤` for `P = 1`. -/
noncomputable def h (P : ℕ) : ℕ∞ := ⨅ p ∈ P.primeFactors, (P.factorization p : ℕ∞)

theorem main :
    ∀ (n : ℕ) (P : Fin n → ℕ), 1 ≤ n → (∀ i, 0 < P i) →
      Pairwise (fun i j => Nat.Coprime (P i) (P j)) →
      min (⨅ i, h (P i)) (h (∑ i, P i)) ≤ (n + 1 : ℕ) := by
  sorry

end OMA.S_mo_365019
