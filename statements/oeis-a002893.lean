import Mathlib

/-!
# A002893: a(n) = Sum_{k=0..n} binomial(n,k)^2 * binomial(2*k,k).

Source: https://oeis.org/A002893
Credit: @mattdorman

The source states (a conjecture of Zhi-Wei Sun): for each `n = 1, 2, 3, …` the polynomial
`g_n(x) = ∑_{k=0}^{n} binomial(n, k)² binomial(2k, k) x^k` is irreducible over the field of
rational numbers.

Reading used here: `g_n` is the polynomial in `ℚ[X]` with those coefficients, and irreducibility
is `Irreducible` in `ℚ[X]`.
-/

open Polynomial

namespace OMA.S_oeis_a002893

/-- Sun's polynomial `g_n(x) = ∑_{k=0}^{n} binomial(n, k)² binomial(2k, k) x^k`. -/
noncomputable def g (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (((n.choose k) ^ 2 * (2 * k).choose k : ℕ) : ℚ) * X ^ k

theorem main : ∀ n : ℕ, 1 ≤ n → Irreducible (g n) := by
  sorry

end OMA.S_oeis_a002893
