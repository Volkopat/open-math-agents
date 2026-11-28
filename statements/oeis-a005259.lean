import Mathlib

/-!
# A005259: Apery (Apéry) numbers: Sum_{k=0..n} (binomial(n,k)*binomial(n+k,k))^2

Source: https://oeis.org/A005259
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A005259): For each n = 1, 2, 3, ... the Apéry
polynomial A_n(x) = Sum_{k=0..n} binomial(n,k)^2 * binomial(n+k,k)^2 * x^k is irreducible over the
field of rational numbers.

Conventions:
* A_n is a polynomial in `ℚ[X]`, and irreducible is Mathlib's `Irreducible` in `ℚ[X]`.
-/

namespace OMA.S_oeis_a005259

open Polynomial

/-- The Apéry polynomial `A_n(x) = Sum_{k=0..n} binomial(n,k)^2 * binomial(n+k,k)^2 * x^k`
over `ℚ`. -/
noncomputable def aperyPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((n.choose k : ℚ) ^ 2 * ((n + k).choose k : ℚ) ^ 2) * X ^ k

/-- Sun's conjecture on A005259: the Apéry polynomial `A_n` is irreducible over `ℚ` for every
`n >= 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Irreducible (aperyPoly n) := by
  sorry

end OMA.S_oeis_a005259
