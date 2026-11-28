import Mathlib

/-!
# A primality test with Fibonacci polynomials

Source: https://math.stackexchange.com/questions/2730611
Credit: @jagraj28

Let `F_n(x)` be the Fibonacci polynomials: `F_0 = 0`, `F_1 = 1`, `F_{n+2} = x F_{n+1} + F_n`
(so `F_2 = x`, `F_3 = x² + 1`). The question asks for a proof or a counterexample of the claim:

  Let `n > 1`. Then `n` is prime if and only if `∑_{k=0}^{n-1} F_n(k) ≡ -1 (mod n)`.

The only answer proves the direction "`n` prime implies the congruence" (using power sums modulo
`p` and the leading coefficient `1` of `F_p`); the converse is open. A computation confirms the
equivalence for all `2 ≤ n < 1500`.

Conventions.
* `fibPoly n : ℤ[X]` is defined by the recursion above; `F_n(k)` is `(fibPoly n).eval k` with
  `k : ℤ`.
* The congruence is `Int.ModEq` modulo `n`.
-/

namespace OMA.S_mse_2730611

open Polynomial

/-- The Fibonacci polynomials: `F₀ = 0`, `F₁ = 1`, `F_{n+2} = X F_{n+1} + F_n`. -/
noncomputable def fibPoly : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | n + 2 => X * fibPoly (n + 1) + fibPoly n

/-- For `n > 1`: `n` is prime if and only if `∑_{k=0}^{n-1} F_n(k) ≡ -1 (mod n)`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n.Prime ↔ (∑ k ∈ Finset.range n, (fibPoly n).eval (k : ℤ)) ≡ -1 [ZMOD n]) := by
  sorry

end OMA.S_mse_2730611
