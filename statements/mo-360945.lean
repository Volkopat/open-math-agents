import Mathlib

/-!
# A reducible quadratic along a linear recurrence in `F_{2^m}`

Source: https://mathoverflow.net/questions/360945
Asked by MathOverflow user Alexey (Reducible polynomial among sequence of polynomials).

Let `a_1, a_2` be elements of the finite field `F_{2^m}` with `a_1^2 ≠ a_2`, and define
`a_{k+2} = a_1 a_{k+1} + a_k`. The question asks whether there is always an element `a` of
`{a_1, a_2, ..., a_{2^m}}` such that the polynomial `x^2 + a x + 1` is reducible over
`F_{2^m}`.

Translation choices.
* `F_{2^m}` is any field `K` with `2^m` elements (`m ≥ 1`); all such fields are isomorphic.
* The sequence is `seq a₁ a₂ k = a_{k+1}`, indexed from `0`, so `a_1, ..., a_{2^m}` are
  `seq a₁ a₂ k` for `k < 2^m`.
* Reducibility of `x^2 + a x + 1` over `K` is `¬ Irreducible (X^2 + C a * X + 1)` in `K[X]`.
-/

namespace OMA.S_mo_360945

open Polynomial

/-- The sequence `a_{k+1}` with `a_{k+2} = a_1 a_{k+1} + a_k`. -/
def seq {K : Type} [Field K] (a₁ a₂ : K) : ℕ → K
  | 0 => a₁
  | 1 => a₂
  | k + 2 => a₁ * seq a₁ a₂ (k + 1) + seq a₁ a₂ k

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ m →
      ∀ a₁ a₂ : K, a₁ ^ 2 ≠ a₂ →
        ∃ k < 2 ^ m, ¬ Irreducible (X ^ 2 + C (seq a₁ a₂ k) * X + 1 : K[X]) := by
  sorry

end OMA.S_mo_360945
