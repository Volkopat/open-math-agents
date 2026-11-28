import Mathlib

/-!
# Wright-type identities for higher powers

Source: https://mathoverflow.net/questions/451340
Asked by MathOverflow user Benjamin L. Warren.

In his paper An easier Waring's problem (1934), E. M. Wright presents the identities
`(x+4)^4 - 2(x+3)^4 + 2(x+1)^4 - x^4 = 48x + 96` and
`(x+3)^5 - 2(x+2)^5 + x^5 + (x-1)^5 - 2(x-3)^5 + (x-4)^5 = 720x - 360`,
which express a non-constant linear polynomial as an integer combination of `k`-th powers of
integer translates of `x`. The question asks whether such identities exist for higher powers
(and what they look like). This file formalizes the existence part: for every exponent
`k ≥ 1` there is such an identity.

Translation choices.
* An identity of this kind is a polynomial identity in `ℤ[X]` of the form
  `∑_i c_i (X + a_i)^k = A X + B` with integers `c_i, a_i, A, B` and `A ≠ 0`.
* The question of characterizing all such identities is not formalized here.
-/

namespace OMA.S_mo_451340

open Polynomial

theorem main :
    ∀ k : ℕ, 1 ≤ k → ∃ (m : ℕ) (c a : Fin m → ℤ) (A B : ℤ), A ≠ 0 ∧
      ∑ i, C (c i) * (X + C (a i)) ^ k = C A * X + C B := by
  sorry

end OMA.S_mo_451340
