import Mathlib

/-!
# Multiple roots of a five-term polynomial

Source: ABB, https://mathoverflow.net/questions/447544 (CC BY-SA 4.0).
Credit: @connoranderson

We state the universal simple-root alternative of the author's question.
A counterexample is precisely a root at which the formal derivative also vanishes.
-/

namespace OMA.S_mo_447544
open Polynomial

noncomputable def fiveTerm (p q r n : ℕ) : Polynomial ℂ :=
  1 + X^p + X^q + X^r - X^n

theorem main : ∀ p q r n : ℕ, 1 < p → p < q → q < r → r < n →
    ∀ z : ℂ, (fiveTerm p q r n).IsRoot z →
      ¬ (fiveTerm p q r n).derivative.IsRoot z := by
  sorry

end OMA.S_mo_447544
