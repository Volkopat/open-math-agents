import Mathlib

/-!
# Higher powers in the symmetric Heron expression

Source: Michael Hardy, https://mathoverflow.net/questions/468166 (CC BY-SA 4.0).
Credit: @connoranderson

The mixed terms are taken once per unordered pair. After expanding the
square of the sum, the positive-diagonal convention is twice the sum of
squares minus the square of the sum. The Boolean permits either global sign.
There are 4+m variables, covering every larger set in the question.
-/

namespace OMA.S_mo_468166
open MvPolynomial

noncomputable def form (d n : ℕ) : MvPolynomial (Fin d) ℂ :=
  2 * (∑ i : Fin d, X i ^ (2*n)) - (∑ i : Fin d, X i ^ n)^2

theorem main : ∀ (m n : ℕ), 0<n → ∀ s : Bool,
    ¬ ∃ l : List (MvPolynomial (Fin (4+m)) ℂ), (∀ g ∈ l, g.totalDegree=1) ∧
      l.prod = (if s then -form (4+m) n else form (4+m) n) := by
  sorry

end OMA.S_mo_468166
