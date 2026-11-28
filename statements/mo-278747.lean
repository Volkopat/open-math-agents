import Mathlib

/-!
# Computability of the represented integers

Source https://mathoverflow.net/questions/278747/is-the-set-of-integers-of-the-form-a-bcb-acc-ab-computable

The question asks whether membership in the set of positive integers
represented by a/(b+c) + b/(a+c) + c/(a+b) is computable when the three
variables range over positive integers.
-/

namespace OMA.S_mo_278747

def HasRepresentation (n : ℕ) : Prop :=
  0 < n ∧ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (a : ℚ) / ((b : ℚ) + c) + (b : ℚ) / ((a : ℚ) + c) +
      (c : ℚ) / ((a : ℚ) + b) = (n : ℚ)

theorem main :
    ComputablePred HasRepresentation := by
  sorry

end OMA.S_mo_278747
