import Mathlib

/-!
# A290472: Number of ways to write 6*n+1 as x^2 + 3*y^2 + 7*z^2, where x is a positive integer, and y and z are nonnegative integers.

Source: https://oeis.org/A290472
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 for all n = 0, 1, 2, ..., and a(n) = 1 only for n = 0, 1, 2, 4, 5, 9, 10, 12, 14, 16,
   17, 24, 30, 34, 66, 84, 86, 116, 124, 152, 286.
2. {6n+5: n = 0, 1, 2, ...} is a subset of {2x^2 + 3y^2 + 5z^2: x, y, z nonnegative integers with
   y > 0}.

Formalization notes:
* a(n) counts triples (x, y, z) with x ≥ 1, y, z ≥ 0 and x^2 + 3y^2 + 7z^2 = 6n + 1; each
  coordinate is at most 6n + 1, which bounds the count.
* "a(n) = 1 only for n in S" is stated as: a(n) = 1 iff n ∈ S.
* Controls (computed): for n < 6000, a(n) > 0 and a(n) = 1 exactly on S; claim 2 holds for
  n < 700.
-/

namespace OMA.S_oeis_a290472

/-- A290472(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (6 * n + 2) ×ˢ Finset.range (6 * n + 2) ×ˢ Finset.range (6 * n + 2)).filter
    fun t : ℕ × ℕ × ℕ => 0 < t.1 ∧ t.1 ^ 2 + 3 * t.2.1 ^ 2 + 7 * t.2.2 ^ 2 = 6 * n + 1).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 1, 2, 4, 5, 9, 10, 12, 14, 16, 17, 24, 30, 34, 66, 84, 86, 116,
        124, 152, 286} : Finset ℕ)) ∧
      ∀ n : ℕ, ∃ x y z : ℕ, 0 < y ∧ 2 * x ^ 2 + 3 * y ^ 2 + 5 * z ^ 2 = 6 * n + 5 := by
  sorry

end OMA.S_oeis_a290472
