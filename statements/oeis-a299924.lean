import Mathlib

/-!
# A299924: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that x + 2*y + 3*z is a power of 4 (including 4^0 = 1).

Source: https://oeis.org/A299924
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry), part (i): a(n) > 0 for all n > 0, and a(n) = 1 only for
n = 3, 7, 13, 49, 61, 4^k*m (k = 0, 1, 2, ... and m = 1, 2, 11, 14, 17). (Part (ii) of the entry, a
classification of all coefficient tuples (a, b, c, d) with this property, is not stated here.)

Formalization notes:
* Powers of 4 are 4^j with j ≥ 0. a(n) counts quadruples with entries ≤ n.
* "a(n) = 1 only for ..." is stated as an equivalence for n > 0.
* Controls (computed): for 1 ≤ n < 130, a(n) > 0 and a(n) = 1 exactly on the stated set.
-/

namespace OMA.S_oeis_a299924

/-- `v` is a power of 4. -/
def IsPow4 (v : ℕ) : Prop := ∃ j : ℕ, v = 4 ^ j

open Classical in
/-- A299924(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun t : ℕ × ℕ × ℕ × ℕ => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = n ^ 2 ∧
      IsPow4 (t.1 + 2 * t.2.1 + 3 * t.2.2.1)).card

/-- Part (i) of the conjecture. -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      ∀ n : ℕ, 0 < n → (a n = 1 ↔ n ∈ ({3, 7, 13, 49, 61} : Finset ℕ) ∨
        ∃ k : ℕ, ∃ m ∈ ({1, 2, 11, 14, 17} : Finset ℕ), n = 4 ^ k * m) := by
  sorry

end OMA.S_oeis_a299924
