import Mathlib

/-!
# A299537: Number of ways to write n^2 as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and z <= w such that x or y is a power of 4 (including 4^0 = 1) and x + 3*y is also a power of 4.

Source: https://oeis.org/A299537
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry; verified for n up to 10^7):
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 4^k*m with k = 0, 1, 2, ... and
m = 1, 2, 3, 5, 7, 11, 15, 19, 43, 47, 135, 1103.
(ii) For any integer n > 1, we can write n^2 as x^2 + y^2 + z^2 + w^2 with x, y, z, w nonnegative
integers such that 2*x or 2*y is a power of 4 and 2*(x+3*y) is also a power of 4.

Formalization notes:
* Powers of 4 are 4^j with j ≥ 0. a(n) counts quadruples with all entries ≤ n (as they must be).
* "a(n) = 1 only for n = 4^k m" is stated as: for n > 0, a(n) = 1 iff n = 4^k m for such k, m.
* Controls (computed): for 1 ≤ n < 150, a(n) > 0, a(n) = 1 exactly on the stated family, and (ii)
  holds.
-/

namespace OMA.S_oeis_a299537

/-- `v` is a power of 4. -/
def IsPow4 (v : ℕ) : Prop := ∃ j : ℕ, v = 4 ^ j

open Classical in
/-- A299537(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun t : ℕ × ℕ × ℕ × ℕ => t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2 = n ^ 2 ∧
      t.2.2.1 ≤ t.2.2.2 ∧ (IsPow4 t.1 ∨ IsPow4 t.2.1) ∧ IsPow4 (t.1 + 3 * t.2.1)).card

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      (∀ n : ℕ, 0 < n → (a n = 1 ↔ ∃ k : ℕ, ∃ m ∈ ({1, 2, 3, 5, 7, 11, 15, 19, 43, 47, 135, 1103} :
        Finset ℕ), n = 4 ^ k * m)) ∧
      ∀ n : ℕ, 1 < n → ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ^ 2 ∧
        (IsPow4 (2 * x) ∨ IsPow4 (2 * y)) ∧ IsPow4 (2 * (x + 3 * y)) := by
  sorry

end OMA.S_oeis_a299537
