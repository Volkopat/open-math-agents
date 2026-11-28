import Mathlib

/-!
# A283366: Number of ways to write 2*n + 1 as x^2 + y^2 + 2*z^2 with x,y,z integers such that 2*x + y + z is a square or a power of two.

Source: https://oeis.org/A283366
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n = 0, 1, 2, ..., and a(n) = 1 only for
n = 19, 32, 47, 115, 200, 974, 1271, 2240, 2549, 3185, 4865, 9254, 15881.

Formalization notes:
* a(n) counts integer triples (x, y, z) (signs and order counted); every coordinate has |.| ≤ 2n + 1.
  "A square" is s^2 (0 included) and "a power of two" 2^j with j ≥ 0.
* "a(n) = 1 only for n in S" is stated as: a(n) = 1 iff n ∈ S.
* Controls (computed): a(0..9) = 2, 4, 3, 5, 4, 2, 7, 5, 5, 6, as in the entry; for n < 2000, a(n) > 0 and
  a(n) = 1 exactly at 19, 32, 47, 115, 200, 974, 1271.
-/

namespace OMA.S_oeis_a283366

open Classical in
/-- A283366(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  let B := 2 * n + 1
  ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter fun t : ℤ × ℤ × ℤ =>
    t.1 ^ 2 + t.2.1 ^ 2 + 2 * t.2.2 ^ 2 = 2 * n + 1 ∧
      (IsSquare (2 * t.1 + t.2.1 + t.2.2) ∨ ∃ j : ℕ, 2 * t.1 + t.2.1 + t.2.2 = 2 ^ j)).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      ∀ n : ℕ, a n = 1 ↔ n ∈ ({19, 32, 47, 115, 200, 974, 1271, 2240, 2549, 3185, 4865, 9254, 15881} :
        Finset ℕ) := by
  sorry

end OMA.S_oeis_a283366
