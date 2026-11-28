import Mathlib

/-!
# A283299: Number of ways to write 2*n + 1 as x^2 + 2*y^2 + 3*z^2 with x,y,z integers such that x + y + z is a square or twice a square.

Source: https://oeis.org/A283299
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n = 0, 1, 2, ..., and a(n) = 1 only for n = 0, 3, 6, 8, 17, 23, 41, 128, 197, 372, 764,
1143, 1893, 3761, 4307, 6408, 6918.
(ii) Any positive odd integer can be written as x^2 + y^2 + 2*z^2 with x, y, z integers such that
x + 2*y + 3*z is a square or twice a square.

Formalization notes:
* a(n) counts integer triples (x, y, z) (signs and order counted); every coordinate has |.| ≤ 2n + 1.
  "A square or twice a square" means s^2 or 2 s^2 for an integer s (0 included).
* "a(n) = 1 only for n in S" is stated as: a(n) = 1 iff n ∈ S.
* Controls (computed): for n < 2000, a(n) > 0, a(n) = 1 exactly at the listed n below 2000, and (ii)
  holds for 2n + 1 < 4000.
-/

namespace OMA.S_oeis_a283299

/-- `v` is a square or twice a square. -/
def SqOrTwice (v : ℤ) : Prop := ∃ s : ℤ, v = s ^ 2 ∨ v = 2 * s ^ 2

open Classical in
/-- A283299(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  let B := 2 * n + 1
  ((Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B ×ˢ Finset.Icc (-(B : ℤ)) B).filter fun t : ℤ × ℤ × ℤ =>
    t.1 ^ 2 + 2 * t.2.1 ^ 2 + 3 * t.2.2 ^ 2 = 2 * n + 1 ∧ SqOrTwice (t.1 + t.2.1 + t.2.2)).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < a n) ∧
      (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 3, 6, 8, 17, 23, 41, 128, 197, 372, 764, 1143, 1893, 3761, 4307, 6408,
        6918} : Finset ℕ)) ∧
      ∀ n : ℕ, Odd n → ∃ x y z : ℤ, x ^ 2 + y ^ 2 + 2 * z ^ 2 = n ∧ SqOrTwice (x + 2 * y + 3 * z) := by
  sorry

end OMA.S_oeis_a283299
