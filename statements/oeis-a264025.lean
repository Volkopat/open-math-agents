import Mathlib

/-!
# A264025: Number of ways to write n as x^2 + y*(2*y+1) + z*(z+1)/2 where x, y and z are nonnegative integers with z or z+1 prime.

Source: https://oeis.org/A264025
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344.
(ii) Any positive integer n not equal to 8 can be written as x*(2*x+1) + y*(y+1)/2 + z*(z+1)/2,
where x, y and z are nonnegative integers with z or z+1 prime.
(iii) Any integer n > 1 can be written as x^2 + y*(y+1) + z*(z+1) (or 2*x^2 + y*(y+1)/2 + z*(z+1)),
where x, y and z are nonnegative integers with z or z+1 prime.

Formalization notes:
* a(n) counts triples (x, y, z) of naturals ≤ n. The "or" in (iii) is read as two separate claims,
  both stated.
* "a(n) = 1 only for n in S" is stated as: for n ≥ 1, a(n) = 1 iff n ∈ S.
* Controls (computed): for n < 1500 all parts hold (the only exception in (ii) is 8) and a(n) = 1
  exactly on S.
-/

namespace OMA.S_oeis_a264025

/-- `y` or `y + 1` is prime. -/
def PP (y : ℕ) : Prop := y.Prime ∨ (y + 1).Prime

instance : DecidablePred PP := fun y => by unfold PP; infer_instance

/-- A264025(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun t : ℕ × ℕ × ℕ => PP t.2.2 ∧
      t.1 ^ 2 + t.2.1 * (2 * t.2.1 + 1) + t.2.2 * (t.2.2 + 1) / 2 = n).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 ≤ n →
        (a n = 1 ↔ n ∈ ({1, 2, 3, 8, 9, 23, 30, 44, 48, 198, 219, 1344} : Finset ℕ))) ∧
      (∀ n : ℕ, 0 < n → n ≠ 8 → ∃ x y z : ℕ, PP z ∧
        x * (2 * x + 1) + y * (y + 1) / 2 + z * (z + 1) / 2 = n) ∧
      (∀ n : ℕ, 1 < n → ∃ x y z : ℕ, PP z ∧ x ^ 2 + y * (y + 1) + z * (z + 1) = n) ∧
      ∀ n : ℕ, 1 < n → ∃ x y z : ℕ, PP z ∧ 2 * x ^ 2 + y * (y + 1) / 2 + z * (z + 1) = n := by
  sorry

end OMA.S_oeis_a264025
