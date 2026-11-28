import Mathlib

/-!
# A264010: Number of ways to write n as x^2 + y*(y+1) + z*(z+1)/2, where x, y and z are nonnegative integers such that y or y+1 is prime, and z or z+1 is prime.

Source: https://oeis.org/A264010
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 2, and a(n) = 1 only for n = 3, 4, 5, 6, 10, 11, 15, 20, 29, 1125.
(ii) Any integer n > 2 can be written as x*(x+1) + y*(y+1)/2 + z*(z+1)/2, where x, y and z are
nonnegative integers such that x or x+1 is prime, and y or y+1 is prime.
(iii) Any integer n > 7 can be written as x*(x+1) + y*(y+1)/2 + 3*z*(z+1)/2, where x, y and z are
nonnegative integers such that y or y+1 is prime, and z or z+1 is prime.

Formalization notes:
* a(n) counts triples (x, y, z) of naturals ≤ n (each coordinate is at most n in a representation).
* "a(n) = 1 only for n in S" is stated as: for n ≥ 1, a(n) = 1 iff n ∈ S.
* Controls (computed): for n < 1500 all three parts hold and a(n) = 1 exactly on S.
-/

namespace OMA.S_oeis_a264010

/-- `y` or `y + 1` is prime. -/
def PP (y : ℕ) : Prop := y.Prime ∨ (y + 1).Prime

instance : DecidablePred PP := fun y => by unfold PP; infer_instance

/-- A264010(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    fun t : ℕ × ℕ × ℕ => PP t.2.1 ∧ PP t.2.2 ∧
      t.1 ^ 2 + t.2.1 * (t.2.1 + 1) + t.2.2 * (t.2.2 + 1) / 2 = n).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 2 < n → 0 < a n) ∧
      (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ({3, 4, 5, 6, 10, 11, 15, 20, 29, 1125} : Finset ℕ))) ∧
      (∀ n : ℕ, 2 < n → ∃ x y z : ℕ, PP x ∧ PP y ∧
        x * (x + 1) + y * (y + 1) / 2 + z * (z + 1) / 2 = n) ∧
      ∀ n : ℕ, 7 < n → ∃ x y z : ℕ, PP y ∧ PP z ∧
        x * (x + 1) + y * (y + 1) / 2 + 3 * (z * (z + 1) / 2) = n := by
  sorry

end OMA.S_oeis_a264010
