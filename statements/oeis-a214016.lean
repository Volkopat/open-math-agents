import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# OEIS A214016

Marius Coman conjectures that infinitely many values of the given quadratic
at natural-number inputs are Poulet numbers, that is, composite numbers
satisfying the Fermat congruence to base two.
Source: https://oeis.org/A214016
-/

namespace OMA.S_oeis_a214016

def quadratic (n : ℕ) : ℕ := 7200 * n ^ 2 + 8820 * n + 2701

def IsPoulet (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ Nat.ModEq m (2 ^ (m - 1)) 1

theorem main : {m : ℕ | IsPoulet m ∧ ∃ n : ℕ, m = quadratic n}.Infinite := by
  sorry

end OMA.S_oeis_a214016
