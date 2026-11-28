import OMAStatements.S_oeis_a035337
import Mathlib

-- Problem: A035337: Third column of Wythoff array.
-- Upstream: formal-conjectures statements/oeis-a035337.lean:0 (declaration OMA.S_oeis_a035337.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write A = floor(n phi). Since phi^2 = phi + 1, floor(n phi^2) = A + n and
floor(A phi^2) = floor(A phi) + A. The key fact is floor(A phi) = A + n - 1: from
n phi - 1 < A < n phi (strict because phi is irrational) and phi (phi - 1) = 1 we get
n - 1 < A (phi - 1) < n. Both sides of Layman's formula then equal 3 A + 2 n - 2. -/

namespace A035337Aux

open Real OMA.S_oeis_a035337

theorem key (n : ℕ) (hn : 1 ≤ n) :
    ⌊((⌊(n : ℝ) * goldenRatio⌋ : ℤ) : ℝ) * goldenRatio⌋ = ⌊(n : ℝ) * goldenRatio⌋ + (n : ℤ) - 1 := by
  set A : ℤ := ⌊(n : ℝ) * goldenRatio⌋ with hA
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have h1 : (1 : ℝ) < goldenRatio := one_lt_goldenRatio
  have h2 : goldenRatio < 2 := goldenRatio_lt_two
  have hle : (A : ℝ) ≤ (n : ℝ) * goldenRatio := Int.floor_le _
  have hlt : (n : ℝ) * goldenRatio < (A : ℝ) + 1 := Int.lt_floor_add_one _
  have hirr : Irrational ((n : ℝ) * goldenRatio) :=
    goldenRatio_irrational.natCast_mul (by omega)
  have hne : (n : ℝ) * goldenRatio ≠ (A : ℝ) := hirr.ne_int A
  have hlt' : (A : ℝ) < (n : ℝ) * goldenRatio := lt_of_le_of_ne hle (Ne.symm hne)
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · nlinarith
  · nlinarith

theorem formula (n : ℕ) (hn : 1 ≤ n) : a n = 3 * AA n - (n : ℤ) + 1 := by
  have hsq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hk := key n hn
  unfold a col1 col2 AA
  have e1 : (n : ℝ) * goldenRatio ^ 2 = (n : ℝ) * goldenRatio + (n : ℝ) := by
    rw [hsq]
    ring
  have e2 : ((⌊(n : ℝ) * goldenRatio⌋ : ℤ) : ℝ) * goldenRatio ^ 2 =
      ((⌊(n : ℝ) * goldenRatio⌋ : ℤ) : ℝ) * goldenRatio + ((⌊(n : ℝ) * goldenRatio⌋ : ℤ) : ℝ) := by
    rw [hsq]
    ring
  rw [e1, e2, Int.floor_add_natCast, Int.floor_add_intCast, hk]
  ring

end A035337Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a035337.main :=
  A035337Aux.formula
