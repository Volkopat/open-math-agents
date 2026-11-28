import OMAStatements.S_oeis_a014201
import Mathlib

namespace OMA.R_oeis_a014201_R1

open Asymptotics Filter OMA.S_oeis_a014201

def H1 : Prop :=
  (fun n : ℕ => (a n : ℝ) - 2 * (Real.pi / Real.sqrt 3) * n) =O[atTop]
    fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 2)

def H2 : Prop := ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
  (fun n : ℕ => (a n : ℝ) - 2 * (Real.pi / Real.sqrt 3) * n) =O[atTop]
    fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 4 + ε)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a014201.main := by
  intro h₁ h₂ ε hε
  by_cases h : ε < 1 / 4
  · exact h₂ ε hε h
  · apply h₁.trans
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), one_mul]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

end OMA.R_oeis_a014201_R1
