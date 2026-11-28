import FormalConjectures.ErdosProblems.«422»

/-! The positivity condition at index `n + 1` gives the bound at index `n`. -/

open Filter

noncomputable def OMA.answer : ℕ+ → ℝ := fun n => n

theorem OMA.solution : Erdos422.erdos_422.variants.growth_rate.answer = OMA.answer →
    type_of% @Erdos422.erdos_422.variants.growth_rate := by
  intro h f hf
  rw [h]
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (2 : ℕ+)] with n hn
  have hn' : (2 : ℕ+) < n + 1 := Nat.lt_succ_of_le hn
  have hlt := (hf.2.2 (n + 1) hn').1
  rw [PNat.add_sub] at hlt
  have hle : (f n : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt_succ hlt
  simpa [OMA.answer, Real.norm_eq_abs] using hle
