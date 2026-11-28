import OMAStatements.S_oeis_a346508
import Mathlib

-- Problem: A346508: Positive integers k such that 10*k+1 is equal to the product of two integers greater than 1 and ending with 1 (A346507).
-- Upstream: formal-conjectures statements/oeis-a346508.lean:0 (declaration OMA.S_oeis_a346508.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Every k = 11 j + 1 with j >= 1 is a term, since 10 k + 1 = 11 (10 j + 1). So the set of terms
is infinite and consecutive terms differ by at most 11. With u(m) the m-th term (from 0),
u(m) >= m, hence 1 <= u(m+1)/u(m) <= 1 + 11/m, which tends to 1. -/

namespace A346508Aux

open OMA.S_oeis_a346508 Filter

theorem term_of_form (j : ℕ) (hj : 1 ≤ j) : IsTerm (11 * j + 1) := by
  refine ⟨by omega, 11, 10 * j + 1, by norm_num, by omega, by norm_num, by omega, by ring⟩

theorem infinite_terms : (Set.ofPred IsTerm).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun j : ℕ => 11 * (j + 1) + 1)
  · intro x y h
    simp only at h
    omega
  · intro j
    exact term_of_form (j + 1) (by omega)

theorem nth_pos (m : ℕ) : 0 < Nat.nth IsTerm m :=
  (Nat.nth_mem_of_infinite infinite_terms m).1

theorem gap (m : ℕ) : Nat.nth IsTerm (m + 1) ≤ Nat.nth IsTerm m + 11 := by
  have hpos := nth_pos m
  set t := Nat.nth IsTerm m with ht
  have hk : IsTerm (11 * ((t + 10) / 11) + 1) := term_of_form _ (by omega)
  have h1 : t < 11 * ((t + 10) / 11) + 1 := by omega
  have h2 : 11 * ((t + 10) / 11) + 1 ≤ t + 11 := by omega
  by_contra hcon
  have h3 : 11 * ((t + 10) / 11) + 1 < Nat.nth IsTerm (m + 1) := by omega
  have h4 := Nat.le_nth_of_lt_nth_succ h3 hk
  omega

theorem le_nth (m : ℕ) : m ≤ Nat.nth IsTerm m :=
  Nat.le_nth (fun hf => absurd hf infinite_terms)

theorem ratio_tendsto :
    Tendsto (fun m : ℕ => (Nat.nth IsTerm (m + 1) : ℝ) / (Nat.nth IsTerm m : ℝ)) atTop (nhds 1) := by
  have hup : Tendsto (fun m : ℕ => (1 : ℝ) + 11 / (m : ℝ)) atTop (nhds 1) := by
    have := (tendsto_const_div_atTop_nhds_zero_nat (11 : ℝ)).const_add (1 : ℝ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards with m
    have hpos : (0 : ℝ) < Nat.nth IsTerm m := by exact_mod_cast nth_pos m
    rw [le_div_iff₀ hpos, one_mul]
    exact_mod_cast (Nat.nth_strictMono infinite_terms).monotone (Nat.le_succ m)
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hpos : (0 : ℝ) < Nat.nth IsTerm m := by exact_mod_cast nth_pos m
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hg : (Nat.nth IsTerm (m + 1) : ℝ) ≤ Nat.nth IsTerm m + 11 := by exact_mod_cast gap m
    have hle : (m : ℝ) ≤ Nat.nth IsTerm m := by exact_mod_cast le_nth m
    rw [div_le_iff₀ hpos]
    have h5 : (11 : ℝ) / m * (Nat.nth IsTerm m : ℝ) ≥ 11 := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hm']
      nlinarith
    nlinarith

end A346508Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a346508.main := by
  have h := A346508Aux.ratio_tendsto.comp (Filter.tendsto_sub_atTop_nat 2)
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  simp only [Function.comp, OMA.S_oeis_a346508.a]
  have e1 : n - 2 + 1 = n - 1 := by omega
  have e2 : n - 1 - 1 = n - 2 := by omega
  rw [e1, e2]
