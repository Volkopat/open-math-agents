import OMAStatements.S_oeis_a025191
import Mathlib

open OMA.S_oeis_a025191

namespace P025191

open Polynomial Finset

noncomputable abbrev P : ℚ[X] := 1 + X + X ^ 2

theorem natDeg_P : P.natDegree ≤ 2 := by
  unfold P; compute_degree

theorem natDeg_Pn (n : ℕ) : (P ^ n).natDegree ≤ 2 * n := by
  calc (P ^ n).natDegree ≤ n * P.natDegree := natDegree_pow_le
    _ ≤ n * 2 := Nat.mul_le_mul_left _ natDeg_P
    _ = 2 * n := by ring

theorem reflect_P : reflect 2 P = P := by
  ext i
  rw [coeff_reflect]
  by_cases hi : i ≤ 2
  · rw [revAt_le hi]
    interval_cases i <;> simp [P, coeff_X, coeff_one]
  · rw [revAt_eq_self_of_lt (by omega)]

theorem reflect_Pn (n : ℕ) : reflect (2 * n) (P ^ n) = P ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', show 2 * (n + 1) = 2 + 2 * n by ring,
      reflect_mul _ _ natDeg_P (natDeg_Pn n), reflect_P, ih]

theorem sym (n k : ℕ) (hk : k ≤ 2 * n) : t n k = t n (2 * n - k) := by
  unfold t
  conv_lhs => rw [← reflect_Pn n]
  rw [coeff_reflect, revAt_le hk]

theorem total (n : ℕ) : ∑ k ∈ range (2 * n + 1), t n k = 3 ^ n := by
  have h := eval_eq_sum_range' (p := P ^ n) (n := 2 * n + 1) (by have := natDeg_Pn n; omega) 1
  simp only [one_pow, mul_one, eval_pow, P, eval_add, eval_one, eval_X] at h
  norm_num at h
  simpa [t] using h.symm

theorem two_A (n : ℕ) : 2 * A027914 n = 3 ^ n + t n n := by
  have h := total n
  rw [show 2 * n + 1 = (n + 1) + n by ring, sum_range_add] at h
  have h2 : ∑ x ∈ range n, t n (n + 1 + x) = ∑ x ∈ range n, t n x := by
    rw [← sum_range_reflect (fun x => t n x) n]
    refine sum_congr rfl fun x hx => ?_
    rw [mem_range] at hx
    rw [sym n (n + 1 + x) (by omega)]
    congr 1
    omega
  rw [h2] at h
  have h3 : A027914 n = ∑ x ∈ range n, t n x + t n n := by
    rw [A027914, sum_range_succ]
  rw [A027914]
  rw [A027914] at h3
  linear_combination h + h3

/-- the central sum -/
noncomputable def cs (n : ℕ) : ℚ :=
  ∑ j ∈ range (n + 1), (n.choose j : ℚ) * (if 2 ∣ j then (j.choose (j / 2) : ℚ) else 0)

theorem coeff_sq_pow (k : ℕ) :
    ((1 + X ^ 2 : ℚ[X]) ^ k).coeff k = if 2 ∣ k then (k.choose (k / 2) : ℚ) else 0 := by
  have : (1 + X ^ 2 : ℚ[X]) ^ k = expand ℚ 2 ((1 + X) ^ k) := by
    simp [expand_X]
  rw [this, coeff_expand two_pos, coeff_one_add_X_pow]

theorem central (n : ℕ) : t n n = cs n := by
  unfold t cs
  rw [show (1 + X + X ^ 2 : ℚ[X]) = X + (1 + X ^ 2) by ring, add_pow, finsetSum_coeff]
  rw [← sum_range_reflect _ (n + 1)]
  refine sum_congr rfl fun j hj => ?_
  rw [mem_range] at hj
  rw [show n + 1 - 1 - j = n - j by omega, mul_comm, ← Polynomial.C_eq_natCast, coeff_C_mul,
    coeff_X_pow_mul', if_pos (by omega), show n - (n - j) = j by omega, coeff_sq_pow,
    Nat.choose_symm (by omega)]

theorem egf_coeff (n : ℕ) : A081673 n = 3 ^ n - 1 + cs n := by
  set B : PowerSeries ℚ := PowerSeries.mk fun n => if Even n then 1 / ((n / 2).factorial : ℚ) ^ 2
    else 0 with hB
  have e1 : egf = PowerSeries.mk (fun n => (3 : ℚ) ^ n / n.factorial) - PowerSeries.exp ℚ +
      B * PowerSeries.exp ℚ := by
    unfold egf; ring
  unfold A081673 cs
  rw [e1, map_add, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_exp, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [hB, PowerSeries.coeff_mk, PowerSeries.coeff_exp]
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  simp only [eq_ratCast, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [mul_add, mul_sub, mul_div_cancel₀ _ hf, mul_one_div_cancel hf, Finset.mul_sum]
  have key : ∀ j ∈ range (n + 1), (n.factorial : ℚ) * ((if Even j then 1 / ((j / 2).factorial : ℚ) ^ 2
      else 0) * (1 / ((n - j).factorial : ℚ))) =
      (n.choose j : ℚ) * (if 2 ∣ j then (j.choose (j / 2) : ℚ) else 0) := by
    intro j hj
    rw [mem_range] at hj
    by_cases he : 2 ∣ j
    · obtain ⟨h, rfl⟩ := he
      rw [if_pos (even_two_mul h), if_pos (dvd_mul_right 2 h), Nat.mul_div_cancel_left _ two_pos]
      have e1 := Nat.choose_mul_factorial_mul_factorial (show 2 * h ≤ n by omega)
      have e2 := Nat.choose_mul_factorial_mul_factorial (show h ≤ 2 * h by omega)
      rw [show 2 * h - h = h by omega] at e2
      have e1' : (n.choose (2 * h) : ℚ) * (2 * h).factorial * (n - 2 * h).factorial = n.factorial := by
        exact_mod_cast e1
      have e2' : ((2 * h).choose h : ℚ) * h.factorial * h.factorial = (2 * h).factorial := by
        exact_mod_cast e2
      have hh : (h.factorial : ℚ) ≠ 0 := by positivity
      have hn : ((n - 2 * h).factorial : ℚ) ≠ 0 := by positivity
      rw [← e1', ← e2']
      field_simp
    · rw [if_neg he, if_neg (by rwa [even_iff_two_dvd])]
      simp
  rw [Finset.sum_congr rfl key]

theorem part1 (m : ℕ) : a (m + 1) = A027914 (m + 1) - A027914 m := by
  unfold a A027914 T
  rw [Finset.sum_sub_distrib, Finset.sum_range_succ' (fun k => if 1 ≤ m + 1 ∧ 1 ≤ k then t (m + 1 - 1) (k - 1) else 0)]
  simp

end P025191

theorem OMA.solution : type_of% @OMA.S_oeis_a025191.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  refine ⟨P025191.part1 m, ?_⟩
  rw [P025191.part1, P025191.egf_coeff, P025191.egf_coeff, ← P025191.central, ← P025191.central]
  have h1 := P025191.two_A (m + 1)
  have h2 := P025191.two_A m
  linear_combination h1 / 2 - h2 / 2
