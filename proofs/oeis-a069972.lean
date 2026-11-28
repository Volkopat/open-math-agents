import OMAStatements.S_oeis_a069972
import Mathlib

/-!
# A069972: the Lambert series

d ∣ 2n and d + 1 ∣ 2n hold together exactly when d(d+1) ∣ 2n (d and d + 1 are coprime), i.e. when the
triangular number T(d) = d(d+1)/2 divides n. For n ≥ 1 such d satisfy d ≤ T(d) ≤ n, so the sum over
1 ≤ d ≤ 2n equals the sum over 1 ≤ d ≤ n, which is the coefficient of xⁿ in
Σ_d d·x^T(d)/(1 − x^T(d)).
-/

namespace PA069972
open Finset OMA.S_oeis_a069972

theorem tri_two (d : ℕ) : 2 * triangular d = d * (d + 1) := by
  unfold triangular
  have h : 2 ∣ d * (d + 1) := (Nat.even_mul_succ_self d).two_dvd
  omega

theorem cond_iff (n d : ℕ) : (d ∣ 2 * n ∧ d + 1 ∣ 2 * n) ↔ triangular d ∣ n := by
  have ht := tri_two d
  constructor
  · rintro ⟨h1, h2⟩
    have hcop : Nat.Coprime d (d + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right d)
    have h3 : d * (d + 1) ∣ 2 * n := hcop.mul_dvd_of_dvd_of_dvd h1 h2
    rw [← ht] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  · intro h
    have h3 : d * (d + 1) ∣ 2 * n := by rw [← ht]; exact Nat.mul_dvd_mul_left 2 h
    exact ⟨(Dvd.intro _ rfl).trans h3, (Dvd.intro_left _ rfl).trans h3⟩

end PA069972

theorem OMA.solution : type_of% @OMA.S_oeis_a069972.main := by
  ext n
  unfold OMA.S_oeis_a069972.lambert
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  unfold OMA.S_oeis_a069972.a
  simp only [PA069972.cond_iff]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  · intro d hd hdn
    simp only [Finset.mem_Icc] at hd hdn
    rw [if_neg]
    intro hdiv
    have h1 := Nat.le_of_dvd hn hdiv
    have h2 := PA069972.tri_two d
    have h3 : d ≤ OMA.S_oeis_a069972.triangular d := by nlinarith
    omega
