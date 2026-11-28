import OMAStatements.S_oeis_a276371
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Paul D. Hanna's sequence A276371 and Peter Bala's totient-period conjecture.
We construct its integral coefficients using the binomial recurrence listed
by Seiichi Manyama, verify the defining series identity, and show that its
residues modulo four repeat 1,1,3,3.
-/

open PowerSeries Finset
open OMA.S_oeis_a276371

namespace OMA.PeriodFour

private def a : ℕ → ℤ
  | 0 => 1
  | n + 1 => a n + ∑ i : Fin n, 2^(n-i.val) * (n.choose i.val : ℤ) * a (i.val+1)
termination_by n => n
decreasing_by all_goals omega

private theorem recurrence (n : ℕ) : a (n+1) =
    a n + ∑ i ∈ range n, 2^(n-i) * (n.choose i : ℤ) * a (i+1) := by
  rw [a]
  congr 1
  exact Fin.sum_univ_eq_sum_range (fun i => (2:ℤ)^(n-i) * (n.choose i : ℤ) * a (i+1)) n

private noncomputable def egf (b : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (b n : ℚ) / n.factorial

private theorem egf_coeff (b : ℕ → ℤ) (n : ℕ) :
    coeff n (egf b) = (b n : ℚ) / n.factorial := coeff_mk _ _

private theorem egf_derivative (b : ℕ → ℤ) :
    derivative ℚ (egf b) = egf (fun n => b (n+1)) := by
  ext n
  rw [coeff_derivative, egf_coeff, egf_coeff, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add_one]
  have hn : (n:ℚ)+1 ≠ 0 := by positivity
  field_simp

private theorem product_coeff (b c : ℕ → ℤ) (n : ℕ) :
    coeff n (egf b * egf c) =
      (∑ i ∈ range (n+1), (b i : ℚ) * (c (n-i) : ℚ) * (n.choose i : ℚ)) / n.factorial := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hl : i ≤ n := by simpa using hi
  rw [egf_coeff, egf_coeff, Nat.cast_choose ℚ hl]
  have hn : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

private theorem exp_model : exp2 = egf (fun n => (2 : ℤ)^n) := by
  ext n
  simp [exp2, egf]

private theorem exp_diff : derivative ℚ exp2 = 2 * exp2 := by
  rw [exp_model, egf_derivative, two_mul]
  ext n
  simp [egf_coeff, pow_succ, add_div, mul_two]

private theorem linear_ode : derivative ℚ (egf a) * (2 - exp2) = egf a := by
  rw [mul_sub, mul_two, sub_eq_iff_eq_add, egf_derivative, exp_model]
  ext n
  simp only [map_add, egf_coeff, product_coeff, Int.cast_pow, Int.cast_ofNat]
  rw [sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  have h := congrArg (fun z : ℤ => (z : ℚ)) (recurrence n)
  push_cast at h
  have hsum : (∑ i ∈ range n, (a (i+1) : ℚ) * 2^(n-i) * (n.choose i : ℚ)) =
      ∑ i ∈ range n, 2^(n-i) * (n.choose i : ℚ) * (a (i+1) : ℚ) := by
    apply sum_congr rfl
    intros
    ring
  rw [hsum]
  rw [← add_div, ← add_div]
  congr 1
  linarith

private theorem series_equation : (egf a)^4 * (2-exp2) = exp2 := by
  let F := (egf a)^4 * (2-exp2)
  have hD : derivative ℚ F = 2 * F := by
    dsimp only [F]
    rw [Derivation.leibniz, map_sub, PowerSeries.derivative_pow, exp_diff]
    have hz : derivative ℚ (2 : PowerSeries ℚ) = 0 := by
      rw [show (2 : PowerSeries ℚ) = 1+1 by norm_num, map_add, derivative_one, zero_add]
    rw [hz]
    simp only [Nat.reduceSub, Nat.cast_ofNat, smul_eq_mul]
    linear_combination (4 * (egf a)^3) * linear_ode
  change F = exp2
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
    have ha : constantCoeff (egf a) = 1 := by simp [← coeff_zero_eq_constantCoeff_apply, egf_coeff, a]
    have he : constantCoeff exp2 = 1 := by rw [exp_model, ← coeff_zero_eq_constantCoeff_apply, egf_coeff]; norm_num
    simp [F, ha, he, show (2 : PowerSeries ℚ) = 1+1 by norm_num]
  | succ n ih =>
    have h := congrArg (coeff n) hD
    have he := congrArg (coeff n) exp_diff
    rw [coeff_derivative, two_mul, map_add, ih] at h
    rw [coeff_derivative, two_mul, map_add] at he
    exact mul_right_cancel₀ (by positivity : (n:ℚ)+1 ≠ 0) (h.trans he.symm)

private theorem step_mod (n : ℕ) :
    (a (n+1) : ZMod 4) = (1 + 2 * (n : ZMod 4)) * (a n : ZMod 4) := by
  cases n with
  | zero => rw [recurrence 0]; simp
  | succ n =>
    rw [recurrence (n+1), sum_range_succ, Nat.choose_succ_self_right]
    push_cast
    have z : (∑ i ∈ range n, (2 : ZMod 4)^(n+1-i) * ((n+1).choose i : ZMod 4) * (a (i+1) : ZMod 4)) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hi' : i < n := mem_range.mp hi
      rw [show n+1-i = 2+(n-1-i) by omega, pow_add, show (2:ZMod 4)^2 = 0 by decide]
      simp
    rw [z]
    simp only [show n+1-n = 1 by omega, pow_one, zero_add]
    ring

private theorem flip (n : ℕ) : (a (n+2) : ZMod 4) = 3 * (a n : ZMod 4) := by
  rw [step_mod (n+1), step_mod n, Nat.cast_add_one, ← mul_assoc]
  congr 1
  have hf : (4:ZMod 4) = 0 := by decide
  linear_combination ((n : ZMod 4)^2 + 2*(n : ZMod 4)) * hf

private theorem blocks (j : ℕ) : (a (4*j) : ZMod 4) = 1 ∧ (a (4*j+2) : ZMod 4) = 3 := by
  have first : (a (4*j) : ZMod 4) = 1 := by
    induction j with
    | zero => simp [a]
    | succ j ih =>
      rw [show 4*(j+1) = 4*j+2+2 by omega, flip, flip, ih]
      decide
  exact ⟨first, by rw [flip, first, mul_one]⟩

end OMA.PeriodFour

open OMA.PeriodFour in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a276371.main) := by
  intro claim
  have h0 : constantCoeff (egf a) = 1 := by simp [← coeff_zero_eq_constantCoeff_apply, egf_coeff, a]
  obtain ⟨N,p,hp,hd,ht⟩ := claim (egf a) a h0 series_equation (egf_coeff a) 4 (by decide)
  have ht' (n : ℕ) (hn : N ≤ n) : (a (n+p) : ZMod 4) = (a n : ZMod 4) :=
    (ZMod.intCast_eq_intCast_iff _ _ 4).2 (ht n hn)
  have htwo : Nat.totient 4 = 2 := by decide
  rw [htwo] at hd
  have ple : p ≤ 2 := Nat.le_of_dvd (by decide) hd
  have eq : (a (4*N+2) : ZMod 4) = (a (4*N) : ZMod 4) := by
    rcases (show p=1 ∨ p=2 by omega) with rfl | rfl
    · exact (ht' (4*N+1) (by omega)).trans (ht' (4*N) (by omega))
    · exact ht' (4*N) (by omega)
  rw [(blocks N).1, (blocks N).2] at eq
  exact (by decide : (3 : ZMod 4) ≠ 1) eq
