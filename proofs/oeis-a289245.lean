import OMAStatements.S_oeis_a289245
import Mathlib

open OMA.S_oeis_a289245 PowerSeries Finset

namespace ReciprocalGrowth

private lemma slopeBounds : 5 / 2 < slope ∧ slope < 8 / 3 := by
  unfold OMA.S_oeis_a289245.slope
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg 5
  constructor <;> nlinarith

private lemma weights : weight 0 = 1 ∧ weight 1 = 4 ∧ weight 2 = 6 := by
  have ⟨lo,hi⟩ := slopeBounds
  have h0 : ⌊slope⌋ = 2 := Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  have h1 : ⌊2*slope⌋ = 5 := Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  have h2 : ⌊3*slope⌋ = 7 := Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
  norm_num [weight, h0, h1, h2]

private lemma differences (n : ℕ) : 2 ≤ weight (n+1)-weight n ∧ weight (n+1)-weight n ≤ 3 := by
  let x := ((n : ℝ)+1)*slope
  have shift : (((n+1 : ℕ) : ℝ)+1)*slope = x+slope := by dsimp [x]; push_cast; ring
  have d : weight (n+1)-weight n = ⌊x+slope⌋ - ⌊x⌋ := by unfold weight; rw [shift]; dsimp [x]; ring
  have h1 := Int.floor_le x
  have h2 := Int.lt_floor_add_one x
  have h3 := Int.floor_le (x+slope)
  have h4 := Int.lt_floor_add_one (x+slope)
  have ⟨lo,hi⟩ := slopeBounds
  have l : (1 : ℝ) < (⌊x+slope⌋ : ℝ) - (⌊x⌋ : ℝ) := by linarith
  have u : (⌊x+slope⌋ : ℝ) - (⌊x⌋ : ℝ) < 4 := by linarith
  have l' : (1 : ℤ) < ⌊x+slope⌋-⌊x⌋ := by exact_mod_cast l
  have u' : ⌊x+slope⌋-⌊x⌋ < (4:ℤ) := by exact_mod_cast u
  omega

private noncomputable abbrev D := alternatingSeries weight 0
private noncomputable def shiftAdd (F : PowerSeries ℤ) := F + F*X
private noncomputable def b (n : ℕ) := coeff n (shiftAdd (shiftAdd D))
private noncomputable def t (n : ℕ) := coeff n (shiftAdd (shiftAdd (1 : PowerSeries ℤ)))

private lemma shiftZero (F : PowerSeries ℤ) : coeff 0 (shiftAdd F) = coeff 0 F := by
  simp [shiftAdd]

private lemma shiftSucc (F : PowerSeries ℤ) (n : ℕ) :
    coeff (n+1) (shiftAdd F) = coeff (n+1) F + coeff n F := by
  simp [shiftAdd, coeff_succ_mul_X]

private lemma dCoeff (n : ℕ) : coeff n D = (-1 : ℤ)^n * weight n := by
  simp [alternatingSeries]

private lemma starts : b 0 = 1 ∧ b 1 = -2 ∧ b 2 = -1 := by
  obtain ⟨w0,w1,w2⟩ := weights
  norm_num [b, shiftSucc, shiftZero, dCoeff, w0, w1, w2]

private lemma bound (n : ℕ) : b (n+2) ≤ 1 := by
  have f : b (n+2) = (-1 : ℤ)^n * ((weight (n+2)-weight (n+1))-(weight (n+1)-weight n)) := by
    simp only [b, shiftSucc, dCoeff, pow_succ]
    ring
  obtain ⟨l1,u1⟩ := differences n
  obtain ⟨l2,u2⟩ := differences (n+1)
  change 2 ≤ weight (n+2)-weight (n+1) at l2
  change weight (n+2)-weight (n+1) ≤ 3 at u2
  rcases neg_one_pow_eq_or ℤ n with h | h <;> rw [f,h] <;> omega

private lemma product : generating * shiftAdd (shiftAdd D) = shiftAdd (shiftAdd 1) := by
  have unit : constantCoeff D = (1 : ℤˣ) := by
    rw [← coeff_zero_eq_constantCoeff_apply, dCoeff, weights.1]
    simp
  have inverse : generating * D = 1 := invOfUnit_mul D 1 unit
  calc
    generating * shiftAdd (shiftAdd D) = (generating * D) * (1+X)^2 := by unfold shiftAdd; ring
    _ = shiftAdd (shiftAdd 1) := by rw [inverse]; unfold shiftAdd; ring

private lemma conv (n : ℕ) : (∑ j ∈ range (n+1), a j * b (n-j)) = t n := by
  have h := congrArg (coeff (R := ℤ) n) product
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  exact h

private lemma rhs (n : ℕ) : 0 ≤ t (n+2) := by
  cases n with
  | zero => norm_num [t, shiftSucc, shiftZero, coeff_one]
  | succ n => simp [t, shiftSucc, coeff_one]

private lemma initial : a 0 = 1 ∧ a 1 = 4 := by
  obtain ⟨b0,b1,_⟩ := starts
  have h0 := conv 0
  have h1 := conv 1
  norm_num [sum_range_succ, b0, b1, t, shiftZero, shiftSucc, coeff_one] at h0 h1
  omega

private lemma growth (m : ℕ) :
    0 < a m ∧ (∑ j ∈ range m, a j) ≤ a m ∧ 2*a m ≤ a (m+1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      obtain ⟨h0,h1⟩ := initial
      simp [h0,h1]
    | succ n =>
      obtain ⟨pos,total,doubles⟩ := ih n (by omega)
      have tail : (∑ j ∈ range n, a j * b (n+2-j)) ≤ ∑ j ∈ range n, a j := by
        apply sum_le_sum
        intro j hj
        have small := mem_range.mp hj
        have positive := (ih j (by omega)).1
        have coef : b (n+2-j) ≤ 1 := by
          simpa only [show n+2-j = (n-j)+2 by omega] using bound (n-j)
        simpa using mul_le_mul_of_nonneg_left coef positive.le
      have eqn := conv (n+2)
      rw [sum_range_succ, sum_range_succ, sum_range_succ] at eqn
      obtain ⟨b0,b1,b2⟩ := starts
      simp only [Nat.sub_self, show n+2-(n+1) = 1 by omega,
        show n+2-n = 2 by omega, b0,b1,b2, mul_one, mul_neg] at eqn
      have nonnegative := rhs n
      rw [sum_range_succ]
      refine ⟨by omega, by omega, ?_⟩
      linarith

end ReciprocalGrowth

theorem OMA.solution : type_of% @OMA.S_oeis_a289245.main := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨pos,_,growth⟩ := ReciprocalGrowth.growth n
  omega
