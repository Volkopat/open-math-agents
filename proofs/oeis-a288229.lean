import OMAStatements.S_oeis_a288229
import Mathlib

/-!
# Strict growth of the reciprocal-series coefficients in OEIS A288229

Multiplying the denominator by (1+X) squared converts its coefficients
into signed second differences of floors. The first four nonconstant
coefficients are all minus one. Every later coefficient is at most one,
and the accumulated adverse tail is bounded by the preceding terms.
-/

namespace A288229Proof

open OMA.S_oeis_a288229 PowerSeries Finset

noncomputable def D := denominator (Real.pi / 2)
noncomputable def T : ℚ⟦X⟧ := D + D * X ^ 1 + D * X ^ 1 + D * X ^ 2
noncomputable def u := a (Real.pi / 2)
noncomputable def b (n : ℕ) := coeff n T

lemma dcoeff (n : ℕ) : coeff n D =
    (-1 : ℚ)^n * (⌊((n : ℝ)+1)*(Real.pi/2)⌋ : ℤ) := by
  simp [D,denominator,weight]

lemma smallD : coeff 0 D = 1 ∧ coeff 1 D = -3 ∧ coeff 2 D = 4 ∧
    coeff 3 D = -6 ∧ coeff 4 D = 7 := by
  have hpi := Real.pi_gt_d2
  have hpi' := Real.pi_lt_d2
  have h0 : ⌊((0:ℝ)+1)*(Real.pi/2)⌋ = (1:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have h1 : ⌊((1:ℝ)+1)*(Real.pi/2)⌋ = (3:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have h2 : ⌊((2:ℝ)+1)*(Real.pi/2)⌋ = (4:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have h3 : ⌊((3:ℝ)+1)*(Real.pi/2)⌋ = (6:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  have h4 : ⌊((4:ℝ)+1)*(Real.pi/2)⌋ = (7:ℤ) := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
  simp only [dcoeff, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, h0,h1,h2,h3,h4]
  norm_num

lemma bformula (n : ℕ) : b n = coeff n D +
    (if 1 ≤ n then coeff (n-1) D else 0) +
    (if 1 ≤ n then coeff (n-1) D else 0) +
    (if 2 ≤ n then coeff (n-2) D else 0) := by
  simp only [b,T,map_add,coeff_mul_X_pow']

lemma smallB : b 0 = 1 ∧ b 1 = -1 ∧ b 2 = -1 ∧ b 3 = -1 ∧ b 4 = -1 := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := smallD
  norm_num [bformula,h0,h1,h2,h3,h4]

lemma second_floor {x y z : ℝ} (h : x+z=2*y) :
    -1 ≤ ⌊x⌋ - 2*⌊y⌋ + ⌊z⌋ ∧ ⌊x⌋ - 2*⌊y⌋ + ⌊z⌋ ≤ 1 := by
  have h₁ : (-2 : ℝ) < ⌊x⌋ - 2*(⌊y⌋:ℝ) + ⌊z⌋ := by
    linarith [Int.lt_floor_add_one x,Int.floor_le y,Int.lt_floor_add_one z]
  have h₂ : (⌊x⌋:ℝ) - 2*(⌊y⌋:ℝ) + ⌊z⌋ < 2 := by
    linarith [Int.floor_le x,Int.lt_floor_add_one y,Int.floor_le z]
  have h₃ : (-2 : ℤ) < ⌊x⌋ - 2*⌊y⌋ + ⌊z⌋ := by exact_mod_cast h₁
  have h₄ : ⌊x⌋ - 2*⌊y⌋ + ⌊z⌋ < (2:ℤ) := by exact_mod_cast h₂
  omega

lemma b_le (n : ℕ) : b n ≤ 1 := by
  obtain _ | _ | n := n
  · rw [smallB.1]
  · rw [smallB.2.1]; norm_num
  have h := second_floor (x := ((n:ℝ)+1)*(Real.pi/2))
    (y := (((n+1:ℕ):ℝ)+1)*(Real.pi/2)) (z := (((n+2:ℕ):ℝ)+1)*(Real.pi/2))
    (by push_cast; ring)
  let z := ⌊((n:ℝ)+1)*(Real.pi/2)⌋ -
    2 * ⌊(((n+1:ℕ):ℝ)+1)*(Real.pi/2)⌋ + ⌊(((n+2:ℕ):ℝ)+1)*(Real.pi/2)⌋
  have hi : (-1:ℤ) ≤ z ∧ z ≤ 1 := h
  have hq : (-1:ℚ) ≤ (z:ℚ) ∧ (z:ℚ) ≤ 1 := by
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  have e : b (n+2) = (-1:ℚ)^n * z := by
    rw [bformula]
    simp only [show 1 ≤ n+2 by omega, show 2 ≤ n+2 by omega, if_true,
      show n+2-1=n+1 by omega, show n+2-2=n by omega,dcoeff,pow_succ,z]
    push_cast
    ring
  rw [e]
  rcases neg_one_pow_eq_or ℚ n with hpow | hpow
  · rw [hpow]; linarith
  · rw [hpow]; linarith

lemma conv (n : ℕ) :
    ∑ i ∈ range (n+1), u i * b (n-i) =
    (if n=0 then 1 else 0) + (if n=1 then 2 else 0) + (if n=2 then 1 else 0) := by
  have hd : constantCoeff D ≠ 0 := by
    rw [←coeff_zero_eq_constantCoeff,smallD.1]; norm_num
  have e : D⁻¹ * T = (1 : ℚ⟦X⟧) + X ^ 1 + X ^ 1 + X ^ 2 := by
    calc
      D⁻¹ * T = (D * D⁻¹) * (1 + X ^ 1 + X ^ 1 + X ^ 2) := by dsimp only [T]; ring
      _ = _ := by rw [PowerSeries.mul_inv_cancel D hd,one_mul]
  have en := congrArg (coeff (R := ℚ) n) e
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i D⁻¹ * coeff j T) n] at en
  change (∑ i ∈ range (n+1), u i * b (n-i)) = _ at en
  rw [en]
  simp only [map_add,coeff_X_pow,coeff_one]
  split_ifs <;> norm_num at *

lemma initial : u 0 = 1 ∧ u 1 = 3 ∧ u 2 = 5 ∧ u 3 = 9 ∧ u 4 = 18 := by
  obtain ⟨b0,b1,b2,b3,b4⟩ := smallB
  have h0 := conv 0
  have h1 := conv 1
  have h2 := conv 2
  have h3 := conv 3
  have h4 := conv 4
  norm_num [sum_range_succ,b0,b1,b2,b3,b4] at h0 h1 h2 h3 h4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

lemma tail (k : ℕ) :
    (∑ i ∈ range (k+1), u i * b (k+5-i)) -
      u (k+1) - u (k+2) - u (k+3) - u (k+4) + u (k+5) = 0 := by
  obtain ⟨b0,b1,b2,b3,b4⟩ := smallB
  have h := conv (k+5)
  rw [sum_range_succ _ (k+5),sum_range_succ _ (k+4),
      sum_range_succ _ (k+3),sum_range_succ _ (k+2),sum_range_succ _ (k+1)] at h
  simp only [show k+5 ≠ 0 by omega,show k+5 ≠ 1 by omega,show k+5 ≠ 2 by omega,
    if_false,add_zero, Nat.sub_self,show k+5-(k+4)=1 by omega,
    show k+5-(k+3)=2 by omega,show k+5-(k+2)=3 by omega,
    show k+5-(k+1)=4 by omega,b0,b1,b2,b3,b4] at h
  linarith only [h]

lemma growth (n : ℕ) :
    0 < u n ∧ (∑ i ∈ range n, u i) < u (n+1) ∧ u n < u (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain ⟨h0,h1,h2,h3,h4⟩ := initial
    obtain _ | _ | _ | _ | k := n
    · norm_num [sum_range_succ,h0,h1]
    · norm_num [sum_range_succ,h0,h1,h2]
    · norm_num [sum_range_succ,h0,h1,h2,h3]
    · norm_num [sum_range_succ,h0,h1,h2,h3,h4]
    · have p := ih (k+3) (by omega)
      have q := ih (k+1) (by omega)
      have ht := tail k
      have htBound : (∑ i ∈ range (k+1), u i * b (k+5-i)) ≤ ∑ i ∈ range (k+1), u i := by
        apply sum_le_sum
        intro i hi
        have hp := (ih i (by have := mem_range.mp hi; omega)).1
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (b_le (k+5-i)) hp.le
      have hfib : u (k+4) + u (k+3) ≤ u (k+5) := by
        linarith only [ht,htBound,q.2.1,q.1]
      refine ⟨lt_trans p.1 p.2.2, ?_, ?_⟩
      · rw [sum_range_succ _ (k+3)]
        linarith only [hfib,p.2.1]
      · linarith only [hfib,p.1]

end A288229Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a288229.main := by
  exact strictMono_nat_of_lt_succ fun n => (A288229Proof.growth n).2.2
