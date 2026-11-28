import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt

/-! Interpolate the squarefree ideal summatory function between consecutive squares.
The individual coefficient bound controls the entire intervening interval. -/
-- Credit: @STARDUSTLC666
namespace OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1
open Filter Asymptotics NumberField
open scoped NumberField Topology

/-- Subpolynomial growth of the individual signed norm coefficients. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ)^S.1.card
    ∀ ε : ℝ, 0 < ε → a =O[atTop] fun n : ℕ => (n : ℝ)^ε

/-- Cancellation sampled at square endpoints. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    let P := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}
    let N (S : Finset P) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1
    let a (n : ℕ) : ℂ := ∑' S : N ⁻¹' {n}, (-1 : ℂ)^S.1.card
    ∀ r : ℝ, 1/2 < r →
      (fun m : ℕ => ∑ k ∈ Finset.Icc 1 (m^2), a k) =O[atTop]
        fun m : ℕ => ((m^2 : ℕ) : ℝ)^r

theorem gap_bound (a : ℕ → ℂ) {ε B : ℝ} (hε : 0 < ε) (hB : 0 < B)
    (ha : ∀ k : ℕ, 0 < k → ‖a k‖ ≤ B*(k : ℝ)^ε) (n : ℕ) (hn : 0 < n) :
    ‖∑ k ∈ Finset.Ioc (n.sqrt^2) n, a k‖ ≤ (2*B)*(n : ℝ)^(1/2+ε) := by
  let J := Finset.Ioc (n.sqrt^2) n
  have hsq := Nat.sqrt_le' n
  have hlen : n - n.sqrt^2 ≤ 2*n.sqrt := by
    have h := Nat.sqrt_le_add n
    rw [← sq] at h
    omega
  have hreal : (J.card : ℝ) ≤ 2*Real.sqrt (n : ℝ) := by
    simp only [J, Nat.card_Ioc]
    exact (show ((n-n.sqrt^2 : ℕ) : ℝ) ≤ 2*(n.sqrt : ℝ) by exact_mod_cast hlen).trans
      (mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt (by norm_num))
  have hpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    _ ≤ ∑ k ∈ J, ‖a k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ J, B*(n : ℝ)^ε := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hk
      exact (ha k (Nat.zero_lt_of_lt hl)).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast hu) hε.le) hB.le)
    _ = (J.card : ℝ) * (B*(n : ℝ)^ε) := by simp
    _ ≤ (2*Real.sqrt (n : ℝ))*(B*(n : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hreal (by positivity)
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_add hpos]; ring

theorem interpolate (a : ℕ → ℂ) {r : ℝ} (hr : 1/2 < r)
    (ha : ∀ ε : ℝ, 0 < ε → a =O[atTop] fun n : ℕ => (n : ℝ)^ε)
    (hs : (fun m : ℕ => ∑ k ∈ Finset.Icc 1 (m^2), a k) =O[atTop]
      fun m : ℕ => ((m^2 : ℕ) : ℝ)^r) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] fun n : ℕ => (n : ℝ)^r := by
  let ε := r-1/2
  have hε : 0 < ε := sub_pos.mpr hr
  obtain ⟨B,hB,hcoeff⟩ := bound_of_isBigO_nat_atTop (ha ε hε)
  obtain ⟨C,hC,hsquare⟩ := bound_of_isBigO_nat_atTop hs
  have hcoeff' (k : ℕ) (hk : 0 < k) : ‖a k‖ ≤ B*(k : ℝ)^ε := by
    have hk' := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk : 0 < (k : ℝ)) ε
    simpa only [Real.norm_of_nonneg hk'.le] using hcoeff (x := k) hk'.ne'
  apply IsBigO.of_bound (C+2*B)
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hm : 0 < n.sqrt := Nat.sqrt_pos.mpr hn
  have hpow : 0 < ((n.sqrt^2 : ℕ) : ℝ)^r := Real.rpow_pos_of_pos (by positivity) _
  have hs' := hsquare (x := n.sqrt) hpow.ne'
  have hbase : ((n.sqrt^2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have hmono := Real.rpow_le_rpow (Nat.cast_nonneg (n.sqrt^2)) hbase (by linarith : 0 ≤ r)
  have hgap := gap_bound a hε hB hcoeff' n hn
  rw [show 1/2+ε = r by dsimp [ε]; ring] at hgap
  simp only [Real.norm_of_nonneg hpow.le] at hs'
  simp only [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) r)]
  have hsum : (∑ k ∈ Finset.Icc 1 (n.sqrt^2), a k) + (∑ k ∈ Finset.Ioc (n.sqrt^2) n, a k)
      = ∑ k ∈ Finset.Icc 1 n, a k := by
    rw [show ∀ m : ℕ, Finset.Icc 1 m = Finset.Ioc 0 m from
      fun m => Finset.Icc_succ_left_eq_Ioc 0 m]
    rw [show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc 0 n]
    exact Finset.sum_Ioc_consecutive a (Nat.zero_le _) (Nat.sqrt_le' n)
  rw [← hsum, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (hs'.trans (mul_le_mul_of_nonneg_left hmono hC.le)) hgap)

theorem main : H1 → H2 → OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1.H2 := by
  intro hcoeff hsquare K _ _ P N a r hr
  exact interpolate a hr (hcoeff K) (hsquare K r hr)

end OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1
