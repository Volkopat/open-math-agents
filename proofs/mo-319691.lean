import OMAStatements.S_mo_319691
import Mathlib

-- Retains @AkiRA-COM-FP’s odd-numerator approximation from PR #13803.
-- The dyadic denominator bound uses Mathlib’s natural-logarithm inequalities.

open OMA.S_mo_319691

private theorem denominator_between (n : ℕ) (hn : 0 < n) :
    ∃ t : ℕ, 1 ≤ t ∧ n^3 ≤ 2^t ∧ 2^t ≤ 2*n^3 := by
  refine ⟨Nat.log 2 (n^3) + 1, by omega,
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n^3)).le, ?_⟩
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (pow_ne_zero _ hn.ne'))

theorem OMA.solution : type_of% @OMA.S_mo_319691.main := by
  refine ⟨1/2,1,1,3,by norm_num,by norm_num,by norm_num,?_⟩
  intro n k hn _
  obtain ⟨t,ht,hLower,hUpper⟩ := denominator_between n hn
  let q := 2^t
  let x := inputFraction n k
  have hX : 0 ≤ x := by unfold x inputFraction; positivity
  let w := (q : ℝ)*x/2
  let r := ⌊w⌋₊
  let p := 2*r+1
  have hW : 0 ≤ w := by dsimp [w]; positivity
  have hLo : (r : ℝ) ≤ w := Nat.floor_le hW
  have hHi : w < (r : ℝ)+1 := Nat.lt_floor_add_one w
  have hq : 0 < q := pow_pos (by decide) t
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hPowR : 0 < (n : ℝ)^3 := pow_pos hnR _
  have hCoprime₂ : Nat.Coprime p 2 := by
    rw [Nat.coprime_two_right]
    exact ⟨r,rfl⟩
  have hCoprime : Nat.Coprime p q := hCoprime₂.pow_right t
  have hL : (n : ℝ)^3 ≤ q := by exact_mod_cast hLower
  have hU : (q : ℝ) ≤ 2*(n : ℝ)^3 := by exact_mod_cast hUpper
  have hDown : (1/2 : ℝ)/(n : ℝ)^3 ≤ 1/(q : ℝ) := by
    apply (div_le_div_iff₀ hPowR hqR).mpr
    linarith
  have hUp : (1 : ℝ)/(q : ℝ) ≤ 1/(n : ℝ)^3 := one_div_le_one_div_of_le hPowR hL
  have hError : |(q : ℝ)*x - (p : ℝ)| ≤ 1 := by
    apply abs_le.mpr
    dsimp [w] at hLo hHi
    simp only [p,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    constructor <;> linarith
  refine ⟨p,q,hq,hCoprime,hDown,hUp,?_⟩
  change |x - (p : ℝ)/(q : ℝ)| ≤ 1/(n : ℝ)^3
  rw [show x-(p : ℝ)/(q : ℝ) = ((q : ℝ)*x-(p : ℝ))/(q : ℝ) by
    field_simp [hqR.ne'],abs_div,abs_of_pos hqR]
  exact (div_le_div_of_nonneg_right hError hqR.le).trans hUp
