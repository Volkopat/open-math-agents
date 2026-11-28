import OMAStatements.S_oeis_a112290
import Mathlib.Tactic

open OMA.S_oeis_a112290 Filter Topology Finset

namespace ReciprocalStirling

-- Every interior entry in row m is at least m(m-1)/2 for m ≥ 3.
private lemma interior (n k : ℕ) (lo : 2 ≤ k) (hi : k ≤ n+2) :
    (n+3)*(n+2) ≤ 2*Nat.stirlingSecond (n+3) k := by
  induction n generalizing k with
  | zero =>
    have : k=2 := by omega
    subst k
    decide
  | succ n ih =>
    change (n+4)*(n+3) ≤ 2*Nat.stirlingSecond ((n+3)+1) k
    rw [Nat.stirlingSecond_succ_left _ _ (by omega)]
    by_cases top : k=n+3
    · subst k
      rw [Nat.stirlingSecond_self,Nat.mul_one,show n+3-1=n+2 by omega]
      nlinarith only [ih (n+2) (by omega) (by omega)]
    · have h := ih k lo (by omega)
      have mul := Nat.mul_le_mul_right (Nat.stirlingSecond (n+3) k) lo
      nlinarith [Nat.zero_le (Nat.stirlingSecond (n+3) (k-1))]

private noncomputable def tail (n : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), (Nat.stirlingSecond (n+3) (i+2):ℝ)⁻¹

private lemma rowSum (n : ℕ) : (reciprocalSum (n+3):ℝ)=2+tail n := by
  unfold reciprocalSum tail
  push_cast
  rw [sum_range_succ _ (n+2),sum_range_succ' _ (n+1)]
  have first : Nat.stirlingSecond (n+3) 1 = 1 := Nat.stirlingSecond_one_right (n+2)
  simp only [Nat.stirlingSecond_self, first, Nat.cast_one, inv_one]
  ring

private lemma estimate (n : ℕ) : tail n ≤ 2*(1/((n:ℝ)+2)) := by
  have h (i : ℕ) (hi : i ∈ range (n+1)) :
      (Nat.stirlingSecond (n+3) (i+2):ℝ)⁻¹ ≤ 2/(((n:ℝ)+1)*((n:ℝ)+2)) := by
    have hir := mem_range.mp hi
    have b : ((n:ℝ)+3)*((n:ℝ)+2) ≤ 2*(Nat.stirlingSecond (n+3) (i+2):ℝ) := by
      exact_mod_cast interior n (i+2) (by omega) (by omega)
    have ns : 0 < (Nat.stirlingSecond (n+3) (i+2):ℝ) := by
      nlinarith [show (0:ℝ) ≤ n by positivity]
    rw [inv_eq_one_div, div_le_div_iff₀ ns (by positivity)]
    nlinarith [show (0:ℝ) ≤ n by positivity]
  unfold tail
  calc
    _ ≤ ∑ _i ∈ range (n+1), 2/(((n:ℝ)+1)*((n:ℝ)+2)) := sum_le_sum h
    _ = _ := by simp; field_simp

private lemma limit : Tendsto (fun n => (reciprocalSum n:ℝ)) atTop (𝓝 2) := by
  have l : Tendsto (fun n : ℕ => 2*(1/((n:ℝ)+2))) atTop (𝓝 (0:ℝ)) := by
    have s := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
    simpa using (tendsto_const_nhds (x := (2:ℝ))).mul s
  have t : Tendsto tail atTop (𝓝 0) := squeeze_zero
    (fun n => Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))) estimate l
  apply (tendsto_add_atTop_iff_nat 3).mp
  have add : Tendsto (fun n => (2:ℝ)+tail n) atTop (𝓝 (2+0)) := tendsto_const_nhds.add t
  simpa only [add_zero] using add.congr (fun n => (rowSum n).symm)

end ReciprocalStirling

theorem OMA.solution : type_of% @OMA.S_oeis_a112290.main := by
  apply ReciprocalStirling.limit.congr
  intro n
  exact Rat.cast_def (reciprocalSum n)
