import OMAStatements.S_oeis_a268965
import Mathlib.Tactic

open OMA.S_oeis_a268965 PowerSeries

namespace ComplementaryEdges

-- From each color there is one complementary choice and 2 ordinary choices.
private lemma emptyCount (k : ℕ) : ∀ x, count k x 0 = 2^k := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [count]
    fin_cases x <;> norm_num [colors,ih,pow_succ] <;> (try split_ifs) <;> omega

private lemma singleCount (k : ℕ) : ∀ x, count (k+1) x 1=(k+1)*2^k := by
  induction k with
  | zero => intro x; fin_cases x <;> decide
  | succ k ih =>
    intro x
    rw [count]
    fin_cases x <;> norm_num [colors,emptyCount,ih,pow_succ] <;> (try split_ifs) <;> first | omega | ring

private lemma formula (n : ℕ) : a (n+1)=4^n*(6*n+9) := by
  rw [a]
  simp only [colors,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    singleCount,emptyCount,Nat.add_zero]
  rw [pow_succ 2 (2*n)]
  rw [pow_mul]
  norm_num
  ring

private lemma rec (n : ℕ) : a (n+3)+16*a (n+1)=8*a (n+2) := by
  rw [formula (n+2),formula n,formula (n+1)]
  simp only [pow_succ]
  ring

private lemma series : (1-4*X)^2*(PowerSeries.mk (fun n => (a n : ℚ))) =
    3*X*(3-4*X) := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  have init : a 0=0 ∧ a 1=9 ∧ a 2=60 := by
    constructor
    · rfl
    · constructor <;> first | exact formula 0 | exact formula 1
  have h : F-C (8:ℚ)*(F*X)+C (16:ℚ)*((F*X)*X) =
      C (9:ℚ)*X - C (12:ℚ)*X^2 := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> norm_num [F,coeff_C_mul,coeff_succ_mul_X,coeff_X,coeff_X_pow,
        coeff_zero_eq_constantCoeff,init.1,init.2.1,init.2.2]
    · obtain ⟨j,rfl⟩ : ∃ j, k=j+3 := ⟨k-3,by omega⟩
      have hr : (a (j+3):ℚ)+16*(a (j+1):ℚ)=8*(a (j+2):ℚ) := by exact_mod_cast rec j
      simp [F,coeff_C_mul,coeff_succ_mul_X,coeff_X_pow]
      linarith
  change (1-4*X)^2*F=_
  simp only [map_ofNat] at h
  linear_combination h

end ComplementaryEdges

theorem OMA.solution : type_of% @OMA.S_oeis_a268965.main :=
  ⟨ComplementaryEdges.rec,ComplementaryEdges.series,ComplementaryEdges.formula⟩
