import OMAStatements.S_oeis_a269270
import Mathlib.Tactic

open OMA.S_oeis_a269270 PowerSeries

namespace ComplementaryEdges

-- From each color there is one complementary choice and 3 ordinary choices.
private lemma emptyCount (k : ℕ) : ∀ x, count k x 0 = 3^k := by
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    rw [count]
    fin_cases x <;> norm_num [colors,ih,pow_succ] <;> (try split_ifs) <;> omega

private lemma singleCount (k : ℕ) : ∀ x, count (k+1) x 1=(k+1)*3^k := by
  induction k with
  | zero => intro x; fin_cases x <;> decide
  | succ k ih =>
    intro x
    rw [count]
    fin_cases x <;> norm_num [colors,emptyCount,ih,pow_succ] <;> (try split_ifs) <;> first | omega | ring

private lemma formula (n : ℕ) : a (n+1)=9^n*(8*n+4) := by
  rw [a]
  simp only [colors,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    singleCount,Nat.add_zero]
  rw [pow_mul]
  norm_num
  ring

private lemma rec (n : ℕ) : a (n+3)+81*a (n+1)=18*a (n+2) := by
  rw [formula (n+2),formula n,formula (n+1)]
  simp only [pow_succ]
  ring

private lemma seriesOfRecurrence (f : ℕ → ℚ) (h₀ : f 0=0) (h₁ : f 1=4) (h₂ : f 2=108)
    (hrec : ∀ j, f (j+3)+81*f (j+1)=18*f (j+2)) :
    (1-9*X)^2*(PowerSeries.mk f)=4*X*(1+9*X) := by
  let F := PowerSeries.mk f
  have h : F-C (18:ℚ)*(F*X)+C (81:ℚ)*((F*X)*X) =
      C (4:ℚ)*X + C (36:ℚ)*X^2 := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> norm_num [F,coeff_C_mul,coeff_succ_mul_X,coeff_X,coeff_X_pow,
        coeff_zero_eq_constantCoeff,h₀,h₁,h₂]
    · obtain ⟨j,rfl⟩ : ∃ j, k=j+3 := ⟨k-3,by omega⟩
      simp [F,coeff_C_mul,coeff_succ_mul_X,coeff_X_pow]
      linarith [hrec j]
  change (1-9*X)^2*F=_
  simp only [map_ofNat] at h
  linear_combination h

private lemma series : (1-9*X)^2*(PowerSeries.mk (fun n => (a n : ℚ))) =
    4*X*(1+9*X) := by
  apply seriesOfRecurrence
  · rfl
  · exact_mod_cast (show a 1=4 from formula 0)
  · exact_mod_cast (show a 2=108 from formula 1)
  · intro j
    exact_mod_cast rec j

end ComplementaryEdges

theorem OMA.solution : type_of% @OMA.S_oeis_a269270.main :=
  ⟨ComplementaryEdges.rec,ComplementaryEdges.series,ComplementaryEdges.formula⟩
