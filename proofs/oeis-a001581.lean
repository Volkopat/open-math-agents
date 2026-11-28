import OMAStatements.S_oeis_a001581

namespace OMA.S_oeis_a001581

private theorem length_mono : Monotone (fun m => (losingUpTo m).length) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [losingUpTo]
  split <;> simp

private theorem history_bound {n x : ℕ} (h : x ∈ losingUpTo n) : x ≤ n := by
  induction n with
  | zero => simpa [losingUpTo] using h
  | succ n ih =>
    simp only [losingUpTo] at h
    split at h
    · exact (ih h).trans (Nat.le_succ _)
    · rcases List.mem_cons.mp h with rfl|h
      · exact le_rfl
      · exact (ih h).trans (Nat.le_succ _)

private theorem history_prefix {n k : ℕ} (h : k ≤ n) :
    (losingUpTo n).filter (fun x => decide (x ≤ k)) = losingUpTo k := by
  induction n with
  | zero =>
    obtain rfl : k=0 := by omega
    rfl
  | succ n ih =>
    by_cases heq : k=n+1
    · subst k
      exact List.filter_eq_self.mpr fun x hx => by simpa using history_bound hx
    · have hk : k≤n := by omega
      simp only [losingUpTo]
      split
      · exact ih hk
      · simpa [show ¬ n+1≤k by omega] using ih hk

private def observed : List ℕ :=
  [4,10,14,20,24,30,36,40,46,50,56,60,66,72,76,82,86,92,96,102,108,112,118,122,128,132,138,150]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem history150 : losingUpTo 150 = observed.reverse ++ [0] := by decide +kernel

private theorem value_at {i x : ℕ} (hx : 0<x) (hi : i+2 ≤ (losingUpTo x).length)
    (hprev : (losingUpTo (x-1)).length < i+2) : a i=x := by
  change sInf {m : ℕ | i+2 ≤ (losingUpTo m).length}=x
  refine le_antisymm (Nat.sInf_le hi) ?_
  have hmin := Nat.sInf_mem (s := {m : ℕ | i+2 ≤ (losingUpTo m).length}) ⟨x,hi⟩
  by_contra! hbad
  have le' := length_mono (show sInf {m : ℕ | i+2 ≤ (losingUpTo m).length} ≤ x-1 by omega)
  exact (Nat.not_lt_of_ge (hmin.trans le')) hprev

private theorem observed_eq (i : Fin 28) : a i = observed[i.val]'(by exact i.isLt) := by
  let x := observed[i.val]'(by exact i.isLt)
  have checks : ∀ j : Fin 28, let v := observed[j.val]'(by exact j.isLt)
      0<v ∧ v≤150 ∧ j.val+2≤((observed.reverse++[0]).filter (fun z => decide (z≤v))).length ∧
      ((observed.reverse++[0]).filter (fun z => decide (z≤v-1))).length<j.val+2 := by decide +kernel
  obtain ⟨hpos,hmax,hupper,hlower⟩ := checks i
  change 0<x at hpos
  change x≤150 at hmax
  apply value_at hpos
  · rw [← history_prefix hmax,history150]
    exact hupper
  · rw [← history_prefix (show x-1≤150 by omega),history150]
    exact hlower

open PowerSeries

/-- Coefficients predicted by the proposed rational function, in blocks of seven. -/
def predicted (n : ℕ) : ℤ := (36 : ℤ) * (n/7 : ℕ) +
  ([4,10,14,20,24,30,36] : List ℤ)[n%7]!

private theorem predicted_period (n : ℕ) : predicted (n+7)=predicted n+36 := by
  simp [predicted,Nat.add_div_right,Nat.add_mod_right]
  ring

private noncomputable def numerator (z : PowerSeries ℤ) :=
  C 4 + C 6*z^1 + C 4*z^2 + C 6*z^3 + C 4*z^4 + C 6*z^5 + C 6*z^6

private theorem expand_num (z : PowerSeries ℤ) :
    2*(1+z)*(3*z^5+2*z^3+z^2+z+2) = numerator z := by
  norm_num [numerator]
  ring

private theorem expand_den (s z : PowerSeries ℤ) :
    s*((z^6+z^5+z^4+z^3+z^2+z+1)*(z-1)^2) =
      s-s*z^1-s*z^7+s*z^8 := by ring

private theorem numerator_coeff (d : ℕ) : coeff d (numerator X) =
    (if d=0 then 4 else 0) + (if d=1 then 6 else 0) + (if d=2 then 4 else 0) +
    (if d=3 then 6 else 0) + (if d=4 then 4 else 0) +
    (if d=5 then 6 else 0) + (if d=6 then 6 else 0) := by
  simp only [numerator,map_add,coeff_C,coeff_C_mul_X_pow]

/-- The displayed rational function has these coefficients in every degree. -/
theorem predicted_generating_function :
    (PowerSeries.mk predicted) * ((X^6+X^5+X^4+X^3+X^2+X+1)*(X-1)^2) =
      2*(1+X)*(3*X^5+2*X^3+X^2+X+2) := by
  rw [expand_den,expand_num]
  ext d
  simp only [map_add,map_sub,coeff_mul_X_pow',coeff_mk,numerator_coeff]
  by_cases h : d<8
  · interval_cases d <;> decide
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 8≤d by omega)
    simp only [show 1≤8+k by omega, show 7≤8+k by omega, show 8≤8+k by omega,
      if_true, show 8+k-1=k+7 by omega, show 8+k-7=k+1 by omega, show 8+k-8=k by omega]
    rw [show 8+k=(k+1)+7 by omega,predicted_period,predicted_period]
    simp (disch := omega)

private theorem observed_predictions : ∀ j : Fin 28, j.val < 27 →
    ((observed[j.val]'j.isLt : ℕ) : ℤ) = predicted j.val := by decide +kernel

/-- The coefficients agree through degree 26, and degree 27 is the first failure. -/
theorem first_difference :
    (∀ i : Fin 27, (a i : ℤ)=predicted i) ∧ a 27=150 ∧ predicted 27=144 := by
  refine ⟨?_,observed_eq ⟨27,by decide⟩,by decide⟩
  intro i
  have h := observed_eq ⟨i.val,by omega⟩
  change a i.val = _ at h
  rw [h]
  exact observed_predictions ⟨i.val,by omega⟩ i.isLt

end OMA.S_oeis_a001581

open OMA.S_oeis_a001581 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001581.main) := by
  intro h
  have hmul := h.trans predicted_generating_function.symm
  have hd : ((X^6+X^5+X^4+X^3+X^2+X+1)*(X-1)^2 : PowerSeries ℤ) ≠ 0 := by
    intro he
    have := congrArg (constantCoeff (R := ℤ)) he
    norm_num at this
  have hs := mul_right_cancel₀ hd hmul
  have hc := congrArg (coeff 27) hs
  simp only [series,coeff_mk,first_difference.2.1,first_difference.2.2] at hc
  norm_num at hc
