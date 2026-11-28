import OMAStatements.S_oeis_a230269
import Mathlib.Tactic

open OMA.S_oeis_a230269 PowerSeries

namespace TernaryArrays

-- Simultaneously rotating colors preserves all legal extensions. A boundary
-- is described by its color difference and the two cells already satisfied.
private def boundary (above : Option Row) (r : Row) : ℕ :=
  4*(r.2-r.1).val + 2*(satisfied r.1 r.2 (above.map Prod.fst) none).toNat
    + (satisfied r.2 r.1 (above.map Prod.snd) none).toNat

private def table : ℕ → List ℕ
  | 0 => [0,0,0,1,0,0,0,1,0,0,0,1]
  | 1 => [0,1,1,3,0,0,0,2,0,0,0,2]
  | 2 => [0,2,2,7,0,0,1,6,0,1,0,6]
  | 3 => [0,7,7,23,1,2,4,20,1,4,2,20]
  | 4 => [0,24,24,79,4,8,15,70,4,15,8,70]
  | _ => []

private def tab (k : ℕ) (above : Option Row) (r : Row) : ℕ :=
  (table k).getD (boundary above r) 0

set_option maxRecDepth 8192 in
private lemma atZero : ∀ (p : Option Row) (r : Row), completions 0 p r = tab 0 p r := by
  decide +kernel

-- Check one application of the original row rule at all ninety boundaries.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
private lemma tableStep : ∀ (i : Fin 4) (p : Option Row) (r : Row),
    ((nextRows p r).map (tab i (some r))).sum = tab (i.val+1) p r := by
  decide +kernel

private lemma short (k : ℕ) (hk : k ≤ 4) (p : Option Row) (r : Row) :
    completions k p r = tab k p r := by
  induction k generalizing p r with
  | zero => exact atZero p r
  | succ k ih =>
    simp only [completions, show completions k (some r) = tab k (some r) from
      funext (ih (by omega) (some r))]
    exact tableStep ⟨k, by omega⟩ p r

set_option maxRecDepth 8192 in
private lemma tableBalance : ∀ (p : Option Row) (r : Row),
    tab 4 p r + tab 2 p r + 2*tab 1 p r = 4*tab 3 p r := by decide +kernel

private lemma sum_relation {α : Type} (rs : List α) (a b c d : α → ℕ)
    (h : ∀ s, a s + b s + 2*c s = 4*d s) :
    (rs.map a).sum + (rs.map b).sum + 2*(rs.map c).sum = 4*(rs.map d).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h r
    omega

private lemma rowRec (k : ℕ) (p : Option Row) (r : Row) :
    completions (k+4) p r + completions (k+2) p r + 2*completions (k+1) p r =
      4*completions (k+3) p r := by
  induction k generalizing p r with
  | zero =>
    change completions 4 p r + completions 2 p r + 2*completions 1 p r = 4*completions 3 p r
    rw [short 4 (by decide), short 2 (by decide), short 1 (by decide), short 3 (by decide)]
    exact tableBalance p r
  | succ k ih =>
    change ((nextRows p r).map (completions (k+4) (some r))).sum +
      ((nextRows p r).map (completions (k+2) (some r))).sum +
      2*((nextRows p r).map (completions (k+1) (some r))).sum =
      4*((nextRows p r).map (completions (k+3) (some r))).sum
    exact sum_relation _ _ _ _ _ (ih (some r))

set_option maxRecDepth 8192 in
private lemma initial : a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=2 ∧ a 4=8 := by decide +kernel

private lemma rec (k : ℕ) : a (k+4)+a (k+2)+2*a (k+1)=4*a (k+3) := by
  cases k with
  | zero => obtain ⟨_,h1,h2,h3,h4⟩ := initial; change a 4+a 2+2*a 1=4*a 3; omega
  | succ k =>
    exact sum_relation colors _ _ _ _ (fun d => rowRec k none (0,d))

private lemma series :
    (1-X)*(1-3*X-2*X^2)*(PowerSeries.mk (fun n => (a n : ℚ))) = 2*X^3 := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  have h : F - C (4:ℚ)*(F*X) + (F*X)*X + C (2:ℚ)*(((F*X)*X)*X) = C (2:ℚ)*X^3 := by
    ext k
    by_cases hk : k ≤ 3
    · obtain ⟨z,o,t,th,_⟩ := initial
      interval_cases k <;> norm_num [F, coeff_C_mul, coeff_succ_mul_X, coeff_X, coeff_X_pow,
        coeff_zero_eq_constantCoeff,z,o,t,th]
    · obtain ⟨j, rfl⟩ : ∃ j, k=j+4 := ⟨k-4,by omega⟩
      have hr : (a (j+4):ℚ)+(a (j+2):ℚ)+2*(a (j+1):ℚ)=4*(a (j+3):ℚ) := by
        exact_mod_cast rec j
      simp [F, coeff_C_mul, coeff_succ_mul_X, coeff_X_pow]
      linarith
  change (1-X)*(1-3*X-2*X^2)*F = _
  simp only [map_ofNat] at h
  linear_combination h

private lemma recTwo (k : ℕ) : a (k+3) = 3*a (k+2)+2*a (k+1)+2 := by
  induction k with
  | zero => obtain ⟨_,h1,h2,h3,_⟩ := initial; change a 3=3*a 2+2*a 1+2; omega
  | succ k =>
    have h := rec k
    change a (k+4)=3*a (k+3)+2*a (k+2)+2
    omega

private lemma powerRec (z : ℝ) (hz : z^2=3*z+2) (n : ℕ) :
    z^(n+2) = 3*z^(n+1)+2*z^n := by
  simp only [pow_succ]
  linear_combination z^n*hz

private lemma closedRec (n : ℕ) :
    closedValue (n+2)=3*closedValue (n+1)+2*closedValue n+2 := by
  let s := Real.sqrt 17
  have hs : s^2=17 := Real.sq_sqrt (by norm_num)
  have h₁ : ((3+s)/2)^2=3*((3+s)/2)+2 := by nlinarith
  have h₂ : ((3-s)/2)^2=3*((3-s)/2)+2 := by nlinarith
  unfold closedValue
  linear_combination ((5-s)/(4*s))*powerRec _ h₁ n - ((5+s)/(4*s))*powerRec _ h₂ n

private lemma closed (k : ℕ) : (a (k+1) : ℝ)=closedValue (k+1) := by
  have hs : (Real.sqrt 17)^2=17 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 17 ≠ 0 := by positivity
  induction k using Nat.twoStepInduction with
  | zero =>
    rw [initial.2.1]
    unfold closedValue
    norm_num
    field_simp
    ring
  | one =>
    rw [initial.2.2.1]
    unfold closedValue
    norm_num
    field_simp
    nlinarith [congrArg (fun x : ℝ => x*Real.sqrt 17) hs]
  | more n h₀ h₁ =>
    have h : (a (n+3):ℝ)=3*(a (n+2):ℝ)+2*(a (n+1):ℝ)+2 := by exact_mod_cast recTwo n
    linarith [closedRec (n+1)]

end TernaryArrays

theorem OMA.solution : type_of% @OMA.S_oeis_a230269.main :=
  ⟨TernaryArrays.rec, TernaryArrays.series, TernaryArrays.closed⟩
