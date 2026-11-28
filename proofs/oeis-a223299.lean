import OMAStatements.S_oeis_a223299
import Mathlib.Tactic

open OMA.S_oeis_a223299 PowerSeries

namespace TriangularArrays

private def count (n : ℕ) (r : Row) := (grids n r).length

private lemma step (n : ℕ) (r : Row) :
    count (n+1) r = ((after r).map (count n)).sum := by
  simp [count, grids, List.length_flatMap]
  rfl

private lemma totals (n : ℕ) : a (n+1) = (rows.map (count n)).sum := by
  simp [a, List.length_flatMap]
  rfl

private lemma sum_relation (rs : List Row) (u v w : Row → ℕ)
    (h : ∀ r ∈ rs, u r + 12*v r = 11*w r) :
    (rs.map u).sum + 12*(rs.map v).sum = 11*(rs.map w).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hh := h r (by simp)
    have ht := ih (fun s hs => h s (List.mem_cons_of_mem r hs))
    simp only [List.map_cons, List.sum_cons]
    omega

-- Each oriented edge has 6, 9, or 12 possible successors. The sum of their
-- degrees is eleven times its degree minus twelve, as checked on all 36 rows.
private lemma rows_rec (n : ℕ) (r : Row) (hr : r ∈ rows) :
    count (n+2) r + 12*count n r = 11*count (n+1) r := by
  induction n generalizing r with
  | zero =>
    have table : rows.all (fun x =>
        decide (((after x).map (fun y => (after y).length)).sum + 12 = 11*(after x).length)) = true := by
      decide
    have hd := of_decide_eq_true ((List.all_eq_true.mp table) r hr)
    have g0 : count 0 = fun _ => 1 := rfl
    have g1 : count 1 = fun s => (after s).length := by
      funext s
      simp [step 0, g0]
    simpa only [step 1 r, g1, g0, Nat.mul_one] using hd
  | succ n ih =>
    rw [step (n+2) r, step n r, step (n+1) r]
    exact sum_relation _ _ _ _ (fun s hs => ih s (List.mem_filter.mp hs).1)

private lemma recurrence (n : ℕ) : a (n+3) + 12*a (n+1) = 11*a (n+2) := by
  rw [totals (n+2), totals n, totals (n+1)]
  exact sum_relation _ _ _ _ (rows_rec n)

set_option maxRecDepth 8192 in
private lemma initial : a 0 = 0 ∧ a 1 = 36 ∧ a 2 = 324 := by decide +kernel

private lemma series :
    (1 - 11*X + 12*X^2) * (mk (fun n => (a n : ℚ))) = 36*X*(1-2*X) := by
  let F := mk (fun n => (a n : ℚ))
  have h : F - C (11:ℚ)*(F*X) + C (12:ℚ)*((F*X)*X) =
      C (36:ℚ)*X - C (72:ℚ)*X^2 := by
    ext k
    by_cases hk : k ≤ 2
    · interval_cases k <;> norm_num [F, coeff_C_mul, coeff_succ_mul_X, coeff_X, coeff_X_pow,
        coeff_zero_eq_constantCoeff, initial.1, initial.2.1, initial.2.2]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j+3 := ⟨k-3, by omega⟩
      have hr : (a (j+3) : ℚ) + 12*(a (j+1) : ℚ) = 11*(a (j+2) : ℚ) := by
        exact_mod_cast recurrence j
      simp [F, coeff_C_mul, coeff_succ_mul_X, coeff_X_pow]
      linarith
  change (1 - 11*X + 12*X^2) * F = _
  simp only [map_ofNat] at h
  linear_combination h

private lemma power_rec (z : ℝ) (hz : z^2+12=11*z) (n : ℕ) :
    z^(n+3)+12*z^(n+1)=11*z^(n+2) := by
  simp only [show n+3=(n+1)+2 by omega, show n+2=(n+1)+1 by omega, pow_add, pow_one]
  linear_combination (z^n*z)*hz

private lemma closed_rec (n : ℕ) :
    closedValue (n+3) + 12*closedValue (n+1) = 11*closedValue (n+2) := by
  let s := Real.sqrt 73
  have hs : s^2 = 73 := Real.sq_sqrt (by norm_num)
  have hu : ((11-s)/2)^2+12 = 11*((11-s)/2) := by nlinarith
  have hv : ((11+s)/2)^2+12 = 11*((11+s)/2) := by nlinarith
  unfold closedValue
  linear_combination (3/s*(s-1))*power_rec _ hu n + (3/s*(s+1))*power_rec _ hv n

private lemma closed (n : ℕ) : (a (n+1) : ℝ) = closedValue (n+1) := by
  have hs : (Real.sqrt 73)^2 = 73 := Real.sq_sqrt (by norm_num)
  have hpos : Real.sqrt 73 ≠ 0 := by positivity
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [initial.2.1]
    unfold closedValue
    norm_num
    field_simp
    ring
  | one =>
    rw [initial.2.2]
    unfold closedValue
    norm_num
    field_simp
    nlinarith [congrArg (fun x : ℝ => x * Real.sqrt 73) hs]
  | more n ih₀ ih₁ =>
    have hr : (a (n+3) : ℝ) + 12*(a (n+1) : ℝ) = 11*(a (n+2) : ℝ) := by
      exact_mod_cast recurrence n
    linarith [closed_rec n]

end TriangularArrays

theorem OMA.solution : type_of% @OMA.S_oeis_a223299.main :=
  ⟨TriangularArrays.recurrence, TriangularArrays.series, TriangularArrays.closed⟩
