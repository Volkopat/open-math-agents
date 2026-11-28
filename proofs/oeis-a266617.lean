import OMAStatements.S_oeis_a266617
import Mathlib

namespace OMA.Rule41
open OMA.S_oeis_a266617 Finset PowerSeries

private theorem background (t : ℕ) (i : ℤ) (h : i < -(t : ℤ) ∨ (t : ℤ) < i) :
    cell 41 t i = decide (t % 2 = 1) := by
  induction t generalizing i with
  | zero => simp [cell, show i ≠ 0 by omega]
  | succ t ih =>
    simp only [cell, ih (i-1) (by omega), ih i (by omega), ih (i+1) (by omega)]
    by_cases hp : t % 2 = 1
    · simp [hp, show (t+1)%2 ≠ 1 by omega, ruleOut]; decide
    · simp [hp, show (t+1)%2 = 1 by omega, ruleOut]

private theorem shift (t : ℕ) (i : ℤ) : cell 41 (t+4) i = cell 41 t (i-4) := by
  induction t generalizing i with
  | zero =>
    by_cases h : -4 ≤ i ∧ i ≤ 4
    · obtain ⟨h₁,h₂⟩ := h
      interval_cases i <;> decide
    · rw [background 4 i (by omega)]
      simp [cell, show i-4 ≠ 0 by omega]
  | succ t ih =>
    change ruleOut 41 (cell 41 (t+4) (i-1)) (cell 41 (t+4) i) (cell 41 (t+4) (i+1)) = _
    rw [ih, ih, ih]
    change ruleOut 41 _ _ _ = ruleOut 41 (cell 41 t (i-4-1)) (cell 41 t (i-4)) (cell 41 t (i-4+1))
    rw [show i-1-4 = i-4-1 by omega, show i+1-4 = i-4+1 by omega]

private theorem plusFour (t : ℕ) :
    onCount 41 (t+4) = (if t % 2 = 1 then 8 else 0) + onCount 41 t := by
  unfold onCount
  rw [show 2 * (t+4)+1 = 8+(2*t+1) by omega, sum_range_add]
  congr 1
  · trans ∑ j ∈ range 8, (if t%2=1 then 1 else 0 : ℕ)
    · apply sum_congr rfl
      intro j hj
      have hj' := mem_range.mp hj
      rw [shift, background _ _ (by push_cast; omega)]
      simp
    · by_cases h : t%2=1 <;> simp [h]
  · apply sum_congr rfl
    intro j hj
    rw [shift]
    rw [show ((8+j : ℕ) : ℤ) - (t+4 : ℕ) - 4 = (j : ℤ) - t by push_cast; ring]

private def off (t : ℕ) : ℤ := (2*t+1 : ℤ) - onCount 41 t

private theorem offStep (t : ℕ) : off (t+4) = off t + (if t%2=1 then 0 else 8) := by
  simp only [off, plusFour, Nat.cast_add]
  by_cases h : t%2=1 <;> simp [h] <;> ring

private theorem recur (n : ℕ) (hn : 6 ≤ n) :
    (off n : ℚ) = off (n-2) + off (n-4) - off (n-6) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+6 := ⟨n-6,by omega⟩
  have h := offStep (k+2)
  have g := offStep k
  have e : (k+2)%2 = k%2 := by omega
  simp only [e, show k+2+4 = k+6 by omega] at h
  exact_mod_cast (show off (k+6) = off (k+4) + off (k+2) - off k by linarith only [h,g])

private theorem generating :
    mk (fun n => (off n : ℚ)) * ((1-X)^2*(1+X)^2*(1+X^2)) =
      X*(3+3*X+X^2+5*X^3-4*X^4) := by
  let S := mk (fun n => (off n : ℚ))
  change S * _ = _
  have lhs : S * ((1-X)^2*(1+X)^2*(1+X^2)) = S-S*X^2-S*X^4+S*X^6 := by ring
  have rhs : (X*(3+3*X+X^2+5*X^3-4*X^4) : PowerSeries ℚ) =
      (3:ℕ) • X^1 + (3:ℕ) • X^2 + X^3 + (5:ℕ) • X^4 - (4:ℕ) • X^5 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 6 ≤ n
  · simp (disch := omega) only [if_pos,if_neg, nsmul_eq_mul]
    linarith only [recur n h]
  · have a0 : off 0 = 0 := by decide
    have a1 : off 1 = 3 := by decide
    have a2 : off 2 = 3 := by decide
    have a3 : off 3 = 4 := by decide
    have a4 : off 4 = 8 := by decide
    have a5 : off 5 = 3 := by decide
    interval_cases n <;> norm_num [a0,a1,a2,a3,a4,a5]

private theorem diff (n : ℕ) : a (n+1) = a n + off (n+1) := by
  unfold a off
  rw [sum_range_succ]

private theorem totalGF :
    PowerSeries.mk (fun n => (a n : ℚ)) * (1-X) = PowerSeries.mk (fun n => (off n : ℚ)) := by
  let S := mk (fun n => (a n : ℚ))
  change S * _ = _
  rw [mul_sub, mul_one, ← pow_one (X : PowerSeries ℚ)]
  ext n
  simp only [map_sub, coeff_mul_X_pow', S, coeff_mk]
  cases n with
  | zero => norm_num [a,off]
  | succ n =>
    simp only [Nat.le_add_left, if_true, Nat.add_one_sub_one]
    exact_mod_cast (show a (n+1) - a n = off (n+1) by rw [diff]; ring)

private theorem totalRec (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = a (n-1) + a (n-2) - a (n-3) + a (n-4) - a (n-5) - a (n-6) + a (n-7) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+7 := ⟨n-7,by omega⟩
  have h := recur (k+7) (by omega)
  simp only [Nat.add_sub_cancel, show k+7-2 = k+5 by omega,
    show k+7-4 = k+3 by omega, show k+7-6 = k+1 by omega] at h
  have e₀ := diff k
  have e₂ := diff (k+2)
  have e₄ := diff (k+4)
  have e₆ := diff (k+6)
  push_cast at h
  have hr : off (k+7) = off (k+5) + off (k+3) - off (k+1) := by exact_mod_cast h
  change (a (k+7) : ℚ) = a (k+6) + a (k+5) - a (k+4) + a (k+3) - a (k+2) - a (k+1) + a k
  exact_mod_cast (show a (k+7) = a (k+6) + a (k+5) - a (k+4) + a (k+3) - a (k+2) - a (k+1) + a k by
    change a (k+3) = a (k+2) + off (k+3) at e₂
    change a (k+5) = a (k+4) + off (k+5) at e₄
    change a (k+7) = a (k+6) + off (k+7) at e₆
    linarith only [hr,e₀,e₂,e₄,e₆])

end OMA.Rule41

open PowerSeries OMA.S_oeis_a266617 in
theorem OMA.solution : type_of% @OMA.S_oeis_a266617.main := by
  refine ⟨OMA.Rule41.totalRec,?_⟩
  rw [show ((1-X)^3 * (1+X)^2 * (1+X^2) : PowerSeries ℚ) =
    (1-X)*((1-X)^2*(1+X)^2*(1+X^2)) by ring, ← mul_assoc, OMA.Rule41.totalGF]
  exact OMA.Rule41.generating
