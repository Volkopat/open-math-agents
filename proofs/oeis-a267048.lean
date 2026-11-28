import OMAStatements.S_oeis_a267048

/-! Barker's formulas for Rule 91 follow from a two-row cycle on the full integer line. -/

namespace Rule91

open OMA.S_oeis_a267048 Finset

def oddRow (i : ℤ) : Bool := decide (i < -1 ∨ 1 < i)
def evenRow (i : ℤ) : Bool := decide (-2 ≤ i ∧ i ≤ 2)

lemma row_three (i : ℤ) : cell 91 3 i = oddRow i := by
  by_cases hl : i < -3
  · simp (disch := omega) only [cell, oddRow, decide_eq_true, decide_eq_false]
    decide
  by_cases hr : 3 < i
  · simp (disch := omega) only [cell, oddRow, decide_eq_true, decide_eq_false]
    decide
  interval_cases i <;> decide

lemma step_odd (i : ℤ) :
    ruleOut 91 (oddRow (i-1)) (oddRow i) (oddRow (i+1)) = evenRow i := by
  by_cases hl : i < -3
  · simp (disch := omega) only [oddRow, evenRow, decide_eq_true, decide_eq_false]
    decide
  by_cases hr : 3 < i
  · simp (disch := omega) only [oddRow, evenRow, decide_eq_true, decide_eq_false]
    decide
  interval_cases i <;> decide

lemma step_even (i : ℤ) :
    ruleOut 91 (evenRow (i-1)) (evenRow i) (evenRow (i+1)) = oddRow i := by
  by_cases hl : i < -3
  · simp (disch := omega) only [oddRow, evenRow, decide_eq_true, decide_eq_false]
    decide
  by_cases hr : 3 < i
  · simp (disch := omega) only [oddRow, evenRow, decide_eq_true, decide_eq_false]
    decide
  interval_cases i <;> decide

theorem phase (k : ℕ) (i : ℤ) :
    cell 91 (k+3) i = if k%2=0 then oddRow i else evenRow i := by
  induction k generalizing i with
  | zero => simpa using row_three i
  | succ k ih =>
    change ruleOut 91 (cell 91 (k+3) (i-1)) (cell 91 (k+3) i) (cell 91 (k+3) (i+1)) = _
    rw [ih, ih, ih]
    by_cases h : k%2=0
    · have h' : (k+1)%2 ≠ 0 := by omega
      simpa only [if_pos h, if_neg h'] using step_odd i
    · have h' : (k+1)%2 = 0 := by omega
      simpa only [if_neg h, if_pos h'] using step_even i

lemma window (n d : ℕ) (h : d ≤ n) :
    (∑ j ∈ range (2*n+1), if -(d : ℤ) ≤ (j : ℤ)-n ∧ (j : ℤ)-n ≤ d
      then (1 : ℕ) else 0) = 2*d+1 := by
  rw [sum_boole]
  have e : (range (2*n+1)).filter (fun j : ℕ => -(d : ℤ) ≤ (j : ℤ)-n ∧ (j : ℤ)-n ≤ d)
      = Icc (n-d) (n+d) := by
    ext j
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  rw [e, Nat.card_Icc]
  change n+d+1-(n-d)=2*d+1
  omega

theorem count (n : ℕ) (hn : 3 ≤ n) :
    a n = if n%2=1 then 3 else 2*(n : ℤ)-4 := by
  have hc (i : ℤ) := phase (n-3) i
  simp only [Nat.sub_add_cancel hn] at hc
  by_cases h : n%2=1
  · have hr (i : ℤ) : cell 91 n i = oddRow i := by
      simpa (disch := omega) only [if_pos] using hc i
    have w := window n 1 (by omega)
    have e : onCount 91 n + 3 = 2*n+1 := by
      unfold onCount
      rw [show (3 : ℕ) = 2*1+1 by decide, ← w, ← sum_add_distrib]
      calc
        _ = ∑ _j ∈ range (2*n+1), (1 : ℕ) := by
          apply sum_congr rfl
          intro j hj
          rw [hr]
          by_cases inside : -(1 : ℤ) ≤ (j : ℤ)-n ∧ (j : ℤ)-n ≤ 1
          · have outside : ¬ ((j : ℤ)-n < -1 ∨ 1 < (j : ℤ)-n) := by omega
            simp only [oddRow, decide_eq_false outside, Nat.cast_one, if_pos inside]
            decide
          · have outside : (j : ℤ)-n < -1 ∨ 1 < (j : ℤ)-n := by omega
            simp only [oddRow, decide_eq_true outside, Nat.cast_one, if_neg inside]
            decide
        _ = 2*n+1 := by simp
    rw [if_pos h, a]
    omega
  · have hr (i : ℤ) : cell 91 n i = evenRow i := by
      simpa (disch := omega) only [if_neg] using hc i
    have e : onCount 91 n = 5 := by
      simpa only [onCount, hr, evenRow, decide_eq_true_eq, Nat.cast_ofNat] using window n 2 (by omega)
    rw [if_neg h, a, e]
    omega

end Rule91

namespace Rule91

open OMA.S_oeis_a267048 PowerSeries

theorem closed (n : ℕ) (hn : 3 ≤ n) :
    (a n : ℚ) = (2*(-1 : ℚ)^n*(n : ℚ)+2*(n : ℚ)-7*(-1 : ℚ)^n-1)/2 := by
  rw [count n hn]
  by_cases h : n%2=1
  · have p : (-1 : ℚ)^n = -1 := by
      rw [show n=2*(n/2)+1 by omega, pow_succ, pow_mul]
      norm_num
    rw [if_pos h, p]
    push_cast
    ring
  · have p : (-1 : ℚ)^n = 1 := by
      rw [show n=2*(n/2) by omega, pow_mul]
      norm_num
    rw [if_neg h, p]
    push_cast
    ring

theorem recurrence (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 2*(a (n-2) : ℚ)-(a (n-4) : ℚ) := by
  rw [count n (by omega), count (n-2) (by omega), count (n-4) (by omega)]
  by_cases h : n%2=1
  · simp (disch := omega) only [if_pos]
    norm_num
  · simp (disch := omega) only [if_neg]
    push_cast [Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega)]
    ring

theorem generating :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1-X)^2*(1+X)^2 : PowerSeries ℚ) =
      X*(1+3*X+X^2-2*X^3-2*X^4+3*X^5) := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hd : F*((1-X)^2*(1+X)^2) = F-F*X^2-F*X^2+F*X^4 := by ring
  have hp : (X*(1+3*X+X^2-2*X^3-2*X^4+3*X^5) : PowerSeries ℚ) =
      C 1*X^1+C 3*X^2+C 1*X^3-C 2*X^4-C 2*X^5+C 3*X^6 := by
    simp only [map_one,map_ofNat]
    ring
  rw [hd,hp]
  ext n
  simp only [map_sub,map_add,coeff_mul_X_pow',coeff_C,coeff_mk,F]
  by_cases hn : 7 ≤ n
  · have h := recurrence n hn
    simp (disch := omega) only [if_pos,if_neg]
    linarith
  · have h0 : a 0 = 0 := by decide
    have h1 : a 1 = 1 := by decide
    have h2 : a 2 = 3 := by decide
    have h3 : a 3 = 3 := by decide
    have h4 : a 4 = 4 := by decide
    have h5 : a 5 = 3 := by decide
    have h6 : a 6 = 8 := by decide
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,h6]

end Rule91

theorem OMA.solution : type_of% @OMA.S_oeis_a267048.main :=
  ⟨Rule91.closed, Rule91.recurrence, Rule91.generating⟩
