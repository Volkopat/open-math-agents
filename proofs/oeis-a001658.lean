import OMAStatements.S_oeis_a001658

/-!
# A001658: the nested sum for the sixth Fibonomial column

Source: the formula proposed by Dale Gerdemann on the OEIS entry A001658,
8 May 2016, as formalized by @Dugongue. The Fibonacci addition identity
gives an inhomogeneous recurrence between adjacent Fibonomial columns.
Unrolling it from the sixth column down to the first gives the five sums.
-/

namespace Fibnom

def col : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | k + 1, d + 1 =>
      Nat.fib (k + 2) * col (k + 1) d + Nat.fib d * col k (d + 1)
termination_by k d => k + d

theorem col_zero (k : ℕ) : col k 0 = 1 := by
  cases k <;> rw [col]

theorem col_step (k d : ℕ) :
    col (k + 1) (d + 1) = Nat.fib (k + 2) * col (k + 1) d + Nat.fib d * col k (d + 1) := by
  rw [col]

theorem col_one (d : ℕ) : col 1 d = Nat.fib (d + 1) := by
  induction d with
  | zero => simp [col_zero]
  | succ d ih =>
    rw [col_step 0, ih, Nat.fib_add_two (n := d)]
    simp [col, add_comm]

def segment : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, d => Nat.fib (d + 1) * segment k (d + 1)

theorem segment_right (k d : ℕ) :
    segment (k + 1) d = segment k d * Nat.fib (d + k + 1) := by
  induction k generalizing d with
  | zero => simp [segment]
  | succ k ih =>
    rw [segment, ih (d + 1), segment, Nat.mul_assoc]
    rw [show d + 1 + k + 1 = d + (k + 1) + 1 by omega]

theorem segment_eq (k d : ℕ) : segment k 0 * col k d = segment k d := by
  induction k generalizing d with
  | zero => simp [segment, col]
  | succ k ih =>
    induction d with
    | zero => rw [col_zero, mul_one]
    | succ d ihd =>
      have hseg := segment_right k 0
      simp only [Nat.zero_add] at hseg
      change segment (k + 1) 0 * col (k + 1) d =
        Nat.fib (d + 1) * segment k (d+1) at ihd
      rw [col_step, segment_right k (d+1),
        show d + 1 + k + 1 = d + (k + 1) + 1 by omega, Nat.fib_add d (k+1)]
      linear_combination Nat.fib (k+2) * ihd + Nat.fib d * Nat.fib (k+1) * ih (d+1) +
        Nat.fib d * col k (d+1) * hseg

theorem a_eq_col (n : ℕ) (h : 6 ≤ n) : OMA.S_oeis_a001658.a n = col 6 (n-6) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [show 6 + d - 6 = d by omega]
  have eqden : (∏ r ∈ Finset.Icc 1 6, Nat.fib r) = segment 6 0 := by decide
  have pos : 0 < segment 6 0 := by decide
  have eqnum : (∏ r ∈ Finset.range 6, Nat.fib (6+d-r)) = segment 6 d := by
    simp (disch := omega) [Finset.prod_range_succ, segment, Nat.add_comm 6 d,
      Nat.add_sub_assoc, Nat.add_assoc]
    ac_rfl
  rw [OMA.S_oeis_a001658.a, eqden, eqnum, ← segment_eq, Nat.mul_div_cancel_left _ pos]

end Fibnom

namespace FibnomUnroll

theorem sum_row (row : ℕ → ℕ → ℕ)
    (base : ∀ k, row k 1 = 1)
    (step : ∀ k s, 2 ≤ k → 1 ≤ s → row k (s+1) =
      Nat.fib (k+1) * row k s + Nat.fib (s-1) * row (k-1) (s+1)) :
    ∀ k s, 2 ≤ k → 1 ≤ s →
      row k s = Nat.fib (k+1)^(s-1) +
        ∑ i ∈ Finset.Icc 3 s, Nat.fib (i-2)*row (k-1) i*Nat.fib (k+1)^(s-i) := by
  intro k s hk hs
  induction s with
  | zero => omega
  | succ s ih =>
    by_cases hzero : s = 0
    · subst s
      simp [base]
    have hs' : 1 ≤ s := by omega
    rw [step k s hk hs', ih hs', Nat.mul_add, Finset.mul_sum]
    by_cases hone : s = 1
    · subst s
      simp
    rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ s+1)]
    have ht :
        (∑ i ∈ Finset.Icc 3 s, Nat.fib (k+1) * (Nat.fib (i-2) * row (k-1) i * Nat.fib (k+1)^(s-i))) =
        ∑ i ∈ Finset.Icc 3 s, Nat.fib (i-2) * row (k-1) i * Nat.fib (k+1)^(s+1-i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have := (Finset.mem_Icc.mp hi).2
      rw [show s+1-i = (s-i)+1 by omega, pow_succ]
      ring
    rw [ht]
    rw [show s+1-1 = (s-1)+1 by omega, pow_succ, show s+1-2=s-1 by omega]
    simp only [Nat.sub_self, pow_zero, mul_one]
    ring

end FibnomUnroll

namespace FibnomExpansion

/-- Carry the preceding Fibonacci factors through one row expansion. -/
private theorem weighted {row : ℕ → ℕ → ℕ} {k s : ℕ} (L R : ℕ)
    (h : row k s = Nat.fib (k+1)^(s-1) +
      ∑ t ∈ Finset.Icc 3 s, Nat.fib (t-2) * row (k-1) t * Nat.fib (k+1)^(s-t)) :
    L * row k s * R = L * Nat.fib (k+1)^(s-1) * R +
      ∑ t ∈ Finset.Icc 3 s,
        (L * Nat.fib (t-2)) * row (k-1) t * (Nat.fib (k+1)^(s-t) * R) := by
  rw [h]
  simp only [Nat.mul_add, Nat.add_mul, Finset.mul_sum, Finset.sum_mul, Nat.mul_assoc]

theorem expand (row : ℕ → ℕ → ℕ)
    (step : ∀ k s, 2 ≤ k → 1 ≤ s →
      row k s = Nat.fib (k+1)^(s-1) +
        ∑ t ∈ Finset.Icc 3 s, Nat.fib (t-2) * row (k-1) t * Nat.fib (k+1)^(s-t))
    (one : ∀ s, 1 ≤ s → row 1 s = Nat.fib s)
    (six : ∀ n, 6 ≤ n → OMA.S_oeis_a001658.a n = row 6 (n-5)) :
    type_of% @OMA.S_oeis_a001658.main := by
  intro n hn
  rw [six n hn, step 6 (n-5) (by decide) (by omega)]
  apply congrArg₂ Nat.add
  · rw [show n-5-1 = n-6 by omega]
  apply Finset.sum_congr rfl
  intro i hi
  have hi₃ := (Finset.mem_Icc.mp hi).1
  rw [show n-5-i = n-i-5 by omega, weighted _ _ (step 5 i (by decide) (by omega))]
  apply congrArg₂ Nat.add
  · rfl
  apply Finset.sum_congr rfl
  intro j hj
  have hj₃ := (Finset.mem_Icc.mp hj).1
  rw [weighted _ _ (step 4 j (by decide) (by omega))]
  apply congrArg₂ Nat.add
  · simp only [Nat.mul_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  have hk₃ := (Finset.mem_Icc.mp hk).1
  rw [weighted _ _ (step 3 k (by decide) (by omega))]
  apply congrArg₂ Nat.add
  · simp only [Nat.mul_assoc]
  apply Finset.sum_congr rfl
  intro l hl
  have hl₃ := (Finset.mem_Icc.mp hl).1
  rw [weighted _ _ (step 2 l (by decide) (by omega))]
  apply congrArg₂ Nat.add
  · simp only [Nat.mul_assoc]
  apply Finset.sum_congr rfl
  intro m hm
  have hm₃ := (Finset.mem_Icc.mp hm).1
  rw [one m (by omega)]
  simp only [Nat.mul_assoc]

end FibnomExpansion

open OMA.S_oeis_a001658 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001658.main := by
  let row := fun k s : ℕ => Fibnom.col k (s-1)
  apply FibnomExpansion.expand row
  · apply FibnomUnroll.sum_row
    · intro k
      exact Fibnom.col_zero k
    · intro k s hk hs
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
      simpa [row] using Fibnom.col_step j d
  · intro s hs
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    exact Fibnom.col_one d
  · intro n hn
    simpa [row, Nat.sub_sub] using Fibnom.a_eq_col n hn
