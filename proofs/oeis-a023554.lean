import OMAStatements.S_oeis_a023554

namespace OMA.P023554

open OMA.S_oeis_a023554 Finset

/-- Fibonacci numbers as integers. -/
def f (n : ℕ) : ℤ := (Nat.fib n : ℤ)

lemma f_add_two (n : ℕ) : f (n + 2) = f n + f (n + 1) := by
  unfold f
  rw [Nat.fib_add_two]
  push_cast
  ring

/-- The reflected form of the convolution. -/
def G (n : ℕ) : ℤ := ∑ j ∈ range n, ((n : ℤ) + 2 - j) * f (j + 2)

/-- Partial sums of the shifted Fibonacci numbers. -/
def P (n : ℕ) : ℤ := ∑ j ∈ range n, f (j + 2)

lemma a_eq_G (n : ℕ) : a n = G n := by
  unfold a G
  rw [← sum_range_reflect]
  refine sum_congr rfl (fun j hj => ?_)
  have hj2 := mem_range.mp hj
  have e1 : n - (n - 1 - j) + 1 = j + 2 := by omega
  have e2 : ((n - 1 - j : ℕ) : ℤ) = (n : ℤ) - 1 - j := by omega
  rw [e1, e2]
  unfold f
  ring

lemma P_closed (n : ℕ) : P n = f (n + 3) - 2 := by
  induction n with
  | zero => simp [P, f, Nat.fib]
  | succ n ih =>
    have h : P (n + 1) = P n + f (n + 2) := sum_range_succ _ _
    have h2 : f (n + 4) = f (n + 2) + f (n + 3) := f_add_two (n + 2)
    rw [h, ih]
    show f (n + 3) - 2 + f (n + 2) = f (n + 4) - 2
    linarith

lemma G_succ (n : ℕ) : G (n + 1) = G n + P n + 3 * f (n + 2) := by
  have h : G (n + 1) = ∑ j ∈ range n, (((n + 1 : ℕ) : ℤ) + 2 - j) * f (j + 2)
      + (((n + 1 : ℕ) : ℤ) + 2 - n) * f (n + 2) := sum_range_succ _ _
  have hc : ∑ j ∈ range n, (((n + 1 : ℕ) : ℤ) + 2 - j) * f (j + 2)
      = ∑ j ∈ range n, (((n : ℤ) + 2 - j) * f (j + 2) + f (j + 2)) := by
    refine sum_congr rfl (fun j _ => ?_)
    push_cast
    ring
  rw [h, hc, sum_add_distrib]
  unfold G P
  push_cast
  ring

lemma G_closed (n : ℕ) : G n = f (n + 5) + 2 * f (n + 3) - (2 * (n : ℤ) + 9) := by
  induction n with
  | zero => simp [G, f, Nat.fib]
  | succ n ih =>
    have h2 : f (n + 4) = f (n + 2) + f (n + 3) := f_add_two (n + 2)
    have h3 : f (n + 5) = f (n + 3) + f (n + 4) := f_add_two (n + 3)
    have h4 : f (n + 6) = f (n + 4) + f (n + 5) := f_add_two (n + 4)
    rw [G_succ, ih, P_closed]
    show _ = f (n + 6) + 2 * f (n + 4) - (2 * ((n + 1 : ℕ) : ℤ) + 9)
    push_cast
    linarith

lemma b_rec (n : ℕ) : A022308 (n + 2) = A022308 (n + 1) + A022308 n + 1 := by
  rw [A022308]

lemma b_closed (n : ℕ) : A022308 n = f (n + 2) + 2 * f n - 1
    ∧ A022308 (n + 1) = f (n + 3) + 2 * f (n + 1) - 1 := by
  induction n with
  | zero => simp [A022308, f, Nat.fib]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have h2 : f (n + 2) = f n + f (n + 1) := f_add_two n
    have h3 : f (n + 3) = f (n + 1) + f (n + 2) := f_add_two (n + 1)
    have h4 : f (n + 4) = f (n + 2) + f (n + 3) := f_add_two (n + 2)
    show A022308 (n + 2) = f (n + 4) + 2 * f (n + 2) - 1
    rw [b_rec]
    linarith

end OMA.P023554

open OMA.S_oeis_a023554 OMA.P023554 in
theorem OMA.solution : type_of% @OMA.S_oeis_a023554.main := by
  intro n
  have hb := (b_closed (n + 4)).1
  have ha : a (n + 1) = f (n + 6) + 2 * f (n + 4) - (2 * ((n + 1 : ℕ) : ℤ) + 9) := by
    rw [a_eq_G, G_closed]
  rw [hb, ha]
  push_cast
  ring
