import OMAStatements.S_oeis_a001338

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: first-order relations for a(n) and auxiliary sums (sum splitting, Pascal rule),
-- combined by linear_combination into the stated recurrence.

open OMA.S_oeis_a001338

namespace P_oeis_a001338

def b (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, (k.factorial : ℤ) * (n.choose (k + 1) : ℤ)

def e (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), (k.factorial : ℤ) * (n.choose k : ℤ)

lemma a_eq (n : ℕ) : a (n + 1) = -1 + b (n + 1) := by
  unfold a b
  simp only [Nat.add_one_ne_zero, if_false]
  congr 1
  have hI : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 1 + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  have hn : n + 1 + 1 - 1 = n + 1 := by omega
  rw [hn]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Nat.add_sub_cancel_left, add_comm 1 k]

lemma b_succ (n : ℕ) : b (n + 1) = b n + e n := by
  unfold b e
  have key : ∀ k ∈ Finset.range (n + 1),
      (k.factorial : ℤ) * ((n + 1).choose (k + 1) : ℤ)
        = (k.factorial : ℤ) * (n.choose k : ℤ) + (k.factorial : ℤ) * (n.choose (k + 1) : ℤ) := by
    intro k _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib,
    Finset.sum_range_succ (fun k => (k.factorial : ℤ) * (n.choose (k + 1) : ℤ)) n]
  simp only [Nat.choose_succ_self, Nat.cast_zero, mul_zero, add_zero]
  ring

lemma e_succ (n : ℕ) : e (n + 1) = ((n : ℤ) + 1) * e n + 1 := by
  unfold e
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have key : ∀ k ∈ Finset.range (n + 1),
      ((k + 1).factorial : ℤ) * ((n + 1).choose (k + 1) : ℤ)
        = ((n : ℤ) + 1) * ((k.factorial : ℤ) * (n.choose k : ℤ)) := by
    intro k _
    have := Nat.add_one_mul_choose_eq n k
    have h3 : (((n + 1) * n.choose k : ℕ) : ℤ) = (((n + 1).choose (k + 1) * (k + 1) : ℕ) : ℤ) := by
      rw [this]
    rw [Nat.factorial_succ]
    push_cast at h3 ⊢
    linear_combination (-(k.factorial : ℤ)) * h3
  rw [Finset.sum_congr rfl key]
  simp

theorem main_proved : ∀ n : ℕ, 4 ≤ n →
    a n + (-(n : ℤ) - 1) * a (n - 1) + 2 * ((n : ℤ) - 1) * a (n - 2) + (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 2 + 1 := by omega
  have e2 : m + 4 - 2 = m + 1 + 1 := by omega
  have e3 : m + 4 - 3 = m + 1 := by omega
  have e4 : m + 4 = m + 3 + 1 := by omega
  rw [e1, e2, e3, e4, a_eq, a_eq, a_eq, a_eq]
  have b1 := b_succ (m + 1)
  have b2 := b_succ (m + 2)
  have b3 := b_succ (m + 3)
  have c1 := e_succ (m + 1)
  have c2 := e_succ (m + 2)
  push_cast at b1 b2 b3 c1 c2 ⊢
  linear_combination b3 + c2 - ((m : ℤ) + 4) * b2 - c1 + ((m : ℤ) + 2) * b1

end P_oeis_a001338

theorem OMA.solution : type_of% @OMA.S_oeis_a001338.main := P_oeis_a001338.main_proved
