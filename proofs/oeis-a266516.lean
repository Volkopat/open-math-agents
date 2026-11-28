import OMAStatements.S_oeis_a266516

namespace OMA.A266516Proof
open OMA.S_oeis_a266516

def P (t : ℕ) (x : ℤ) : Bool :=
  if t % 2 = 0 then (if x = 0 then true else false) else (if x = -1 then false else true)

theorem S (t : ℕ) : ∀ x, state 29 t x = P t x := by
  induction t with
  | zero => intro x; simp [state, P]
  | succ t ih =>
    intro x
    simp only [state, step, ih, P]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem V (n : ℕ) : (a n : ℚ) = ∑ i ∈ Finset.range (2 * n + 1), if P n ((n : ℤ) - i) then (2 : ℚ) ^ i else 0 := by
  simp only [a, rowValue, S]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  cases P n ((n : ℤ) - i) <;> simp

theorem E (n : ℕ) (h : Even n) : (a n : ℚ) = 2 ^ n := by
  rw [V, Finset.sum_eq_single n]
  · simp [P, Nat.even_iff.1 h]
  · intro i _ hi
    simp [P, Nat.even_iff.1 h, sub_eq_zero, Ne.symm hi]
  · intro hn; simp at hn; omega

theorem O (n : ℕ) (h : Odd n) : (a n : ℚ) = 2 * (4 ^ n - 2 ^ n) - 1 := by
  have hn : n % 2 = 1 := Nat.odd_iff.1 h
  have hn1 : 1 ≤ n := h.pos
  rw [V]
  have e : ∀ i ∈ Finset.range (2 * n + 1),
      (if P n ((n : ℤ) - i) then (2 : ℚ) ^ i else 0) = 2 ^ i - if i = n + 1 then 2 ^ i else 0 := by
    intro i _
    by_cases hi : i = n + 1
    · subst hi; simp [P, hn]
    · simp [P, hn, hi, show ¬ ((n : ℤ) - i = -1) by omega]
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (by simp; omega),
    geom_sum_eq (by norm_num), show (4 : ℚ) ^ n = 2 ^ (2 * n) by rw [pow_mul]; norm_num]
  ring

end OMA.A266516Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a266516.main := ⟨OMA.A266516Proof.O, OMA.A266516Proof.E⟩
