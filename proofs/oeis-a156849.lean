import OMAStatements.S_oeis_a156849

-- Problem: A156849, numbers k with k^2 == 2 (mod 529): closed form and recurrence.
-- Credit: @ShoQo
-- Proof: k^2 == 2 (mod 529) depends only on k mod 529, and the residues are exactly 156 and
-- 373 (kernel decide on one period). Counting with Nat.count gives a(2j+1) = 529j + 156 and
-- a(2j+2) = 529j + 373, which is the closed form; the recurrence follows from it.

open OMA.S_oeis_a156849

namespace OMA_A156849_Proof

lemma a_eq (n : ℕ) : a n = Nat.nth (fun k => k ^ 2 % 529 = 2) (n - 1) := by
  unfold a; norm_num

lemma sq_mod_shift (j k : ℕ) : (529 * j + k) ^ 2 % 529 = k ^ 2 % 529 := by
  rw [Nat.pow_mod, Nat.mul_add_mod, ← Nat.pow_mod]

lemma count_base : Nat.count (fun k => k ^ 2 % 529 = 2) 529 = 2 ∧
    Nat.count (fun k => k ^ 2 % 529 = 2) 156 = 0 ∧
    Nat.count (fun k => k ^ 2 % 529 = 2) 373 = 1 := by decide +kernel

lemma count_shift (j b : ℕ) : Nat.count (fun k => k ^ 2 % 529 = 2) (529 * j + b)
    = Nat.count (fun k => k ^ 2 % 529 = 2) (529 * j) + Nat.count (fun k => k ^ 2 % 529 = 2) b := by
  rw [Nat.count_add]
  simp only [sq_mod_shift]

lemma count_mul (j : ℕ) : Nat.count (fun k => k ^ 2 % 529 = 2) (529 * j) = 2 * j := by
  induction j with
  | zero => simp
  | succ j ih => rw [show 529 * (j + 1) = 529 * j + 529 by ring, count_shift, ih, count_base.1]; ring

lemma nth_even (j : ℕ) : Nat.nth (fun k => k ^ 2 % 529 = 2) (2 * j) = 529 * j + 156 := by
  have h := Nat.nth_count (p := fun k => k ^ 2 % 529 = 2) (n := 529 * j + 156)
    (by show (529 * j + 156) ^ 2 % 529 = 2; rw [sq_mod_shift]; norm_num)
  rwa [count_shift, count_mul, count_base.2.1, add_zero] at h

lemma nth_odd (j : ℕ) : Nat.nth (fun k => k ^ 2 % 529 = 2) (2 * j + 1) = 529 * j + 373 := by
  have h := Nat.nth_count (p := fun k => k ^ 2 % 529 = 2) (n := 529 * j + 373)
    (by show (529 * j + 373) ^ 2 % 529 = 2; rw [sq_mod_shift]; norm_num)
  rwa [count_shift, count_mul, count_base.2.2] at h

lemma closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = 529 * n / 2 - 529 / 4 - 95 * (-1) ^ n / 4 := by
  rw [a_eq]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show m + 1 - 1 = m by omega]
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · rw [nth_even, show 2 * j + 1 = 2 * j + 1 from rfl, pow_succ, pow_mul]
    push_cast; norm_num; ring
  · rw [nth_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, pow_mul]
    push_cast; norm_num; ring

end OMA_A156849_Proof

open OMA_A156849_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a156849.main := by
  refine ⟨fun n hn => ?_, closed⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [closed _ (by omega), closed _ (by omega), closed _ (by omega), closed _ (by omega),
    show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  push_cast
  rw [pow_succ, pow_succ, pow_succ]
  ring

