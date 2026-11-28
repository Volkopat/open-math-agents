import OMAReductions.R_Arxiv_2107_12475_CollatzLike_R1
import Mathlib

/-! Since `2` has order `162` modulo `3 ^ 5 = 243`, the five lowest ternary digits of `2 ^ n`
depend only on `n % 162`; outside the sixteen listed classes one of them is `2` (a finite table). -/

namespace OMA.Step_Arxiv_2107_12475_CollatzLike_R1_H1

/-- `2` has order `162` modulo `243`. -/
theorem pow_mod_243 (n : ℕ) : 2 ^ n % 243 = 2 ^ (n % 162) % 243 := by
  conv_lhs => rw [← Nat.div_add_mod n 162, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod]
  norm_num

/-- The ternary digit `i < 5` of `m` depends only on `m % 243`. -/
theorem digit_mod (m i : ℕ) (hi : i < 5) : m / 3 ^ i % 3 = m % 243 / 3 ^ i % 3 := by
  have hd : 3 ^ i * 3 ∣ 243 := by
    rw [← pow_succ]
    exact Nat.pow_dvd_pow 3 (by omega : i + 1 ≤ 5) |>.trans (by norm_num)
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self (m % 243), Nat.mod_mod_of_dvd _ hd]

/-- A nonzero digit is a member of the digit list. -/
theorem mem_digits {m i : ℕ} (h : m / 3 ^ i % 3 = 2) : 2 ∈ Nat.digits 3 m := by
  have hg := Nat.getD_digits m i (b := 3) (by norm_num)
  rw [h] at hg
  have hlt : i < (Nat.digits 3 m).length := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by omega)] at hg
    omega
  rw [List.getD_eq_getElem _ _ hlt] at hg
  exact hg ▸ List.getElem_mem hlt

theorem table : ∀ r : ℕ, r < 162 →
    r ∈ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ) ∨
      ∃ i : ℕ, i < 5 ∧ 2 ^ r % 243 / 3 ^ i % 3 = 2 := by
  decide +kernel

theorem settled (n : ℕ) (_hn : 8 < n)
    (hS : n % 162 ∉ ({0, 2, 8, 20, 24, 26, 54, 56, 62, 72, 74, 78, 80, 96, 126, 150} : Finset ℕ)) :
    2 ∈ Nat.digits 3 (2 ^ n) := by
  obtain ⟨i, hi, h⟩ := (table (n % 162) (Nat.mod_lt _ (by norm_num))).resolve_left hS
  apply mem_digits (i := i)
  rw [digit_mod _ _ hi, pow_mod_243]
  exact h

end OMA.Step_Arxiv_2107_12475_CollatzLike_R1_H1

theorem OMA.solution : OMA.R_Arxiv_2107_12475_CollatzLike_R1.H1 :=
  OMA.Step_Arxiv_2107_12475_CollatzLike_R1_H1.settled
