import OMAStatements.S_oeis_a056084

open OMA.S_oeis_a056084 in
theorem OMA.solution : type_of% @OMA.S_oeis_a056084.main := by
  set P := fun k : ℕ => k ^ 8 % 9 ^ 3 = 1
  have per (q k : ℕ) : P (729 * q + k) ↔ P k := by
    show _ % 729 = 1 ↔ _ % 729 = 1
    rw [Nat.pow_mod, Nat.mul_add_mod, ← Nat.pow_mod]
  have d (q r : ℕ) : Nat.count P (729 * q + r) = Nat.count P (729 * q) + Nat.count P r := by
    simp only [Nat.count_add, per]
  have e (q : ℕ) : Nat.count P (729 * q) = 2 * q := by
    induction q with
    | zero => simp
    | succ q ih => rw [mul_add_one, d, ih, show Nat.count P 729 = 2 by decide +kernel]; ring
  intro n hn
  obtain ⟨j, rfl | rfl⟩ : ∃ j, n = 2 * j + 1 ∨ n = 2 * j + 2 := ⟨(n - 1) / 2, by omega⟩
  · rw [a, show 2 * j + 1 - 1 = Nat.count P (729 * j + 1) by rw [d, e, show Nat.count P 1 = 0 by decide]; rfl,
      Nat.nth_count ((per j 1).2 (by decide))]
    push_cast
    rw [pow_succ, pow_mul]
    norm_num
    ring
  · rw [a, show 2 * j + 2 - 1 = Nat.count P (729 * j + 728) by rw [d, e, show Nat.count P 728 = 1 by decide +kernel]; rfl,
      Nat.nth_count ((per j 728).2 (by decide))]
    push_cast
    rw [pow_succ, pow_succ, pow_mul]
    norm_num
    ring
