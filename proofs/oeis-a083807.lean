import OMAStatements.S_oeis_a083807

namespace OMA.S_oeis_a083807

/-- Squaring a number with just two digits equal to 2 gives three nonzero
digits, with the same spacing. -/
private theorem squareDigits (k : ℕ) :
    Nat.digits 10 ((2 + 20 * 10 ^ k) ^ 2) =
      4 :: (List.replicate k 0 ++ 8 :: (List.replicate k 0 ++ [4])) := by
  have expand : (2 + 20 * 10 ^ k) ^ 2 =
      4 + 10 * (10 ^ k * (8 + 10 * (10 ^ k * 4))) := by ring
  rw [expand, Nat.digits_add 10 (by decide) 4 _ (by decide) (Or.inl (by decide)),
    Nat.digits_base_pow_mul (by decide : 1 < 10) (by positivity),
    Nat.digits_add 10 (by decide) 8 _ (by decide) (Or.inl (by decide)),
    Nat.digits_base_pow_mul (by decide : 1 < 10) (by decide : 0 < 4),
    Nat.digits_of_lt 10 4 (by decide) (by decide)]

end OMA.S_oeis_a083807

theorem OMA.solution : type_of% @OMA.S_oeis_a083807.main := by
  apply Set.infinite_of_forall_exists_gt
  intro k
  refine ⟨(2 + 20 * 10 ^ k) ^ 2, ⟨⟨⟨2 + 20 * 10 ^ k, 2, by omega, by decide, rfl⟩, ?_⟩, ?_⟩, ?_⟩
  · intro d hd
    rw [OMA.S_oeis_a083807.squareDigits] at hd
    simp only [List.mem_cons, List.mem_append, List.mem_replicate] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · rintro ⟨j, m, hj, _, heq⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    have hmod := congrArg (fun x : ℕ => x % 10) heq
    simp [pow_succ, Nat.add_mod, Nat.mul_mod] at hmod
  · have hbound : k < 10 ^ k := Nat.lt_pow_self (by decide)
    nlinarith [Nat.zero_le (10 ^ k)]
