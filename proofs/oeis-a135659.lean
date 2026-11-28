import OMAStatements.S_oeis_a135659

private lemma powmod (n : ℕ) :
    2 ^ (n + 3) % 24 = 8 ∨ 2 ^ (n + 3) % 24 = 16 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 + 3 = n + 3 + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h <;> simp [h]

theorem OMA.solution : type_of% @OMA.S_oeis_a135659.main := by
  rintro m hm ⟨p, rfl⟩ h
  rcases p with _ | _ | _ | p <;> try omega
  change 3 < 2 ^ (p + 3) - 1 at h
  rcases powmod p with h₈ | h₁₆
  · refine ⟨(2 ^ (p + 3) - 1) / 24, ?_⟩
    change 2 ^ (p + 3) - 1 = 24 * _ + 7
    omega
  · have hd : 3 ∣ 2 ^ (p + 3) - 1 := by omega
    have := hm.eq_one_or_self_of_dvd 3 hd
    omega
