import OMAStatements.S_oeis_a053922
open OMA.S_oeis_a053922
-- Harvey P. Dale's conjecture on OEIS A053922, using Zhao Hui Du's square pattern.
theorem OMA.solution : type_of% @OMA.S_oeis_a053922.main := by
  intro n d hd
  have h (k d : ℕ) : Nat.ofDigits 10 (List.replicate k d) * 9 + d = d * 10 ^ k := by
    induction k <;> simp [List.replicate_succ, Nat.ofDigits_cons, pow_succ] <;> linarith
  have m : ∀ x ∈ 4 :: (List.replicate n 2 ++ 6 :: List.replicate n 4), x = 2 ∨ x = 4 ∨ x = 6 := by
    intro x hx; simp at hx; omega
  have e : sixesEight n ^ 2 = Nat.ofDigits 10 (4 :: (List.replicate n 2 ++ 6 :: List.replicate n 4)) := by
    have h1 := h n 1
    have h2 := h n 2
    have h4 := h n 4
    simp only [sixesEight, Nat.ofDigits_cons, Nat.ofDigits_append, List.length_replicate]
    generalize Nat.ofDigits 10 (List.replicate n 1) = R at *
    generalize Nat.ofDigits 10 (List.replicate n 2) = A at *
    generalize Nat.ofDigits 10 (List.replicate n 4) = B at *
    obtain rfl : A = 2 * R := by omega
    obtain rfl : B = 4 * R := by omega
    rw [show 10 ^ n = 9 * R + 1 by omega, show (9 * R + 1 - 1) / 9 = R by omega]
    ring
  rw [e, Nat.digits_ofDigits 10 (by norm_num)] at hd
  · exact m d hd
  · intro x hx; have := m x hx; omega
  · intro h; have := m _ (List.getLast_mem h); omega
