import OMAStatements.S_oeis_a100691

namespace OMA.A100691

open OMA.S_oeis_a100691

private theorem change_sign (n : ℕ) :
    tails n (-1) false = tails n 1 false ∧ tails n (-1) true = tails n 1 true := by
  induction n with
  | zero => simp [tails]
  | succ n ih =>
      constructor
      · norm_num [tails, ih.1, ih.2]
        omega
      · norm_num [tails, ih.1]

private theorem zero_step (n : ℕ) :
    tails (n+1) 0 false = tails n 0 false + 2 * tails n 1 true := by
  norm_num [tails, (change_sign n).2]
  omega

private theorem one_step (n : ℕ) :
    tails (n+1) 1 false = tails n 0 false + tails n 1 false + tails n 1 true := by
  norm_num [tails, (change_sign n).1]
  omega

private theorem pending_step (n : ℕ) : tails (n+1) 1 true = tails n 1 false := by
  norm_num [tails, (change_sign n).1]

private theorem words_rec (n : ℕ) : words (n+3) = 2 * words (n+2) + words n := by
  have h0 := zero_step n
  have h1 := zero_step (n+1)
  have h2 := zero_step (n+2)
  have h3 := one_step n
  have h4 := pending_step n
  have h5 := pending_step (n+1)
  change tails (n+2) 0 false = tails (n+1) 0 false + 2*tails (n+1) 1 true at h1
  change tails (n+3) 0 false = tails (n+2) 0 false + 2*tails (n+2) 1 true at h2
  change tails (n+2) 1 true = tails (n+1) 1 false at h5
  unfold words
  omega

theorem walk_eq (m : ℕ) : walks (m+1) + 3 = words (m+3) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      rcases m with _ | m
      · decide +kernel
      rcases m with _ | m
      · decide +kernel
      rcases m with _ | m
      · decide +kernel
      have h0 := ih m (by omega)
      have h1 := ih (m+2) (by omega)
      have hr := words_rec (m+3)
      change walks (m+3) + 3 = words (m+5) at h1
      change words (m+6) = 2*words (m+5) + words (m+3) at hr
      change walks (m+4) + 3 = words (m+6)
      have hw : walks (m+4) = 2 * walks (m+3) + walks (m+1) + 6 := by
        rw [walks]
      omega

end OMA.A100691

theorem OMA.solution : type_of% @OMA.S_oeis_a100691.main :=
  OMA.A100691.walk_eq