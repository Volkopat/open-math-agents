import OMAStatements.S_oeis_a121757

-- Problem: A121757: Triangle read by rows: multiply Pascal's triangle by 1,2,6,24,120,720,... = A000142.
-- Upstream: formal-conjectures statements/oeis-a121757.lean:0 (declaration OMA.S_oeis_a121757.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: by induction on n, D(n+1, k+1) = binomial(n, k) * (k+1)! for k <= n. The cases
-- k = 0 and k = n are the boundary values 1 and (n+1)!; for 0 < k < n the recursion gives
-- (k+1) * C(n-1, k-1) * k! + C(n-1, k) * (k+1)! = (C(n-1, k-1) + C(n-1, k)) * (k+1)! = C(n, k) * (k+1)!.

namespace K04A121757

open OMA.S_oeis_a121757

theorem D_succ (p r : ℕ) : D (p + 1) r =
    if r = 1 then 1
    else if r = p + 1 then Nat.factorial (p + 1)
    else r * D p (r - 1) + D p r := rfl

theorem key (n : ℕ) : ∀ k : ℕ, k ≤ n → D (n + 1) (k + 1) = Nat.choose n k * Nat.factorial (k + 1) := by
  induction n with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    decide
  | succ n ih =>
    intro k hk
    rw [D_succ]
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      simp
    · rcases Nat.lt_or_ge k (n + 1) with hlt | hge
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [if_neg (show ¬(j + 1 + 1 = 1) by omega),
          if_neg (show ¬(j + 1 + 1 = n + 1 + 1) by omega),
          show j + 1 + 1 - 1 = j + 1 by omega, ih j (by omega), ih (j + 1) (by omega),
          Nat.choose_succ_succ' n j, Nat.factorial_succ (j + 1)]
        ring
      · have hk' : k = n + 1 := by omega
        subst hk'
        rw [if_neg (show ¬(n + 1 + 1 = 1) by omega),
          if_pos (show n + 1 + 1 = n + 1 + 1 from rfl), Nat.choose_self, one_mul]

end K04A121757

open OMA.S_oeis_a121757 K04A121757 in
theorem OMA.solution : type_of% @OMA.S_oeis_a121757.main := by
  intro n k hk
  exact (key n k hk).symm
