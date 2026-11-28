import OMAReductions.R_Erdos396_erdos_396_R1

-- The explicit seventeenth-factor certificate was obtained from Justin Dehorty's
-- witness at k = 16. The remaining existence question begins at k = 17.

namespace OMA.R_Erdos396_erdos_396_R1_H2_R1

/-- The remaining known numerical cases, all covered by the same witness. -/
def H1 : Prop := ∀ k : ℕ, 5 ≤ k → k ≤ 16 →
    ∃ n : ℕ, Nat.descFactorial n (k+1) ∣ Nat.centralBinom n

/-- The next witness search target. -/
def H2 : Prop := ∃ n : ℕ, Nat.descFactorial n 18 ∣ Nat.centralBinom n

/-- Propagate existence from one level to the next, starting at seventeen. -/
def H3 : Prop := ∀ k : ℕ, 17 ≤ k →
    (∃ n : ℕ, Nat.descFactorial n (k+1) ∣ Nat.centralBinom n) →
    ∃ n : ℕ, Nat.descFactorial n (k+2) ∣ Nat.centralBinom n

theorem main : H1 → H2 → H3 → OMA.R_Erdos396_erdos_396_R1.H2 := by
  intro h1 h2 h3 k hk5
  by_cases hk : k ≤ 16
  · exact h1 k hk5 hk
  · have tail : ∀ j : ℕ, 17 ≤ j →
        ∃ n : ℕ, Nat.descFactorial n (j+1) ∣ Nat.centralBinom n := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => exact h2
      | succ j hj ih => exact h3 j hj ih
    exact tail k (by omega)

end OMA.R_Erdos396_erdos_396_R1_H2_R1
