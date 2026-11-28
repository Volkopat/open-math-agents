import OMAReductions.R_Erdos1053_erdos_1053_variants_guy_R1

-- Reduction Erdos1053.erdos_1053.variants.guy.R1.H2.R1 of step Erdos1053.erdos_1053.variants.guy.R1.H2
-- Credit: @Ciphore

/-!
# Split odd multiperfect numbers by the number of distinct prime factors

For fixed `k` the abundancy identity is a multiplicative constraint on the prime-power
factorization of `n`.  It is therefore natural to separate two independent inputs: finiteness
when the number of distinct prime factors is bounded, and a uniform bound on that number over
all odd non-squarefree multiperfect numbers of even multiplicity.  Neither hypothesis is a
restatement of the target: the first is a fixed-width Diophantine exponential problem, while
the second is the missing width estimate.
-/

namespace OMA.R_Erdos1053_erdos_1053_variants_guy_R1_H2_R1

private def S (k : ℕ) : Set ℕ :=
  {n : ℕ | Nat.IsPerfectFor n 1 k ∧ Odd n ∧ ¬ Squarefree n}

/-- Finiteness with any prescribed bound on the number of distinct prime factors. -/
def H1 : Prop :=
  ∀ r k : ℕ, 3 ≤ k → Even k → {n ∈ S k | n.primeFactors.card ≤ r}.Finite

/-- A uniform width bound for odd non-squarefree multiperfect numbers of even multiplicity. -/
def H2 : Prop :=
  ∃ r : ℕ, ∀ k : ℕ, 3 ≤ k → Even k → ∀ n ∈ S k, n.primeFactors.card ≤ r

theorem main : H1 → H2 → OMA.R_Erdos1053_erdos_1053_variants_guy_R1.H2 := by
  intro fixed uniform k hk heven
  obtain ⟨r, hr⟩ := uniform
  exact (fixed r k hk heven).subset (by
    intro n hn
    exact ⟨hn, hr k hk heven n hn⟩)

end OMA.R_Erdos1053_erdos_1053_variants_guy_R1_H2_R1
