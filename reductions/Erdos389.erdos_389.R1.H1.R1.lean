import OMAReductions.R_Erdos389_erdos_389_R1

/-!
# Splitting the smooth-block existence step of Erdős 389

The open step asks for a witness `k` satisfying a smoothness condition on the block
`k + s` together with the small-prime valuation inequalities. These are separated:
one hypothesis supplies a smooth block, the other transfers smoothness to the
valuations. The first is the occurrence problem for smooth consecutive values;
the second is the Legendre-formula comparison at small primes. Neither hypothesis
is the original step, and their conjunction is exactly the step.
-/
-- Credit: @PetrouilFan

namespace OMA.R_Erdos389_erdos_389_R1_H1_R1

/-- Smooth block existence: for every `n >= 1` there is a positive `k` such that every prime
dividing one of the blocks `k + s` in the critical range is below the smoothness bound
`max (n - 1) (Nat.sqrt (n + 2 * k - 1))`. -/
def H1 : Prop := ∀ n ≥ 1, ∃ k ≥ 1,
    ∀ s : ℕ, n - 1 < 2 * s → s ≤ n - 1 → ∀ p : ℕ, p.Prime → p ∣ k + s →
      p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))

/-- Smoothness transfers to the small-prime valuation inequalities: whenever a positive `k`
has the smooth block above `n`, the two consecutive products satisfy the required comparison
at every prime not exceeding the smoothness bound. -/
def H2 : Prop := ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    (∀ s : ℕ, n - 1 < 2 * s → s ≤ n - 1 → ∀ p : ℕ, p.Prime → p ∣ k + s →
      p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1))) →
    ∀ p : ℕ, p.Prime → p ≤ max (n - 1) (Nat.sqrt (n + 2 * k - 1)) →
      padicValNat p (∏ i ∈ Finset.range k, (n + i)) ≤
        padicValNat p (∏ i ∈ Finset.range k, (n + k + i))

theorem main : H1 → H2 → OMA.R_Erdos389_erdos_389_R1.H1 := by
  intro smooth existsTransfer n hn
  obtain ⟨k, hk, hblock⟩ := smooth n hn
  refine ⟨k, hk, hblock, ?_⟩
  intro p hp hle
  exact existsTransfer n k hn hk hblock p hp hle

end OMA.R_Erdos389_erdos_389_R1_H1_R1
