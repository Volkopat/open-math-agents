import OMAStatements.S_oeis_a001043

namespace OMA.R_oeis_a001043_R1

open OMA.S_oeis_a001043

def H1 : Prop :=
  ∀ m : ℕ, 0 < m → Even m → ∀ q : ℚ, 0 < q → HasPrimeBlockExpansion m q

def H2 : Prop :=
  ∀ m : ℕ, 1 < m → Odd m → ∀ c d : ℕ, 0 < c → 0 < d → Odd d →
    HasPrimeBlockExpansion m ((c : ℚ) / (d : ℚ))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a001043.main := by
  intro evenBlock oddBlock
  exact ⟨evenBlock, oddBlock⟩

end OMA.R_oeis_a001043_R1
