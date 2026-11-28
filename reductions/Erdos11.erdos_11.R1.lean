import FormalConjectures.ErdosProblems.«11»

-- Credit: @PetrouilFan
-- The "all odd n > 1" form is the genuinely open strengthening of Erdős 11.
-- Upstream already proves that it implies the eventual form (eventually_of_all_odd),
-- so the only open hypothesis is H1.

open Filter

namespace OMA.R_Erdos11_erdos_11_R1

def H1 : Prop :=
  ∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

def H2 : Prop :=
  (∀ n : ℕ, Odd n → 1 < n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l) →
    ∀ᶠ n : ℕ in atTop, Odd n → ∃ k l : ℕ, Squarefree k ∧ n = k + 2 ^ l

theorem main : H1 → H2 → type_of% @Erdos11.erdos_11 := by
  intro h1 h2
  exact h2 h1

end OMA.R_Erdos11_erdos_11_R1
