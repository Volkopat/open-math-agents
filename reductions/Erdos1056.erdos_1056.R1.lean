import FormalConjectures.ErdosProblems.«1056»

-- Credit: @PetrouilFan
-- Reduction of Erdős 1056.  The small cases k = 2 and k = 3 are finite explicit
-- witnesses, already proved upstream as variants.k2 and variants.k3.  The remaining
-- hypothesis is the genuinely open construction for every k >= 4.

namespace OMA.R_Erdos1056_erdos_1056_R1

open Erdos1056
open Nat

-- k = 2: explicit finite witness.
def H1 : Prop :=
  ∃ (p : ℕ) (_ : p.Prime) (b : Fin (2 + 1) → ℕ) (_ : StrictMono b), AllModProdEqualsOne p b

-- k = 3: explicit finite witness.
def H2 : Prop :=
  ∃ (p : ℕ) (_ : p.Prime) (b : Fin (3 + 1) → ℕ) (_ : StrictMono b), AllModProdEqualsOne p b

-- The genuinely open regime: all k >= 4.
def H3 : Prop :=
  ∀ k : ℕ, 4 ≤ k →
    ∃ (p : ℕ) (_ : p.Prime) (b : Fin (k + 1) → ℕ) (_ : StrictMono b), AllModProdEqualsOne p b

theorem main : H1 → H2 → H3 → type_of% @Erdos1056.erdos_1056 := by
  intro hw2 hw3 hlarge k hk
  by_cases h : k ≤ 3
  · have hk23 : k = 2 ∨ k = 3 := by omega
    rcases hk23 with rfl | rfl
    · simpa [H1] using hw2
    · simpa [H2] using hw3
  · exact hlarge k (by omega)

end OMA.R_Erdos1056_erdos_1056_R1
