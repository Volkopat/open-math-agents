import FormalConjectures.ErdosProblems.«102»

-- Credit: @PetrouilFan
-- Reduction of Erdős 102.  Upstream proves the API equivalence `tendsto_h_iff`
-- between the eventual lower bound on `h c n` and a finite-point rich-line density
-- statement.  H1 is that geometric density statement (the genuine open core); H2 is
-- the proved transfer bridge.  Together they are exactly the target.

namespace OMA.R_Erdos102_erdos_102_R1

open Erdos102
open EuclideanGeometry
open Filter

-- The genuinely open geometric density statement.
def H1 : Prop := ∀ c : ℝ, ∀ M : ℕ, ∀ᶠ n in atTop,
    ∀ P : Finset ℝ², P.card = n → c * (n : ℝ) ^ 2 ≤ richLineCount P →
      ∃ L, IsLine L ∧ M ≤ pointsOn P L

-- The upstream-proved transfer lemma (tendsto_h_iff).
def H2 : Prop := ∀ c : ℝ,
    (∀ M : ℕ, ∀ᶠ n in atTop,
      ∀ P : Finset ℝ², P.card = n → c * (n : ℝ) ^ 2 ≤ richLineCount P →
        ∃ L, IsLine L ∧ M ≤ pointsOn P L) →
    ∀ M : ℕ, ∀ᶠ n in atTop, (M : ℕ∞) ≤ h c n

theorem main : H1 → H2 → type_of% @Erdos102.erdos_102 := by
  intro h1 h2 c hc M
  exact h2 c (h1 c) M

end OMA.R_Erdos102_erdos_102_R1
