import FormalConjectures.Wikipedia.CramerConjecture

-- Reduction CramerConjecture.cramer_conjecture.variants.limsup_eq_one.R1 of Cramér's conjecture
-- (the limsup formulation).
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Cramér's conjecture is a two-sided statement about the normalised prime gap ratio: it is
-- eventually at most `1 + eps` for every `eps > 0` (upper side, a bound on prime gaps), and it is
-- frequently at least `1 - eps` (lower side, an unboundedness statement supplied by large gaps).
-- The two sides are logically independent, so each is its own step.

namespace OMA.R_CramerConjecture_cramer_conjecture_variants_limsup_eq_one_R1

/-- Upper side of the limsup: the normalised prime gap is eventually below `1 + eps`. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Eventually (fun n => CramerConjecture.cramerRatio n ≤ 1 + ε) Filter.atTop

/-- Lower side of the limsup: the normalised prime gap comes back above `1 - eps` infinitely
often. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Filter.Frequently (fun n => 1 - ε ≤ CramerConjecture.cramerRatio n) Filter.atTop

theorem main : H1 → H2 →
    type_of% @CramerConjecture.cramer_conjecture.variants.limsup_eq_one := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_CramerConjecture_cramer_conjecture_variants_limsup_eq_one_R1
