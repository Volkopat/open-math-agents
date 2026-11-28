import OMAStatements.S_wp_monomial_conjecture_on_noetherian_local_rings
import Mathlib

/-!
Classical slice of Hochster's monomial conjecture.

H1 collects the classical low cases, valid for every Noetherian local ring:
* `t = 0` in every dimension (a system of parameters generates a proper ideal);
* dimension `d ≤ 1` for every `t` (in dimension 1, `x ^ t = r * x ^ (t + 1)` forces `x` to be
  nilpotent, because `1 - r * x` is a unit, and then every prime ideal is maximal, so the
  dimension would be 0).
This is a known case, not progress on the conjecture.

H2 is the open rest: dimension at least 2 and exponent at least 1.
-/

namespace OMA.R_wp_monomial_conjecture_on_noetherian_local_rings_R1

open IsLocalRing

/-- The monomial property for `d ≤ 1` or `t = 0`. -/
def H1 : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (d : ℕ),
    ringKrullDim R = d →
    ∀ x : Fin d → R, (Ideal.span (Set.range x)).radical = maximalIdeal R →
    ∀ t : ℕ, (d ≤ 1 ∨ t = 0) →
      (∏ i, x i) ^ t ∉ Ideal.span (Set.range fun i => x i ^ (t + 1))

/-- Open rest: dimension at least 2 and exponent at least 1. -/
def H2 : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (d : ℕ),
    ringKrullDim R = d →
    ∀ x : Fin d → R, (Ideal.span (Set.range x)).radical = maximalIdeal R →
    ∀ t : ℕ, 2 ≤ d → 1 ≤ t →
      (∏ i, x i) ^ t ∉ Ideal.span (Set.range fun i => x i ^ (t + 1))

theorem main : H1 → H2 →
    type_of% @OMA.S_wp_monomial_conjecture_on_noetherian_local_rings.main := by
  intro h1 h2 R _ _ _ d hd x hx t
  by_cases h : d ≤ 1 ∨ t = 0
  · exact h1 R d hd x hx t h
  · obtain ⟨hd2, ht2⟩ := not_or.1 h
    exact h2 R d hd x hx t (by omega) (by omega)

end OMA.R_wp_monomial_conjecture_on_noetherian_local_rings_R1
