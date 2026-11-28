import Mathlib

/-!
# Sums of strongly z-ideals

Source: https://mathoverflow.net/questions/104812
In the ring `C(X)` of continuous real functions, an ideal is a strongly z-ideal if it is an
intersection of maximal ideals. If `I` and `J` are strongly z-ideals, is `I + J` a strongly
z-ideal or all of `C(X)`? `main` states the affirmative answer.

Conventions. `X` is an arbitrary topological space and `C(X) = C(X, ℝ)`. An intersection of
an empty family is `⊤`, so "a strongly z-ideal or all of `C(X)`" is: `I + J` is the infimum
of some set of maximal ideals.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_104812

/-- `I` is an intersection of maximal ideals (allowing the empty intersection `⊤`). -/
def IsInfOfMaximal {R : Type*} [CommRing R] (I : Ideal R) : Prop :=
  ∃ S : Set (Ideal R), (∀ M ∈ S, M.IsMaximal) ∧ I = sInf S

theorem main :
    ∀ (X : Type) [TopologicalSpace X] (I J : Ideal C(X, ℝ)),
      IsInfOfMaximal I → IsInfOfMaximal J → IsInfOfMaximal (I ⊔ J) := by
  sorry

end OMA.S_mo_104812
