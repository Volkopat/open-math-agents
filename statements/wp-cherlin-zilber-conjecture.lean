import Mathlib

/-!
# Cherlin–Zilber conjecture

This is the omega-stable formulation in the cited source.
Source: https://en.wikipedia.org/wiki/Stable_group
Credit: @witeg4
-/

namespace OMA.S_wp_cherlin_zilber_conjecture

open FirstOrder

universe u

/-- The ternary relation is the graph of multiplication. In a group it also defines
the identity and inverse, so this presents the pure group language. -/
inductive GroupRelation : ℕ → Type
  | product : GroupRelation 3

def groupLanguage : Language := ⟨fun _ => Empty, GroupRelation⟩

instance groupStructure (G : Type u) [Group G] : groupLanguage.Structure G where
  funMap := fun {_} f => nomatch f
  RelMap | .product => fun a => a 0 * a 1 = a 2

/-- Count the complete one-types over every countable model of the complete theory.
The elementary diagram names each element of that model as a parameter. -/
def OmegaStable (G : Type u) [Group G] : Prop :=
  ∀ (M : Type) [Group M] [Countable M], groupLanguage.ElementarilyEquivalent G M →
    Countable ((groupLanguage.elementaryDiagram M).CompleteType Unit)

/-- A faithful linear representation with Zariski-closed image realizes G as the
points of a linear algebraic group. Closedness is relative to the invertible matrices.
For an infinite abstractly simple G the image has no nontrivial proper normal subgroup,
and its finite-index identity component is the entire image. -/
def IsAlgebraic (G : Type u) [Group G] : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : IsAlgClosed K) (n : ℕ)
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) K),
    Function.Injective ρ ∧
    ∃ equations : Set (MvPolynomial (Fin n × Fin n) K),
      ∀ A : Matrix.GeneralLinearGroup (Fin n) K, A ∈ ρ.range ↔
        ∀ p ∈ equations, MvPolynomial.eval (fun ij => A.val ij.1 ij.2) p = 0

theorem main : ∀ (G : Type u) [Group G] [Infinite G] [IsSimpleGroup G],
    OmegaStable G → IsAlgebraic G := by
  sorry

end OMA.S_wp_cherlin_zilber_conjecture
