import Mathlib

namespace OMA.S_opg_rank_vs_genus

abbrev LorentzSpace := Fin 4 → ℝ
abbrev LinearSymmetry := (Matrix (Fin 4) (Fin 4) ℝ)ˣ

noncomputable def lorentzForm (x y : LorentzSpace) : ℝ :=
  -(x 0 * y 0) + x 1 * y 1 + x 2 * y 2 + x 3 * y 3

def hyperboloid : Set LorentzSpace :=
  {x | lorentzForm x x = -1 ∧ 0 < x 0}

abbrev HyperbolicSpace := ↥hyperboloid

noncomputable def act (g : LinearSymmetry) (x : LorentzSpace) : LorentzSpace :=
  g.val.mulVec x

/-- A hyperbolic manifold presented as an orbit quotient of the future sheet
by a free, properly discontinuous group of Lorentz isometries. -/
def IsHyperbolicQuotient (M : Type) [TopologicalSpace M] : Prop :=
  ∃ Γ : Subgroup LinearSymmetry,
    (∀ g : Γ,
      (∀ x y : LorentzSpace, lorentzForm (act g.val x) (act g.val y) = lorentzForm x y) ∧
      (∀ x : HyperbolicSpace, act g.val x.val ∈ hyperboloid)) ∧
    (∀ x : HyperbolicSpace, ∃ U : Set HyperbolicSpace, IsOpen U ∧ x ∈ U ∧
      ∀ g : Γ, g ≠ 1 → ∀ u ∈ U, ∀ v ∈ U, act g.val u.val ≠ v.val) ∧
    ∃ q : HyperbolicSpace → M, Continuous q ∧ IsOpenMap q ∧ Function.Surjective q ∧
      ∀ x y : HyperbolicSpace, q x = q y ↔ ∃ g : Γ, act g.val x.val = y.val

/-- A model of the genus-g handlebody. Thicken a rectangle with g interior
open squares removed by a closed interval. -/
def handlebody (g : ℕ) : Set (Fin 3 → ℝ) :=
  {x | x 0 ∈ Set.Icc 0 (3 * (g : ℝ) + 1) ∧
    x 1 ∈ Set.Icc 0 3 ∧ x 2 ∈ Set.Icc 0 1 ∧
    ∀ i : Fin g, ¬ (x 0 ∈ Set.Ioo (3 * (i.val : ℝ) + 1) (3 * (i.val : ℝ) + 2) ∧
      x 1 ∈ Set.Ioo 1 2)}

def handlebodyBoundary (g : ℕ) : Set ↥(handlebody g) :=
  {x | x.val ∈ frontier (handlebody g)}

/-- The two handlebodies cover M and meet along their entire common boundary. -/
def HasHeegaardSplitting (M : Type) [TopologicalSpace M] (g : ℕ) : Prop :=
  ∃ (A B : Set M) (left : ↥(handlebody g) ≃ₜ ↥A) (right : ↥(handlebody g) ≃ₜ ↥B),
    A ∪ B = Set.univ ∧
    (fun x => (left x).val) '' handlebodyBoundary g = A ∩ B ∧
    (fun x => (right x).val) '' handlebodyBoundary g = A ∩ B

/-- The gap between Heegaard genus and fundamental group rank is unbounded
among closed hyperbolic 3-manifolds. -/
theorem main :
    ∀ gap : ℕ, ∃ (M : Type) (t : TopologicalSpace M),
      letI : TopologicalSpace M := t
      T2Space M ∧ CompactSpace M ∧ IsHyperbolicQuotient M ∧
        (∃ g : ℕ, HasHeegaardSplitting M g) ∧
        ∃ (base : M) (generators : Finset (FundamentalGroup M base)),
          Subgroup.closure (generators : Set (FundamentalGroup M base)) = ⊤ ∧
          ∀ g : ℕ, HasHeegaardSplitting M g → generators.card + gap < g := by
  sorry

end OMA.S_opg_rank_vs_genus
