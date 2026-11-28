import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.ULift
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.CWComplex.Classical.Finite

open CategoryTheory Topology
open scoped DirectSum

namespace OMA.S_mo_157395

universe u

/-- Singular homology with coefficients in the integral module. -/
noncomputable def integralHomology (n : ℕ) : TopCat.{u} ⥤ ModuleCat.{u} ℤ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) n).obj
    (ModuleCat.of ℤ (ULift.{u} ℤ))

/-- Does every connected CW complex with finitely generated total
integral homology have a map from a finite CW complex inducing a homology isomorphism? -/
theorem main :
    ∀ (X : TopCat.{u}) [T2Space X] [ConnectedSpace X] [CWComplex (Set.univ : Set X)],
      Module.Finite ℤ (⨁ n : ℕ, (integralHomology n).obj X) →
      ∃ (Y : TopCat.{u}) (_ : T2Space Y) (cw : CWComplex (Set.univ : Set Y)),
        letI := cw
        RelCWComplex.Finite (D := ∅) (Set.univ : Set Y) ∧
          ∃ f : Y ⟶ X, ∀ n : ℕ, IsIso ((integralHomology n).map f) := by
  sorry

end OMA.S_mo_157395
