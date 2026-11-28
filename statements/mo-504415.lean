import Mathlib

/-!
# Direct and inverse images of internal derived Hom sheafs

Source: https://mathoverflow.net/questions/504415
Credit: @eltociear

The question (RandomMathUser, MathOverflow 504415, unanswered at the time of
writing) asks the following. Let `i_*`, `i^*` be a geometric morphism of
topoi, with `i^* : Sh(Y) → Sh(X)` the inverse image and `i_* : Sh(X) → Sh(Y)`
the direct image, in the direction used in the question. In the derived
category `D(X)` of abelian sheaves on `X` one has the internal derived Hom
`Rℋom_{D(X)}`. For `F ∈ D(Y)` and `G ∈ D(X)`, what is the relationship
between

* `Ri_* Rℋom_{D(X)}(i^*F, G)` and `Rℋom_{D(Y)}(F, Ri_*G)`, and
* `Rℋom_{D(X)}(i^*F, G)` and `i^* Rℋom_{D(Y)}(F, Ri_*G)`?

Namely: is the natural morphism between them an isomorphism? The asker is
particularly interested in the case where `X` and `Y` have the same ambient
space but the topology on `X` is finer, so that `i^*` is sheafification;
that case is included in the general statement below. (The question's
meta-question about references is not mathematical content and is not
formalized.)

## How this is stated

Mathlib has neither derived categories of sheaf topoi, nor internal derived
Hom, nor geometric morphisms of topoi, so the data of the question is
packaged abstractly in `DerivedGeomMorphism`: two categories `D(X)`, `D(Y)`,
the functors `i^*` (exact, hence equal to its own derived functor) and
`Ri_*`, their adjunction, the derived tensor products, and the internal
derived Homs, the latter pinned down by the tensor–Hom adjunctions
`F ⊗ - ⊣ Rℋom(F, -)`. The package also carries the standard further data of
a geometric morphism (that `i^*` preserves tensor products, and the
projection formula `Ri_*(i^*F ⊗ A) ≅ F ⊗ Ri_*A`). The two morphisms of the
question are the canonical natural transformations `can1` and `can2` of the
package: in the standard theory they are constructed from exactly this
adjunction data (units, counits, evaluation maps and the projection
formula). The theorem states that both of them are isomorphisms, for all
`F` and `G` — precisely what the question asks.
-/

namespace OMA.S_mo_504415

open CategoryTheory

universe u

/-- The derived-category package of a geometric morphism of sheaf topoi. -/
structure DerivedGeomMorphism (DX DY : Type u) [Category DX] [Category DY] where
  /-- The inverse image functor `i^* : D(Y) → D(X)` (exact, hence derived = itself). -/
  iStar : DY ⥤ DX
  /-- The derived direct image functor `Ri_* : D(X) → D(Y)`. -/
  iLower : DX ⥤ DY
  /-- The adjunction `i^* ⊣ Ri_*` of the geometric morphism. -/
  adj : iStar ⊣ iLower
  /-- The derived tensor product on `D(X)`. -/
  tensorX : DX × DX ⥤ DX
  /-- The derived tensor product on `D(Y)`. -/
  tensorY : DY × DY ⥤ DY
  /-- The internal derived Hom on `D(X)`. -/
  RHomX : DXᵒᵖ × DX ⥤ DX
  /-- The internal derived Hom on `D(Y)`. -/
  RHomY : DYᵒᵖ × DY ⥤ DY
  /-- The tensor–Hom adjunction on `D(X)`: `F ⊗ - ⊣ Rℋom(F, -)`. -/
  tensorHomAdjX : ∀ F : DX, tensorX.curryObj.obj F ⊣ RHomX.curryObj.obj (Opposite.op F)
  /-- The tensor–Hom adjunction on `D(Y)`. -/
  tensorHomAdjY : ∀ F : DY, tensorY.curryObj.obj F ⊣ RHomY.curryObj.obj (Opposite.op F)
  /-- The inverse image preserves the tensor product. -/
  iStarTensor : tensorY ⋙ iStar ≅ (iStar.prod iStar) ⋙ tensorX
  /-- The projection formula: `Ri_*(i^*F ⊗ A) ≅ F ⊗ Ri_*A`. -/
  projFormula : ((iStar.prod (Functor.id DX)) ⋙ tensorX) ⋙ iLower ≅
    ((Functor.id DY).prod iLower) ⋙ tensorY
  /-- The first canonical morphism:
  `Ri_* Rℋom_{D(X)}(i^*F, G) → Rℋom_{D(Y)}(F, Ri_*G)`. -/
  can1 : ((iStar.op.prod (Functor.id DX)) ⋙ RHomX) ⋙ iLower ⟶
    ((Functor.id DYᵒᵖ).prod iLower) ⋙ RHomY
  /-- The second canonical morphism:
  `i^* Rℋom_{D(Y)}(F, Ri_*G) → Rℋom_{D(X)}(i^*F, G)`. -/
  can2 : (((Functor.id DYᵒᵖ).prod iLower) ⋙ RHomY) ⋙ iStar ⟶
    (iStar.op.prod (Functor.id DX)) ⋙ RHomX

namespace DerivedGeomMorphism

/-- The object-level first comparison of the question. -/
def can1App {DX DY : Type u} [Category DX] [Category DY] (d : DerivedGeomMorphism DX DY)
    (F : DY) (G : DX) :
    d.iLower.obj (d.RHomX.obj (Opposite.op (d.iStar.obj F), G)) ⟶
      d.RHomY.obj (Opposite.op F, d.iLower.obj G) :=
  d.can1.app (Opposite.op F, G)

/-- The object-level second comparison of the question. -/
def can2App {DX DY : Type u} [Category DX] [Category DY] (d : DerivedGeomMorphism DX DY)
    (F : DY) (G : DX) :
    d.iStar.obj (d.RHomY.obj (Opposite.op F, d.iLower.obj G)) ⟶
      d.RHomX.obj (Opposite.op (d.iStar.obj F), G) :=
  d.can2.app (Opposite.op F, G)

end DerivedGeomMorphism

theorem main : ∀ (DX DY : Type u) [Category DX] [Category DY]
    (d : DerivedGeomMorphism DX DY) (F : DY) (G : DX),
    IsIso (d.can1App F G) ∧ IsIso (d.can2App F G) := by
  sorry

end OMA.S_mo_504415
