import OMAStatements.S_mo_312425

open CategoryTheory

universe u

namespace OMA.S_mo_312425

private def converse {X Y : RelCat.{u}} (R : X ⟶ Y) : Y ⟶ X :=
  RelCat.Hom.ofRel R.rel.inv

private def graph {X Y : RelCat.{u}} (f : X → Y) : X ⟶ Y :=
  RelCat.Hom.ofRel f.graph

private theorem converse_converse {X Y : RelCat.{u}} (R : X ⟶ Y) :
    converse (converse R) = R := by
  apply RelCat.Hom.ext
  rfl

private theorem converse_comp {X Y Z : RelCat.{u}} (R : X ⟶ Y) (S : Y ⟶ Z) :
    converse (R ≫ S) = converse S ≫ converse R := by
  apply RelCat.Hom.ext
  exact SetRel.inv_comp R.rel S.rel

-- In the inclusion-ordered category of relations, a right adjoint is precisely
-- the converse of its left adjoint. The two inequalities suffice directly.
private theorem right_adjoint_eq_converse {X Y : RelCat.{u}}
    (R : X ⟶ Y) (S : Y ⟶ X)
    (hunit : (𝟙 X : X ⟶ X).rel ⊆ (R ≫ S).rel)
    (hcounit : (S ≫ R).rel ⊆ (𝟙 Y : Y ⟶ Y).rel) :
    S = converse R := by
  apply RelCat.Hom.ext
  ext ⟨y, x⟩
  change (y, x) ∈ S.rel ↔ (x, y) ∈ R.rel
  obtain ⟨z, hxz, hzx⟩ := hunit (show (x, x) ∈ (𝟙 X : X ⟶ X).rel from rfl)
  constructor
  · intro hyx
    have hyz : (y, z) ∈ (𝟙 Y : Y ⟶ Y).rel := hcounit ⟨x, hyx, hxz⟩
    change y = z at hyz
    exact hyz.symm ▸ hxz
  · intro hxy
    have hzy : (z, y) ∈ (𝟙 Y : Y ⟶ Y).rel := hcounit ⟨x, hzx, hxy⟩
    change z = y at hzy
    exact hzy ▸ hzx

private theorem map_converse_graph (F : RelCat.{u} ⥤ RelCat.{u})
    (hmono : ∀ {X Y : RelCat.{u}} {R S : X ⟶ Y},
      R.rel ⊆ S.rel → (F.map R).rel ⊆ (F.map S).rel)
    {X Y : RelCat.{u}} (f : X → Y) :
    F.map (converse (graph f)) = converse (F.map (graph f)) := by
  apply right_adjoint_eq_converse
  · have h : (𝟙 X : X ⟶ X).rel ⊆ (graph f ≫ converse (graph f)).rel := by
      rintro ⟨x, x'⟩ hxx'
      change x = x' at hxx'
      subst x'
      exact ⟨f x, rfl, rfl⟩
    have h' := hmono h
    simpa only [F.map_id, F.map_comp] using h'
  · have h : (converse (graph f) ≫ graph f).rel ⊆ (𝟙 Y : Y ⟶ Y).rel := by
      rintro ⟨y, y'⟩ ⟨x, hxy, hxy'⟩
      change f x = y at hxy
      change f x = y' at hxy'
      change y = y'
      exact hxy.symm.trans hxy'
    have h' := hmono h
    simpa only [F.map_id, F.map_comp] using h'

/-- Every locally monotone endofunctor of the category of sets and relations
preserves relation converse. -/
theorem monotone_endofunctor_preserves_converse
    (F : RelCat.{u} ⥤ RelCat.{u})
    (hmono : ∀ {X Y : RelCat.{u}} {R S : X ⟶ Y},
      R.rel ⊆ S.rel → (F.map R).rel ⊆ (F.map S).rel) :
    ∀ {X Y : RelCat.{u}} (R : X ⟶ Y),
      F.map (RelCat.Hom.ofRel R.rel.inv) =
        RelCat.Hom.ofRel (F.map R).rel.inv := by
  intro X Y R
  change F.map (converse R) = converse (F.map R)
  let E : RelCat.{u} := {e : X × Y // e ∈ R.rel}
  let p : E → X := fun e => e.val.1
  let q : E → Y := fun e => e.val.2
  have hfactor : R = converse (graph p) ≫ graph q := by
    apply RelCat.Hom.ext
    ext ⟨x, y⟩
    change (x, y) ∈ R.rel ↔ ∃ e : E, p e = x ∧ q e = y
    constructor
    · intro hxy
      exact ⟨⟨(x, y), hxy⟩, rfl, rfl⟩
    · rintro ⟨⟨⟨x', y'⟩, hxy⟩, hp, hq⟩
      change x' = x at hp
      change y' = y at hq
      subst x'
      subst y'
      exact hxy
  rw [hfactor]
  simp only [converse_comp, converse_converse, F.map_comp,
    map_converse_graph F hmono]

end OMA.S_mo_312425

theorem OMA.solution : type_of% @OMA.S_mo_312425.main := by
  intro F hmono X Y R
  exact OMA.S_mo_312425.monotone_endofunctor_preserves_converse F hmono R
