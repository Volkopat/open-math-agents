import Mathlib

/-!
# Berge conjecture

A knot in the three-sphere admitting a nonmeridional Dehn surgery to a lens space
has a doubly primitive position on a genus-two Heegaard surface.

Source: https://en.wikipedia.org/wiki/Berge_knot
For the free-generator characterization of the meridian-disk condition, see
John Berge, *Some knots with surgeries yielding lens spaces*, Theorem 1 and its proof.
https://arxiv.org/abs/1802.09722

For lens space surgery we use the convention of Greene's introduction:
the lens space has fundamental group of order greater than one.
https://annals.math.princeton.edu/wp-content/uploads/annals-v177-n2-p03-p.pdf
Credit: @yuka30240
-/

namespace OMA.S_wp_berge_conjecture

open Set Topology

abbrev Sphere3 := {z : ℂ × ℂ // Complex.normSq z.1 + Complex.normSq z.2 = 1}

/-- The quotient of the unit three-sphere by the action of the p-th roots of unity
with weights 1 and q. -/
abbrev LensSpace (p q : ℕ) :=
  Quot (fun x y : Sphere3 => ∃ u : Circle, u ^ p = 1 ∧
    y.val.1 = (u : ℂ) * x.val.1 ∧ y.val.2 = (u : ℂ) ^ q * x.val.2)

abbrev Disk := {z : ℂ // ‖z‖ ≤ 1}
abbrev SolidTorus := Circle × Disk
abbrev Torus := Circle × Circle

def boundaryPoint (t : Torus) : SolidTorus :=
  (t.1, ⟨(t.2 : ℂ), (Circle.norm_coe t.2).le⟩)

/-- A boundary homeomorphism preserves the unoriented meridian slope precisely
when it extends over the solid torus. -/
def ChangesMeridian (g : Torus ≃ₜ Torus) : Prop :=
  ¬ ∃ h : SolidTorus ≃ₜ SolidTorus, ∀ t, h (boundaryPoint t) = boundaryPoint (g t)

/-- Use an open tube around the knot so the radius-one boundary has a collar. -/
abbrev Tube := C(Circle × ℂ, Sphere3)

abbrev Exterior (tube : Tube) :=
  {x : Sphere3 // x ∉ tube '' {u : Circle × ℂ | ‖u.2‖ < 1}}

/-- Glue the boundary of the filling solid torus to the exterior using g in
the original tube coordinates. The quotient carries the quotient topology. -/
def fillingRelation (tube : Tube) (g : Torus ≃ₜ Torus) :
    Exterior tube ⊕ SolidTorus → Exterior tube ⊕ SolidTorus → Prop
  | .inl x, .inr y => ∃ t : Torus, y = boundaryPoint t ∧
      x.val = tube ((g t).1, ((g t).2 : ℂ))
  | _, _ => False

/-- The knot is the core of the open tube, so it is a locally flat embedded circle.
Some filling at a nonmeridional slope must give a lens space. -/
def AdmitsLensSurgery (k : C(Circle, Sphere3)) : Prop :=
  ∃ (tube : Tube) (g : Torus ≃ₜ Torus) (p q : ℕ),
    IsOpenEmbedding tube ∧ (∀ t, tube (t, 0) = k t) ∧ ChangesMeridian g ∧
    1 < p ∧ p.Coprime q ∧ Nonempty (Quot (fillingRelation tube g) ≃ₜ LensSpace p q)

/-- A genus-two handlebody is a thickened pair of pants. In the complex plane,
remove the two open disks of radius one centered at ±2 from the closed disk of radius four. -/
abbrev Handlebody :=
  {z : ℂ // ‖z‖ ≤ 4 ∧ 1 ≤ ‖z - 2‖ ∧ 1 ≤ ‖z + 2‖} × Set.Icc (0 : ℝ) 1

/-- Lift the knot to the handlebody. Its loop, traversed once in either orientation,
must belong to a free basis of the fundamental group there. -/
def PrimitiveIn (k : C(Circle, Sphere3)) (H : Set Sphere3) : Prop :=
  ∃ c : C(Circle, H), (∀ t, (c t).val = k t) ∧
    ∃ (a : FundamentalGroup Circle 1) (e : FundamentalGroup H (c 1) ≃* FreeGroup (Fin 2)),
      Subgroup.zpowers a = ⊤ ∧ e (FundamentalGroup.map c 1 a) = FreeGroup.of 0

/-- The two handlebodies cover the sphere and meet along their common boundary.
Varying the splitting allows every ambient isotopy of the knot. -/
def IsBergeKnot (k : C(Circle, Sphere3)) : Prop :=
  ∃ A B : Set Sphere3, Nonempty (A ≃ₜ Handlebody) ∧ Nonempty (B ≃ₜ Handlebody) ∧
    A ∪ B = univ ∧ A ∩ B = frontier A ∧ A ∩ B = frontier B ∧
    PrimitiveIn k A ∧ PrimitiveIn k B

theorem main : ∀ k : C(Circle, Sphere3), AdmitsLensSurgery k → IsBergeKnot k := by
  sorry

end OMA.S_wp_berge_conjecture
