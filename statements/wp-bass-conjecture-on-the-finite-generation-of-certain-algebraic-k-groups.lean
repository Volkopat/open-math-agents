import Mathlib

/-!
# Bass conjecture on the finite generation of certain algebraic K-groups

Source: https://en.wikipedia.org/wiki/Bass_conjecture
Credit: @yuka30240

We use the source's G-theory formulation for commutative rings of finite type over ℤ.
For such a ring the finitely generated modules form an abelian category. Its Quillen
Q-category has arrows represented by spans M ↞ S ↪ N, up to isomorphism of S.
We encode the span by the image of S in M × N. Projection onto M is surjective
and projection onto N is injective. Conversely these two projections recover the span.
The ring is Noetherian, so these submodules and the kernels of the projections to M
are finitely generated. Pullback composition of spans becomes composition of relations.

Reference: D. Quillen, *Higher algebraic K-theory I*, §2 (the Q-construction).
-/

namespace OMA.S_wp_bass_conjecture_on_the_finite_generation_of_certain_algebraic_k_groups

open CategoryTheory
open scoped Simplicial

universe u

/-- Objects of the Q-category of finitely generated modules. -/
structure QObj (A : Type u) [CommRing A] where
  moduleObj : FGModuleCat.{u} A

variable {A : Type u} [CommRing A]

/-- The image of a span M ↞ S ↪ N as a linear relation. -/
def QHom (M N : QObj A) :=
  { S : Submodule A (M.moduleObj × N.moduleObj) //
    (∀ x, ∃ y, (x, y) ∈ S) ∧
    (∀ {x x' y}, (x, y) ∈ S → (x', y) ∈ S → x = x') }

def QHom.identity (M : QObj A) : QHom M M :=
  ⟨(LinearMap.id : M.moduleObj →ₗ[A] M.moduleObj).graph,
    fun x => ⟨x, rfl⟩, fun h h' => h.symm.trans h'⟩

def QHom.compose {M N P : QObj A} (f : QHom M N) (g : QHom N P) : QHom M P :=
  ⟨{ carrier := {p | ∃ y, (p.1, y) ∈ f.val ∧ (y, p.2) ∈ g.val}
     zero_mem' := ⟨0, f.val.zero_mem, g.val.zero_mem⟩
     add_mem' := by
       rintro _ _ ⟨y, hf, hg⟩ ⟨y', hf', hg'⟩
       exact ⟨y + y', f.val.add_mem hf hf', g.val.add_mem hg hg'⟩
     smul_mem' := by
       rintro a _ ⟨y, hf, hg⟩
       exact ⟨a • y, f.val.smul_mem a hf, g.val.smul_mem a hg⟩ },
   by
     intro x
     obtain ⟨y, hf⟩ := f.property.1 x
     obtain ⟨z, hg⟩ := g.property.1 y
     exact ⟨z, y, hf, hg⟩,
   by
     rintro x x' z ⟨y, hf, hg⟩ ⟨y', hf', hg'⟩
     obtain rfl := g.property.2 hg hg'
     exact f.property.2 hf hf'⟩

instance : Category (QObj A) where
  Hom := QHom
  id := QHom.identity
  comp := QHom.compose
  id_comp := by
    intro M N f
    apply Subtype.ext
    apply SetLike.ext
    rintro ⟨x, y⟩
    change (∃ t, t = x ∧ (t, y) ∈ f.val) ↔ _
    simp
  comp_id := by
    intro M N f
    apply Subtype.ext
    apply SetLike.ext
    rintro ⟨x, y⟩
    change (∃ t, (x, t) ∈ f.val ∧ y = t) ↔ _
    simp
  assoc := by
    intro M N P T f g h
    apply Subtype.ext
    apply SetLike.ext
    rintro ⟨x, w⟩
    change (∃ z, (∃ y, (x, y) ∈ f.val ∧ (y, z) ∈ g.val) ∧ (z, w) ∈ h.val) ↔
      (∃ y, (x, y) ∈ f.val ∧ ∃ z, (y, z) ∈ g.val ∧ (z, w) ∈ h.val)
    constructor
    · rintro ⟨z, ⟨y, hf, hg⟩, hh⟩
      exact ⟨y, hf, z, hg, hh⟩
    · rintro ⟨y, hf, z, hg, hh⟩
      exact ⟨z, ⟨y, hf, hg⟩, hh⟩

variable (A)

/-- The vertex of the realized nerve corresponding to the zero module. -/
noncomputable def zeroVertex : SSet.toTop.obj (nerve (QObj A)) :=
  TopCat.toSSetObj₀Equiv (((sSetTopAdj.unit.app (nerve (QObj A))).app _)
    (ComposableArrows.mk₀ (⟨FGModuleCat.of A PUnit⟩ : QObj A)))

/-- Quillen's G-group in degree n is the (n+1)st homotopy group at the zero module. -/
noncomputable abbrev gGroup (n : ℕ) :=
  HomotopyGroup.Pi (n + 1) (SSet.toTop.obj (nerve (QObj A))) (zeroVertex A)

theorem main :
    ∀ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] (n : ℕ), Group.FG (gGroup R n) := by
  sorry

end OMA.S_wp_bass_conjecture_on_the_finite_generation_of_certain_algebraic_k_groups
