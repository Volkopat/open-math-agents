import OMAStatements.S_mse_5124478
import Mathlib

/-!
Witness: one unary operation `c` with the identity `c x = c y`, i.e. sets with a constant
unary map (pointed sets together with the empty algebra).
-/

namespace OMA.Sol5124478

open CategoryTheory OMA.S_mse_5124478

universe v₁ v₂ u₁ u₂

/-- Every hom-set is inhabited. -/
def AllHom (C : Type u₁) [Category.{v₁} C] : Prop := ∀ X Y : C, Nonempty (X ⟶ Y)

/-- There is an object receiving maps from everything and with at most one map to anything. -/
def HasSpecial (C : Type u₁) [Category.{v₁} C] : Prop :=
  ∃ S : C, ∀ Y : C, Nonempty (Y ⟶ S) ∧ ∀ f g : S ⟶ Y, f = g

theorem allHom_transfer {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (e : C ≌ D) (h : AllHom D) : AllHom C := by
  intro X Y
  obtain ⟨f⟩ := h (e.functor.obj X) (e.functor.obj Y)
  exact ⟨e.functor.preimage f⟩

theorem hasSpecial_transfer {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (e : C ≌ D) (h : HasSpecial C) : HasSpecial D := by
  obtain ⟨S, hS⟩ := h
  refine ⟨e.functor.obj S, fun Y => ⟨?_, ?_⟩⟩
  · obtain ⟨f⟩ := (hS (e.inverse.obj Y)).1
    exact ⟨(e.counitIso.app Y).inv ≫ e.functor.map f⟩
  · intro f g
    apply e.inverse.map_injective
    have := (hS (e.inverse.obj Y)).2 ((e.unitIso.app S).hom ≫ e.inverse.map f)
      ((e.unitIso.app S).hom ≫ e.inverse.map g)
    exact (cancel_epi _).1 this

abbrev ar : Unit → ℕ := fun _ => 1

def E : Set (AlgTerm ar × AlgTerm ar) :=
  {(AlgTerm.op () (fun _ => AlgTerm.var 0), AlgTerm.op () (fun _ => AlgTerm.var 1))}

theorem interp_const (A : VarietyObj ar E) (xs ys : Fin 1 → A.1.carrier) :
    A.1.interp () xs = A.1.interp () ys := by
  have h := A.2 _ rfl (fun n => if n = 0 then xs 0 else ys 0)
  simp only [evalTerm] at h
  have e1 : xs = fun _ => xs 0 := by funext k; rw [Subsingleton.elim k 0]
  have e2 : ys = fun _ => ys 0 := by funext k; rw [Subsingleton.elim k 0]
  rw [e1, e2]
  simpa using h

def mk (X : Type) (f : (Fin 1 → X) → X) (hf : ∀ xs ys, f xs = f ys) : VarietyObj ar E :=
  ⟨⟨X, fun _ => f⟩, by
    intro e he
    rw [E, Set.mem_singleton_iff] at he
    subst he
    intro env
    exact hf _ _⟩

def ptAlg : VarietyObj ar E := mk Unit (fun _ => ()) (fun _ _ => rfl)
def emptyAlg : VarietyObj ar E := mk Empty (fun xs => xs 0) (fun xs _ => (xs 0).elim)
def natAlg : VarietyObj ar E := mk ℕ (fun _ => 0) (fun _ _ => rfl)

theorem not_allHom : ¬ AllHom (VarietyObj ar E) := by
  intro h
  obtain ⟨f⟩ := h ptAlg emptyAlg
  exact (f.1 ()).elim

theorem hasSpecial : HasSpecial (VarietyObj ar E) := by
  refine ⟨ptAlg, fun Y => ⟨⟨⟨fun _ => (), fun _ _ => rfl⟩⟩, ?_⟩⟩
  intro f g
  apply Subtype.ext
  funext x
  have hf := f.2 () (fun _ => ())
  have hg := g.2 () (fun _ => ())
  have hx : x = ptAlg.1.interp () (fun _ => ()) := rfl
  rw [hx, hf, hg]
  exact interp_const Y _ _

theorem aleph0 : IsAleph0Categorical ar E := by
  refine ⟨⟨natAlg, ?_, ?_⟩, ?_⟩
  · exact (inferInstance : Countable ℕ)
  · exact (inferInstance : Infinite ℕ)
  · intro A B hA1 hA2 hB1 hB2
    classical
    obtain ⟨e⟩ : Nonempty (A.1.carrier ≃ B.1.carrier) := nonempty_equiv_of_countable
    obtain ⟨a0⟩ : Nonempty A.1.carrier := inferInstance
    let a : A.1.carrier := A.1.interp () (fun _ => a0)
    let b : B.1.carrier := B.1.interp () (fun _ => e a0)
    let f : A.1.carrier ≃ B.1.carrier := e.trans (Equiv.swap (e a) b)
    have hfa : f a = b := by simp [f]
    have hfb : f.symm b = a := by rw [← hfa]; simp
    refine ⟨⟨⟨f, ?_⟩, ⟨f.symm, ?_⟩, ?_, ?_⟩⟩
    · intro i xs
      rw [interp_const A xs (fun _ => a0), interp_const B (f ∘ xs) (fun _ => e a0)]
      exact hfa
    · intro i xs
      rw [interp_const B xs (fun _ => e a0), interp_const A (f.symm ∘ xs) (fun _ => a0)]
      exact hfb
    · apply Subtype.ext
      funext x
      exact f.symm_apply_apply x
    · apply Subtype.ext
      funext x
      exact f.apply_symm_apply x

theorem type_not_special : ¬ HasSpecial Type := by
  rintro ⟨S, hS⟩
  obtain ⟨f⟩ := (hS PUnit).1
  have h := (hS Bool).2 (TypeCat.ofHom (fun _ => true)) (TypeCat.ofHom (fun _ => false))
  have h2 := congrArg (fun k : S ⟶ Bool => k (f PUnit.unit)) h
  simp at h2

theorem pointed_allHom : AllHom PointedSet := fun _ Y => ⟨⟨fun _ => Y.pt, rfl⟩⟩

theorem module_allHom (K : Type) [Field K] : AllHom (ModuleCat.{0} K) := fun _ _ => ⟨0⟩

def lineObj (K : Type) [Field K] : AffObj K where
  carrier := K
  affComb c x y := (1 - c) * x + c * y
  embeddable := ⟨K, inferInstance, inferInstance, id, Function.injective_id, fun _ _ _ => rfl⟩

theorem aff_not_special (K : Type) [Field K] : ¬ HasSpecial (AffObj K) := by
  rintro ⟨S, hS⟩
  obtain ⟨f⟩ := (hS (lineObj K)).1
  have h := (hS (lineObj K)).2
    ⟨fun _ => (0 : K), fun c x y => by show (0 : K) = (1 - c) * 0 + c * 0; ring⟩
    ⟨fun _ => (1 : K), fun c x y => by show (1 : K) = (1 - c) * 1 + c * 1; ring⟩
  have h2 := congrFun (congrArg Subtype.val h) (f.1 (show (lineObj K).carrier from (0 : K)))
  exact zero_ne_one (α := K) h2

end OMA.Sol5124478

open CategoryTheory OMA.S_mse_5124478 OMA.Sol5124478 in
theorem OMA.solution : type_of% @OMA.S_mse_5124478.main := by
  refine ⟨Unit, inferInstance, ar, E, aleph0, ?_, ?_, ?_, ?_⟩
  · rintro ⟨e⟩
    exact type_not_special (hasSpecial_transfer e hasSpecial)
  · rintro ⟨e⟩
    exact not_allHom (allHom_transfer e pointed_allHom)
  · intro K _ _
    rintro ⟨e⟩
    exact not_allHom (allHom_transfer e (module_allHom K))
  · intro K _ _
    rintro ⟨e⟩
    exact aff_not_special K (hasSpecial_transfer e hasSpecial)
