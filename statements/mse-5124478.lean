import Mathlib

/-!
# Classification of $\aleph_0$-categorical varieties

Source: https://math.stackexchange.com/questions/5124478/is-there-a-classification-of-aleph-0-categorical-varieties
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

A variety (equational class in universal algebra) is $\aleph_0$-categorical if it has a
unique countably infinite algebra up to isomorphism. Known examples include:
- the variety of sets,
- the variety of pointed sets,
- the variety of $K$-vector spaces for a finite field $K$,
- the variety of $K$-affine spaces for a finite field $K$.

Is there an $\aleph_0$-categorical variety in a countable algebraic language whose category
of algebras and homomorphisms is not equivalent to any of the above?
-/

namespace OMA.S_mse_5124478

open CategoryTheory

/-- Terms over an algebraic signature with operation symbols `I` and arity function `arity`. -/
inductive AlgTerm {I : Type} (arity : I → ℕ) : Type
  | var : ℕ → AlgTerm arity
  | op (i : I) : (Fin (arity i) → AlgTerm arity) → AlgTerm arity

/-- An algebra for the signature `(I, arity)`. -/
structure AlgStructure {I : Type} (arity : I → ℕ) where
  carrier : Type
  interp (i : I) : (Fin (arity i) → carrier) → carrier

/-- Evaluation of a term in an algebra under a variable assignment. -/
def evalTerm {I : Type} {arity : I → ℕ} (A : AlgStructure arity) (env : ℕ → A.carrier) :
    AlgTerm arity → A.carrier
  | .var n => env n
  | .op i args => A.interp i (fun k => evalTerm A env (args k))

/-- An algebra satisfies an identity `(s, t)` if `s` and `t` evaluate equally under all assignments. -/
def SatisfiesEq {I : Type} {arity : I → ℕ} (A : AlgStructure arity)
    (e : AlgTerm arity × AlgTerm arity) : Prop :=
  ∀ env : ℕ → A.carrier, evalTerm A env e.1 = evalTerm A env e.2

/-- Objects of the variety defined by a set of identities `E`. -/
def VarietyObj {I : Type} (arity : I → ℕ) (E : Set (AlgTerm arity × AlgTerm arity)) : Type 1 :=
  {A : AlgStructure arity // ∀ e ∈ E, SatisfiesEq A e}

/-- Homomorphisms between algebras in a variety. -/
def VarietyHom {I : Type} {arity : I → ℕ} {E : Set (AlgTerm arity × AlgTerm arity)}
    (A B : VarietyObj arity E) : Type :=
  {f : A.1.carrier → B.1.carrier //
    ∀ (i : I) (xs : Fin (arity i) → A.1.carrier), f (A.1.interp i xs) = B.1.interp i (f ∘ xs)}

instance varietyCategory {I : Type} (arity : I → ℕ)
    (E : Set (AlgTerm arity × AlgTerm arity)) : Category (VarietyObj arity E) where
  Hom A B := VarietyHom A B
  id A := ⟨id, fun _ _ => rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun i xs => by simp [f.2, g.2, Function.comp_assoc]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- A variety is $\aleph_0$-categorical if it has a countably infinite algebra and all its
countably infinite algebras are isomorphic. -/
def IsAleph0Categorical {I : Type} (arity : I → ℕ)
    (E : Set (AlgTerm arity × AlgTerm arity)) : Prop :=
  (∃ A : VarietyObj arity E, Countable A.1.carrier ∧ Infinite A.1.carrier) ∧
  ∀ A B : VarietyObj arity E,
    Countable A.1.carrier → Infinite A.1.carrier →
    Countable B.1.carrier → Infinite B.1.carrier →
    Nonempty (A ≅ B)

/-- Category of pointed sets (sets with a distinguished basepoint). -/
structure PointedSet where
  carrier : Type
  pt : carrier

instance pointedSetCategory : Category PointedSet where
  Hom X Y := {f : X.carrier → Y.carrier // f X.pt = Y.pt}
  id X := ⟨id, rfl⟩
  comp f g := ⟨g.1 ∘ f.1, by simp [f.2, g.2]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Category of affine spaces over a field `K` (including the empty affine space),
represented via affine combination operations `(1 - c)x + cy`. -/
structure AffObj (K : Type) [Field K] where
  carrier : Type
  affComb : K → carrier → carrier → carrier
  embeddable :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module K V) (ι : carrier → V),
      Function.Injective ι ∧
      ∀ (c : K) (x y : carrier), ι (affComb c x y) = (1 - c) • ι x + c • ι y

instance affCategory (K : Type) [Field K] : Category (AffObj K) where
  Hom X Y := {f : X.carrier → Y.carrier // ∀ c x y, f (X.affComb c x y) = Y.affComb c (f x) (f y)}
  id X := ⟨id, fun _ _ _ => rfl⟩
  comp f g := ⟨g.1 ∘ f.1, fun c x y => by simp [f.2, g.2]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem main :
    ∃ (I : Type) (_ : Countable I) (arity : I → ℕ) (E : Set (AlgTerm arity × AlgTerm arity)),
      IsAleph0Categorical arity E ∧
      ¬ Nonempty (VarietyObj arity E ≌ Type) ∧
      ¬ Nonempty (VarietyObj arity E ≌ PointedSet) ∧
      (∀ (K : Type) [Field K] [Fintype K], ¬ Nonempty (VarietyObj arity E ≌ ModuleCat.{0} K)) ∧
      (∀ (K : Type) [Field K] [Fintype K], ¬ Nonempty (VarietyObj arity E ≌ AffObj K)) := by
  sorry

end OMA.S_mse_5124478
