import Mathlib

/-!
# Thomas' conjecture on reducts of homogeneous structures

Source: https://en.wikipedia.org/wiki/Reduct
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (Wikipedia, Thomas' conjecture): does a finitely presented homogeneous structure for
a finite relational language have finitely many reducts?

Conventions:
* Structures are countably infinite, with universe `ℕ`, in a finite relational language: finitely
  many relations `R_i ⊆ ℕ^{a_i}`. Finite structures of the same language live on `Fin k`.
* Homogeneous: every isomorphism between finite substructures extends to an automorphism.
* "Finitely presented" is read, as in Thomas' formulation, as finitely bounded: there is a finite
  set of finite structures such that a finite structure embeds into `M` iff none of them embeds
  into it.
* Reducts are counted up to first-order interdefinability. Such an `M` is `ω`-categorical, so by
  the standard Galois correspondence (Ryll-Nardzewski, Engeler, Svenonius) its reducts up to
  interdefinability correspond to the closed subgroups of `Sym(ℕ)` (pointwise convergence
  topology) containing `Aut(M)`. We state finiteness of that set. A subgroup `H` is closed iff any
  permutation agreeing on each finite set with some element of `H` lies in `H`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_reduct

/-- A relational structure on `α` with relations of arities `ar i`. -/
abbrev Str (m : ℕ) (ar : Fin m → ℕ) (α : Type) : Type := ∀ i : Fin m, Set (Fin (ar i) → α)

variable {m : ℕ} {ar : Fin m → ℕ}

/-- `f : α → β` is an embedding of structures. -/
def IsEmb {α β : Type} (A : Str m ar α) (B : Str m ar β) (f : α → β) : Prop :=
  Function.Injective f ∧ ∀ i (t : Fin (ar i) → α), t ∈ A i ↔ f ∘ t ∈ B i

/-- `σ` is an automorphism of the structure `M` on `ℕ`. -/
def IsAut (M : Str m ar ℕ) (σ : Equiv.Perm ℕ) : Prop := IsEmb M M σ

/-- Homogeneity: every partial isomorphism between finite substructures extends to an
automorphism. -/
def Homogeneous (M : Str m ar ℕ) : Prop :=
  ∀ (A : Finset ℕ) (f : ℕ → ℕ), Set.InjOn f A →
    (∀ i (t : Fin (ar i) → ℕ), (∀ j, t j ∈ A) → (t ∈ M i ↔ f ∘ t ∈ M i)) →
      ∃ σ : Equiv.Perm ℕ, IsAut M σ ∧ ∀ a ∈ A, σ a = f a

/-- Finite boundedness. -/
def FinitelyBounded (M : Str m ar ℕ) : Prop :=
  ∃ (r : ℕ) (sz : Fin r → ℕ) (F : ∀ j : Fin r, Str m ar (Fin (sz j))),
    ∀ (k : ℕ) (A : Str m ar (Fin k)),
      (∃ f : Fin k → ℕ, IsEmb A M f) ↔ ∀ j, ¬ ∃ f : Fin (sz j) → Fin k, IsEmb (F j) A f

/-- `H` is a closed subgroup of `Sym(ℕ)`. -/
def IsClosed' (H : Subgroup (Equiv.Perm ℕ)) : Prop :=
  ∀ σ : Equiv.Perm ℕ, (∀ A : Finset ℕ, ∃ h ∈ H, ∀ a ∈ A, h a = σ a) → σ ∈ H

theorem main :
    ∀ (m : ℕ) (ar : Fin m → ℕ) (M : Str m ar ℕ), Homogeneous M → FinitelyBounded M →
      {H : Subgroup (Equiv.Perm ℕ) | IsClosed' H ∧ ∀ σ, IsAut M σ → σ ∈ H}.Finite := by
  sorry

end OMA.S_wp_reduct
