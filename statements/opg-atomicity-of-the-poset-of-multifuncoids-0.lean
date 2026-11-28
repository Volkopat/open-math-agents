import Mathlib

/-!
# Atomicity of the poset of multifuncoids

Source: https://www.openproblemgarden.org/op/atomicity_of_the_poset_of_multifuncoids_0
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Porton): for all sets `℧` and `n`, the poset of multifuncoids of the form
`(𝒫℧)ⁿ` is atomic and atomistic.

Conventions, following the source's definitions:
* `𝒫℧` is `Set U` ordered by inclusion (a join-semilattice with least element `∅`), and
  `(𝒫℧)ⁿ` is the family indexed by `n` (here any type `ι`) all of whose members are `𝒫℧`; its
  product is `ι → Set U`.
* A free star on `Set U` is a set `S` of subsets with `∅ ∉ S` and
  `A ∪ B ∈ S ↔ A ∈ S ∨ B ∈ S`.
* For `f ⊆ ι → Set U`, `i : ι` and `L` defined off `i` (encoded as a full function whose value at
  `i` is ignored), `(val f)ᵢ L = {X | L ∪ {(i, X)} ∈ f} = {X | update L i X ∈ f}`.
* A multifuncoid is an upper set `f` (for the pointwise order) with every `(val f)ᵢ L` a free
  star. Multifuncoids are ordered by inclusion; the least one is `∅`.
* Atomic: every nonzero element is above an atom. Atomistic: every element is the least upper
  bound, in this poset, of the atoms below it.
-/

namespace OMA.S_opg_atomicity_of_the_poset_of_multifuncoids_0

variable {U ι : Type}

/-- A free star on the lattice `Set U`. -/
def IsFreeStar (S : Set (Set U)) : Prop :=
  ∅ ∉ S ∧ ∀ A B : Set U, A ∪ B ∈ S ↔ A ∈ S ∨ B ∈ S

/-- `(val f)ᵢ L`. -/
def val [DecidableEq ι] (f : Set (ι → Set U)) (i : ι) (L : ι → Set U) : Set (Set U) :=
  {X | Function.update L i X ∈ f}

/-- A multifuncoid of the form `(𝒫℧)ⁿ`. -/
def IsMultifuncoid [DecidableEq ι] (f : Set (ι → Set U)) : Prop :=
  IsUpperSet f ∧ ∀ (i : ι) (L : ι → Set U), IsFreeStar (val f i L)

/-- An atom of the poset of multifuncoids. -/
def IsMFAtom [DecidableEq ι] (a : Set (ι → Set U)) : Prop :=
  IsMultifuncoid a ∧ a ≠ ∅ ∧ ∀ g, IsMultifuncoid g → g ⊆ a → g = ∅ ∨ g = a

theorem main :
    ∀ (U ι : Type) [DecidableEq ι],
      -- atomic
      (∀ f : Set (ι → Set U), IsMultifuncoid f → f ≠ ∅ → ∃ a, IsMFAtom a ∧ a ⊆ f) ∧
      -- atomistic
      (∀ f : Set (ι → Set U), IsMultifuncoid f →
        ∀ g : Set (ι → Set U), IsMultifuncoid g →
          (∀ a, IsMFAtom a → a ⊆ f → a ⊆ g) → f ⊆ g) := by
  sorry

end OMA.S_opg_atomicity_of_the_poset_of_multifuncoids_0
