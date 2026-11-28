import Mathlib

/-!
# Upgrading a completary multifuncoid

Source: https://www.openproblemgarden.org/op/upgrading_a_completary_multifuncoid
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `℧` be a set, `𝔉` the set of filters on `℧` ordered reverse to set-theoretic inclusion, `𝔓`
the set of principal filters on `℧`, and `n` an index set. Consider the filtrator `(𝔉ⁿ; 𝔓ⁿ)`.
Conjecture (Porton): if `f` is a completary multifuncoid of the form `𝔓ⁿ`, then `E* f` is a
completary multifuncoid of the form `𝔉ⁿ`.

Conventions, following the source's definitions:
* Mathlib's order on `Filter U` is reverse inclusion of the families of sets, as in the source;
  its join `⊔` and least element `⊥` (the improper filter) are the source's `∪` and `0`.
  `𝔓` is identified with `Set U` through `X ↦ 𝓟 X` (an order embedding; `0` is `∅`, join is `∪`).
  `𝔄ⁿ` carries the pointwise order and pointwise joins; `n` is any type `ι`.
* `up L = {Y ∈ 𝔓ⁿ | Y ≥ L}` and `E* K = {L ∈ 𝔉ⁿ | up L ⊆ K}`.
* A completary multifuncoid of the form `𝔄` (a family of join-semilattices with least elements)
  is `f ⊆ ∏ 𝔄` with `L₀ ∪ L₁ ∈ f ↔ ∃ c ∈ {0,1}ⁿ, (λ i, L_{c i} i) ∈ f` for all `L₀, L₁`, and
  `L ∉ f` whenever some `L i` is the least element.
-/

namespace OMA.S_opg_upgrading_a_completary_multifuncoid

/-- A completary multifuncoid of the form `(𝒫 U)ⁿ` (principal filters, as sets). -/
def IsCompletaryP {U ι : Type} (f : Set (ι → Set U)) : Prop :=
  (∀ L₀ L₁ : ι → Set U, (fun i => L₀ i ∪ L₁ i) ∈ f ↔
    ∃ c : ι → Bool, (fun i => if c i then L₁ i else L₀ i) ∈ f) ∧
  (∀ L : ι → Set U, (∃ i, L i = ∅) → L ∉ f)

/-- A completary multifuncoid of the form `𝔉ⁿ` (filters). -/
def IsCompletaryF {U ι : Type} (f : Set (ι → Filter U)) : Prop :=
  (∀ L₀ L₁ : ι → Filter U, (fun i => L₀ i ⊔ L₁ i) ∈ f ↔
    ∃ c : ι → Bool, (fun i => if c i then L₁ i else L₀ i) ∈ f) ∧
  (∀ L : ι → Filter U, (∃ i, L i = ⊥) → L ∉ f)

/-- `E* K`: the upgrading of a set `K` of principal elements. -/
def upgrade {U ι : Type} (K : Set (ι → Set U)) : Set (ι → Filter U) :=
  {L | ∀ Y : ι → Set U, (∀ i, L i ≤ Filter.principal (Y i)) → Y ∈ K}

theorem main :
    ∀ (U ι : Type) (f : Set (ι → Set U)), IsCompletaryP f → IsCompletaryF (upgrade f) := by
  sorry

end OMA.S_opg_upgrading_a_completary_multifuncoid
