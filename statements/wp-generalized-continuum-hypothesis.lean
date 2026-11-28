import Mathlib

/-!
# Generalized continuum hypothesis and diamond at successors of singulars

Source: https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_mathematics (set theory),
linked from https://en.wikipedia.org/wiki/generalized_continuum_hypothesis
Credit: @hermitokatt

The source: "Does the generalized continuum hypothesis entail `◇(E^{λ⁺}_{cf(λ)})` for every
singular cardinal `λ`?"

Definitions, following https://en.wikipedia.org/wiki/Diamond_principle :
* For a cardinal `κ` (here viewed as its initial ordinal) and `S ⊆ κ`, `◇_κ(S)` says there is a
  sequence `⟨A_α : α ∈ S⟩` with `A_α ⊆ α` such that for every `A ⊆ κ` the set
  `{α ∈ S : A ∩ α = A_α}` is stationary in `κ`.
* A set is stationary in `κ` if it meets every closed unbounded (club) subset of `κ`.
* `E^{κ}_{μ} = {α < κ : cf(α) = μ}`.
* GCH: `2 ^ μ = μ⁺` for every infinite cardinal `μ`.
* `λ` is singular: infinite with `cf(λ) < λ`.

Direction. The question is yes/no. A negative answer would say that GCH is consistent with the
failure of the principle, which is a consistency (metamathematical) result and cannot be a theorem
inside Lean. So the only formal content of the question is the affirmative statement, which is
what `main` states, for cardinals in an arbitrary universe `u` and GCH in that universe.
Known context: Shelah (2010) proved that `2 ^ λ = λ⁺` implies `◇_{λ⁺}(S)` for every stationary
`S ⊆ λ⁺` with no point of cofinality `cf(λ)`, for uncountable `λ`; the open case is `S = E^{λ⁺}_{cf(λ)}`.
-/

namespace OMA.S_wp_generalized_continuum_hypothesis

universe u

open Cardinal Ordinal Set

/-- `C` is closed and unbounded in the ordinal `κ`: `C ⊆ κ`, `C` is cofinal in `κ`, and every
nonzero `α < κ` in which `C` is cofinal belongs to `C` (only limit `α` can satisfy the premise). -/
def IsClub (κ : Ordinal.{u}) (C : Set Ordinal.{u}) : Prop :=
  C ⊆ Iio κ ∧
  (∀ β < κ, ∃ γ ∈ C, β ≤ γ) ∧
  (∀ α < κ, α ≠ 0 → (∀ β < α, ∃ γ ∈ C, β < γ ∧ γ < α) → α ∈ C)

/-- `S` is stationary in `κ`: a subset of `κ` meeting every club of `κ`. -/
def IsStationary (κ : Ordinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  S ⊆ Iio κ ∧ ∀ C, IsClub κ C → (S ∩ C).Nonempty

/-- `◇_κ(S)`: a sequence `A_α ⊆ α` (`α ∈ S`) guessing every `A ⊆ κ` on a stationary set. -/
def Diamond (κ : Ordinal.{u}) (S : Set Ordinal.{u}) : Prop :=
  ∃ A : Ordinal.{u} → Set Ordinal.{u}, (∀ α ∈ S, A α ⊆ Iio α) ∧
    ∀ X ⊆ Iio κ, IsStationary κ {α | α ∈ S ∧ X ∩ Iio α = A α}

/-- `E^{κ}_{μ}`: the ordinals below `κ` of cofinality `μ`. -/
def cofEq (κ : Ordinal.{u}) (μ : Cardinal.{u}) : Set Ordinal.{u} :=
  {α | α < κ ∧ α.cof = μ}

/-- The generalized continuum hypothesis in universe `u`. -/
def GCH : Prop :=
  ∀ μ : Cardinal.{u}, ℵ₀ ≤ μ → (2 : Cardinal.{u}) ^ μ = Order.succ μ

/-- GCH implies `◇(E^{λ⁺}_{cf(λ)})` for every singular cardinal `λ`. -/
theorem main : GCH.{u} → ∀ lam : Cardinal.{u}, ℵ₀ ≤ lam → lam.ord.cof < lam →
    Diamond (Order.succ lam).ord (cofEq (Order.succ lam).ord lam.ord.cof) := by
  sorry

end OMA.S_wp_generalized_continuum_hypothesis
