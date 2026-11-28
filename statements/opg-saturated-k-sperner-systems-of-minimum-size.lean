import Mathlib

/-!
# Saturated `k`-Sperner systems of minimum size

Source: https://www.openproblemgarden.org/op/saturated_k_sperner_systems_of_minimum_size
Credit: @pyaf

A collection `𝓕 ⊆ 𝓟(X)` is a `k`-Sperner system if it contains no `(k+1)`-chain
`A₁ ⊊ ⋯ ⊊ A_{k+1}`. It is saturated if for every subset `S` of `X` not in `𝓕`, the collection
`𝓕 ∪ {S}` contains a `(k+1)`-chain. Question (Morrison, Noel and Scott): does there exist a constant
`c > 1/2` and a function `n₀(k)` such that if `|X| ≥ n₀(k)`, then every saturated `k`-Sperner
system `𝓕 ⊆ 𝓟(X)` has cardinality at least `2^{(1+o(1))ck}`?

## Encoding

* The ground set `X` is `Fin n` (only `|X|` matters); `𝓟(X)` is `Finset (Fin n)`.
* A `(k+1)`-chain in `𝓕` is a strictly increasing map `Fin (k+1) → Finset (Fin n)` with values
  in `𝓕`.
* `2^{(1+o(1))ck}` as a lower bound: there is `f : ℕ → ℝ` with `f k → 0` as `k → ∞` and
  `|𝓕| ≥ 2^{(1 + f k) c k}` for every `k ≥ 1` and every `n ≥ n₀(k)`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer no.
-/

namespace OMA.S_opg_saturated_k_sperner_systems_of_minimum_size

open Filter Topology

/-- `𝓕` contains a chain `A₀ ⊊ A₁ ⊊ ⋯ ⊊ A_k` of `k + 1` sets. -/
def HasChain {n : ℕ} (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∃ a : Fin (k + 1) → Finset (Fin n), StrictMono a ∧ ∀ i, a i ∈ 𝓕

/-- `𝓕` is a saturated `k`-Sperner system: no `(k+1)`-chain, and adding any new set creates one. -/
def IsSaturatedSperner {n : ℕ} (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ¬ HasChain k 𝓕 ∧ ∀ S ∉ 𝓕, HasChain k (insert S 𝓕)

/-- For some `c > 1/2`, saturated `k`-Sperner systems on large ground sets have size at least
`2^{(1+o(1))ck}`. -/
theorem main :
    ∃ c : ℝ, 1 / 2 < c ∧ ∃ n₀ : ℕ → ℕ, ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
      ∀ k n : ℕ, 1 ≤ k → n₀ k ≤ n → ∀ 𝓕 : Finset (Finset (Fin n)), IsSaturatedSperner k 𝓕 →
        (2 : ℝ) ^ ((1 + f k) * c * k) ≤ 𝓕.card := by
  sorry

end OMA.S_opg_saturated_k_sperner_systems_of_minimum_size
