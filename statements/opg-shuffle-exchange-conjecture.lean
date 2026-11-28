import Mathlib

/-!
# Shuffle-Exchange Conjecture

Source: https://www.openproblemgarden.org/op/shuffle_exchange_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For integers `k, n ≥ 2` let `𝔖` be the symmetric group on the words of length `n` over a
`k`-letter alphabet, `σ ∈ 𝔖` the shuffle `σ(x₁ x₂ … xₙ) = x₂ … xₙ x₁`, and `𝔊 ≤ 𝔖` the exchange
group of permutations preserving the first `n - 1` letters of every word. `d(k, n)` is the
smallest `d ≥ 2` with `𝔖 = (σ𝔊)^d = σ𝔊σ𝔊⋯σ𝔊` (`d` factors).

Conjecture (Shuffle-Exchange, Beneš): `d(k, n) = 2n - 1` for all `k, n ≥ 2`.

Conventions:
* Words are maps `Fin n → Fin k`; letter `xᵢ₊₁` sits at position `i : Fin n`. The shuffle sends
  `x` to `x ∘ finRotate n`, since `finRotate n i = i + 1 (mod n)`.
* `(σ𝔊)^d` is the set of products `σ g₁ σ g₂ ⋯ σ g_d` with all `gᵢ ∈ 𝔊`, products taken in
  `Equiv.Perm`. `d(k, n)` is the infimum of `{d ≥ 2 | (σ𝔊)^d = 𝔖}`.
-/

namespace OMA.S_opg_shuffle_exchange_conjecture

/-- Words of length `n` over `k` letters. -/
abbrev Word (k n : ℕ) := Fin n → Fin k

/-- The shuffle permutation `x₁ x₂ … xₙ ↦ x₂ … xₙ x₁`. -/
def shuffle (k n : ℕ) : Equiv.Perm (Word k n) :=
  (finRotate n).symm.arrowCongr (Equiv.refl (Fin k))

/-- The exchange group: permutations preserving the first `n - 1` letters of every word. -/
def exchange (k n : ℕ) : Set (Equiv.Perm (Word k n)) :=
  {g | ∀ x : Word k n, ∀ i : Fin n, i.val < n - 1 → g x i = x i}

/-- `(σ𝔊)^d`: products `σ g₁ σ g₂ ⋯ σ g_d` with `gᵢ ∈ 𝔊`. -/
def shuffleExchangePow (k n : ℕ) : ℕ → Set (Equiv.Perm (Word k n))
  | 0 => {1}
  | d + 1 => {p | ∃ a ∈ shuffleExchangePow k n d, ∃ g ∈ exchange k n, p = a * (shuffle k n * g)}

/-- `d(k, n)`: the least `d ≥ 2` with `(σ𝔊)^d = 𝔖`. -/
noncomputable def d (k n : ℕ) : ℕ :=
  sInf {d : ℕ | 2 ≤ d ∧ shuffleExchangePow k n d = Set.univ}

/-- The Shuffle-Exchange Conjecture: `d(k, n) = 2n - 1` for all `k, n ≥ 2`. -/
theorem main : ∀ k n : ℕ, 2 ≤ k → 2 ≤ n → d k n = 2 * n - 1 := by
  sorry

end OMA.S_opg_shuffle_exchange_conjecture
