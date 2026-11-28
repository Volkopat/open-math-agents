import Mathlib

/-!
# Injective maps between the low-weight and high-weight vectors of the cube

Source: https://mathoverflow.net/questions/471098
Asked by MathOverflow user West Book.

Let `k > 0` and `k₀ < k` be integers. Let `A ⊆ {0,1}^k` be the set of vectors with more than
`k/2 + k₀` coordinates equal to `0`, and `B ⊆ {0,1}^k` the set of vectors with more than
`k/2 + k₀` coordinates equal to `1`. The question asks whether for every `x ∈ A` there is a
one-to-one map `f_x : A → B` such that for every `a ∈ A`, at every coordinate `i` where `a`
and `f_x(a)` differ one has `a_i = x_i` (and `f_x(a)_i ≠ x_i`).

Translation choices.
* Vectors in `{0,1}^k` are functions `Fin k → Bool`, with `false` for `0` and `true` for `1`.
* More than `k/2 + k₀` zeros means `k + 2 k₀ < 2 * (number of zeros)`, and similarly for ones.
* The map `f_x` is a function on all vectors which sends `A` into `B` and is injective on `A`.
  The condition `f_x(a)_i ≠ x_i` at the coordinates where `a` and `f_x(a)` differ follows from
  `a_i = x_i` there, so only `a_i = x_i` is required.
* The post also suggests the regime `√k < k₀ ≪ k`; the statement uses the general hypothesis
  `k₀ < k` stated first in the post.
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_471098

/-- Number of coordinates of `v` equal to `b`. -/
def cnt {k : ℕ} (v : Fin k → Bool) (b : Bool) : ℕ := (Finset.univ.filter fun i => v i = b).card

/-- The vectors with more than `k/2 + k₀` zeros. -/
def SetA (k k₀ : ℕ) : Set (Fin k → Bool) := {v | k + 2 * k₀ < 2 * cnt v false}

/-- The vectors with more than `k/2 + k₀` ones. -/
def SetB (k k₀ : ℕ) : Set (Fin k → Bool) := {v | k + 2 * k₀ < 2 * cnt v true}

theorem main :
    ∀ k k₀ : ℕ, 0 < k → k₀ < k → ∀ x ∈ SetA k k₀,
      ∃ f : (Fin k → Bool) → (Fin k → Bool),
        (∀ a ∈ SetA k k₀, f a ∈ SetB k k₀) ∧ Set.InjOn f (SetA k k₀) ∧
        ∀ a ∈ SetA k k₀, ∀ i, a i ≠ f a i → a i = x i := by
  sorry

end OMA.S_mo_471098
