import Mathlib

/-!
# Quasi-Noetherian sets of positive integers and the sum of reciprocals

Source: https://mathoverflow.net/questions/404886
Asked by MathOverflow user Sylvain JULIEN (Quasi-ideals and Erdős conjecture on arithmetic
progressions).

Let `A` be a set of positive integers. A `k`-quasi-ideal of `A` is a set `J` of `k + 1`
consecutive nonnegative integers such that there is a couple `(a, c) ∈ A²` with
`a + cJ ⊆ A`; a quasi-ideal of `A` is a `k`-quasi-ideal for some positive integer `k`. The
set `A` is quasi-Noetherian if every increasing sequence of quasi-ideals of `A` is
stationary. The question asks whether every quasi-Noetherian `A` satisfies
`∑_{n ∈ A} 1/n < ∞`.

Translation choices.
* Sets of integers are `Set ℕ`; positivity of `A` is the hypothesis `∀ n ∈ A, 0 < n`.
* A set of `k + 1` consecutive nonnegative integers is an interval `Set.Icc m (m + k)`, and
  `a + cJ ⊆ A` means `a + c * j ∈ A` for all `j ∈ J` (`IsQuasiIdeal`).
* An increasing sequence of quasi-ideals is a monotone sequence `s : ℕ → Set ℕ` of
  quasi-ideals; it is stationary if it is eventually constant (`QuasiNoetherian`).
* Convergence of `∑_{n ∈ A} 1/n` is `Summable` of `n ↦ 1 / n` over the subtype `A`.
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_404886

/-- `J` is a quasi-ideal of `A`: `k + 1` consecutive integers (`k ≥ 1`) with `a + cJ ⊆ A`
for some `a, c ∈ A`. -/
def IsQuasiIdeal (A : Set ℕ) (J : Set ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ m : ℕ, J = Set.Icc m (m + k) ∧
    ∃ a ∈ A, ∃ c ∈ A, ∀ j ∈ J, a + c * j ∈ A

/-- Every increasing sequence of quasi-ideals of `A` is stationary. -/
def QuasiNoetherian (A : Set ℕ) : Prop :=
  ∀ s : ℕ → Set ℕ, (∀ i, IsQuasiIdeal A (s i)) → Monotone s → ∃ N, ∀ n ≥ N, s n = s N

theorem main :
    ∀ A : Set ℕ, (∀ n ∈ A, 0 < n) → QuasiNoetherian A →
      Summable (fun n : A => (1 : ℝ) / (n : ℕ)) := by
  sorry

end OMA.S_mo_404886
