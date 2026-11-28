import Mathlib

/-!
# O-minimal expansions of the real field with fast-growing functions

Source: https://mathoverflow.net/questions/121010
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow): is there an o-minimal expansion of the real field with functions of
growth higher than every iterated exponential (a trans-exponential function)?

Conventions:
* As in the standard formulation of this question (the known o-minimal structures with rapid
  growth are expansions of the real field), we ask for an o-minimal expansion of the ordered
  field `ℝ`. Structures are given in van den Dries' set form: a family `D n` of subsets of `ℝⁿ`
  (the definable sets, parameters allowed) that is a Boolean algebra in each `n`, is closed under
  `A ↦ A × ℝ`, `A ↦ ℝ × A` and the projection `ℝⁿ⁺¹ → ℝⁿ` forgetting the last coordinate,
  contains the diagonals `{x | xᵢ = xⱼ}`, every singleton of `ℝ`, the order `{x | x₀ < x₁}` and the
  graphs of `+` and `·`. It is o-minimal if every set in `D 1` is a finite union of points and
  open intervals (possibly unbounded).
* A function `f : ℝ → ℝ` is definable if its graph is in `D 2`, and trans-exponential if it
  eventually exceeds every finite iterate of `exp`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_121010

/-- `D` is (the family of definable sets of) a structure expanding the ordered field `ℝ`. -/
def IsExpansionOfRealField (D : ∀ n : ℕ, Set (Set (Fin n → ℝ))) : Prop :=
  (∀ n, Set.univ ∈ D n) ∧
  (∀ n, ∀ A ∈ D n, Aᶜ ∈ D n) ∧
  (∀ n, ∀ A ∈ D n, ∀ B ∈ D n, A ∪ B ∈ D n) ∧
  (∀ n, ∀ A ∈ D n, {x : Fin (n + 1) → ℝ | Fin.init x ∈ A} ∈ D (n + 1)) ∧
  (∀ n, ∀ A ∈ D n, {x : Fin (n + 1) → ℝ | Fin.tail x ∈ A} ∈ D (n + 1)) ∧
  (∀ n, ∀ A ∈ D (n + 1), Fin.init '' A ∈ D n) ∧
  (∀ n (i j : Fin n), {x : Fin n → ℝ | x i = x j} ∈ D n) ∧
  (∀ r : ℝ, {x : Fin 1 → ℝ | x 0 = r} ∈ D 1) ∧
  {x : Fin 2 → ℝ | x 0 < x 1} ∈ D 2 ∧
  {x : Fin 3 → ℝ | x 0 + x 1 = x 2} ∈ D 3 ∧
  {x : Fin 3 → ℝ | x 0 * x 1 = x 2} ∈ D 3

/-- O-minimality: every definable subset of `ℝ` is a finite union of points and open
intervals. -/
def IsOMinimal (D : ∀ n : ℕ, Set (Set (Fin n → ℝ))) : Prop :=
  ∀ A ∈ D 1, ∃ (s : Finset ℝ) (I : Finset (EReal × EReal)),
    {t : ℝ | (fun _ => t) ∈ A} = (s : Set ℝ) ∪ ⋃ p ∈ I, {t : ℝ | p.1 < (t : EReal) ∧ (t : EReal) < p.2}

theorem main :
    ∃ (D : ∀ n : ℕ, Set (Set (Fin n → ℝ))) (f : ℝ → ℝ),
      IsExpansionOfRealField D ∧ IsOMinimal D ∧
      {x : Fin 2 → ℝ | f (x 0) = x 1} ∈ D 2 ∧
      ∀ k : ℕ, ∀ᶠ t in Filter.atTop, Real.exp^[k] t < f t := by
  sorry

end OMA.S_mo_121010
