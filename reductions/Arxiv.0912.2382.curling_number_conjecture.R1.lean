import FormalConjectures.Arxiv.«0912.2382».CurlingNumberConjecture
import Mathlib

/-!
Reduction Arxiv.0912.2382.curling_number_conjecture.R1: split by whether the curling number
ever appends a new value.

H1 is the structural case: if at some stage `m` the curling number `c = k (S m)` does not yet occur
in `S m`, then the next sequence `S (m + 1) = S m ++ [c]` has curling number 1. Indeed a
decomposition `S m ++ [c] = X Y^r` with `r ≥ 2` ends in a copy of `Y`, whose last entry is `c`,
and the copy of `Y` before it lies inside `S m`, so `c` would already occur. This covers, for
instance, every starting sequence of non-positive integers. A known observation of Chaffin and
Sloane, not progress on the conjecture.

H2 is the open remainder: starting sequences for which every appended curling number already
occurs in the current sequence.
-/

namespace OMA.R_Arxiv_0912_2382_curling_number_conjecture_R1

open Arxiv.«0912.2382»

/-- The conjecture when some appended curling number is a new value. -/
def H1 : Prop :=
  ∀ S₀ : List ℤ, S₀ ≠ [] → (∃ m, ((k (S S₀ m) : ℕ) : ℤ) ∉ S S₀ m) → ∃ m, k (S S₀ m) = 1

/-- The open remainder: every appended curling number already occurs. -/
def H2 : Prop :=
  ∀ S₀ : List ℤ, S₀ ≠ [] → (∀ m, ((k (S S₀ m) : ℕ) : ℤ) ∈ S S₀ m) → ∃ m, k (S S₀ m) = 1

theorem main : H1 → H2 → type_of% @Arxiv.«0912.2382».curling_number_conjecture := by
  intro h1 h2 S₀ hS
  by_cases h : ∃ m, ((k (S S₀ m) : ℕ) : ℤ) ∉ S S₀ m
  · exact h1 S₀ hS h
  · simp only [not_exists, not_not] at h
    exact h2 S₀ hS h

end OMA.R_Arxiv_0912_2382_curling_number_conjecture_R1
