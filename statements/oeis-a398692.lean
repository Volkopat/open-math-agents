import Mathlib

/-!
# Reversed Collatz trajectories (OEIS A398692)

Source: https://oeis.org/A398692
Credit: @etaubman

The initial printed list is [1]. Each extension starts at the least missing
positive integer, walks up to the first previously printed value, and appends
the new values in reverse order. A finite completed stage exists only when
the corresponding walks have stopped. The word "natural" in the OEIS comment
refers to positive integers, as in its sequence definition.
-/

namespace OMA.S_oeis_a398692

def step (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The finite Collatz trajectory from a starting value can reach one. -/
inductive ReachesOne : ℕ → Prop
  | one : ReachesOne 1
  | back {n} : ReachesOne (step n) → ReachesOne n

def Collatz : Prop := ∀ n : ℕ, 0 < n → ReachesOne n

/-- The new block, reversed, ending immediately before the first old entry. -/
inductive Walk (old : List ℕ) : ℕ → List ℕ → Prop
  | hit {n} : n ∈ old → Walk old n []
  | fresh {n tail} : n ∉ old → Walk old (step n) tail → Walk old n (tail ++ [n])

inductive Stage : List ℕ → Prop
  | initial : Stage [1]
  | extend {old block : List ℕ} {seed : ℕ} :
      Stage old → 0 < seed → seed ∉ old →
      (∀ k, 0 < k → k < seed → k ∈ old) →
      Walk old seed block → Stage (old ++ block)

def printed : Set ℕ := {n | ∃ xs, Stage xs ∧ n ∈ xs}

theorem main : (printed.Infinite ∧ (∀ n : ℕ, 0 < n → n ∈ printed)) ↔ Collatz := by
  sorry

end OMA.S_oeis_a398692
