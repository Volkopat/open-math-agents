import Mathlib

/-!
# OEIS A399307: the Lucas–Collatz orbit conjecture away from multiples of five

Source: https://oeis.org/A399307
Lucas representation and iteration: https://oeis.org/A130310 and https://oeis.org/A399721
Credit: @gblacher2
-/

namespace OMA.S_oeis_a399307

/-- The weight at index `i` in the minimal Lucas representation. -/
def lucasWeight : ℕ → ℕ
  | 0 => 2
  | i + 1 => Nat.fib (i + 2) + Nat.fib i

/-- Collect the usable weights from `L₂ = 3` onward in descending order. -/
def descendingWeights (bound : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, _, _, _, weights => weights
  | fuel + 1, index, previous, current, weights =>
      if current ≤ bound then
        descendingWeights bound fuel (index + 1) current (previous + current)
          ((index, current) :: weights)
      else weights

/-- Greedy Lucas representation stored as the ascending indices of its set bits. -/
def lucasIndices (n : ℕ) : List ℕ :=
  let weights := descendingWeights n n 2 1 3 []
  let (remainder, indices) := weights.foldl
    (fun (remaining, indices) (index, weight) =>
      if weight ≤ remaining then (remaining - weight, index :: indices)
      else (remaining, indices)) (n, [])
  match remainder with
  | 1 => 1 :: indices
  | 2 => 0 :: indices
  | _ => indices

/-- Remove the final zero only if the shifted indices still give a minimal representation. -/
def step (n : ℕ) : ℕ :=
  let indices := lucasIndices n
  let shifted := indices.map (· - 1)
  let value := (shifted.map lucasWeight).sum
  if 0 ∉ indices ∧ lucasIndices value = shifted then value else 2 * n

def a (index : ℕ) : ℕ := (step^[index]) 23

theorem main : ∀ n : ℕ, 0 < n → ¬ 5 ∣ n →
    ∃ k : ℕ, (∃ j < 132, (step^[k]) n = a j) ∨ (step^[k]) n ∈ ({2, 4, 3, 1} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a399307
