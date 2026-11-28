import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Minimum-part positions in integer compositions

Source: https://oeis.org/A377824
Credit: @blakestone-x

A minimum occurring several times contributes each of its one-based positions.
All ordered compositions are enumerated by prepending one or increasing the first part.
-/

namespace OMA.S_oeis_a377824

def bump : List ℕ → List ℕ
  | [] => []
  | x :: xs => (x + 1) :: xs

def compositions : ℕ → List (List ℕ)
  | 0 => [[]]
  | 1 => [[1]]
  | n + 2 => (compositions (n+1)).map (List.cons 1) ++
      (compositions (n+1)).map bump

def marks (p : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + marks p xs

def weights (p : ℕ → Bool) : List ℕ → ℕ
  | [] => 0
  | x :: xs => (if p x then 1 else 0) + marks p xs + weights p xs

def minWeights (l : List ℕ) : ℕ :=
  weights (fun x => decide (∀ y ∈ l, x ≤ y)) l

def total (f : List ℕ → ℕ) (n : ℕ) : ℕ :=
  ((compositions n).map f).sum

def a (n : ℕ) : ℕ := total minWeights n

theorem main : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (a n : ℝ))
    (fun n : ℕ => (n : ℝ)^2 * (2 : ℝ)^n / 32) := by
  sorry

end OMA.S_oeis_a377824
