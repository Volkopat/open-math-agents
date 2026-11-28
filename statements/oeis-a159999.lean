import Mathlib

/-!
# Counts on the stopped Collatz trajectory

Source: https://oeis.org/A159999 and https://oeis.org/A076228
Credit: @etaubman

A159999 counts terms at most the starting value. A076228 counts terms strictly
below it. Both stop at the first visit to 1 and include both endpoints.
The conditional identity was recorded by R. J. Mathar on June 24, 2021.
-/

namespace OMA.S_oeis_a159999

def collatzStep (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

def trajectory (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => collatzStep (trajectory n k)

def Collatz : Prop := ∀ n : ℕ, 0 < n → ∃ k : ℕ, trajectory n k = 1

/-- For a convergent trajectory this is its first hitting time for 1. -/
noncomputable def stopping (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, trajectory n k = 1 then Nat.find h else 0

noncomputable def hits (n : ℕ) (p : ℕ → Prop) [DecidablePred p] : Finset ℕ :=
  (Finset.range (stopping n + 1)).filter (fun i => p (trajectory n i))

theorem main : Collatz → ∀ n : ℕ, 0 < n →
    (∀ i j : ℕ, i < j → j ≤ stopping n → trajectory n i ≠ trajectory n j) ∧
    (hits n (· ≤ n)).card = 1 + (hits n (· < n)).card := by
  sorry

end OMA.S_oeis_a159999
