import Mathlib.Data.Nat.Prime.Defs

/-!
# Two cycles of the Collatz-2 map

Reinhard Zumkeller records the first repeat in the orbit of 17 and points to the
orbit of 29 as a counterexample to the proposed uniqueness of the cycle of 3.
The indices of the orbits start at zero.

Sources: https://oeis.org/A063041, https://oeis.org/A063042,
https://oeis.org/A063043, and https://oeis.org/A063044.
OEIS Foundation, CC BY-SA 4.0. Lean formalization: @yukimiyazaki.
-/

namespace OMA.S_oeis_a063043

/-- The largest prime at most the bound, with default 1 when the bound is below 2. -/
def primeAtMost : ℕ → ℕ
  | 0 => 1
  | k + 1 => if (k + 1).Prime then k + 1 else primeAtMost k

/-- OEIS A063041, evaluated on its domain of integers at least 2. -/
def step (n : ℕ) : ℕ :=
  if n.Prime then n * primeAtMost (n - 1) + 1 else n / n.minFac

/-- The value after the given number of iterations from the starting point. -/
def orbit (start : ℕ) : ℕ → ℕ
  | 0 => start
  | k + 1 => step (orbit start k)

def cycleOfThree : List ℕ := [3, 7, 36, 18, 9]

/-- Every periodic point of the map on its domain belongs to the cycle of 3. -/
def onlyCycle : Prop :=
  ∀ n : ℕ, 2 ≤ n → (∃ k : ℕ, 0 < k ∧ orbit n k = n) → n ∈ cycleOfThree

theorem main :
    (orbit 17 23 = 9 ∧ orbit 17 28 = 9) ∧
    (∀ i j : Fin 28, orbit 17 i = orbit 17 j ↔ i = j) ∧
    ((List.range 5).map (orbit 3) = cycleOfThree ∧ orbit 3 5 = 3) ∧
    ¬ onlyCycle := by
  sorry

end OMA.S_oeis_a063043
