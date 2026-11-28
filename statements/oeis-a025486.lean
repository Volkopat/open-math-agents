import Mathlib

/-!
# A025486

Source: https://oeis.org/A025486
Credit: @RiverMint78

The two sequences are defined from the original iterations in A025485 and
A006892. The use of `sInf` does not assume the conjectured recurrences.
-/

namespace OMA.S_oeis_a025486

/-- The least natural number whose square is at least `x`. -/
def ceilRoot (x : ℕ) : ℕ :=
  if x = 0 then 0 else Nat.sqrt (x - 1) + 1

/-- A025485: distance to the least square at or above the current value. -/
def complement (x : ℕ) : ℕ := ceilRoot x ^ 2 - x

/-- A006892: subtract the greatest square at or below the current value. -/
def subtractSquare (x : ℕ) : ℕ := x - Nat.sqrt x ^ 2

/-- First time an iteration reaches a value at or below `bound`. -/
noncomputable def firstHit (f : ℕ → ℕ) (bound x : ℕ) : ℕ :=
  sInf {t : ℕ | (f^[t]) x ≤ bound}

/-- The iteration reaches the stopping interval. -/
def Reaches (f : ℕ → ℕ) (bound x : ℕ) : Prop :=
  ∃ t : ℕ, (f^[t]) x ≤ bound

/-- Least input whose first-hit time is `n`. -/
noncomputable def leastInput (f : ℕ → ℕ) (bound n : ℕ) : ℕ :=
  sInf {x : ℕ | Reaches f bound x ∧ firstHit f bound x = n}

/-- For n ≥ 3, A025486(n) = A006892(n+1) + 3. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    leastInput complement 2 n = leastInput subtractSquare 0 (n + 1) + 3 := by
  sorry

end OMA.S_oeis_a025486
