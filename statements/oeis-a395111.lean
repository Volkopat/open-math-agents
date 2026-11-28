import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Radical-constrained partitions and partitions into distinct squarefree parts

Both recurrences count partitions into distinct positive parts bounded by L.
At each step the largest available part is either omitted or taken once.
For radicalWays the second remaining total is the sum of radicals.

Source: https://oeis.org/A395111 and https://oeis.org/A087188
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a395111

open Filter Topology

def rad (n : ℕ) : ℕ :=
  if n = 0 then 0 else n.primeFactorsList.dedup.prod

def radicalWays : ℕ → ℕ → ℕ → ℕ
  | 0, n, s => if n = 0 ∧ s = 0 then 1 else 0
  | L+1, n, s => radicalWays L n s +
      if L+1 ≤ n ∧ rad (L+1) ≤ s then radicalWays L (n-(L+1)) (s-rad (L+1)) else 0

def squareWays : ℕ → ℕ → ℕ
  | 0, n => if n = 0 then 1 else 0
  | L+1, n => squareWays L n +
      if Squarefree (L+1) ∧ L+1 ≤ n then squareWays L (n-(L+1)) else 0

def A (n : ℕ) := radicalWays n n (rad n)
def B (n : ℕ) := squareWays n n

theorem main : Set.range A = Set.range B ∧
    Tendsto (fun N : ℕ => ((((Finset.range N).filter (fun n => A n = 1)).card : ℕ) : ℝ) / N)
      atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a395111
