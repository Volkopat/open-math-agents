import Mathlib

/-!
# Call count for König's memoized Fibonacci algorithm

Thomas König conjectured a logarithmic bound for OEIS A331164.
The cache starts with the values at 0, 1 and 2. Each lookup counts as one call.
Source: https://oeis.org/A331164
-/

namespace OMA.S_oeis_a331164

/-- Arguments requested when expanding a single Fibonacci call. -/
def children (m : ℕ) : Finset ℕ :=
  if m ≤ 2 then ∅
  else if m % 2 = 0 then {m / 2 - 1, m / 2, m / 2 + 1}
  else {m / 2, m / 2 + 1}

/-- Arguments at a given depth of the recursion. -/
def layer (n : ℕ) : ℕ → Finset ℕ
  | 0 => {n}
  | d + 1 => (layer n d).biUnion children

/-- Each distinct reachable argument above 2 expands once. Every recursive edge
strictly decreases its argument, so depths zero through `n` cover all calls. -/
def expanded (n : ℕ) : Finset ℕ :=
  (((Finset.range (n + 1)).biUnion (layer n)).filter fun m => 2 < m)

/-- One initial call, plus every child lookup made by an expanded argument. -/
def calls (n : ℕ) : ℕ := 1 + ∑ m ∈ expanded n, (children m).card

theorem main : (fun n : ℕ => (calls n : ℝ)) =O[Filter.atTop]
    (fun n : ℕ => Real.log (n : ℝ)) := by
  sorry

end OMA.S_oeis_a331164
