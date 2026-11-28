import Mathlib

/-!
# A116731: distinct (flips, iterations) pairs of bubble sort

Source: https://oeis.org/A116731
Credit: @avivorly

Name (%N): Number of permutations of length n which avoid the patterns 321, 2143, 3124; or avoid the
patterns 132, 2314, 4312, etc.

Formula (%F): a(n) = (n^3 - 3*n^2 + 5*n)/3. - Franklin T. Adams-Watters, Sep 13 2006

Conjecture (%C): Conjecture: also counts the distinct pairs (flips, iterations) that a bubble sort program
generates when sorting all permutations of 1..n. - Wouter Meeussen, Dec 13 2008

Conventions:
- `a(n)` is taken from the %F closed form of Adams-Watters, which is how the entry gives `a(n)` for all `n`
  (offset 1); the claim is that, for every `n ≥ 1`, the number of distinct pairs equals `a(n)`. In `ℕ` the
  formula is written `(n ^ 3 + 5 * n - 3 * n ^ 2) / 3`, which is exact: `n ^ 3 + 5 * n ≥ 3 * n ^ 2` for every
  `n`, and `n ^ 3 - 3 * n ^ 2 + 5 * n` is divisible by `3`. (The order `n ^ 3 - 3 * n ^ 2 + 5 * n` would
  truncate at `n = 2`.)
- The model: a bubble sort program is read as the standard bubble sort with early exit. It makes repeated
  left-to-right passes; a pass compares each pair of adjacent entries in turn and swaps them when they are out
  of order, so the larger entry is carried to the right; the program stops after the first pass that makes no
  swap. A flip is one swap: flips is the total number of swaps, and iterations is the number of passes, the
  last pass (the one with no swap) included.
- `pass l` is one pass on the list `l`; it returns the new list and its number of swaps. `run f l` repeats
  passes with fuel `f` and returns `(flips, iterations)`. `stats l` runs it with fuel `l.length * l.length + 1`,
  which never runs out: each pass with a swap removes at least one inversion (exactly one per swap), and a list
  of length `n` has at most `n ^ 2` inversions, so at most `n ^ 2` passes make a swap, and the next pass makes
  none and ends the run.
- A permutation `σ` of `Fin n` is sorted as the list `σ 0 + 1, ..., σ (n - 1) + 1`, a permutation of `1..n`.
- With `n = 3` the model gives the pairs (0,1), (1,2), (2,2), (2,3), (3,3): 5 = a(3).
-/

namespace OMA.S_oeis_a116731

/-- One left-to-right bubble pass: each adjacent out-of-order pair met is swapped, so the larger entry is
carried to the right. Returns the new list and the number of swaps. -/
def pass : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | [x] => ([x], 0)
  | x :: y :: t =>
    if y < x then
      let p := pass (x :: t)
      (y :: p.1, p.2 + 1)
    else
      let p := pass (y :: t)
      (x :: p.1, p.2)
termination_by l => l.length

/-- Bubble sort with early exit on `l`, with fuel `f`: returns `(flips, iterations)`; the last pass, with no
swap, is counted as an iteration. -/
def run : ℕ → List ℕ → ℕ × ℕ
  | 0, _ => (0, 0)
  | f + 1, l =>
    let p := pass l
    if p.2 = 0 then (0, 1)
    else
      let q := run f p.1
      (p.2 + q.1, 1 + q.2)

/-- `(flips, iterations)` of the bubble sort on `l` (the fuel never runs out, see Conventions). -/
def stats (l : List ℕ) : ℕ × ℕ := run (l.length * l.length + 1) l

/-- The distinct `(flips, iterations)` pairs over all permutations of `1..n`. -/
def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) => stats (List.ofFn fun i => (σ i : ℕ) + 1))

theorem main : ∀ n : ℕ, 1 ≤ n → (pairs n).card = (n ^ 3 + 5 * n - 3 * n ^ 2) / 3 := by
  sorry

end OMA.S_oeis_a116731
