import Mathlib

/-!
# A007782: Number of factors of the Kolakoski word

Source: https://oeis.org/A007782
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of different factors (contiguous subwords) of length `n` of the Kolakoski
sequence A000002 `1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, …`. It is conjectured that `a(n)` grows
like `n^(log 3 / log (3/2))`.

## Encoding

* The Kolakoski sequence is generated from the prefix `[1, 2, 2]`: at step `j ≥ 2` append
  `K(j)` copies of `1` if `j` is even and of `2` if `j` is odd; `kol n` reads entry `n` of the
  list after `n` steps (it has length `> n`). Values checked against A000002.
* `a n` is the number of distinct length-`n` lists `[K(i), …, K(i+n-1)]`, `i ∈ ℕ`.
* "Grows like `n^α`" is read as polynomial growth of exponent exactly `α`:
  `log a(n) / log n → log 3 / log (3/2)`.
-/

namespace OMA.S_oeis_a007782

open Filter Topology

/-- The Kolakoski generation process: the list after `k` steps. -/
def gen : ℕ → List ℕ
  | 0 => [1, 2, 2]
  | k + 1 =>
    let L := gen k
    L ++ List.replicate (L.getD (k + 2) 0) (if (k + 2) % 2 = 0 then 1 else 2)

/-- The Kolakoski sequence (0-indexed). -/
def kol (n : ℕ) : ℕ := (gen n).getD n 0

/-- `a n`: the number of distinct factors of length `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {w : List ℕ | ∃ i : ℕ, w = (List.range n).map fun t => kol (i + t)}

theorem main :
    Tendsto (fun n : ℕ => Real.log (a n) / Real.log n) atTop
      (𝓝 (Real.log 3 / Real.log (3 / 2))) := by
  sorry

end OMA.S_oeis_a007782
