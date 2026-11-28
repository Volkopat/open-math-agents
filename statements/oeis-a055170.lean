import Mathlib

/-!
# A055170: The order of first occurrences in A055168 is a permutation

Sources: https://oeis.org/A055170 and https://oeis.org/A055168.

Starting with [0], append a segment by listing each distinct value
already written in first-occurrence order, immediately followed by
its frequency in the entire existing prefix. This is the
noun-before-adjective convention in A055168.

After n added segments, the first-occurrence list contains 0 through n,
so its zero-based position n exists. That entry is a(n) in our convention,
corresponding to position n+1 in the OEIS entry. The proof also shows the
same position persists in every longer prefix.
-/

namespace OMA.S_oeis_a055170

/-- One noun-frequency pair for every distinct noun in the prefix. -/
def nextSegment (xs : List ℕ) : List ℕ :=
  xs.eraseDups.flatMap (fun x => [x, xs.count x])

/-- A055168 through the first n added segments, after the initial zero. -/
def stage : ℕ → List ℕ
  | 0 => [0]
  | n+1 => stage n ++ nextSegment (stage n)

/-- The zero-based first-occurrence sequence. -/
def a (n : ℕ) : ℕ := (stage n).eraseDups.getD n 0

/-- Kimberling's conjecture, proved by Sigrist's zero-count argument. -/
theorem main : Function.Bijective a := by
  sorry

end OMA.S_oeis_a055170
