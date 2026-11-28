import Mathlib

/-!
# OEIS A140427 and the earliest binary de Bruijn cycle of order three

Sean A. Irvine conjectured that A140427 gives partial sums of A169675.
Both sequences start at index zero. The sum at n uses the first n bits.
The dimension sequence is specified by the published recursion in equation
(13) of Doran et al., https://arxiv.org/abs/0806.0051.

Sources: https://oeis.org/A140427 and https://oeis.org/A169675.
-/

namespace OMA.S_oeis_a140427

/-- Maximum dimension of a length-n doubly-even binary code, specified by
the eight initial values of equation (13) and its length-eight recursion. -/
def kappa : ℕ → ℕ
  | 0 | 1 | 2 | 3 => 0
  | 4 | 5 => 1
  | 6 => 2
  | 7 => 3
  | n + 8 => kappa n + 4

/-- Most significant bit first in an eight-bit word, read cyclically. -/
def digit (word i : ℕ) : ℕ :=
  (word / 2 ^ (7 - i % 8)) % 2

/-- All eight cyclic windows of length three must be distinct. -/
def isDeBruijn (word : ℕ) : Bool :=
  let windows := (List.range 8).map fun i =>
    4 * digit word i + 2 * digit word (i+1) + digit word (i+2)
  decide windows.Nodup

/-- For fixed-width words, increasing numeric order is lexicographic order. -/
theorem main : ∃ word : ℕ,
    (List.range 256).find? isDeBruijn = some word ∧
    ∀ n : ℕ, kappa n = ∑ i ∈ Finset.range n, digit word i := by
  sorry

end OMA.S_oeis_a140427
