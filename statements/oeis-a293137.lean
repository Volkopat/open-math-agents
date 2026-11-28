import Mathlib

/-!
# A293137: a(0) = 0, and a(n) = floor(2*sqrt(n)) - 1 for n >= 1.

Source: https://oeis.org/A293137
Credit: @rickmanelius

Conjecture: a(n) is index k of last nonzero entry in row n of A293136.

Formalization notes:
* A293136 is the irregular triangle T(n,k): the number of strongly unimodal compositions of n
  (A059618) into k parts. A composition of n is Mathlib's `Composition n` (an ordered list of
  positive parts with sum n), and its number of parts is `Composition.length`.
* A composition (a_1, ..., a_s) is strongly unimodal when a_1 < ... < a_r > ... > a_s for some
  peak position r: its list of parts is l1 ++ p :: l2 with l1 ++ [p] strictly increasing and
  p :: l2 strictly decreasing. The empty composition of 0 is counted, as in the source (row 0 of
  A293136 is [1]).
* Row n of A293136 lists T(n,0), T(n,1), ... and a(n) is the index of its last nonzero entry:
  T(n, a(n)) is nonzero and T(n, k) = 0 for every k > a(n).
* floor(2*sqrt(n)) uses the real square root, as in the definition. For n >= 1 it is at least 2,
  so the natural number subtraction of 1 is exact.
-/

namespace OMA.S_oeis_a293137

/-- A293137: a(0) = 0, and a(n) = floor(2*sqrt(n)) - 1 for n >= 1. -/
noncomputable def a (n : ℕ) : ℕ := if n = 0 then 0 else ⌊2 * Real.sqrt n⌋₊ - 1

/-- Strongly unimodal list: a_1 < ... < a_r > ... > a_s for some peak a_r, or the empty list. -/
def StronglyUnimodal (l : List ℕ) : Prop :=
  l = [] ∨ ∃ l₁ p l₂, l = l₁ ++ p :: l₂ ∧ (l₁ ++ [p]).Pairwise (· < ·) ∧
    (p :: l₂).Pairwise (· > ·)

open Classical in
/-- A293136: T(n,k), the number of strongly unimodal compositions of n into k parts. -/
noncomputable def T (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun c : Composition n => c.length = k ∧ StronglyUnimodal c.blocks)).card

/-- a(n) is the index k of the last nonzero entry in row n of A293136. -/
theorem main : ∀ n : ℕ, T n (a n) ≠ 0 ∧ ∀ k, a n < k → T n k = 0 := by
  sorry

end OMA.S_oeis_a293137
