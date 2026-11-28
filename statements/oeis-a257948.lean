import Mathlib

/-!
# OEIS A257948: the map s_2 has exactly ten cycles of length > 1

Source: https://oeis.org/A257948 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Pieter Post, May 14 2015), offset 1: Length of cycle in which n ends under iteration of
sum-of-squares-of-two-digits map s_2. If n = abcdef has an even number of digits,
s_2(n) = (ab)^2 + (cd)^2 + (ef)^2; if n = abcde has an odd number of digits,
s_2(n) = (a)^2 + (bc)^2 + (de)^2. Comment: The following statements, densities and conjectures
are based on calculations for n = 1...10000. It is conjectured that iterations of s_2 always end
in cycles of finite period length and besides the 1-cycles there are ten different cycles of
length > 1. The period lengths are 2, 2, 4, 5, 5, 6, 10, 14, 35 or 56.

Formalization notes:
* s2 n is the sum of the squares of the base-100 digits of n, which are exactly the two-digit
  blocks of the entry counted from the right (a leading single digit forms its own block).
* IsCycle c says that the list c is nonempty, has no repetitions, and s2 maps it onto its rotation
  by one place; such a list is a cycle of s2 of length c.length.
* main is the conjunction of the two claims: every orbit is eventually periodic (iterations end in
  cycles of finite period), and there is a list of ten cycles with lengths 2, 2, 4, 5, 5, 6, 10, 14,
  35, 56, pairwise disjoint (the concatenation has no repetitions), that contains every periodic
  point which is not a fixed point (the 1-cycles are excluded, as in the comment).
-/

namespace OMA.S_oeis_a257948

/-- `s_2`: the sum of the squares of the base-100 digits of `n`, that is of its two-digit blocks
counted from the right (A257795). -/
def s2 (n : ℕ) : ℕ := ((Nat.digits 100 n).map (fun d => d ^ 2)).sum

/-- `c` is a cycle of `s2`: a nonempty list without repetitions that `s2` maps onto its rotation by one. -/
def IsCycle (c : List ℕ) : Prop := c ≠ [] ∧ c.Nodup ∧ c.map s2 = c.rotate 1

/-- Post's conjecture: orbits end in cycles, and the cycles of length > 1 are ten cycles of lengths
2, 2, 4, 5, 5, 6, 10, 14, 35 and 56. -/
theorem main :
    (∀ n, ∃ k m, 0 < m ∧ s2^[k + m] n = s2^[k] n) ∧
    ∃ cs : List (List ℕ), cs.map List.length = [2, 2, 4, 5, 5, 6, 10, 14, 35, 56] ∧
      (∀ c ∈ cs, IsCycle c) ∧ cs.flatten.Nodup ∧
      ∀ n, (∃ m, 0 < m ∧ s2^[m] n = n) → s2 n ≠ n → n ∈ cs.flatten := by
  sorry

end OMA.S_oeis_a257948
