import Mathlib

/-!
# A239241: distinct-part partitions with as many odd as even parts (Kotesovec's constant)

Source: https://oeis.org/A239241 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A239241 (offset 0): number of partitions of n into distinct parts for which (number of odd
parts) = (number of even parts); data 1, 0, 0, 1, 0, 2, 0, 3, 0, 4, 1, 5, ...

The entry records (Vaclav Kotesovec, Feb 19 2026):

  a(n) ~ c * exp(Pi*sqrt(n/3)) / n.
  Conjecture: c = 1/(2^(5/2)*3^(1/2)).

Reading of the source:
* `a n` counts the partitions of `n` (Mathlib's `Nat.Partition n`, whose parts are positive)
  whose parts are pairwise distinct and contain as many odd parts as even parts. The empty
  partition of 0 counts (a(0) = 1); for n = 3 the only one is 1 + 2.
* The conjecture is the asymptotic equivalence `a(n) ~ c exp(π √(n/3)) / n` with the stated
  value `c = 1 / (2^(5/2) √3)`, as `n → ∞` over the naturals (`~[atTop]`, ratio tending to 1).
  (The first line, with an unspecified `c`, is the existence of such a constant; it is implied.)
-/

namespace OMA.S_oeis_a239241

open Asymptotics Filter

/-- A239241(n): partitions of `n` into distinct parts with equally many odd and even parts. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Nat.Partition n =>
    p.parts.Nodup ∧ (p.parts.filter Odd).card = (p.parts.filter Even).card)).card

/-- Kotesovec's conjecture: `a(n) ~ exp(π √(n/3)) / (2^(5/2) √3 n)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      (fun n : ℕ => 1 / ((2 : ℝ) ^ ((5 : ℝ) / 2) * Real.sqrt 3) *
        Real.exp (Real.pi * Real.sqrt ((n : ℝ) / 3)) / n) := by
  sorry

end OMA.S_oeis_a239241
