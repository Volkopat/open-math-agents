import Mathlib

/-!
# Halting time of Wolfram machine 3626

Peter Bala's conjecture in OEIS A393210. The two states below are A and B
(`false` and `true`). The tape contains the binary expansion of n, with the
head starting at its least significant bit. A move past that boundary halts
and counts as one transition. Rule 3626 has octal digits 7052 in Wolfram's
order (A1, A0, B1, B0).
Sources: https://oeis.org/A393210, https://oeis.org/A069517 and
https://github.com/WolframInstitute/TuringMachine/blob/main/TuringMachine/Libs/ndtm_search/src/models.rs.
Credit: @marcelopierry
-/

namespace OMA.S_oeis_a393210

/-- Bits below the head are stored nearest first. The remaining tape starts
at the head and extends inward, padded with zeros. -/
structure Config where
  stateB : Bool
  lower : List Bool
  high : ℕ

/-- Return one cell toward the boundary in state B after writing the tape. -/
def outward (high : ℕ) : List Bool → Option Config
  | [] => none
  | bit :: lower => some ⟨true, lower, 2*high+bit.toNat⟩

/-- The four transitions of rule 3626. Inward moves push the written bit.
Outward moves expose the nearest bit on the lower stack. -/
def step (c : Config) : Option Config :=
  if c.high % 2 = 0 then some ⟨false, c.stateB :: c.lower, c.high/2⟩
  else outward (if c.stateB then c.high-1 else c.high) c.lower

/-- Exactly t transitions. A halted machine has no further transition. -/
inductive Runs : Config → ℕ → Option Config → Prop where
  | one (c) : Runs c 1 (step c)
  | more {c d t z} : step c = some d → Runs d t z → Runs c (t+1) z

/-- OEIS A069517, the signed sum of the Möbius function over the divisors. -/
def m (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (-1 : ℤ)^(d+1) * ArithmeticFunction.moebius d

/-- The halting time of rule 3626 on n equals the indicated divisor sum. -/
theorem main : ∀ n : ℕ, 0 < n → ∃ t : ℕ,
    Runs ⟨false, [], n⟩ t none ∧
    (t : ℤ) = ∑ d ∈ n.divisors, (m d)^2 * (Nat.totient d : ℤ) := by
  sorry

end OMA.S_oeis_a393210
