import Mathlib

/-!
# A003625. Irreducibility of a quadratic over prime fields

Federico Provvedi's 21 July 2018 conjecture characterizes the primes in
residue classes 3, 5 and 6 modulo 7 by irreducibility of X² + X + 2.
Source: https://oeis.org/A003625 (OEIS Foundation, CC BY-SA 4.0).
Formalization by @anmolspace with Codex.
-/

namespace OMA.S_oeis_a003625

open Polynomial

theorem main : ∀ (p : ℕ) [Fact p.Prime],
    (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6) ↔
      Irreducible ((X : (ZMod p)[X]) ^ 2 + X + 2) := by
  sorry

end OMA.S_oeis_a003625
