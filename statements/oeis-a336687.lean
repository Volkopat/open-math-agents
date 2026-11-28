import Mathlib

/-!
# A336687: Numbers m such that tau(sigma(m)) and sigma(tau(m)) both divide m, where tau(m) is the number of divisors function (A000005) and sigma(m) is the sum of divisors function (A000203).

Source: https://oeis.org/A336687
Credit: @azmiozgen

Conjecture (Ivan N. Ianakiev, Aug 06 2020; the entry notes it was proved, see Ren (2026)): the
only m such that m = tau(sigma(m))*sigma(tau(m)) are in {1, 468, 3240}. (A further conjecture of
the entry, about the cycles of the iteration n -> tau(sigma(n))*sigma(tau(n)), is not stated
here.)

Formalization notes:
* tau = `Nat.divisors.card`, sigma = `ArithmeticFunction.sigma 1`.
* Stated for every m ≥ 1 as an equivalence (1, 468 and 3240 do satisfy the equation).
* Controls (computed): the m < 200000 with m = tau(sigma(m))*sigma(tau(m)) are 1, 468, 3240.
-/

namespace OMA.S_oeis_a336687

open ArithmeticFunction

/-- Ianakiev's statement: `m = τ(σ(m)) σ(τ(m))` exactly for `m ∈ {1, 468, 3240}`. -/
theorem main :
    ∀ m : ℕ, 1 ≤ m →
      (m = (sigma 1 m).divisors.card * sigma 1 m.divisors.card ↔ m = 1 ∨ m = 468 ∨ m = 3240) := by
  sorry

end OMA.S_oeis_a336687
