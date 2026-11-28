import OMAReductions.R_SolitaryNumber_is_ten_solitary_R1

-- Reduction SolitaryNumber.is_ten_solitary.R1.H3.R1 of step SolitaryNumber.is_ten_solitary.R1.H3
-- Credit: @marcusbuffett

/-!
# Odd square friends of 10: at most two prime factors, and the open rest

The parent step says that no odd square `m` has `10 σ(m) = 18 m` (abundancy `9/5`).

* `H1` (elementary): no such `m` has at most two distinct prime factors. The equation gives
  `5 ∣ m`. A power of `5` has abundancy below `5/4`. For `m = 5^e q^f` with `q ≥ 7` the
  abundancy is below `(5/4)(7/6)`. For `q = 3` (with `e` even because `m` is a square)
  `σ(5^e)` is `1` modulo `3` and modulo `5`, so it is coprime to `9 * 5^e * 3^f`, which it would
  have to divide.
* `H2`: three or more distinct prime factors. This stays open (the literature shows that a
  friend of `10` needs at least six).
-/

namespace OMA.R_SolitaryNumber_is_ten_solitary_R1_H3_R1

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- At most two distinct prime factors. -/
def H1 : Prop :=
  ∀ m : ℕ, Odd m → IsSquare m → m.primeFactors.card ≤ 2 → σ 1 m * 10 ≠ 18 * m

/-- The open part: three or more distinct prime factors. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → IsSquare m → 3 ≤ m.primeFactors.card → σ 1 m * 10 ≠ 18 * m

theorem main : H1 → H2 → OMA.R_SolitaryNumber_is_ten_solitary_R1.H3 := by
  intro h1 h2 m hodd hsq
  by_cases hc : m.primeFactors.card ≤ 2
  · exact h1 m hodd hsq hc
  · exact h2 m hodd hsq (by omega)

end OMA.R_SolitaryNumber_is_ten_solitary_R1_H3_R1
