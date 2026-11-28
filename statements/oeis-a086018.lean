import Mathlib

/-!
# A086018: Number of cyclic numbers (A001913) <= 10^n.

Source: https://oeis.org/A086018
Credit: @gblacher2

Conjecture (formula line of A086018): "Conjectured ratio a(n)/A006880(n) as n->infinity is
Artin's constant 0.3739558136..."

Definitions used, all from the OEIS:
* A001913 (https://oeis.org/A001913), "Full reptend primes: primes with primitive root 10",
  i.e. the primes `p` for which `10` has multiplicative order `p - 1` modulo `p` (equivalently,
  the decimal expansion of `1/p` has period `p - 1`); A086018 notes that its "cyclic numbers"
  are exactly these;
* A086018(n), offset 0, is the number of terms of A001913 that are `≤ 10^n`;
* A006880(n), "Number of primes < 10^n", is `Nat.primeCounting' (10 ^ n)`;
* Artin's constant (A005596) is `Product_{p=prime} (1-1/(p^2-p))`, written here as in
  `FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean`.

The source only claims the limit of the ratio along `x = 10^n`, so that is what is stated; it is
the case `a = 10` of the density form of Artin's primitive root conjecture, sampled at powers
of 10. (For `n = 0` the denominator is `0`; the value of the ratio there does not affect the
limit.)
-/

namespace OMA.S_oeis_a086018

open Filter Topology

/-- `p` is in A001913: a prime with primitive root `10`, i.e. `10` has multiplicative order
`p - 1` modulo `p`. -/
def IsFullReptendPrime (p : ℕ) : Prop :=
  p.Prime ∧ orderOf (10 : ZMod p) = p - 1

/-- A086018(n): the number of full reptend primes (A001913) that are `≤ 10^n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {p : ℕ | p ≤ 10 ^ n ∧ IsFullReptendPrime p}.ncard

/-- Artin's constant `∏_{p prime} (1 - 1/(p(p-1)))` (A005596). -/
noncomputable def artinConstant : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / ((p : ℝ) * ((p : ℝ) - 1)))

/-- The conjecture: `a(n) / A006880(n)` tends to Artin's constant as `n → ∞`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (Nat.primeCounting' (10 ^ n) : ℝ)) atTop
      (𝓝 artinConstant) := by
  sorry

end OMA.S_oeis_a086018
