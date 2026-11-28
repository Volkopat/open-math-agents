import Mathlib

/-!
# A103362: Reduced numerators of the fraction of primes < 10^n that are full reptend primes.

Source: https://oeis.org/A103362
Credit: @tczyzycki

A full reptend prime (A001913) is a prime `p` for which `10` is a primitive root modulo `p`,
equivalently `p` is prime, `gcd(10, p) = 1`, and the multiplicative order of `10` in `(ℤ/pℤ)ˣ`
equals `p - 1`. The fraction `A103362(n) / A103363(n)` is the proportion of primes `< 10^n`
that are full reptend primes (`A086018(n) / A006880(n)`). The conjecture states that this
proportion tends to Artin's constant `A005596 = ∏_{p prime} (1 - 1 / (p (p - 1)))` as `n → ∞`.
-/

namespace OMA.S_oeis_a103362

/-- A prime `p` is a full reptend prime (OEIS A001913) if `10` is a primitive root modulo `p`. -/
def IsFullReptendPrime (p : ℕ) : Prop :=
  p.Prime ∧ Nat.Coprime 10 p ∧ orderOf (10 : ZMod p) = p - 1

/-- The number of full reptend primes strictly less than `N` (gives OEIS A086018 at `N = 10^n`). -/
noncomputable def fullReptendCount (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).filter IsFullReptendPrime).card

/-- The number of primes strictly less than `N` (gives OEIS A006880 at `N = 10^n`). -/
noncomputable def primeCountLt (N : ℕ) : ℕ :=
  open Classical in
  ((Finset.range N).filter Nat.Prime).card

/-- Artin's constant (OEIS A005596): `∏_{p prime} (1 - 1 / (p * (p - 1)))`. -/
noncomputable def artinConstant : ℝ :=
  ∏' p : Nat.Primes, (1 - 1 / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)))

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (fullReptendCount (10 ^ n) : ℝ) / (primeCountLt (10 ^ n) : ℝ))
      Filter.atTop (nhds artinConstant) := by
  sorry

end OMA.S_oeis_a103362
