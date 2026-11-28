import Mathlib

/-!
# A090524: Primes arising in A090523, or 0 if no such prime exists

Source: https://oeis.org/A090524
Credit: @xor2k
Sibling of OEIS A090526 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the OEIS A090524 conjecture (offset 3): Conjecture: No term is zero.

Conventions: A090523(n) is the smallest prime `p` such that `floor(n! / p)` is prime, or `0` if no
such prime exists; it is modelled as `sInf` of that set of primes, which is `0` exactly when the set
is empty (no prime is `0`). A090524(n) is `floor(n! / A090523(n))`, or `0` if no such prime exists
(that is, if `A090523(n) = 0`); floor division is `/` on `ℕ`. The conjecture is stated for every
index `n ≥ 3` (the offset).
-/

namespace OMA.S_oeis_a090524

/-- A090523: smallest prime `p` such that `floor(n! / p)` is prime, or `0` if none exists. -/
noncomputable def a090523 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (n.factorial / p).Prime}

/-- A090524: the prime `floor(n! / A090523(n))`, or `0` if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  if a090523 n = 0 then 0 else n.factorial / a090523 n

/-- No term of A090524 is zero for `n ≥ 3`. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090524
