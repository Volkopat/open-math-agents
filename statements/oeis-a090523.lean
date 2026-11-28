import Mathlib

/-!
# A090523: Smallest prime p such that floor(n!/p) is prime, or 0 if no such prime exists

Source: https://oeis.org/A090523
Credit: @AkiRA-COM-FP

Formalizes the OEIS A090523 conjecture: there are no zeros in `a(n)` for `n > 2`.
-/

namespace OMA.S_oeis_a090523

/-- The OEIS sequence A090523: smallest prime `p` such that `floor(n! / p)` is prime,
or `0` if no such prime exists. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (n.factorial / p).Prime}

/-- There are no zeros in A090523 for `n > 2`. -/
theorem main :
    ∀ n : ℕ, 2 < n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a090523
