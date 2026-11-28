import Mathlib

/-!
# A282290: Expansion of (Sum{p prime, i>=2} x^(p^i))*(Sum{j>=2} mu(j)^2*x^j), where mu() is the Moebius function (A008683).

Source: https://oeis.org/A282290
Credit: @ceejcake

The entry's comment reads: number of ways of writing `n` as a sum of a proper prime power
(A246547) and a squarefree number `> 1` (A144338).

Conjecture (Ilya Gutkovskiy, 2017, stated in the OEIS entry): `a(n) > 0` for all `n > 8`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* A proper prime power (A246547) is `p ^ i` with `p` prime and `i ≥ 2`; in Mathlib terms this
  is `IsPrimePow u ∧ ¬ u.Prime` (`IsPrimePow` requires exponent `i ≥ 1`, and the case `i = 1`
  is exactly the primes).
* A squarefree number `> 1` (A144338) is `v` with `1 < v ∧ Squarefree v`; this matches the
  factor `Sum_{j ≥ 2} mu(j)^2 x^j` of the generating function. Primes are allowed, `1` is not.
* `a n` counts the `u` with `0 ≤ u ≤ n` such that `u` is a proper prime power and `v = n - u`
  is a squarefree number `> 1`, i.e. the pairs `(u, v)` of natural numbers with `u + v = n`
  (each pair is determined by `u`, and `u ≤ n` is forced, so `Finset.range (n + 1)` loses no
  solutions). This is the coefficient of `x ^ n` in the generating function of the entry.
* Initial values for `n = 0, 1, ..., 15`:
  `a(n) = 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 2, 3, 1, 1, 3, 3, ...`; `a(19) = 4`
  (`16 + 3`, `4 + 15`, `8 + 11`, `9 + 10`); the last zero in the data is `a(8) = 0`.
-/

namespace OMA.S_oeis_a282290

/-- `u` is a proper prime power `p ^ i` with `p` prime and `i ≥ 2` (OEIS A246547). -/
def IsProperPrimePow (u : ℕ) : Prop := IsPrimePow u ∧ ¬ u.Prime

instance : DecidablePred IsProperPrimePow := fun u => by
  unfold IsProperPrimePow; infer_instance

/-- `v` is a squarefree number greater than `1` (OEIS A144338). -/
def IsSquarefreeGtOne (v : ℕ) : Prop := 1 < v ∧ Squarefree v

instance : DecidablePred IsSquarefreeGtOne := fun v => by
  unfold IsSquarefreeGtOne; infer_instance

/-- `a n` is the number of ways to write `n = u + v` with `u` a proper prime power and `v` a
squarefree number greater than `1` (OEIS A282290). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun u => IsProperPrimePow u ∧ IsSquarefreeGtOne (n - u)).card

/-- OEIS A282290 conjecture (Ilya Gutkovskiy): `a n > 0` for every `n > 8`. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a282290
