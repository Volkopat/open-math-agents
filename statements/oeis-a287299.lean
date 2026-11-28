import Mathlib

/-!
# A287299: Number of ways of writing n as a sum of a proper prime power (A246547) and a nonprime squarefree number (A000469).

Source: https://oeis.org/A287299
Credit: @ceejcake

Conjecture (Ilya Gutkovskiy, 2017, stated in the OEIS entry): `a(n) > 0` for all `n > 108`.

Formalization notes:
* The sequence has offset `0` (`n : ℕ`).
* A proper prime power (A246547) is `p ^ k` with `p` prime and `k ≥ 2`; in Mathlib terms this is
  `IsPrimePow u ∧ ¬ u.Prime` (`IsPrimePow` requires exponent `k ≥ 1`, and the case `k = 1` is
  exactly the primes).
* A nonprime squarefree number (A000469) is `v ≥ 1` with `Squarefree v ∧ ¬ v.Prime`; this
  includes `v = 1` (A000469 starts `1, 6, 10, 14, ...`). The explicit `0 < v` is redundant
  since `Squarefree 0` is false, but is kept for readability.
* `a n` counts the `u` with `0 ≤ u ≤ n` such that `u` is a proper prime power and `v = n - u`
  is a nonprime squarefree number, i.e. the pairs `(u, v)` of natural numbers with `u + v = n`
  (each pair is determined by `u`, and `u ≤ n` is forced, so `Finset.range (n + 1)` loses no
  solutions). This matches the generating function in the entry.
* Initial values for `n = 0, 1, ..., 15`:
  `a(n) = 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 2, 1, ...`; `a(26) = 3`
  (`25 + 1`, `4 + 22`, `16 + 10`); the last zero in the data is `a(108) = 0`.
-/

namespace OMA.S_oeis_a287299

/-- `u` is a proper prime power `p ^ k` with `p` prime and `k ≥ 2` (OEIS A246547). -/
def IsProperPrimePow (u : ℕ) : Prop := IsPrimePow u ∧ ¬ u.Prime

instance : DecidablePred IsProperPrimePow := fun u => by
  unfold IsProperPrimePow; infer_instance

/-- `v` is a nonprime squarefree number, including `1` (OEIS A000469). -/
def IsNonprimeSquarefree (v : ℕ) : Prop := 0 < v ∧ Squarefree v ∧ ¬ v.Prime

instance : DecidablePred IsNonprimeSquarefree := fun v => by
  unfold IsNonprimeSquarefree; infer_instance

/-- `a n` is the number of ways to write `n = u + v` with `u` a proper prime power and `v` a
nonprime squarefree number (OEIS A287299). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter fun u => IsProperPrimePow u ∧ IsNonprimeSquarefree (n - u)).card

/-- OEIS A287299 conjecture (Ilya Gutkovskiy): `a n > 0` for every `n > 108`. -/
theorem main : ∀ n : ℕ, 108 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a287299
