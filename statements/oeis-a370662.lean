import Mathlib

/-!
# A370662: Numbers m such that 3 does not divide the m-th Catalan number A000108(m); m such that A067397(m) = 0.

Source: https://oeis.org/A370662
Credit: @luciusacarr

Data: 0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 26, 27, 28, 29, 30, 31, 35, ...

Conjecture (from the entry): the only terms of the form 2^r-1 are 0, 1, 3, 31 and 255. `main`
states it. (The entry adds that, since 2^r - 1 is never 2 mod 3, this is equivalent to saying that
the only numbers of the form 2^r - 1 with no digit 2 in ternary are 0, 1, 3, 31, 255; and that the
conjecture would imply that the n-th Catalan number is divisible by 2 or 3 unless n is one of
these values. Those are consequences, not further conjectures, and are not stated.)

Reading of the source:
* The m-th Catalan number is Mathlib's `catalan m` (A000108, offset 0).
* `r` ranges over the natural numbers `r ≥ 0` (2^0 - 1 = 0).
* "The only terms of the form 2^r - 1 are 0, 1, 3, 31, 255" is stated as: for every `r`,
  3 does not divide `catalan (2^r - 1)` if and only if `2^r - 1` is one of 0, 1, 3, 31, 255
  (i.e. `r ∈ {0, 1, 2, 5, 8}`; checked numerically for r < 400 through the ternary criterion).
-/

namespace OMA.S_oeis_a370662

theorem main :
    -- The only terms of the form 2^r - 1 are 0, 1, 3, 31 and 255.
    ∀ r : ℕ, (¬ 3 ∣ catalan (2 ^ r - 1) ↔ 2 ^ r - 1 ∈ ({0, 1, 3, 31, 255} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a370662
