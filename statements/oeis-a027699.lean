import Mathlib

/-!
# A027699: Evil primes.

Source: https://oeis.org/A027699
Name: Evil primes: primes with even number of 1's in their binary expansion.
Conjecture (Vladimir Shevelev, Jun 01 2007): If `pi_1(m)` is the number of
A027699 terms not exceeding `m` and `pi_2(m)` is the number of A027697 terms
(odious primes, primes with an odd number of 1's in binary) not exceeding `m`,
then `pi_1(m) <= pi_2(m)` for all natural `m` except `m = 5` and `m = 6`.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We count over `{0, ..., m}` (only primes contribute, so this matches "not
exceeding `m`").  Parity of the binary digit sum is taken mod `2`: `0` means
evil, `1` means odious.  The exceptional values are exactly `5` and `6`, where
the evil primes `3, 5` outnumber the odious prime `2`.  The body stays `sorry`;
a person reviews the translation before merging.
-/

noncomputable section

open scoped Classical

namespace OMA.S_oeis_a027699

/-- Binary digit sum of `n`. -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- Number of evil primes (even binary weight) not exceeding `m`. -/
def piEvil (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter
    (fun n => Nat.Prime n && s2 n % 2 = 0)).card

/-- Number of odious primes (odd binary weight) not exceeding `m`. -/
def piOdious (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter
    (fun n => Nat.Prime n && s2 n % 2 = 1)).card

theorem main :
    ∀ m : ℕ, m ≠ 5 → m ≠ 6 → piEvil m ≤ piOdious m := by
  sorry

end OMA.S_oeis_a027699

end
