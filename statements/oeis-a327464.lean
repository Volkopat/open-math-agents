import Mathlib

/-!
# A327464: base-5 reversals of the next prime or next composite

Source: https://oeis.org/A327464
Credit: @warshanks

`a(1) = 1`; thereafter, `a(n)` is the reversal in base 5 of the next prime after `a(n - 1)` if `n`
is prime, and the reversal in base 5 of the next composite after `a(n - 1)` if `n` is composite
(the values are written in base 10). The entry records one conjecture:

  the maximal value is `107`, first attained at `n = 883`.

`main` states it as: `a(n) ≤ 107` for every `n ≥ 1`, `a(883) = 107`, and `a(n) < 107` for
`1 ≤ n < 883`.

Conventions:
* the reversal in base 5 of `m` reads the base-5 digits of `m` backwards
  (`Nat.ofDigits 5 (Nat.digits 5 m).reverse`), so trailing zeros are dropped: `10₅ = 5 ↦ 1`;
* "the next prime after `m`" is the least prime `> m`, and "the next composite after `m`" is the
  least composite (non-prime and `> 1`) number `> m`; both sets are nonempty, so `sInf` is their
  least element;
* the sequence starts at `n = 1`; the value `a 0` is a placeholder outside the sequence and plays
  no role (every `n ≥ 2` is either prime or composite, and `a 1` does not depend on `a 0`).
-/

namespace OMA.S_oeis_a327464

/-- The reversal of `m` in base 5. -/
def rev5 (m : ℕ) : ℕ := Nat.ofDigits 5 (Nat.digits 5 m).reverse

/-- The next prime after `m`: the least prime `> m`. -/
noncomputable def nextPrime (m : ℕ) : ℕ := sInf {c : ℕ | m < c ∧ c.Prime}

/-- The next composite after `m`: the least composite number `> m`. -/
noncomputable def nextComposite (m : ℕ) : ℕ := sInf {c : ℕ | m < c ∧ 1 < c ∧ ¬ c.Prime}

/-- OEIS A327464 (offset 1): `a 1 = 1`, and for `n ≥ 2`, `a n` is the base-5 reversal of the next
prime after `a (n - 1)` if `n` is prime, and of the next composite after `a (n - 1)` otherwise. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => if (n + 2).Prime then rev5 (nextPrime (a (n + 1))) else rev5 (nextComposite (a (n + 1)))

/-- The conjecture of OEIS A327464: the maximal value of the sequence is `107`, first attained at
`n = 883`. -/
theorem main : (∀ n : ℕ, 1 ≤ n → a n ≤ 107) ∧ a 883 = 107 ∧ ∀ n : ℕ, 1 ≤ n → n < 883 → a n < 107 := by
  sorry

end OMA.S_oeis_a327464
