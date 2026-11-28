import Mathlib

/-!
# A091340: Amicable numbers with property that each member m of the corresponding amicable pair is divisible by sopfr(m) (the sum of prime factors with repetition, A001414).

Source: https://oeis.org/A091340
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite (even though there are many known
amicable numbers, about 8*10^7). Its terms begin 821921625, 988676775, 4024942087978, ...;
both members of each qualifying amicable pair appear.

Reading of the source:
* `s(m) = sigma(m) - m` is the sum of the proper divisors of `m`. A number `m ≥ 1` is amicable if
  `s(m) ≠ m` and `s(s(m)) = m`; its amicable partner is `s(m)`.
* `sopfr(m)` is the sum of the prime factors of `m` counted with multiplicity,
  `(Nat.primeFactorsList m).sum` (e.g. 821921625 = 3^2 * 5^3 * 7 * 29 * 59 * 61 has
  sopfr = 177 = 3 * 59).
* `m` is a term if `m` is amicable, `sopfr(m)` divides `m` and `sopfr(s(m))` divides `s(m)`.
-/

namespace OMA.S_oeis_a091340

/-- The sum of the proper divisors of `m`. -/
def s (m : ℕ) : ℕ := ArithmeticFunction.sigma 1 m - m

/-- The sum of the prime factors of `m` with repetition (A001414). -/
def sopfr (m : ℕ) : ℕ := (Nat.primeFactorsList m).sum

/-- `m` is a term of A091340. -/
def IsTerm (m : ℕ) : Prop :=
  1 ≤ m ∧ s m ≠ m ∧ s (s m) = m ∧ sopfr m ∣ m ∧ sopfr (s m) ∣ s m

theorem main : {m : ℕ | IsTerm m}.Finite := by
  sorry

end OMA.S_oeis_a091340
