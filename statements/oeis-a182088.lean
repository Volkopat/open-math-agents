import Mathlib

/-!
# A182088: Carmichael numbers of the form C = (30n-29)*(60n-59)*(90n-89)*(180n-179), where n is a natural number.

Source: https://oeis.org/A182088
Credit: @agchua

Comment of A182088 (unsigned; the entry is by Marius Coman, Apr 11 2012):
  Conjecture: The number C = (30n-29)*(60n-59)*(90n-89)*(180n-179) is a Carmichael number if
  (but not only if) 30n-29, 60n-59, 90n-89 and 180n-179 are all four prime numbers.
The sequence has offset 1 and n is a natural number, so the claim is stated for n >= 1.
A Carmichael number (A002997) is a composite number c, that is c > 1 and c not prime, such that
b^(c-1) == 1 (mod c) for every b coprime to c. The words (but not only if) say that the converse
fails: for some n >= 1 the number C is a Carmichael number although its four factors are not all
prime. Both parts are stated.
-/

namespace OMA.S_oeis_a182088

/-- A002997: c is a Carmichael number. -/
def IsCarmichael (c : ℕ) : Prop :=
  1 < c ∧ ¬ c.Prime ∧ ∀ b : ℕ, Nat.Coprime b c → b ^ (c - 1) ≡ 1 [MOD c]

/-- C(n) = (30n-29)*(60n-59)*(90n-89)*(180n-179). -/
def C (n : ℕ) : ℕ := (30 * n - 29) * (60 * n - 59) * (90 * n - 89) * (180 * n - 179)

/-- The four factors 30n-29, 60n-59, 90n-89 and 180n-179 are all prime. -/
def AllPrime (n : ℕ) : Prop :=
  (30 * n - 29).Prime ∧ (60 * n - 59).Prime ∧ (90 * n - 89).Prime ∧ (180 * n - 179).Prime

/-- The conjecture: C(n) is a Carmichael number if its four factors are prime, and the converse
fails for some n. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → AllPrime n → IsCarmichael (C n)) ∧
    (∃ n : ℕ, 1 ≤ n ∧ IsCarmichael (C n) ∧ ¬ AllPrime n) := by
  sorry

end OMA.S_oeis_a182088
