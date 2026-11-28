import Mathlib

/-!
# A307244: a(0) = 1; a(n) is the smallest integer k > a(n-1) such that 3^(k-1) == 1 (mod a(n-1)*k).

Source: https://oeis.org/A307244
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A307244 (Thomas Ordowski, Mar 30 2019): a(n) is prime for every n > 0.

Conventions:
* The sequence has offset 0 (data 1, 2, 5, 13, 19, 37, 73, 97, 193, 241, ...).
* a(0) = 1 and a(n+1) is the least natural number k with a(n) < k and
  3^(k-1) == 1 (mod a(n)*k); the congruence is `Nat.ModEq`, and the least element is
  `sInf` on natural numbers. If no such k existed, `sInf` of the empty set would be 0, which
  is not prime, so the statement also contains the (expected) existence of every term.
* The rest of the comment (namely, a(n) is the smallest prime p > a(n-1) different from 3
  such that 3^(p-1) == 1 (mod a(n-1))) is the description that follows from primality and is
  not a separate part of the statement.
-/

namespace OMA.S_oeis_a307244

/-- A307244: a(0) = 1; a(n+1) is the smallest k > a(n) with
3^(k-1) == 1 (mod a(n)*k). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | (n + 1) => sInf {k : ℕ | a n < k ∧ 3 ^ (k - 1) ≡ 1 [MOD a n * k]}

/-- The conjecture: a(n) is prime for every n > 0. -/
theorem main : ∀ n : ℕ, 0 < n → (a n).Prime := by
  sorry

end OMA.S_oeis_a307244
