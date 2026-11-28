import Mathlib

/-!
# A223934: Least prime p such that x^n-x-1 is irreducible modulo p.

Source: https://oeis.org/A223934
Credit: @azmiozgen

Conjectures (from the entry):
1. a(n) < n*(n+3)/2 for all n > 1.
2. For every n = 2, 3, ... there is a positive integer z not exceeding the (2n-2)-th prime such
   that z^n - z - 1 is prime. (The entry adds that the Galois group of x^n - x - 1 over the
   rationals is the symmetric group S_n; that part is not stated here.)

Formalization notes:
* a(n), offset 2, is the least prime p such that X^n - X - 1 is irreducible in (ZMod p)[X].
* Conjecture 1 is stated without division as 2 a(n) < n(n+3).
* The k-th prime is `Nat.nth Nat.Prime (k - 1)` (prime(1) = 2). z^n - z - 1 is computed in ℕ; for
  z = 1 it is 0 (not prime), as -1 is not prime either, so the truncation does not matter.
* Controls (computed): a(2..21) = 2, 2, 2, 3, 2, 2, 7, 2, 17, 7, 5, 3, 3, 2, 109, 3, 101, 19, 229,
  5, as in the entry; conjecture 1 holds for 2 ≤ n < 40 and conjecture 2 for 2 ≤ n < 30.
-/

namespace OMA.S_oeis_a223934

open Polynomial

/-- A223934(n): the least prime `p` with `X^n - X - 1` irreducible over `ZMod p`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ Irreducible (X ^ n - X - 1 : (ZMod p)[X])}

/-- Both conjectures of the entry (the Galois-group part excepted). -/
theorem main :
    (∀ n : ℕ, 1 < n → 2 * a n < n * (n + 3)) ∧
      ∀ n : ℕ, 2 ≤ n →
        ∃ z : ℕ, 0 < z ∧ z ≤ Nat.nth Nat.Prime (2 * n - 3) ∧ (z ^ n - z - 1).Prime := by
  sorry

end OMA.S_oeis_a223934
