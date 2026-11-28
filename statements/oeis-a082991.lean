import Mathlib

/-!
# A082991: a(1) = 1 and for n > 1, a(n) = 2 * length of the cycle reached for the map
x -> A062401(x), starting at n [where A062401(n) = phi(sigma(n))], or -1 if no finite cycle is
ever reached.

Source: https://oeis.org/A082991
Credit: @gblacher2

The comment section of A082991 contains two conjectures:
1. "From the original definition: Define a sequence un as follows: un(1) = n, thereafter
   un(2k) = sigma(un(2k-1)), un(2k+1) = phi(un(2k)); then a(n) is the length of the ultimate
   period of u_n(k) (which is conjectured to become ultimately periodic for any n>=1)."
2. "Conjecture: despite results for small terms, all even number are obtained as values.
   (For example, 12 occurs since a(12102) = 12)."

Modelling choices:
* `u n k` is the source's `u_n(k + 1)` (index shifted by one so that it starts at `0`):
  `u n 0 = n`, the step from an even index `k` applies `sigma` (the sum of divisors,
  `ArithmeticFunction.sigma 1`) and the step from an odd index applies Euler's `phi`
  (`Nat.totient`). So `u n (2k - 1) = un(2k)` and `u n (2k) = un(2k+1)`.
* "Ultimately periodic with period `p`" means `0 < p` and `u n (k + p) = u n k` for all large `k`.
  The index shift does not change this property or its least period.
* a(n), "the length of the ultimate period", is the least such `p`. With this definition the
  first 105 values agree with the OEIS data (1, 2, 2, 4, 2, 4, ...), including a(1) = 1.
* "All even numbers are obtained as values" is read as: every even `m > 0` equals a(n) for some
  `n ≥ 1` (a(n) is never `0`, and the value `-1` of the name is not even).
* The two conjectures are stated together, as a conjunction.
-/

namespace OMA.S_oeis_a082991

/-- `u n k` is `u_n(k + 1)`: start at `n`, then alternately apply `sigma` and `phi`. -/
def u (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => if k % 2 = 0 then ArithmeticFunction.sigma 1 (u n k) else Nat.totient (u n k)

/-- `p` is an ultimate period of `u_n`: `0 < p` and `u_n(k + p) = u_n(k)` for all large `k`. -/
def IsUltimatePeriod (n p : ℕ) : Prop :=
  0 < p ∧ ∃ N : ℕ, ∀ k ≥ N, u n (k + p) = u n k

/-- Both conjectures of A082991: `u_n` is ultimately periodic for every `n ≥ 1`, and every even
`m > 0` is the least ultimate period a(n) of some `u_n` with `n ≥ 1`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, IsUltimatePeriod n p) ∧
    (∀ m : ℕ, 0 < m → Even m → ∃ n : ℕ, 1 ≤ n ∧ IsLeast {p : ℕ | IsUltimatePeriod n p} m) := by
  sorry

end OMA.S_oeis_a082991
