import Mathlib

/-!
# A382074: a(n) is the number of solutions to phi(x) + phi(n-x) = phi(n) where 1 <= x <= floor(n/2).

Source: https://oeis.org/A382074 (and https://oeis.org/A065381)
Credit: @agchua

Comment of A382074 (entry by Felix Huber, Mar 22 2025), stated here literally, all of it:
  a(2*i) = 0 is not true for every positive odd i. For example, a(2*3) = 1. It is conjectured
  that a(2*A065381(n)) = 0 for n > 1. However, there are positive odd numbers i not in A065381
  and for which a(2*i) = 0. For example, a(2*529) = a(2*1155) = 0.
The same conjecture is the formula line: Conjecture: a(2*A065381(n)) = 0 for n > 1.
A382074 has offset 1; phi is Euler's totient function, Nat.totient. A065381 (offset 1) is the
sequence of primes not of the form p + 2^k, p prime and k >= 0 (its name line): 2, 127, 149, ...
Computed (not part of the statement): the listed terms agree with this definition; a(6) = 0
(phi(1) + phi(5) = 5, phi(2) + phi(4) = 3, phi(3) + phi(3) = 4, phi(6) = 2), so the printed
example a(2*3) = 1 does not hold, and the first odd i with a(2*i) > 0 is i = 5 (a(10) = 1);
the conjecture also fails at the term 3697 of A065381, since a(7394) = 1 (x = 959).
-/

namespace OMA.S_oeis_a382074

/-- A382074(n): the number of x with 1 ≤ x ≤ n/2 and phi(x) + phi(n-x) = phi(n). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter
    (fun x => Nat.totient x + Nat.totient (n - x) = Nat.totient n)).card

/-- Membership in A065381: p is a prime that is not of the form q + 2^k, q prime, k ≥ 0. -/
def IsA065381 (p : ℕ) : Prop := p.Prime ∧ ∀ q k : ℕ, q.Prime → p ≠ q + 2 ^ k

/-- A065381(n), offset 1: the n-th prime not of the form q + 2^k (q prime, k ≥ 0). -/
noncomputable def A065381 (n : ℕ) : ℕ := Nat.nth IsA065381 (n - 1)

/-- The comment as printed: a(2i) = 0 fails for some positive odd i; a(2*3) = 1;
the conjecture a(2*A065381(n)) = 0 for n > 1; some positive odd i not in A065381 has
a(2i) = 0; and a(2*529) = a(2*1155) = 0. -/
theorem main :
    (¬ ∀ i : ℕ, 0 < i → Odd i → a (2 * i) = 0) ∧
    a (2 * 3) = 1 ∧
    (∀ n : ℕ, 1 < n → a (2 * A065381 n) = 0) ∧
    (∃ i : ℕ, 0 < i ∧ Odd i ∧ (∀ n : ℕ, 1 ≤ n → A065381 n ≠ i) ∧ a (2 * i) = 0) ∧
    a (2 * 529) = 0 ∧ a (2 * 1155) = 0 := by
  sorry

end OMA.S_oeis_a382074
