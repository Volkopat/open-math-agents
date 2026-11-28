import Mathlib

/-!
# A278720: The p-defect p - N(p) of the congruence y^2 == x^3 + 4*x (mod p) for primes p, where N(p) is the number of solutions given by A276730.

Source: https://oeis.org/A278720
Credit: @agchua

Comment and formula of A278720 (the entry is by Wolfdieter Lang, Dec 11 2016):
  a(n) = 0 if prime(n) == 2 or 3 (mod 4). (see the conjecture by Robert Israel, Sep 28 2016 in A276730).
  a(n) = 0 if prime(n) == 2 or 3 (mod 4) (this is conjecture II from above).
Offset 1: a(n) = p - N(p) with p = prime(n), the n-th prime (prime(1) = 2), and N(p) = A276730(n)
the number of pairs (x, y) of residues modulo p with y^2 == x^3 + 4*x (mod p). The claim is stated
for every n >= 1 with prime(n) == 2 or 3 (mod 4); the case 2 (mod 4) is only prime(1) = 2.
-/

namespace OMA.S_oeis_a278720

/-- N(p) = A276730: the number of solutions (x, y) modulo p of y^2 == x^3 + 4*x (mod p). -/
noncomputable def N (p : ℕ) : ℕ := Nat.card {q : ZMod p × ZMod p // q.2 ^ 2 = q.1 ^ 3 + 4 * q.1}

/-- a(n) = p - N(p) where p = prime(n) is the n-th prime (offset 1). -/
noncomputable def a (n : ℕ) : ℤ := (Nat.nth Nat.Prime (n - 1) : ℤ) - (N (Nat.nth Nat.Prime (n - 1)) : ℤ)

/-- The claim: a(n) = 0 whenever prime(n) == 2 or 3 (mod 4). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (Nat.nth Nat.Prime (n - 1) % 4 = 2 ∨ Nat.nth Nat.Prime (n - 1) % 4 = 3) → a n = 0 := by
  sorry

end OMA.S_oeis_a278720
