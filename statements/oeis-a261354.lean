import Mathlib

/-!
# A261354: Primes p such that prime(p)^2 - 2 = prime(q) for some prime q.

Source: https://oeis.org/A261354
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261354): The sequence has infinitely many terms. In general, for
any integers `a, b, c` with `a > 0` and `gcd(a, b, c) = 1`, if `b^2 - 4ac` is not a square,
`a + b + c` is odd, and `gcd(b, a + c)` is not divisible by 3, then there are infinitely many prime
pairs `{p, q}` such that `a prime(p)^2 + b prime(p) + c = prime(q)`.

Formalization notes:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`; since
  `prime(p)^2 ≥ 4`, `prime(p) ^ 2 - 2` in `ℕ` is exact. The general statement is taken in `ℤ`.
* "Infinitely many prime pairs `{p, q}`" is stated as: the set of pairs `(p, q)` of primes satisfying
  the equation is infinite.
* With this definition the first term is 31, matching the data of A261354.
-/

namespace OMA.S_oeis_a261354

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- Sun's conjectures of A261354. -/
theorem main :
    {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ prime p ^ 2 - 2 = prime q}.Infinite ∧
      ∀ a b c : ℤ, 0 < a → Int.gcd (Int.gcd a b) c = 1 → ¬ IsSquare (b ^ 2 - 4 * a * c) →
        Odd (a + b + c) → ¬ (3 : ℤ) ∣ (Int.gcd b (a + c) : ℤ) →
          {pq : ℕ × ℕ | pq.1.Prime ∧ pq.2.Prime ∧
            a * (prime pq.1 : ℤ) ^ 2 + b * prime pq.1 + c = prime pq.2}.Infinite := by
  sorry

end OMA.S_oeis_a261354
