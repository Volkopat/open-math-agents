import Mathlib

/-!
# A234308: a(n) = |{0 < k <= n/2: phi(k^2)*phi(n-k) - 1 is a Sophie Germain prime}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A234308
Credit: @luciusacarr

Data: 0, 0, 0, 0, 1, 3, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2, 1, 2, 1, 1, ... (offset 1).

The entry's comment (Zhi-Wei Sun) states a four-part conjecture. `main` states all four parts,
as a conjunction, in the order the source gives them.

Conjecture: (i) a(n) > 0 for all n > 4.
(ii) If n > 3, then phi(k^2)*phi(n-k) - 1 and phi(k^2)*phi(n-k) + 1 are both prime for some
0 < k < n, and also phi(j)^2*phi(n-j) - 1 and phi(j)^2*phi(n-j) + 1 are both prime for some
0 < j < n.
(iii) If n > 9 is not equal to 14, then |phi(k) - phi(n-k)|/2 is prime for some 0 < k < n, and
also |phi(j) - phi(n-j)| - 1 and |phi(j) - phi(n-j)| + 1 are both prime for some 0 < j < n.
(iv) If n > 5, then sigma(k)*phi(n-k) + 1 is a square for some 0 < k < n, where sigma(k) is the
sum of all positive divisors of k.

Reading of the source:
* `phi` is `Nat.totient` and `sigma` is `ArithmeticFunction.sigma 1`. A Sophie Germain prime is
  a prime `p` with `2p + 1` also prime.
* `0 < k ≤ n/2` is written `0 < k ∧ 2k ≤ n`. The first 30 data values were recomputed from this
  definition.
* `|phi(k) - phi(n-k)|` is the distance `Nat.dist`; "|phi(k) - phi(n-k)|/2 is prime" means that
  this distance is twice a prime.
* "A square" means the square of a natural number.
* All four parts were checked numerically for n < 200 or n < 300.
-/

namespace OMA.S_oeis_a234308

/-- `p` is a Sophie Germain prime: `p` and `2p + 1` are prime. -/
def IsSophieGermain (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

theorem main :
    -- (i) a(n) > 0 for all n > 4.
    (∀ n : ℕ, 4 < n → ∃ k : ℕ, 0 < k ∧ 2 * k ≤ n ∧
      IsSophieGermain (Nat.totient (k ^ 2) * Nat.totient (n - k) - 1)) ∧
    -- (ii) n > 3: twin primes around phi(k^2) phi(n-k) and around phi(j)^2 phi(n-j).
    (∀ n : ℕ, 3 < n →
      (∃ k : ℕ, 0 < k ∧ k < n ∧ (Nat.totient (k ^ 2) * Nat.totient (n - k) - 1).Prime ∧
        (Nat.totient (k ^ 2) * Nat.totient (n - k) + 1).Prime) ∧
      (∃ j : ℕ, 0 < j ∧ j < n ∧ (Nat.totient j ^ 2 * Nat.totient (n - j) - 1).Prime ∧
        (Nat.totient j ^ 2 * Nat.totient (n - j) + 1).Prime)) ∧
    -- (iii) n > 9, n ≠ 14.
    (∀ n : ℕ, 9 < n → n ≠ 14 →
      (∃ k q : ℕ, 0 < k ∧ k < n ∧ q.Prime ∧
        Nat.dist (Nat.totient k) (Nat.totient (n - k)) = 2 * q) ∧
      (∃ j : ℕ, 0 < j ∧ j < n ∧
        (Nat.dist (Nat.totient j) (Nat.totient (n - j)) - 1).Prime ∧
        (Nat.dist (Nat.totient j) (Nat.totient (n - j)) + 1).Prime)) ∧
    -- (iv) n > 5: sigma(k) phi(n-k) + 1 is a square for some 0 < k < n.
    (∀ n : ℕ, 5 < n → ∃ k x : ℕ, 0 < k ∧ k < n ∧
      ArithmeticFunction.sigma 1 k * Nat.totient (n - k) + 1 = x ^ 2) := by
  sorry

end OMA.S_oeis_a234308
