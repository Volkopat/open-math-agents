import Mathlib

/-!
# A106303: Period of the Fibonacci 5-step sequence A001591 mod n.

Source: https://oeis.org/A106303
Credit: @prasledi

Conjectures (Chai Wah Wu, Feb 25 2022, in the FORMULA section of A106303):
a(5^k) = 781*5^(k-1) for k > 0. If a(p) != a(p^2) for p prime, then a(p^k) = p^(k-1)*a(p)
for k > 0.

Formalization notes:
* A001591 (pentanacci numbers): f(0) = f(1) = f(2) = f(3) = 0, f(4) = 1,
  f(n) = f(n-1) + f(n-2) + f(n-3) + f(n-4) + f(n-5).
* a(n) (offset 1) is the period of f modulo n: the least P > 0 such that
  f(m + P) ≡ f(m) (mod n) for every m >= 0. Such a P exists for every n >= 1 (the recurrence is
  invertible, so f is purely periodic modulo n); `sInf` of the set of such P is that least one.
  For example a(1) = 1, a(2) = 6, a(5) = 781.
* Both conjectures are stated as one conjunction, with k ranging over the natural numbers k > 0
  and p over all primes (including p = 2, as in the source, which does not exclude it).
-/

namespace OMA.S_oeis_a106303

/-- The pentanacci numbers A001591. -/
def f : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | (n + 5) => f n + f (n + 1) + f (n + 2) + f (n + 3) + f (n + 4)

/-- `a n`: the period of the pentanacci numbers modulo `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {P : ℕ | 0 < P ∧ ∀ m : ℕ, f (m + P) ≡ f m [MOD n]}

/-- The two conjectures of A106303. -/
theorem main :
    (∀ k : ℕ, 0 < k → a (5 ^ k) = 781 * 5 ^ (k - 1)) ∧
    (∀ p : ℕ, p.Prime → a p ≠ a (p ^ 2) → ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p) := by
  sorry

end OMA.S_oeis_a106303
