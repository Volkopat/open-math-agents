import Mathlib

/-!
# A106297: Period of the Lucas 5-step sequence A074048 mod n.

Source: https://oeis.org/A106297
Credit: @prasledi

Conjectures (Chai Wah Wu, Feb 25 2022, in the FORMULA section of A106297):
a(5^k) = 781*5^(k-1) for k > 0. a(2^k) = 3*2^(k-1) for k > 1. If a(p) != a(p^2) for prime
p > 2, then a(p^k) = p^(k-1)*a(p) for k > 0.

Formalization notes:
* A074048 (Lucas 5-step numbers): s(0) = 5, s(1) = 1, s(2) = 3, s(3) = 7, s(4) = 15,
  s(n) = s(n-1) + s(n-2) + s(n-3) + s(n-4) + s(n-5).
* a(n) (offset 1) is the period of s modulo n: the least P > 0 such that
  s(m + P) ≡ s(m) (mod n) for every m >= 0. Such a P exists for every n >= 1 (the recurrence is
  invertible, so s is purely periodic modulo n); `sInf` of the set of such P is that least one.
  For example a(1) = a(2) = 1, a(3) = 104, a(4) = 6, a(5) = 781.
* The three conjectures are stated as one conjunction, with k and p as in the source.
-/

namespace OMA.S_oeis_a106297

/-- The Lucas 5-step numbers A074048. -/
def s : ℕ → ℕ
  | 0 => 5
  | 1 => 1
  | 2 => 3
  | 3 => 7
  | 4 => 15
  | (n + 5) => s n + s (n + 1) + s (n + 2) + s (n + 3) + s (n + 4)

/-- `a n`: the period of the Lucas 5-step numbers modulo `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {P : ℕ | 0 < P ∧ ∀ m : ℕ, s (m + P) ≡ s m [MOD n]}

/-- The three conjectures of A106297. -/
theorem main :
    (∀ k : ℕ, 0 < k → a (5 ^ k) = 781 * 5 ^ (k - 1)) ∧
    (∀ k : ℕ, 1 < k → a (2 ^ k) = 3 * 2 ^ (k - 1)) ∧
    (∀ p : ℕ, p.Prime → 2 < p → a p ≠ a (p ^ 2) →
      ∀ k : ℕ, 0 < k → a (p ^ k) = p ^ (k - 1) * a p) := by
  sorry

end OMA.S_oeis_a106297
