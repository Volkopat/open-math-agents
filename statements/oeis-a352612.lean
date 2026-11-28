import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a352612

/-- OEIS A352612:
`a(n) = (n - 1) * ∏_{p prime, 2 ≤ p ≤ n-2, gcd(p,n)=1} (-p^2) * ∏_{2 ≤ k ≤ n-2, k & n-k composite, gcd(k,n)=1} k`.
(Reduced modulo `n` in OEIS.) -/
def a (n : ℕ) : ℤ :=
  ((n : ℤ) - 1) *
    (∏ p ∈ (Finset.Icc 2 (n - 2)).filter (fun p => p.Prime ∧ Nat.Coprime p n), (-(p : ℤ) ^ 2)) *
    (∏ k ∈ (Finset.Icc 2 (n - 2)).filter (fun k => ¬ k.Prime ∧ ¬ (n - k).Prime ∧ Nat.Coprime k n), (k : ℤ))

/-- OEIS A352612 Conjecture: for odd `n > 1`, if `a(n) ≡ -1 (mod n)` then `n` must be a prime power. -/
theorem main :
    ∀ n : ℕ, 1 < n → Odd n → a n ≡ -1 [ZMOD (n : ℤ)] → IsPrimePow n := by
  sorry

end OMA.S_oeis_a352612
