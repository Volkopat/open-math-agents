import Mathlib

/-!
# A361892: a(n) = S(7,2*n-1)/S(1,2*n-1), where S(r,n) = Sum_{k = 0..floor(n/2)} ( binomial(n,k) - binomial(n,k-1) )^r.

Source: https://oeis.org/A361892
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): the supercongruence a(n*p^r) == a(n*p^(r-1))
(mod p^(3*r)) holds for positive integers n and r and all primes p >= 5.

Formalization notes:
* binomial(n, -1) = 0, so the k = 0 term of S(r, n) is binomial(n, 0)^r = 1. S is computed in ℤ and
  a(n) = S(7, 2n-1)/S(1, 2n-1) in ℚ (offset 1); its values are integers.
* "x == y (mod p^(3r))" is stated as: x - y = p^(3r) * z for an integer z.
* Controls (computed): a(1..6) = 1, 43, 9451, 6031627, 6571985126, 9140730357409, as in the entry;
  the congruence holds for p = 5, 7 and n = 1, 2 with r = 1.
-/

namespace OMA.S_oeis_a361892

/-- `S(r, n) = ∑_{k=0}^{⌊n/2⌋} (C(n,k) - C(n,k-1))^r`, with `C(n,-1) = 0`. -/
def S (r n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    ((n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))) ^ r

/-- A361892(n) = S(7, 2n-1) / S(1, 2n-1). -/
noncomputable def a (n : ℕ) : ℚ := (S 7 (2 * n - 1) : ℚ) / S 1 (2 * n - 1)

/-- The supercongruences `a(n p^r) ≡ a(n p^(r-1)) (mod p^(3r))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n r : ℕ, 1 ≤ n → 1 ≤ r →
      ∃ z : ℤ, a (n * p ^ r) - a (n * p ^ (r - 1)) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a361892
