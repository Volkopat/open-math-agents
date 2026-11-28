import Mathlib

/-!
# A179089: a(n) = (1/n^2) * Sum_{k=0..n-1} (2k+1)*T_k^2*(-3)^(n-1-k)

Source: https://oeis.org/A179089

T_k is the central trinomial coefficient (A002426), T_k = Sum_j C(k,2j) C(2j,j). Offset 1.
Conjecture (Zhi-Wei Sun, Jun 28 2010): a(p) = (1 + (p/3))/2 (mod p) for every prime p,
where (p/3) is the Legendre symbol. Sun also conjectured that a(n) is an integer; that part
follows from Mark van Hoeij's closed formula (Nov 2022) and is not the target here, though
integrality at primes is needed to state the congruence and is included.

Formalized: a(n) is defined in ℚ by the literal sum divided by n^2. For every prime p we
assert that a(p) is an integer m with 2*m = 1 + (p/3) (mod p), and, for p ≠ 3 (where
(1 + (p/3))/2 is an integer, 0 or 1), m = (1 + (p/3))/2 (mod p). For p = 3 the residue
(1+0)/2 means the inverse of 2 mod 3, which is exactly the first clause. The Legendre
symbol (p/3) is written as jacobiSym p 3.
-/

namespace OMA.S_oeis_a179089

/-- Central trinomial coefficient T_k (A002426). -/
def T (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k / 2 + 1), (Nat.choose k (2 * j) * Nat.choose (2 * j) j : ℤ)

/-- a(n) = (1/n^2) Sum_{k=0..n-1} (2k+1) T_k^2 (-3)^(n-1-k), as a rational number. -/
def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((2 * k + 1 : ℤ) * T k ^ 2 * (-3 : ℤ) ^ (n - 1 - k) : ℚ)) / (n : ℚ) ^ 2

theorem main : ∀ p : ℕ, p.Prime → ∃ m : ℤ, (m : ℚ) = a p ∧
    2 * m ≡ 1 + jacobiSym (p : ℤ) 3 [ZMOD (p : ℤ)] ∧
    (p ≠ 3 → m ≡ (1 + jacobiSym (p : ℤ) 3) / 2 [ZMOD (p : ℤ)]) := by
  sorry

end OMA.S_oeis_a179089
