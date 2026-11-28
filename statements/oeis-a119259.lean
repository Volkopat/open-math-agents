import Mathlib

/-!
# A119259: Central terms of the triangle in A119258.

Source: https://oeis.org/A119259

A119258 is the triangle read by rows with T(n,0) = T(n,n) = 1 and, for 0 < k < n,
T(n,k) = 2*T(n-1,k-1) + T(n-1,k). A119259 is a(n) = T(2n,n), offset 0
(1, 3, 17, 111, 769, 5503, ...).

Claims (Peter Bala, Mar 23 2020, formula section):
(1) a(p) == 3 (mod p^3) for prime p >= 5;
(2) more generally, conjectured: a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) for prime p >= 5
    and positive integers n and k.
The entry also records the Gauss congruences mod p^k as known; they are not part of the target.

Formalized: `T` follows the recurrence of A119258 literally, with values in ℤ; for k > n the
value of `T n k` is an irrelevant junk value (never used for k <= n). Congruences are stated
with `Int.ModEq`. Both claims are stated as a conjunction in the order of the entry.
-/

namespace OMA.S_oeis_a119259

/-- The triangle A119258: T(n,0) = T(n,n) = 1, T(n,k) = 2 T(n-1,k-1) + T(n-1,k) for 0 < k < n. -/
def T : ℕ → ℕ → ℤ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => if k + 1 = n + 1 then 1 else 2 * T n k + T n (k + 1)

/-- A119259: a(n) = T(2n, n). -/
def a (n : ℕ) : ℤ := T (2 * n) n

theorem main :
    (∀ p : ℕ, p.Prime → 5 ≤ p → a p ≡ 3 [ZMOD (p : ℤ) ^ 3]) ∧
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      a (n * p ^ k) ≡ a (n * p ^ (k - 1)) [ZMOD (p : ℤ) ^ (3 * k)]) := by
  sorry

end OMA.S_oeis_a119259
