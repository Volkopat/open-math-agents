import Mathlib

/-!
# A001658: Fibonomial coefficients [n choose 6]_F

Source: https://oeis.org/A001658
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
Let `F(n) = Nat.fib n` be the Fibonacci sequence and `a(n) = [n choose 6]_F` be the
Fibonomial coefficient `(∏_{r=0}^5 F(n - r)) / (∏_{r=1}^6 F(r))` for `n ≥ 6`.
Then for all `n ≥ 6`, `a(n)` equals:
`F(7)^(n-6) + ∑_{i=3}^{n-5} (F(i-2)*F(6)^(i-1)*F(7)^(n-i-5)
  + ∑_{j=3}^i (F(i-2)*F(j-2)*F(5)^(j-1)*F(6)^(i-j)*F(7)^(n-i-5)
  + ∑_{k=3}^j (F(i-2)*F(j-2)*F(k-2)*F(4)^(k-1)*F(5)^(j-k)*F(6)^(i-j)*F(7)^(n-i-5)
  + ∑_{l=3}^k (F(i-2)*F(j-2)*F(k-2)*F(l-2)*F(3)^(l-1)*F(4)^(k-l)*F(5)^(j-k)*F(6)^(i-j)*F(7)^(n-i-5)
  + ∑_{m=3}^l F(i-2)*F(j-2)*F(k-2)*F(l-2)*F(m-2)*F(m)*F(3)^(l-m)*F(4)^(k-l)*F(5)^(j-k)*F(6)^(i-j)*F(7)^(n-i-5)))))`.
-/

namespace OMA.S_oeis_a001658

/-- Fibonomial coefficient `[n choose 6]_F` (A001658). -/
def a (n : ℕ) : ℕ :=
  (∏ r ∈ Finset.range 6, Nat.fib (n - r)) / (∏ r ∈ Finset.Icc 1 6, Nat.fib r)

/-- Nested sum identity for the Fibonomial coefficients `[n choose 6]_F`. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n →
      a n =
        Nat.fib 7 ^ (n - 6) +
        ∑ i ∈ Finset.Icc 3 (n - 5),
          (Nat.fib (i - 2) * Nat.fib 6 ^ (i - 1) * Nat.fib 7 ^ (n - i - 5) +
          ∑ j ∈ Finset.Icc 3 i,
            (Nat.fib (i - 2) * Nat.fib (j - 2) * Nat.fib 5 ^ (j - 1) *
              Nat.fib 6 ^ (i - j) * Nat.fib 7 ^ (n - i - 5) +
            ∑ k ∈ Finset.Icc 3 j,
              (Nat.fib (i - 2) * Nat.fib (j - 2) * Nat.fib (k - 2) * Nat.fib 4 ^ (k - 1) *
                Nat.fib 5 ^ (j - k) * Nat.fib 6 ^ (i - j) * Nat.fib 7 ^ (n - i - 5) +
              ∑ l ∈ Finset.Icc 3 k,
                (Nat.fib (i - 2) * Nat.fib (j - 2) * Nat.fib (k - 2) * Nat.fib (l - 2) *
                  Nat.fib 3 ^ (l - 1) * Nat.fib 4 ^ (k - l) * Nat.fib 5 ^ (j - k) *
                  Nat.fib 6 ^ (i - j) * Nat.fib 7 ^ (n - i - 5) +
                ∑ m ∈ Finset.Icc 3 l,
                  Nat.fib (i - 2) * Nat.fib (j - 2) * Nat.fib (k - 2) * Nat.fib (l - 2) *
                    Nat.fib (m - 2) * Nat.fib m * Nat.fib 3 ^ (l - m) * Nat.fib 4 ^ (k - l) *
                    Nat.fib 5 ^ (j - k) * Nat.fib 6 ^ (i - j) * Nat.fib 7 ^ (n - i - 5))))) := by
  sorry

end OMA.S_oeis_a001658
