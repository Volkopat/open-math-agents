import Mathlib

/-!
# A140358: Smallest nonnegative integer k such that n = +-1+-2+...+-k for some choice of +'s and -'s.

Source: https://oeis.org/A140358
Credit: @agchua

Formula line of A140358 (the entry is by John W. Layman, Jun 23 2008):
  Conjecture when n is greater than 0. Choose k so that t(k)<=n<t(k+1) where t(n) is the n-th
  triangular number t(n)=n(n+1)/2. If n=t(k), a(n)=k, otherwise if k is odd then a(n)=k+2 if
  n-t(k) is odd, a(n)=k+1 if n-t(k) is even, else if k is even than a(n)=k+1 if n-t(k) is odd,
  a(n)=k+3 if n-t(k) is even. (This has been verified for n up to 100.)
The claim is stated for n > 0, as in the conjecture, and for the k with t(k) <= n < t(k+1).
A choice of signs is a function e with values 1 and -1; the empty sum (k = 0) is 0. a(n) is the
least k for which such a representation exists (sInf of a set of naturals).
-/

namespace OMA.S_oeis_a140358

/-- n = +-1+-2+...+-k: n = Sum_{i<k} e(i)*(i+1) for some signs e(i) in {1, -1}. -/
def IsSignedSum (n : ℤ) (k : ℕ) : Prop :=
  ∃ e : ℕ → ℤ, (∀ i, e i = 1 ∨ e i = -1) ∧ ∑ i ∈ Finset.range k, e i * ((i : ℤ) + 1) = n

/-- A140358(n): the smallest k >= 0 such that n = +-1+-2+...+-k. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | IsSignedSum n k}

/-- The triangular number t(n) = n(n+1)/2. -/
def t (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Layman's conjecture: for n > 0 and t(k) <= n < t(k+1), a(n) is k if n = t(k), and otherwise
k+2 or k+1 (k odd, n-t(k) odd or even), k+1 or k+3 (k even, n-t(k) odd or even). -/
theorem main : ∀ n k : ℕ, 0 < n → t k ≤ n → n < t (k + 1) →
    a n = if n = t k then k
      else if k % 2 = 1 then (if (n - t k) % 2 = 1 then k + 2 else k + 1)
      else (if (n - t k) % 2 = 1 then k + 1 else k + 3) := by
  sorry

end OMA.S_oeis_a140358
