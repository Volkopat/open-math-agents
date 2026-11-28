import Mathlib

/-!
# A096164: Triangle T(n,m) read by rows: matrix product A053121 * A038207.

Source: https://oeis.org/A096164
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A096164 (R. J. Mathar, Mar 25 2010):
Sum_{m=0..n} T(n,m) = A126931(n).

Conventions:
* The triangle is indexed as in the formula and the Maple program of the entry:
  T(n,m) = Sum_{k=0..n} A053121(n,k)*A038207(k,m) for 0 <= m <= n, n >= 0
  (rows 1; 2, 1; 5, 4, 1; 12, 14, 6, 1; ...).
* A053121 (Catalan triangle with 0's) is given by the closed formula of its entry, which is also
  the one used in the Maple program of A096164: A053121(n,k) = 0 if n < k or n-k is odd, and
  (k+1)*binomial(n+1,(n-k)/2)/(n+1) otherwise. It is `c n k` below; the division by n+1 is formed
  in `ℚ` (it is exact).
* A038207(i,j) = binomial(i,j)*2^(i-j), and 0 if j > i (Maple program of the entry); for j > i
  the natural number binomial coefficient `Nat.choose i j` is already 0. It is `p i j` below.
* A126931(n) = A127359(n+1)/2 - A127359(n) (this is the name of A126931), where
  A127359(n) = Sum_{k=0..n} binomial(n, floor(k/2))*3^(n-k) (the name of A127359), `s n` below.
  The halving is done in `ℚ`.
* Both sides are rational numbers, so the equality is stated in `ℚ`, for every n >= 0, which is
  the full range of row indices.
-/

namespace OMA.S_oeis_a096164

/-- A053121(n,k): 0 if n < k or n-k odd, else (k+1)*binomial(n+1,(n-k)/2)/(n+1). -/
def c (n k : ℕ) : ℚ :=
  if n < k ∨ (n - k) % 2 = 1 then 0
  else ((k : ℚ) + 1) * ((n + 1).choose ((n - k) / 2) : ℚ) / ((n : ℚ) + 1)

/-- A038207(i,j) = binomial(i,j)*2^(i-j) (which is 0 for j > i). -/
def p (i j : ℕ) : ℚ := (i.choose j : ℚ) * 2 ^ (i - j)

/-- A096164: T(n,m) = Sum_{k=0..n} A053121(n,k)*A038207(k,m). -/
def T (n m : ℕ) : ℚ := ∑ k ∈ Finset.range (n + 1), c n k * p k m

/-- A127359(n) = Sum_{k=0..n} binomial(n, floor(k/2))*3^(n-k). -/
def s (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose (k / 2) * 3 ^ (n - k)

/-- A126931(n) = A127359(n+1)/2 - A127359(n). -/
def A126931 (n : ℕ) : ℚ := (s (n + 1) : ℚ) / 2 - (s n : ℚ)

/-- For every `n ≥ 0`, Sum_{m=0..n} T(n,m) = A126931(n). -/
theorem main : ∀ n : ℕ, ∑ m ∈ Finset.range (n + 1), T n m = A126931 n := by
  sorry

end OMA.S_oeis_a096164
