import Mathlib

/-!
# A193665: Q-residue of A075392, where Q=A075392.  (See Comments.)

Source: https://oeis.org/A193665
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A193665 (R. J. Mathar, Feb 19 2015):
a(n) +(-n-4)*a(n-1) +(n+1)*a(n-2) -a(n-3)=0.

Conventions:
* The sequence has offset 0 (data 1, 6, 33, 208, 1505, 12330, 112973, ...).
* The Q-residue is computed by the formulation given in the COMMENTS of A193649 (to which the
  entry refers for the definition) and used verbatim by the Mathematica program of the entry:
  write q(n,k) for the entries of Q, define r(0) = 1 and
  r(k) = Sum_{i=0..k-1} q(k-1,i)*r(k-1-i), and then a(n) = v(n) = Sum_{k=0..n} p(n,k)*r(n-k),
  where p(n,k) is the entry in row n and column k of the triangle P.
* Here P = Q is the triangle of the Mathematica program of the entry,
  q(n,k) = p(n,k) = (k+1)*(n+1) for 0 <= k <= n (rows 1; 2, 4; 3, 6, 9; ..., which the program
  labels A075362; the A-number printed in the name differs from it in one digit). This triangle
  reproduces the data.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which all the indices n-1, n-2, n-3 are at least the offset 0.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`.
-/

namespace OMA.S_oeis_a193665

/-- r(0) = 1 and r(k) = Sum_{i=0..k-1} q(k-1,i)*r(k-1-i) with q(n,i) = (i+1)*(n+1). -/
def r : ℕ → ℤ
  | 0 => 1
  | k + 1 => ∑ i : Fin (k + 1), ((((i : ℕ) : ℤ) + 1) * ((k : ℤ) + 1)) * r (k - (i : ℕ))

/-- A193665 (offset 0): a(n) = Sum_{k=0..n} p(n,k)*r(n-k) with p(n,k) = (k+1)*(n+1). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (((k : ℤ) + 1) * ((n : ℤ) + 1)) * r (n - k)

/-- For every `n ≥ 3`, a(n) + (-n-4)*a(n-1) + (n+1)*a(n-2) - a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + (-(n : ℤ) - 4) * a (n - 1) + ((n : ℤ) + 1) * a (n - 2) - a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a193665
