import Mathlib

/-!
# A005313: Plouffe's generating function

Source: https://oeis.org/A005313
Credit: @ivillar

Status: known result. The entry records the g.f. as conjectured by Simon Plouffe in his 1992
dissertation, with the note: this is in fact the correct g.f. (N. J. A. Sloane, Jan 28 2022).
Here it is derived from the formula a(n) = A064831(n-1) + n recorded in the entry, which is used as
the definition.

A005313 (offset 1): maximal sum of inverse squares of the singular values of triangular
anti-Hadamard matrices of order n;
data 1, 3, 6, 13, 29, 70, 175, 449, 1164, 3035, 7931, 20748, 54301, 142143, 372114, ...

G.f. (conjectured by Simon Plouffe): [x(1-x-3x^2+x^3)]/[(1-3x+x^2)(1+x)(1-x)^2].

Formalization: the entry records a(n) = A064831(n-1) + n, where A064831(m) is the m-th partial sum
of A001654(k) = F(k)*F(k+1), k = 0..m (F the Fibonacci numbers). So
a(n) = n + Sum_{k=0..n-1} F(k)*F(k+1), which is the definition used here; it gives a(0) = 0, in
agreement with the g.f., which has no constant term. The statement is the identity of formal power
series over ℚ with the denominator cleared.
-/

namespace OMA.S_oeis_a005313

open PowerSeries

/-- a(n) = n + Sum_{k<n} F(k) F(k+1), i.e. A064831(n-1) + n as recorded in the entry. -/
def a (n : ℕ) : ℤ :=
  (n : ℤ) + ∑ k ∈ Finset.range n, (Nat.fib k : ℤ) * (Nat.fib (k + 1) : ℤ)

/-- Plouffe's g.f. for A005313, with the denominator cleared. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 3 * X + X ^ 2) * (1 + X) * (1 - X) ^ 2) =
      X * (1 - X - 3 * X ^ 2 + X ^ 3) := by
  sorry

end OMA.S_oeis_a005313
