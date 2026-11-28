import Mathlib

/-!
# A185943: Riordan array ((1/(1-x))^m, x*A000108(x)), m = 2.

Source: https://oeis.org/A185943
Credit: @agchua

R. J. Mathar (Feb 11 2011), in the formula section of A185943:
  Conjecture: R(n,1,2) = A014140(n-1). R(n,2,2) = A014143(n-2).

The triangle (offset 0) is the Riordan array (d(x), h(x)) with d(x) = (1/(1-x))^2 and
h(x) = x*C(x), where C(x) = Sum_{i>=0} catalan(i)*x^i is the g.f. of the Catalan numbers A000108.
By the usual convention its entry in row n, column k is the coefficient of x^n in d(x)*h(x)^k;
below this is `R n k`, a coefficient of a formal power series over ℚ. It reproduces the listed
rows 1; 2, 1; 3, 3, 1; 4, 7, 4, 1; 5, 16, 12, 5, 1; ... and R(n,0,2) = n + 1.
A014140 (offset 0): apply the partial sum operator twice to the Catalan numbers, that is
A014140(n) = Sum_{m=0..n} Sum_{k=0..m} catalan(k) (data 1, 3, 7, 16, 39, ...).
A014138 (offset 0): partial sums of the Catalan numbers starting 1, 2, 5, ..., that is
A014138(m) = catalan(1) + ... + catalan(m) (data 0, 1, 3, 8, 22, ...).
A014143 (offset 0): partial sums of A014138, with data 1, 4, 12, 34, 98, ..., that is
A014143(n) = A014138(1) + ... + A014138(n+1) (the leading term A014138(0) = 0 adds nothing).
The two claims are stated from the first row in which every index is a term: n >= 1 for
column 1 and n >= 2 for column 2.
-/

namespace OMA.S_oeis_a185943

/-- The g.f. of the Catalan numbers A000108, as a power series over ℚ. -/
noncomputable def catGF : PowerSeries ℚ := PowerSeries.mk (fun i => (catalan i : ℚ))

/-- A185943: R(n,k,2), the coefficient of x^n in (1/(1-x))^2 * (x*C(x))^k. -/
noncomputable def R (n k : ℕ) : ℚ :=
  PowerSeries.coeff n (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ ^ 2 * (PowerSeries.X * catGF) ^ k)

/-- A014140(n) = Sum_{m=0..n} Sum_{k=0..m} catalan(k). -/
def A014140 (n : ℕ) : ℕ := ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1), catalan k

/-- A014138(m) = catalan(1) + ... + catalan(m). -/
def A014138 (m : ℕ) : ℕ := ∑ k ∈ Finset.range m, catalan (k + 1)

/-- A014143(n) = A014138(1) + ... + A014138(n+1). -/
def A014143 (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), A014138 (j + 1)

/-- Mathar's conjecture: column 1 of A185943 is A014140 shifted by one, column 2 is A014143
shifted by two. -/
theorem main : (∀ n : ℕ, 1 ≤ n → R n 1 = (A014140 (n - 1) : ℚ)) ∧
    (∀ n : ℕ, 2 ≤ n → R n 2 = (A014143 (n - 2) : ℚ)) := by
  sorry

end OMA.S_oeis_a185943
