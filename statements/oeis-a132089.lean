import Mathlib

/-!
# A132089: Triangle T, read by rows, equal to the matrix square of Losanitsch's triangle (A034851).

Source: https://oeis.org/A132089 (Losanitsch's triangle: https://oeis.org/A034851,
A005418: https://oeis.org/A005418)
Credit: @agchua

Comment line of A132089 (no author or date given there), quoted verbatim:
  Conjectures: (1) The first column equals the row sums of Losanitsch's triangle (which equals
  A005418). (2) Let L^n denote the n-th power of Losanitsch's triangle. Then the first column of
  L^(n+1) equals the row sums of L^n.

Definitions.
* Losanitsch's triangle A034851 (offset 0, rows n >= 0, 0 <= k <= n), from its formula line
  T(n, k) = (1/2) * (A007318(n, k) + A051159(n, k)), written out as in the PARI program of A132089:
  L(n, k) = (1/2) * (binomial(n, k) + binomial(n mod 2, k mod 2) * binomial(floor(n/2), floor(k/2))).
  For k > n this is 0, so L is an infinite lower triangular matrix. Its values are integers; they
  are computed in the rationals because the formula divides by 2.
* `Lpow m` is the m-th matrix power L^m: L^0 is the identity matrix and
  L^(m+1)(i, j) = Sum_{k=0..i} L^m(i, k) * L(k, j). The sum may stop at k = i because L^m is lower
  triangular, so this is the ordinary product of infinite lower triangular matrices.
* A132089 (offset 0) is T = L^2: T(n, k) = Sum_{j=0..n} L(n, j) * L(j, k) (again L(n, j) = 0 for
  j > n).
* A005418 (offset 1), from its formula line: a(m) = 2^(m-2) + 2^(floor(m/2) - 1) (integer powers
  of 2 in the rationals; for m = 1 both exponents are -1). Its name line says it is also the row
  sums of A034851, row n of the triangle giving a(n+1); so the claim in parentheses is stated as
  Sum_{j=0..n} L(n, j) = A005418(n+1) for all n >= 0.
Part (1) is stated for every row n >= 0, part (2) for every power n >= 0 (L^0 is the identity)
and every row i >= 0.
-/

namespace OMA.S_oeis_a132089

/-- Losanitsch's triangle A034851: L(n, k) = (C(n, k) + C(n mod 2, k mod 2) * C(n/2, k/2)) / 2. -/
noncomputable def L (n k : ℕ) : ℚ :=
  ((Nat.choose n k + Nat.choose (n % 2) (k % 2) * Nat.choose (n / 2) (k / 2) : ℕ) : ℚ) / 2

/-- The matrix powers L^m of the lower triangular matrix L. -/
noncomputable def Lpow : ℕ → ℕ → ℕ → ℚ
  | 0, i, j => if i = j then 1 else 0
  | m + 1, i, j => ∑ k ∈ Finset.range (i + 1), Lpow m i k * L k j

/-- A132089: the matrix square T = L^2 of Losanitsch's triangle. -/
noncomputable def T (n k : ℕ) : ℚ := ∑ j ∈ Finset.range (n + 1), L n j * L j k

/-- A005418(m) = 2^(m-2) + 2^(floor(m/2) - 1), offset 1. -/
noncomputable def A005418 (m : ℕ) : ℚ :=
  (2 : ℚ) ^ ((m : ℤ) - 2) + (2 : ℚ) ^ (((m / 2 : ℕ) : ℤ) - 1)

/-- Conjecture (1): the first column of T is the row sums of L, and these are A005418(n+1);
conjecture (2): the first column of L^(m+1) is the row sums of L^m. -/
theorem main :
    (∀ n : ℕ, T n 0 = ∑ j ∈ Finset.range (n + 1), L n j) ∧
    (∀ n : ℕ, ∑ j ∈ Finset.range (n + 1), L n j = A005418 (n + 1)) ∧
    (∀ m i : ℕ, Lpow (m + 1) i 0 = ∑ j ∈ Finset.range (i + 1), Lpow m i j) := by
  sorry

end OMA.S_oeis_a132089
