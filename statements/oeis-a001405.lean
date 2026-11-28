import Mathlib

/-!
# A001405: a(n) = binomial(n, floor(n/2)).

Source: https://oeis.org/A001405
Credit: @diegopluna

Conjecture (John M. Campbell, Mar 30 2018). Let C_n(R, H) denote the transition matrix from the
ribbon basis to the homogeneous basis of the graded component of the algebra of noncommutative
symmetric functions of order n. Letting I(2^(n-1)) denote the identity matrix of order 2^(n-1),
the dimension of the kernel of C_n(R, H) - I(2^(n-1)) is always equal to a(n-1).

Reading of the source:
* `a n = Nat.choose n (n / 2)`, offset 0.
* The degree-n component of NSym has the ribbon basis (R_I) and the homogeneous basis (H_I),
  both indexed by the compositions I of n (there are 2^(n-1) of them for n >= 1, matching the
  order of the identity matrix in the source; the statement is for n >= 1).
* The change of basis is the standard one (Gelfand, Krob, Lascoux, Leclerc, Retakh, Thibon,
  "Noncommutative symmetric functions", Prop. 3.13):
    R_I = sum over compositions J coarser than I of (-1)^(l(I) - l(J)) H_J,
  where J is coarser than I when the partial sums of J are among those of I, that is
  `J.boundaries ⊆ I.boundaries` in Mathlib's `Composition`, and l is the number of parts.
  `C n` is this matrix: row I lists the coordinates of R_I in the H basis.
* The kernel is taken over ℚ (the entries are integers). Reading the transition matrix the
  other way round (transpose, or the inverse matrix expressing H in terms of R) does not change
  the dimension of the kernel of (matrix - identity): transposing preserves rank, and
  M⁻¹ - 1 = M⁻¹ (1 - M). So the statement does not depend on that convention.
* Checked numerically (exact rational rank) for n = 1, ..., 9: kernel dimensions
  1, 1, 2, 3, 6, 10, 20, 35, 70 = a(0), ..., a(8).
-/

namespace OMA.S_oeis_a001405

/-- A001405(n) = binomial(n, floor(n/2)). -/
def a (n : ℕ) : ℕ := Nat.choose n (n / 2)

/-- The transition matrix from the ribbon basis to the homogeneous basis of NSym in degree n:
the entry at (I, J) is the coefficient of H_J in R_I, namely (-1)^(l(I) - l(J)) when J is coarser
than I, and 0 otherwise. -/
def C (n : ℕ) : Matrix (Composition n) (Composition n) ℚ :=
  fun I J => if J.boundaries ⊆ I.boundaries then (-1 : ℚ) ^ (I.length - J.length) else 0

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      Module.finrank ℚ (LinearMap.ker (Matrix.toLin' (C n - 1))) = a (n - 1) := by
  sorry

end OMA.S_oeis_a001405
