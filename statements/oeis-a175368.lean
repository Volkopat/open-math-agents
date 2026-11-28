import Mathlib

/-!
# A175368: Number of integer 4-tuples (x,y,z,u) satisfying |x|^3 + |y|^3 + |z|^3 + |u|^3 = n, -n <= x,y,z,u <= n.

Source: https://oeis.org/A175368
Credit: @agchua

From the formula section of A175368 (entry by R. J. Mathar, Apr 24 2010):
  Conjectured g.f.: (1 + 2*Sum_{j>=1} x^(j^3))^4.
Offset 0 (a(0) = 1, the tuple (0,0,0,0)). The definition below counts the 4-tuples of integers in
[-n, n] with |x|^3 + |y|^3 + |z|^3 + |u|^3 = n, exactly as in the name. The power series
Sum_{j>=1} x^(j^3) is the formal power series over ℚ whose coefficient of x^m is the number of j in
1..m with j^3 = m (that is 1 if m is a positive cube and 0 otherwise; every j ≥ 1 with j^3 = m
satisfies j ≤ m). The conjecture is stated as the identity of formal power series over ℚ
Sum_n a(n) x^n = (1 + 2 * Sum_{j>=1} x^(j^3))^4.
-/

namespace OMA.S_oeis_a175368

/-- A175368(n): the number of (x, y, z, u) ∈ ℤ^4 with -n ≤ x, y, z, u ≤ n and
|x|^3 + |y|^3 + |z|^3 + |u|^3 = n. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ
      Finset.Icc (-(n : ℤ)) n).filter
    (fun p : ℤ × ℤ × ℤ × ℤ =>
      |p.1| ^ 3 + |p.2.1| ^ 3 + |p.2.2.1| ^ 3 + |p.2.2.2| ^ 3 = (n : ℤ))).card

/-- The conjectured g.f. (1 + 2 Sum_{j ≥ 1} x^(j^3))^4. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 2 * PowerSeries.mk
        (fun m => (((Finset.Icc 1 m).filter (fun j => j ^ 3 = m)).card : ℚ))) ^ 4 := by
  sorry

end OMA.S_oeis_a175368
