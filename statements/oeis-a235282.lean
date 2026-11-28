import Mathlib

/-!
# A235282: Number of (n+1) X (1+1) 0..3 arrays with every 2 X 2 subblock having its diagonal sum differing from its antidiagonal sum by 4 (constant-stress 1 X 1 tilings)

Source: https://oeis.org/A235282
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 20, 40, 68, 136, 236, 472, 836, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 4 (row i, column j, value in 0..3); its 2 X 2 subblocks are formed by
rows i, i+1. For the subblock [[p, q], [r, s]] the diagonal sum is p + s and the antidiagonal sum is
q + r; they must differ by 4 (in either direction).

Conjectures (Colin Barker, Oct 18 2018), together with the empirical recurrence of the entry:
a(n) = 2*a(n-1) + 3*a(n-2) - 6*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: 4*x*(5 - 18*x^2) / ((1 - 2*x)*(1 - 3*x^2)) (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 2^(2+n) + 2*3^((-1+n)/2) * (3-3*(-1)^n + 2*sqrt(3) + 2*(-1)^n*sqrt(3)) (n ≥ 1, over ℝ,
with 3^((-1+n)/2) the real power).
-/

namespace OMA.S_oeis_a235282

/-- The diagonal and antidiagonal sums of the subblock formed by rows u, v differ by 4. -/
def BlockOK (u v : Fin 2 → Fin 4) : Prop :=
  (u 0 : ℕ) + v 1 = u 1 + v 0 + 4 ∨ (u 1 : ℕ) + v 0 = u 0 + v 1 + 4

/-- a(n): the number of (n+1) X 2 arrays over 0..3 all of whose 2 X 2 subblocks satisfy BlockOK. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. 4*x*(5 - 18*x^2) / ((1 - 2*x)*(1 - 3*x^2)). -/
noncomputable def G : PowerSeries ℚ :=
  (4 * PowerSeries.X * (5 - 18 * PowerSeries.X ^ 2)) *
    ((1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X ^ 2))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 2 ^ (2 + n) + 2 * (3 : ℝ) ^ (((-1 : ℝ) + n) / 2) *
      (3 - 3 * (-1) ^ n + 2 * Real.sqrt 3 + 2 * (-1) ^ n * Real.sqrt 3)) := by
  sorry

end OMA.S_oeis_a235282
