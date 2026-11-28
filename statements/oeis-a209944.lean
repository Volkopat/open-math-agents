import Mathlib

/-!
# A209944: a(n) is half the number of (n+1) X 2 0..2 arrays with every 2 X 2 subblock having at most one duplicate clockwise edge difference

Source: https://oeis.org/A209944
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 34, 258, 1956, 14832, 112464, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed by
rows i, i+1. Going clockwise around the subblock [[p, q], [r, s]] (p -> q -> s -> r -> p), the edge
differences are q - p, s - q, r - s, p - r (integers); at most one duplicate means that at least
three distinct values occur among these four differences. a(n) is half the number N(n) of such
arrays.

Conjectures of the entry (empirical recurrence; Colin Barker, Jul 14 2018; Stefano Spezia, Aug 02 2025):
a(n) = 6*a(n-1) + 12*a(n-2) (stated for n ≥ 3, all indices at least the offset 1);
G.f.: 2*x*(17 + 27*x) / (1 - 6*x - 12*x^2) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = ((3-sqrt(21))^n*(-41+9*sqrt(21)) + (3+ sqrt(21))^n*(41+9*sqrt(21))) / (4*sqrt(21)) (n ≥ 1);
e.g.f.: exp(3*x)*(189*cosh(sqrt(21)*x) + 41*sqrt(21)*sinh(sqrt(21)*x))/42 - 9/2, i.e. for every
real x the series Sum_{n ≥ 1} a(n) x^n/n! converges to that value (the e.g.f. has no constant term,
matching the offset 1).
-/

namespace OMA.S_oeis_a209944

/-- At least three distinct values among the clockwise edge differences of [[p, q], [r, s]]. -/
def CW (p q r s : Fin 3) : Prop :=
  3 ≤ ([(q : ℤ) - p, (s : ℤ) - q, (r : ℤ) - s, (p : ℤ) - r].toFinset).card

/-- The subblock formed by rows u, v satisfies the condition. -/
def BlockOK (u v : Fin 2 → Fin 3) : Prop := CW (u 0) (u 1) (v 0) (v 1)

/-- N(n): the number of such (n+1) X 2 arrays. -/
noncomputable def N (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- a(n) = N(n)/2. -/
noncomputable def a (n : ℕ) : ℕ := N n / 2

/-- The conjectured g.f. 2*x*(17 + 27*x) / (1 - 6*x - 12*x^2). -/
noncomputable def G : PowerSeries ℚ :=
  (2 * PowerSeries.X * (17 + 27 * PowerSeries.X)) * (1 - 6 * PowerSeries.X - 12 * PowerSeries.X ^ 2)⁻¹

/-- The recurrence, the g.f., the closed form and the e.g.f. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → a n = 6 * a (n - 1) + 12 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((3 - Real.sqrt 21) ^ n * (-41 + 9 * Real.sqrt 21) +
      (3 + Real.sqrt 21) ^ n * (41 + 9 * Real.sqrt 21)) / (4 * Real.sqrt 21)) ∧
    (∀ x : ℝ, HasSum (fun n => (if n = 0 then (0 : ℝ) else (a n : ℝ)) * x ^ n / (n.factorial : ℝ))
      (Real.exp (3 * x) * (189 * Real.cosh (Real.sqrt 21 * x) +
        41 * Real.sqrt 21 * Real.sinh (Real.sqrt 21 * x)) / 42 - 9 / 2)) := by
  sorry

end OMA.S_oeis_a209944
