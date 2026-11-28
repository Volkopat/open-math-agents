import Mathlib

/-!
# A204708: Number of (n+1) X 4 0..1 arrays with the permanents of all 2 X 2 subblocks equal and nonzero

Source: https://oeis.org/A204708
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 25, 81, 257, 833, 2689, 8705, ...). An array is a map
x : Fin (n+1) → Fin 4 → Fin 2 (row i, column j, value in 0..1); its 2 X 2 subblocks are formed by
rows i, i+1 and columns j, j+1, and the permanent of [[p, q], [r, s]] is p*s + q*r. The condition is
that there is a nonzero number k such that every subblock has permanent k.

Conjectures (Colin Barker, Jun 09 2018), together with the empirical recurrence of the entry:
a(n) = 3*a(n-1) +2*a(n-2) -4*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: x*(25 + 6*x - 36*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)) (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = (5 + (20-8*sqrt(5))*(1-sqrt(5))^n + 4*(1+sqrt(5))^n*(5+2*sqrt(5))) / 5 (n ≥ 1, over ℝ).
-/

namespace OMA.S_oeis_a204708

/-- The permanent of [[p, q], [r, s]]. -/
def perm (p q r s : Fin 2) : ℕ := (p : ℕ) * s + (q : ℕ) * r

/-- All three 2 X 2 subblocks formed by rows u, v have permanent k. -/
def BlockP (k : ℕ) (u v : Fin 4 → Fin 2) : Prop :=
  ∀ j : Fin 3, perm (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ) = k

/-- The permanents of all 2 X 2 subblocks are equal and nonzero. -/
def Good {n : ℕ} (x : Fin (n + 1) → Fin 4 → Fin 2) : Prop :=
  ∃ k : ℕ, k ≠ 0 ∧ ∀ i : Fin n, BlockP k (x i.castSucc) (x i.succ)

/-- a(n): the number of such (n+1) X 4 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin (n + 1) → Fin 4 → Fin 2 // Good x}

/-- The conjectured g.f. x*(25 + 6*x - 36*x^2) / ((1 - x)*(1 - 2*x - 4*x^2)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (25 + 6 * PowerSeries.X - 36 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 2 * a (n - 2) - 4 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (5 + (20 - 8 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n +
      4 * (1 + Real.sqrt 5) ^ n * (5 + 2 * Real.sqrt 5)) / 5) := by
  sorry

end OMA.S_oeis_a204708
