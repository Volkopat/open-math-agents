import Mathlib

/-!
# A235878: Number of (n+1) X (2+1) 0..2 arrays with the minimum plus the upper median equal to the lower median plus the maximum in every 2 X 2 subblock

Source: https://oeis.org/A235878
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 51, 105, 231, 537, 1311, 3345, ...). An array is a map
x : Fin (n+1) → Fin 3 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed by
rows i, i+1 and columns j, j+1. Sorting the four entries of a subblock increasingly as
l0 ≤ l1 ≤ l2 ≤ l3, the minimum is l0, the lower median l1, the upper median l2 and the maximum l3;
the condition is l0 + l2 = l1 + l3.

Conjectures (Colin Barker, Oct 19 2018), together with the empirical recurrence of the entry:
a(n) = 6*a(n-1) - 11*a(n-2) + 6*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: 3*x*(17 - 67*x + 54*x^2) / ((1 - x)*(1 - 2*x)*(1 - 3*x)) (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 3*(2 + 3*2^(1+n) + 3^n) (n ≥ 1).
-/

namespace OMA.S_oeis_a235878

/-- Minimum plus upper median equals lower median plus maximum, for the entries p, q, r, s. -/
def Med4 (p q r s : Fin 3) : Prop :=
  (List.insertionSort (· ≤ ·) [(p : ℕ), q, r, s]).getD 0 0 +
      (List.insertionSort (· ≤ ·) [(p : ℕ), q, r, s]).getD 2 0 =
    (List.insertionSort (· ≤ ·) [(p : ℕ), q, r, s]).getD 1 0 +
      (List.insertionSort (· ≤ ·) [(p : ℕ), q, r, s]).getD 3 0

/-- Both 2 X 2 subblocks formed by rows u, v satisfy the median condition. -/
def BlockOK (u v : Fin 3 → Fin 3) : Prop :=
  ∀ j : Fin 2, Med4 (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- a(n): the number of such (n+1) X 3 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 3 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. 3*x*(17 - 67*x + 54*x^2) / ((1 - x)*(1 - 2*x)*(1 - 3*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (3 * PowerSeries.X * (17 - 67 * PowerSeries.X + 54 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 11 * a (n - 2) + 6 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → a n = 3 * (2 + 3 * 2 ^ (1 + n) + 3 ^ n)) := by
  sorry

end OMA.S_oeis_a235878
