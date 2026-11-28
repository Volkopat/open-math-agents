import Mathlib

/-!
# A188822: Number of n X 7 binary arrays without the pattern 0 1 diagonally or antidiagonally

Source: https://oeis.org/A188822
Credit: @ivillar

Status: open conjecture (R. H. Hardin's empirical recurrence, Apr 11 2011; g.f. and closed forms
conjectured by Colin Barker, Apr 30 2018).

R. H. Hardin's sequence (offset 1, data 128, 1156, 3888, 8836, 15776, 24964, ...). An array with n ≥
1 rows is a map x : Fin n → Fin 7 → Fin 2 (row i, column j); the pattern 0 1 is read downwards along
diagonals and antidiagonals, so the condition involves pairs of consecutive rows only (see PairOK;
with this reading the counts agree with the data). To have consecutive rows i.castSucc, i.succ
available the number of rows is written m+1: cnt(m) counts the (m+1) X 7 arrays and a(n) = cnt(n-1).

Conjectures of the entry, all three stated in `main`:
a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4) for n>7 (stated for n ≥ 8, so that all indices are at least the
offset 1; over ℤ);
G.f.: 4*x*(32 + 225*x + 394*x^2 + 329*x^3 + 72*x^4 + 8*x^5 - 36*x^6) / ((1 - x)^3*(1 + x)) (of
Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 2*(578 - 1088*n + 512*n^2) for n>3 and even; a(n) = 2*(528 - 1088*n + 512*n^2) for n>3 and
odd (n ≥ 4, over ℚ).
-/

namespace OMA.S_oeis_a188822

/-- The condition on two consecutive rows u = x(i,·), v = x(i+1,·): reading downwards, no diagonal step
(i,j) → (i+1,j+1) and no antidiagonal step (i,j+1) → (i+1,j) shows the pattern 0 1. -/
def PairOK (u v : Fin 7 → Fin 2) : Prop :=
  ∀ j : Fin 6,
    ¬ (u j.castSucc = 0 ∧ v j.succ = 1) ∧
    ¬ (u j.succ = 0 ∧ v j.castSucc = 1)

/-- cnt(m): the number of (m+1) X 7 binary arrays x (row i, column j) in which every pair of consecutive rows
satisfies PairOK. -/
noncomputable def cnt (m : ℕ) : ℕ :=
  Nat.card {x : Fin (m + 1) → Fin 7 → Fin 2 // ∀ i : Fin m, PairOK (x i.castSucc) (x i.succ)}

/-- a(n) for n ≥ 1: the number of such n X 7 arrays, i.e. cnt(n-1). (Only n ≥ 1 is used below; the sequence has
offset 1.) -/
noncomputable def a (n : ℕ) : ℕ := cnt (n - 1)

/-- The conjectured g.f. 4*x*(32 + 225*x + 394*x^2 + 329*x^3 + 72*x^4 + 8*x^5 - 36*x^6) / ((1 - x)^3*(1 + x)). -/
noncomputable def G : PowerSeries ℚ :=
  (128 * PowerSeries.X + 900 * PowerSeries.X ^ 2 + 1576 * PowerSeries.X ^ 3 + 1316 * PowerSeries.X ^ 4 + 288 * PowerSeries.X ^ 5 + 32 * PowerSeries.X ^ 6 - 144 * PowerSeries.X ^ 7) * ((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) - 2 * (a (n - 3) : ℤ) + 1 * (a (n - 4) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 4 ≤ n → Even n → (a n : ℚ) = 2 * (578 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) ∧
    (∀ n : ℕ, 4 ≤ n → Odd n → (a n : ℚ) = 2 * (528 - 1088 * (n : ℚ) + 512 * (n : ℚ) ^ 2)) := by
  sorry

end OMA.S_oeis_a188822
