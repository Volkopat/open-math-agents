import Mathlib

/-!
# A250778: Number of (n+1) X (3+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction

Source: https://oeis.org/A250778
Credit: @ivillar

Status: open conjecture (R. H. Hardin's empirical recurrence, Nov 27 2014; g.f. and closed form
conjectured by Colin Barker, Nov 19 2018).

R. H. Hardin's sequence (offset 1, data 46, 106, 230, 482, 990, 2010, ...). An array is a map x :
Fin (n+1) → Fin 4 → Fin 2 (row i, column j, entries 0..1). The two conditions of the title compare,
for every 2 X 2 subblock (rows i-1, i and columns j-1, j), the two rows (first condition) and the
two columns (second condition); see PairOK. a(n) is the number of such arrays.

Conjectures of the entry, all three stated in `main`:
a(n) = 4*a(n-1) - 5*a(n-2) + 2*a(n-3) (stated for n ≥ 4, so that all indices are at least the offset
1; over ℤ);
G.f.: 2*x*(23 - 39*x + 18*x^2) / ((1 - x)^2*(1 - 2*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series
over ℚ);
a(n) = 2^(5+n) - 4*n - 14 (n ≥ 1, over ℚ).
-/

namespace OMA.S_oeis_a250778

/-- The conditions on the 2 X 2 subblocks formed by two consecutive rows u = x(i-1,·), v = x(i,·)
and two consecutive columns j-1, j (here j.castSucc and j.succ): x(i,j)+x(i,j-1) is nondecreasing in
the i direction, i.e. x(i-1,j)+x(i-1,j-1) ≤ x(i,j)+x(i,j-1), and |x(i,j)-x(i-1,j)| is nondecreasing
in the j direction, i.e. |x(i,j-1)-x(i-1,j-1)| ≤ |x(i,j)-x(i-1,j)|. -/
def PairOK (u v : Fin 4 → Fin 2) : Prop :=
  ∀ j : Fin 3,
    ((u j.succ : ℕ) : ℤ) + ((u j.castSucc : ℕ) : ℤ) ≤ ((v j.succ : ℕ) : ℤ) + ((v j.castSucc : ℕ) : ℤ) ∧
    |((v j.castSucc : ℕ) : ℤ) - ((u j.castSucc : ℕ) : ℤ)| ≤ |((v j.succ : ℕ) : ℤ) - ((u j.succ : ℕ) : ℤ)|

/-- a(n): the number of such (n+1) X 4 arrays x (row i, column j, entries 0..1). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 4 → Fin 2 // ∀ i : Fin n, PairOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. 2*x*(23 - 39*x + 18*x^2) / ((1 - x)^2*(1 - 2*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (46 * PowerSeries.X - 78 * PowerSeries.X ^ 2 + 36 * PowerSeries.X ^ 3) * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 4 * (a (n - 1) : ℤ) - 5 * (a (n - 2) : ℤ) + 2 * (a (n - 3) : ℤ)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 : ℚ) ^ (5 + n) - 4 * (n : ℚ) - 14) := by
  sorry

end OMA.S_oeis_a250778
