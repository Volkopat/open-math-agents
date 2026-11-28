import Mathlib

/-!
# A235886: Number of (n+1) X (1+1) 0..3 arrays with the minimum plus the upper median equal to the lower median plus the maximum in every 2 X 2 subblock

Source: https://oeis.org/A235886
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 40, 112, 352, 1216, 4480, 17152, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 4 (row i, column j, value in 0..3); its 2 X 2 subblocks are formed by
rows i, i+1. Sorting the four entries of a subblock increasingly as l0 ≤ l1 ≤ l2 ≤ l3, the minimum is
l0, the lower median l1, the upper median l2 and the maximum l3; the condition is l0 + l2 = l1 + l3.

Conjectures (Colin Barker, Oct 19 2018), together with the empirical recurrence of the entry:
a(n) = 6*a(n-1) - 8*a(n-2) (stated for n ≥ 3, all indices at least the offset 1, over ℤ);
G.f.: 8*x*(5 - 16*x) / ((1 - 2*x)*(1 - 4*x)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 2^(2+n) * (3+2^n) (n ≥ 1).
-/

namespace OMA.S_oeis_a235886

/-- The four entries of the subblock formed by rows u and v, sorted increasingly. -/
def sorted4 (u v : Fin 2 → Fin 4) : List ℕ :=
  List.insertionSort (· ≤ ·) [(u 0 : ℕ), (u 1 : ℕ), (v 0 : ℕ), (v 1 : ℕ)]

/-- Minimum plus upper median equals lower median plus maximum. -/
def BlockOK (u v : Fin 2 → Fin 4) : Prop :=
  (sorted4 u v).getD 0 0 + (sorted4 u v).getD 2 0 = (sorted4 u v).getD 1 0 + (sorted4 u v).getD 3 0

/-- a(n): the number of (n+1) X 2 arrays over 0..3 all of whose 2 X 2 subblocks satisfy BlockOK. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- The conjectured g.f. 8*x*(5 - 16*x) / ((1 - 2*x)*(1 - 4*x)). -/
noncomputable def G : PowerSeries ℚ :=
  (8 * PowerSeries.X * (5 - 16 * PowerSeries.X)) * ((1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 8 * a (n - 2)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → a n = 2 ^ (2 + n) * (3 + 2 ^ n)) := by
  sorry

end OMA.S_oeis_a235886
