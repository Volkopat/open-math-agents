import Mathlib

/-!
# A209722: 1/4 the number of (n+1) X 4 0..2 arrays with every 2 X 2 subblock having distinct clockwise edge differences

Source: https://oeis.org/A209722
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 4, 5, 6, 8, 10, 14, 18, 26, 34, 50, ...). An array is a map
x : Fin (n+1) → Fin 4 → Fin 3 (row i, column j, value in 0..2); its 2 X 2 subblocks are formed by
rows i, i+1 and columns j, j+1. Going clockwise around the subblock [[p, q], [r, s]] (p -> q -> s ->
r -> p), the edge differences are q - p, s - q, r - s, p - r (integers), and they must be pairwise
distinct. a(n) is 1/4 of the number N(n) of such arrays.

Conjectures (Colin Barker, Jul 12 2018), together with the empirical recurrence of the entry:
a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: x*(4 + x - 7*x^2) / ((1 - x)*(1 - 2*x^2)) (of Sum_{n ≥ 1} a(n) x^n, as a power series over ℚ);
a(n) = 3*2^(n/2 - 1) + 2 for n even, a(n) = 2^((n + 1)/2) + 2 for n odd (n ≥ 1).
-/

namespace OMA.S_oeis_a209722

/-- The clockwise edge differences of the subblock [[p, q], [r, s]] are pairwise distinct. -/
def CW (p q r s : Fin 3) : Prop :=
  [(q : ℤ) - p, (s : ℤ) - q, (r : ℤ) - s, (p : ℤ) - r].Nodup

/-- All three 2 X 2 subblocks formed by rows u, v satisfy the condition. -/
def BlockOK (u v : Fin 4 → Fin 3) : Prop :=
  ∀ j : Fin 3, CW (u j.castSucc) (u j.succ) (v j.castSucc) (v j.succ)

/-- N(n): the number of such (n+1) X 4 arrays. -/
noncomputable def N (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 4 → Fin 3 // ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ)}

/-- a(n) = N(n)/4. -/
noncomputable def a (n : ℕ) : ℕ := N n / 4

/-- The conjectured g.f. x*(4 + x - 7*x^2) / ((1 - x)*(1 - 2*x^2)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (4 + PowerSeries.X - 7 * PowerSeries.X ^ 2)) *
    ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))⁻¹

/-- The recurrence, the g.f. and the closed forms. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → Even n → a n = 3 * 2 ^ (n / 2 - 1) + 2) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → a n = 2 ^ ((n + 1) / 2) + 2) := by
  sorry

end OMA.S_oeis_a209722
