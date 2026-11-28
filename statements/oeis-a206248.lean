import Mathlib

/-!
# A206248: Number of (n+1) X 2 0..3 arrays with every 2 X 2 subblock having zero permanent

Source: https://oeis.org/A206248
Credit: @ivillar

R. H. Hardin's sequence (offset 1, data 49, 361, 1600, 9409, 47089, ...). An array is a map
x : Fin (n+1) → Fin 2 → Fin 4 (row i, column j, value in 0..3); its 2 X 2 subblocks are formed by
rows i, i+1, and the permanent of [[p, q], [r, s]] is p*s + q*r.

Conjectures (Colin Barker, Jun 14 2018), together with the empirical recurrence of the entry:
a(n) = 4*a(n-1) +12*a(n-2) -27*a(n-3) (stated for n ≥ 4, all indices at least the offset 1, over ℤ);
G.f.: x*(49 + 165*x - 432*x^2) / ((1 + 3*x)*(1 - 7*x + 9*x^2)) (of Sum_{n ≥ 1} a(n) x^n, over ℚ);
a(n) = 2^(-n)*((-1)^n*2^(1+n)*3^(3+n) + (77-20*sqrt(13))*(7-sqrt(13))^n
  + (7+sqrt(13))^n*(77+20*sqrt(13))) / 13 (n ≥ 1, over ℝ).
Status: known result: Sela Fried (Feb 13 2026) records in the entry that Barker's conjectures are
true (see the Fried link there).
-/

namespace OMA.S_oeis_a206248

/-- The permanent of the 2 X 2 subblock formed by rows r and s. -/
def perm (r s : Fin 2 → Fin 4) : ℕ := (r 0 : ℕ) * s 1 + (r 1 : ℕ) * s 0

/-- a(n): the number of (n+1) X 2 arrays over 0..3 all of whose 2 X 2 subblocks have zero
permanent. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin (n + 1) → Fin 2 → Fin 4 // ∀ i : Fin n, perm (x i.castSucc) (x i.succ) = 0}

/-- The conjectured g.f. x*(49 + 165*x - 432*x^2) / ((1 + 3*x)*(1 - 7*x + 9*x^2)). -/
noncomputable def G : PowerSeries ℚ :=
  (PowerSeries.X * (49 + 165 * PowerSeries.X - 432 * PowerSeries.X ^ 2)) *
    ((1 + 3 * PowerSeries.X) * (1 - 7 * PowerSeries.X + 9 * PowerSeries.X ^ 2))⁻¹

/-- The recurrence, the g.f. and the closed form. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (a n : ℤ) = 4 * a (n - 1) + 12 * a (n - 2) - 27 * a (n - 3)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (2 : ℝ) ^ (-(n : ℤ)) *
      ((-1) ^ n * 2 ^ (1 + n) * 3 ^ (3 + n) + (77 - 20 * Real.sqrt 13) * (7 - Real.sqrt 13) ^ n +
        (7 + Real.sqrt 13) ^ n * (77 + 20 * Real.sqrt 13)) / 13) := by
  sorry

end OMA.S_oeis_a206248
