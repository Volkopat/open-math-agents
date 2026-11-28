import Mathlib

/-!
# A208139: Number of n X 5 0..1 arrays avoiding 0 0 1 and 0 1 1 horizontally and 0 0 1 and 1 0 1 vertically.

Source: https://oeis.org/A208139
Credit: @Salofe

Conjectures from the entry, quoted verbatim:
* R. H. Hardin (Feb 23 2012): "Empirical: a(n) = n^5 + 4*n^4 + 5*n^3 + 2*n^2."
* Colin Barker, Jun 28 2018: "G.f.: 12*x*(1 + 6*x + 3*x^2) / (1 - x)^6." and
  "a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6."
* Amiram Eldar, Jun 16 2026: "Sum_{n>=1} 1/a(n) = Pi^2/4 - 19/8." and
  "Sum_{n>=1} (-1)^(n+1)/a(n) = 15/8 - Pi^2/24 - 2*log(2)."

Formalization notes:
* Offset 1, as in the entry (data: 12, 144, 720, 2400, 6300, ...). The value `a 0` (the empty
  array, counted once) is never used: Hardin's formula is stated for n ≥ 1 only.
* An n X 5 0..1 array is a function `A : Fin n → Fin 5 → Fin 2`; `A i j` is the entry in row `i`
  (top to bottom) and column `j` (left to right). Arrays are labelled: they are not identified up
  to symmetry.
* "Avoiding x y z horizontally" means that no row contains the letters x, y, z in three
  consecutive positions, read left to right; "vertically" means the same for every column, read
  top to bottom (`HasFactor`). Reading in the opposite directions gives the same count (mirror
  the array).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
* The two sums over n ≥ 1 are written with n = m + 1 for m ≥ 0, so the sign (-1)^(n+1) becomes
  `(-1) ^ (m + 1 + 1)`. They are stated with `HasSum`, which asserts that the series converges
  (unconditionally, which in `ℝ` is the same as absolutely) to the given value; `Real.log` is the
  natural logarithm.
-/

namespace OMA.S_oeis_a208139

/-- The word `w = w 0, w 1, ..., w (m - 1)` contains the letters `x, y, z` in three consecutive
positions. -/
def HasFactor {m : ℕ} (w : Fin m → Fin 2) (x y z : Fin 2) : Prop :=
  ∃ (k : ℕ) (h : k + 2 < m), w ⟨k, by omega⟩ = x ∧ w ⟨k + 1, by omega⟩ = y ∧ w ⟨k + 2, h⟩ = z

/-- An n X 5 array of 0's and 1's avoiding `0 0 1` and `0 1 1` horizontally (in every row `A i`)
and `0 0 1` and `1 0 1` vertically (in every column `fun i => A i j`). -/
def Valid {n : ℕ} (A : Fin n → Fin 5 → Fin 2) : Prop :=
  (∀ i : Fin n, ¬ HasFactor (A i) 0 0 1 ∧ ¬ HasFactor (A i) 0 1 1) ∧
  (∀ j : Fin 5, ¬ HasFactor (fun i => A i j) 0 0 1 ∧ ¬ HasFactor (fun i => A i j) 1 0 1)

/-- A208139(n): the number of such n X 5 arrays. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin n → Fin 5 → Fin 2 // Valid A}

open PowerSeries in
/-- Hardin's empirical formula, Barker's g.f. and recurrence, and Eldar's two sums. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = n ^ 5 + 4 * n ^ 4 + 5 * n ^ 3 + 2 * n ^ 2) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
        12 * X * (1 + 6 * X + 3 * X ^ 2) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3)
        - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    HasSum (fun m : ℕ => 1 / (a (m + 1) : ℝ)) (Real.pi ^ 2 / 4 - 19 / 8) ∧
    HasSum (fun m : ℕ => (-1 : ℝ) ^ (m + 1 + 1) / (a (m + 1) : ℝ))
        (15 / 8 - Real.pi ^ 2 / 24 - 2 * Real.log 2) := by
  sorry

end OMA.S_oeis_a208139
