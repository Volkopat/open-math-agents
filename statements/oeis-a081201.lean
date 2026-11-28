import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi

/-!
# Hardin's count of six collinear points in a cubic grid (OEIS A081201)

Source: https://oeis.org/A081201
Credit: @anmolspace

R. H. Hardin conjectured that in the grid with six positions in each of
n dimensions, the number of unordered sets of six distinct collinear points
is the nth term of A081201. Its published closed form is (8^n - 6^n)/2.
The entries at n=0, 1, 2 are 0, 1, 14.
-/

namespace OMA.S_oeis_a081201

abbrev Grid (n : ℕ) := Fin n → Fin 6

/-- Every displacement from a fixed point is parallel to the line through two
distinct points of the set. All two-coordinate minors are computed in ℤ. -/
def Collinear {n : ℕ} (s : Finset (Grid n)) : Prop :=
  ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∀ z ∈ s, ∀ i j : Fin n,
    ((z i : ℤ) - a i) * ((b j : ℤ) - a j) =
      ((z j : ℤ) - a j) * ((b i : ℤ) - a i)

/-- Count subsets, so permuting their six points never creates a second line. -/
noncomputable def lineCount (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s : Finset (Grid n) => s.card = 6 ∧ Collinear s)).card

theorem main : ∀ n : ℕ, lineCount n = (8^n - 6^n) / 2 := by
  sorry

end OMA.S_oeis_a081201
