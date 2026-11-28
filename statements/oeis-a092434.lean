import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Dist

/-!
John W. Layman's absolute-difference conjecture, OEIS A092434 (2004).
Source: https://oeis.org/A092434 (OEIS Foundation, CC BY-SA 4.0).
Positions are numbered from zero. Entry (r,i) uses only input positions i through i+r.
-/

namespace OMA.S_oeis_a092434

/-- Entry at position i after r successive rows of adjacent absolute differences. -/
def entry (w : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, i => w i
  | r + 1, i => Nat.dist (entry w r i) (entry w r (i + 1))

/-- A finite ternary word, extended by zeros beyond its last position. -/
def extend {n : ℕ} (w : Fin n → Fin 3) (i : ℕ) : ℕ :=
  if h : i < n then (w ⟨i, h⟩).val else 0

/-- Count words whose first entry in each successive row reproduces the word. -/
def fixedCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 3 =>
    ∀ i : Fin n, entry (extend w) i.val 0 = (w i).val)).card

theorem main : ∀ n : ℕ, 1 ≤ n →
    fixedCount n = (n + 2) * 2 ^ ((n - 1) / 2) := by
  sorry

end OMA.S_oeis_a092434
