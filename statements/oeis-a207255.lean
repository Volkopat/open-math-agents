import Mathlib

/-!
# OEIS A207255 — four-row binary arrays with forbidden patterns

R. H. Hardin defined the array counts. Colin Barker conjectured the generating
function and recurrence on 21 June 2018. The sequence starts at width one.

Source: https://oeis.org/A207255 (OEIS Foundation, CC BY-SA 4.0).
Lean formalization: @rifter0418.
-/

namespace OMA.S_oeis_a207255

abbrev Grid (n : ℕ) := Fin 4 → Fin n → Bool

/-- Three consecutive entries of a line, starting at an index that fits. -/
def window {m : ℕ} (line : Fin m → Bool) (i : Fin (m - 2)) : Bool × Bool × Bool :=
  have hi := i.isLt
  (line ⟨i.val, by omega⟩, line ⟨i.val + 1, by omega⟩, line ⟨i.val + 2, by omega⟩)

/-- Read each row from left to right and each column from top to bottom. -/
def IsValid {n : ℕ} (g : Grid n) : Prop :=
  (∀ (r : Fin 4) (j : Fin (n - 2)),
    let w := window (g r) j
    w ≠ (false, false, true) ∧ w ≠ (true, false, true)) ∧
  (∀ (c : Fin n) (i : Fin 2),
    let w := window (fun r => g r c) i
    w ≠ (false, true, false) ∧ w ≠ (true, false, true))

instance {n : ℕ} (g : Grid n) : Decidable (IsValid g) := by
  unfold IsValid
  infer_instance

/-- The positive coefficients count valid grids. The offset-one series has constant term zero. -/
def a : ℕ → ℤ
  | 0 => 0
  | n + 1 => ((Finset.univ.filter (fun g : Grid (n + 1) => IsValid g)).card : ℤ)

open PowerSeries

/-- Barker's generating function with its unit denominator cleared, and his recurrence for n > 5. -/
theorem main :
    (PowerSeries.mk a * (1 - X) ^ 5 = 10 * X * (1 + 5 * X - 3 * X ^ 2 - X ^ 3)) ∧
    ∀ n : ℕ, 5 < n →
      a n = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
        5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a207255
