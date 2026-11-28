import Mathlib

/-!
# OEIS A022163: First row of the spectral array W(√(3/2))

Source: https://oeis.org/A022163
The recurrence and generating function are credited there to Colin Barker.
-/

namespace OMA.S_oeis_a022163

noncomputable def slope : ℝ := Real.sqrt (3 / 2)

noncomputable def lower (k : ℕ) : ℕ :=
  (⌊(k : ℝ) * slope⌋ : ℤ).toNat

-- The complementary Beatty sequence enumerates the positive integers
-- outside the lower sequence, with indexing starting at one.
noncomputable def upper (k : ℕ) : ℕ :=
  (⌊(k : ℝ) * (slope / (slope - 1))⌋ : ℤ).toNat

-- Consecutive pairs in the first row, following the OEIS algorithm.
noncomputable def rowPair : ℕ → ℕ × ℕ
  | 0 => (lower 1 ^ 2, upper (lower 1))
  | n + 1 =>
    let k := (rowPair n).2
    (lower k, upper k)

noncomputable def term (n : ℕ) : ℕ :=
  if n % 2 = 0 then (rowPair (n / 2)).1 else (rowPair (n / 2)).2

noncomputable def ogf : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (term n : ℤ))

-- The generating function is written after multiplying by its denominator.
theorem main :
    (∀ n : ℕ, (term (n + 4) : ℤ) =
      6 * (term (n + 2) : ℤ) - 3 * (term n : ℤ)) ∧
    (let x : PowerSeries ℤ := PowerSeries.X
     (3 * x ^ 4 - 6 * x ^ 2 + 1) * ogf = 1 + 5 * x - 3 * x ^ 3) := by
  sorry

end OMA.S_oeis_a022163
