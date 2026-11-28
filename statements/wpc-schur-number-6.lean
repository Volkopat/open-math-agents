import Mathlib

/-!
# The Schur number S(6)

Source: https://en.wikipedia.org/wiki/Schur%27s_theorem
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_wpc_schur_number_6

-- definitions the statement needs (no sorry, no axiom)

/-- A coloring of `{1,...,S}` (represented by `Fin S`, the integer being `val + 1`)
with `c` colors has a monochromatic solution of `x + y = z` when some `x`, `y`, `z`
of the same color satisfy `(x.val + 1) + (y.val + 1) = z.val + 1`. -/
def HasMonochromaticSum (c S : ℕ) (color : Fin S → Fin c) : Prop :=
  ∃ x y z : Fin S, color x = color y ∧ color y = color z ∧ x.val + y.val + 1 = z.val

/-- `IsSchur c S`: every partition of the integers `{1,...,S}` into `c` parts
(a coloring `Fin S → Fin c`; a part is a color class, empty parts allowed) has one
of the parts containing integers `x`, `y` and `z` with `x + y = z`. -/
def IsSchur (c S : ℕ) : Prop :=
  ∀ color : Fin S → Fin c, HasMonochromaticSum c S color

/-- The Schur number `S(c)`: the smallest number `S` such that every partition of
`{1,...,S}` into `c` parts has a part containing `x`, `y`, `z` with `x + y = z`
(defined as `0` when no such `S` exists; Schur's theorem ensures one exists for
every positive `c`). -/
noncomputable def schurNumber (c : ℕ) : ℕ := by
  by_cases h : ∃ S, 0 < S ∧ IsSchur c S
  · haveI : DecidablePred (fun n : ℕ => 0 < n ∧ IsSchur c n) := Classical.decPred _
    exact Nat.find h
  · exact 0

/-- Schur's theorem at `c = 6` (the source's statement with `c := 6`): there exists
a positive integer `S` such that for every partition of the integers `{1,...,S}`
into 6 parts, one of the parts contains integers `x`, `y` and `z` with `x + y = z`.
This is exactly the source's guarantee that the Schur number `S(6)` is well-defined. -/
theorem main : ∃ S : ℕ, 0 < S ∧ IsSchur 6 S := by
  sorry

end OMA.S_wpc_schur_number_6
