import OMAStatements.S_mo_495589
import Mathlib

/-!
# MathOverflow 495589: the first-failure characterisation is false for `k = 0`, `l = 4`

Here `k` is even and `l ≡ 1 (mod 3)`, so the right-hand side of the first equivalence holds.
But `weighted 0 4 0 = 4` and `weighted 0 4 1 = 1 · (4 + 4⁰) / 2 = 5/2`, which is not an integer,
so the first failure happens at `n = 2`, not at `n = 3`.
-/

open OMA.S_mo_495589 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_495589.main) := by
  rintro ⟨h, -⟩
  have hf : firstFailure 0 4 3 := (h 0 4).1.mpr (Or.inr ⟨rfl, rfl⟩)
  have h2 := hf.2.2 2 (by norm_num) (by norm_num)
  revert h2
  decide +kernel
