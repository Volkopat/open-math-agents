import OMAStatements.S_oeis_a225662

/-!
# Disproof of OEIS A225662

We disprove the claim `∀ n t : ℕ, hasPreperiod (digits n) t → 6 < t → Odd t`
by exhibiting the explicit counterexample `n = 20655` and `t = 8`.

In base 4, `20655 = 11002233_4`, so `histogram (digits 20655) = [2, 2, 2, 2]`.
Its orbit under `histogram` is:
- `t = 1`: `[2, 2, 2, 2]`
- `t = 2`: `[0, 0, 4]`
- `t = 3`: `[2, 0, 0, 0, 1]`
- `t = 4`: `[3, 1, 1]`
- `t = 5`: `[0, 2, 0, 1]`
- `t = 6`: `[2, 1, 1]`
- `t = 7`: `[0, 2, 1]` (with `histogram^[6] [0, 2, 1] = [2, 0, 1] ≠ [0, 2, 1]`)
- `t = 8`: `[1, 1, 1]` (with `histogram^[6] [1, 1, 1] = [1, 1, 1]`)

Thus `hasPreperiod (digits 20655) 8` holds with `6 < 8`, while `8` is even.
-/

namespace OMA.A225662Disproof

open OMA.S_oeis_a225662

private lemma digits_20655 : digits 20655 = [1, 1, 0, 0, 2, 2, 3, 3] := by decide

private lemma hist8 : histogram^[8] (digits 20655) = [1, 1, 1] := by
  rw [digits_20655]; decide

private lemma hist7 : histogram^[7] (digits 20655) = [0, 2, 1] := by
  rw [digits_20655]; decide

private lemma hasPreperiod_20655_8 : hasPreperiod (digits 20655) 8 := by
  unfold hasPreperiod
  refine ⟨?_, Or.inr ?_⟩
  · rw [hist8]; decide
  · change histogram^[6] (histogram^[7] (digits 20655)) ≠ histogram^[7] (digits 20655)
    rw [hist7]; decide

theorem result : ¬ (type_of% @OMA.S_oeis_a225662.main) := by
  intro h
  have hodd : Odd 8 := h 20655 8 hasPreperiod_20655_8 (by decide)
  rcases hodd with ⟨k, hk⟩
  omega

end OMA.A225662Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a225662.main) := OMA.A225662Disproof.result
