import OMAStatements.S_oeis_a276706
import Mathlib

/-!
# OEIS A276706: the first recurrence fails at `n = 5`

`L(n) = lcm(n + 3, |n - 3|)` takes the values `4, 5, 0, 7, 8, 9, …` for `n = 1, 2, 3, …`. Since
`L(3) = 0`, the index `3` is not a record, and the records are at `n = 1, 2, 4, 5, 6, …`. Hence
`a(2) = 2`, `a(3) = 4`, `a(4) = 5`, `a(5) = 6`, while the recurrence would give
`a(5) = a(4) + a(3) - a(2) = 7`.
-/

open OMA.S_oeis_a276706

namespace OMA.A276706

/-- The `k`-th record (0-indexed) is `m` when `m` is a record with exactly `k` records below it. -/
lemma nth_eq {k m : ℕ} (hm : IsRecord m) (hc : Nat.count IsRecord m = k) :
    Nat.nth IsRecord k = m := by
  rw [← hc]
  exact Nat.nth_count hm

lemma a_2 : a 2 = 2 := nth_eq (by decide) (by decide)

lemma a_3 : a 3 = 4 := nth_eq (by decide) (by decide)

lemma a_4 : a 4 = 5 := nth_eq (by decide) (by decide)

lemma a_5 : a 5 = 6 := nth_eq (by decide) (by decide)

end OMA.A276706

open OMA.A276706 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a276706.main) := by
  rintro ⟨h, -, -⟩
  have h5 := h 5 (by norm_num)
  rw [show (5 : ℕ) - 1 = 4 from rfl, show (5 : ℕ) - 2 = 3 from rfl, show (5 : ℕ) - 3 = 2 from rfl,
    a_5, a_4, a_3, a_2] at h5
  norm_num at h5
