import OMAStatements.S_oeis_a347365
import Mathlib

/-!
# OEIS A347365: `a(n) = n (2 - (-1)^n)` at `n ≡ 1, 5 (mod 6)`

For odd `m` we have `(-1)^m = -1`, so `a(m) = 3m` and `a(m)/3 = m`. Both `6n + 1` and `6n + 5`
are odd.
-/

open OMA.S_oeis_a347365

namespace OMA.A347365

/-- `a(m) = 3m` for odd `m`. -/
lemma a_odd {m : ℕ} (hm : Odd m) : a m = 3 * (m : ℤ) := by
  unfold a
  rw [hm.neg_one_pow]
  ring

end OMA.A347365

open OMA.A347365 in
theorem OMA.solution : type_of% @OMA.S_oeis_a347365.main := by
  intro n
  constructor
  · rw [a_odd ⟨3 * n, by ring⟩]
    push_cast
    omega
  · rw [a_odd ⟨3 * n + 2, by ring⟩]
    push_cast
    omega
