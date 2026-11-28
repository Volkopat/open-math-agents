import Mathlib

/-!
# Is every powerful number the sum of a powerful number and a prime?

Source: https://mathoverflow.net/questions/269080 (CC BY-SA 4.0).

A positive integer `n` is powerful if `p² ∣ n` for every prime `p ∣ n`; in particular `1` is
powerful. Conjecture: every powerful `n > 1` can be written as `n = m + p` with `m` a powerful
(positive) integer and `p` a prime.
-/

namespace OMA.S_mo_269080

/-- `n` is a powerful positive integer. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

theorem main : ∀ n : ℕ, 1 < n → Powerful n →
    ∃ m p : ℕ, Powerful m ∧ p.Prime ∧ n = m + p := by
  sorry

end OMA.S_mo_269080
