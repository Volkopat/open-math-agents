import OMAStatements.S_oeis_a115026
import Mathlib

/-!
# A115026: the bound `a n ≤ 370` is false

The map `f` sends a number to the sum of the `L`-th powers of its digits, `L` being the number
of digits.  The number `1634 = 1⁴ + 6⁴ + 3⁴ + 4⁴` is a fixed point of `f`, so its whole orbit
is `{1634}`, the only periodic point reached from it is `1634`, and `a 1634 = 1634 > 370`.
-/

namespace OMA.S_oeis_a115026

/-- `1634` is a fixed point (a four-digit narcissistic number). -/
lemma f_fixed : f 1634 = 1634 := by
  unfold f
  norm_num

end OMA.S_oeis_a115026

open OMA.S_oeis_a115026 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a115026.main) := by
  intro h
  have hle := h 1634 (by norm_num)
  -- the defining set contains `1634`, so its infimum is attained
  have hne : ({m : ℕ | (∃ k : ℕ, f^[k] 1634 = m) ∧ m ∈ Function.periodicPts f}).Nonempty :=
    ⟨1634, ⟨0, rfl⟩, Function.mk_mem_periodicPts (by norm_num : 0 < 1)
      (Function.IsFixedPt.isPeriodicPt f_fixed 1)⟩
  obtain ⟨⟨k, hk⟩, -⟩ := Nat.sInf_mem hne
  -- every iterate of the fixed point is the fixed point itself
  have hiter : f^[k] 1634 = 1634 := Function.iterate_fixed f_fixed k
  have ha : a 1634 = 1634 := by
    unfold a
    rw [← hk, hiter]
  omega
