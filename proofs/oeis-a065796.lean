import OMAStatements.S_oeis_a065796
import Mathlib
import Mathlib.Data.ZMod.Basic

open OMA.S_oeis_a065796 in
theorem OMA.solution : type_of% @OMA.S_oeis_a065796.main := by
  have h (l : List ℕ) : (11 : ℤ) ∣ ((Nat.ofDigits 10 l : ℕ) : ℤ) - alternatingSum l := by
    induction l with
    | nil => simp [alternatingSum]
    | cons d ds ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨Nat.ofDigits 10 ds - c, ?_⟩
      rw [Nat.ofDigits_cons, alternatingSum]
      push_cast at hc ⊢
      linarith
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => 11 * (t : ℤ) + 2)
    (fun s t e => by simp at e; omega) fun t n _ hz => ?_
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 11).2 (h (Nat.digits 10 (n ^ 2)))
  rw [Nat.ofDigits_digits, show alternatingSum (Nat.digits 10 (n ^ 2)) = 11 * t + 2 from hz] at this
  push_cast at this
  revert this
  generalize (n : ZMod 11) = x
  generalize (t : ZMod 11) = y
  revert x y
  decide
