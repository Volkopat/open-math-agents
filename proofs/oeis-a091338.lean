import OMAStatements.S_oeis_a091338
import Mathlib

/-!
The last clause fails at n = 0: a(16) = (3/2)^4 = 1 while -a(4) = -(3/2)^2 = -1.
-/

namespace R091338
open OMA.S_oeis_a091338

theorem k_succ (n : ℕ) : kronecker 3 (n + 1) =
    if (n + 1) % 2 = 0 then kron2 3 * kronecker 3 ((n + 1) / 2) else jacobiSym 3 (n + 1) := by
  rw [kronecker]

theorem k_one : kronecker 3 1 = 1 :=
  (k_succ 0).trans (by norm_num [jacobiSym.one_right])

theorem k_even (n : ℕ) : kronecker 3 (2 * n + 2) = -kronecker 3 (n + 1) := by
  have h := k_succ (2 * n + 1)
  rw [if_pos (show (2 * n + 1 + 1) % 2 = 0 by omega),
    show (2 * n + 1 + 1) / 2 = n + 1 by omega] at h
  have h3 : kron2 3 = -1 := by unfold kron2; decide
  rw [h3] at h
  exact h.trans (by ring)

theorem vals : a 16 = 1 ∧ a 4 = 1 := by
  have e0 : kronecker 3 2 = -kronecker 3 1 := k_even 0
  have e1 : kronecker 3 4 = -kronecker 3 2 := k_even 1
  have e3 : kronecker 3 8 = -kronecker 3 4 := k_even 3
  have e7 : kronecker 3 16 = -kronecker 3 8 := k_even 7
  show kronecker 3 16 = 1 ∧ kronecker 3 4 = 1
  rw [e7, e3, e1, e0, k_one]
  norm_num

end R091338

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a091338.main) := by
  intro h
  obtain ⟨-, -, -, -, -, -, -, h8⟩ := h
  have e : OMA.S_oeis_a091338.a 16 = -OMA.S_oeis_a091338.a 4 := h8 0
  rw [R091338.vals.1, R091338.vals.2] at e
  norm_num at e
