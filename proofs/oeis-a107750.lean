import OMAStatements.S_oeis_a107750
import Mathlib

open OMA.S_oeis_a107750 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a107750.main) := fun h => by
  have s (n u v) (e : a n = u) (H : u < v ∧ zeros v ≠ zeros u ∧ ∀ m < v, u < m → zeros m = zeros u) :
      a (n + 1) = v := by
    subst e; exact le_antisymm (Nat.sInf_le ⟨H.1, H.2.1⟩) (le_csInf ⟨v, H.1, H.2.1⟩ fun m h =>
      not_lt.1 fun l => h.2 (H.2.2 m l h.1))
  have a2 := s 1 1 2 (s 0 0 1 rfl (by decide)) (by decide)
  have a3 := s 2 2 3 a2 (by decide)
  have a5 := s 4 4 5 (s 3 3 4 a3 (by decide)) (by decide)
  have := h.2 6 (by norm_num)
  norm_num [s 5 5 7 a5 (by decide), a5, a3, a2] at this
