import OMAStatements.S_oeis_a066223
import Mathlib

namespace A066223Proof
open OMA.S_oeis_a066223

lemma t_rec (k : ℕ) : t (k + 2) = t (k + 1) + ((k : ℤ) + 1) * t k := by
  rw [t]

end A066223Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a066223.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  unfold OMA.S_oeis_a066223.a
  have f1 : 2 * (m + 2) = 2 * m + 2 + 2 := by ring
  have f2 : 2 * (m + 1) = 2 * m + 2 := by ring
  have f3 : 2 * m + 2 + 1 = 2 * m + 1 + 2 := by ring
  have f4 : 2 * m + 1 + 1 = 2 * m + 2 := by ring
  rw [f1, f2, A066223Proof.t_rec (2 * m + 2), f3, A066223Proof.t_rec (2 * m + 1), f4]
  have h2 := A066223Proof.t_rec (2 * m)
  push_cast at h2 ⊢
  linear_combination (-(2 * (m : ℤ) + 2)) * h2
