import OMAReductions.R_Erdos398_erdos_398_R1
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Ring.Parity

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1.H2 := fun n hn => by
  simp only [eq_comm (a := n.factorial + 1), Nat.exists_mul_self', Set.mem_insert_iff,
    Set.mem_singleton_iff]
  exact (by decide +kernel : ∀ j : Fin 128, (j.val.factorial + 1).sqrt ^ 2 = j.val.factorial + 1 ↔
    j.val = 4 ∨ j.val = 5 ∨ j.val = 7) ⟨n, hn⟩
