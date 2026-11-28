import OMAStatements.S_oeis_a382946
import Mathlib

open OMA.S_oeis_a382946

theorem OMA.solution : type_of% @OMA.S_oeis_a382946.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  set L : List ℕ := [1, 0, m + 1, m + 2] with hL
  have hk : Nat.digits (m + 3) (Nat.ofDigits (m + 3) L) = L := by
    apply Nat.digits_ofDigits _ (by omega)
    · intro x hx
      simp only [hL, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · intro _
      simp [hL]
  have hd : Nat.digits (m + 3) (Nat.ofDigits (m + 3) L.reverse) = L.reverse := by
    apply Nat.digits_ofDigits _ (by omega)
    · intro x hx
      simp only [hL, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      omega
    · intro _
      simp [hL]
  have ek : Nat.ofDigits (m + 3) L = (m + 2) * Nat.ofDigits (m + 3) L.reverse := by
    simp only [hL, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil]
    push_cast
    ring
  have dpos : 0 < Nat.ofDigits (m + 3) L.reverse := by
    simp only [hL, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      Nat.ofDigits_cons, Nat.ofDigits_nil]
    push_cast
    positivity
  have mem : Nat.ofDigits (m + 3) L ∈ {k : ℕ | ∃ d, P (m + 3) k d} := by
    refine ⟨Nat.ofDigits (m + 3) L.reverse, ⟨m + 2, by rw [ek]; ring⟩, ?_, ?_⟩
    · rw [ek]; nlinarith
    · rw [hk, hd]; exact (List.reverse_perm L).symm
  have hne : ({k : ℕ | ∃ d, P (m + 3) k d}).Nonempty := ⟨_, mem⟩
  obtain ⟨d, hd1, hd2, _⟩ := Nat.sInf_mem hne
  unfold a_val
  omega
