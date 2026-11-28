import OMAStatements.S_oeis_a155151
import Mathlib

open OMA.S_oeis_a155151

theorem OMA.solution : type_of% @OMA.S_oeis_a155151.main := by
  intro p _ h
  obtain ⟨n, k, hk, hkn, he⟩ := h
  have ht : T n k = (2*n+1)*(2*k+1)+1 := by
    unfold T
    ring
  rw [← he, ht, Nat.add_sub_cancel]
  exact Nat.not_prime_mul (by omega) (by omega)