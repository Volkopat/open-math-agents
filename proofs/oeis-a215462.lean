import OMAStatements.S_oeis_a215462
import Mathlib

namespace OMA.S_oeis_a215462

lemma notprime3 (b : ℕ) (h3 : 3 ∣ b) (hb : 3 < b) : ¬ b.Prime := by
  intro hp
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3
  omega

end OMA.S_oeis_a215462

theorem OMA.solution : type_of% @OMA.S_oeis_a215462.main := by
  intro n hn
  have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h with h | h | h
  · refine ⟨9, 2 * n - 9, by decide, ?_, by norm_num, ?_, by omega⟩
    · exact ⟨n - 5, by omega⟩
    · exact OMA.S_oeis_a215462.notprime3 _ (by omega) (by omega)
  · refine ⟨35, 2 * n - 35, by decide, ?_, by norm_num, ?_, by omega⟩
    · exact ⟨n - 18, by omega⟩
    · exact OMA.S_oeis_a215462.notprime3 _ (by omega) (by omega)
  · refine ⟨25, 2 * n - 25, by decide, ?_, by norm_num, ?_, by omega⟩
    · exact ⟨n - 13, by omega⟩
    · exact OMA.S_oeis_a215462.notprime3 _ (by omega) (by omega)
