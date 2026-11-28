import OMAStatements.S_oeis_a249264
import Mathlib

-- Disproof of the A249264 conjecture. Heptagonal H(221) = 221 * 551 = 121771 = 493 * 494 / 2 = triangular T(493).
-- The conjecture gives a(441) = H(221) and a(986) = T(493), so a(441) = a(986); but the terms are distinct.
-- Distinctness: at every step the admissible set is nonempty (m = n * T(2S+1) - S exceeds every earlier term,
-- each of which is at most the sum S), so its infimum a(n) is admissible, hence not among the earlier terms.

namespace OMA.A249264Proof

open OMA.S_oeis_a249264

/-- Some admissible term exists after any prefix: `m = n * T(2S+1) - S` with `S` the sum of the prefix. -/
theorem adm_nonempty (n : ℕ) (hn : 1 ≤ n) (l : List ℕ) :
    ∃ m : ℕ, m ∉ l ∧ ∃ k : ℕ, l.sum + m = n * (k * (k + 1) / 2) := by
  have h2 : (2 * l.sum + 1) * 2 ≤ (2 * l.sum + 1) * (2 * l.sum + 1 + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hk : 2 * l.sum + 1 ≤ (2 * l.sum + 1) * (2 * l.sum + 1 + 1) / 2 := by omega
  have hn' : (2 * l.sum + 1) * (2 * l.sum + 1 + 1) / 2 ≤
      n * ((2 * l.sum + 1) * (2 * l.sum + 1 + 1) / 2) :=
    Nat.le_mul_of_pos_left _ hn
  refine ⟨n * ((2 * l.sum + 1) * (2 * l.sum + 1 + 1) / 2) - l.sum, ?_, 2 * l.sum + 1, by omega⟩
  intro hmem
  have := List.le_sum_of_mem hmem
  omega

/-- The chosen term is admissible, so it is not among the earlier terms. -/
theorem next_not_mem (n : ℕ) (hn : 1 ≤ n) (l : List ℕ) : next n l ∉ l := by
  obtain ⟨m, hm⟩ := adm_nonempty n hn l
  have hmem := Nat.sInf_mem (s := {m : ℕ | m ∉ l ∧ ∃ k : ℕ, l.sum + m = n * (k * (k + 1) / 2)}) ⟨m, hm⟩
  exact hmem.1

theorem pre_succ (n : ℕ) : pre (n + 1) = pre n ++ [a (n + 1)] := by
  simp only [pre, a, Nat.add_sub_cancel]

/-- `a i` is among the first `n` terms for `1 ≤ i ≤ n`. -/
theorem mem_pre (i n : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) : a i ∈ pre n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [pre_succ]
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact List.mem_append_left _ (ih (by omega))
    · have hi' : i = n + 1 := by omega
      subst hi'
      exact List.mem_append_right _ (List.mem_singleton_self _)

/-- `a j` is not among the first `j - 1` terms. -/
theorem a_not_mem (j : ℕ) (hj : 1 ≤ j) : a j ∉ pre (j - 1) :=
  next_not_mem j hj (pre (j - 1))

/-- The terms are distinct. -/
theorem a_ne (i j : ℕ) (hi : 1 ≤ i) (hij : i < j) : a i ≠ a j := by
  intro h
  have h1 := mem_pre i (j - 1) hi (by omega)
  rw [h] at h1
  exact a_not_mem j (by omega) h1

end OMA.A249264Proof

/-- The conjecture fails: it gives `a(441) = 221 * 551 = 121771` and `a(986) = 493 * 494 / 2 = 121771`, two equal
terms at different indices. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a249264.main) := by
  intro h
  have h1 : OMA.S_oeis_a249264.a 441 = 121771 := by
    simpa using (h 221 (by norm_num)).1
  have h2 : OMA.S_oeis_a249264.a 986 = 121771 := by
    simpa using (h 493 (by norm_num)).2
  exact OMA.A249264Proof.a_ne 441 986 (by norm_num) (by norm_num) (h1.trans h2.symm)
