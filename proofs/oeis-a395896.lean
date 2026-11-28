import OMAStatements.S_oeis_a395896
import Mathlib

open OMA.S_oeis_a395896

private theorem odd_squarefreeTerm {n : ℕ} (hn : Even n) :
    Odd (squarefreeTerm n) := by
  obtain ⟨j, hj⟩ := hn
  rw [show n = 2 * j by omega, squarefreeTerm, Nat.bitIndices_two_mul]
  apply Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one
  intro i hi
  obtain ⟨t, _, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hi)
  exact (Nat.prime_nth_prime (t + 1)).odd_of_ne_two
    (by have h := Nat.add_two_le_nth_prime (t + 1); omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a395896.main := by
  intro n hn
  have ho := odd_squarefreeTerm hn
  have hmod := Nat.odd_iff.1 ho
  have hne : squarefreeTerm n ≠ 0 := by omega
  have hnot : 2 ∉ (squarefreeTerm n).primeFactors := by
    intro h
    have hd := (Nat.mem_primeFactors.1 h).2.1
    omega
  unfold a
  apply Finset.card_eq_zero.2
  apply Finset.eq_empty_iff_forall_notMem.2
  intro k hk
  obtain ⟨hi, hfirst, hnext⟩ := Finset.mem_filter.1 hk
  have hpos : 1 ≤ k := (Finset.mem_Ico.1 hi).1
  apply hnot
  by_cases hd : 2 ∣ k
  · exact (Nat.radical_dvd_iff hne).1 hfirst (Nat.mem_primeFactors.2
      ⟨Nat.prime_two, hd, by omega⟩)
  · exact (Nat.radical_dvd_iff hne).1 hnext (Nat.mem_primeFactors.2
      ⟨Nat.prime_two, by omega, by omega⟩)
