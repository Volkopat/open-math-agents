import OMAStatements.S_oeis_a394454
import Mathlib

open OMA.S_oeis_a394454

theorem OMA.solution : type_of% @OMA.S_oeis_a394454.main := by
  have infinite_indices (p : ℕ) (hp : p.Prime) :
      {n : ℕ | 1 ≤ n ∧ p ∣ n.centralBinom}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro B
    have hmul := Nat.mul_le_mul_right (B + 1) hp.two_le
    have hd : p ∣ (p * (B + 1) - 1).succ := by
      convert Nat.dvd_mul_right p (B + 1) using 1
      omega
    exact ⟨_, ⟨by omega, hd.trans (Nat.succ_dvd_centralBinom _)⟩, by omega⟩
  refine ⟨infinite_indices, ?_⟩
  intro B N
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 1)
  obtain ⟨n, ⟨_, hdiv⟩, hn⟩ := (infinite_indices p hp).exists_gt N
  refine ⟨n, hn, lt_of_lt_of_le (show B < p by omega) ?_⟩
  exact Finset.single_le_sum (f := id) (fun _ _ => Nat.zero_le _)
    (hp.mem_primeFactors hdiv (Nat.centralBinom_pos n).ne')
