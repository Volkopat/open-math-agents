import OMAReductions.R_Erdos240_erdos_240_variants_tijdeman_finite_R1
import Mathlib

/-! Elementary structure of the enumeration of P-smooth numbers.

The set of P-smooth numbers contains every power of a prime of P, so it is infinite; hence
its enumeration by Nat.nth is strictly increasing and takes values in the set. For p in P,
the number p times a P i is again P-smooth and larger than a P i, so it is enumerated at an
index larger than i, which bounds a P (i + 1).
-/

theorem OMA.solution : OMA.R_Erdos240_erdos_240_variants_tijdeman_finite_R1.H2 := by
  classical
  intro P _ ⟨q, hq⟩ hprime
  have hqp := hprime hq
  have hinf : (Set.ofPred (· ∈ Erdos675.composedOf P)).Infinite := by
    refine Set.infinite_of_injective_forall_mem (Nat.pow_right_injective hqp.two_le) fun k => ?_
    refine ⟨pow_pos hqp.pos k, fun r hr hd => ?_⟩
    rwa [(Nat.prime_dvd_prime_iff_eq hr hqp).1 (hr.dvd_of_dvd_pow hd)]
  have hmono := Nat.nth_strictMono hinf
  have hmem (i : ℕ) : Erdos240.a P i ∈ Erdos675.composedOf P := Nat.nth_mem_of_infinite hinf i
  refine ⟨hmono, hmem, fun p hp i => ?_⟩
  have hpp := hprime hp
  have hpm : p * Erdos240.a P i ∈ Erdos675.composedOf P := by
    refine ⟨mul_pos hpp.pos (hmem i).1, fun r hr hd => ?_⟩
    rcases hr.dvd_mul.mp hd with hd | hd
    · rwa [(Nat.prime_dvd_prime_iff_eq hr hpp).1 hd]
    · exact (hmem i).2 r hr hd
  have hcount := Nat.nth_count (p := (· ∈ Erdos675.composedOf P)) hpm
  have hlt : Erdos240.a P i < p * Erdos240.a P i :=
    lt_mul_of_one_lt_left (hmem i).1 hpp.one_lt
  rw [← hcount] at hlt ⊢
  exact hmono.monotone (Nat.succ_le_of_lt (hmono.lt_iff_lt.mp hlt))
