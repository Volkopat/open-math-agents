import OMAStatements.S_oeis_a129150
import Mathlib

-- Problem: A129150: The n-th arithmetic derivative of 2^3.
-- Upstream: formal-conjectures statements/oeis-a129150.lean:0 (declaration OMA.S_oeis_a129150.main)
-- Credit: @npnelson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

-- Proof. If 4 | n and n >= 8 then n' > n and 4 | n'. Write n = 4 m and v for the exponent of 2
-- in n. The prime 2 contributes (n / 2) v >= n to n', and every odd prime p | n contributes a
-- multiple of 4, since 4 p | n. If v >= 3 the contribution of 2 already exceeds n and is a
-- multiple of 4; if v = 2 it equals n, and m is odd with m >= 2, so an odd prime contributes
-- something positive. Starting from 8, every term is therefore a multiple of 4 that is at
-- least 8, and the sequence is strictly increasing.

namespace ArithDeriv129150Proof
open OMA.S_oeis_a129150

lemma step {n : ℕ} (h4 : 4 ∣ n) (h8 : 8 ≤ n) : n < arithDeriv n ∧ 4 ∣ arithDeriv n := by
  have hn0 : n ≠ 0 := by omega
  have h2mem : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, dvd_trans (by norm_num) h4, hn0⟩
  have hv : 2 ≤ n.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp (by simpa using h4)
  obtain ⟨m, hm⟩ := h4
  have hhalf : n / 2 = 2 * m := by omega
  have hrest_dvd : 4 ∣ ∑ p ∈ n.primeFactors.erase 2, n / p * n.factorization p := by
    apply Finset.dvd_sum
    intro p hp
    obtain ⟨hp2, hpm⟩ := Finset.mem_erase.mp hp
    obtain ⟨hpp, hpn, -⟩ := Nat.mem_primeFactors.mp hpm
    have hcop : Nat.Coprime (2 ^ 2) p :=
      Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hpp).mpr (Ne.symm hp2))
    have h4n : 2 ^ 2 ∣ n := ⟨m, by rw [hm]; norm_num⟩
    obtain ⟨c, hc⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h4n hpn
    have hdiv : n / p = 4 * c := by
      have h' : n = p * (4 * c) := by rw [hc]; ring
      rw [h', Nat.mul_div_cancel_left _ hpp.pos]
    rw [hdiv]
    exact Dvd.dvd.mul_right (Dvd.intro _ rfl) _
  have hsplit : arithDeriv n = n / 2 * n.factorization 2
      + ∑ p ∈ n.primeFactors.erase 2, n / p * n.factorization p := by
    unfold arithDeriv
    exact (Finset.add_sum_erase _ (fun p => n / p * n.factorization p) h2mem).symm
  rw [hsplit, hhalf]
  rcases Nat.lt_or_ge (n.factorization 2) 3 with hlt | hge
  · have hv2 : n.factorization 2 = 2 := by omega
    rw [hv2]
    have hmodd : ¬ 2 ∣ m := by
      intro h2m
      obtain ⟨t, ht⟩ := h2m
      have h8n : 2 ^ 3 ∣ n := ⟨t, by rw [hm, ht]; ring⟩
      have := (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mp h8n
      omega
    have hq : (m.minFac).Prime := Nat.minFac_prime (by omega)
    have hqm : m.minFac ∣ m := Nat.minFac_dvd m
    have hqn : m.minFac ∣ n := dvd_trans hqm ⟨4, by rw [hm]; ring⟩
    have hq2 : m.minFac ≠ 2 := fun h => hmodd (h ▸ hqm)
    have hqmem : m.minFac ∈ n.primeFactors.erase 2 :=
      Finset.mem_erase.mpr ⟨hq2, Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩⟩
    have hpos : 0 < n / m.minFac * n.factorization m.minFac :=
      Nat.mul_pos (Nat.div_pos (Nat.le_of_dvd (by omega) hqn) hq.pos)
        (hq.factorization_pos_of_dvd hn0 hqn)
    have hle : n / m.minFac * n.factorization m.minFac
        ≤ ∑ p ∈ n.primeFactors.erase 2, n / p * n.factorization p :=
      Finset.single_le_sum (f := fun p => n / p * n.factorization p)
        (fun _ _ => Nat.zero_le _) hqmem
    refine ⟨by omega, ?_⟩
    exact (Nat.dvd_add_right (⟨m, by ring⟩ : 4 ∣ 2 * m * 2)).mpr hrest_dvd
  · obtain ⟨t, ht⟩ := (Nat.prime_two.pow_dvd_iff_le_factorization hn0).mpr hge
    have hmt : m = 2 * t := by omega
    refine ⟨?_, ?_⟩
    · have h3 : 2 * m * 3 ≤ 2 * m * n.factorization 2 := Nat.mul_le_mul_left _ hge
      omega
    · refine (Nat.dvd_add_right ?_).mpr hrest_dvd
      rw [hmt]
      exact ⟨t * n.factorization 2, by ring⟩

theorem inv : ∀ n : ℕ, 4 ∣ a n ∧ 8 ≤ a n
  | 0 => ⟨by decide, by decide⟩
  | n + 1 => by
      obtain ⟨h4, h8⟩ := inv n
      obtain ⟨hlt, hd⟩ := step h4 h8
      refine ⟨hd, ?_⟩
      show 8 ≤ arithDeriv (a n)
      omega

end ArithDeriv129150Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a129150.main := by
  intro n
  obtain ⟨h4, h8⟩ := ArithDeriv129150Proof.inv n
  exact (ArithDeriv129150Proof.step h4 h8).1
