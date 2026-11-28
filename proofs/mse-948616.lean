import OMAStatements.S_mse_948616
import Mathlib
open OMA.S_mse_948616

theorem OMA.mse948616.prime_step (q k : ℕ) (hq : q.Prime) (hk : q - 1 ∣ k) (a : ℤ) :
    (q : ℤ) ∣ a ^ (k + 1) - a := by
  have := Fact.mk hq
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  obtain ⟨j, rfl⟩ := hk
  by_cases ha : (a : ZMod q) = 0
  · rw [ha]; simp
  · rw [pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one ha]; simp

theorem OMA.mse948616.sqf_step (n k : ℕ) (hn : Squarefree n) (hk : ∀ q, q.Prime → q ∣ n → q - 1 ∣ k)
    (a : ℤ) : a ^ (k + 1) ≡ a [ZMOD n] := by
  apply Int.ModEq.symm
  apply Int.modEq_of_dvd
  rw [← Nat.prod_primeFactors_of_squarefree hn, Int.natCast_dvd]
  apply Finset.prod_primes_dvd
  · intro q hq; exact (Nat.prime_of_mem_primeFactors hq).prime
  · intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    rw [← Int.natCast_dvd]
    exact prime_step q k hqp (hk q hqp (Nat.dvd_of_mem_primeFactors hq)) a

theorem OMA.mse948616.part2 (d : ℕ) (hs : ¬ Squarefree (d + 1)) (n : ℕ) (hdn : d + 1 ∣ n)
    (hne : n ≠ d + 1) : ¬ Valid d n := by
  rintro ⟨hle, hv⟩
  rw [Nat.squarefree_iff_prime_squarefree] at hs
  push Not at hs
  obtain ⟨p, hp, hpp⟩ := hs
  have hp2 := hp.two_le
  obtain ⟨c, rfl⟩ := hdn
  have hc : 2 ≤ c := by
    rcases c with _ | _ | c
    · simp at hle
    · simp at hne
    · omega
  have hexp : 2 ≤ (d + 1) * c - d := by
    have := Nat.mul_le_mul_left (d + 1) hc
    omega
  have h1 := (hv (p : ℤ)).symm.dvd
  have h2 : ((p * p : ℕ) : ℤ) ∣ (((d + 1) * c : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left hpp c)
  have h3 : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) ^ ((d + 1) * c - d) := by
    push_cast
    rw [← pow_two]
    exact pow_dvd_pow _ hexp
  have h4 : ((p * p : ℕ) : ℤ) ∣ (p : ℤ) := by
    have := dvd_sub h3 (h2.trans h1)
    rwa [sub_sub_cancel] at this
  have h5 := Nat.le_of_dvd hp.pos (Int.natCast_dvd_natCast.mp h4)
  nlinarith

theorem OMA.mse948616.part1 (d : ℕ) (hs : Squarefree (d + 1)) :
    {p : ℕ | p.Prime ∧ Valid d (p * (d + 1))}.Infinite := by
  have hm : (d + 1).factorial ≠ 0 := Nat.factorial_ne_zero _
  refine (Nat.infinite_setOfPred_prime_and_modEq hm (Nat.coprime_one_left _)).mono ?_
  rintro p ⟨hp, hpm⟩
  have hp1 := hp.one_le
  have hdvd : (d + 1).factorial ∣ p - 1 :=
    (Nat.modEq_iff_dvd' hp1).mp hpm.symm
  have hcop : ¬ p ∣ d + 1 := by
    intro h
    have h1 : p ∣ (d + 1).factorial := Nat.dvd_factorial hp.pos (Nat.le_of_dvd (by omega) h)
    have h2 : p ∣ p - 1 := h1.trans hdvd
    have h3 : p ∣ p - (p - 1) := Nat.dvd_sub (dvd_refl p) h2
    rw [show p - (p - 1) = 1 by omega] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  refine ⟨hp, ?_, ?_⟩
  · nlinarith
  · intro a
    have hsq : Squarefree (p * (d + 1)) := by
      rw [Nat.squarefree_mul_iff]
      exact ⟨(Nat.Prime.coprime_iff_not_dvd hp).mpr hcop,
        hp.squarefree, hs⟩
    have hexp : p * (d + 1) - d = (d + 1) * (p - 1) + 1 := by
      rcases p with _ | p
      · omega
      · simp only [Nat.add_sub_cancel]; ring_nf; omega
    rw [hexp]
    apply sqf_step _ _ hsq
    intro q hq hqn
    rcases (Nat.Prime.dvd_mul hq).mp hqn with h | h
    · rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]
      exact dvd_mul_left _ _
    · have : q - 1 ∣ (d + 1).factorial :=
        Nat.dvd_factorial (by have := hq.two_le; omega)
          (by have := Nat.le_of_dvd (by omega) h; omega)
      exact (this.trans hdvd).mul_left _

theorem OMA.solution : type_of% @OMA.S_mse_948616.main :=
  fun d => ⟨OMA.mse948616.part1 d, OMA.mse948616.part2 d⟩
