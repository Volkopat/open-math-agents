import OMAReductions.R_mo_499750_R1

/-! For odd `n = k + 1` and a prime `p ∣ n` (necessarily odd) we have
`k % p = p - 1` and `k / p = n / p - 1`. The failure of the digit test at `p`
therefore forces `p ∣ n / p - 1`. This rules out `p ^ 2 ∣ n`, so `n` is squarefree.
Modulo each prime factor `q`, every cofactor `n / p` with `p ≠ q` vanishes while
`n / q ≡ 1`, so `q ∣ ∑ n / p - 1`; squarefreeness lifts this to the Giuga
congruence modulo `n`. -/

namespace OMA.Mo499750H1

lemma key {k p : ℕ} (ho : Odd (k + 1))
    (noPrime : ¬ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k % p + k / p % p)
    (hp : p.Prime) (hpn : p ∣ k + 1) : p ∣ (k + 1) / p - 1 := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨c, hc⟩ := hpn
    have := Nat.odd_iff.mp ho
    omega
  have hle : ¬ p ≤ k % p + k / p % p := fun h => noPrime ⟨p, hp, hp2, h⟩
  have hp1 : 1 ≤ p := hp.one_lt.le
  obtain ⟨m, hm⟩ := hpn
  rcases m with _ | m
  · omega
  have hk : k = (p - 1) + p * m := by
    have h' : k + 1 = p * m + p := by rw [hm]; ring
    generalize p * m = t at h' ⊢
    omega
  have hmod : k % p = p - 1 := by
    rw [hk, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hdiv : k / p = m := by
    rw [hk, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt (by omega), zero_add]
  have hnp : (k + 1) / p = m + 1 := by
    rw [hm, Nat.mul_div_cancel_left _ hp.pos]
  rw [hnp, Nat.add_sub_cancel]
  rw [hmod, hdiv] at hle
  apply Nat.dvd_of_mod_eq_zero
  generalize m % p = r at hle ⊢
  omega

lemma sqf {n : ℕ} (hn0 : n ≠ 0) (h : ∀ p ∈ n.primeFactors, p ∣ n / p - 1) :
    Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
  have hdvd1 : p ∣ n / p - 1 := h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn0⟩)
  rcases hpp with ⟨c, hc⟩
  have hdiv : n / p = p * c := by
    rw [hc, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have hdvd2 : p ∣ n / p := ⟨c, hdiv⟩
  have hge1 : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn) hp.pos
  have h1 : p ∣ 1 := by
    have hadd : n / p - 1 + 1 = n / p := Nat.sub_add_cancel hge1
    exact (Nat.dvd_add_right hdvd1).mp (hadd.symm ▸ hdvd2)
  exact hp.not_dvd_one h1

theorem H1_proof : OMA.R_mo_499750_R1.H1 := by
  intro k hk ho noPrime
  have hn0 : k + 1 ≠ 0 := by omega
  have hall : ∀ p ∈ (k + 1).primeFactors, p ∣ (k + 1) / p - 1 := fun p hp =>
    key ho noPrime (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hsq : Squarefree (k + 1) := sqf hn0 hall
  refine ⟨hsq, ?_⟩
  have hne : (k + 1).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hpos : ∀ p ∈ (k + 1).primeFactors, 1 ≤ (k + 1) / p := fun p hp =>
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp))
      (Nat.prime_of_mem_primeFactors hp).pos
  have hS1 : 1 ≤ ∑ p ∈ (k + 1).primeFactors, (k + 1) / p := by
    obtain ⟨q, hq⟩ := hne
    exact (hpos q hq).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hq)
  have hdvd : ∀ q ∈ (k + 1).primeFactors,
      q ∣ (∑ p ∈ (k + 1).primeFactors, (k + 1) / p) - 1 := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hqn := Nat.dvd_of_mem_primeFactors hq
    have hT : q ∣ ∑ p ∈ (k + 1).primeFactors.erase q, (k + 1) / p := by
      apply Finset.dvd_sum
      intro p hp
      have hpq : p ≠ q := Finset.ne_of_mem_erase hp
      have hp' := Finset.mem_of_mem_erase hp
      have hpp := Nat.prime_of_mem_primeFactors hp'
      have hcop : Nat.Coprime q p := (Nat.coprime_primes hqp hpp).mpr (Ne.symm hpq)
      apply hcop.dvd_of_dvd_mul_left
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp')]
      exact hqn
    have hsplit : (k + 1) / q + ∑ p ∈ (k + 1).primeFactors.erase q, (k + 1) / p =
        ∑ p ∈ (k + 1).primeFactors, (k + 1) / p :=
      Finset.add_sum_erase _ _ hq
    have h1 := hpos q hq
    have heq : (∑ p ∈ (k + 1).primeFactors, (k + 1) / p) - 1 =
        ((k + 1) / q - 1) + ∑ p ∈ (k + 1).primeFactors.erase q, (k + 1) / p := by
      rw [← hsplit]
      generalize (k + 1) / q = a at h1 ⊢
      generalize ∑ p ∈ (k + 1).primeFactors.erase q, (k + 1) / p = T
      omega
    rw [heq]
    exact dvd_add (hall q hq) hT
  have hn_dvd : (k + 1) ∣ (∑ p ∈ (k + 1).primeFactors, (k + 1) / p) - 1 := by
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have := Finset.prod_primes_dvd ((∑ p ∈ (k + 1).primeFactors, (k + 1) / p) - 1)
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hdvd
    rwa [hprod] at this
  exact ((Nat.modEq_iff_dvd' hS1).mpr hn_dvd).symm

end OMA.Mo499750H1

theorem OMA.solution : OMA.R_mo_499750_R1.H1 := OMA.Mo499750H1.H1_proof
