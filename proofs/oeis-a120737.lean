import OMAStatements.S_oeis_a120737

namespace OMA.A120737Proof

open UniqueFactorizationMonoid

lemma core (k : ℕ) (hk : k ≠ 0) (h : k.divisors.card ∣ radical k) :
    k.divisors.card = radical k := by
  set P := k.primeFactors with hP
  set e := fun p => k.factorization p + 1 with he
  have hd : k.divisors.card = ∏ p ∈ P, e p := Nat.card_divisors hk
  have hr : radical k = ∏ p ∈ P, p := Nat.radical_eq_prod_primeFactors
  have hsq : Squarefree (radical k) := squarefree_radical
  have hrpos : 0 < radical k := Nat.radical_pos k
  let f := fun p => (e p).minFac
  have he2 : ∀ p ∈ P, e p ≠ 1 := by
    intro p hp
    have : 0 < k.factorization p := Nat.Prime.factorization_pos_of_dvd
      (Nat.prime_of_mem_primeFactors hp) hk (Nat.dvd_of_mem_primeFactors hp)
    simp only [he]
    omega
  have hfprime : ∀ p ∈ P, (f p).Prime := fun p hp => Nat.minFac_prime (he2 p hp)
  have hedvd : ∀ p ∈ P, e p ∣ radical k := by
    intro p hp
    have h1 := Finset.dvd_prod_of_mem e hp
    rw [← hd] at h1
    exact h1.trans h
  have hfP : ∀ p ∈ P, f p ∈ P := by
    intro p hp
    have h1 : f p ∣ radical k := dvd_trans (Nat.minFac_dvd _) (hedvd p hp)
    have h2 : radical k ∣ k := by rw [hr]; exact Nat.prod_primeFactors_dvd k
    exact Nat.mem_primeFactors.mpr ⟨hfprime p hp, dvd_trans h1 h2, hk⟩
  have hinj : Set.InjOn f P := by
    intro p hp q hq hpq
    by_contra hne
    have h1 : e p * e q ∣ ∏ x ∈ P, e x := by
      have : ∏ x ∈ ({p, q} : Finset ℕ), e x = e p * e q := Finset.prod_pair hne
      rw [← this]
      apply Finset.prod_dvd_prod_of_subset
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have h2 : f p * f p ∣ radical k := by
      rw [← hd] at h1
      apply dvd_trans _ (h1.trans h)
      exact mul_dvd_mul (Nat.minFac_dvd _) (hpq ▸ Nat.minFac_dvd _)
    have h3 := hsq (f p) h2
    rw [Nat.isUnit_iff] at h3
    exact (hfprime p hp).one_lt.ne' h3
  have himg : P.image f = P := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨p, hp, rfl⟩ := hx
      exact hfP p hp
    · rw [Finset.card_image_of_injOn hinj]
  have hrf : radical k = ∏ p ∈ P, f p := by
    rw [hr]
    conv_lhs => rw [← himg]
    rw [Finset.prod_image hinj]
  have hle : radical k ≤ k.divisors.card := by
    rw [hrf, hd]
    apply Finset.prod_le_prod'
    intro p hp
    exact Nat.minFac_le (by simp only [he]; omega)
  have hge : k.divisors.card ≤ radical k := Nat.le_of_dvd hrpos h
  omega

end OMA.A120737Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a120737.main := by
  intro k hk h
  rw [OMA.A120737Proof.core k (by omega) h]
  exact Nat.div_self (Nat.radical_pos k)
