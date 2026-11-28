import OMAStatements.S_oeis_a225004
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a225004.main := by
  intro n hn m hm
  obtain ⟨⟨k, rfl⟩, hmpos, hcard⟩ := hm.1
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hmpos
  have hn0 : n ≠ 0 := by omega
  suffices hkn : k ∣ n by
    rw [sq]; exact Nat.mul_dvd_mul_left n hkn
  by_contra hkn
  rw [← Nat.factorization_prime_le_iff_dvd hk0 hn0] at hkn
  rw [not_forall] at hkn
  obtain ⟨p, hp'⟩ := hkn
  rw [Classical.not_imp, not_le] at hp'
  obtain ⟨hp, hlt⟩ := hp'
  have hpk : p ^ (n.factorization p + 1) ∣ k :=
    (hp.pow_dvd_iff_le_factorization hk0).mpr (Nat.succ_le_of_lt hlt)
  have hpn : ¬ p ^ (n.factorization p + 1) ∣ n := by
    rw [hp.pow_dvd_iff_le_factorization hn0]; omega
  have hsub : n.divisors ∪ n.divisors.image (fun d => d * p ^ (n.factorization p + 1)) ⊆
      (n * k).divisors := by
    intro d hd
    rw [Finset.mem_union, Finset.mem_image] at hd
    rw [Nat.mem_divisors]
    refine ⟨?_, Nat.mul_ne_zero hn0 hk0⟩
    rcases hd with hd | ⟨d', hd', rfl⟩
    · exact Dvd.dvd.mul_right (Nat.dvd_of_mem_divisors hd) k
    · exact Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hd') hpk
  have hdisj : Disjoint n.divisors
      (n.divisors.image (fun d => d * p ^ (n.factorization p + 1))) := by
    rw [Finset.disjoint_left]
    intro d hd hd2
    rw [Finset.mem_image] at hd2
    obtain ⟨d', -, rfl⟩ := hd2
    exact hpn (Dvd.dvd.trans (Dvd.intro_left d' rfl) (Nat.dvd_of_mem_divisors hd))
  have hinj : Function.Injective (fun d : ℕ => d * p ^ (n.factorization p + 1)) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) hxy
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj] at hc
  omega
