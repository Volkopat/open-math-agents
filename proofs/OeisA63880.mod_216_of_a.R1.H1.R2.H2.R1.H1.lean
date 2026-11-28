import OMAReductions.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1

/-! Removing prime factors of exponent one preserves the ratio of divisor sums. -/

namespace OMA
open OeisA63880

private theorem staged_a63880_powerful_core : R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1.H1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hodd hA
      by_cases hpower : ∀ q : ℕ, q.Prime → q ∣ n → 2 ≤ n.factorization q
      · exact ⟨n, dvd_rfl, hodd, hA, hpower, fun _ _ hd h => (h hd).elim⟩
      push Not at hpower
      obtain ⟨p, hp, hpn, hval⟩ := hpower
      have hn : 0 < n := hA.1
      have h1 : n.factorization p = 1 := by
        have hpval := (hp.dvd_iff_one_le_factorization hn.ne').mp hpn
        omega
      let m := n / p
      have hnm : n = m * p := (Nat.div_mul_cancel hpn).symm
      have hm : 0 < m := by
        have hprod : 0 < m * p := hnm ▸ hn
        exact Nat.pos_of_mul_pos_right hprod
      have hlt : m < n := by
        have hp1 := hp.one_lt
        nlinarith
      have hmn : m ∣ n := ⟨p, hnm⟩
      have hmp : ¬ p ∣ m := by
        intro hd
        have hpp : p ^ 2 ∣ n := by
          rw [hnm, pow_two]
          exact Nat.mul_dvd_mul_right hd p
        have := (hp.pow_dvd_iff_le_factorization hn.ne').mp hpp
        omega
      have hAm : A m := A_of_mul_prime hm (hnm ▸ hA) hp hmp
      obtain ⟨d, hdm, hod, hAd, hdp, hdrem⟩ := ih m hlt (hodd.of_dvd_nat hmn) hAm
      refine ⟨d, hdm.trans hmn, hod, hAd, hdp, ?_⟩
      intro q hq hqn hqn_d
      by_cases hqp : q = p
      · simpa [hqp] using h1
      · have hpq : ¬ q ∣ p := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h)
        rw [hnm] at hqn
        have hqm := (hq.dvd_mul.mp hqn).resolve_right hpq
        have hq1 := hdrem q hq hqm hqn_d
        rw [hnm, Nat.factorization_mul hm.ne' hp.ne_zero, Finsupp.add_apply, hp.factorization,
          Finsupp.single_eq_of_ne hqp, add_zero, hq1]

end OMA

theorem OMA.solution : OMA.R_OeisA63880_mod_216_of_a_R1_H1_R2_H2_R1.H1 := OMA.staged_a63880_powerful_core