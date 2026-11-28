import OMAStatements.S_oeis_a326578
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-! Bernoulli denominators and Carmichael numbers, following @Volkopat (#24453).
The denominator of a reduced fraction is now read directly using Mathlib's
coprime numerator/denominator theorem. The Bernoulli and Korselt arguments
and the exact registered conclusion are retained. -/

namespace OMA.P_oeis_a326578

open OMA.S_oeis_a326578

private lemma rat_den_dvd_iff_exists_int (q : ℚ) {m : ℕ} (_hm : 0 < m) :
    q.den ∣ m ↔ ∃ z : ℤ, (m : ℚ) * q = (z : ℚ) := by
  constructor
  · intro ⟨c, hc⟩
    refine ⟨(c : ℤ) * q.num, ?_⟩
    have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hdq : (q.den : ℚ) * q = (q.num : ℚ) := by
      conv_lhs => rhs; rw [← Rat.num_div_den q]
      field_simp
    calc (m : ℚ) * q = ((q.den * c : ℕ) : ℚ) * q := by rw [hc]
      _ = (c : ℚ) * ((q.den : ℚ) * q) := by push_cast; ring
      _ = (c : ℚ) * (q.num : ℚ) := by rw [hdq]
      _ = (((c : ℤ) * q.num : ℤ) : ℚ) := by push_cast; rfl
  · intro ⟨z, hz⟩
    have hden_ne : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
    have hq : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
    rw [hq] at hz
    have hmulQ : (m : ℚ) * (q.num : ℚ) = (z : ℚ) * (q.den : ℚ) := by
      have := congrArg (· * (q.den : ℚ)) hz
      field_simp at this
      linarith
    have hmulZ : (m : ℤ) * q.num = z * (q.den : ℤ) := by exact_mod_cast hmulQ
    have hdvdZ : (q.den : ℤ) ∣ (m : ℤ) * q.num := ⟨z, by linarith⟩
    have hdvdN : q.den ∣ m * q.num.natAbs := by
      have h := Int.natAbs_dvd_natAbs.mpr hdvdZ
      simpa [Int.natAbs_mul] using h
    exact q.reduced.symm.dvd_of_dvd_mul_right hdvdN

private lemma den_bernoulli_even (k : ℕ) (_hk : 1 ≤ k) :
    (bernoulli (2 * k)).den =
      ∏ p ∈ (Finset.range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k), p := by
  set S := (Finset.range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)
  set P := ∏ p ∈ S, p
  have hP_pos : 0 < P := Finset.prod_pos fun p hp => (Finset.mem_filter.mp hp).2.1.pos
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
  -- Step 1: (bernoulli (2*k)).den ∣ P
  have hdvd1 : (bernoulli (2 * k)).den ∣ P := by
    rw [rat_den_dvd_iff_exists_int _ hP_pos]
    have hsum_int : ∃ s : ℤ, (P : ℚ) * ∑ p ∈ S, (1 : ℚ) / (p : ℚ) = (s : ℚ) := by
      refine ⟨∑ p ∈ S, ((P / p : ℕ) : ℤ), ?_⟩
      rw [Finset.mul_sum]
      simp only [Int.cast_sum, Int.cast_natCast]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
      have hp_dvd : p ∣ P := Finset.dvd_prod_of_mem _ hp
      have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
      have hPm : (p : ℚ) * ((P / p : ℕ) : ℚ) = (P : ℚ) := by exact_mod_cast Nat.mul_div_cancel' hp_dvd
      field_simp
      linarith
    obtain ⟨s, hs⟩ := hsum_int
    refine ⟨(P : ℤ) * z - s, ?_⟩
    have hmul : (P : ℚ) * (bernoulli (2 * k) + ∑ p ∈ S, (1 : ℚ) / (p : ℚ)) = (P : ℚ) * (z : ℚ) := by
      rw [hz]
    rw [mul_add, hs] at hmul
    push_cast
    linarith
  -- Step 2: every p ∈ S divides (bernoulli (2*k)).den
  have hp_dvd_den : ∀ p ∈ S, p ∣ (bernoulli (2 * k)).den := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2.1
    set d := (bernoulli (2 * k)).den
    set P' := ∏ q ∈ S.erase p, q
    have hp_not_P' : ¬ p ∣ P' := by
      intro hdvd
      rw [hp_prime.prime.dvd_finsetProd_iff] at hdvd
      obtain ⟨q, hq, hpq⟩ := hdvd
      have hq_mem : q ∈ S := Finset.mem_of_mem_erase hq
      have hq_ne : q ≠ p := (Finset.mem_erase.mp hq).1
      have hq_prime : q.Prime := (Finset.mem_filter.mp hq_mem).2.1
      exact hq_ne ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hpq).symm
    -- (d * P') * (1 / p) is an integer!
    have hint_inv : ∃ w : ℤ, ((d * P' : ℕ) : ℚ) * ((1 : ℚ) / (p : ℚ)) = (w : ℚ) := by
      have hsplit : ∑ q ∈ S, (1 : ℚ) / (q : ℚ) = (1 : ℚ) / (p : ℚ) + ∑ q ∈ S.erase p, (1 : ℚ) / (q : ℚ) :=
        (Finset.add_sum_erase S (fun q => (1 : ℚ) / (q : ℚ)) hp).symm
      have hb_int : ((d : ℕ) : ℚ) * bernoulli (2 * k) = ((bernoulli (2 * k)).num : ℚ) := by
        have hden : ((bernoulli (2 * k)).den : ℚ) ≠ 0 := by exact_mod_cast (bernoulli (2 * k)).den_nz
        simp only [d]
        conv_lhs => rhs; rw [← Rat.num_div_den (bernoulli (2 * k))]
        field_simp
      have hrest_int : ∃ r : ℤ, (P' : ℚ) * ∑ q ∈ S.erase p, (1 : ℚ) / (q : ℚ) = (r : ℚ) := by
        refine ⟨∑ q ∈ S.erase p, ((P' / q : ℕ) : ℤ), ?_⟩
        rw [Finset.mul_sum]
        simp only [Int.cast_sum, Int.cast_natCast]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq_prime : q.Prime := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hq)).2.1
        have hq_dvd : q ∣ P' := Finset.dvd_prod_of_mem _ hq
        have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq_prime.ne_zero
        have hQm : (q : ℚ) * ((P' / q : ℕ) : ℚ) = (P' : ℚ) := by exact_mod_cast Nat.mul_div_cancel' hq_dvd
        field_simp
        linarith
      obtain ⟨r, hr⟩ := hrest_int
      refine ⟨(d : ℤ) * (P' : ℤ) * z - (P' : ℤ) * (bernoulli (2 * k)).num - (d : ℤ) * r, ?_⟩
      have hmul : ((d * P' : ℕ) : ℚ) * (bernoulli (2 * k) + ∑ q ∈ S, (1 : ℚ) / (q : ℚ)) =
          ((d * P' : ℕ) : ℚ) * (z : ℚ) := by rw [hz]
      rw [hsplit] at hmul
      push_cast at hmul ⊢
      have h1 : (d : ℚ) * (P' : ℚ) * bernoulli (2 * k) = (P' : ℚ) * ((bernoulli (2 * k)).num : ℚ) := by
        calc (d : ℚ) * (P' : ℚ) * bernoulli (2 * k) = (P' : ℚ) * ((d : ℚ) * bernoulli (2 * k)) := by ring
          _ = (P' : ℚ) * ((bernoulli (2 * k)).num : ℚ) := by rw [hb_int]
      have h2 : (d : ℚ) * (P' : ℚ) * ∑ q ∈ S.erase p, (1 : ℚ) / (q : ℚ) = (d : ℚ) * (r : ℚ) := by
        calc (d : ℚ) * (P' : ℚ) * ∑ q ∈ S.erase p, (1 : ℚ) / (q : ℚ)
            = (d : ℚ) * ((P' : ℚ) * ∑ q ∈ S.erase p, (1 : ℚ) / (q : ℚ)) := by ring
          _ = (d : ℚ) * (r : ℚ) := by rw [hr]
      linarith
    obtain ⟨w, hw⟩ := hint_inv
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp_prime.ne_zero
    have heqQ : ((d * P' : ℕ) : ℚ) = (p : ℚ) * (w : ℚ) := by
      have := congrArg (· * (p : ℚ)) hw
      field_simp at this
      linarith
    have heqZ : ((d * P' : ℕ) : ℤ) = (p : ℤ) * w := by exact_mod_cast heqQ
    have hp_dvd_prod : p ∣ d * P' := Int.ofNat_dvd.mp ⟨w, heqZ⟩
    rcases hp_prime.dvd_mul.mp hp_dvd_prod with h | h
    · exact h
    · exact absurd h hp_not_P'
  -- Step 3: P ∣ (bernoulli (2*k)).den since all p ∈ S are distinct primes dividing it
  have hdvd2 : P ∣ (bernoulli (2 * k)).den := by
    have hprod_dvd : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ p ∣ (bernoulli (2 * k)).den) →
        (∏ p ∈ T, p) ∣ (bernoulli (2 * k)).den := by
      intro T
      induction T using Finset.cons_induction with
      | empty => intro _; simp
      | cons a s ha ih =>
        intro hT
        rw [Finset.prod_cons]
        have ha_mem : a ∈ Finset.cons a s ha := Finset.mem_cons_self a s
        have ha_p : a.Prime := (hT a ha_mem).1
        have ha_d : a ∣ (bernoulli (2 * k)).den := (hT a ha_mem).2
        have hs_d : (∏ p ∈ s, p) ∣ (bernoulli (2 * k)).den :=
          ih fun p hp => hT p (Finset.mem_cons_of_mem hp)
        have hcop : Nat.Coprime a (∏ p ∈ s, p) := by
          rw [ha_p.coprime_iff_not_dvd]
          intro hdvd
          rw [ha_p.prime.dvd_finsetProd_iff] at hdvd
          obtain ⟨q, hq, haq⟩ := hdvd
          have hq_p : q.Prime := (hT q (Finset.mem_cons_of_mem hq)).1
          have hqa : a = q := (Nat.prime_dvd_prime_iff_eq ha_p hq_p).mp haq
          exact ha (hqa ▸ hq)
        exact hcop.mul_dvd_of_dvd_of_dvd ha_d hs_d
    exact hprod_dvd S fun p hp => ⟨(Finset.mem_filter.mp hp).2.1, hp_dvd_den p hp⟩
  exact Nat.dvd_antisymm hdvd1 hdvd2

private lemma korselt_iff_carmichael {m : ℕ} (hm2 : 2 ≤ m) (hcomp : ¬ m.Prime) :
    IsCarmichael m ↔ Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p - 1) ∣ (m - 1) := by
  constructor
  · intro ⟨_, _, hferm⟩
    refine ⟨?_, ?_⟩
    · rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpp
      have hcong : p ^ m ≡ p [MOD m] := hferm p
      have hcong2 : p ^ m ≡ p [MOD p * p] := hcong.of_dvd hpp
      have hp_le : p ≤ p ^ m := by
        calc p = p ^ 1 := (pow_one p).symm
          _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos (by omega)
      have hdvd_sub : p * p ∣ p ^ m - p := (Nat.modEq_iff_dvd' hp_le).mp hcong2.symm
      have hdvd_pow : p * p ∣ p ^ m := by
        rw [← sq]
        exact Nat.pow_dvd_pow p hm2
      have h1 : p * p ∣ p := by
        have := Nat.dvd_sub hdvd_pow hdvd_sub
        rwa [Nat.sub_sub_self hp_le] at this
      have hle : p * p ≤ p := Nat.le_of_dvd hp.pos h1
      have := hp.two_le
      nlinarith
    · intro p hp hpm
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
      set a := ((g : ZMod p)).val
      have ha_cast : (a : ZMod p) = (g : ZMod p) := ZMod.natCast_zmod_val _
      have hcong : a ^ m ≡ a [MOD p] := (hferm a).of_dvd hpm
      have hzmod : ((a : ZMod p)) ^ m = (a : ZMod p) := by
        simpa [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff _ _ p).mpr hcong
      rw [ha_cast] at hzmod
      have hunit : g ^ m = g := Units.ext (by simpa using hzmod)
      have hunit1 : g ^ (m - 1) = 1 := by
        have hmul : g ^ (m - 1) * g = 1 * g := by
          rw [← pow_succ, show m - 1 + 1 = m by omega, hunit, one_mul]
        exact mul_right_cancel hmul
      have hord : orderOf g = p - 1 := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hunit1
  · intro ⟨hsf, hkor⟩
    refine ⟨hm2, hcomp, fun a => ?_⟩
    have hm_pos : 0 < m := by omega
    have hprod_eq : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsf
    have ha_le : a ≤ a ^ m := by
      rcases Nat.eq_zero_or_pos a with rfl | ha_pos
      · simp [zero_pow (by omega : m ≠ 0)]
      · calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ m := Nat.pow_le_pow_right ha_pos (by omega)
    have hprime_dvd : ∀ p ∈ m.primeFactors, p ∣ a ^ m - a := by
      intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp_mem
      have hdvd_sub : (p - 1) ∣ (m - 1) := hkor p hp hpm
      rw [← Nat.modEq_iff_dvd' ha_le]
      by_cases hpa : p ∣ a
      · have h1 : a ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpa
        have h2 : a ^ m ≡ 0 [MOD p] := by
          simpa [zero_pow (by omega : m ≠ 0)] using h1.pow m
        exact h1.trans h2.symm
      · have : Fact p.Prime := ⟨hp⟩
        have ha_ne : (a : ZMod p) ≠ 0 := by
          intro h0
          exact hpa ((ZMod.natCast_eq_zero_iff a p).mp h0)
        have hferm_p : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one ha_ne
        obtain ⟨q, hq⟩ := hdvd_sub
        have hm1 : (a : ZMod p) ^ (m - 1) = 1 := by
          rw [hq, pow_mul, hferm_p, one_pow]
        have hm_eq : (a : ZMod p) ^ m = (a : ZMod p) := by
          conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
          rw [hm1, one_mul]
        exact ((ZMod.natCast_eq_natCast_iff a (a ^ m) p).mp (by simpa [Nat.cast_pow] using hm_eq.symm))
    -- Product of distinct primes dividing a^m - a divides a^m - a
    have hprod_dvd : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ p ∣ a ^ m - a) →
        (∏ p ∈ T, p) ∣ a ^ m - a := by
      intro T
      induction T using Finset.cons_induction with
      | empty => intro _; simp
      | cons r s hr ih =>
        intro hT
        rw [Finset.prod_cons]
        have hr_mem : r ∈ Finset.cons r s hr := Finset.mem_cons_self r s
        have hr_p : r.Prime := (hT r hr_mem).1
        have hr_d : r ∣ a ^ m - a := (hT r hr_mem).2
        have hs_d : (∏ p ∈ s, p) ∣ a ^ m - a := ih fun p hp => hT p (Finset.mem_cons_of_mem hp)
        have hcop : Nat.Coprime r (∏ p ∈ s, p) := by
          rw [hr_p.coprime_iff_not_dvd]
          intro hdvd
          rw [hr_p.prime.dvd_finsetProd_iff] at hdvd
          obtain ⟨q, hq, hrq⟩ := hdvd
          have hq_p : q.Prime := (hT q (Finset.mem_cons_of_mem hq)).1
          have hqr : r = q := (Nat.prime_dvd_prime_iff_eq hr_p hq_p).mp hrq
          exact hr (hqr ▸ hq)
        exact hcop.mul_dvd_of_dvd_of_dvd hr_d hs_d
    have hfinal : m ∣ a ^ m - a := by
      conv_lhs => rw [← hprod_eq]
      exact hprod_dvd m.primeFactors fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hprime_dvd p hp⟩
    exact ((Nat.modEq_iff_dvd' ha_le).mpr hfinal).symm


private lemma den_eq_mul_den_iff {q : ℚ} {n : ℕ} (hn : 1 ≤ n) :
    q.den = n * ((n : ℚ) * q).den ↔ n ∣ q.den := by
  constructor
  · intro h
    exact ⟨((n : ℚ) * q).den, h⟩
  · intro ⟨d, hd⟩
    have hd_pos : 0 < d := Nat.pos_of_mul_pos_left (hd ▸ q.den_pos)
    have hcop : Nat.Coprime q.num.natAbs d :=
      q.reduced.coprime_dvd_right (hd.symm ▸ dvd_mul_left d n)
    have hmul_eq : (n : ℚ) * q = (q.num : ℚ) / (d : ℚ) := by
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd_pos.ne'
      conv_lhs => rhs; rw [← Rat.num_div_den q, hd]
      push_cast
      field_simp
    have hden_eq : ((n : ℚ) * q).den = d := by
      rw [hmul_eq]
      exact_mod_cast Rat.den_div_eq_of_coprime (a := q.num) (b := (d : ℤ))
        (by exact_mod_cast hd_pos) (by simpa using hcop)
    rw [hden_eq, hd]

private lemma dvd_den_bernoulli_iff_korselt {m : ℕ} (hm2 : 2 ≤ m) :
    m ∣ (bernoulli (m - 1)).den ↔
      Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p - 1) ∣ (m - 1) := by
  by_cases hm_eq2 : m = 2
  · subst hm_eq2
    have hb1 : bernoulli 1 = -1 / 2 := bernoulli_one
    have hden2 : (bernoulli 1).den = 2 := by rw [hb1]; norm_num
    simp only [show 2 - 1 = 1 by decide, hden2, dvd_refl, true_iff]
    refine ⟨(by decide : Nat.Prime 2).squarefree, fun p hp hp2 => ?_⟩
    have hp_eq2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hp2
    rw [hp_eq2]
  · by_cases hmeven : m % 2 = 0
    · have hm4 : 4 ≤ m := by omega
      have hodd : Odd (m - 1) := ⟨m / 2 - 1, by omega⟩
      have hb0 : bernoulli (m - 1) = 0 := bernoulli_eq_zero_of_odd hodd (by omega)
      have hden1 : (bernoulli (m - 1)).den = 1 := by rw [hb0]; rfl
      rw [hden1]
      constructor
      · intro hdvd
        have := Nat.le_of_dvd (by decide) hdvd
        omega
      · intro ⟨hsf, hkor⟩
        have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero hmeven
        have hm_div2 : 2 ≤ m / 2 := by omega
        set q := (m / 2).minFac
        have hq : q.Prime := Nat.minFac_prime (by omega)
        have hqm2 : q ∣ m / 2 := Nat.minFac_dvd (m / 2)
        have hqm : q ∣ m := dvd_trans hqm2 (Nat.div_dvd_of_dvd h2m)
        have hq_ne2 : q ≠ 2 := by
          intro hq2
          rw [hq2] at hqm2
          have h4m : 4 ∣ m := by obtain ⟨c, hc⟩ := hqm2; exact ⟨c, by omega⟩
          rw [Nat.squarefree_iff_prime_squarefree] at hsf
          exact hsf 2 (by decide) h4m
        have hq_odd : 2 ∣ q - 1 := by
          rcases hq.eq_two_or_odd with h2 | hodd_q
          · exact absurd h2 hq_ne2
          · omega
        have h2_sub : 2 ∣ m - 1 := dvd_trans hq_odd (hkor q hq hqm)
        omega
    · set k := (m - 1) / 2
      have hm_eq : m - 1 = 2 * k := by omega
      have hk1 : 1 ≤ k := by omega
      rw [hm_eq, den_bernoulli_even k hk1]
      set S := (Finset.range (2 * k + 2)).filter (fun p => p.Prime ∧ (p - 1) ∣ 2 * k)
      have hP_sf : Squarefree (∏ p ∈ S, p) := by
        rw [Nat.squarefree_iff_prime_squarefree]
        intro p hp hpp
        have hp_dvd_prod : p ∣ ∏ q ∈ S, q := dvd_trans (dvd_mul_left p p) hpp
        rw [hp.prime.dvd_finsetProd_iff] at hp_dvd_prod
        obtain ⟨q, hq, hpq⟩ := hp_dvd_prod
        have hq_p : q.Prime := (Finset.mem_filter.mp hq).2.1
        have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_p).mp hpq
        subst hqp
        have hsplit : ∏ r ∈ S, r = p * ∏ r ∈ S.erase p, r := (Finset.mul_prod_erase S id hq).symm
        rw [hsplit] at hpp
        have hp_rest : p ∣ ∏ r ∈ S.erase p, r := (mul_dvd_mul_iff_left hp.ne_zero).mp hpp
        rw [hp.prime.dvd_finsetProd_iff] at hp_rest
        obtain ⟨r, hr, hpr⟩ := hp_rest
        have hr_p : r.Prime := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hr)).2.1
        have hrp : p = r := (Nat.prime_dvd_prime_iff_eq hp hr_p).mp hpr
        exact (Finset.mem_erase.mp hr).1 hrp.symm
      constructor
      · intro hdvd
        refine ⟨Squarefree.squarefree_of_dvd hdvd hP_sf, ?_⟩
        intro p hp hpm
        have hp_dvd : p ∣ ∏ q ∈ S, q := dvd_trans hpm hdvd
        rw [hp.prime.dvd_finsetProd_iff] at hp_dvd
        obtain ⟨q, hq, hpq⟩ := hp_dvd
        have hq_p : q.Prime := (Finset.mem_filter.mp hq).2.1
        have hqp : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_p).mp hpq
        rw [hqp]
        exact (Finset.mem_filter.mp hq).2.2
      · intro ⟨hsf, hkor⟩
        have hprod_m : ∏ p ∈ m.primeFactors, p = m := Nat.prod_primeFactors_of_squarefree hsf
        rw [← hprod_m]
        refine Finset.prod_dvd_prod_of_subset _ _ id ?_
        intro p hp
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp
        have hple : p ≤ m := Nat.le_of_dvd (by omega) hpm
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp_prime, ?_⟩
        exact hkor p hp_prime hpm


private theorem prove_main : type_of% @OMA.S_oeis_a326578.main := by
  intro n hcar
  have hn2 : 2 ≤ n := hcar.1
  have hcomp : ¬ n.Prime := hcar.2.1
  have hkor := (korselt_iff_carmichael hn2 hcomp).mp hcar
  have hdvd : n ∣ (bernoulli (n - 1)).den := (dvd_den_bernoulli_iff_korselt hn2).mpr hkor
  have hden := (den_eq_mul_den_iff (by omega : 1 ≤ n)).mpr hdvd
  unfold A326578
  rw [hden]
  set d := ((n : ℚ) * bernoulli (n - 1)).den
  have hd_pos : 0 < d := Nat.pos_of_ne_zero ((n : ℚ) * bernoulli (n - 1)).den_nz
  have hnum : n ^ 2 * d = n * (n * d) := by ring
  rw [hnum, Nat.mul_div_cancel _ (Nat.mul_pos (by omega) hd_pos)]

end OMA.P_oeis_a326578

theorem OMA.solution : type_of% @OMA.S_oeis_a326578.main :=
  OMA.P_oeis_a326578.prove_main
