import OMAStatements.S_oeis_a143772
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Factorization.Basic

-- Complete proof of OEIS A143772 (Robert G. Wilson v's 2008 conjecture) via Dirichlet's theorem and CRT
-- Author: Paul Roulleau (@Solfanbtc) via Antigravity NEON-SWARM FACTORY v3

open OMA.S_oeis_a143772

private lemma value_dvd_of_mem {m d : ℕ} (hd : d ∈ m.divisors) :
    value m ∣ d + m / d := by
  unfold value
  exact Finset.gcd_dvd hd

private lemma dvd_value_of_forall {m g : ℕ} (h : ∀ d ∈ m.divisors, g ∣ d + m / d) :
    g ∣ value m := by
  unfold value
  exact Finset.dvd_gcd h

private lemma forward_dir {m : ℕ} (hm1 : 1 < m) (hnp : ¬ m.Prime) :
    Even (value m) ∨ value m = 1 ∨ value m = 3 := by
  have hm0 : m ≠ 0 := by omega
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | hodd
  · have h1mem : 1 ∈ m.divisors := Nat.mem_divisors.mpr ⟨one_dvd m, hm0⟩
    have h2dvd : 2 ∣ m := ⟨k, by omega⟩
    have h2mem : 2 ∈ m.divisors := Nat.mem_divisors.mpr ⟨h2dvd, hm0⟩
    have hd1 : value m ∣ 1 + m := by
      simpa using value_dvd_of_mem h1mem
    have hd2 : value m ∣ 2 + k := by
      have hdiv : m / 2 = k := by omega
      simpa [hdiv] using value_dvd_of_mem h2mem
    have hd2' : value m ∣ 4 + m := by
      have : 4 + m = 2 * (2 + k) := by omega
      rw [this]
      exact dvd_mul_of_dvd_right hd2 2
    have hd3 : value m ∣ 3 := by
      have hsub := Nat.dvd_sub hd2' hd1
      have : 4 + m - (1 + m) = 3 := by omega
      rwa [this] at hsub
    have hle : value m ≤ 3 := Nat.le_of_dvd (by omega) hd3
    have hpos : 0 < value m := by
      by_contra h0
      have hz : value m = 0 := by omega
      rw [hz, zero_dvd_iff] at hd3
      omega
    rcases (by omega : value m = 1 ∨ value m = 2 ∨ value m = 3) with h1 | h2 | h3
    · exact Or.inr (Or.inl h1)
    · exact Or.inl ⟨1, by omega⟩
    · exact Or.inr (Or.inr h3)
  · left
    rw [even_iff_two_dvd]
    apply dvd_value_of_forall
    intro d hd
    have hdm : d ∣ m := (Nat.mem_divisors.mp hd).1
    have hdo : Odd d := hodd.of_dvd_nat hdm
    have hqo : Odd (m / d) := hodd.of_dvd_nat (Nat.div_dvd_of_dvd hdm)
    obtain ⟨a, ha⟩ := hdo
    obtain ⟨b, hb⟩ := hqo
    exact ⟨a + b + 1, by omega⟩

private lemma value_four : value 4 = 1 := by decide
private lemma value_eight : value 8 = 3 := by decide

private lemma value_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    value (p * q) = Nat.gcd (p + q) (p * q + 1) := by
  have hdiv : (p * q).divisors = {1, p, q, p * q} := by
    ext d
    simp only [Nat.mem_divisors, ne_eq, mul_eq_zero, hp.ne_zero, hq.ne_zero, or_self,
      not_false_eq_true, and_true, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hd
      obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hd
      rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
        rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact one_dvd _
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
      · exact dvd_refl _
  unfold value
  rw [hdiv]
  have h1 : p * q / 1 = p * q := Nat.div_one _
  have h2 : p * q / p = q := Nat.mul_div_cancel_left q hp.pos
  have h3 : p * q / q = p := Nat.mul_div_cancel p hq.pos
  have h4 : p * q / (p * q) = 1 := Nat.div_self (Nat.mul_pos hp.pos hq.pos)
  simp only [Finset.gcd_insert, Finset.gcd_singleton, normalize_eq, h1, h2, h3, h4]
  change Nat.gcd (1 + p * q) (Nat.gcd (p + q) (Nat.gcd (q + p) (p * q + 1))) =
    Nat.gcd (p + q) (p * q + 1)
  rw [add_comm q p, add_comm 1 (p * q)]
  have hdup : Nat.gcd (p + q) (Nat.gcd (p + q) (p * q + 1)) = Nat.gcd (p + q) (p * q + 1) := by
    rw [← Nat.gcd_assoc, Nat.gcd_self]
  rw [hdup, Nat.gcd_comm (p * q + 1), Nat.gcd_assoc, Nat.gcd_self]

private lemma gcd_pq_eq_gcd_p2 {p q : ℕ} (hp : 1 ≤ p) :
    Nat.gcd (p + q) (p * q + 1) = Nat.gcd (p + q) (p ^ 2 - 1) := by
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have h1 : Nat.gcd (p + q) (p * q + 1) ∣ p * (p + q) :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) p
    have h2 : Nat.gcd (p + q) (p * q + 1) ∣ p * q + 1 := Nat.gcd_dvd_right _ _
    have hsub := Nat.dvd_sub h1 h2
    have hle : p * q + 1 ≤ p * (p + q) := by nlinarith
    have heq : p * (p + q) - (p * q + 1) = p ^ 2 - 1 := by
      zify [hp2, hle]; ring
    rwa [heq] at hsub
  · apply Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    have h1 : Nat.gcd (p + q) (p ^ 2 - 1) ∣ p * (p + q) :=
      dvd_mul_of_dvd_right (Nat.gcd_dvd_left _ _) p
    have h2 : Nat.gcd (p + q) (p ^ 2 - 1) ∣ p ^ 2 - 1 := Nat.gcd_dvd_right _ _
    have hsub := Nat.dvd_sub h1 h2
    have hp2_le : p ^ 2 ≤ p * (p + q) := by nlinarith
    have hle : p ^ 2 - 1 ≤ p * (p + q) := by omega
    have heq : p * (p + q) - (p ^ 2 - 1) = p * q + 1 := by
      zify [hp2, hle]; ring
    rwa [heq] at hsub

private lemma prod_dvd_of_nat_coprime {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℕ) (n : ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (f i) (f j))
    (hdvd : ∀ i ∈ s, f i ∣ n) :
    (∏ i ∈ s, f i) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hcop_i : Nat.Coprime (f i) (∏ j ∈ s, f j) :=
      Nat.Coprime.prod_right fun j hj =>
        hcop i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj) (fun h => hi (h ▸ hj))
    have hdvd_s : (∏ j ∈ s, f j) ∣ n :=
      ih (fun u hu v hv huv => hcop u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv)
        (fun j hj => hdvd j (Finset.mem_insert_of_mem hj))
    exact hcop_i.mul_dvd_of_dvd_of_dvd (hdvd i (Finset.mem_insert_self i s)) hdvd_s

private lemma prod_primeFactors_pow_eq (n : ℕ) (hn : n ≠ 0) :
    ∏ r ∈ n.primeFactors, r ^ n.factorization r = n := by
  have h := Nat.prod_factorization_pow_eq_self hn
  simpa [Finsupp.prod, Nat.support_factorization] using h

private lemma crt_finset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (m a : ι → ℕ)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (m i) (m j)) :
    ∃ x : ℕ, ∀ i ∈ s, x ≡ a i [MOD m i] := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert i s hi ih =>
    have hcop_s : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → Nat.Coprime (m u) (m v) :=
      fun u hu v hv huv => hcop u (Finset.mem_insert_of_mem hu) v (Finset.mem_insert_of_mem hv) huv
    obtain ⟨x₀, hx₀⟩ := ih hcop_s
    have hcop_prod : Nat.Coprime (m i) (∏ j ∈ s, m j) := by
      apply Nat.Coprime.prod_right
      intro j hj
      exact hcop i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    let cr := Nat.chineseRemainder hcop_prod (a i) x₀
    refine ⟨cr.val, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hjs
    · exact cr.property.1
    · have hdvd : m j ∣ ∏ k ∈ s, m k := Finset.dvd_prod_of_mem m hjs
      exact (cr.property.2.of_dvd hdvd).trans (hx₀ j hjs)

private lemma exists_even_witness {g : ℕ} (hg_pos : 0 < g) (hg_even : Even g) :
    ∃ m : ℕ, 1 < m ∧ ¬ m.Prime ∧ value m = g := by
  have hg2 : 2 ∣ g := even_iff_two_dvd.mp hg_even
  have hg_ge2 : 2 ≤ g := Nat.le_of_dvd hg_pos hg2
  have hcop_g : Nat.Coprime (g - 1) g := by
    have h1 : Nat.Coprime (g - 1) (g - 1 + 1) := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
    rwa [Nat.sub_add_cancel (by omega)] at h1
  obtain ⟨p, hpg, hp, hp_mod⟩ := Nat.forall_exists_prime_gt_and_modEq g (by omega) hcop_g
  have hp_ge3 : 3 ≤ p := by omega
  have hgdvd_p1 : g ∣ p + 1 := by
    have h1 : p + 1 ≡ (g - 1) + 1 [MOD g] := hp_mod.add_right 1
    rw [Nat.sub_add_cancel (by omega)] at h1
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using h1)
  obtain ⟨s, hs⟩ := hgdvd_p1
  set M := p ^ 2 - 1
  have hM_eq : M = (p - 1) * (p + 1) := by
    have hp1 : 1 ≤ p := by omega
    have hp2 : 1 ≤ p ^ 2 := by nlinarith
    dsimp only [M]
    zify [hp1, hp2]; ring
  have hM_pos : 0 < M := by
    have : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hgdvd_M : g ∣ M := by
    rw [hM_eq]
    exact dvd_mul_of_dvd_right ⟨s, hs⟩ (p - 1)
  let Q : ℕ → ℕ := fun r => r ^ (M.factorization r)
  let ar : ℕ → ℕ := fun r =>
    if r ∣ g then (if r ∣ s then g + 1 else 1)
    else (if r ∣ p + 1 then 2 else 1)
  have hcop_Q : ∀ r₁ ∈ M.primeFactors, ∀ r₂ ∈ M.primeFactors, r₁ ≠ r₂ →
      Nat.Coprime (Q r₁) (Q r₂) := by
    intro r₁ hr₁ r₂ hr₂ hne
    have hp1 := Nat.prime_of_mem_primeFactors hr₁
    have hp2 := Nat.prime_of_mem_primeFactors hr₂
    exact ((Nat.coprime_primes hp1 hp2).mpr hne).pow _ _
  obtain ⟨a, ha⟩ := crt_finset M.primeFactors Q ar hcop_Q
  have hprod_Q : ∏ r ∈ M.primeFactors, Q r = M := prod_primeFactors_pow_eq M (by omega)
  have ha_cop : Nat.Coprime a M := by
    rw [← hprod_Q]
    apply Nat.Coprime.prod_right
    intro r hr
    have hpr : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hmod : a ≡ ar r [MOD Q r] := ha r hr
    have he_pos : 0 < M.factorization r :=
      Nat.Prime.factorization_pos_of_dvd hpr (by omega) (Nat.dvd_of_mem_primeFactors hr)
    have hrdvd_Q : r ∣ Q r := dvd_pow_self r (by omega)
    have hmod_r : a ≡ ar r [MOD r] := hmod.of_dvd hrdvd_Q
    have har_cop : Nat.Coprime (ar r) r := by
      simp only [ar]
      split_ifs with hrg hrs hrp
      · obtain ⟨t, ht⟩ := hrg
        rw [ht, Nat.coprime_mul_left_add_left]
        exact Nat.coprime_one_left r
      · exact Nat.coprime_one_left r
      · have hr_ne2 : r ≠ 2 := by
          intro h2; subst h2; exact hrg hg2
        exact (Nat.coprime_primes Nat.prime_two hpr).mpr hr_ne2.symm
      · exact Nat.coprime_one_left r
    have hcop_r : Nat.Coprime a r := by
      rw [Nat.coprime_iff_gcd_eq_one, hmod_r.gcd_eq, ← Nat.coprime_iff_gcd_eq_one]
      exact har_cop
    exact hcop_r.pow_right _
  obtain ⟨q, hqp, hq, hq_mod⟩ := Nat.forall_exists_prime_gt_and_modEq p (by omega) ha_cop
  have hpq_ne : p ≠ q := by omega
  refine ⟨p * q, ?_, ?_, ?_⟩
  · have : 2 ≤ p := hp.two_le
    have : 2 ≤ q := hq.two_le
    nlinarith
  · exact Nat.not_prime_mul hp.one_lt.ne' hq.one_lt.ne'
  · rw [value_mul_primes hp hq hpq_ne, gcd_pq_eq_gcd_p2 (by omega)]
    change Nat.gcd (p + q) M = g
    have hgcd_mod : Nat.gcd (p + q) M = Nat.gcd (p + a) M := by
      have h1 : p + q ≡ p + a [MOD M] := hq_mod.add_left p
      exact Nat.ModEq.gcd_eq h1
    rw [hgcd_mod]
    have hgdvd_pa : g ∣ p + a := by
      rw [← prod_primeFactors_pow_eq g (by omega)]
      apply prod_dvd_of_nat_coprime
      · intro r₁ hr₁ r₂ hr₂ hne
        exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hr₁)
          (Nat.prime_of_mem_primeFactors hr₂)).mpr hne).pow _ _
      · intro r hr
        have hpr := Nat.prime_of_mem_primeFactors hr
        have hrg : r ∣ g := Nat.dvd_of_mem_primeFactors hr
        have hrM : r ∈ M.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpr, hrg.trans hgdvd_M, by omega⟩
        have hle : g.factorization r ≤ M.factorization r :=
          (Nat.factorization_le_iff_dvd (by omega) (by omega)).mpr hgdvd_M r
        have hpow_dvd : r ^ g.factorization r ∣ Q r := Nat.pow_dvd_pow r hle
        have hmod_r : a ≡ ar r [MOD r ^ g.factorization r] := (ha r hrM).of_dvd hpow_dvd
        have hpa_mod : p + a ≡ p + ar r [MOD r ^ g.factorization r] := hmod_r.add_left p
        have hpow_g : r ^ g.factorization r ∣ g := Nat.ordProj_dvd g r
        have hdvd_par : g ∣ p + ar r := by
          simp only [ar, hrg, ↓reduceIte]
          split_ifs
          · exact ⟨s + 1, by linarith⟩
          · exact ⟨s, by linarith⟩
        exact (Nat.ModEq.dvd_iff hpa_mod (dvd_refl _)).mpr (hpow_g.trans hdvd_par)
    obtain ⟨u, hu⟩ := hgdvd_pa
    obtain ⟨K, hK⟩ := hgdvd_M
    rw [hu, hK, Nat.gcd_mul_left]
    suffices hcop_uK : Nat.Coprime u K by rw [hcop_uK, mul_one]
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne1
    obtain ⟨r, hpr, hrdvd_gcd⟩ := Nat.exists_prime_and_dvd hne1
    have hru : r ∣ u := hrdvd_gcd.trans (Nat.gcd_dvd_left u K)
    have hrK : r ∣ K := hrdvd_gcd.trans (Nat.gcd_dvd_right u K)
    have hrM_dvd : r ∣ M := hrK.trans ⟨g, by rw [hK]; ring⟩
    have hrM : r ∈ M.primeFactors := Nat.mem_primeFactors.mpr ⟨hpr, hrM_dvd, by omega⟩
    have hrg_dvd_pa : r * g ∣ p + a := by
      obtain ⟨w, hw⟩ := hru
      exact ⟨w, by rw [hu, hw]; ring⟩
    have hrg_dvd_M : r * g ∣ M := by
      obtain ⟨w, hw⟩ := hrK
      exact ⟨w, by rw [hK, hw]; ring⟩
    by_cases hrg : r ∣ g
    · have hle : g.factorization r + 1 ≤ M.factorization r := by
        have h1 := (Nat.factorization_le_iff_dvd (mul_ne_zero hpr.ne_zero (by omega)) (by omega)).mpr hrg_dvd_M r
        rw [Nat.factorization_mul hpr.ne_zero (by omega), Finsupp.add_apply,
            hpr.factorization_self] at h1
        omega
      have hpow_dvd : r ^ (g.factorization r + 1) ∣ Q r := Nat.pow_dvd_pow r hle
      have hmod_r : p + a ≡ p + ar r [MOD r ^ (g.factorization r + 1)] :=
        ((ha r hrM).of_dvd hpow_dvd).add_left p
      have hpow_rg : r ^ (g.factorization r + 1) ∣ r * g := by
        rw [pow_succ']
        exact Nat.mul_dvd_mul_left r (Nat.ordProj_dvd g r)
      have hdv_par : r ^ (g.factorization r + 1) ∣ p + ar r :=
        (Nat.ModEq.dvd_iff hmod_r (dvd_refl _)).mp (hpow_rg.trans hrg_dvd_pa)
      simp only [ar, hrg, ↓reduceIte] at hdv_par
      split_ifs at hdv_par with hrs
      · have hval : p + (g + 1) = g * (s + 1) := by linarith
        rw [hval] at hdv_par
        have hfac := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hpr.ne_zero)
          (mul_ne_zero (by omega) (by omega))).mpr hdv_par r
        rw [Nat.factorization_pow, Finsupp.smul_apply, hpr.factorization_self, smul_eq_mul, mul_one,
            Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply] at hfac
        have hpos_s1 : 1 ≤ (s + 1).factorization r := by omega
        have hr_s1 : r ∣ s + 1 := (hpr.dvd_iff_one_le_factorization (by omega)).mpr hpos_s1
        have hr1 : r ∣ 1 := by
          have := Nat.dvd_sub hr_s1 hrs
          simpa using this
        exact hpr.not_dvd_one hr1
      · have hval : p + 1 = g * s := hs
        rw [hval] at hdv_par
        have hs_pos : s ≠ 0 := by rintro rfl; simp at hs
        have hfac := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hpr.ne_zero)
          (mul_ne_zero (by omega) hs_pos)).mpr hdv_par r
        rw [Nat.factorization_pow, Finsupp.smul_apply, hpr.factorization_self, smul_eq_mul, mul_one,
            Nat.factorization_mul (by omega) hs_pos, Finsupp.add_apply] at hfac
        have hpos_s : 1 ≤ s.factorization r := by omega
        exact hrs ((hpr.dvd_iff_one_le_factorization hs_pos).mpr hpos_s)
    · have he_pos : 0 < M.factorization r :=
        Nat.Prime.factorization_pos_of_dvd hpr (by omega) hrM_dvd
      have hrdvd_Q : r ∣ Q r := dvd_pow_self r (by omega)
      have hmod_r : p + a ≡ p + ar r [MOD r] := ((ha r hrM).of_dvd hrdvd_Q).add_left p
      have hr_pa : r ∣ p + a := (dvd_mul_right r g).trans hrg_dvd_pa
      have hr_par : r ∣ p + ar r := (Nat.ModEq.dvd_iff hmod_r (dvd_refl _)).mp hr_pa
      simp only [ar, hrg, ↓reduceIte] at hr_par
      split_ifs at hr_par with hrp
      · have hr1 : r ∣ 1 := by
          have hsub := Nat.dvd_sub hr_par hrp
          have : p + 2 - (p + 1) = 1 := by omega
          rwa [this] at hsub
        exact hpr.not_dvd_one hr1
      · exact hrp hr_par

theorem OMA.solution : type_of% @OMA.S_oeis_a143772.main := by
  intro g hg
  constructor
  · rintro ⟨m, hm1, hnp, rfl⟩
    exact forward_dir hm1 hnp
  · rintro (heven | rfl | rfl)
    · exact exists_even_witness hg heven
    · exact ⟨4, by decide, by decide, value_four⟩
    · exact ⟨8, by decide, by decide, value_eight⟩
