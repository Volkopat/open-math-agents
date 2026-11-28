import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1
import Mathlib

/-! Proof of `Erdos955.erdos_955.variants.pollack_pomerance_thompson_bound.R1.H1.R1.H2`:
bounds the three exceptional classes (a) no prime factor `<= log x`, (c) a powerful divisor
`> x^(2η)`, and (d) `n^2 <= x` each by `(δ / 3) * x` for sufficiently large `x`:
- (d) via `n <= Nat.sqrt x <= √x = o(x)`.
- (c) via `q = a^2 * b^3` for powerful `q`, summability of `1 / (a^2 * b^3)` on `ℕ × ℕ`, and
  `x^(2η) >= exp(2 * log x / log (log x)) -> ∞`.
- (a) via divergence of `∑_{p prime} 1/p` (`Nat.Primes.not_summable_one_div`), giving a fixed
  primorial `M = ∏_{p ∈ P} p` with `φ(M)/M < δ/6`, and residue-class counting mod `M`. -/

namespace OMA.Erdos955Exceptional

open Filter Topology Finset Real

private lemma exists_sq_mul_cube_of_powerful :
    ∀ q : ℕ, 0 < q → (∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q) →
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ q = a ^ 2 * b ^ 3 := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro hq hpow
    by_cases hq1 : q = 1
    · exact ⟨1, 1, one_pos, one_pos, by omega⟩
    · set p := q.minFac
      have hp : p.Prime := Nat.minFac_prime hq1
      have hp_dvd : p ∣ q := Nat.minFac_dvd q
      have hp2_dvd : p ^ 2 ∣ q := hpow p hp hp_dvd
      by_cases hp3_dvd : p ^ 3 ∣ q
      · by_cases hp4_dvd : p ^ 4 ∣ q
        · obtain ⟨q', hq'⟩ := hp2_dvd
          have hq'_pos : 0 < q' := by
            rcases Nat.eq_zero_or_pos q' with rfl | hpos
            · simp at hq'; omega
            · exact hpos
          have hq'_lt : q' < q := by
            have hp2_gt1 : 1 < p ^ 2 := by have := hp.two_le; nlinarith
            nlinarith
          have hq'_pow : ∀ r : ℕ, r.Prime → r ∣ q' → r ^ 2 ∣ q' := by
            intro r hr hrq'
            by_cases hrp : r = p
            · subst hrp
              obtain ⟨k, hk⟩ := hp4_dvd
              have hk' : p ^ 2 * q' = p ^ 2 * (p ^ 2 * k) := by rw [← hq', hk]; ring
              have : q' = p ^ 2 * k := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) hk'
              exact ⟨k, this⟩
            · have hrq : r ∣ q := dvd_trans hrq' ⟨p ^ 2, by rw [hq', mul_comm]⟩
              have hr2q : r ^ 2 ∣ q := hpow r hr hrq
              rw [hq'] at hr2q
              have hcop : Nat.Coprime (r ^ 2) (p ^ 2) :=
                ((Nat.coprime_primes hr hp).2 hrp).pow 2 2
              exact hcop.dvd_of_dvd_mul_left hr2q
          obtain ⟨a, b, ha, hb, hab⟩ := ih q' hq'_lt hq'_pos hq'_pow
          exact ⟨p * a, b, Nat.mul_pos hp.pos ha, hb, by rw [hq', hab]; ring⟩
        · obtain ⟨q', hq'⟩ := hp3_dvd
          have hq'_pos : 0 < q' := by
            rcases Nat.eq_zero_or_pos q' with rfl | hpos
            · simp at hq'; omega
            · exact hpos
          have hq'_lt : q' < q := by
            have hp3_gt1 : 1 < p ^ 3 := one_lt_pow₀ hp.one_lt (by norm_num)
            nlinarith
          have hp_ndvd : ¬ p ∣ q' := by
            intro hdvd
            obtain ⟨k, hk⟩ := hdvd
            apply hp4_dvd
            exact ⟨k, by rw [hq', hk]; ring⟩
          have hq'_pow : ∀ r : ℕ, r.Prime → r ∣ q' → r ^ 2 ∣ q' := by
            intro r hr hrq'
            have hrp : r ≠ p := fun h => hp_ndvd (h ▸ hrq')
            have hrq : r ∣ q := dvd_trans hrq' ⟨p ^ 3, by rw [hq', mul_comm]⟩
            have hr2q : r ^ 2 ∣ q := hpow r hr hrq
            rw [hq'] at hr2q
            have hcop : Nat.Coprime (r ^ 2) (p ^ 3) :=
              ((Nat.coprime_primes hr hp).2 hrp).pow 2 3
            exact hcop.dvd_of_dvd_mul_left hr2q
          obtain ⟨a, b, ha, hb, hab⟩ := ih q' hq'_lt hq'_pos hq'_pow
          exact ⟨a, p * b, ha, Nat.mul_pos hp.pos hb, by rw [hq', hab]; ring⟩
      · obtain ⟨q', hq'⟩ := hp2_dvd
        have hq'_pos : 0 < q' := by
          rcases Nat.eq_zero_or_pos q' with rfl | hpos
          · simp at hq'; omega
          · exact hpos
        have hq'_lt : q' < q := by
          have hp2_gt1 : 1 < p ^ 2 := by have := hp.two_le; nlinarith
          nlinarith
        have hp_ndvd : ¬ p ∣ q' := by
          intro hdvd
          obtain ⟨k, hk⟩ := hdvd
          apply hp3_dvd
          exact ⟨k, by rw [hq', hk]; ring⟩
        have hq'_pow : ∀ r : ℕ, r.Prime → r ∣ q' → r ^ 2 ∣ q' := by
          intro r hr hrq'
          have hrp : r ≠ p := fun h => hp_ndvd (h ▸ hrq')
          have hrq : r ∣ q := dvd_trans hrq' ⟨p ^ 2, by rw [hq', mul_comm]⟩
          have hr2q : r ^ 2 ∣ q := hpow r hr hrq
          rw [hq'] at hr2q
          have hcop : Nat.Coprime (r ^ 2) (p ^ 2) :=
            ((Nat.coprime_primes hr hp).2 hrp).pow 2 2
          exact hcop.dvd_of_dvd_mul_left hr2q
        obtain ⟨a, b, ha, hb, hab⟩ := ih q' hq'_lt hq'_pos hq'_pow
        exact ⟨p * a, b, Nat.mul_pos hp.pos ha, hb, by rw [hq', hab]; ring⟩

private lemma card_filter_dvd_le (x q : ℕ) (hq : 0 < q) :
    ((Icc 1 x).filter (fun n => q ∣ n)).card ≤ x / q := by
  have hcard : (Icc 1 (x / q)).card = x / q := by simp [Nat.card_Icc]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun n => n / q) ?_ ?_
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨hn1, hnx⟩, k, hk⟩ := hn
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp at hk; omega
      · exact hpos
    have hdiv : n / q = k := by rw [hk, Nat.mul_div_cancel_left k hq]
    exact ⟨by omega, Nat.div_le_div_right hnx⟩
  · intro n1 hn1 n2 hn2 hdiv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hn1 hn2
    obtain ⟨k1, hk1⟩ := hn1.2
    obtain ⟨k2, hk2⟩ := hn2.2
    have h1 : n1 / q = k1 := by rw [hk1, Nat.mul_div_cancel_left k1 hq]
    have h2 : n2 / q = k2 := by rw [hk2, Nat.mul_div_cancel_left k2 hq]
    dsimp only at hdiv
    rw [hk1, hk2, ← h1, ← h2, hdiv]

private lemma exists_powerful_tail_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ T₀ : ℕ, ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, 0 < p.1 ∧ 0 < p.2 ∧ T₀ < p.1 ^ 2 * p.2 ^ 3) →
        ∑ p ∈ F, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) ≤ δ := by
  have hsum2 : Summable (fun a : ℕ => (1 : ℝ) / (a : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsum3 : Summable (fun b : ℕ => (1 : ℝ) / (b : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hsum : Summable (fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3)) := by
    have hmul := Summable.mul_of_nonneg hsum2 hsum3 (fun _ => by positivity) (fun _ => by positivity)
    refine hmul.congr fun p => ?_
    ring
  have hhas : Tendsto (fun s : Finset (ℕ × ℕ) =>
      ∑ p ∈ s, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3)) atTop
      (𝓝 (∑' p : ℕ × ℕ, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3))) := hsum.hasSum
  rw [Metric.tendsto_atTop] at hhas
  obtain ⟨S₀, hS₀⟩ := hhas δ hδ
  set K : ℕ := (S₀.sup (fun p : ℕ × ℕ => max p.1 p.2)) + 1
  refine ⟨K ^ 2 * K ^ 3, fun F hF => ?_⟩
  have hdisj : Disjoint S₀ F := by
    rw [Finset.disjoint_left]
    intro p hpS hpF
    have hle1 : p.1 ≤ K := by
      have : max p.1 p.2 ≤ S₀.sup (fun q : ℕ × ℕ => max q.1 q.2) :=
        Finset.le_sup (f := fun q : ℕ × ℕ => max q.1 q.2) hpS
      have := le_max_left p.1 p.2
      omega
    have hle2 : p.2 ≤ K := by
      have : max p.1 p.2 ≤ S₀.sup (fun q : ℕ × ℕ => max q.1 q.2) :=
        Finset.le_sup (f := fun q : ℕ × ℕ => max q.1 q.2) hpS
      have := le_max_right p.1 p.2
      omega
    have hprod : p.1 ^ 2 * p.2 ^ 3 ≤ K ^ 2 * K ^ 3 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hle1 2) (Nat.pow_le_pow_left hle2 3)
    have hgt := (hF p hpF).2.2
    omega
  have hS0_le : ∑ p ∈ S₀, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) ≤
      ∑' p : ℕ × ℕ, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) :=
    hsum.sum_le_tsum S₀ (fun _ _ => by positivity)
  have hU_le : ∑ p ∈ S₀ ∪ F, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) ≤
      ∑' p : ℕ × ℕ, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) :=
    hsum.sum_le_tsum (S₀ ∪ F) (fun _ _ => by positivity)
  have hdist := hS₀ S₀ (subset_refl S₀)
  rw [Real.dist_eq, abs_lt] at hdist
  rw [Finset.sum_union hdisj] at hU_le
  linarith

private lemma exists_prime_finset_prod_lt (δ : ℝ) (hδ : 0 < δ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime) ∧ ∏ p ∈ P, (1 - 1 / (p : ℝ)) < δ := by
  have hnot := Nat.Primes.not_summable_one_div
  have hnot_nat : ¬ Summable (fun n : ℕ => if n.Prime then (1 : ℝ) / (n : ℝ) else 0) := by
    intro hsum
    apply hnot
    have hcomp : Summable (fun p : Nat.Primes =>
        (fun n : ℕ => if n.Prime then (1 : ℝ) / (n : ℝ) else 0) p.1) :=
      hsum.comp_injective Subtype.val_injective
    refine hcomp.congr fun p => ?_
    simp [p.2]
  have hunb : ∃ S : Finset ℕ, -Real.log δ + 1 <
      ∑ n ∈ S, (if n.Prime then (1 : ℝ) / (n : ℝ) else 0) := by
    by_contra hle
    push Not at hle
    apply hnot_nat
    exact summable_of_sum_le (fun n => by split_ifs <;> positivity) hle
  obtain ⟨S, hS⟩ := hunb
  set P : Finset ℕ := S.filter Nat.Prime
  have hP_prime : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have hP_sum : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) =
      ∑ n ∈ S, (if n.Prime then (1 : ℝ) / (n : ℝ) else 0) := by
    rw [Finset.sum_filter]
  refine ⟨P, hP_prime, ?_⟩
  have hprod_le : ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ Real.exp (- ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod ?_ ?_
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP_prime p hp).two_le
      have h1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    · intro p _
      have := Real.add_one_le_exp (-(1 / (p : ℝ)))
      linarith
  have hexp_lt : Real.exp (- ∑ p ∈ P, (1 : ℝ) / (p : ℝ)) < δ := by
    rw [hP_sum]
    calc
      Real.exp (- ∑ n ∈ S, (if n.Prime then (1 : ℝ) / (n : ℝ) else 0))
          < Real.exp (Real.log δ) := Real.exp_lt_exp.2 (by linarith)
      _ = δ := Real.exp_log hδ
  exact lt_of_le_of_lt hprod_le hexp_lt

private lemma totient_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ((Nat.totient (∏ p ∈ P, p) : ℝ) / ((∏ p ∈ P, p : ℕ) : ℝ)) =
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  classical
  induction P using Finset.induction with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hP p (Finset.mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hndvd : ¬ p ∣ ∏ q ∈ s, q := by
      intro hdvd
      obtain ⟨q, hqs, hpq⟩ := (hp.prime.dvd_finsetProd_iff id).1 hdvd
      have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hqs)).1 hpq
      exact hps (heq ▸ hqs)
    rw [Finset.prod_insert hps, Finset.prod_insert hps,
        Nat.totient_mul_of_prime_of_not_dvd hp hndvd]
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.2 hp.pos
    have hprod_pos : (0 : ℝ) < ((∏ q ∈ s, q : ℕ) : ℝ) := by
      exact_mod_cast Finset.prod_pos fun q hq => (hs q hq).pos
    rw [Nat.cast_mul, Nat.cast_mul, ← ih hs]
    have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by simpa using Nat.cast_sub (R := ℝ) hp.one_le
    rw [hp1]
    field_simp [hp_pos.ne', hprod_pos.ne']

private lemma card_filter_coprime_le (x M : ℕ) (hM : 0 < M) :
    ((Icc 1 x).filter (fun n => Nat.Coprime n M)).card ≤ (x / M + 1) * Nat.totient M := by
  set S := (Icc 1 x).filter (fun n => Nat.Coprime n M)
  set T := (Icc 0 (x / M)) ×ˢ ((Finset.range M).filter (fun r => Nat.Coprime r M))
  have hTcard : T.card = (x / M + 1) * Nat.totient M := by
    rw [Finset.card_product, Nat.card_Icc, Nat.totient]
    simp [Nat.coprime_comm]
  rw [← hTcard]
  refine Finset.card_le_card_of_injOn (fun n => (n / M, n % M)) ?_ ?_
  · intro n hn
    simp only [S, T, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_product,
      Finset.mem_range] at hn ⊢
    refine ⟨⟨Nat.zero_le _, Nat.div_le_div_right hn.1.2⟩, Nat.mod_lt n hM, ?_⟩
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hn.2
  · intro n1 _ n2 _ h
    have h1 : n1 / M = n2 / M := congrArg Prod.fst h
    have h2 : n1 % M = n2 % M := congrArg Prod.snd h
    have e1 := Nat.div_add_mod n1 M
    have e2 := Nat.div_add_mod n2 M
    rw [h1, h2] at e1
    omega

private lemma solve_H2 :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H2 := by
  classical
  intro ε _ δ hδ
  obtain ⟨T₀, hT₀⟩ := exists_powerful_tail_bound (δ / 3) (by positivity)
  obtain ⟨P, hP_prime, hP_prod⟩ := exists_prime_finset_prod_lt (δ / 6) (by positivity)
  set M : ℕ := ∏ p ∈ P, p
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hP_prime p hp).pos
  set Pmax : ℕ := P.sup id
  have hlog_ge : ∀ᶠ x : ℕ in atTop, (Pmax : ℝ) ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (Pmax : ℝ)
  have hloglog_ge : ∀ᶠ x : ℕ in atTop, (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  have hpow_ge : ∀ᶠ x : ℕ in atTop, (T₀ : ℝ) ≤ (x : ℝ) ^ (2 / Real.log (Real.log (x : ℝ))) := by
    have hdiv_top : Tendsto (fun t : ℝ => 2 * t / Real.log t) atTop atTop := by
      have hlo : (fun t : ℝ => Real.log t) =o[atTop] (fun t : ℝ => t ^ (1 : ℝ)) :=
        isLittleO_log_rpow_atTop one_pos
      rw [Filter.tendsto_atTop]
      intro B
      have hB : 0 < 1 / (max B 1) := by positivity
      have hb := hlo.bound hB
      filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with t ht ht1
      have hlogp : 0 < Real.log t := Real.log_pos ht1
      rw [Real.rpow_one, Real.norm_of_nonneg hlogp.le, Real.norm_of_nonneg (by linarith)] at ht
      rw [le_div_iff₀ hlogp]
      have hmax : B ≤ max B 1 := le_max_left B 1
      have hmax_pos : 0 < max B 1 := lt_of_lt_of_le one_pos (le_max_right B 1)
      have ht' : max B 1 * Real.log t ≤ t := by
        rw [one_div_mul_eq_div, le_div_iff₀ hmax_pos] at ht
        linarith
      nlinarith
    have hexp_top : Tendsto (fun x : ℕ => Real.exp (2 * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ))))
        atTop atTop :=
      Real.tendsto_exp_atTop.comp
        (hdiv_top.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
    filter_upwards [hexp_top.eventually_ge_atTop (T₀ : ℝ), eventually_ge_atTop 3] with x hx hx3
    have hxpos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.2 (by omega)
    rw [Real.rpow_def_of_pos hxpos]
    have heq : Real.log (x : ℝ) * (2 / Real.log (Real.log (x : ℝ))) =
        2 * Real.log (x : ℝ) / Real.log (Real.log (x : ℝ)) := by ring
    rw [heq]
    exact hx
  have hsqrt_le : ∀ᶠ x : ℕ in atTop, (Nat.sqrt x : ℝ) ≤ (δ / 3) * (x : ℝ) := by
    filter_upwards [eventually_ge_atTop (⌈(3 / δ) ^ 2⌉₊ + 1)] with x hx
    have hxpos : (0 : ℝ) < (x : ℝ) := Nat.cast_pos.2 (by omega)
    have hsq : (Nat.sqrt x : ℝ) ≤ Real.sqrt (x : ℝ) := by
      have h1 : ((Nat.sqrt x : ℝ)) ^ 2 ≤ (x : ℝ) := by
        exact_mod_cast (show Nat.sqrt x ^ 2 ≤ x by simpa [pow_two] using Nat.sqrt_le x)
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (Nat.cast_nonneg _)] at h2
    have hle : (3 / δ) ^ 2 ≤ (x : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈(3 / δ) ^ 2⌉₊ ≤ x by omega))
    have h3 : 3 / δ ≤ Real.sqrt (x : ℝ) := by
      have := Real.sqrt_le_sqrt hle
      rwa [Real.sqrt_sq (by positivity)] at this
    have h4 : Real.sqrt (x : ℝ) ≤ (δ / 3) * (x : ℝ) := by
      have hsq2 : Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) = (x : ℝ) := Real.mul_self_sqrt hxpos.le
      have hmul : (3 / δ) * Real.sqrt (x : ℝ) ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      rw [hsq2] at hmul
      have hpos : (0 : ℝ) < δ / 3 := by positivity
      have := mul_le_mul_of_nonneg_left hmul hpos.le
      have hsimp : δ / 3 * (3 / δ * Real.sqrt (x : ℝ)) = Real.sqrt (x : ℝ) := by
        field_simp [hδ.ne']
      linarith
    exact le_trans hsq h4
  have hM_le : ∀ᶠ x : ℕ in atTop, (M : ℝ) ≤ (δ / 6) * (x : ℝ) := by
    filter_upwards [eventually_ge_atTop (⌈6 * (M : ℝ) / δ⌉₊ + 1)] with x hx
    have h1 : 6 * (M : ℝ) / δ ≤ (x : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (show ⌈6 * (M : ℝ) / δ⌉₊ ≤ x by omega))
    have := (div_le_iff₀ hδ).1 h1
    linarith
  filter_upwards [hlog_ge, hloglog_ge, hpow_ge, hsqrt_le, hM_le, eventually_ge_atTop 3]
    with x hlogx hllx hpowx hsqx hMx hx3
  set η : ℝ := max (ε x) (1 / Real.log (Real.log (x : ℝ)))
  set P1 : ℕ → Prop := fun n => ¬ ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : ℝ) ≤ Real.log (x : ℝ)
  set P2 : ℕ → Prop := fun n =>
    ∃ q ∈ n.divisors, (x : ℝ) ^ (2 * η) < (q : ℝ) ∧ ∀ p : ℕ, p.Prime → p ∣ q → p ^ 2 ∣ q
  set P3 : ℕ → Prop := fun n => n ^ 2 ≤ x
  have hsplit : ((Icc 1 x).filter fun n => P1 n ∨ P2 n ∨ P3 n).card ≤
      ((Icc 1 x).filter P1).card + ((Icc 1 x).filter P2).card + ((Icc 1 x).filter P3).card := by
    have hsub : (Icc 1 x).filter (fun n => P1 n ∨ P2 n ∨ P3 n) ⊆
        ((Icc 1 x).filter P1 ∪ (Icc 1 x).filter P2) ∪ (Icc 1 x).filter P3 := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
      rcases hn.2 with h1 | h2 | h3
      · exact Or.inl (Or.inl ⟨hn.1, h1⟩)
      · exact Or.inl (Or.inr ⟨hn.1, h2⟩)
      · exact Or.inr ⟨hn.1, h3⟩
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have hC1 : (((Icc 1 x).filter P1).card : ℝ) ≤ (δ / 3) * (x : ℝ) := by
    have hsub1 : (Icc 1 x).filter P1 ⊆ (Icc 1 x).filter (fun n => Nat.Coprime n M) := by
      intro n hn
      simp only [Finset.mem_filter] at hn ⊢
      refine ⟨hn.1, ?_⟩
      rw [Nat.coprime_comm]
      apply Nat.Coprime.prod_left
      intro p hp
      have hp_prime := hP_prime p hp
      apply hp_prime.coprime_iff_not_dvd.2
      intro hdvd
      apply hn.2
      have hple : (p : ℝ) ≤ Real.log (x : ℝ) := by
        have h1 : p ≤ Pmax := Finset.le_sup (f := id) hp
        exact le_trans (by exact_mod_cast h1) hlogx
      exact ⟨p, hp_prime, hdvd, hple⟩
    have hc1 : ((Icc 1 x).filter P1).card ≤ (x / M + 1) * Nat.totient M :=
      (Finset.card_le_card hsub1).trans (card_filter_coprime_le x M hM_pos)
    have hc1R : (((Icc 1 x).filter P1).card : ℝ) ≤
        ((x : ℝ) / (M : ℝ) + 1) * (Nat.totient M : ℝ) := by
      have hcast : (((Icc 1 x).filter P1).card : ℝ) ≤ ((x / M + 1 : ℕ) : ℝ) * (Nat.totient M : ℝ) := by
        exact_mod_cast hc1
      refine le_trans hcast (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
      push_cast
      have hdiv : ((x / M : ℕ) : ℝ) ≤ (x : ℝ) / (M : ℝ) := Nat.cast_div_le
      linarith
    have htot_le : (Nat.totient M : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.totient_le M
    have hratio : (Nat.totient M : ℝ) / (M : ℝ) < δ / 6 := by
      rw [totient_prod_primes P hP_prime]
      exact hP_prod
    have hMposR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.2 hM_pos
    calc
      (((Icc 1 x).filter P1).card : ℝ)
          ≤ ((x : ℝ) / (M : ℝ) + 1) * (Nat.totient M : ℝ) := hc1R
      _ = (x : ℝ) * ((Nat.totient M : ℝ) / (M : ℝ)) + (Nat.totient M : ℝ) := by ring
      _ ≤ (x : ℝ) * (δ / 6) + (M : ℝ) := by
        have h1 : (x : ℝ) * ((Nat.totient M : ℝ) / (M : ℝ)) ≤ (x : ℝ) * (δ / 6) :=
          mul_le_mul_of_nonneg_left hratio.le (Nat.cast_nonneg x)
        linarith
      _ ≤ (δ / 3) * (x : ℝ) := by linarith
  have hC2 : (((Icc 1 x).filter P2).card : ℝ) ≤ (δ / 3) * (x : ℝ) := by
    have hT_le_x : (T₀ : ℝ) ≤ (x : ℝ) ^ (2 * η) := by
      have hη_ge : 1 / Real.log (Real.log (x : ℝ)) ≤ η := le_max_right _ _
      have h2η : 2 / Real.log (Real.log (x : ℝ)) ≤ 2 * η := by
        rw [show (2 : ℝ) / Real.log (Real.log (x : ℝ)) = 2 * (1 / Real.log (Real.log (x : ℝ))) by ring]
        linarith
      have h1 : (x : ℝ) ^ (2 / Real.log (Real.log (x : ℝ))) ≤ (x : ℝ) ^ (2 * η) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ x by omega)) h2η
      exact le_trans hpowx h1
    set F : Finset (ℕ × ℕ) :=
      (Icc 1 x ×ˢ Icc 1 x).filter fun p => T₀ < p.1 ^ 2 * p.2 ^ 3
    have hsub2 : (Icc 1 x).filter P2 ⊆
        F.biUnion fun p => (Icc 1 x).filter (fun n => p.1 ^ 2 * p.2 ^ 3 ∣ n) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, hnx⟩, q, hq_div, hq_gt, hq_pow⟩ := hn
      have hq_dvd : q ∣ n := Nat.dvd_of_mem_divisors hq_div
      have hq_pos : 0 < q := Nat.pos_of_mem_divisors hq_div
      have hq_le_x : q ≤ x := le_trans (Nat.le_of_dvd (by omega) hq_dvd) hnx
      obtain ⟨a, b, ha, hb, hab⟩ := exists_sq_mul_cube_of_powerful q hq_pos hq_pow
      have hq_gt_T0 : T₀ < a ^ 2 * b ^ 3 := by
        have hR : (T₀ : ℝ) < (q : ℝ) := lt_of_le_of_lt hT_le_x hq_gt
        have hN : T₀ < q := by exact_mod_cast hR
        omega
      have ha_le : a ≤ x := by
        have : a ≤ a ^ 2 * b ^ 3 := by
          have hb1 : 1 ≤ b ^ 3 := Nat.one_le_pow 3 b hb
          have ha1 : a ≤ a ^ 2 := by nlinarith
          nlinarith
        omega
      have hb_le : b ≤ x := by
        have : b ≤ a ^ 2 * b ^ 3 := by
          have ha1 : 1 ≤ a ^ 2 := Nat.one_le_pow 2 a ha
          have hb1 : b ≤ b ^ 3 := Nat.le_self_pow (by norm_num) b
          nlinarith
        omega
      rw [Finset.mem_biUnion]
      refine ⟨(a, b), ?_, ?_⟩
      · simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨⟨ha, ha_le⟩, ⟨hb, hb_le⟩⟩, hq_gt_T0⟩
      · simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hn1, hnx⟩, hab ▸ hq_dvd⟩
    have hc2_nat : ((Icc 1 x).filter P2).card ≤ ∑ p ∈ F, x / (p.1 ^ 2 * p.2 ^ 3) := by
      calc
        ((Icc 1 x).filter P2).card
            ≤ (F.biUnion fun p => (Icc 1 x).filter (fun n => p.1 ^ 2 * p.2 ^ 3 ∣ n)).card :=
          Finset.card_le_card hsub2
        _ ≤ ∑ p ∈ F, ((Icc 1 x).filter (fun n => p.1 ^ 2 * p.2 ^ 3 ∣ n)).card :=
          Finset.card_biUnion_le
        _ ≤ ∑ p ∈ F, x / (p.1 ^ 2 * p.2 ^ 3) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
          have hpos : 0 < p.1 ^ 2 * p.2 ^ 3 := Nat.mul_pos (pow_pos hp.1.1.1 2) (pow_pos hp.1.2.1 3)
          exact card_filter_dvd_le x (p.1 ^ 2 * p.2 ^ 3) hpos
    have hF_prop : ∀ p ∈ F, 0 < p.1 ∧ 0 < p.2 ∧ T₀ < p.1 ^ 2 * p.2 ^ 3 := by
      intro p hp
      simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      exact ⟨hp.1.1.1, hp.1.2.1, hp.2⟩
    calc
      (((Icc 1 x).filter P2).card : ℝ)
          ≤ ∑ p ∈ F, ((x / (p.1 ^ 2 * p.2 ^ 3) : ℕ) : ℝ) := by exact_mod_cast hc2_nat
      _ ≤ ∑ p ∈ F, (x : ℝ) * ((1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3)) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hdiv : ((x / (p.1 ^ 2 * p.2 ^ 3) : ℕ) : ℝ) ≤
            (x : ℝ) / ((p.1 ^ 2 * p.2 ^ 3 : ℕ) : ℝ) := Nat.cast_div_le
        push_cast at hdiv
        linarith [show (x : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) =
          (x : ℝ) * ((1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3)) by ring]
      _ = (x : ℝ) * ∑ p ∈ F, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3) := by
        rw [← Finset.mul_sum]
      _ ≤ (x : ℝ) * (δ / 3) := mul_le_mul_of_nonneg_left (hT₀ F hF_prop) (Nat.cast_nonneg x)
      _ = (δ / 3) * (x : ℝ) := by ring
  have hC3 : (((Icc 1 x).filter P3).card : ℝ) ≤ (δ / 3) * (x : ℝ) := by
    have hsub3 : (Icc 1 x).filter P3 ⊆ Icc 1 (Nat.sqrt x) := by
      intro n hn
      simp only [P3, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1.1, Nat.le_sqrt.2 (by simpa [pow_two] using hn.2)⟩
    have hc3 : ((Icc 1 x).filter P3).card ≤ Nat.sqrt x := by
      calc
        ((Icc 1 x).filter P3).card ≤ (Icc 1 (Nat.sqrt x)).card := Finset.card_le_card hsub3
        _ = Nat.sqrt x := by simp [Nat.card_Icc]
    exact le_trans (by exact_mod_cast hc3) hsqx
  have htotal : (((Icc 1 x).filter fun n => P1 n ∨ P2 n ∨ P3 n).card : ℝ) ≤
      (((Icc 1 x).filter P1).card : ℝ) + (((Icc 1 x).filter P2).card : ℝ) +
      (((Icc 1 x).filter P3).card : ℝ) := by exact_mod_cast hsplit
  linarith

end OMA.Erdos955Exceptional

theorem OMA.solution :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H2 :=
  OMA.Erdos955Exceptional.solve_H2
