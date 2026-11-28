import OMAReductions.R_oeis_a085265_R1

open Finset Nat Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace A085265H2

/-!
### Section 1: Elementary modular counting and Mobius sieve
-/

private lemma card_Icc_zmod_eq_bounds (N m : ℕ) (hm : 0 < m) (r : ZMod m) :
    let S := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r)
    N / m ≤ S.card ∧ S.card ≤ N / m + 1 := by
  intro S
  have : NeZero m := ⟨hm.ne'⟩
  let r0 : ℕ := r.val
  have hr0_lt : r0 < m := ZMod.val_lt r
  let r1 : ℕ := if r0 = 0 then m else r0
  have hr1_pos : 1 ≤ r1 := by
    dsimp [r1]; split_ifs with h <;> omega
  have hr1_le : r1 ≤ m := by
    dsimp [r1]; split_ifs with h <;> omega
  have hr1_cast : (r1 : ZMod m) = r := by
    dsimp [r1]
    split_ifs with h
    · rw [ZMod.natCast_self]
      have hval : r.val = 0 := h
      exact (ZMod.val_eq_zero r).mp hval |>.symm
    · exact ZMod.natCast_zmod_val r
  have hmem : ∀ j : ℕ, j ∈ S ↔ ∃ t : ℕ, j = t * m + r1 ∧ t * m + r1 ≤ N := by
    intro j
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hj1, hjN⟩, hjr⟩
      have hmod : j % m = r1 % m := by
        rw [← ZMod.val_natCast, ← ZMod.val_natCast, hjr, hr1_cast]
      have hge : r1 ≤ j := by
        dsimp [r1]
        split_ifs with h
        · have : j % m = 0 := by
            rw [hmod]
            dsimp [r1]
            rw [if_pos h, Nat.mod_self]
          exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero this)
        · have : j % m = r0 := by
            rw [hmod]
            dsimp [r1]
            rw [if_neg h, Nat.mod_eq_of_lt hr0_lt]
          have := Nat.mod_le j m
          omega
      have hdvd : m ∣ j - r1 := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have hsub : ((j - r1 : ℕ) : ZMod m) = 0 := by
          rw [Nat.cast_sub hge, hjr, hr1_cast, sub_self]
        rw [← ZMod.val_natCast, hsub, ZMod.val_zero]
      rcases hdvd with ⟨t, ht⟩
      have hadd : j - r1 + r1 = j := Nat.sub_add_cancel hge
      have hmul : m * t = t * m := mul_comm m t
      exact ⟨t, by omega, by omega⟩
    · rintro ⟨t, rfl, hle⟩
      refine ⟨⟨by omega, hle⟩, ?_⟩
      push_cast
      rw [ZMod.natCast_self, mul_zero, zero_add, hr1_cast]
  let f : ℕ → ℕ := fun t => t * m + r1
  have hf_inj : Function.Injective f := by
    intro t1 t2 h
    dsimp [f] at h
    have : t1 * m = t2 * m := by omega
    exact Nat.eq_of_mul_eq_mul_right hm this
  by_cases hN : N < r1
  · have hS_empty : S = ∅ := by
      ext j
      simp only [hmem, Finset.notMem_empty, iff_false, not_exists, not_and]
      intro t _
      omega
    rw [hS_empty, Finset.card_empty]
    have : N / m = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · push_neg at hN
    let K : ℕ := (N - r1) / m
    have hS_eq : S = (Finset.range (K + 1)).image f := by
      ext j
      rw [hmem, Finset.mem_image]
      constructor
      · rintro ⟨t, rfl, hle⟩
        refine ⟨t, Finset.mem_range.mpr ?_, rfl⟩
        have : t * m ≤ N - r1 := by omega
        have : t ≤ (N - r1) / m := (Nat.le_div_iff_mul_le hm).mpr this
        omega
      · rintro ⟨t, ht, rfl⟩
        rw [Finset.mem_range] at ht
        refine ⟨t, rfl, ?_⟩
        have htK : t ≤ (N - r1) / m := by omega
        have := (Nat.le_div_iff_mul_le hm).mp htK
        omega
    rw [hS_eq, Finset.card_image_of_injective _ hf_inj, Finset.card_range]
    have h1 : N / m ≤ K + 1 := by
      have hdivm := Nat.div_add_mod (N - r1) m
      have hltm := Nat.mod_lt (N - r1) hm
      have hsubN : N - r1 + r1 = N := Nat.sub_add_cancel hN
      have hNlt : N < m * (K + 2) := by dsimp [K]; nlinarith
      have := Nat.div_lt_of_lt_mul hNlt
      omega
    have h2 : K + 1 ≤ N / m + 1 := by
      have : K ≤ N / m := Nat.div_le_div_right (Nat.sub_le N r1)
      omega
    exact ⟨h1, h2⟩

private lemma card_Icc_zmod_eq_real_bounds (N m : ℕ) (hm : 0 < m) (r : ZMod m) :
    let S := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r)
    |(S.card : ℝ) - (N : ℝ) / (m : ℝ)| ≤ 1 := by
  intro S
  obtain ⟨hlo, hhi⟩ := card_Icc_zmod_eq_bounds N m hm r
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv_lo : (N : ℝ) / (m : ℝ) - 1 < ((N / m : ℕ) : ℝ) := by
    have hmod : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
    have hlt : ((N % m : ℕ) : ℝ) < (m : ℝ) := by exact_mod_cast Nat.mod_lt N hm
    have hcast : (N : ℝ) = (m : ℝ) * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hmod
    rw [hcast, add_div, mul_div_cancel_left₀ _ hm_pos.ne']
    have : ((N % m : ℕ) : ℝ) / (m : ℝ) < 1 := (div_lt_one hm_pos).mpr hlt
    linarith
  have hdiv_hi : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hm_pos]
    exact_mod_cast Nat.div_mul_le_self N m
  have hloR : ((N / m : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hlo
  have hhiR : (S.card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by exact_mod_cast hhi
  rw [abs_le]
  constructor <;> linarith

private lemma card_Icc_dvd_eq_div (N d : ℕ) (hd : 0 < d) :
    ((Finset.Icc 1 N).filter (fun j => d ∣ j)).card = N / d := by
  have hS : (Finset.Icc 1 N).filter (fun j => d ∣ j) =
      (Finset.Icc 1 (N / d)).image (fun t => t * d) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hj1, hjN⟩, ⟨t, rfl⟩⟩
      refine ⟨t, ⟨?_, ?_⟩, mul_comm t d⟩
      · by_contra ht0
        have : t = 0 := by omega
        subst this; omega
      · rw [Nat.le_div_iff_mul_le hd]; linarith
    · rintro ⟨t, ⟨ht1, htN⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_left d t⟩
      exact (Nat.le_div_iff_mul_le hd).mp htN
  rw [hS, Finset.card_image_of_injective _ (fun t1 t2 h => Nat.eq_of_mul_eq_mul_right hd h)]
  simp

private lemma linear_cong_equiv_zmod (a b m : ℕ) (hm : 0 < m) (hcop : a.Coprime m) (r : ZMod m) :
    ∃ r' : ZMod m, ∀ j : ℕ, b ≤ a * j →
      (((a * j - b : ℕ) : ZMod m) = r ↔ (j : ZMod m) = r') := by
  let u : (ZMod m)ˣ := ZMod.unitOfCoprime a hcop
  refine ⟨u⁻¹ * (r + (b : ZMod m)), fun j hbj => ?_⟩
  have ha : ((a : ℕ) : ZMod m) = (u : ZMod m) := by
    simp [u, ZMod.coe_unitOfCoprime]
  rw [Nat.cast_sub hbj, Nat.cast_mul, ha]
  constructor
  · intro h
    have h1 : (u : ZMod m) * (j : ZMod m) = r + (b : ZMod m) := eq_add_of_sub_eq h
    calc (j : ZMod m) = (u⁻¹ : (ZMod m)ˣ) * ((u : ZMod m) * (j : ZMod m)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = u⁻¹ * (r + (b : ZMod m)) := by rw [h1]
  · intro h
    rw [h, ← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel_right]

private lemma sum_moebius_div_eq_prod_one_sub {g : ℕ} (hg : Squarefree g) :
    ∑ d ∈ g.divisors, (μ d : ℝ) / (d : ℝ) =
      ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) := by
  let f : ArithmeticFunction ℝ :=
    { toFun := fun n => if n = 0 then 0 else (n : ℝ)⁻¹
      map_zero' := by simp }
  have hf : f.IsMultiplicative := by
    refine ⟨by simp [f], fun {m n} _ => ?_⟩
    by_cases hm : m = 0 <;> by_cases hn : n = 0
    · simp [f, hm, hn]
    · simp [f, hm, hn]
    · simp [f, hm, hn]
    · simp [f, hm, hn, mul_inv, mul_comm]
  have h := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree f hf hg
  calc ∑ d ∈ g.divisors, (μ d : ℝ) / (d : ℝ)
      = ∑ d ∈ g.divisors, (μ d : ℝ) * f d := by
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_mem_divisors hd)
        simp [f, hd0, div_eq_mul_inv]
    _ = ∏ p ∈ g.primeFactors, (1 - f p) := h.symm
    _ = ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ)) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp0 : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
        simp [f, hp0, one_div]

private lemma card_divisors_of_squarefree {g : ℕ} (hg : Squarefree g) :
    g.divisors.card = 2 ^ g.primeFactors.card := by
  have hg0 : g ≠ 0 := hg.ne_zero
  rw [Nat.card_divisors hg0]
  calc ∏ p ∈ g.primeFactors, (g.factorization p + 1)
      = ∏ _p ∈ g.primeFactors, 2 := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hp' := Nat.prime_of_mem_primeFactors hp
        have h1 : g.factorization p = 1 := by
          have hle : g.factorization p ≤ 1 := by
            by_contra hgt
            push_neg at hgt
            have h2 : p ^ 2 ∣ g := by
              exact (hp'.pow_dvd_iff_le_factorization hg0).mpr hgt
            have hu := hg p (by simpa [sq] using h2)
            exact hp'.not_isUnit hu
          have hpos : 1 ≤ g.factorization p := by
            have hdvd := Nat.dvd_of_mem_primeFactors hp
            exact (hp'.pow_dvd_iff_le_factorization hg0).mp (by simpa using hdvd)
          omega
        omega
    _ = 2 ^ g.primeFactors.card := by simp

private lemma sum_moebius_divisors_indicator (x g : ℕ) (hg0 : g ≠ 0) :
    ∑ d ∈ g.divisors, (if d ∣ x then (μ d : ℤ) else 0) = if x.Coprime g then 1 else 0 := by
  have h1 : ∑ d ∈ g.divisors, (if d ∣ x then (μ d : ℤ) else 0) =
      ∑ d ∈ (Nat.gcd x g).divisors, (μ d : ℤ) := by
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    have hgcd0 : Nat.gcd x g ≠ 0 := by
      intro h; exact hg0 (Nat.gcd_eq_zero_iff.mp h).2
    constructor
    · rintro ⟨⟨hdg, _⟩, hdx⟩
      exact ⟨Nat.dvd_gcd hdx hdg, hgcd0⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_right x g), hg0⟩, hd.trans (Nat.gcd_dvd_left x g)⟩
  rw [h1]
  have h2 := congr_arg (fun f : ArithmeticFunction ℤ => f (Nat.gcd x g))
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h2
  rw [h2]
  simp [ArithmeticFunction.one_apply, Nat.Coprime]

private lemma card_coprime_linear_prog_eq_sum (N a b g m : ℕ) (hg : Squarefree g)
    (r : ZMod m) :
    let S := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ (a * j - b).Coprime g)
    (S.card : ℝ) = ∑ d ∈ g.divisors, (μ d : ℝ) *
      (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ d ∣ (a * j - b))).card : ℝ) := by
  intro S
  have hg0 : g ≠ 0 := hg.ne_zero
  have hZ : (S.card : ℤ) = ∑ d ∈ g.divisors, (μ d : ℤ) *
      (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ d ∣ (a * j - b))).card : ℤ) := by
    have hcard : (S.card : ℤ) = ∑ j ∈ (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r),
        (if (a * j - b).Coprime g then (1 : ℤ) else 0) := by
      rw [Finset.sum_boole]
      congr 2
      ext j
      simp [S, and_assoc]
    rw [hcard]
    simp_rw [← sum_moebius_divisors_indicator _ g hg0]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 3
    ext j
    simp [and_assoc]
  exact_mod_cast hZ

private lemma card_coprime_linear_prog_le (N a b g m : ℕ) (hm : 0 < m)
    (hg : Squarefree g) (hcop_a : a.Coprime g) (hcop_m : m.Coprime g)
    (hb : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j) (r : ZMod m) :
    let S := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ (a * j - b).Coprime g)
    (S.card : ℝ) ≤
      (N : ℝ) / (m : ℝ) * (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) +
        (2 ^ g.primeFactors.card : ℝ) := by
  intro S
  rw [card_coprime_linear_prog_eq_sum N a b g m hg r, ← sum_moebius_div_eq_prod_one_sub hg,
    Finset.mul_sum]
  have hdiff : ∑ d ∈ g.divisors, (μ d : ℝ) *
      (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ d ∣ (a * j - b))).card : ℝ) -
      ∑ d ∈ g.divisors, (N : ℝ) / (m : ℝ) * ((μ d : ℝ) / (d : ℝ)) ≤
      (2 ^ g.primeFactors.card : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ d ∈ g.divisors, ((μ d : ℝ) *
            (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ d ∣ (a * j - b))).card : ℝ) -
            (N : ℝ) / (m : ℝ) * ((μ d : ℝ) / (d : ℝ)))
        ≤ ∑ d ∈ g.divisors, (1 : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
          have hd_dvd : d ∣ g := Nat.dvd_of_mem_divisors hd
          have hcop_ad : a.Coprime d := hcop_a.coprime_dvd_right hd_dvd
          have hcop_md : m.Coprime d := hcop_m.coprime_dvd_right hd_dvd
          obtain ⟨r_d, hr_d⟩ := linear_cong_equiv_zmod a b d hd_pos hcop_ad 0
          let e := ZMod.chineseRemainder hcop_md
          let r_md : ZMod (m * d) := e.symm (r, r_d)
          have hfilter : (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod m) = r ∧ d ∣ (a * j - b)) =
              (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (m * d)) = r_md) := by
            ext j
            simp only [Finset.mem_filter]
            refine and_congr_right fun hj => ?_
            have hd_iff : d ∣ a * j - b ↔ ((a * j - b : ℕ) : ZMod d) = 0 :=
              (ZMod.natCast_eq_zero_iff (a * j - b) d).symm
            rw [hd_iff, hr_d j (hb j hj)]
            constructor
            · rintro ⟨h1, h2⟩
              apply e.injective
              rw [e.apply_symm_apply]
              ext
              · simpa [e, ZMod.chineseRemainder] using h1
              · simpa [e, ZMod.chineseRemainder] using h2
            · intro h
              have h' := congr_arg e h
              rw [e.apply_symm_apply] at h'
              exact ⟨by simpa [e, ZMod.chineseRemainder] using congr_arg Prod.fst h',
                     by simpa [e, ZMod.chineseRemainder] using congr_arg Prod.snd h'⟩
          rw [hfilter]
          have hbd := card_Icc_zmod_eq_real_bounds N (m * d) (Nat.mul_pos hm hd_pos) r_md
          have hmu_abs : |(μ d : ℝ)| ≤ 1 := by
            have hsq : Squarefree d := hg.squarefree_of_dvd hd_dvd
            rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
            push_cast
            rw [abs_pow, abs_neg, abs_one, one_pow]
          have hcast_md : ((m * d : ℕ) : ℝ) = (m : ℝ) * (d : ℝ) := by push_cast; ring
          have hrew : (μ d : ℝ) *
              (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (m * d)) = r_md)).card : ℝ) -
              (N : ℝ) / (m : ℝ) * ((μ d : ℝ) / (d : ℝ)) =
              (μ d : ℝ) *
              ((((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (m * d)) = r_md)).card : ℝ) -
                (N : ℝ) / ((m * d : ℕ) : ℝ)) := by
            rw [hcast_md]; ring
          rw [hrew]
          calc (μ d : ℝ) * _ ≤ |(μ d : ℝ) * _| := le_abs_self _
            _ = |(μ d : ℝ)| * |_| := abs_mul _ _
            _ ≤ 1 * 1 := mul_le_mul hmu_abs hbd (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = (g.divisors.card : ℝ) := by simp
      _ = (2 ^ g.primeFactors.card : ℝ) := by exact_mod_cast card_divisors_of_squarefree hg
  linarith

private lemma card_coprime_linear_ge (N a b g : ℕ)
    (hg : Squarefree g) (hcop_a : a.Coprime g)
    (hb : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j) :
    let J := (Finset.Icc 1 N).filter (fun j : ℕ => (a * j - b).Coprime g)
    (N : ℝ) * (∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))) -
      ((2 ^ g.primeFactors.card : ℝ) - 1) ≤ (J.card : ℝ) := by
  intro J
  have hJeq : J = (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ (a * j - b).Coprime g) := by
    ext j; simp [J, Subsingleton.elim (j : ZMod 1) 0]
  rw [hJeq, card_coprime_linear_prog_eq_sum N a b g 1 hg 0,
    ← sum_moebius_div_eq_prod_one_sub hg, Finset.mul_sum]
  have hdiff : ∑ d ∈ g.divisors, (N : ℝ) * ((μ d : ℝ) / (d : ℝ)) -
      ∑ d ∈ g.divisors, (μ d : ℝ) *
      (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ d ∣ (a * j - b))).card : ℝ) ≤
      (2 ^ g.primeFactors.card : ℝ) - 1 := by
    rw [← Finset.sum_sub_distrib]
    have h1mem : 1 ∈ g.divisors := Nat.one_mem_divisors.mpr hg.ne_zero
    rw [← Finset.add_sum_erase _ _ h1mem]
    have h1term : (N : ℝ) * ((μ 1 : ℝ) / ((1 : ℕ) : ℝ)) - (μ 1 : ℝ) *
        (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ 1 ∣ (a * j - b))).card : ℝ) = 0 := by
      have hcard : ((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ 1 ∣ (a * j - b))).card = N := by
        have : (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ 1 ∣ (a * j - b)) = Finset.Icc 1 N := by
          ext j; simp [Subsingleton.elim (j : ZMod 1) 0]
        rw [this]; simp
      rw [hcard, ArithmeticFunction.moebius_apply_one]
      norm_num
    rw [h1term, zero_add]
    calc ∑ d ∈ g.divisors.erase 1, ((N : ℝ) * ((μ d : ℝ) / (d : ℝ)) - (μ d : ℝ) *
            (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ d ∣ (a * j - b))).card : ℝ))
        ≤ ∑ _d ∈ g.divisors.erase 1, (1 : ℝ) := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd' := Finset.mem_of_mem_erase hd
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd'
          have hd_dvd : d ∣ g := Nat.dvd_of_mem_divisors hd'
          have hcop_ad : a.Coprime d := hcop_a.coprime_dvd_right hd_dvd
          obtain ⟨r_d, hr_d⟩ := linear_cong_equiv_zmod a b d hd_pos hcop_ad 0
          have hfilter : (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ d ∣ (a * j - b)) =
              (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod d) = r_d) := by
            ext j
            simp only [Finset.mem_filter]
            refine and_congr_right fun hj => ?_
            have h1z : (j : ZMod 1) = 0 := Subsingleton.elim _ _
            simp only [h1z, true_and]
            rw [← ZMod.natCast_eq_zero_iff (a * j - b) d]
            exact hr_d j (hb j hj)
          rw [hfilter]
          have hbd := card_Icc_zmod_eq_real_bounds N d hd_pos r_d
          have hmu_abs : |(μ d : ℝ)| ≤ 1 := by
            have hsq : Squarefree d := hg.squarefree_of_dvd hd_dvd
            rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
            push_cast
            rw [abs_pow, abs_neg, abs_one, one_pow]
          have hrew : (N : ℝ) * ((μ d : ℝ) / (d : ℝ)) - (μ d : ℝ) *
              (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod d) = r_d)).card : ℝ) =
              -(μ d : ℝ) *
              ((((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod d) = r_d)).card : ℝ) -
                (N : ℝ) / (d : ℝ)) := by ring
          rw [hrew]
          calc -(μ d : ℝ) * _ ≤ |-(μ d : ℝ) * _| := le_abs_self _
            _ = |(μ d : ℝ)| * |_| := by rw [abs_mul, abs_neg]
            _ ≤ 1 * 1 := mul_le_mul hmu_abs hbd (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = ((g.divisors.erase 1).card : ℝ) := by simp
      _ = (2 ^ g.primeFactors.card : ℝ) - 1 := by
          rw [Finset.card_erase_of_mem h1mem, card_divisors_of_squarefree hg]
          have hge1 : 1 ≤ 2 ^ g.primeFactors.card := Nat.one_le_pow _ _ (by omega)
          rw [Nat.cast_sub hge1]
          push_cast; ring
  linarith

private lemma card_coprime_le_half_err (N Q : ℕ) (hQ : Squarefree Q) (hQ1 : 1 < Q) :
    (((Finset.Icc 1 N).filter (fun j => j.Coprime Q)).card : ℝ) ≤
      (N : ℝ) * (∏ p ∈ Q.primeFactors, (1 - 1 / (p : ℝ))) +
        (2 ^ (Q.primeFactors.card - 1) : ℝ) := by
  have hS : (Finset.Icc 1 N).filter (fun j => j.Coprime Q) =
      (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ (1 * j - 0).Coprime Q) := by
    ext j; simp [Subsingleton.elim (j : ZMod 1) 0]
  rw [hS, card_coprime_linear_prog_eq_sum N 1 0 Q 1 hQ 0,
    ← sum_moebius_div_eq_prod_one_sub hQ, Finset.mul_sum]
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hsum_mu : ∑ d ∈ Q.divisors, (μ d : ℝ) = 0 := by
    have h := sum_moebius_divisors_indicator 0 Q hQ0
    have hcop0 : ¬ Nat.Coprime 0 Q := by
      rw [Nat.coprime_zero_left]; omega
    simp only [dvd_zero, ↓reduceIte, hcop0] at h
    exact_mod_cast h
  have hsum_abs_mu : ∑ d ∈ Q.divisors, |(μ d : ℝ)| = (2 ^ Q.primeFactors.card : ℝ) := by
    calc ∑ d ∈ Q.divisors, |(μ d : ℝ)|
        = ∑ _d ∈ Q.divisors, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hsq : Squarefree d := hQ.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
          rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
          push_cast; rw [abs_pow, abs_neg, abs_one, one_pow]
      _ = (Q.divisors.card : ℝ) := by simp
      _ = (2 ^ Q.primeFactors.card : ℝ) := by exact_mod_cast card_divisors_of_squarefree hQ
  have hpf_pos : 1 ≤ Q.primeFactors.card := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : Q ≠ 1)
    exact Finset.card_pos.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpd, hQ0⟩⟩
  have hdiff : ∑ d ∈ Q.divisors, (μ d : ℝ) *
      (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ d ∣ (1 * j - 0))).card : ℝ) -
      ∑ d ∈ Q.divisors, (N : ℝ) * ((μ d : ℝ) / (d : ℝ)) ≤
      (2 ^ (Q.primeFactors.card - 1) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ d ∈ Q.divisors, ((μ d : ℝ) *
            (((Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ d ∣ (1 * j - 0))).card : ℝ) -
            (N : ℝ) * ((μ d : ℝ) / (d : ℝ)))
        ≤ ∑ d ∈ Q.divisors, (|(μ d : ℝ)| - (μ d : ℝ)) / 2 := by
          refine Finset.sum_le_sum fun d hd => ?_
          have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
          have hfilt : (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod 1) = 0 ∧ d ∣ (1 * j - 0)) =
              (Finset.Icc 1 N).filter (fun j => d ∣ j) := by
            ext j; simp [Subsingleton.elim (j : ZMod 1) 0]
          rw [hfilt, card_Icc_dvd_eq_div N d hd_pos]
          have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
          have hfrac_nonneg : 0 ≤ (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) := by
            have : ((N / d : ℕ) : ℝ) * (d : ℝ) ≤ (N : ℝ) := by
              exact_mod_cast Nat.div_mul_le_self N d
            rw [sub_nonneg, le_div_iff₀ hdR]; exact this
          have hfrac_le : (N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ) ≤ 1 := by
            have hmod : N = d * (N / d) + N % d := (Nat.div_add_mod N d).symm
            have hlt : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt N hd_pos
            have hcast : (N : ℝ) = (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
              exact_mod_cast hmod
            rw [hcast, add_div, mul_div_cancel_left₀ _ hdR.ne']
            have : ((N % d : ℕ) : ℝ) / (d : ℝ) ≤ 1 := (div_le_one hdR).mpr hlt.le
            linarith
          have hrew : (μ d : ℝ) * ((N / d : ℕ) : ℝ) - (N : ℝ) * ((μ d : ℝ) / (d : ℝ)) =
              (-(μ d : ℝ)) * ((N : ℝ) / (d : ℝ) - ((N / d : ℕ) : ℝ)) := by ring
          rw [hrew]
          have hsq : Squarefree d := hQ.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)
          rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
          rcases Nat.even_or_odd (cardFactors d) with he | ho
          · have h1 : ((-1 : ℤ) ^ cardFactors d : ℤ) = 1 := he.neg_one_pow
            rw [h1]; norm_num; linarith
          · have h1 : ((-1 : ℤ) ^ cardFactors d : ℤ) = -1 := ho.neg_one_pow
            rw [h1]; norm_num; linarith
      _ = (∑ d ∈ Q.divisors, |(μ d : ℝ)| - ∑ d ∈ Q.divisors, (μ d : ℝ)) / 2 := by
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
      _ = (2 ^ (Q.primeFactors.card - 1) : ℝ) := by
          rw [hsum_abs_mu, hsum_mu, sub_zero]
          have hpow : (2 : ℝ) ^ Q.primeFactors.card = 2 * (2 : ℝ) ^ (Q.primeFactors.card - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hpf_pos, pow_succ, mul_comm]
          rw [hpow]; ring
  linarith

/-!
### Section 2: Quadratic congruence roots mod `p^2`
-/

private lemma sq_sub_sq_dvd_cases {n p a b j1 j2 : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hab : a * b = 2 * b) (ha : a = 1 ∨ a = 2)
    (hb1 : b ≤ a * j1) (hb2 : b ≤ a * j2)
    (h1lt : (a * j1 - b) ^ 2 ≤ n) (h2lt : (a * j2 - b) ^ 2 ≤ n)
    (hd1 : p ^ 2 ∣ n - (a * j1 - b) ^ 2) (hd2 : p ^ 2 ∣ n - (a * j2 - b) ^ 2) :
    ((j1 : ZMod (p ^ 2)) = (j2 : ZMod (p ^ 2))) ∨
      (((j1 + j2 : ℕ) : ZMod (p ^ 2)) = (b : ZMod (p ^ 2))) := by
  let x1 : ℕ := a * j1 - b
  let x2 : ℕ := a * j2 - b
  have hx1_mod : ((x1 : ℤ) ^ 2 : ZMod (p ^ 2)) = (n : ZMod (p ^ 2)) := by
    have hsub : ((n - x1 ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd1
    rw [Nat.cast_sub h1lt] at hsub
    have := eq_of_sub_eq_zero hsub
    simpa [x1] using this.symm
  have hx2_mod : ((x2 : ℤ) ^ 2 : ZMod (p ^ 2)) = (n : ZMod (p ^ 2)) := by
    have hsub : ((n - x2 ^ 2 : ℕ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hd2
    rw [Nat.cast_sub h2lt] at hsub
    have := eq_of_sub_eq_zero hsub
    simpa [x2] using this.symm
  have hdiff_zmod : (((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ)) : ZMod (p ^ 2)) = 0 := by
    have h0 : ((x1 : ℤ) ^ 2 - (x2 : ℤ) ^ 2 : ZMod (p ^ 2)) = 0 := by
      rw [hx1_mod, hx2_mod, sub_self]
    convert h0 using 1
    ring
  have hdvd_prod : ((p : ℤ) ^ 2) ∣ ((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ)) := by
    have h0 : ((((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ)) : ℤ) : ZMod (p ^ 2)) = 0 := by
      simpa using hdiff_zmod
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (((x1 : ℤ) - (x2 : ℤ)) * ((x1 : ℤ) + (x2 : ℤ))) (p ^ 2)).mp h0
    simpa using h
  have hp_ndvd_x1 : ¬ ((p : ℤ) ∣ (x1 : ℤ)) := by
    intro hpx
    have hpxN : p ∣ x1 := Int.natCast_dvd_natCast.mp hpx
    have hpx2 : p ^ 2 ∣ x1 ^ 2 := pow_dvd_pow_of_dvd hpxN 2
    have hpn2 : p ^ 2 ∣ n := by
      have := Nat.dvd_add hd1 hpx2
      rwa [Nat.sub_add_cancel h1lt] at this
    exact hpn (dvd_trans (dvd_pow_self p (by norm_num)) hpn2)
  have hnot_both : ¬ ((p : ℤ) ∣ ((x1 : ℤ) - (x2 : ℤ)) ∧ (p : ℤ) ∣ ((x1 : ℤ) + (x2 : ℤ))) := by
    rintro ⟨hsub, hadd⟩
    have h2x : (p : ℤ) ∣ 2 * (x1 : ℤ) := by
      have hsum := dvd_add hsub hadd
      rwa [show ((x1 : ℤ) - (x2 : ℤ)) + ((x1 : ℤ) + (x2 : ℤ)) = 2 * (x1 : ℤ) by ring] at hsum
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    rcases hpZ.dvd_or_dvd h2x with h2 | hx
    · have : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
      have := Nat.le_of_dvd (by norm_num) this
      have := hp.two_le
      omega
    · exact hp_ndvd_x1 hx
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcases_x : ((p : ℤ) ^ 2 ∣ (x1 : ℤ) - (x2 : ℤ)) ∨ ((p : ℤ) ^ 2 ∣ (x1 : ℤ) + (x2 : ℤ)) := by
    by_cases h1 : (p : ℤ) ∣ (x1 : ℤ) - (x2 : ℤ)
    · left
      have hnot2 : ¬ (p : ℤ) ∣ (x1 : ℤ) + (x2 : ℤ) := fun h2 => hnot_both ⟨h1, h2⟩
      have hcop : IsCoprime ((p : ℤ) ^ 2) ((x1 : ℤ) + (x2 : ℤ)) :=
        (hpZ.coprime_iff_not_dvd.mpr hnot2).pow_left
      exact hcop.dvd_of_dvd_mul_right hdvd_prod
    · right
      have hcop : IsCoprime ((p : ℤ) ^ 2) ((x1 : ℤ) - (x2 : ℤ)) :=
        (hpZ.coprime_iff_not_dvd.mpr h1).pow_left
      exact hcop.dvd_of_dvd_mul_left hdvd_prod
  have hcop_ap : a.Coprime (p ^ 2) := by
    rcases ha with rfl | rfl
    · simp
    · exact (hp.coprime_iff_not_dvd.mpr (by
        intro h; have := Nat.le_of_dvd (by norm_num) h; have := hp.two_le; omega)).symm.pow_right 2
  have hu_inj : ∀ u v : ZMod (p ^ 2), (a : ZMod (p ^ 2)) * u = (a : ZMod (p ^ 2)) * v → u = v := by
    intro u v huv
    let ua := ZMod.unitOfCoprime a hcop_ap
    have hua : (a : ZMod (p ^ 2)) = (ua : ZMod (p ^ 2)) := by simp [ua, ZMod.coe_unitOfCoprime]
    rw [hua] at huv
    calc u = (ua⁻¹ : (ZMod (p ^ 2))ˣ) * ((ua : ZMod (p ^ 2)) * u) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (ua⁻¹ : (ZMod (p ^ 2))ˣ) * ((ua : ZMod (p ^ 2)) * v) := by rw [huv]
      _ = v := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rcases hcases_x with hsub | hadd
  · left
    have hz : ((((x1 : ℤ) - (x2 : ℤ)) : ℤ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((x1 : ℤ) - (x2 : ℤ)) (p ^ 2)).mpr (by simpa using hsub)
    apply hu_inj
    have hx1c : ((x1 : ℤ) : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) * (j1 : ZMod (p ^ 2)) - (b : ZMod (p ^ 2)) := by
      dsimp [x1]; push_cast; rw [Nat.cast_sub hb1]; push_cast; ring
    have hx2c : ((x2 : ℤ) : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) * (j2 : ZMod (p ^ 2)) - (b : ZMod (p ^ 2)) := by
      dsimp [x2]; push_cast; rw [Nat.cast_sub hb2]; push_cast; ring
    rw [Int.cast_sub, hx1c, hx2c] at hz
    exact eq_of_sub_eq_zero (by linear_combination hz)
  · right
    have hz : ((((x1 : ℤ) + (x2 : ℤ)) : ℤ) : ZMod (p ^ 2)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((x1 : ℤ) + (x2 : ℤ)) (p ^ 2)).mpr (by simpa using hadd)
    apply hu_inj
    have hx1c : ((x1 : ℤ) : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) * (j1 : ZMod (p ^ 2)) - (b : ZMod (p ^ 2)) := by
      dsimp [x1]; push_cast; rw [Nat.cast_sub hb1]; push_cast; ring
    have hx2c : ((x2 : ℤ) : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) * (j2 : ZMod (p ^ 2)) - (b : ZMod (p ^ 2)) := by
      dsimp [x2]; push_cast; rw [Nat.cast_sub hb2]; push_cast; ring
    have hab_z : (a : ZMod (p ^ 2)) * (b : ZMod (p ^ 2)) = 2 * (b : ZMod (p ^ 2)) := by
      have h := congr_arg (fun t : ℕ => (t : ZMod (p ^ 2))) hab
      push_cast at h; exact h
    rw [Int.cast_add, hx1c, hx2c] at hz
    push_cast
    linear_combination hz + hab_z.symm

private lemma bad_p_card_le_one_of_large {N n p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hab : a * b = 2 * b) (ha : a = 1 ∨ a = 2)
    (hb_le : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j ∧ (a * j - b) ^ 2 ≤ n)
    (hb_val : b ≤ 1) (hlarge : 2 * N ≤ p ^ 2) :
    ((Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j1 hj1 j2 hj2
  by_cases hjj : j1 = j2
  · exact hjj
  simp only [Finset.mem_filter, Finset.mem_Icc] at hj1 hj2
  have hcases := sq_sub_sq_dvd_cases hp hp2 hpn hab ha
    (hb_le j1 (Finset.mem_Icc.mpr hj1.1)).1 (hb_le j2 (Finset.mem_Icc.mpr hj2.1)).1
    (hb_le j1 (Finset.mem_Icc.mpr hj1.1)).2 (hb_le j2 (Finset.mem_Icc.mpr hj2.1)).2
    hj1.2 hj2.2
  rcases hcases with heq | hsum
  · have hlt1 : j1 < p ^ 2 := by omega
    have hlt2 : j2 < p ^ 2 := by omega
    have hv := congr_arg ZMod.val heq
    rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hv
    exact hv
  · exfalso
    have hpos : 1 ≤ j1 + j2 - b := by omega
    have hlt : j1 + j2 - b < p ^ 2 := by omega
    have h0 : ((j1 + j2 - b : ℕ) : ZMod (p ^ 2)) = 0 := by
      rw [Nat.cast_sub (by omega : b ≤ j1 + j2), hsum, sub_self]
    have hv := congr_arg ZMod.val h0
    rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
    omega

private lemma bad_p_subset_two_classes {N n p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hab : a * b = 2 * b) (ha : a = 1 ∨ a = 2)
    (hb_le : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j ∧ (a * j - b) ^ 2 ≤ n) :
    ∃ r1 r2 : ZMod (p ^ 2),
      ∀ j ∈ Finset.Icc 1 N, p ^ 2 ∣ n - (a * j - b) ^ 2 →
        (j : ZMod (p ^ 2)) = r1 ∨ (j : ZMod (p ^ 2)) = r2 := by
  by_cases hne : ∃ j0 ∈ Finset.Icc 1 N, p ^ 2 ∣ n - (a * j0 - b) ^ 2
  · obtain ⟨j0, hj0, hd0⟩ := hne
    refine ⟨(j0 : ZMod (p ^ 2)), (b : ZMod (p ^ 2)) - (j0 : ZMod (p ^ 2)), fun j hj hd => ?_⟩
    have hcases := sq_sub_sq_dvd_cases hp hp2 hpn hab ha
      (hb_le j hj).1 (hb_le j0 hj0).1 (hb_le j hj).2 (hb_le j0 hj0).2 hd hd0
    rcases hcases with heq | hsum
    · left; exact heq
    · right; push_cast at hsum; exact eq_sub_of_add_eq hsum
  · push_neg at hne
    exact ⟨0, 0, fun j hj hd => (hne j hj hd).elim⟩

private lemma bad_p_card_direct_le {N n p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hab : a * b = 2 * b) (ha : a = 1 ∨ a = 2)
    (hb_le : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j ∧ (a * j - b) ^ 2 ≤ n) :
    (((Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2)).card : ℝ) ≤
      2 * ((N : ℝ) / (p : ℝ) ^ 2) + 2 := by
  obtain ⟨r1, r2, hr⟩ := bad_p_subset_two_classes hp hp2 hpn hab ha hb_le
  let S1 := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (p ^ 2)) = r1)
  let S2 := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (p ^ 2)) = r2)
  have hsub : (Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2) ⊆ S1 ∪ S2 := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    simp only [Finset.mem_union, Finset.mem_filter, S1, S2]
    rcases hr j hj.1 hj.2 with h1 | h2
    · left; exact ⟨hj.1, h1⟩
    · right; exact ⟨hj.1, h2⟩
  have hcard : ((Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2)).card ≤
      S1.card + S2.card := (Finset.card_le_card hsub).trans (Finset.card_union_le S1 S2)
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hb1 := (abs_le.mp (card_Icc_zmod_eq_real_bounds N (p ^ 2) hp2_pos r1)).2
  have hb2 := (abs_le.mp (card_Icc_zmod_eq_real_bounds N (p ^ 2) hp2_pos r2)).2
  have hcast : (((p ^ 2 : ℕ) : ℝ)) = (p : ℝ) ^ 2 := by push_cast; rfl
  rw [hcast] at hb1 hb2
  have hcardR : (((Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2)).card : ℝ) ≤
      (S1.card : ℝ) + (S2.card : ℝ) := by exact_mod_cast hcard
  linarith

private lemma bad_p_card_mobius_le {N n p a b g : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : ¬ p ∣ n) (hab : a * b = 2 * b) (ha : a = 1 ∨ a = 2)
    (hg : Squarefree g) (hcop_a : a.Coprime g) (hpg : ¬ p ∣ g)
    (hb_le : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j ∧ (a * j - b) ^ 2 ≤ n) :
    (((Finset.Icc 1 N).filter (fun j => (a * j - b).Coprime g ∧ p ^ 2 ∣ n - (a * j - b) ^ 2)).card : ℝ) ≤
      2 * ((N : ℝ) / (p : ℝ) ^ 2 * (∏ q ∈ g.primeFactors, (1 - 1 / (q : ℝ))) +
        (2 ^ g.primeFactors.card : ℝ)) := by
  obtain ⟨r1, r2, hr⟩ := bad_p_subset_two_classes hp hp2 hpn hab ha hb_le
  let S1 := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (p ^ 2)) = r1 ∧ (a * j - b).Coprime g)
  let S2 := (Finset.Icc 1 N).filter (fun j : ℕ => (j : ZMod (p ^ 2)) = r2 ∧ (a * j - b).Coprime g)
  have hsub : (Finset.Icc 1 N).filter (fun j => (a * j - b).Coprime g ∧ p ^ 2 ∣ n - (a * j - b) ^ 2) ⊆
      S1 ∪ S2 := by
    intro j hj
    simp only [Finset.mem_filter] at hj
    simp only [Finset.mem_union, Finset.mem_filter, S1, S2]
    rcases hr j hj.1 hj.2.2 with h1 | h2
    · left; exact ⟨hj.1, h1, hj.2.1⟩
    · right; exact ⟨hj.1, h2, hj.2.1⟩
  have hcardR : (((Finset.Icc 1 N).filter (fun j =>
      (a * j - b).Coprime g ∧ p ^ 2 ∣ n - (a * j - b) ^ 2)).card : ℝ) ≤
      (S1.card : ℝ) + (S2.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le S1 S2)
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hcop_pg : (p ^ 2).Coprime g := (hp.coprime_iff_not_dvd.mpr hpg).pow_left 2
  have hb1 := card_coprime_linear_prog_le N a b g (p ^ 2) hp2_pos hg hcop_a hcop_pg
    (fun j hj => (hb_le j hj).1) r1
  have hb2 := card_coprime_linear_prog_le N a b g (p ^ 2) hp2_pos hg hcop_a hcop_pg
    (fun j hj => (hb_le j hj).1) r2
  have hcast : (((p ^ 2 : ℕ) : ℝ)) = (p : ℝ) ^ 2 := by push_cast; rfl
  rw [hcast] at hb1 hb2
  linarith

/-!
### Section 3: The `m = 1` bound for `(2j)^2 + p^2 = n` when `n % 4 = 1`
-/

private lemma roots_neg_one_prime_pow {q e : ℕ} [NeZero (q ^ e)] (hq : q.Prime) (hq2 : q ≠ 2) (he : 1 ≤ e) :
    let R := (Finset.univ : Finset (ZMod (q ^ e))).filter (fun u => u ^ 2 = -1)
    R.card ≤ 2 ∧ (R.Nonempty → q % 4 = 1) := by
  intro R
  have hqe_pos : 0 < q ^ e := pow_pos hq.pos e
  have : Fact q.Prime := ⟨hq⟩
  constructor
  · by_cases hne : R.Nonempty
    · obtain ⟨u0, hu0⟩ := hne
      have hu0_sq : u0 ^ 2 = -1 := (Finset.mem_filter.mp hu0).2
      have hsub : R ⊆ ({u0, -u0} : Finset (ZMod (q ^ e))) := by
        intro u hu
        have hu_sq : u ^ 2 = -1 := (Finset.mem_filter.mp hu).2
        have hmul0 : (u - u0) * (u + u0) = 0 := by
          linear_combination hu_sq - hu0_sq
        let a := u.val
        let b := u0.val
        have hdvd : ((q : ℤ) ^ e) ∣ ((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ)) := by
          have h0 : ((((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ)) : ℤ) : ZMod (q ^ e)) = 0 := by
            push_cast
            simp only [a, b, ZMod.natCast_zmod_val]
            exact hmul0
          have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (((a : ℤ) - (b : ℤ)) * ((a : ℤ) + (b : ℤ))) (q ^ e)).mp h0
          simpa using hd
        have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
        have hq_ndvd_a : ¬ ((q : ℤ) ∣ (a : ℤ)) := by
          intro hqa
          have hqaN : q ∣ a := Int.natCast_dvd_natCast.mp hqa
          have hqe : q ∣ q ^ e := dvd_pow_self q (by omega)
          have ha2 : q ∣ a ^ 2 := dvd_trans hqaN (dvd_pow_self a (by norm_num))
          have h_add : q ^ e ∣ a ^ 2 + 1 := by
            have h0 : ((a ^ 2 + 1 : ℕ) : ZMod (q ^ e)) = 0 := by
              push_cast
              simp only [a, ZMod.natCast_zmod_val]
              rw [hu_sq]; ring
            exact (ZMod.natCast_eq_zero_iff _ _).mp h0
          have hq1 : q ∣ 1 := (Nat.dvd_add_right ha2).mp (hqe.trans h_add)
          exact hq.not_dvd_one hq1
        have hnot_both : ¬ ((q : ℤ) ∣ (a : ℤ) - (b : ℤ) ∧ (q : ℤ) ∣ (a : ℤ) + (b : ℤ)) := by
          rintro ⟨h1, h2⟩
          have h2a : (q : ℤ) ∣ 2 * (a : ℤ) := by
            have hsum := dvd_add h1 h2
            rwa [show ((a : ℤ) - (b : ℤ)) + ((a : ℤ) + (b : ℤ)) = 2 * (a : ℤ) by ring] at hsum
          rcases hqZ.dvd_or_dvd h2a with h2q | haq
          · have : q ∣ 2 := Int.natCast_dvd_natCast.mp h2q
            have := Nat.le_of_dvd (by norm_num) this
            have := hq.two_le; omega
          · exact hq_ndvd_a haq
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h1 : (q : ℤ) ∣ (a : ℤ) - (b : ℤ)
        · left
          have hnot2 : ¬ (q : ℤ) ∣ (a : ℤ) + (b : ℤ) := fun h2 => hnot_both ⟨h1, h2⟩
          have hcop : IsCoprime ((q : ℤ) ^ e) ((a : ℤ) + (b : ℤ)) :=
            (hqZ.coprime_iff_not_dvd.mpr hnot2).pow_left
          have hd1 := hcop.dvd_of_dvd_mul_right hdvd
          have hz : ((((a : ℤ) - (b : ℤ)) : ℤ) : ZMod (q ^ e)) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) - (b : ℤ)) (q ^ e)).mpr (by simpa using hd1)
          push_cast at hz
          simp only [a, b, ZMod.natCast_zmod_val] at hz
          exact sub_eq_zero.mp hz
        · right
          have hcop : IsCoprime ((q : ℤ) ^ e) ((a : ℤ) - (b : ℤ)) :=
            (hqZ.coprime_iff_not_dvd.mpr h1).pow_left
          have hd2 := hcop.dvd_of_dvd_mul_left hdvd
          have hz : ((((a : ℤ) + (b : ℤ)) : ℤ) : ZMod (q ^ e)) = 0 :=
            (ZMod.intCast_zmod_eq_zero_iff_dvd ((a : ℤ) + (b : ℤ)) (q ^ e)).mpr (by simpa using hd2)
          push_cast at hz
          simp only [a, b, ZMod.natCast_zmod_val] at hz
          exact eq_neg_of_add_eq_zero_left hz
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
  · rintro ⟨u, hu⟩
    have hu_sq : u ^ 2 = -1 := (Finset.mem_filter.mp hu).2
    let f : ZMod (q ^ e) →+* ZMod q := ZMod.castHom (dvd_pow_self q (by omega)) (ZMod q)
    let x : ZMod q := f u
    have hx_sq : x ^ 2 = -1 := by
      dsimp [x]; rw [← map_pow, hu_sq, map_neg, map_one]
    have hx_ne : x ≠ 0 := by
      intro hx0
      rw [hx0, zero_pow (by norm_num)] at hx_sq
      have : (1 : ZMod q) = 0 := by linear_combination hx_sq
      exact one_ne_zero this
    let ux : (ZMod q)ˣ := Units.mk0 x hx_ne
    have hux2 : ux ^ 2 = -1 := by ext; exact hx_sq
    have hux4 : ux ^ 4 = 1 := by
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, ux, Units.val_mk0]
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, hx_sq]
      ring
    have hux2_ne1 : ux ^ 2 ≠ 1 := by
      rw [hux2]
      intro h
      have h2 : (2 : ZMod q) = 0 := by
        have h1 : (-1 : ZMod q) = 1 := congr_arg Units.val h
        linear_combination -h1
      have hqd : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp (by simpa using h2)
      have := Nat.le_of_dvd (by norm_num) hqd
      have := hq.two_le; omega
    have hord : orderOf ux = 4 := by
      have hdvd4 : orderOf ux ∣ 4 := orderOf_dvd_of_pow_eq_one hux4
      have hne1 : orderOf ux ≠ 1 := by
        intro h1; rw [orderOf_eq_one_iff] at h1
        exact hux2_ne1 (by rw [h1, one_pow])
      have hne2 : orderOf ux ≠ 2 := by
        intro h2
        have := pow_orderOf_eq_one ux
        rw [h2] at this
        exact hux2_ne1 this
      have hle4 : orderOf ux ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
      have hpos : 0 < orderOf ux := Nat.pos_of_dvd_of_pos hdvd4 (by norm_num)
      interval_cases h : orderOf ux
      · exact (hne1 rfl).elim
      · exact (hne2 rfl).elim
      · norm_num at hdvd4
      · rfl
    have hcard_units : Fintype.card (ZMod q)ˣ = q - 1 := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime hq]
    have hdvd_card : 4 ∣ q - 1 := by
      rw [← hord, ← hcard_units]
      exact orderOf_dvd_card
    have hq_ge : 3 ≤ q := by have := hq.two_le; omega
    omega

private lemma roots_neg_one_odd_le {n : ℕ} [NeZero n] (hn_odd : n % 2 = 1) :
    let R := (Finset.univ : Finset (ZMod n)).filter (fun u => u ^ 2 = -1)
    R.card ≤ 2 ^ n.primeFactors.card ∧
      (R.Nonempty → ∀ q ∈ n.primeFactors, q % 4 = 1) := by
  have hn_pos : 0 < n := by omega
  suffices ∀ (m : ℕ), 0 < m → m % 2 = 1 → ∀ [NeZero m],
      let R := (Finset.univ : Finset (ZMod m)).filter (fun u => u ^ 2 = -1)
      R.card ≤ 2 ^ m.primeFactors.card ∧
        (R.Nonempty → ∀ q ∈ m.primeFactors, q % 4 = 1) from this n hn_pos hn_odd
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hm_odd _
    by_cases hm1 : m = 1
    · subst hm1
      refine ⟨?_, by simp⟩
      calc ((Finset.univ : Finset (ZMod 1)).filter (fun u => u ^ 2 = -1)).card
          ≤ (Finset.univ : Finset (ZMod 1)).card := Finset.card_filter_le _ _
        _ = 1 := by simp
        _ = 2 ^ (1 : ℕ).primeFactors.card := by simp
    · obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm1
      have hq2 : q ≠ 2 := by
        intro h2; subst h2; obtain ⟨t, rfl⟩ := hqm; omega
      let e := m.factorization q
      have he_pos : 1 ≤ e :=
        (hq.pow_dvd_iff_le_factorization hm.ne').mp (show q ^ 1 ∣ m by simpa using hqm)
      let m1 := q ^ e
      let m2 := m / m1
      have hm1_dvd : m1 ∣ m := Nat.ordProj_dvd m q
      have hm_eq : m = m1 * m2 := (Nat.mul_div_cancel' hm1_dvd).symm
      have hm1_pos : 0 < m1 := pow_pos hq.pos e
      have hm2_pos : 0 < m2 := Nat.div_pos (Nat.le_of_dvd hm hm1_dvd) hm1_pos
      have hm2_lt : m2 < m := by
        have h1 : 1 < m1 := one_lt_pow₀ hq.one_lt (by omega)
        exact Nat.div_lt_self hm h1
      have hm2_odd : m2 % 2 = 1 := by
        have : (m1 * m2) % 2 = 1 := by rwa [← hm_eq]
        rw [Nat.mul_mod] at this
        have hm1_mod : m1 % 2 = 1 := by
          have hqm2 : q % 2 = 1 := by
            have := hq.eq_two_or_odd; omega
          dsimp [m1]; rw [Nat.pow_mod, hqm2, one_pow]; norm_num
        rw [hm1_mod, one_mul] at this
        omega
      have hq_ndvd_m2 : ¬ q ∣ m2 := Nat.not_dvd_ordCompl hq hm.ne'
      have hcop : m1.Coprime m2 := (hq.coprime_iff_not_dvd.mpr hq_ndvd_m2).pow_left e
      have : NeZero m := ⟨hm.ne'⟩
      have : NeZero m1 := ⟨hm1_pos.ne'⟩
      have : NeZero m2 := ⟨hm2_pos.ne'⟩
      let crt : ZMod m ≃+* ZMod m1 × ZMod m2 :=
        (ZMod.ringEquivCongr hm_eq).trans (ZMod.chineseRemainder hcop)
      let R := (Finset.univ : Finset (ZMod m)).filter (fun u => u ^ 2 = -1)
      let R1 := (Finset.univ : Finset (ZMod m1)).filter (fun u => u ^ 2 = -1)
      let R2 := (Finset.univ : Finset (ZMod m2)).filter (fun u => u ^ 2 = -1)
      have hR_card : R.card = R1.card * R2.card := by
        rw [← Finset.card_product]
        refine Finset.card_bij (fun u _ => crt u) ?_ ?_ ?_
        · intro u hu
          have hu2 : u ^ 2 = -1 := (Finset.mem_filter.mp hu).2
          have hcrt2 : crt u ^ 2 = -1 := by rw [← map_pow, hu2, map_neg, map_one]
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, R1, R2]
          exact ⟨congr_arg Prod.fst hcrt2, congr_arg Prod.snd hcrt2⟩
        · intro u1 _ u2 _ h; exact crt.injective h
        · intro p hp
          simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, R1, R2] at hp
          refine ⟨crt.symm p, ?_, crt.apply_symm_apply p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, R]
          apply crt.injective
          rw [map_pow, crt.apply_symm_apply, map_neg, map_one]
          ext
          · exact hp.1
          · exact hp.2
      obtain ⟨hR1_le, hR1_mod⟩ := roots_neg_one_prime_pow hq hq2 he_pos
      obtain ⟨hR2_le, hR2_mod⟩ := ih m2 hm2_lt hm2_pos hm2_odd
      have hpf : m.primeFactors = insert q m2.primeFactors := by
        rw [hm_eq, Nat.primeFactors_mul hm1_pos.ne' hm2_pos.ne']
        have hpf1 : m1.primeFactors = {q} := Nat.primeFactors_prime_pow (by omega) hq
        rw [hpf1]; simp
      have hq_nmem : q ∉ m2.primeFactors := by
        intro h; exact hq_ndvd_m2 (Nat.dvd_of_mem_primeFactors h)
      have hpf_card : m.primeFactors.card = m2.primeFactors.card + 1 := by
        rw [hpf, Finset.card_insert_of_notMem hq_nmem]
      constructor
      · rw [hR_card, hpf_card, pow_succ']
        exact Nat.mul_le_mul hR1_le hR2_le
      · intro hne p hp_mem
        have hR1_ne : R1.Nonempty := by
          obtain ⟨u, hu⟩ := hne
          refine ⟨(crt u).1, ?_⟩
          have hu2 : u ^ 2 = -1 := (Finset.mem_filter.mp hu).2
          have hcrt2 : crt u ^ 2 = -1 := by rw [← map_pow, hu2, map_neg, map_one]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, R1]
          exact congr_arg Prod.fst hcrt2
        have hR2_ne : R2.Nonempty := by
          obtain ⟨u, hu⟩ := hne
          refine ⟨(crt u).2, ?_⟩
          have hu2 : u ^ 2 = -1 := (Finset.mem_filter.mp hu).2
          have hcrt2 : crt u ^ 2 = -1 := by rw [← map_pow, hu2, map_neg, map_one]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, R2]
          exact congr_arg Prod.snd hcrt2
        rw [hpf, Finset.mem_insert] at hp_mem
        rcases hp_mem with rfl | hp2
        · exact hR1_mod hR1_ne
        · exact hR2_mod hR2_ne p hp2

private noncomputable def evenSqPrimeSet (n M : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 (M / 2)).filter
    (fun j => ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n ∧ (2 * j) ^ 2 + p ^ 2 = n)

private lemma mem_evenSqPrimeSet {n M j : ℕ} :
    j ∈ evenSqPrimeSet n M ↔
      j ∈ Finset.Icc 1 (M / 2) ∧ ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n ∧ (2 * j) ^ 2 + p ^ 2 = n := by
  unfold evenSqPrimeSet
  classical
  simp

private lemma card_even_sq_add_prime_sq_le {n M : ℕ} (hn4 : n % 4 = 1) (hn1 : 1 < n) :
    (evenSqPrimeSet n M).card = 0 ∨
      ((∀ q ∈ n.primeFactors, q % 4 = 1) ∧ (evenSqPrimeSet n M).card ≤ 2 ^ (n.primeFactors.card - 1)) := by
  let E := evenSqPrimeSet n M
  by_cases hE : E.card = 0
  · left; exact hE
  · right
    have hn_pos : 0 < n := by omega
    have hn_odd : n % 2 = 1 := by omega
    have : NeZero n := ⟨hn_pos.ne'⟩
    let R := (Finset.univ : Finset (ZMod n)).filter (fun u => u ^ 2 = -1)
    obtain ⟨hR_le, hR_mod⟩ := roots_neg_one_odd_le hn_odd
    have hex_p : ∀ j ∈ E, ∃ p : ℕ, p.Prime ∧ ¬ p ∣ n ∧ (2 * j) ^ 2 + p ^ 2 = n := by
      intro j hj; exact (mem_evenSqPrimeSet.mp hj).2
    classical
    let pOf : ℕ → ℕ := fun j => if h : j ∈ E then Classical.choose (hex_p j h) else 1
    have hpOf_spec : ∀ j (hj : j ∈ E),
        (pOf j).Prime ∧ ¬ (pOf j) ∣ n ∧ (2 * j) ^ 2 + (pOf j) ^ 2 = n := by
      intro j hj; dsimp [pOf]; rw [dif_pos hj]; exact Classical.choose_spec (hex_p j hj)
    let uOf : ℕ → ZMod n := fun j =>
      (2 * (j : ZMod n)) * ((pOf j : ZMod n))⁻¹
    have huOf_mem : ∀ j ∈ E, uOf j ∈ R := by
      intro j hj
      obtain ⟨hp, hpn, heq⟩ := hpOf_spec j hj
      have hcop : (pOf j).Coprime n := hp.coprime_iff_not_dvd.mpr hpn
      have hp_unit : IsUnit ((pOf j : ℕ) : ZMod n) := (ZMod.isUnit_iff_coprime _ _).mpr hcop
      have hp_inv : ((pOf j : ℕ) : ZMod n) * ((pOf j : ℕ) : ZMod n)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ hp_unit
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, R]
      have hsum0 : (2 * (j : ZMod n)) ^ 2 + ((pOf j : ℕ) : ZMod n) ^ 2 = 0 := by
        have h := congr_arg (fun t : ℕ => (t : ZMod n)) heq
        push_cast at h
        rw [ZMod.natCast_self] at h
        exact h
      have hsq : (2 * (j : ZMod n)) ^ 2 = -(((pOf j : ℕ) : ZMod n) ^ 2) :=
        eq_neg_of_add_eq_zero_left hsum0
      dsimp [uOf]
      rw [mul_pow, hsq]
      calc -((pOf j : ZMod n) ^ 2) * ((pOf j : ZMod n)⁻¹) ^ 2
          = -(((pOf j : ZMod n) * (pOf j : ZMod n)⁻¹) ^ 2) := by ring
        _ = -1 := by rw [hp_inv, one_pow]
    have hR_ne : R.Nonempty := by
      obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hE)
      exact ⟨uOf j, huOf_mem j hj⟩
    refine ⟨hR_mod hR_ne, ?_⟩
    have huOf_inj : Set.InjOn uOf E := by
      intro j1 hj1 j2 hj2 heq
      obtain ⟨hp1, hpn1, heq1⟩ := hpOf_spec j1 hj1
      obtain ⟨hp2, hpn2, heq2⟩ := hpOf_spec j2 hj2
      have hcop1 : (pOf j1).Coprime n := hp1.coprime_iff_not_dvd.mpr hpn1
      have hcop2 : (pOf j2).Coprime n := hp2.coprime_iff_not_dvd.mpr hpn2
      have hinv1 : ((pOf j1 : ℕ) : ZMod n) * ((pOf j1 : ℕ) : ZMod n)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop1)
      have hinv2 : ((pOf j2 : ℕ) : ZMod n) * ((pOf j2 : ℕ) : ZMod n)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop2)
      have hcross : (((2 * j1) * pOf j2 : ℕ) : ZMod n) = (((2 * j2) * pOf j1 : ℕ) : ZMod n) := by
        have hm := congr_arg (fun x => x * (pOf j1 : ZMod n) * (pOf j2 : ZMod n)) heq
        dsimp [uOf] at hm
        push_cast
        linear_combination hm - (2 * (j1 : ZMod n)) * (pOf j2 : ZMod n) * hinv1
          + (2 * (j2 : ZMod n)) * (pOf j1 : ZMod n) * hinv2
      have hlt1 : (2 * j1) * pOf j2 < n := by
        have hj1_pos : 1 ≤ j1 := (Finset.mem_Icc.mp (mem_evenSqPrimeSet.mp hj1).1).1
        have h1 : (2 * j1) ^ 2 < n := by nlinarith [hp1.pos]
        have h2 : (pOf j2) ^ 2 < n := by
          have hj2_pos : 1 ≤ j2 := (Finset.mem_Icc.mp (mem_evenSqPrimeSet.mp hj2).1).1
          nlinarith
        nlinarith
      have hlt2 : (2 * j2) * pOf j1 < n := by
        have hj1_pos : 1 ≤ j1 := (Finset.mem_Icc.mp (mem_evenSqPrimeSet.mp hj1).1).1
        have hj2_pos : 1 ≤ j2 := (Finset.mem_Icc.mp (mem_evenSqPrimeSet.mp hj2).1).1
        have h1 : (2 * j2) ^ 2 < n := by nlinarith [hp2.pos]
        have h2 : (pOf j1) ^ 2 < n := by nlinarith
        nlinarith
      have heq_prod : (2 * j1) * pOf j2 = (2 * j2) * pOf j1 := by
        have hv := congr_arg ZMod.val hcross
        rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hv
        exact hv
      have hcop_j1p1 : (pOf j1).Coprime (2 * j1) := by
        refine hp1.coprime_iff_not_dvd.mpr fun h => hpn1 ?_
        have hsq : pOf j1 ∣ (2 * j1) ^ 2 := dvd_trans h (dvd_pow_self _ (by norm_num))
        have hp_sq : pOf j1 ∣ (pOf j1) ^ 2 := dvd_pow_self _ (by norm_num)
        rw [← heq1]; exact Nat.dvd_add hsq hp_sq
      have hcop_j2p2 : (pOf j2).Coprime (2 * j2) := by
        refine hp2.coprime_iff_not_dvd.mpr fun h => hpn2 ?_
        have hsq : pOf j2 ∣ (2 * j2) ^ 2 := dvd_trans h (dvd_pow_self _ (by norm_num))
        have hp_sq : pOf j2 ∣ (pOf j2) ^ 2 := dvd_pow_self _ (by norm_num)
        rw [← heq2]; exact Nat.dvd_add hsq hp_sq
      have hd12 : pOf j1 ∣ pOf j2 := by
        have : pOf j1 ∣ (2 * j1) * pOf j2 := by rw [heq_prod]; exact dvd_mul_left _ _
        exact hcop_j1p1.dvd_of_dvd_mul_left this
      have hd21 : pOf j2 ∣ pOf j1 := by
        have : pOf j2 ∣ (2 * j2) * pOf j1 := by rw [← heq_prod]; exact dvd_mul_left _ _
        exact hcop_j2p2.dvd_of_dvd_mul_left this
      have hp_eq : pOf j1 = pOf j2 := Nat.dvd_antisymm hd12 hd21
      rw [hp_eq] at heq_prod
      have h2eq : 2 * j1 = 2 * j2 := Nat.eq_of_mul_eq_mul_right hp2.pos heq_prod
      omega
    have hdisj : Disjoint (E.image uOf) (E.image (fun j => -uOf j)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_image] at hx1 hx2
      obtain ⟨j1, hj1, rfl⟩ := hx1
      obtain ⟨j2, hj2, heq⟩ := hx2
      obtain ⟨hp1, hpn1, heq1⟩ := hpOf_spec j1 hj1
      obtain ⟨hp2, hpn2, heq2⟩ := hpOf_spec j2 hj2
      have hcop1 : (pOf j1).Coprime n := hp1.coprime_iff_not_dvd.mpr hpn1
      have hcop2 : (pOf j2).Coprime n := hp2.coprime_iff_not_dvd.mpr hpn2
      have hinv1 : ((pOf j1 : ℕ) : ZMod n) * ((pOf j1 : ℕ) : ZMod n)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop1)
      have hinv2 : ((pOf j2 : ℕ) : ZMod n) * ((pOf j2 : ℕ) : ZMod n)⁻¹ = 1 :=
        ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime _ _).mpr hcop2)
      have hsum_zmod : (((2 * j1) * pOf j2 + (2 * j2) * pOf j1 : ℕ) : ZMod n) = 0 := by
        have hm := congr_arg (fun z => z * (pOf j1 : ZMod n) * (pOf j2 : ZMod n)) heq
        dsimp [uOf] at hm
        push_cast
        linear_combination -hm - (2 * (j1 : ZMod n)) * (pOf j2 : ZMod n) * hinv1
          - (2 * (j2 : ZMod n)) * (pOf j1 : ZMod n) * hinv2
      have hdvd_n : n ∣ (2 * j1) * pOf j2 + (2 * j2) * pOf j1 :=
        (ZMod.natCast_eq_zero_iff _ _).mp hsum_zmod
      have hj1_pos : 1 ≤ j1 := (Finset.mem_Icc.mp (mem_evenSqPrimeSet.mp hj1).1).1
      have hj2_pos : 1 ≤ j2 := (Finset.mem_Icc.mp (mem_evenSqPrimeSet.mp hj2).1).1
      have hlt1 : (2 * j1) * pOf j2 < n := by
        have h1 : (2 * j1) ^ 2 < n := by nlinarith [hp1.pos]
        have h2 : (pOf j2) ^ 2 < n := by nlinarith
        nlinarith
      have hlt2 : (2 * j2) * pOf j1 < n := by
        have h1 : (2 * j2) ^ 2 < n := by nlinarith [hp2.pos]
        have h2 : (pOf j1) ^ 2 < n := by nlinarith
        nlinarith
      have hpos : 0 < (2 * j1) * pOf j2 + (2 * j2) * pOf j1 := by
        have := hp1.pos; have := hp2.pos; nlinarith
      obtain ⟨t, ht⟩ := hdvd_n
      have ht_ge1 : 1 ≤ t := by
        rcases t with _ | t
        · rw [mul_zero] at ht; linarith
        · omega
      have ht_le1 : t ≤ 1 := by
        by_contra hgt
        have h2 : 2 ≤ t := by omega
        have h2n : 2 * n ≤ n * t := by
          have := Nat.mul_le_mul_left n h2
          linarith
        omega
      have ht1 : t = 1 := by omega
      subst ht1
      have heven : ((2 * j1) * pOf j2 + (2 * j2) * pOf j1) % 2 = 0 := by
        have : (2 * j1) * pOf j2 + (2 * j2) * pOf j1 = 2 * (j1 * pOf j2 + j2 * pOf j1) := by ring
        omega
      rw [ht, mul_one] at heven
      omega
    have hsub : (E.image uOf) ∪ (E.image (fun j => -uOf j)) ⊆ R := by
      rw [Finset.union_subset_iff]
      refine ⟨Finset.image_subset_iff.mpr huOf_mem, Finset.image_subset_iff.mpr fun j hj => ?_⟩
      have hu := (Finset.mem_filter.mp (huOf_mem j hj)).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, R]
      rw [neg_sq]; exact hu
    have h2E : 2 * E.card ≤ 2 ^ n.primeFactors.card := by
      have hneg_inj : Set.InjOn (fun j => -uOf j) E := fun j1 hj1 j2 hj2 h =>
        huOf_inj hj1 hj2 (neg_inj.mp h)
      have hc1 : (E.image uOf).card = E.card := Finset.card_image_of_injOn huOf_inj
      have hc2 : (E.image (fun j => -uOf j)).card = E.card := Finset.card_image_of_injOn hneg_inj
      have hu := Finset.card_union_of_disjoint hdisj
      have hle := (Finset.card_le_card hsub).trans hR_le
      omega
    have hpf_pos : 1 ≤ n.primeFactors.card := by
      obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      exact Finset.card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqn, hn_pos.ne'⟩⟩
    have hpow : 2 ^ n.primeFactors.card = 2 * 2 ^ (n.primeFactors.card - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hpf_pos, pow_succ, mul_comm]
    dsimp [E] at h2E
    omega

private lemma card_1mod4_primeFactors_bound {n : ℕ} (hn_pos : 0 < n)
    (h14 : ∀ q ∈ n.primeFactors, q % 4 = 1) :
    (n.primeFactors.card ≥ 6 → 48612265 ≤ n) ∧
    (n.primeFactors.card ≥ 7 → 2576450045 ≤ n) ∧
    (n.primeFactors.card ≥ 8 → 157163452745 ≤ n) ∧
    (65 * (2 ^ n.primeFactors.card) ^ 4 ≤ 256 * n) := by
  have hprod_le : ∏ q ∈ n.primeFactors, q ≤ n :=
    Nat.le_of_dvd hn_pos (Nat.prod_primeFactors_dvd n)
  -- Helper: any subset of primes = 1 mod 4 has bounded elements
  have hge5 : ∀ q ∈ n.primeFactors, 5 ≤ q := by
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    have hm := h14 q hq
    have := hp.two_le; omega
  have hnot_small : ∀ q ∈ n.primeFactors, q ≠ 9 ∧ q ≠ 21 ∧ q ≠ 25 ∧ q ≠ 33 ∧ q ≠ 45 ∧ q ≠ 49 ∧ q ≠ 57 := by
    intro q hq
    have hp := Nat.prime_of_mem_primeFactors hq
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; norm_num at hp)
  -- Helper to sort n.primeFactors
  let s := n.primeFactors
  let k := s.card
  let emb : Fin k ↪o ℕ := s.orderEmbOfFin rfl
  have hemb_mem : ∀ i : Fin k, emb i ∈ s := fun i => Finset.orderEmbOfFin_mem s rfl i
  have hemb_strict : StrictMono emb := emb.strictMono
  have hprod_emb : ∏ i : Fin k, emb i = ∏ q ∈ s, q := by
    have himg : Finset.univ.image emb = s := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact hemb_mem i
      · intro hx
        have hx' : x ∈ (s : Set ℕ) := hx
        rw [← Finset.range_orderEmbOfFin s rfl] at hx'
        exact Set.mem_range.mp hx'
    rw [← himg, Finset.prod_image (fun a _ b _ h => emb.injective h)]
  have h_el : ∀ (i : Fin k),
      (0 ≤ i.val → 5 ≤ emb i) ∧
      (1 ≤ i.val → 13 ≤ emb i) ∧
      (2 ≤ i.val → 17 ≤ emb i) ∧
      (3 ≤ i.val → 29 ≤ emb i) ∧
      (4 ≤ i.val → 37 ≤ emb i) ∧
      (5 ≤ i.val → 41 ≤ emb i) ∧
      (6 ≤ i.val → 53 ≤ emb i) ∧
      (7 ≤ i.val → 61 ≤ emb i) := by
    have h0 : ∀ i : Fin k, 5 ≤ emb i := fun i => hge5 (emb i) (hemb_mem i)
    have h1 : ∀ i : Fin k, 1 ≤ i.val → 13 ≤ emb i := by
      intro i hi
      let i0 : Fin k := ⟨0, by omega⟩
      have hlt : emb i0 < emb i := hemb_strict (show i0 < i from hi)
      have hge : 5 ≤ emb i0 := h0 i0
      have hm := h14 (emb i) (hemb_mem i)
      have hns := hnot_small (emb i) (hemb_mem i)
      omega
    have h2 : ∀ i : Fin k, 2 ≤ i.val → 17 ≤ emb i := by
      intro i hi
      let i1 : Fin k := ⟨1, by omega⟩
      have hlt : emb i1 < emb i := hemb_strict (show i1 < i from hi)
      have hge : 13 ≤ emb i1 := h1 i1 (by dsimp [i1]; omega)
      have hm := h14 (emb i) (hemb_mem i)
      omega
    have h3 : ∀ i : Fin k, 3 ≤ i.val → 29 ≤ emb i := by
      intro i hi
      let i2 : Fin k := ⟨2, by omega⟩
      have hlt : emb i2 < emb i := hemb_strict (show i2 < i from hi)
      have hge : 17 ≤ emb i2 := h2 i2 (by dsimp [i2]; omega)
      have hm := h14 (emb i) (hemb_mem i)
      have hns := hnot_small (emb i) (hemb_mem i)
      omega
    have h4 : ∀ i : Fin k, 4 ≤ i.val → 37 ≤ emb i := by
      intro i hi
      let i3 : Fin k := ⟨3, by omega⟩
      have hlt : emb i3 < emb i := hemb_strict (show i3 < i from hi)
      have hge : 29 ≤ emb i3 := h3 i3 (by dsimp [i3]; omega)
      have hm := h14 (emb i) (hemb_mem i)
      have hns := hnot_small (emb i) (hemb_mem i)
      omega
    have h5 : ∀ i : Fin k, 5 ≤ i.val → 41 ≤ emb i := by
      intro i hi
      let i4 : Fin k := ⟨4, by omega⟩
      have hlt : emb i4 < emb i := hemb_strict (show i4 < i from hi)
      have hge : 37 ≤ emb i4 := h4 i4 (by dsimp [i4]; omega)
      have hm := h14 (emb i) (hemb_mem i)
      omega
    have h6 : ∀ i : Fin k, 6 ≤ i.val → 53 ≤ emb i := by
      intro i hi
      let i5 : Fin k := ⟨5, by omega⟩
      have hlt : emb i5 < emb i := hemb_strict (show i5 < i from hi)
      have hge : 41 ≤ emb i5 := h5 i5 (by dsimp [i5]; omega)
      have hm := h14 (emb i) (hemb_mem i)
      have hns := hnot_small (emb i) (hemb_mem i)
      omega
    have h7 : ∀ i : Fin k, 7 ≤ i.val → 61 ≤ emb i := by
      intro i hi
      let i6 : Fin k := ⟨6, by omega⟩
      have hlt : emb i6 < emb i := hemb_strict (show i6 < i from hi)
      have hge : 53 ≤ emb i6 := h6 i6 (by dsimp [i6]; omega)
      have hm := h14 (emb i) (hemb_mem i)
      have hns := hnot_small (emb i) (hemb_mem i)
      omega
    intro i
    exact ⟨fun _ => h0 i, h1 i, h2 i, h3 i, h4 i, h5 i, h6 i, h7 i⟩
  have hprod_ge_sub : ∀ (m : ℕ) (f : Fin m → ℕ) (hmk : m ≤ k),
      (∀ j : Fin m, f j ≤ emb ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmk⟩) →
      ∏ j : Fin m, f j ≤ n := by
    intro m f hmk hle
    calc ∏ j : Fin m, f j
        ≤ ∏ j : Fin m, emb ⟨j.val, Nat.lt_of_lt_of_le j.isLt hmk⟩ := Finset.prod_le_prod' fun j _ => hle j
      _ = ∏ i ∈ Finset.univ.filter (fun i : Fin k => i.val < m), emb i := by
          refine Finset.prod_bij (fun j _ => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hmk⟩ : Fin k)) ?_ ?_ ?_ ?_
          · intro j _; simp [j.isLt]
          · intro j1 _ j2 _ h; exact Fin.ext (congr_arg (Fin.val : Fin k → ℕ) h)
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact ⟨⟨i.val, hi⟩, Finset.mem_univ _, by ext; rfl⟩
          · intro j _; rfl
      _ ≤ ∏ i : Fin k, emb i := by
          refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
          intro i _ _
          have := (h_el i).1 (Nat.zero_le _); omega
      _ = ∏ q ∈ s, q := hprod_emb
      _ ≤ n := hprod_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hk6
    have hle := hprod_ge_sub 6 ![5, 13, 17, 29, 37, 41] hk6 (by
      intro j; fin_cases j
      · exact (h_el _).1 (by dsimp; decide)
      · exact (h_el _).2.1 (by dsimp; decide)
      · exact (h_el _).2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.2.1 (by dsimp; decide))
    have hval : ∏ j : Fin 6, (![5, 13, 17, 29, 37, 41] : Fin 6 → ℕ) j = 48612265 := by decide
    omega
  · intro hk7
    have hle := hprod_ge_sub 7 ![5, 13, 17, 29, 37, 41, 53] hk7 (by
      intro j; fin_cases j
      · exact (h_el _).1 (by dsimp; decide)
      · exact (h_el _).2.1 (by dsimp; decide)
      · exact (h_el _).2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.2.2.1 (by dsimp; decide))
    have hval : ∏ j : Fin 7, (![5, 13, 17, 29, 37, 41, 53] : Fin 7 → ℕ) j = 2576450045 := by decide
    omega
  · intro hk8
    have hle := hprod_ge_sub 8 ![5, 13, 17, 29, 37, 41, 53, 61] hk8 (by
      intro j; fin_cases j
      · exact (h_el _).1 (by dsimp; decide)
      · exact (h_el _).2.1 (by dsimp; decide)
      · exact (h_el _).2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.2.2.1 (by dsimp; decide)
      · exact (h_el _).2.2.2.2.2.2.2 (by dsimp; decide))
    have hval : ∏ j : Fin 8, (![5, 13, 17, 29, 37, 41, 53, 61] : Fin 8 → ℕ) j = 157163452745 := by decide
    omega
  · -- 65 * (2^k)^4 <= 256 * n
    have hpow : (2 ^ n.primeFactors.card) ^ 4 = ∏ _q ∈ s, 16 := by
      dsimp [s]
      rw [Finset.prod_const, ← pow_mul, mul_comm, pow_mul]; norm_num
    rw [hpow]
    let s1 := s.filter (fun q => q ≤ 13)
    let s2 := s.filter (fun q => ¬ q ≤ 13)
    have hsplit : ∏ _q ∈ s, 16 = (∏ _q ∈ s1, 16) * (∏ _q ∈ s2, 16) :=
      (Finset.prod_filter_mul_prod_filter_not s (fun q => q ≤ 13) (fun _ => 16)).symm
    have hsplit_q : ∏ q ∈ s, q = (∏ q ∈ s1, q) * (∏ q ∈ s2, q) :=
      (Finset.prod_filter_mul_prod_filter_not s (fun q => q ≤ 13) (fun q => q)).symm
    have hs2_le : ∏ _q ∈ s2, 16 ≤ ∏ q ∈ s2, q := by
      refine Finset.prod_le_prod' fun q hq => ?_
      simp only [Finset.mem_filter, s2] at hq
      have hm := h14 q hq.1
      omega
    have hs1_sub : s1 ⊆ ({5, 13} : Finset ℕ) := by
      intro q hq
      simp only [Finset.mem_filter, s1] at hq
      have hm := h14 q hq.1
      have hge := hge5 q hq.1
      have hns := hnot_small q hq.1
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h65_s1 : 65 * (∏ _q ∈ s1, 16) ≤ 256 * (∏ q ∈ s1, q) := by
      by_cases h5 : 5 ∈ s1 <;> by_cases h13 : 13 ∈ s1
      · have hs1_eq : s1 = {5, 13} := by
          ext q; constructor
          · exact fun h => hs1_sub h
          · simp only [Finset.mem_insert, Finset.mem_singleton]
            rintro (rfl | rfl) <;> assumption
        rw [hs1_eq]; norm_num
      · have hs1_eq : s1 = {5} := by
          ext q; constructor
          · intro h; have := hs1_sub h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            rcases this with rfl | rfl
            · rfl
            · exact (h13 h).elim
          · simp only [Finset.mem_singleton]; rintro rfl; exact h5
        rw [hs1_eq]; norm_num
      · have hs1_eq : s1 = {13} := by
          ext q; constructor
          · intro h; have := hs1_sub h
            simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
            rcases this with rfl | rfl
            · exact (h5 h).elim
            · rfl
          · simp only [Finset.mem_singleton]; rintro rfl; exact h13
        rw [hs1_eq]; norm_num
      · have hs1_eq : s1 = ∅ := by
          ext q; simp only [Finset.notMem_empty, iff_false]
          intro h; have := hs1_sub h
          simp only [Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact h5 h
          · exact h13 h
        rw [hs1_eq]; norm_num
    calc 65 * ∏ _q ∈ s, 16
        = (65 * ∏ _q ∈ s1, 16) * (∏ _q ∈ s2, 16) := by rw [hsplit]; ring
      _ ≤ (256 * ∏ q ∈ s1, q) * (∏ q ∈ s2, q) := Nat.mul_le_mul h65_s1 hs2_le
      _ = 256 * (∏ q ∈ s, q) := by rw [hsplit_q]; ring
      _ ≤ 256 * n := Nat.mul_le_mul_left 256 hprod_le

/-!
### Section 4: Prime counting upper bounds (elementary sieve and Chebyshev)
-/

private lemma primeCounting_le_sieve (x Q : ℕ) (hQ : Squarefree Q) (hQ1 : 1 < Q) :
    (Nat.primeCounting x : ℝ) ≤
      (Q.primeFactors.card : ℝ) +
      (x : ℝ) * (∏ p ∈ Q.primeFactors, (1 - 1 / (p : ℝ))) +
      (2 ^ (Q.primeFactors.card - 1) : ℝ) := by
  have hpi : Nat.primeCounting x = ((Finset.Icc 1 x).filter Nat.Prime).card := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hlt, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩
    · rintro ⟨⟨_, hle⟩, hp⟩; exact ⟨by omega, hp⟩
  have hsub : (Finset.Icc 1 x).filter Nat.Prime ⊆
      Q.primeFactors ∪ (Finset.Icc 1 x).filter (fun j => j.Coprime Q) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hd : p ∣ Q
    · left; exact Nat.mem_primeFactors.mpr ⟨hp.2, hd, hQ.ne_zero⟩
    · right; exact ⟨hp.1, hp.2.coprime_iff_not_dvd.mpr hd⟩
  have hcard : (Nat.primeCounting x : ℝ) ≤
      (Q.primeFactors.card : ℝ) +
      (((Finset.Icc 1 x).filter (fun j => j.Coprime Q)).card : ℝ) := by
    rw [hpi]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith [card_coprime_le_half_err x Q hQ hQ1]

private lemma squarefree_prod_primes {L : List ℕ} (hnd : L.Nodup) (hp : ∀ p ∈ L, p.Prime) :
    Squarefree L.prod ∧ L.prod.primeFactors = L.toFinset := by
  induction L with
  | nil => simp
  | cons p ps ih =>
    rw [List.nodup_cons] at hnd
    have hp_p : p.Prime := hp p (List.mem_cons_self ..)
    have hps_p : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    obtain ⟨hsq_ps, hpf_ps⟩ := ih hnd.2 hps_p
    have hndvd : ¬ p ∣ ps.prod := by
      intro hd
      have hmem : p ∈ ps.prod.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hp_p, hd, hsq_ps.ne_zero⟩
      rw [hpf_ps, List.mem_toFinset] at hmem
      exact hnd.1 hmem
    have hcop : p.Coprime ps.prod := hp_p.coprime_iff_not_dvd.mpr hndvd
    refine ⟨?_, ?_⟩
    · rw [List.prod_cons]
      exact (Nat.squarefree_mul hcop).mpr ⟨hp_p.squarefree, hsq_ps⟩
    · rw [List.prod_cons, Nat.primeFactors_mul hp_p.ne_zero hsq_ps.ne_zero,
        hp_p.primeFactors, hpf_ps, List.toFinset_cons]
      simp

private lemma primeCounting_le_Q11 (x : ℕ) :
    (Nat.primeCounting x : ℝ) ≤ (16 / 77 : ℝ) * (x : ℝ) + 21 := by
  have h := squarefree_prod_primes (L := [2, 3, 5, 7, 11]) (by decide) (by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num)
  have hQ : ([2, 3, 5, 7, 11] : List ℕ).prod = 2310 := by norm_num
  rw [hQ] at h
  have hle := primeCounting_le_sieve x 2310 h.1 (by norm_num)
  rw [h.2] at hle
  have hcard : ([2, 3, 5, 7, 11] : List ℕ).toFinset.card = 5 := by decide
  have hprod : ∏ p ∈ ([2, 3, 5, 7, 11] : List ℕ).toFinset, (1 - 1 / (p : ℝ)) = 16 / 77 := by
    have : ([2, 3, 5, 7, 11] : List ℕ).toFinset = {2, 3, 5, 7, 11} := by decide
    rw [this]; norm_num
  rw [hcard, hprod] at hle
  linarith

private lemma primeCounting_le_Q13 (x : ℕ) :
    (Nat.primeCounting x : ℝ) ≤ (192 / 1001 : ℝ) * (x : ℝ) + 38 := by
  have h := squarefree_prod_primes (L := [2, 3, 5, 7, 11, 13]) (by decide) (by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  have hQ : ([2, 3, 5, 7, 11, 13] : List ℕ).prod = 30030 := by norm_num
  rw [hQ] at h
  have hle := primeCounting_le_sieve x 30030 h.1 (by norm_num)
  rw [h.2] at hle
  have hcard : ([2, 3, 5, 7, 11, 13] : List ℕ).toFinset.card = 6 := by decide
  have hprod : ∏ p ∈ ([2, 3, 5, 7, 11, 13] : List ℕ).toFinset, (1 - 1 / (p : ℝ)) = 192 / 1001 := by
    have : ([2, 3, 5, 7, 11, 13] : List ℕ).toFinset = {2, 3, 5, 7, 11, 13} := by decide
    rw [this]; norm_num
  rw [hcard, hprod] at hle
  linarith

private lemma primeCounting_le_Q17 (x : ℕ) :
    (Nat.primeCounting x : ℝ) ≤ (3072 / 17017 : ℝ) * (x : ℝ) + 71 := by
  have h := squarefree_prod_primes (L := [2, 3, 5, 7, 11, 13, 17]) (by decide) (by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  have hQ : ([2, 3, 5, 7, 11, 13, 17] : List ℕ).prod = 510510 := by norm_num
  rw [hQ] at h
  have hle := primeCounting_le_sieve x 510510 h.1 (by norm_num)
  rw [h.2] at hle
  have hcard : ([2, 3, 5, 7, 11, 13, 17] : List ℕ).toFinset.card = 7 := by decide
  have hprod : ∏ p ∈ ([2, 3, 5, 7, 11, 13, 17] : List ℕ).toFinset, (1 - 1 / (p : ℝ)) =
      3072 / 17017 := by
    have : ([2, 3, 5, 7, 11, 13, 17] : List ℕ).toFinset = {2, 3, 5, 7, 11, 13, 17} := by decide
    rw [this]; norm_num
  rw [hcard, hprod] at hle
  linarith

private lemma primeCounting_le_Q23 (x : ℕ) :
    (Nat.primeCounting x : ℝ) ≤ (1216512 / 7436429 : ℝ) * (x : ℝ) + 265 := by
  have h := squarefree_prod_primes (L := [2, 3, 5, 7, 11, 13, 17, 19, 23]) (by decide) (by
    intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
  have hQ : ([2, 3, 5, 7, 11, 13, 17, 19, 23] : List ℕ).prod = 223092870 := by norm_num
  rw [hQ] at h
  have hle := primeCounting_le_sieve x 223092870 h.1 (by norm_num)
  rw [h.2] at hle
  have hcard : ([2, 3, 5, 7, 11, 13, 17, 19, 23] : List ℕ).toFinset.card = 9 := by decide
  have hprod : ∏ p ∈ ([2, 3, 5, 7, 11, 13, 17, 19, 23] : List ℕ).toFinset, (1 - 1 / (p : ℝ)) =
      1216512 / 7436429 := by
    have : ([2, 3, 5, 7, 11, 13, 17, 19, 23] : List ℕ).toFinset =
        {2, 3, 5, 7, 11, 13, 17, 19, 23} := by decide
    rw [this]; norm_num
  rw [hcard, hprod] at hle
  linarith

private lemma integral_inv_log_sq_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (Real.log t) ^ 2 ≤ b / (Real.log a) ^ 2 := by
  have hint : IntervalIntegrable (fun t => 1 / (Real.log t) ^ 2) MeasureTheory.volume a b :=
    Chebyshev.intervalIntegrable_one_div_log_sq ha (lt_of_lt_of_le ha hab)
  have hmono : ∫ t in a..b, 1 / (Real.log t) ^ 2 ≤ ∫ _t in a..b, 1 / (Real.log a) ^ 2 := by
    refine intervalIntegral.integral_mono_on hab hint intervalIntegrable_const fun t ht => ?_
    have hlog_pos : 0 < Real.log a := Real.log_pos ha
    have hlog_le : Real.log a ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    gcongr
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hnonneg : 0 ≤ a / (Real.log a) ^ 2 := by positivity
  linarith [show (b - a) * (1 / (Real.log a) ^ 2) = b / (Real.log a) ^ 2 - a / (Real.log a) ^ 2 by ring]

private lemma primeCounting_le_cheb_34 {x : ℝ} (hx : 16 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      Real.log 4 * (x / Real.log x + Real.sqrt x / (Real.log 2) ^ 2 +
        4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
        (16 / 9 : ℝ) * x / (Real.log x) ^ 2) := by
  have hx2 : 2 ≤ x := by linarith
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2]
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have h1 : Chebyshev.theta x / Real.log x ≤ Real.log 4 * (x / Real.log x) := by
    have := Chebyshev.theta_le_log4_mul_x (by linarith : (0 : ℝ) ≤ x)
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right this hlogx.le
  have hint_theta : IntervalIntegrable (fun t => Chebyshev.theta t / (t * (Real.log t) ^ 2))
      MeasureTheory.volume 2 x := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx2, ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq x
  have hint_inv : IntervalIntegrable (fun t => Real.log 4 * (1 / (Real.log t) ^ 2))
      MeasureTheory.volume 2 x :=
    (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _
  have h2 : ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2) ≤
      Real.log 4 * ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hx2 hint_theta hint_inv fun t ht => ?_
    have ht0 : 0 < t := by linarith [ht.1]
    have hth := Chebyshev.theta_le_log4_mul_x ht0.le
    calc Chebyshev.theta t / (t * (Real.log t) ^ 2)
        ≤ (Real.log 4 * t) / (t * (Real.log t) ^ 2) := by
          gcongr
      _ = Real.log 4 * (1 / (Real.log t) ^ 2) := by field_simp
  let y1 : ℝ := Real.sqrt x
  let y2 : ℝ := Real.sqrt x * Real.sqrt (Real.sqrt x)
  have hy1_ge : 2 ≤ y1 := by
    dsimp [y1]
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  have hy1_gt1 : 1 < y1 := by linarith
  have hsqsq_ge : 2 ≤ Real.sqrt (Real.sqrt x) := by
    have : 4 ≤ Real.sqrt x := by
      rw [show (4 : ℝ) = Real.sqrt 16 by norm_num]
      exact Real.sqrt_le_sqrt hx
    rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
    exact Real.sqrt_le_sqrt this
  have hy1_le_y2 : y1 ≤ y2 := by
    dsimp [y1, y2]; nlinarith
  have hy2_le_x : y2 ≤ x := by
    dsimp [y2]
    have hsq_sq : Real.sqrt (Real.sqrt x) ≤ Real.sqrt x := by
      refine Real.sqrt_le_sqrt ?_
      have : 1 ≤ Real.sqrt x := by linarith
      nlinarith [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ x)]
    calc Real.sqrt x * Real.sqrt (Real.sqrt x)
        ≤ Real.sqrt x * Real.sqrt x := by gcongr
      _ = x := Real.mul_self_sqrt (by linarith)
  have hint_2_y1 := Chebyshev.intervalIntegrable_one_div_log_sq (a := 2) (b := y1) (by norm_num) hy1_gt1
  have hint_y1_y2 := Chebyshev.intervalIntegrable_one_div_log_sq (a := y1) (b := y2) hy1_gt1 (lt_of_lt_of_le hy1_gt1 hy1_le_y2)
  have hint_y2_x := Chebyshev.intervalIntegrable_one_div_log_sq (a := y2) (b := x) (lt_of_lt_of_le hy1_gt1 hy1_le_y2) (by linarith)
  have hsplit1 : ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 =
      (∫ t in (2 : ℝ)..y1, 1 / (Real.log t) ^ 2) +
      (∫ t in y1..y2, 1 / (Real.log t) ^ 2) +
      (∫ t in y2..x, 1 / (Real.log t) ^ 2) := by
    symm
    rw [intervalIntegral.integral_add_adjacent_intervals hint_2_y1 hint_y1_y2,
        intervalIntegral.integral_add_adjacent_intervals (hint_2_y1.trans hint_y1_y2) hint_y2_x]
  have hb1 := integral_inv_log_sq_mono (by norm_num : (1 : ℝ) < 2) hy1_ge
  have hb2 := integral_inv_log_sq_mono hy1_gt1 hy1_le_y2
  have hb3 := integral_inv_log_sq_mono (lt_of_lt_of_le hy1_gt1 hy1_le_y2) hy2_le_x
  have hlog_y1 : Real.log y1 = Real.log x / 2 := Real.log_sqrt (by linarith)
  have hlog_y2 : Real.log y2 = (3 / 4 : ℝ) * Real.log x := by
    dsimp [y2]
    have hsq_pos : 0 < Real.sqrt x := by linarith
    have hsqsq_pos : 0 < Real.sqrt (Real.sqrt x) := by linarith
    rw [Real.log_mul hsq_pos.ne' hsqsq_pos.ne', Real.log_sqrt hsq_pos.le, Real.log_sqrt (by linarith)]
    ring
  rw [hlog_y1] at hb2
  rw [hlog_y2] at hb3
  have hb2' : y2 / (Real.log x / 2) ^ 2 = 4 * y2 / (Real.log x) ^ 2 := by ring
  have hb3' : x / ((3 / 4 : ℝ) * Real.log x) ^ 2 = (16 / 9 : ℝ) * x / (Real.log x) ^ 2 := by ring
  rw [hb2'] at hb2
  rw [hb3'] at hb3
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h3 : ∫ t in (2 : ℝ)..x, 1 / (Real.log t) ^ 2 ≤
      y1 / (Real.log 2) ^ 2 + 4 * y2 / (Real.log x) ^ 2 + (16 / 9 : ℝ) * x / (Real.log x) ^ 2 := by
    linarith [hsplit1, hb1, hb2, hb3]
  have h23 := le_trans h2 (mul_le_mul_of_nonneg_left h3 hlog4_nonneg)
  linarith [h1, h23]

/-!
### Section 5: Elementary bounds on `∑ 2/p^2`, `2^ω(g)`, and `φ(g)/g`
-/

private lemma finset_sum_union_le {α : Type*} [DecidableEq α] {s t : Finset α} {f : α → ℝ}
    (hf : ∀ x ∈ s ∩ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + (∑ x ∈ t, f x) := by
  linarith [Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f), Finset.sum_nonneg hf]

private lemma sum_Ico_telescope (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (f k - f (k + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

private lemma two_div_odd_sq_le_sub (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (2 * (k : ℝ)) - 1 / (2 * ((k + 1 : ℕ) : ℝ)) := by
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hc1 : ((2 * k + 1 : ℕ) : ℝ) = 2 * (k : ℝ) + 1 := by push_cast; ring
  have hc2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hc1, hc2]
  have h1 : 1 / (2 * (k : ℝ)) - 1 / (2 * ((k : ℝ) + 1)) =
      1 / (2 * (k : ℝ) * ((k : ℝ) + 1)) := by
    have ha : (2 * (k : ℝ)) ≠ 0 := by linarith
    have hb : (2 * ((k : ℝ) + 1)) ≠ 0 := by linarith
    field_simp
    ring
  rw [h1, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

private lemma sum_two_div_odd_sq_le (Y N : ℕ) (hY : Y % 2 = 1) (hY3 : 3 ≤ Y) :
    ∑ p ∈ (Finset.Icc (Y + 1) N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 ≤
      1 / ((Y : ℝ) + 1) := by
  let k0 : ℕ := (Y + 1) / 2
  have hY_eq : Y + 1 = 2 * k0 := by omega
  let K : ℕ := N / 2 + 1
  have hsub : (Finset.Icc (Y + 1) N).filter Nat.Prime ⊆
      (Finset.Ico k0 K).image (fun k => 2 * k + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp_odd : p % 2 = 1 := by
      have := hp.2.eq_two_or_odd
      omega
    rw [Finset.mem_image]
    refine ⟨p / 2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun k : ℕ => 2 * k + 1) (Finset.Ico k0 K) := by
    intro a _ b _ h; dsimp at h; omega
  calc ∑ p ∈ (Finset.Icc (Y + 1) N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ((Finset.Ico k0 K).image (fun k : ℕ => 2 * k + 1)), (2 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ k ∈ Finset.Ico k0 K, (2 : ℝ) / ((2 * k + 1 : ℕ) : ℝ) ^ 2 :=
        Finset.sum_image (f := fun p : ℕ => (2 : ℝ) / (p : ℝ) ^ 2) hinj
    _ ≤ ∑ k ∈ Finset.Ico k0 K, (1 / (2 * (k : ℝ)) - 1 / (2 * ((k + 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun k hk => two_div_odd_sq_le_sub k (by have := (Finset.mem_Ico.mp hk).1; omega)
    _ ≤ 1 / (2 * (k0 : ℝ)) := by
        by_cases hlt : k0 ≤ K
        · rw [sum_Ico_telescope (fun k : ℕ => 1 / (2 * (k : ℝ))) k0 K hlt]
          have : 0 ≤ 1 / (2 * (K : ℝ)) := by positivity
          linarith
        · have hempty : Finset.Ico k0 K = ∅ := Finset.Ico_eq_empty (by omega)
          rw [hempty, Finset.sum_empty]
          positivity
    _ = 1 / ((Y : ℝ) + 1) := by
        have : (2 * (k0 : ℝ)) = (Y : ℝ) + 1 := by exact_mod_cast hY_eq.symm
        rw [this]

private lemma sum_two_div_prime_sq_gt7 (N : ℕ) :
    ∑ p ∈ (Finset.Icc 8 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 ≤ 81 / 1000 := by
  have hsub : (Finset.Icc 8 N).filter Nat.Prime ⊆
      ({11, 13, 17, 19, 23, 29} : Finset ℕ) ∪ (Finset.Icc 30 N).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc]
    by_cases h30 : 30 ≤ p
    · right; exact ⟨⟨h30, hp.1.2⟩, hp.2⟩
    · left
      have hge8 : 8 ≤ p := hp.1.1
      have hle29 : p ≤ 29 := by omega
      have hpr := hp.2
      interval_cases p <;> (try norm_num at hpr) <;> (try norm_num)
  calc ∑ p ∈ (Finset.Icc 8 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ({11, 13, 17, 19, 23, 29} : Finset ℕ) ∪ (Finset.Icc 30 N).filter Nat.Prime,
          (2 : ℝ) / (p : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ (∑ p ∈ ({11, 13, 17, 19, 23, 29} : Finset ℕ), (2 : ℝ) / (p : ℝ) ^ 2) +
        (∑ p ∈ (Finset.Icc 30 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2) :=
        finset_sum_union_le (fun _ _ => by positivity)
    _ ≤ (∑ p ∈ ({11, 13, 17, 19, 23, 29} : Finset ℕ), (2 : ℝ) / (p : ℝ) ^ 2) + 1 / 30 := by
        gcongr
        have := sum_two_div_odd_sq_le 29 N (by norm_num) (by norm_num)
        norm_num at this
        exact this
    _ ≤ 81 / 1000 := by norm_num

private lemma sum_two_div_prime_sq_ge3 (N : ℕ) :
    ∑ p ∈ (Finset.Icc 3 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 ≤ 43 / 100 := by
  have hsub : (Finset.Icc 3 N).filter Nat.Prime ⊆
      ({3, 5, 7} : Finset ℕ) ∪ (Finset.Icc 8 N).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc]
    by_cases h8 : 8 ≤ p
    · right; exact ⟨⟨h8, hp.1.2⟩, hp.2⟩
    · left
      have hpr := hp.2; have h1 := hp.1.1
      interval_cases p <;> (try norm_num at hpr) <;> (try norm_num)
  calc ∑ p ∈ (Finset.Icc 3 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2
      ≤ (∑ p ∈ ({3, 5, 7} : Finset ℕ), (2 : ℝ) / (p : ℝ) ^ 2) +
        (∑ p ∈ (Finset.Icc 8 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2) :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
          (finset_sum_union_le (fun _ _ => by positivity))
    _ ≤ (∑ p ∈ ({3, 5, 7} : Finset ℕ), (2 : ℝ) / (p : ℝ) ^ 2) + 81 / 1000 := by
        gcongr; exact sum_two_div_prime_sq_gt7 N
    _ ≤ 43 / 100 := by norm_num

private lemma sum_two_div_prime_sq_ge5 (N : ℕ) :
    ∑ p ∈ (Finset.Icc 5 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 ≤ 21 / 100 := by
  have hsub : (Finset.Icc 5 N).filter Nat.Prime ⊆
      ({5, 7} : Finset ℕ) ∪ (Finset.Icc 8 N).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter, Finset.mem_Icc]
    by_cases h8 : 8 ≤ p
    · right; exact ⟨⟨h8, hp.1.2⟩, hp.2⟩
    · left
      have hpr := hp.2; have h1 := hp.1.1
      interval_cases p <;> (try norm_num at hpr) <;> (try norm_num)
  calc ∑ p ∈ (Finset.Icc 5 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2
      ≤ (∑ p ∈ ({5, 7} : Finset ℕ), (2 : ℝ) / (p : ℝ) ^ 2) +
        (∑ p ∈ (Finset.Icc 8 N).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2) :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
          (finset_sum_union_le (fun _ _ => by positivity))
    _ ≤ (∑ p ∈ ({5, 7} : Finset ℕ), (2 : ℝ) / (p : ℝ) ^ 2) + 81 / 1000 := by
        gcongr; exact sum_two_div_prime_sq_gt7 N
    _ ≤ 21 / 100 := by norm_num

private lemma two_pow_omega_odd_sqfree_le {g : ℕ} (hg : Squarefree g) (hodd : g % 2 = 1) :
    (2 ^ g.primeFactors.card : ℝ) ≤ 3 * Real.sqrt (Real.sqrt (g : ℝ)) := by
  have hg_pos : 0 < g := Nat.pos_of_ne_zero hg.ne_zero
  suffices h4 : (2 ^ g.primeFactors.card : ℝ) ^ 4 ≤ 81 * (g : ℝ) by
    have hnonneg : 0 ≤ (2 ^ g.primeFactors.card : ℝ) := by positivity
    have hrhs_nonneg : 0 ≤ 3 * Real.sqrt (Real.sqrt (g : ℝ)) := by positivity
    have hsq1 : (3 * Real.sqrt (Real.sqrt (g : ℝ))) ^ 4 = 81 * (g : ℝ) := by
      have hgR : (0 : ℝ) ≤ (g : ℝ) := by positivity
      calc (3 * Real.sqrt (Real.sqrt (g : ℝ))) ^ 4
          = 81 * ((Real.sqrt (Real.sqrt (g : ℝ))) ^ 2) ^ 2 := by ring
        _ = 81 * (Real.sqrt (g : ℝ)) ^ 2 := by rw [Real.sq_sqrt (Real.sqrt_nonneg _)]
        _ = 81 * (g : ℝ) := by rw [Real.sq_sqrt hgR]
    rw [← hsq1] at h4
    by_contra hlt
    push_neg at hlt
    have : (3 * Real.sqrt (Real.sqrt (g : ℝ))) ^ 4 < (2 ^ g.primeFactors.card : ℝ) ^ 4 := by gcongr
    linarith
  suffices hN : (2 ^ g.primeFactors.card) ^ 4 ≤ 81 * g by exact_mod_cast hN
  let s := g.primeFactors
  have hprod_le : ∏ p ∈ s, p ≤ g := Nat.le_of_dvd hg_pos (Nat.prod_primeFactors_dvd g)
  have hpow : (2 ^ s.card) ^ 4 = ∏ _p ∈ s, 16 := by
    rw [Finset.prod_const, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [hpow]
  let s1 := s.filter (fun p => p ≤ 13)
  let s2 := s.filter (fun p => ¬ p ≤ 13)
  have hsplit : ∏ _p ∈ s, 16 = (∏ _p ∈ s1, 16) * (∏ _p ∈ s2, 16) :=
    (Finset.prod_filter_mul_prod_filter_not s (fun p => p ≤ 13) (fun _ => 16)).symm
  have hsplit_p : ∏ p ∈ s, p = (∏ p ∈ s1, p) * (∏ p ∈ s2, p) :=
    (Finset.prod_filter_mul_prod_filter_not s (fun p => p ≤ 13) (fun p => p)).symm
  have hs2_le : ∏ _p ∈ s2, 16 ≤ ∏ p ∈ s2, p := by
    refine Finset.prod_le_prod' fun p hp => ?_
    simp only [Finset.mem_filter, s2] at hp
    have hpr := Nat.prime_of_mem_primeFactors hp.1
    have hgt13 : 14 ≤ p := by omega
    by_contra hlt
    have hcases : p = 14 ∨ p = 15 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hpr
  have hs1_sub : s1 ⊆ ({3, 5, 7, 11, 13} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_filter, s1] at hp
    have hpr := Nat.prime_of_mem_primeFactors hp.1
    have hne2 : p ≠ 2 := by
      intro h2; subst h2
      have := Nat.dvd_of_mem_primeFactors hp.1
      omega
    have hge2 := hpr.two_le
    have hle13 := hp.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases p <;> (try norm_num at hpr) <;> (try omega) <;> (try norm_num)
  have hs1_le : ∏ _p ∈ s1, 16 ≤ 81 * (∏ p ∈ s1, p) := by
    let T : Finset ℕ := {3, 5, 7, 11, 13}
    have hpos_rem : 0 < ∏ p ∈ T \ s1, p := Finset.prod_pos fun p hp => by
      have hp' := Finset.sdiff_subset hp
      simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp'
      rcases hp' with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hmul : (∏ _p ∈ s1, 16) * (∏ p ∈ T \ s1, p) ≤ (81 * ∏ p ∈ s1, p) * (∏ p ∈ T \ s1, p) := by
      calc (∏ _p ∈ s1, 16) * (∏ p ∈ T \ s1, p)
          ≤ (∏ _p ∈ s1, 16) * (∏ _p ∈ T \ s1, 16) := by
            refine Nat.mul_le_mul_left _ (Finset.prod_le_prod' fun p hp => ?_)
            have hp' := Finset.sdiff_subset hp
            simp only [T, Finset.mem_insert, Finset.mem_singleton] at hp'
            rcases hp' with rfl | rfl | rfl | rfl | rfl <;> norm_num
        _ = ∏ _p ∈ T, 16 := by rw [mul_comm, Finset.prod_sdiff hs1_sub]
        _ ≤ 81 * (∏ p ∈ T, p) := by decide
        _ = 81 * ((∏ p ∈ T \ s1, p) * (∏ p ∈ s1, p)) := by rw [Finset.prod_sdiff hs1_sub]
        _ = (81 * ∏ p ∈ s1, p) * (∏ p ∈ T \ s1, p) := by ring
    exact Nat.le_of_mul_le_mul_right hmul hpos_rem
  calc ∏ _p ∈ s, 16
      = (∏ _p ∈ s1, 16) * (∏ _p ∈ s2, 16) := hsplit
    _ ≤ (81 * ∏ p ∈ s1, p) * (∏ p ∈ s2, p) := Nat.mul_le_mul hs1_le hs2_le
    _ = 81 * (∏ p ∈ s, p) := by rw [hsplit_p]; ring
    _ ≤ 81 * g := Nat.mul_le_mul_left 81 hprod_le

-- Exact count of {m in [19, B] : m % 6 = 1 or m % 6 = 5} by direct induction!
private lemma card_mod6_15_exact (B : ℕ) (hB : 18 ≤ B) :
    3 * ((Finset.Icc 19 B).filter (fun m => m % 6 = 1 ∨ m % 6 = 5)).card +
      (if B % 6 = 4 then 1 else 0) =
      (B - 18) + (if B % 6 = 1 then 2 else if B % 6 = 2 ∨ B % 6 = 5 then 1 else 0) := by
  induction B, hB using Nat.le_induction with
  | base => simp
  | succ B hB ih =>
    have hIcc : Finset.Icc 19 (B + 1) = insert (B + 1) (Finset.Icc 19 B) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hIcc, Finset.filter_insert]
    have hnm : B + 1 ∉ (Finset.Icc 19 B).filter (fun m => m % 6 = 1 ∨ m % 6 = 5) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]; omega
    by_cases h1 : (B + 1) % 6 = 1 ∨ (B + 1) % 6 = 5
    · simp only [if_pos h1, Finset.card_insert_of_notMem hnm]
      split_ifs at ih ⊢ <;> omega
    · simp only [if_neg h1]
      split_ifs at ih ⊢ <;> omega

private lemma card_mod6_15_le (B : ℕ) (hB : 19 ≤ B) :
    3 * ((Finset.Icc 19 B).filter (fun m => m % 6 = 1 ∨ m % 6 = 5)).card ≤ B - 16 := by
  have h := card_mod6_15_exact B (by omega)
  split_ifs at h <;> omega

private lemma prod_telescope_16 (k : ℕ) :
    ∏ i : Fin k, ((3 * (i.val : ℝ) + 16) / (3 * (i.val : ℝ) + 19)) =
      (16 : ℝ) / (3 * (k : ℝ) + 16) := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_last, Fin.val_castSucc]
    rw [ih]
    push_cast
    have hpos : (0 : ℝ) < 3 * (m : ℝ) + 16 := by positivity
    field_simp
    ring

private lemma prod_one_sub_primes_ge19_cubed {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ 19 ≤ p) :
    (16 : ℝ) / (3 * (S.card : ℝ) + 16) ≤ (∏ p ∈ S, (1 - 1 / (p : ℝ))) ^ 3 := by
  let k := S.card
  let emb : Fin k ↪o ℕ := S.orderEmbOfFin rfl
  have hemb_mem : ∀ i : Fin k, emb i ∈ S := fun i => Finset.orderEmbOfFin_mem S rfl i
  have hemb_ge : ∀ i : Fin k, 3 * i.val + 19 ≤ emb i := by
    intro i
    have hpi := hS (emb i) (hemb_mem i)
    have hsub : (Finset.univ.filter (fun j : Fin k => j ≤ i)).image emb ⊆
        (Finset.Icc 19 (emb i)).filter (fun m => m % 6 = 1 ∨ m % 6 = 5) := by
      intro m hm
      rw [Finset.mem_image] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      have hpj := hS (emb j) (hemb_mem j)
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hpj.2, emb.monotone hj⟩, ?_⟩
      have hpr := hpj.1
      have hnd2 : ¬ 2 ∣ emb j := by
        intro h2
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hpr).mp h2
        omega
      have hnd3 : ¬ 3 ∣ emb j := by
        intro h3
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).mp h3
        omega
      omega
    have hcard_lhs : ((Finset.univ.filter (fun j : Fin k => j ≤ i)).image emb).card = i.val + 1 := by
      rw [Finset.card_image_of_injective _ emb.injective]
      have hfilt : Finset.univ.filter (fun j : Fin k => j ≤ i) =
          (Finset.range (i.val + 1)).attach.image
            (fun x => (⟨x.val, by have := Finset.mem_range.mp x.prop; omega⟩ : Fin k)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach]
        constructor
        · intro hj
          exact ⟨⟨j.val, Finset.mem_range.mpr (by exact Nat.lt_succ_of_le hj)⟩, by ext; rfl⟩
        · rintro ⟨⟨v, hv⟩, heq⟩
          have hv' : v < i.val + 1 := Finset.mem_range.mp hv
          have : j.val = v := congr_arg Fin.val heq.symm
          exact Nat.le_of_lt_succ (by omega)
      rw [hfilt, Finset.card_image_of_injective]
      · simp
      · intro x y h; ext; exact congr_arg Fin.val h
    have hcard_le := Finset.card_le_card hsub
    rw [hcard_lhs] at hcard_le
    have hb := card_mod6_15_le (emb i) hpi.2
    omega
  have hprod_eq : ∏ p ∈ S, (1 - 1 / (p : ℝ)) = ∏ i : Fin k, (1 - 1 / (emb i : ℝ)) := by
    have himg : Finset.univ.image emb = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩; exact hemb_mem i
      · intro hx
        have hx' : x ∈ (S : Set ℕ) := hx
        rw [← Finset.range_orderEmbOfFin S rfl] at hx'
        exact Set.mem_range.mp hx'
    rw [← himg, Finset.prod_image (fun a _ b _ h => emb.injective h)]
  rw [hprod_eq, ← Finset.prod_pow]
  have hstep : ∀ i : Fin k,
      (3 * (i.val : ℝ) + 16) / (3 * (i.val : ℝ) + 19) ≤ (1 - 1 / (emb i : ℝ)) ^ 3 := by
    intro i
    have hge : (3 * (i.val : ℝ) + 19) ≤ (emb i : ℝ) := by exact_mod_cast hemb_ge i
    have hu_pos : (0 : ℝ) < 3 * (i.val : ℝ) + 19 := by positivity
    have hmono : (1 - 1 / (3 * (i.val : ℝ) + 19)) ^ 3 ≤ (1 - 1 / (emb i : ℝ)) ^ 3 := by
      gcongr
      have : 0 ≤ 1 - 1 / (3 * (i.val : ℝ) + 19) := by
        rw [sub_nonneg, div_le_one hu_pos]; linarith
      exact this
    refine le_trans ?_ hmono
    let u : ℝ := 3 * (i.val : ℝ) + 19
    have hu : (19 : ℝ) ≤ u := by dsimp [u]; linarith [show (0 : ℝ) ≤ (i.val : ℝ) by positivity]
    have hrew1 : 3 * (i.val : ℝ) + 16 = u - 3 := by dsimp [u]; ring
    have hrew2 : 1 - 1 / u = (u - 1) / u := by field_simp
    rw [hrew1, hrew2, div_pow, div_le_div_iff₀ (by linarith) (by positivity)]
    nlinarith [sq_nonneg u]
  calc (16 : ℝ) / (3 * (k : ℝ) + 16)
      = ∏ i : Fin k, ((3 * (i.val : ℝ) + 16) / (3 * (i.val : ℝ) + 19)) := (prod_telescope_16 k).symm
    _ ≤ ∏ i : Fin k, (1 - 1 / (emb i : ℝ)) ^ 3 := by
        refine Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hstep i)

private lemma phi_main_cubed_ge_large {g M : ℕ} (hg : Squarefree g) (hodd : g % 2 = 1)
    (hg_le : g ≤ M + 1) (hM : 200000 ≤ M) (Y1 : ℕ) :
    let phi_r := ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))
    let S_small := ∑ p ∈ (Finset.Icc 3 Y1).filter (fun p => p.Prime ∧ ¬ p ∣ g), (2 : ℝ) / (p : ℝ) ^ 2
    0 ≤ phi_r * (1 - S_small) ∧
      (158 / 1000 : ℝ) / Real.log (M : ℝ) ≤ (phi_r * (1 - S_small)) ^ 3 := by
  intro phi_r S_small
  have hg_pos : 0 < g := Nat.pos_of_ne_zero hg.ne_zero
  have hS_small_le3 : S_small ≤ 43 / 100 := by
    calc S_small ≤ ∑ p ∈ (Finset.Icc 3 Y1).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro p hp; simp only [Finset.mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
      _ ≤ 43 / 100 := sum_two_div_prime_sq_ge3 Y1
  have hphi_nonneg : 0 ≤ phi_r := by
    refine Finset.prod_nonneg fun p hp => ?_
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    rw [sub_nonneg, div_le_one (by linarith)]; exact hp1
  have hmain_nonneg : 0 ≤ phi_r * (1 - S_small) :=
    mul_nonneg hphi_nonneg (by linarith)
  refine ⟨hmain_nonneg, ?_⟩
  -- Split g.primeFactors into {3}, primes in [5, 17], and primes >= 19
  let P_mid := g.primeFactors.filter (fun p => 5 ≤ p ∧ p ≤ 17)
  let P_big := g.primeFactors.filter (fun p => 19 ≤ p)
  have hP_mid_sub : P_mid ⊆ ({5, 7, 11, 13, 17} : Finset ℕ) := by
    intro p hp
    simp only [Finset.mem_filter, P_mid] at hp
    have hpr := Nat.prime_of_mem_primeFactors hp.1
    have h1 := hp.2.1; have h2 := hp.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases p <;> (try norm_num at hpr) <;> (try norm_num)
  have hP_mid_ge : (9216 / 17017 : ℝ) ≤ ∏ p ∈ P_mid, (1 - 1 / (p : ℝ)) := by
    have hprod_all : ∏ p ∈ ({5, 7, 11, 13, 17} : Finset ℕ), (1 - 1 / (p : ℝ)) = 9216 / 17017 := by
      norm_num
    rw [← hprod_all]
    have hle : ∀ p ∈ ({5, 7, 11, 13, 17} : Finset ℕ), 0 ≤ 1 - 1 / (p : ℝ) ∧ 1 - 1 / (p : ℝ) ≤ 1 := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hsplit := (Finset.prod_sdiff hP_mid_sub (f := fun p : ℕ => (1 - 1 / (p : ℝ)))).symm
    rw [hsplit]
    have hsdiff_le1 : ∏ p ∈ ({5, 7, 11, 13, 17} : Finset ℕ) \ P_mid, (1 - 1 / (p : ℝ)) ≤ 1 :=
      Finset.prod_le_one (fun p hp => (hle p (Finset.sdiff_subset hp)).1)
        (fun p hp => (hle p (Finset.sdiff_subset hp)).2)
    have hmid_nonneg : 0 ≤ ∏ p ∈ P_mid, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg fun p hp => (hle p (hP_mid_sub hp)).1
    nlinarith
  have hP_big_spec : ∀ p ∈ P_big, p.Prime ∧ 19 ≤ p := by
    intro p hp
    simp only [Finset.mem_filter, P_big] at hp
    exact ⟨Nat.prime_of_mem_primeFactors hp.1, hp.2⟩
  have hP_big_cubed := prod_one_sub_primes_ge19_cubed hP_big_spec
  -- Bound P_big.card via 19^k <= M + 1
  have h19_pow : 19 ^ P_big.card ≤ M + 1 := by
    calc 19 ^ P_big.card
        = ∏ _p ∈ P_big, 19 := by simp
      _ ≤ ∏ p ∈ P_big, p := Finset.prod_le_prod' fun p hp => (hP_big_spec p hp).2
      _ ≤ ∏ p ∈ g.primeFactors, p :=
          Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
            (fun p hp _ => (Nat.prime_of_mem_primeFactors hp).one_le)
      _ ≤ g := Nat.le_of_dvd hg_pos (Nat.prod_primeFactors_dvd g)
      _ ≤ M + 1 := hg_le
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlog2_gt : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog3_gt : (1.098612 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlog19_gt : (2.929 : ℝ) < Real.log 19 := by
    have hpow : ((3 : ℝ) ^ 8) < ((19 : ℝ) ^ 3) := by norm_num
    have hlog := Real.log_lt_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog
    linarith
  have hlogM_gt : (12.188 : ℝ) < Real.log (M : ℝ) := by
    have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (M : ℝ) := by
      have : (200000 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hlog := Real.log_lt_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    push_cast at hlog
    linarith
  have hlogM1_le : Real.log ((M : ℝ) + 1) ≤ Real.log (M : ℝ) + 1 / (200000 : ℝ) := by
    have hdiv : ((M : ℝ) + 1) / (M : ℝ) = 1 + 1 / (M : ℝ) := by field_simp
    have hle1 : Real.log (1 + 1 / (M : ℝ)) ≤ 1 / (M : ℝ) := by
      have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / (M : ℝ))
      linarith
    rw [show Real.log ((M : ℝ) + 1) = Real.log (M : ℝ) + Real.log (((M : ℝ) + 1) / (M : ℝ)) by
      rw [Real.log_div (by linarith) hM_pos.ne']; ring]
    rw [hdiv]
    have hinv : 1 / (M : ℝ) ≤ 1 / (200000 : ℝ) := by
      gcongr; exact_mod_cast hM
    linarith
  have hk_log : (P_big.card : ℝ) * Real.log 19 ≤ Real.log ((M : ℝ) + 1) := by
    have hR : ((19 : ℝ) ^ P_big.card) ≤ (M : ℝ) + 1 := by exact_mod_cast h19_pow
    have := Real.log_le_log (by positivity) hR
    rwa [Real.log_pow] at this
  have hden_le : 3 * (P_big.card : ℝ) + 16 ≤ (234 / 100 : ℝ) * Real.log (M : ℝ) := by
    have hk_le : (P_big.card : ℝ) ≤ Real.log ((M : ℝ) + 1) / 2.929 := by
      rw [le_div_iff₀ (by norm_num)]
      have hk0 : (0 : ℝ) ≤ (P_big.card : ℝ) := by positivity
      nlinarith
    nlinarith
  have hP_big_lb : (16 : ℝ) / ((234 / 100 : ℝ) * Real.log (M : ℝ)) ≤
      (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) ^ 3 := by
    refine le_trans ?_ hP_big_cubed
    gcongr
  -- Now split on 3 ∣ g!
  have hdisj_mb : Disjoint P_mid P_big := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_filter, P_mid, P_big] at hp1 hp2
    omega
  have hpart : ∀ p ∈ g.primeFactors, p = 3 ∨ p ∈ P_mid ∨ p ∈ P_big := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hne2 : p ≠ 2 := by
      intro h2; subst h2
      have := Nat.dvd_of_mem_primeFactors hp
      omega
    have hge2 := hpr.two_le
    have hne4 : p ≠ 4 := by rintro rfl; norm_num at hpr
    by_cases h3 : p = 3
    · left; exact h3
    · by_cases h17 : p ≤ 17
      · right; left; exact Finset.mem_filter.mpr ⟨hp, by omega, h17⟩
      · right; right; exact Finset.mem_filter.mpr ⟨hp, by
          have hne18 : p ≠ 18 := by rintro rfl; norm_num at hpr
          omega⟩
  have hP_big_nonneg : 0 ≤ ∏ p ∈ P_big, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hP_big_spec p hp).1.one_le
    rw [sub_nonneg, div_le_one (by linarith)]; exact h1
  have hcoeff : (2852 / 10000 : ℝ) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) ≤
      phi_r * (1 - S_small) := by
    by_cases h3g : 3 ∣ g
    · have h3mem : 3 ∈ g.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_three, h3g, hg.ne_zero⟩
      have hpf_eq : g.primeFactors = insert 3 (P_mid ∪ P_big) := by
        ext p; simp only [Finset.mem_insert, Finset.mem_union]
        constructor
        · exact hpart p
        · rintro (rfl | h | h)
          · exact h3mem
          · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1
      have h3nm : 3 ∉ P_mid ∪ P_big := by
        simp only [Finset.mem_union, Finset.mem_filter, P_mid, P_big]; omega
      have hphi_eq : phi_r = (2 / 3 : ℝ) * (∏ p ∈ P_mid, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by
        dsimp [phi_r]
        rw [hpf_eq, Finset.prod_insert h3nm, Finset.prod_union hdisj_mb]
        norm_num; ring
      have hS_le5 : S_small ≤ 21 / 100 := by
        calc S_small ≤ ∑ p ∈ (Finset.Icc 5 Y1).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
              intro p hp
              simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
              refine ⟨⟨?_, hp.1.2⟩, hp.2.1⟩
              have hne3 : p ≠ 3 := fun h => hp.2.2 (h ▸ h3g)
              have hpr := hp.2.1
              have hne4 : p ≠ 4 := by rintro rfl; norm_num at hpr
              omega
          _ ≤ 21 / 100 := sum_two_div_prime_sq_ge5 Y1
      rw [hphi_eq]
      have hc1 : (2852 / 10000 : ℝ) ≤ (2 / 3 : ℝ) * (9216 / 17017 : ℝ) * (1 - 21 / 100 : ℝ) := by
        norm_num
      have hmid_nn : 0 ≤ ∏ p ∈ P_mid, (1 - 1 / (p : ℝ)) := by linarith
      calc (2852 / 10000 : ℝ) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ)))
          ≤ ((2 / 3 : ℝ) * (9216 / 17017 : ℝ) * (1 - 21 / 100 : ℝ)) *
              (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by gcongr
        _ ≤ ((2 / 3 : ℝ) * (∏ p ∈ P_mid, (1 - 1 / (p : ℝ))) * (1 - S_small)) *
              (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by
            gcongr
        _ = (2 / 3 : ℝ) * (∏ p ∈ P_mid, (1 - 1 / (p : ℝ))) *
              (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) * (1 - S_small) := by ring
    · have hpf_eq : g.primeFactors = P_mid ∪ P_big := by
        ext p; simp only [Finset.mem_union]
        constructor
        · intro hp
          rcases hpart p hp with rfl | h | h
          · exact (h3g (Nat.dvd_of_mem_primeFactors hp)).elim
          · left; exact h
          · right; exact h
        · rintro (h | h)
          · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1
      have hphi_eq : phi_r = (∏ p ∈ P_mid, (1 - 1 / (p : ℝ))) *
          (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by
        dsimp [phi_r]
        rw [hpf_eq, Finset.prod_union hdisj_mb]
      rw [hphi_eq]
      have hc1 : (2852 / 10000 : ℝ) ≤ (9216 / 17017 : ℝ) * (1 - 43 / 100 : ℝ) := by norm_num
      have hmid_nn : 0 ≤ ∏ p ∈ P_mid, (1 - 1 / (p : ℝ)) := by linarith
      calc (2852 / 10000 : ℝ) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ)))
          ≤ ((9216 / 17017 : ℝ) * (1 - 43 / 100 : ℝ)) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by gcongr
        _ ≤ ((∏ p ∈ P_mid, (1 - 1 / (p : ℝ))) * (1 - S_small)) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by
            gcongr
        _ = (∏ p ∈ P_mid, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) * (1 - S_small) := by ring
  have hcubed : ((2852 / 10000 : ℝ) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ)))) ^ 3 ≤
      (phi_r * (1 - S_small)) ^ 3 := by
    gcongr
  rw [mul_pow] at hcubed
  have hconst : (158 / 1000 : ℝ) ≤ (2852 / 10000 : ℝ) ^ 3 * (16 / (234 / 100 : ℝ)) := by norm_num
  calc (158 / 1000 : ℝ) / Real.log (M : ℝ)
      ≤ ((2852 / 10000 : ℝ) ^ 3 * (16 / (234 / 100 : ℝ))) / Real.log (M : ℝ) := by
        gcongr
    _ = (2852 / 10000 : ℝ) ^ 3 * ((16 : ℝ) / ((234 / 100 : ℝ) * Real.log (M : ℝ))) := by ring
    _ ≤ (2852 / 10000 : ℝ) ^ 3 * (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) ^ 3 := by
        gcongr
    _ ≤ (phi_r * (1 - S_small)) ^ 3 := hcubed

private lemma primes_ge11_bounds {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ 11 ≤ p) :
    let prodS := ∏ p ∈ S, p
    let phiS := ∏ p ∈ S, (1 - 1 / (p : ℝ))
    (S.card = 0 → phiS = 1) ∧
    (S.card = 1 → 11 ≤ prodS ∧ (10 / 11 : ℝ) ≤ phiS) ∧
    (S.card = 2 → 143 ≤ prodS ∧ (120 / 143 : ℝ) ≤ phiS) ∧
    (S.card = 3 → 2431 ≤ prodS ∧ (1920 / 2431 : ℝ) ≤ phiS) ∧
    (S.card = 4 → 46189 ≤ prodS ∧ (34560 / 46189 : ℝ) ≤ phiS) ∧
    (S.card ≥ 5 → 1062347 ≤ prodS) := by
  intro prodS phiS
  let k := S.card
  let emb : Fin k ↪o ℕ := S.orderEmbOfFin rfl
  have hemb_mem : ∀ i : Fin k, emb i ∈ S := fun i => Finset.orderEmbOfFin_mem S rfl i
  have hemb_pr : ∀ i : Fin k, (emb i).Prime ∧ 11 ≤ emb i := fun i => hS (emb i) (hemb_mem i)
  have himg_S : Finset.univ.image emb = S := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact hemb_mem i
    · intro hx
      have hx' : x ∈ (S : Set ℕ) := hx
      rw [← Finset.range_orderEmbOfFin S rfl] at hx'
      exact Set.mem_range.mp hx'
  have hprod_eq : prodS = ∏ i : Fin k, emb i := by
    dsimp [prodS]
    rw [← himg_S, Finset.prod_image (fun a _ b _ h => emb.injective h)]
  have hphi_eq : phiS = ∏ i : Fin k, (1 - 1 / (emb i : ℝ)) := by
    dsimp [phiS]
    rw [← himg_S, Finset.prod_image (fun a _ b _ h => emb.injective h)]
  have h0 : ∀ i : Fin k, 11 ≤ emb i := fun i => (hemb_pr i).2
  have h1 : ∀ i : Fin k, 1 ≤ i.val → 13 ≤ emb i := by
    intro i hi
    let i0 : Fin k := ⟨0, by omega⟩
    have hlt : emb i0 < emb i := emb.strictMono (show i0 < i from hi)
    have hge : 11 ≤ emb i0 := h0 i0
    have hpr := (hemb_pr i).1
    have hne12 : emb i ≠ 12 := by intro h; rw [h] at hpr; norm_num at hpr
    omega
  have h2 : ∀ i : Fin k, 2 ≤ i.val → 17 ≤ emb i := by
    intro i hi
    let i1 : Fin k := ⟨1, by omega⟩
    have hlt : emb i1 < emb i := emb.strictMono (show i1 < i from hi)
    have hge : 13 ≤ emb i1 := h1 i1 (by dsimp [i1]; omega)
    have hpr := (hemb_pr i).1
    have hne14 : emb i ≠ 14 := by intro h; rw [h] at hpr; norm_num at hpr
    have hne15 : emb i ≠ 15 := by intro h; rw [h] at hpr; norm_num at hpr
    have hne16 : emb i ≠ 16 := by intro h; rw [h] at hpr; norm_num at hpr
    omega
  have h3 : ∀ i : Fin k, 3 ≤ i.val → 19 ≤ emb i := by
    intro i hi
    let i2 : Fin k := ⟨2, by omega⟩
    have hlt : emb i2 < emb i := emb.strictMono (show i2 < i from hi)
    have hge : 17 ≤ emb i2 := h2 i2 (by dsimp [i2]; omega)
    have hpr := (hemb_pr i).1
    have hne18 : emb i ≠ 18 := by intro h; rw [h] at hpr; norm_num at hpr
    omega
  have h4 : ∀ i : Fin k, 4 ≤ i.val → 23 ≤ emb i := by
    intro i hi
    let i3 : Fin k := ⟨3, by omega⟩
    have hlt : emb i3 < emb i := emb.strictMono (show i3 < i from hi)
    have hge : 19 ≤ emb i3 := h3 i3 (by dsimp [i3]; omega)
    have hpr := (hemb_pr i).1
    have hne20 : emb i ≠ 20 := by intro h; rw [h] at hpr; norm_num at hpr
    have hne21 : emb i ≠ 21 := by intro h; rw [h] at hpr; norm_num at hpr
    have hne22 : emb i ≠ 22 := by intro h; rw [h] at hpr; norm_num at hpr
    omega
  have hmono_one_sub : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b →
      (1 - 1 / (a : ℝ)) ≤ (1 - 1 / (b : ℝ)) := by
    intro a b ha hab
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hk0
    have : S = ∅ := Finset.card_eq_zero.mp hk0
    simp [phiS, this]
  · intro hk1
    rw [hprod_eq, hphi_eq]
    have hle : 11 ≤ emb ⟨0, by omega⟩ := h0 ⟨0, by omega⟩
    have hp1 : ∏ i : Fin k, emb i = emb ⟨0, by omega⟩ := by
      have : ∀ i : Fin k, i = ⟨0, by omega⟩ := fun i => by ext; omega
      rw [Finset.prod_eq_single ⟨0, by omega⟩ (fun i _ hi => absurd (this i) hi) (by simp)]
    have hph1 : ∏ i : Fin k, (1 - 1 / (emb i : ℝ)) = 1 - 1 / (emb ⟨0, by omega⟩ : ℝ) := by
      have : ∀ i : Fin k, i = ⟨0, by omega⟩ := fun i => by ext; omega
      rw [Finset.prod_eq_single ⟨0, by omega⟩ (fun i _ hi => absurd (this i) hi) (by simp)]
    rw [hp1, hph1]
    exact ⟨hle, by linarith [hmono_one_sub (by omega : 1 ≤ 11) hle]⟩
  · intro hk2
    rw [hprod_eq, hphi_eq]
    let he : Fin k ≃ Fin 2 := finCongr hk2
    rw [Fintype.prod_equiv he _ (fun j => emb (he.symm j)) (fun i => by simp),
        Fintype.prod_equiv he _ (fun j => 1 - 1 / (emb (he.symm j) : ℝ)) (fun i => by simp)]
    simp only [Fin.prod_univ_two]
    have hb0 : 11 ≤ emb (he.symm 0) := h0 _
    have hb1 : 13 ≤ emb (he.symm 1) := h1 _ (by dsimp [he]; simp)
    refine ⟨by nlinarith, ?_⟩
    have hm0 := hmono_one_sub (by omega : 1 ≤ 11) hb0
    have hm1 := hmono_one_sub (by omega : 1 ≤ 13) hb1
    nlinarith
  · intro hk3
    rw [hprod_eq, hphi_eq]
    let he : Fin k ≃ Fin 3 := finCongr hk3
    rw [Fintype.prod_equiv he _ (fun j => emb (he.symm j)) (fun i => by simp),
        Fintype.prod_equiv he _ (fun j => 1 - 1 / (emb (he.symm j) : ℝ)) (fun i => by simp)]
    simp only [Fin.prod_univ_three]
    have hb0 : 11 ≤ emb (he.symm 0) := h0 _
    have hb1 : 13 ≤ emb (he.symm 1) := h1 _ (by dsimp [he]; simp)
    have hb2 : 17 ≤ emb (he.symm 2) := h2 _ (by dsimp [he]; simp)
    have h01 : 143 ≤ emb (he.symm 0) * emb (he.symm 1) := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    have hm0 := hmono_one_sub (by omega : 1 ≤ 11) hb0
    have hm1 := hmono_one_sub (by omega : 1 ≤ 13) hb1
    have hm2 := hmono_one_sub (by omega : 1 ≤ 17) hb2
    have hp1 : (10 / 11 : ℝ) * (12 / 13) ≤ (1 - 1 / (emb (he.symm 0) : ℝ)) * (1 - 1 / (emb (he.symm 1) : ℝ)) := by
      nlinarith
    nlinarith
  · intro hk4
    rw [hprod_eq, hphi_eq]
    let he : Fin k ≃ Fin 4 := finCongr hk4
    rw [Fintype.prod_equiv he _ (fun j => emb (he.symm j)) (fun i => by simp),
        Fintype.prod_equiv he _ (fun j => 1 - 1 / (emb (he.symm j) : ℝ)) (fun i => by simp)]
    simp only [Fin.prod_univ_four]
    have hb0 : 11 ≤ emb (he.symm 0) := h0 _
    have hb1 : 13 ≤ emb (he.symm 1) := h1 _ (by dsimp [he]; simp)
    have hb2 : 17 ≤ emb (he.symm 2) := h2 _ (by dsimp [he]; simp)
    have hb3 : 19 ≤ emb (he.symm 3) := h3 _ (by dsimp [he]; simp)
    have h01 : 143 ≤ emb (he.symm 0) * emb (he.symm 1) := by nlinarith
    have h012 : 2431 ≤ emb (he.symm 0) * emb (he.symm 1) * emb (he.symm 2) := by nlinarith
    refine ⟨by nlinarith, ?_⟩
    have hm0 := hmono_one_sub (by omega : 1 ≤ 11) hb0
    have hm1 := hmono_one_sub (by omega : 1 ≤ 13) hb1
    have hm2 := hmono_one_sub (by omega : 1 ≤ 17) hb2
    have hm3 := hmono_one_sub (by omega : 1 ≤ 19) hb3
    have hp1 : (10 / 11 : ℝ) * (12 / 13) ≤ (1 - 1 / (emb (he.symm 0) : ℝ)) * (1 - 1 / (emb (he.symm 1) : ℝ)) := by
      nlinarith
    have hp2 : (10 / 11 : ℝ) * (12 / 13) * (16 / 17) ≤
        (1 - 1 / (emb (he.symm 0) : ℝ)) * (1 - 1 / (emb (he.symm 1) : ℝ)) * (1 - 1 / (emb (he.symm 2) : ℝ)) := by
      nlinarith
    nlinarith
  · intro hk5
    rw [hprod_eq]
    calc 1062347 = ∏ j : Fin 5, (![11, 13, 17, 19, 23] : Fin 5 → ℕ) j := by decide
      _ ≤ ∏ j : Fin 5, emb ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk5⟩ := by
          refine Finset.prod_le_prod' fun j _ => ?_
          fin_cases j
          · exact h0 _
          · exact h1 _ (by dsimp; decide)
          · exact h2 _ (by dsimp; decide)
          · exact h3 _ (by dsimp; decide)
          · exact h4 _ (by dsimp; decide)
      _ = ∏ i ∈ Finset.univ.filter (fun i : Fin k => i.val < 5), emb i := by
          refine Finset.prod_bij (fun j _ => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hk5⟩ : Fin k)) ?_ ?_ ?_ ?_
          · intro j _; simp [j.isLt]
          · intro j1 _ j2 _ h; exact Fin.ext (congr_arg (Fin.val : Fin k → ℕ) h)
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact ⟨⟨i.val, hi⟩, Finset.mem_univ _, by ext; rfl⟩
          · intro j _; rfl
      _ ≤ ∏ i : Fin k, emb i :=
          Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
            (fun i _ _ => (hemb_pr i).1.one_le)

/-!
### Section 6: Unified sieve framework and final proof of H2
-/

private lemma card_odd_primes_lt_sqrt_le (N Y : ℕ) (hY : 2 ≤ Y) :
    (((Finset.Icc (Y + 1) N).filter (fun p => p.Prime ∧ p ^ 2 < 2 * N)).card : ℝ) ≤
      Real.sqrt (2 * (N : ℝ)) / 2 := by
  let K : ℕ := Nat.sqrt (2 * N)
  have hsub : (Finset.Icc (Y + 1) N).filter (fun p => p.Prime ∧ p ^ 2 < 2 * N) ⊆
      (Finset.Icc 1 (K / 2)).image (fun t => 2 * t + 1) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    have hge3 : 3 ≤ p := by omega
    have hodd : p % 2 = 1 := by
      have := hp.2.1.eq_two_or_odd; omega
    have hp_le_K : p ≤ K := Nat.le_sqrt.mpr (by simpa [sq] using hp.2.2.le)
    rw [Finset.mem_image]
    refine ⟨p / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  have hcard : ((Finset.Icc (Y + 1) N).filter (fun p => p.Prime ∧ p ^ 2 < 2 * N)).card ≤ K / 2 := by
    calc _ ≤ ((Finset.Icc 1 (K / 2)).image (fun t => 2 * t + 1)).card := Finset.card_le_card hsub
      _ = (Finset.Icc 1 (K / 2)).card := Finset.card_image_of_injective _ (fun a b h => by omega)
      _ = K / 2 := by simp
  have hK_le : (K : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have hK : K * K ≤ 2 * N := Nat.sqrt_le (2 * N)
    rw [sq]; exact_mod_cast hK
  have hdiv : ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast Nat.div_mul_le_self K 2
  have hcR : (((Finset.Icc (Y + 1) N).filter (fun p => p.Prime ∧ p ^ 2 < 2 * N)).card : ℝ) ≤
      ((K / 2 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

private lemma sieve_master_bound {n N a b g pMax Y1 : ℕ}
    (hY1_odd : Y1 % 2 = 1) (hY1_ge : 2 ≤ Y1)
    (hg : Squarefree g) (hg_odd : g % 2 = 1)
    (ha : a = 1 ∨ a = 2) (hab : a * b = 2 * b) (hb1 : b ≤ 1)
    (hN_le : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j ∧ 1 ≤ a * j - b ∧ (a * j - b) ^ 2 < n)
    (hno4 : ∀ j ∈ Finset.Icc 1 N, ¬ 4 ∣ n - (a * j - b) ^ 2)
    (hno_g : ∀ j ∈ Finset.Icc 1 N, (a * j - b).Coprime g →
      ∀ p : ℕ, p.Prime → p ∣ g → ¬ p ^ 2 ∣ n - (a * j - b) ^ 2)
    (E : Finset ℕ)
    (hcover : ¬ OMA.S_oeis_a085265.IsTerm n →
      ∀ j ∈ Finset.Icc 1 N, (a * j - b).Coprime g →
        j ∈ E ∨ ∃ p ∈ (Finset.Icc 3 pMax).filter (fun p => p.Prime ∧ ¬ p ∣ g ∧ ¬ p ∣ n),
          p ^ 2 ∣ n - (a * j - b) ^ 2)
    (htail_ub : ℝ)
    (htail : ∑ p ∈ (Finset.Icc (Y1 + 1) pMax).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 ≤ htail_ub)
    (hstrict :
      let phi_r := ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))
      let S_sm_set := (Finset.Icc 3 Y1).filter (fun p => p.Prime ∧ ¬ p ∣ g)
      let S_sm := ∑ p ∈ S_sm_set, (2 : ℝ) / (p : ℝ) ^ 2
      ((2 ^ g.primeFactors.card : ℝ) - 1) +
        2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) +
        (N : ℝ) * htail_ub +
        Real.sqrt (2 * (N : ℝ)) / 2 +
        (Nat.primeCounting pMax : ℝ) +
        (E.card : ℝ) <
      (N : ℝ) * phi_r * (1 - S_sm)) :
    OMA.S_oeis_a085265.IsTerm n := by
  by_contra hnot
  let J := (Finset.Icc 1 N).filter (fun j => (a * j - b).Coprime g)
  let P_all := (Finset.Icc 3 pMax).filter (fun p => p.Prime ∧ ¬ p ∣ g ∧ ¬ p ∣ n)
  let Bad : ℕ → Finset ℕ := fun p => J.filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2)
  have hJ_sub : J ⊆ E ∪ P_all.biUnion Bad := by
    intro j hj
    simp only [Finset.mem_filter, J] at hj
    simp only [Finset.mem_union, Finset.mem_biUnion, Bad]
    rcases hcover hnot j hj.1 hj.2 with hE | ⟨p, hp, hdp⟩
    · left; exact hE
    · right; exact ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr hj, hdp⟩⟩
  have hJ_card : (J.card : ℝ) ≤ (E.card : ℝ) + ∑ p ∈ P_all, ((Bad p).card : ℝ) := by
    have h1 : J.card ≤ E.card + (P_all.biUnion Bad).card :=
      (Finset.card_le_card hJ_sub).trans (Finset.card_union_le _ _)
    have h2 : (P_all.biUnion Bad).card ≤ ∑ p ∈ P_all, (Bad p).card := Finset.card_biUnion_le
    exact_mod_cast h1.trans (Nat.add_le_add_left h2 _)
  have hcop_ag : a.Coprime g := by
    rcases ha with rfl | rfl
    · simp
    · exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hg_odd)
  have hJ_lb := card_coprime_linear_ge N a b g hg hcop_ag (fun j hj => (hN_le j hj).1)
  -- Split P_all into p <= Y1 and p > Y1
  let P_sm := P_all.filter (fun p => p ≤ Y1)
  let P_lg := P_all.filter (fun p => ¬ p ≤ Y1)
  have hsum_split : ∑ p ∈ P_all, ((Bad p).card : ℝ) =
      (∑ p ∈ P_sm, ((Bad p).card : ℝ)) + (∑ p ∈ P_lg, ((Bad p).card : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not P_all (fun p => p ≤ Y1) _).symm
  have hb_le : ∀ j ∈ Finset.Icc 1 N, b ≤ a * j ∧ (a * j - b) ^ 2 ≤ n :=
    fun j hj => ⟨(hN_le j hj).1, (hN_le j hj).2.2.le⟩
  -- Bound small primes p <= Y1 via Mobius
  let phi_r := ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))
  let S_sm_set := (Finset.Icc 3 Y1).filter (fun p => p.Prime ∧ ¬ p ∣ g)
  have hP_sm_sub : P_sm ⊆ S_sm_set := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc, P_sm, P_all, S_sm_set] at hp ⊢
    exact ⟨⟨hp.1.1.1, hp.2⟩, hp.1.2.1, hp.1.2.2.1⟩
  have hsm_ub : ∑ p ∈ P_sm, ((Bad p).card : ℝ) ≤
      (N : ℝ) * phi_r * (∑ p ∈ S_sm_set, (2 : ℝ) / (p : ℝ) ^ 2) +
      2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) := by
    calc ∑ p ∈ P_sm, ((Bad p).card : ℝ)
        ≤ ∑ p ∈ P_sm, (2 * ((N : ℝ) / (p : ℝ) ^ 2 * phi_r + (2 ^ g.primeFactors.card : ℝ))) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [Finset.mem_filter, Finset.mem_Icc, P_sm, P_all] at hp
          have hp2 : p ≠ 2 := by omega
          have hBad_eq : Bad p = (Finset.Icc 1 N).filter
              (fun j => (a * j - b).Coprime g ∧ p ^ 2 ∣ n - (a * j - b) ^ 2) := by
            ext j; simp [Bad, J, and_assoc]
          rw [hBad_eq]
          exact bad_p_card_mobius_le hp.1.2.1 hp2 hp.1.2.2.2 hab ha hg hcop_ag hp.1.2.2.1 hb_le
      _ ≤ ∑ p ∈ S_sm_set, (2 * ((N : ℝ) / (p : ℝ) ^ 2 * phi_r + (2 ^ g.primeFactors.card : ℝ))) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hP_sm_sub fun p _ _ => ?_
          have hphi_nn : 0 ≤ phi_r := Finset.prod_nonneg fun q hq => by
            have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
            rw [sub_nonneg, div_le_one (by linarith)]; exact hq1
          positivity
      _ = (N : ℝ) * phi_r * (∑ p ∈ S_sm_set, (2 : ℝ) / (p : ℝ) ^ 2) +
          2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_congr rfl (fun p _ => by ring : ∀ p ∈ S_sm_set,
            2 * ((N : ℝ) / (p : ℝ) ^ 2 * phi_r + (2 ^ g.primeFactors.card : ℝ)) =
            (N : ℝ) * phi_r * (2 / (p : ℝ) ^ 2) + 2 * (2 ^ g.primeFactors.card : ℝ))]
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  -- Bound larger primes p > Y1
  have hlg_ub : ∑ p ∈ P_lg, ((Bad p).card : ℝ) ≤
      (N : ℝ) * htail_ub + Real.sqrt (2 * (N : ℝ)) / 2 + (Nat.primeCounting pMax : ℝ) := by
    let P_med := P_lg.filter (fun p => p ^ 2 < 2 * N)
    let P_big := P_lg.filter (fun p => ¬ p ^ 2 < 2 * N)
    have hlg_sp : ∑ p ∈ P_lg, ((Bad p).card : ℝ) =
        (∑ p ∈ P_med, ((Bad p).card : ℝ)) + (∑ p ∈ P_big, ((Bad p).card : ℝ)) :=
      (Finset.sum_filter_add_sum_filter_not P_lg (fun p => p ^ 2 < 2 * N) _).symm
    have hmed_ub : ∑ p ∈ P_med, ((Bad p).card : ℝ) ≤
        ∑ p ∈ P_med, (2 * ((N : ℝ) / (p : ℝ) ^ 2) + 1 + 1) := by
      refine Finset.sum_le_sum fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc, P_med, P_lg, P_all] at hp
      have hp2 : p ≠ 2 := by omega
      have hsub : Bad p ⊆ (Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2) := by
        intro j hj; simp only [Finset.mem_filter, Bad, J] at hj ⊢; exact ⟨hj.1.1, hj.2⟩
      have hle : ((Bad p).card : ℝ) ≤
          (((Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [bad_p_card_direct_le hp.1.1.2.1 hp2 hp.1.1.2.2.2 hab ha hb_le]
    have hbig_ub : ∑ p ∈ P_big, ((Bad p).card : ℝ) ≤ ∑ _p ∈ P_big, (1 : ℝ) := by
      refine Finset.sum_le_sum fun p hp => ?_
      simp only [Finset.mem_filter, Finset.mem_Icc, P_big, P_lg, P_all] at hp
      have hp2 : p ≠ 2 := by omega
      have hsub : Bad p ⊆ (Finset.Icc 1 N).filter (fun j => p ^ 2 ∣ n - (a * j - b) ^ 2) := by
        intro j hj; simp only [Finset.mem_filter, Bad, J] at hj ⊢; exact ⟨hj.1.1, hj.2⟩
      have h1 := (Finset.card_le_card hsub).trans
        (bad_p_card_le_one_of_large hp.1.1.2.1 hp2 hp.1.1.2.2.2 hab ha hb_le hb1 (by omega))
      exact_mod_cast h1
    have hmed_sub_tail : P_med ⊆ (Finset.Icc (Y1 + 1) pMax).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, P_med, P_lg, P_all] at hp ⊢
      exact ⟨⟨by omega, hp.1.1.1.2⟩, hp.1.1.2.1⟩
    have hmed_sub_sq : P_med ⊆ (Finset.Icc (Y1 + 1) N).filter (fun p => p.Prime ∧ p ^ 2 < 2 * N) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, P_med, P_lg, P_all] at hp ⊢
      have hp_le_N : p ≤ N := by
        have h3 : 3 ≤ p := hp.1.1.1.1
        nlinarith [hp.2]
      exact ⟨⟨by omega, hp_le_N⟩, hp.1.1.2.1, hp.2⟩
    have hlg_sub_pi : P_lg ⊆ (Finset.Icc 1 pMax).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, P_lg, P_all] at hp ⊢
      exact ⟨⟨by omega, hp.1.1.2⟩, hp.1.2.1⟩
    have hcard_lg_le_pi : (P_lg.card : ℝ) ≤ (Nat.primeCounting pMax : ℝ) := by
      have hpi : Nat.primeCounting pMax = ((Finset.Icc 1 pMax).filter Nat.Prime).card := by
        rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
        congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
        constructor
        · rintro ⟨hlt, hp⟩; exact ⟨⟨hp.one_le, by omega⟩, hp⟩
        · rintro ⟨⟨_, hle⟩, hp⟩; exact ⟨by omega, hp⟩
      rw [hpi]; exact_mod_cast Finset.card_le_card hlg_sub_pi
    have hcard_split : (P_med.card : ℝ) + (P_big.card : ℝ) = (P_lg.card : ℝ) := by
      have hdisj : Disjoint P_med P_big := by
        rw [Finset.disjoint_left]; intro x hx1 hx2
        simp only [Finset.mem_filter, P_med, P_big] at hx1 hx2; exact hx2.2 hx1.2
      have hunion : P_med ∪ P_big = P_lg := by
        ext x; simp only [Finset.mem_union, Finset.mem_filter, P_med, P_big]; tauto
      have hN : P_med.card + P_big.card = P_lg.card := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      exact_mod_cast hN
    have hmed_sum1 : ∑ p ∈ P_med, 2 * ((N : ℝ) / (p : ℝ) ^ 2) ≤ (N : ℝ) * htail_ub := by
      calc ∑ p ∈ P_med, 2 * ((N : ℝ) / (p : ℝ) ^ 2)
          = (N : ℝ) * ∑ p ∈ P_med, (2 : ℝ) / (p : ℝ) ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (N : ℝ) * ∑ p ∈ (Finset.Icc (Y1 + 1) pMax).filter Nat.Prime, (2 : ℝ) / (p : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hmed_sub_tail (fun _ _ _ => by positivity))
              (by positivity)
        _ ≤ (N : ℝ) * htail_ub := by gcongr
    have hmed_card_le : (P_med.card : ℝ) ≤ Real.sqrt (2 * (N : ℝ)) / 2 :=
      le_trans (by exact_mod_cast Finset.card_le_card hmed_sub_sq) (card_odd_primes_lt_sqrt_le N Y1 hY1_ge)
    have hmed_expand : ∑ p ∈ P_med, (2 * ((N : ℝ) / (p : ℝ) ^ 2) + 1 + 1) =
        (∑ p ∈ P_med, 2 * ((N : ℝ) / (p : ℝ) ^ 2)) + (P_med.card : ℝ) + (P_med.card : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hmed_expand] at hmed_ub
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hbig_ub
    linarith [hlg_sp, hmed_ub, hbig_ub, hmed_sum1, hmed_card_le, hcard_split, hcard_lg_le_pi]
  linarith [hJ_card, hJ_lb, hsum_split, hsm_ub, hlg_ub, hstrict]

-- Helper: squarefree factor g of n
private lemma exists_sq_factor_of_not_squarefree {m : ℕ} (hm : 1 ≤ m) (hns : ¬ Squarefree m) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ m := by
  by_contra hall
  push_neg at hall
  apply hns
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  exact hall p hp (by simpa [sq] using hpp)

private lemma prime_sq_dvd_sub_sq_elim {n k p : ℕ} (hp : p.Prime) (hk2 : k ^ 2 < n)
    (hdiv : p ^ 2 ∣ n - k ^ 2) (hpn : p ∣ n) : p ^ 2 ∣ n ∧ p ∣ k := by
  have hp_sub : p ∣ n - k ^ 2 := dvd_trans (dvd_pow_self p (by norm_num)) hdiv
  have hp_k2 : p ∣ k ^ 2 := by
    have hadd : (n - k ^ 2) + k ^ 2 = n := Nat.sub_add_cancel hk2.le
    exact (Nat.dvd_add_right hp_sub).mp (hadd.symm ▸ hpn)
  have hpk : p ∣ k := hp.dvd_of_dvd_pow hp_k2
  have hpk2 : p ^ 2 ∣ k ^ 2 := pow_dvd_pow_of_dvd hpk 2
  have hpn2 : p ^ 2 ∣ n := by
    have := Nat.dvd_add hdiv hpk2
    rwa [Nat.sub_add_cancel hk2.le] at this
  exact ⟨hpn2, hpk⟩

private lemma exp_linear_lower {M M0 : ℝ} {a : ℝ} (hM0 : 1 < M0) (hM : M0 ≤ M)
    (ha : 1 ≤ a * Real.log M0) :
    (M0 ^ a / Real.log M0) * Real.log M ≤ M ^ a := by
  have hM0_pos : 0 < M0 := by linarith
  have hM_pos : 0 < M := by linarith
  have hL0_pos : 0 < Real.log M0 := Real.log_pos hM0
  have hL_ge : Real.log M0 ≤ Real.log M := Real.log_le_log hM0_pos hM
  rw [Real.rpow_def_of_pos hM0_pos, Real.rpow_def_of_pos hM_pos]
  have hdiff : Real.exp (Real.log M * a) =
      Real.exp (Real.log M0 * a) * Real.exp (a * (Real.log M - Real.log M0)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hdiff]
  have hexp : 1 + a * (Real.log M - Real.log M0) ≤ Real.exp (a * (Real.log M - Real.log M0)) := by
    linarith [Real.add_one_le_exp (a * (Real.log M - Real.log M0))]
  have hlin : Real.log M / Real.log M0 ≤ 1 + a * (Real.log M - Real.log M0) := by
    rw [div_le_iff₀ hL0_pos]
    nlinarith
  have h0 : 0 ≤ Real.exp (Real.log M0 * a) := (Real.exp_pos _).le
  calc (Real.exp (Real.log M0 * a) / Real.log M0) * Real.log M
      = Real.exp (Real.log M0 * a) * (Real.log M / Real.log M0) := by ring
    _ ≤ Real.exp (Real.log M0 * a) * (1 + a * (Real.log M - Real.log M0)) :=
        mul_le_mul_of_nonneg_left hlin h0
    _ ≤ Real.exp (Real.log M0 * a) * Real.exp (a * (Real.log M - Real.log M0)) :=
        mul_le_mul_of_nonneg_left hexp h0

private lemma sqrt_div_log_ge {x x0 L0_hi : ℝ} {c : ℝ}
    (hx0 : 1 < x0) (hx : x0 ≤ x) (hL : Real.log x0 ≤ L0_hi)
    (h1 : 2 ≤ Real.log x0) (hc : c ≤ Real.sqrt x0) (hc_pos : 0 < c) :
    1 / Real.sqrt x ≤ (L0_hi / c) / Real.log x := by
  have hx0_pos : 0 < x0 := by linarith
  have hx_pos : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLx0_pos : 0 < Real.log x0 := Real.log_pos hx0
  have h := exp_linear_lower hx0 hx (a := (1 / 2 : ℝ)) (by linarith)
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  have h2 : (c / L0_hi) * Real.log x ≤ Real.sqrt x := by
    have hc_div : c / L0_hi ≤ Real.sqrt x0 / Real.log x0 := by
      rw [div_le_div_iff₀ (by linarith) hLx0_pos]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right hc_div hLx_pos.le) h
  rw [div_le_div_iff₀ (Real.sqrt_pos.mpr hx_pos) hLx_pos, one_mul, div_mul_eq_mul_div, le_div_iff₀ hc_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h2
  linarith

private lemma sqrt_sqrt_div_log_ge {x x0 L0_hi : ℝ} {c : ℝ}
    (hx0 : 1 < x0) (hx : x0 ≤ x) (hL : Real.log x0 ≤ L0_hi)
    (h1 : 4 ≤ Real.log x0) (hc : c ≤ Real.sqrt (Real.sqrt x0)) (hc_pos : 0 < c) :
    1 / Real.sqrt (Real.sqrt x) ≤ (L0_hi / c) / Real.log x := by
  have hx0_pos : 0 < x0 := by linarith
  have hx_pos : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hLx0_pos : 0 < Real.log x0 := Real.log_pos hx0
  have h := exp_linear_lower hx0 hx (a := (1 / 4 : ℝ)) (by linarith)
  have hrpow4 : ∀ y : ℝ, 0 ≤ y → y ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt y) := by
    intro y hy
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hy]
    norm_num
  rw [hrpow4 x0 hx0_pos.le, hrpow4 x hx_pos.le] at h
  have h2 : (c / L0_hi) * Real.log x ≤ Real.sqrt (Real.sqrt x) := by
    have hc_div : c / L0_hi ≤ Real.sqrt (Real.sqrt x0) / Real.log x0 := by
      rw [div_le_div_iff₀ (by linarith) hLx0_pos]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right hc_div hLx_pos.le) h
  have hsqsq_pos : 0 < Real.sqrt (Real.sqrt x) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx_pos)
  rw [div_le_div_iff₀ hsqsq_pos hLx_pos, one_mul, div_mul_eq_mul_div, le_div_iff₀ hc_pos]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h2
  linarith

-- Small-M regime helper (M < 200000, Y1 = 7)
private lemma small_regime_arith {N g pMax e_ub : ℕ} {phiQ piC : ℝ}
    (hg : Squarefree g) (hg_odd : g % 2 = 1) (hN_pos : 1 ≤ N)
    (hpi : (Nat.primeCounting pMax : ℝ) ≤ phiQ * (pMax : ℝ) + piC)
    (hM_lo : 0 < (N : ℝ))
    (hcase_margin :
      ∀ (has3 has5 has7 : Bool),
        let p3 : ℕ := if has3 then 3 else 1
        let p5 : ℕ := if has5 then 5 else 1
        let p7 : ℕ := if has7 then 7 else 1
        let prodS : ℕ := p3 * p5 * p7
        let phiS : ℝ := (if has3 then 2 / 3 else 1) * (if has5 then 4 / 5 else 1) * (if has7 then 6 / 7 else 1)
        let sSum : ℝ := (if has3 then 0 else 2 / 9) + (if has5 then 0 else 2 / 25) + (if has7 then 0 else 2 / 49)
        let nNot : ℕ := (if has3 then 0 else 1) + (if has5 then 0 else 1) + (if has7 then 0 else 1)
        let szS : ℕ := (if has3 then 1 else 0) + (if has5 then 1 else 0) + (if has7 then 1 else 0)
        prodS ∣ g →
        ∀ k : ℕ,
          (k = 0 ∧ 1 ≤ g / prodS →
            (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
              Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
            (N : ℝ) * (phiS * 1) * (1 - sSum)) ∧
          (k = 1 ∧ 11 ≤ g / prodS →
            (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
              Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
            (N : ℝ) * (phiS * (10 / 11)) * (1 - sSum)) ∧
          (k = 2 ∧ 143 ≤ g / prodS →
            (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
              Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
            (N : ℝ) * (phiS * (120 / 143)) * (1 - sSum)) ∧
          (k = 3 ∧ 2431 ≤ g / prodS →
            (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
              Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
            (N : ℝ) * (phiS * (1920 / 2431)) * (1 - sSum)) ∧
          (k = 4 ∧ 46189 ≤ g / prodS →
            (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
              Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
            (N : ℝ) * (phiS * (34560 / 46189)) * (1 - sSum)))
    (hg_lt : g < 1062347) :
    let phi_r := ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))
    let S_sm_set := (Finset.Icc 3 7).filter (fun p => p.Prime ∧ ¬ p ∣ g)
    let S_sm := ∑ p ∈ S_sm_set, (2 : ℝ) / (p : ℝ) ^ 2
    ((2 ^ g.primeFactors.card : ℝ) - 1) +
      2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) +
      (N : ℝ) * (81 / 1000) +
      Real.sqrt (2 * (N : ℝ)) / 2 +
      (Nat.primeCounting pMax : ℝ) +
      (e_ub : ℝ) <
    (N : ℝ) * phi_r * (1 - S_sm) := by
  intro phi_r S_sm_set S_sm
  have hg_pos : 0 < g := Nat.pos_of_ne_zero hg.ne_zero
  let has3 : Bool := decide (3 ∣ g)
  let has5 : Bool := decide (5 ∣ g)
  let has7 : Bool := decide (7 ∣ g)
  let P_sm := g.primeFactors.filter (fun p => p ≤ 7)
  let P_big := g.primeFactors.filter (fun p => ¬ p ≤ 7)
  have hP_big_spec : ∀ p ∈ P_big, p.Prime ∧ 11 ≤ p := by
    intro p hp
    simp only [Finset.mem_filter, P_big] at hp
    have hpr := Nat.prime_of_mem_primeFactors hp.1
    refine ⟨hpr, ?_⟩
    by_contra h; push_neg at h
    have : 8 ≤ p := by omega
    interval_cases p <;> norm_num at hpr
  have hdisj : Disjoint P_sm P_big := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_filter, P_sm, P_big] at hx1 hx2; exact hx2.2 hx1.2
  have hunion : g.primeFactors = P_sm ∪ P_big := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter, P_sm, P_big]; tauto
  have hcard_g : g.primeFactors.card = P_sm.card + P_big.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  have hphi_split : phi_r = (∏ p ∈ P_sm, (1 - 1 / (p : ℝ))) * (∏ p ∈ P_big, (1 - 1 / (p : ℝ))) := by
    dsimp [phi_r]; rw [hunion, Finset.prod_union hdisj]
  -- Exact identification of P_sm and S_sm_set from has3, has5, has7
  have hP_sm_mem : ∀ p, p ∈ P_sm ↔ (p = 3 ∧ has3 = true) ∨ (p = 5 ∧ has5 = true) ∨ (p = 7 ∧ has7 = true) := by
    intro p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, P_sm, has3, has5, has7, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hpr, hdg, _⟩, hle7⟩
      have hne2 : p ≠ 2 := by intro h2; subst h2; omega
      have := hpr.two_le
      interval_cases p <;> (try norm_num at hpr hne2) <;> tauto
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact ⟨⟨Nat.prime_three, h, hg.ne_zero⟩, by norm_num⟩
      · exact ⟨⟨by norm_num, h, hg.ne_zero⟩, by norm_num⟩
      · exact ⟨⟨by norm_num, h, hg.ne_zero⟩, by norm_num⟩
  have hS_sm_mem : ∀ p, p ∈ S_sm_set ↔ (p = 3 ∧ has3 = false) ∨ (p = 5 ∧ has5 = false) ∨ (p = 7 ∧ has7 = false) := by
    intro p
    simp only [Finset.mem_filter, Finset.mem_Icc, S_sm_set, has3, has5, has7, decide_eq_false_iff_not]
    constructor
    · rintro ⟨⟨h3, h7⟩, hpr, hnd⟩
      interval_cases p <;> (try norm_num at hpr) <;> tauto
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact ⟨⟨by norm_num, by norm_num⟩, Nat.prime_three, h⟩
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, h⟩
      · exact ⟨⟨by norm_num, by norm_num⟩, by norm_num, h⟩
  let p3 : ℕ := if has3 then 3 else 1
  let p5 : ℕ := if has5 then 5 else 1
  let p7 : ℕ := if has7 then 7 else 1
  let prodS : ℕ := p3 * p5 * p7
  let phiS : ℝ := (if has3 then 2 / 3 else 1) * (if has5 then 4 / 5 else 1) * (if has7 then 6 / 7 else 1)
  let sSum : ℝ := (if has3 then 0 else 2 / 9) + (if has5 then 0 else 2 / 25) + (if has7 then 0 else 2 / 49)
  let nNot : ℕ := (if has3 then 0 else 1) + (if has5 then 0 else 1) + (if has7 then 0 else 1)
  let szS : ℕ := (if has3 then 1 else 0) + (if has5 then 1 else 0) + (if has7 then 1 else 0)
  have hP_sm_eq : P_sm = (if has3 then ({3} : Finset ℕ) else ∅) ∪
      (if has5 then {5} else ∅) ∪ (if has7 then {7} else ∅) := by
    ext p; rw [hP_sm_mem]
    cases has3 <;> cases has5 <;> cases has7 <;> simp <;> tauto
  have hS_sm_eq : S_sm_set = (if has3 then ∅ else ({3} : Finset ℕ)) ∪
      (if has5 then ∅ else {5}) ∪ (if has7 then ∅ else {7}) := by
    ext p; rw [hS_sm_mem]
    cases has3 <;> cases has5 <;> cases has7 <;> simp <;> tauto
  have hprodS_eq : ∏ p ∈ P_sm, p = prodS := by
    dsimp [prodS, p3, p5, p7]; rw [hP_sm_eq]
    cases has3 <;> cases has5 <;> cases has7 <;> norm_num
  have hphiS_eq : ∏ p ∈ P_sm, (1 - 1 / (p : ℝ)) = phiS := by
    dsimp [phiS]; rw [hP_sm_eq]
    cases has3 <;> cases has5 <;> cases has7 <;> norm_num
  have hszS_eq : P_sm.card = szS := by
    dsimp [szS]; rw [hP_sm_eq]
    cases has3 <;> cases has5 <;> cases has7 <;> decide
  have hnNot_eq : S_sm_set.card = nNot := by
    dsimp [nNot]; rw [hS_sm_eq]
    cases has3 <;> cases has5 <;> cases has7 <;> decide
  have hsSum_eq : S_sm = sSum := by
    dsimp [S_sm, sSum]; rw [hS_sm_eq]
    cases has3 <;> cases has5 <;> cases has7 <;> norm_num
  have hprodS_dvd : prodS ∣ g := by
    rw [← hprodS_eq]
    exact (Finset.prod_dvd_prod_of_subset P_sm g.primeFactors (fun p => p) (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd g)
  have hprod_big_le : ∏ p ∈ P_big, p ≤ g / prodS := by
    have hmul_dvd : prodS * (∏ p ∈ P_big, p) ∣ g := by
      rw [← hprodS_eq, ← Finset.prod_union hdisj, ← hunion]
      exact Nat.prod_primeFactors_dvd g
    have hprodS_pos : 0 < prodS := by
      dsimp [prodS, p3, p5, p7]; cases has3 <;> cases has5 <;> cases has7 <;> norm_num
    have hle := Nat.le_of_dvd hg_pos hmul_dvd
    exact (Nat.le_div_iff_mul_le hprodS_pos).mpr (by linarith)
  have hdiv_pos : 1 ≤ g / prodS := by
    have hprodS_pos : 0 < prodS := by
      dsimp [prodS, p3, p5, p7]; cases has3 <;> cases has5 <;> cases has7 <;> norm_num
    exact Nat.div_pos (Nat.le_of_dvd hg_pos hprodS_dvd) hprodS_pos
  have h11 := primes_ge11_bounds hP_big_spec
  have hk_lt5 : P_big.card < 5 := by
    by_contra hge5
    push_neg at hge5
    have h1 := h11.2.2.2.2.2 hge5
    have h2 : g / prodS ≤ g := Nat.div_le_self g prodS
    omega
  have hmargin := hcase_margin has3 has5 has7 hprodS_dvd P_big.card
  have h1_sub_nonneg : 0 ≤ 1 - sSum := by
    dsimp [sSum]; cases has3 <;> cases has5 <;> cases has7 <;> norm_num
  have hphiS_nonneg : 0 ≤ phiS := by
    dsimp [phiS]; cases has3 <;> cases has5 <;> cases has7 <;> norm_num
  have hrew_mob : ((2 ^ g.primeFactors.card : ℝ) - 1) +
      2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) =
      (((1 + 2 * nNot) * 2 ^ (szS + P_big.card) : ℕ) : ℝ) - 1 := by
    rw [hcard_g, hszS_eq, hnNot_eq]; push_cast; ring
  rw [hrew_mob, hphi_split, hphiS_eq, hsSum_eq]
  interval_cases hk : P_big.card
  · have hphi1 := h11.1 rfl
    have hm := hmargin.1 ⟨rfl, hdiv_pos⟩
    rw [hphi1]; linarith
  · obtain ⟨hp1, hph1⟩ := h11.2.1 rfl
    have hm := hmargin.2.1 ⟨rfl, le_trans hp1 hprod_big_le⟩
    have hmon : (N : ℝ) * (phiS * (10 / 11 : ℝ)) * (1 - sSum) ≤
        (N : ℝ) * (phiS * ∏ p ∈ P_big, (1 - 1 / (p : ℝ))) * (1 - sSum) := by
      gcongr
    linarith
  · obtain ⟨hp2, hph2⟩ := h11.2.2.1 rfl
    have hm := hmargin.2.2.1 ⟨rfl, le_trans hp2 hprod_big_le⟩
    have hmon : (N : ℝ) * (phiS * (120 / 143 : ℝ)) * (1 - sSum) ≤
        (N : ℝ) * (phiS * ∏ p ∈ P_big, (1 - 1 / (p : ℝ))) * (1 - sSum) := by
      gcongr
    linarith
  · obtain ⟨hp3, hph3⟩ := h11.2.2.2.1 rfl
    have hm := hmargin.2.2.2.1 ⟨rfl, le_trans hp3 hprod_big_le⟩
    have hmon : (N : ℝ) * (phiS * (1920 / 2431 : ℝ)) * (1 - sSum) ≤
        (N : ℝ) * (phiS * ∏ p ∈ P_big, (1 - 1 / (p : ℝ))) * (1 - sSum) := by
      gcongr
    linarith
  · obtain ⟨hp4, hph4⟩ := h11.2.2.2.2.1 rfl
    have hm := hmargin.2.2.2.2 ⟨rfl, le_trans hp4 hprod_big_le⟩
    have hmon : (N : ℝ) * (phiS * (34560 / 46189 : ℝ)) * (1 - sSum) ≤
        (N : ℝ) * (phiS * ∏ p ∈ P_big, (1 - 1 / (p : ℝ))) * (1 - sSum) := by
      gcongr
    linarith

private def smallIntervalCheckProp (g_max N_lo e_ub : ℕ) (phiQ piC pCoeff pAdd hsq_ub : ℝ) : Prop :=
  ∀ (has3 has5 has7 : Bool),
    let p3 : ℕ := if has3 then 3 else 1
    let p5 : ℕ := if has5 then 5 else 1
    let p7 : ℕ := if has7 then 7 else 1
    let prodS : ℕ := p3 * p5 * p7
    let phiS : ℝ := (if has3 then 2 / 3 else 1) * (if has5 then 4 / 5 else 1) * (if has7 then 6 / 7 else 1)
    let sSum : ℝ := (if has3 then 0 else 2 / 9) + (if has5 then 0 else 2 / 25) + (if has7 then 0 else 2 / 49)
    let nNot : ℕ := (if has3 then 0 else 1) + (if has5 then 0 else 1) + (if has7 then 0 else 1)
    let szS : ℕ := (if has3 then 1 else 0) + (if has5 then 1 else 0) + (if has7 then 1 else 0)
    (prodS ≤ g_max →
      ((((1 + 2 * nNot) * 2 ^ (szS + 0) : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)) / (N_lo : ℝ) +
        (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff < (phiS * 1) * (1 - sSum)) ∧
    (11 * prodS ≤ g_max →
      ((((1 + 2 * nNot) * 2 ^ (szS + 1) : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)) / (N_lo : ℝ) +
        (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff < (phiS * (10 / 11)) * (1 - sSum)) ∧
    (143 * prodS ≤ g_max →
      ((((1 + 2 * nNot) * 2 ^ (szS + 2) : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)) / (N_lo : ℝ) +
        (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff < (phiS * (120 / 143)) * (1 - sSum)) ∧
    (2431 * prodS ≤ g_max →
      ((((1 + 2 * nNot) * 2 ^ (szS + 3) : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)) / (N_lo : ℝ) +
        (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff < (phiS * (1920 / 2431)) * (1 - sSum)) ∧
    (46189 * prodS ≤ g_max →
      ((((1 + 2 * nNot) * 2 ^ (szS + 4) : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)) / (N_lo : ℝ) +
        (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff < (phiS * (34560 / 46189)) * (1 - sSum))

-- Clean rational verifier for a single interval [M_lo, M_hi]
private lemma small_interval_check {N g pMax e_ub g_max N_lo : ℕ} {phiQ piC pCoeff pAdd : ℝ}
    (hg_le : g ≤ g_max) (hN_ge : N_lo ≤ N)
    (hpMax_le : (pMax : ℝ) ≤ pCoeff * (N : ℝ) + pAdd)
    (hN_lo_pos : 0 < (N_lo : ℝ))
    (hphiQ_nn : 0 ≤ phiQ) (hpAdd_nn : 0 ≤ pAdd) (hpiC_nn : 0 ≤ piC)
    (hsq_ub : ℝ) (hsq : Real.sqrt (2 / (N_lo : ℝ)) / 2 ≤ hsq_ub)
    (hchk : smallIntervalCheckProp g_max N_lo e_ub phiQ piC pCoeff pAdd hsq_ub) :
    ∀ (has3 has5 has7 : Bool),
      let p3 : ℕ := if has3 then 3 else 1
      let p5 : ℕ := if has5 then 5 else 1
      let p7 : ℕ := if has7 then 7 else 1
      let prodS : ℕ := p3 * p5 * p7
      let phiS : ℝ := (if has3 then 2 / 3 else 1) * (if has5 then 4 / 5 else 1) * (if has7 then 6 / 7 else 1)
      let sSum : ℝ := (if has3 then 0 else 2 / 9) + (if has5 then 0 else 2 / 25) + (if has7 then 0 else 2 / 49)
      let nNot : ℕ := (if has3 then 0 else 1) + (if has5 then 0 else 1) + (if has7 then 0 else 1)
      let szS : ℕ := (if has3 then 1 else 0) + (if has5 then 1 else 0) + (if has7 then 1 else 0)
      prodS ∣ g →
      ∀ k : ℕ,
        (k = 0 ∧ 1 ≤ g / prodS →
          (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
            Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
          (N : ℝ) * (phiS * 1) * (1 - sSum)) ∧
        (k = 1 ∧ 11 ≤ g / prodS →
          (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
            Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
          (N : ℝ) * (phiS * (10 / 11)) * (1 - sSum)) ∧
        (k = 2 ∧ 143 ≤ g / prodS →
          (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
            Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
          (N : ℝ) * (phiS * (120 / 143)) * (1 - sSum)) ∧
        (k = 3 ∧ 2431 ≤ g / prodS →
          (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
            Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
          (N : ℝ) * (phiS * (1920 / 2431)) * (1 - sSum)) ∧
        (k = 4 ∧ 46189 ≤ g / prodS →
          (((1 + 2 * nNot) * 2 ^ (szS + k) : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
            Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) <
          (N : ℝ) * (phiS * (34560 / 46189)) * (1 - sSum)) := by
  intro has3 has5 has7 p3 p5 p7 prodS phiS sSum nNot szS _hdvd k
  have hN_geR : (N_lo : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge
  have hN_pos : 0 < (N : ℝ) := lt_of_lt_of_le hN_lo_pos hN_geR
  have hsq_N : Real.sqrt (2 * (N : ℝ)) / 2 ≤ (N : ℝ) * hsq_ub := by
    have h1 : Real.sqrt (2 * (N : ℝ)) / 2 = (N : ℝ) * (Real.sqrt (2 / (N : ℝ)) / 2) := by
      rw [Real.sqrt_div (by norm_num), Real.sqrt_mul (by norm_num)]
      have hsqN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hN_pos).ne'
      have hsq2 : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := Real.mul_self_sqrt hN_pos.le
      field_simp; linarith
    rw [h1]
    have h2 : Real.sqrt (2 / (N : ℝ)) / 2 ≤ hsq_ub := le_trans (by gcongr) hsq
    exact mul_le_mul_of_nonneg_left h2 hN_pos.le
  have hmul_dvd_le : ∀ c : ℕ, c ≤ g / prodS → c * prodS ≤ g_max := by
    intro c hc
    have hp_pos : 0 < prodS := by
      dsimp [prodS, p3, p5, p7]; cases has3 <;> cases has5 <;> cases has7 <;> norm_num
    have := (Nat.le_div_iff_mul_le hp_pos).mp hc
    omega
  have hpi_le : phiQ * (pMax : ℝ) + piC ≤ (phiQ * pCoeff) * (N : ℝ) + (phiQ * pAdd + piC) := by
    nlinarith
  have hpa_nn : 0 ≤ phiQ * pAdd + piC := by nlinarith
  have h_use : ∀ (m : ℕ) (B : ℝ),
      ((((1 + 2 * nNot) * 2 ^ m : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)) / (N_lo : ℝ) +
        (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff < B →
      (((1 + 2 * nNot) * 2 ^ m : ℕ) : ℝ) - 1 + (N : ℝ) * (81 / 1000) +
        Real.sqrt (2 * (N : ℝ)) / 2 + (phiQ * (pMax : ℝ) + piC) + (e_ub : ℝ) < (N : ℝ) * B := by
    intro m B hlt
    let C : ℝ := (((1 + 2 * nNot) * 2 ^ m : ℕ) : ℝ) - 1 + phiQ * pAdd + piC + (e_ub : ℝ)
    have hC : 0 ≤ C := by
      dsimp [C]
      have h1 : (1 : ℝ) ≤ (((1 + 2 * nNot) * 2 ^ m : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos (by omega) (Nat.one_le_pow m 2 (by omega))
      have he : (0 : ℝ) ≤ (e_ub : ℝ) := by positivity
      linarith
    have hC_N : C ≤ (N : ℝ) * (C / (N_lo : ℝ)) := by
      calc C = (N_lo : ℝ) * (C / (N_lo : ℝ)) := (mul_div_cancel₀ C hN_lo_pos.ne').symm
        _ ≤ (N : ℝ) * (C / (N_lo : ℝ)) := mul_le_mul_of_nonneg_right hN_geR (div_nonneg hC hN_lo_pos.le)
    have hmul : (N : ℝ) * (C / (N_lo : ℝ) + (81 / 1000 : ℝ) + hsq_ub + phiQ * pCoeff) < (N : ℝ) * B :=
      mul_lt_mul_of_pos_left hlt hN_pos
    dsimp [C] at hC_N hmul
    linarith
  have hchk' := hchk has3 has5 has7
  refine ⟨fun ⟨hk, hg1⟩ => ?_, fun ⟨hk, hg1⟩ => ?_, fun ⟨hk, hg1⟩ => ?_,
          fun ⟨hk, hg1⟩ => ?_, fun ⟨hk, hg1⟩ => ?_⟩
  · subst hk
    exact h_use (szS + 0) ((phiS * 1) * (1 - sSum))
      (hchk'.1 (by have h := hmul_dvd_le 1 hg1; rw [one_mul] at h; exact h))
      |> fun h => by linarith
  · subst hk
    exact h_use (szS + 1) ((phiS * (10 / 11)) * (1 - sSum)) (hchk'.2.1 (hmul_dvd_le 11 hg1))
      |> fun h => by linarith
  · subst hk
    exact h_use (szS + 2) ((phiS * (120 / 143)) * (1 - sSum)) (hchk'.2.2.1 (hmul_dvd_le 143 hg1))
      |> fun h => by linarith
  · subst hk
    exact h_use (szS + 3) ((phiS * (1920 / 2431)) * (1 - sSum)) (hchk'.2.2.2.1 (hmul_dvd_le 2431 hg1))
      |> fun h => by linarith
  · subst hk
    exact h_use (szS + 4) ((phiS * (34560 / 46189)) * (1 - sSum)) (hchk'.2.2.2.2 (hmul_dvd_le 46189 hg1))
      |> fun h => by linarith

private lemma sqrt_two_div_le_of_sq {N_lo : ℕ} {c : ℝ} (hN : 0 < N_lo) (hc : 0 ≤ c)
    (h : 1 ≤ 2 * (N_lo : ℝ) * c ^ 2) :
    Real.sqrt (2 / (N_lo : ℝ)) / 2 ≤ c := by
  have hN' : (0 : ℝ) < (N_lo : ℝ) := by exact_mod_cast hN
  rw [div_le_iff₀ (by norm_num), Real.sqrt_le_left (by linarith)]
  rw [div_le_iff₀ hN']
  nlinarith

-- Helper to construct g = prod_{p^2 | n} p and its properties
private lemma sq_part_props {n M : ℕ} (hn_pos : 0 < n) (hM_hi : n ≤ (M + 1) ^ 2) :
    let g := ∏ p ∈ n.primeFactors.filter (fun p => p ^ 2 ∣ n), p
    Squarefree g ∧ g ^ 2 ∣ n ∧ g ≤ M + 1 ∧
      ∀ p : ℕ, p.Prime → (p ∣ g ↔ p ^ 2 ∣ n) := by
  intro g
  let P := n.primeFactors.filter (fun p => p ^ 2 ∣ n)
  have hP_pr : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hsq : Squarefree g := by
    have hnd : P.toList.Nodup := P.nodup_toList
    have hpr : ∀ p ∈ P.toList, p.Prime := fun p hp => hP_pr p (Finset.mem_toList.mp hp)
    have h := (squarefree_prod_primes hnd hpr).1
    simpa [g, Finset.prod_toList] using h
  have hpf : g.primeFactors = P := by
    have hnd : P.toList.Nodup := P.nodup_toList
    have hpr : ∀ p ∈ P.toList, p.Prime := fun p hp => hP_pr p (Finset.mem_toList.mp hp)
    have h := (squarefree_prod_primes hnd hpr).2
    simpa [g, Finset.prod_toList] using h
  have hg2_dvd : g ^ 2 ∣ n := by
    rw [show g ^ 2 = ∏ p ∈ P, p ^ 2 by dsimp [g]; rw [Finset.prod_pow]]
    suffices ∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ p ^ 2 ∣ n) → ∏ p ∈ Q, p ^ 2 ∣ n from
      this P (fun p hp => ⟨hP_pr p hp, (Finset.mem_filter.mp hp).2⟩)
    intro Q hQ
    induction Q using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.prod_insert has]
      have ha := hQ a (Finset.mem_insert_self a s)
      have hs := ih (fun p hp => hQ p (Finset.mem_insert_of_mem hp))
      have hcop : (a ^ 2).Coprime (∏ p ∈ s, p ^ 2) := by
        refine Nat.Coprime.prod_right fun p hp => ?_
        have hpa := hQ p (Finset.mem_insert_of_mem hp)
        have hne : a ≠ p := fun h => has (h ▸ hp)
        exact ((Nat.coprime_primes ha.1 hpa.1).mpr hne).pow 2 2
      exact hcop.mul_dvd_of_dvd_of_dvd ha.2 hs
  have hg_le : g ≤ M + 1 := by
    have hle := Nat.le_of_dvd hn_pos hg2_dvd
    nlinarith
  have hdvd_iff : ∀ p : ℕ, p.Prime → (p ∣ g ↔ p ^ 2 ∣ n) := by
    intro p hp
    constructor
    · intro hpg
      have hmem : p ∈ g.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpg, hsq.ne_zero⟩
      rw [hpf] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · intro hp2
      have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hp2
      have hmem : p ∈ P := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpn, hn_pos.ne'⟩, hp2⟩
      exact Finset.dvd_prod_of_mem _ hmem
  exact ⟨hsq, hg2_dvd, hg_le, hdvd_iff⟩

-- Large-M Chebyshev arithmetic bound (M >= 200000)
set_option maxHeartbeats 400000 in
private lemma large_regime_arith {M N g pMax : ℕ} {xCoeff xAdd eCoeff alpha lxLo x0Sq x0Qrt mOverN : ℝ}
    (hM : 200000 ≤ M) (hg : Squarefree g) (hg_odd : g % 2 = 1) (hg_le : g ≤ M + 1)
    (hN_lo : (M : ℝ) ≤ mOverN * (N : ℝ)) (hmOverN_pos : 0 < mOverN) (hmOverN_le : mOverN ≤ 200002 / 100000)
    (hN_pos : 1 ≤ N)
    (hN_sq : (M : ℝ) - 1 ≤ 2 * (N : ℝ))
    (hpMax_le : (pMax : ℝ) ≤ xCoeff * (M : ℝ))
    (hxCoeff_pos : 0 < xCoeff)
    (hlog_x_ge : alpha * Real.log (M : ℝ) ≤ Real.log (xCoeff * (M : ℝ)))
    (halpha_pos : 0 < alpha)
    (hlx_ge : lxLo ≤ Real.log (xCoeff * (M : ℝ))) (hlx_pos : 0 < lxLo)
    (hx0_ge16 : 16 ≤ xCoeff * (200000 : ℝ))
    (hx0_log_lo : 4 ≤ Real.log (xCoeff * (200000 : ℝ)))
    (hx0_log_hi : Real.log (xCoeff * (200000 : ℝ)) ≤ 1226 / 100)
    (hx0_sq : x0Sq ≤ Real.sqrt (xCoeff * (200000 : ℝ))) (hx0_sq_pos : 0 < x0Sq)
    (hx0_qrt : x0Qrt ≤ Real.sqrt (Real.sqrt (xCoeff * (200000 : ℝ)))) (hx0_qrt_pos : 0 < x0Qrt)
    (E_card : ℕ) (hE_le : (E_card : ℝ) ≤ eCoeff * Real.sqrt (M : ℝ)) (heCoeff_nn : 0 ≤ eCoeff)
    (hctot :
      let ratio := xCoeff * mOverN * (1387 / 1000 : ℝ)
      (1226 / 100 : ℝ) / 42 +
        (1233 / 100 : ℝ) * (1226 / 100) / 447 +
        (1001 / 1000 : ℝ) * (1226 / 100) / 447 +
        (eCoeff * mOverN) * (1226 / 100) / 447 +
        ratio * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
          4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
          (209 / 100) * (1226 / 100) / (x0Sq * alpha)) ≤ 280 / 100) :
    let s := Nat.sqrt (Nat.sqrt M)
    let Y1 := 2 * s + 1
    let phi_r := ∏ p ∈ g.primeFactors, (1 - 1 / (p : ℝ))
    let S_sm_set := (Finset.Icc 3 Y1).filter (fun p => p.Prime ∧ ¬ p ∣ g)
    let S_sm := ∑ p ∈ S_sm_set, (2 : ℝ) / (p : ℝ) ^ 2
    ((2 ^ g.primeFactors.card : ℝ) - 1) +
      2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) +
      (N : ℝ) * (1 / ((Y1 : ℝ) + 1)) +
      Real.sqrt (2 * (N : ℝ)) / 2 +
      (Nat.primeCounting pMax : ℝ) +
      (E_card : ℝ) <
    (N : ℝ) * phi_r * (1 - S_sm) := by
  intro s Y1 phi_r S_sm_set S_sm
  have hMR : (200000 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hM_pos : (0 : ℝ) < (M : ℝ) := by linarith
  have hN_posR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hlog2_gt : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_lt : Real.log 2 < (0.693148 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hlog3_gt : (1.098612 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlog3_lt : Real.log 3 < (1.098613 : ℝ) := by linarith [Real.log_three_lt_d9]
  have hlog4_lt : Real.log 4 < 1387 / 1000 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
    linarith
  have hinv_log2_sq : 1 / (Real.log 2) ^ 2 ≤ 209 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hL0_lo : (12.188 : ℝ) < Real.log (200000 : ℝ) := by
    have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (200000 : ℝ) := by norm_num
    have hlog := Real.log_lt_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    push_cast at hlog; linarith
  have hL0_hi : Real.log (200000 : ℝ) ≤ 1226 / 100 := by
    have h1 : (200000 : ℝ) < (2 : ℝ) ^ 5 * (3 : ℝ) ^ 8 := by norm_num
    have hlog := Real.log_lt_log (by positivity) h1
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
    push_cast at hlog; linarith
  have hLM_ge : Real.log (200000 : ℝ) ≤ Real.log (M : ℝ) := Real.log_le_log (by norm_num) hMR
  have hLM_gt : (12.188 : ℝ) < Real.log (M : ℝ) := lt_of_lt_of_le hL0_lo hLM_ge
  have hLM_pos : 0 < Real.log (M : ℝ) := by linarith
  -- Bound 1/sqrt(M) and 1/sqrt(sqrt(M)) in terms of 1/L
  have h447 : (447 : ℝ) ≤ Real.sqrt (200000 : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have h21 : (21 : ℝ) ≤ Real.sqrt (Real.sqrt (200000 : ℝ)) := by
    rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hinv_sqrtM : 1 / Real.sqrt (M : ℝ) ≤ (1226 / 100 / 447 : ℝ) / Real.log (M : ℝ) :=
    sqrt_div_log_ge (by norm_num) hMR hL0_hi (by linarith) h447 (by norm_num)
  have hinv_qrtM : 1 / Real.sqrt (Real.sqrt (M : ℝ)) ≤ (1226 / 100 / 21 : ℝ) / Real.log (M : ℝ) :=
    sqrt_sqrt_div_log_ge (by norm_num) hMR hL0_hi (by linarith) h21 (by norm_num)
  -- (1) tail: 1 / (Y1 + 1) <= 1 / (2 * sqrt(sqrt M))
  have hs_ge : 21 ≤ s := by
    dsimp [s]
    have h1 : 441 ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by omega)
    exact Nat.le_sqrt.mpr (by omega)
  have hs_le : (s : ℝ) ≤ Real.sqrt (Real.sqrt (M : ℝ)) := by
    rw [Real.le_sqrt (by positivity) (Real.sqrt_nonneg _), Real.le_sqrt (by positivity) (by positivity)]
    have h1 : s * s ≤ Nat.sqrt M := Nat.sqrt_le (Nat.sqrt M)
    have h2 : Nat.sqrt M * Nat.sqrt M ≤ M := Nat.sqrt_le M
    have h3 : (s ^ 2) ^ 2 ≤ M := by
      have h1' : s ^ 2 ≤ Nat.sqrt M := by rwa [sq]
      exact (Nat.mul_le_mul h1' h1').trans h2 |> fun h => by rwa [← sq] at h
    exact_mod_cast h3
  have hs_succ_gt : Real.sqrt (Real.sqrt (M : ℝ)) ≤ (s : ℝ) + 1 := by
    have h1 : M < (Nat.sqrt M + 1) * (Nat.sqrt M + 1) := Nat.lt_succ_sqrt M
    have h2 : Nat.sqrt M < (s + 1) * (s + 1) := Nat.lt_succ_sqrt (Nat.sqrt M)
    have h2' : Nat.sqrt M + 1 ≤ (s + 1) ^ 2 := by rw [sq]; omega
    have h4 : M ≤ ((s + 1) ^ 2) ^ 2 := by
      rw [sq]
      exact le_trans h1.le (Nat.mul_le_mul h2' h2')
    have h4R : (M : ℝ) ≤ (((s : ℝ) + 1) ^ 2) ^ 2 := by exact_mod_cast h4
    have hsq1 : Real.sqrt (M : ℝ) ≤ ((s : ℝ) + 1) ^ 2 :=
      Real.sqrt_le_iff.mpr ⟨by positivity, by linarith⟩
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by linarith⟩
  have hterm_tail : 1 / ((Y1 : ℝ) + 1) ≤ ((1226 / 100 : ℝ) / 42) / Real.log (M : ℝ) := by
    have hY1_eq : (Y1 : ℝ) + 1 = 2 * ((s : ℝ) + 1) := by dsimp [Y1]; push_cast; ring
    rw [hY1_eq]
    have h1 : 1 / (2 * ((s : ℝ) + 1)) ≤ 1 / (2 * Real.sqrt (Real.sqrt (M : ℝ))) := by
      gcongr
    have h2 : 1 / (2 * Real.sqrt (Real.sqrt (M : ℝ))) = (1 / 2 : ℝ) * (1 / Real.sqrt (Real.sqrt (M : ℝ))) := by
      ring
    calc 1 / (2 * ((s : ℝ) + 1))
        ≤ (1 / 2 : ℝ) * (1 / Real.sqrt (Real.sqrt (M : ℝ))) := by linarith
      _ ≤ (1 / 2 : ℝ) * ((1226 / 100 / 21 : ℝ) / Real.log (M : ℝ)) := by gcongr
      _ = ((1226 / 100 : ℝ) / 42) / Real.log (M : ℝ) := by ring
  -- (2) mobius error: ((2^r - 1) + 2 * S_sm_set.card * 2^r) / N
  have hS_sm_card : S_sm_set.card ≤ s := by
    have hsub : S_sm_set ⊆ (Finset.Icc 1 s).image (fun t => 2 * t + 1) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, S_sm_set] at hp
      have hodd : p % 2 = 1 := by
        have := hp.2.1.eq_two_or_odd; omega
      rw [Finset.mem_image]
      refine ⟨p / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    calc S_sm_set.card ≤ ((Finset.Icc 1 s).image (fun t => 2 * t + 1)).card := Finset.card_le_card hsub
      _ = (Finset.Icc 1 s).card := Finset.card_image_of_injective _ (fun a b h => by omega)
      _ = s := by simp
  have h2r_le : (2 ^ g.primeFactors.card : ℝ) ≤ 3 * Real.sqrt (Real.sqrt ((M : ℝ) + 1)) := by
    refine le_trans (two_pow_omega_odd_sqfree_le hg hg_odd) ?_
    gcongr; exact_mod_cast hg_le
  have hqrt_M1 : Real.sqrt (Real.sqrt ((M : ℝ) + 1)) ≤ (1001 / 1000 : ℝ) * Real.sqrt (Real.sqrt (M : ℝ)) := by
    have h1 : (M : ℝ) + 1 ≤ (1001 / 1000 : ℝ) ^ 4 * (M : ℝ) := by linarith
    have h2 : Real.sqrt ((M : ℝ) + 1) ≤ (1001 / 1000 : ℝ) ^ 2 * Real.sqrt (M : ℝ) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc (M : ℝ) + 1 ≤ (1001 / 1000 : ℝ) ^ 4 * (M : ℝ) := h1
        _ = ((1001 / 1000 : ℝ) ^ 2 * Real.sqrt (M : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hM_pos.le]; ring
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc Real.sqrt ((M : ℝ) + 1) ≤ (1001 / 1000 : ℝ) ^ 2 * Real.sqrt (M : ℝ) := h2
      _ = ((1001 / 1000 : ℝ) * Real.sqrt (Real.sqrt (M : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]
  have hmob_num : ((2 ^ g.primeFactors.card : ℝ) - 1) +
      2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) ≤ (616 / 100 : ℝ) * Real.sqrt (M : ℝ) := by
    have hS_R : (S_sm_set.card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hS_sm_card
    have hs_geR : (21 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs_ge
    have h2s1 : 2 * (S_sm_set.card : ℝ) + 1 ≤ (43 / 21 : ℝ) * Real.sqrt (Real.sqrt (M : ℝ)) := by
      have : 2 * (s : ℝ) + 1 ≤ (43 / 21 : ℝ) * (s : ℝ) := by linarith
      linarith [this, hs_le]
    have h2r' : (2 ^ g.primeFactors.card : ℝ) ≤ (3003 / 1000 : ℝ) * Real.sqrt (Real.sqrt (M : ℝ)) := by
      linarith [h2r_le, hqrt_M1]
    have hsq_eq : Real.sqrt (Real.sqrt (M : ℝ)) * Real.sqrt (Real.sqrt (M : ℝ)) = Real.sqrt (M : ℝ) :=
      Real.mul_self_sqrt (Real.sqrt_nonneg _)
    have hnn1 : 0 ≤ (2 ^ g.primeFactors.card : ℝ) := by positivity
    have hnn2 : 0 ≤ 2 * (S_sm_set.card : ℝ) + 1 := by positivity
    have hprod : (2 * (S_sm_set.card : ℝ) + 1) * (2 ^ g.primeFactors.card : ℝ) ≤
        ((43 / 21 : ℝ) * (3003 / 1000 : ℝ)) * Real.sqrt (M : ℝ) := by
      calc (2 * (S_sm_set.card : ℝ) + 1) * (2 ^ g.primeFactors.card : ℝ)
          ≤ ((43 / 21 : ℝ) * Real.sqrt (Real.sqrt (M : ℝ))) *
              ((3003 / 1000 : ℝ) * Real.sqrt (Real.sqrt (M : ℝ))) :=
            mul_le_mul h2s1 h2r' hnn1 (by positivity)
        _ = ((43 / 21 : ℝ) * (3003 / 1000 : ℝ)) *
              (Real.sqrt (Real.sqrt (M : ℝ)) * Real.sqrt (Real.sqrt (M : ℝ))) := by ring
        _ = ((43 / 21 : ℝ) * (3003 / 1000 : ℝ)) * Real.sqrt (M : ℝ) := by rw [hsq_eq]
    have hconst : (43 / 21 : ℝ) * (3003 / 1000 : ℝ) ≤ 616 / 100 := by norm_num
    have hrew : ((2 ^ g.primeFactors.card : ℝ) - 1) +
        2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) =
        (2 * (S_sm_set.card : ℝ) + 1) * (2 ^ g.primeFactors.card : ℝ) - 1 := by ring
    have hmul_c := mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg (M : ℝ))
    linarith [hrew, hprod, hmul_c]
  have hterm_mob : (((2 ^ g.primeFactors.card : ℝ) - 1) +
      2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ)) / (N : ℝ) ≤
      ((1233 / 100 : ℝ) * (1226 / 100) / 447) / Real.log (M : ℝ) := by
    have hM_div_N : (M : ℝ) / (N : ℝ) ≤ 200002 / 100000 := by
      rw [div_le_iff₀ hN_posR]
      exact le_trans hN_lo (mul_le_mul_of_nonneg_right hmOverN_le hN_posR.le)
    have h1 : (((2 ^ g.primeFactors.card : ℝ) - 1) +
        2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ)) / (N : ℝ) ≤
        (616 / 100 : ℝ) * Real.sqrt (M : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right hmob_num hN_posR.le
    have h2 : Real.sqrt (M : ℝ) / (N : ℝ) = ((M : ℝ) / (N : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by
      have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM_pos.le
      have hsq0 : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hM_pos).ne'
      field_simp; linarith only [hsqM]
    have h3 : (616 / 100 : ℝ) * (200002 / 100000 : ℝ) ≤ 1233 / 100 := by norm_num
    have hinv_nn : 0 ≤ 1 / Real.sqrt (M : ℝ) := by positivity
    calc _ ≤ (616 / 100 : ℝ) * (((M : ℝ) / (N : ℝ)) * (1 / Real.sqrt (M : ℝ))) := by
            rw [← h2, ← mul_div_assoc]; exact h1
      _ ≤ (616 / 100 : ℝ) * ((200002 / 100000 : ℝ) * (1 / Real.sqrt (M : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM_div_N hinv_nn) (by norm_num)
      _ = ((616 / 100 : ℝ) * (200002 / 100000 : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by ring
      _ ≤ (1233 / 100 : ℝ) * (1 / Real.sqrt (M : ℝ)) := mul_le_mul_of_nonneg_right h3 hinv_nn
      _ ≤ (1233 / 100 : ℝ) * ((1226 / 100 / 447 : ℝ) / Real.log (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv_sqrtM (by norm_num)
      _ = ((1233 / 100 : ℝ) * (1226 / 100) / 447) / Real.log (M : ℝ) := by ring
  -- (3) sqrt(2 N) / (2 N) = 1 / sqrt(2 N) <= 1001/1000 / sqrt(M)
  have hterm_sq : (Real.sqrt (2 * (N : ℝ)) / 2) / (N : ℝ) ≤
      ((1001 / 1000 : ℝ) * (1226 / 100) / 447) / Real.log (M : ℝ) := by
    have hrew : (Real.sqrt (2 * (N : ℝ)) / 2) / (N : ℝ) = 1 / Real.sqrt (2 * (N : ℝ)) := by
      have hsq2N : Real.sqrt (2 * (N : ℝ)) * Real.sqrt (2 * (N : ℝ)) = 2 * (N : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hne : Real.sqrt (2 * (N : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      field_simp; linarith only [hsq2N]
    rw [hrew]
    have hM_le_2N : (M : ℝ) ≤ (1001 / 1000 : ℝ) ^ 2 * (2 * (N : ℝ)) := by
      have hconst : (1 : ℝ) ≤ ((1001 / 1000 : ℝ) ^ 2 - 1) * (200000 - 1 : ℝ) := by norm_num
      nlinarith only [hN_sq, hMR, hconst]
    have hsq_cmp : Real.sqrt (M : ℝ) ≤ (1001 / 1000 : ℝ) * Real.sqrt (2 * (N : ℝ)) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by positivity)]; exact hM_le_2N
    have h1 : 1 / Real.sqrt (2 * (N : ℝ)) ≤ (1001 / 1000 : ℝ) * (1 / Real.sqrt (M : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hM_pos)]
      linarith only [hsq_cmp]
    calc _ ≤ (1001 / 1000 : ℝ) * (1 / Real.sqrt (M : ℝ)) := h1
      _ ≤ (1001 / 1000 : ℝ) * ((1226 / 100 / 447 : ℝ) / Real.log (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv_sqrtM (by norm_num)
      _ = ((1001 / 1000 : ℝ) * (1226 / 100) / 447) / Real.log (M : ℝ) := by ring
  -- (4) extra E_card / N
  have hterm_ext : (E_card : ℝ) / (N : ℝ) ≤
      ((eCoeff * mOverN) * (1226 / 100) / 447) / Real.log (M : ℝ) := by
    have hM_div_N : (M : ℝ) / (N : ℝ) ≤ mOverN := by rw [div_le_iff₀ hN_posR]; linarith only [hN_lo]
    have h2 : Real.sqrt (M : ℝ) / (N : ℝ) = ((M : ℝ) / (N : ℝ)) * (1 / Real.sqrt (M : ℝ)) := by
      have hsqM : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := Real.mul_self_sqrt hM_pos.le
      have hsq0 : Real.sqrt (M : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hM_pos).ne'
      field_simp; linarith only [hsqM]
    calc (E_card : ℝ) / (N : ℝ)
        ≤ (eCoeff * Real.sqrt (M : ℝ)) / (N : ℝ) := div_le_div_of_nonneg_right hE_le hN_posR.le
      _ = eCoeff * (((M : ℝ) / (N : ℝ)) * (1 / Real.sqrt (M : ℝ))) := by rw [← h2]; ring
      _ ≤ eCoeff * (mOverN * (1 / Real.sqrt (M : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM_div_N (by positivity)) heCoeff_nn
      _ = (eCoeff * mOverN) * (1 / Real.sqrt (M : ℝ)) := by ring
      _ ≤ (eCoeff * mOverN) * ((1226 / 100 / 447 : ℝ) / Real.log (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv_sqrtM (mul_nonneg heCoeff_nn hmOverN_pos.le)
      _ = ((eCoeff * mOverN) * (1226 / 100) / 447) / Real.log (M : ℝ) := by ring
  -- (5) Chebyshev primeCounting(pMax) / N
  let x : ℝ := xCoeff * (M : ℝ)
  let x0 : ℝ := xCoeff * (200000 : ℝ)
  have hx0_le_x : x0 ≤ x := by dsimp [x, x0]; gcongr
  have hx_ge16 : 16 ≤ x := le_trans hx0_ge16 hx0_le_x
  have hx_pos : 0 < x := by linarith
  have hpi_mono : Nat.primeCounting pMax ≤ Nat.primeCounting ⌊x⌋₊ :=
    Nat.monotone_primeCounting (Nat.le_floor hpMax_le)
  have hpi_cheb := primeCounting_le_cheb_34 hx_ge16
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le hlx_pos hlx_ge
  have hinv_sqrt_x : 1 / Real.sqrt x ≤ (1226 / 100 / x0Sq) / Real.log x :=
    sqrt_div_log_ge (by linarith) hx0_le_x hx0_log_hi (by linarith) hx0_sq hx0_sq_pos
  have hinv_qrt_x : 1 / Real.sqrt (Real.sqrt x) ≤ (1226 / 100 / x0Qrt) / Real.log x :=
    sqrt_sqrt_div_log_ge (by linarith) hx0_le_x hx0_log_hi hx0_log_lo hx0_qrt hx0_qrt_pos
  have hinv_logx : 1 / Real.log x ≤ (1 / alpha) / Real.log (M : ℝ) := by
    rw [div_div, div_le_div_iff₀ hlogx_pos (mul_pos halpha_pos hLM_pos)]
    linarith only [hlog_x_ge]
  have hpi_div_x : (Nat.primeCounting pMax : ℝ) / x ≤
      (1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
        4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
        (209 / 100) * (1226 / 100) / (x0Sq * alpha)) / Real.log (M : ℝ) := by
    have hpi_le_cheb : (Nat.primeCounting pMax : ℝ) ≤
        Real.log 4 * (x / Real.log x + Real.sqrt x / (Real.log 2) ^ 2 +
          4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
          (16 / 9 : ℝ) * x / (Real.log x) ^ 2) :=
      le_trans (by exact_mod_cast hpi_mono) hpi_cheb
    have hinner_nn : 0 ≤ x / Real.log x + Real.sqrt x / (Real.log 2) ^ 2 +
        4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
        (16 / 9 : ℝ) * x / (Real.log x) ^ 2 := by positivity
    have hpi_le2 : (Nat.primeCounting pMax : ℝ) ≤
        (1387 / 1000 : ℝ) * (x / Real.log x + Real.sqrt x / (Real.log 2) ^ 2 +
          4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
          (16 / 9 : ℝ) * x / (Real.log x) ^ 2) :=
      le_trans hpi_le_cheb (mul_le_mul_of_nonneg_right hlog4_lt.le hinner_nn)
    have hdiv_eq : (x / Real.log x + Real.sqrt x / (Real.log 2) ^ 2 +
          4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
          (16 / 9 : ℝ) * x / (Real.log x) ^ 2) / x =
        1 / Real.log x + (1 / (Real.log 2) ^ 2) * (1 / Real.sqrt x) +
          4 * (1 / Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
          (16 / 9 : ℝ) / (Real.log x) ^ 2 := by
      have hsqx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx_pos.le
      have hqqx : Real.sqrt (Real.sqrt x) * Real.sqrt (Real.sqrt x) = Real.sqrt x :=
        Real.mul_self_sqrt (Real.sqrt_nonneg _)
      have hne1 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx_pos).ne'
      have hne2 : Real.sqrt (Real.sqrt x) ≠ 0 := (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx_pos)).ne'
      have hne3 : Real.log x ≠ 0 := hlogx_pos.ne'
      have hne4 : Real.log 2 ≠ 0 := by linarith only [hlog2_gt]
      have ha : (x / Real.log x) / x = 1 / Real.log x := by field_simp
      have hb : (Real.sqrt x / (Real.log 2) ^ 2) / x = (1 / (Real.log 2) ^ 2) * (1 / Real.sqrt x) := by
        have h1 : Real.sqrt x / x = 1 / Real.sqrt x := by
          rw [div_eq_div_iff hx_pos.ne' hne1, one_mul, hsqx]
        calc (Real.sqrt x / (Real.log 2) ^ 2) / x
            = (1 / (Real.log 2) ^ 2) * (Real.sqrt x / x) := by ring
          _ = (1 / (Real.log 2) ^ 2) * (1 / Real.sqrt x) := by rw [h1]
      have hc : (4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2) / x =
          4 * (1 / Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 := by
        have h1 : (Real.sqrt x * Real.sqrt (Real.sqrt x)) / x = 1 / Real.sqrt (Real.sqrt x) := by
          rw [div_eq_div_iff hx_pos.ne' hne2, one_mul, mul_assoc, hqqx, hsqx]
        calc (4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2) / x
            = (4 / (Real.log x) ^ 2) * ((Real.sqrt x * Real.sqrt (Real.sqrt x)) / x) := by ring
          _ = (4 / (Real.log x) ^ 2) * (1 / Real.sqrt (Real.sqrt x)) := by rw [h1]
          _ = 4 * (1 / Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 := by ring
      have hd : ((16 / 9 : ℝ) * x / (Real.log x) ^ 2) / x = (16 / 9 : ℝ) / (Real.log x) ^ 2 := by
        field_simp
      rw [add_div, add_div, add_div, ha, hb, hc, hd]
    have ht1 : 1 / Real.log x ≤ (1 / alpha) / Real.log (M : ℝ) := hinv_logx
    have ht2 : (16 / 9 : ℝ) / (Real.log x) ^ 2 ≤ ((16 / 9 : ℝ) / (alpha * lxLo)) / Real.log (M : ℝ) := by
      have h1 : (16 / 9 : ℝ) / (Real.log x) ^ 2 = ((16 / 9 : ℝ) / Real.log x) * (1 / Real.log x) := by ring
      have h2 : (16 / 9 : ℝ) / Real.log x ≤ (16 / 9 : ℝ) / lxLo := by gcongr
      calc (16 / 9 : ℝ) / (Real.log x) ^ 2
          = ((16 / 9 : ℝ) / Real.log x) * (1 / Real.log x) := h1
        _ ≤ ((16 / 9 : ℝ) / lxLo) * ((1 / alpha) / Real.log (M : ℝ)) :=
            mul_le_mul h2 hinv_logx (by positivity) (by positivity)
        _ = ((16 / 9 : ℝ) / (alpha * lxLo)) / Real.log (M : ℝ) := by ring
    have ht3 : 4 * (1 / Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 ≤
        (4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha)) / Real.log (M : ℝ) := by
      have hlogsq : 1 / (Real.log x) ^ 2 ≤ 1 / lxLo ^ 2 := by gcongr
      have hqrt_M : 1 / Real.sqrt (Real.sqrt x) ≤ (1226 / 100 / (x0Qrt * alpha)) / Real.log (M : ℝ) := by
        calc 1 / Real.sqrt (Real.sqrt x)
            ≤ (1226 / 100 / x0Qrt) * (1 / Real.log x) := by rw [← div_eq_mul_one_div]; exact hinv_qrt_x
          _ ≤ (1226 / 100 / x0Qrt) * ((1 / alpha) / Real.log (M : ℝ)) := by gcongr
          _ = (1226 / 100 / (x0Qrt * alpha)) / Real.log (M : ℝ) := by ring
      calc 4 * (1 / Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2
          = 4 * (1 / Real.sqrt (Real.sqrt x)) * (1 / (Real.log x) ^ 2) := by ring
        _ ≤ 4 * ((1226 / 100 / (x0Qrt * alpha)) / Real.log (M : ℝ)) * (1 / lxLo ^ 2) := by gcongr
        _ = (4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha)) / Real.log (M : ℝ) := by ring
    have ht4 : (1 / (Real.log 2) ^ 2) * (1 / Real.sqrt x) ≤
        ((209 / 100) * (1226 / 100) / (x0Sq * alpha)) / Real.log (M : ℝ) := by
      have hsq_M : 1 / Real.sqrt x ≤ (1226 / 100 / (x0Sq * alpha)) / Real.log (M : ℝ) := by
        calc 1 / Real.sqrt x
            ≤ (1226 / 100 / x0Sq) * (1 / Real.log x) := by rw [← div_eq_mul_one_div]; exact hinv_sqrt_x
          _ ≤ (1226 / 100 / x0Sq) * ((1 / alpha) / Real.log (M : ℝ)) := by gcongr
          _ = (1226 / 100 / (x0Sq * alpha)) / Real.log (M : ℝ) := by ring
      calc (1 / (Real.log 2) ^ 2) * (1 / Real.sqrt x)
          ≤ (209 / 100 : ℝ) * ((1226 / 100 / (x0Sq * alpha)) / Real.log (M : ℝ)) :=
            mul_le_mul hinv_log2_sq hsq_M (by positivity) (by norm_num)
        _ = ((209 / 100) * (1226 / 100) / (x0Sq * alpha)) / Real.log (M : ℝ) := by ring
    calc (Nat.primeCounting pMax : ℝ) / x
        ≤ (1387 / 1000 : ℝ) * ((x / Real.log x + Real.sqrt x / (Real.log 2) ^ 2 +
            4 * (Real.sqrt x * Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
            (16 / 9 : ℝ) * x / (Real.log x) ^ 2) / x) := by
          rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hpi_le2 hx_pos.le
      _ = (1387 / 1000 : ℝ) * (1 / Real.log x + (1 / (Real.log 2) ^ 2) * (1 / Real.sqrt x) +
            4 * (1 / Real.sqrt (Real.sqrt x)) / (Real.log x) ^ 2 +
            (16 / 9 : ℝ) / (Real.log x) ^ 2) := by rw [hdiv_eq]
      _ ≤ (1387 / 1000 : ℝ) * ((1 / alpha) / Real.log (M : ℝ) +
            ((209 / 100) * (1226 / 100) / (x0Sq * alpha)) / Real.log (M : ℝ) +
            (4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha)) / Real.log (M : ℝ) +
            ((16 / 9 : ℝ) / (alpha * lxLo)) / Real.log (M : ℝ)) := by gcongr
      _ = (1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
            4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
            (209 / 100) * (1226 / 100) / (x0Sq * alpha)) / Real.log (M : ℝ) := by ring
  have hterm_pi : (Nat.primeCounting pMax : ℝ) / (N : ℝ) ≤
      (xCoeff * mOverN * (1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
        4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
        (209 / 100) * (1226 / 100) / (x0Sq * alpha))) / Real.log (M : ℝ) := by
    have hx_div_N : x / (N : ℝ) ≤ xCoeff * mOverN := by
      dsimp [x]; rw [div_le_iff₀ hN_posR]
      calc xCoeff * (M : ℝ) ≤ xCoeff * (mOverN * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hN_lo hxCoeff_pos.le
        _ = xCoeff * mOverN * (N : ℝ) := by ring
    have hpi_nn : 0 ≤ (Nat.primeCounting pMax : ℝ) / x := by positivity
    calc (Nat.primeCounting pMax : ℝ) / (N : ℝ)
        = (x / (N : ℝ)) * ((Nat.primeCounting pMax : ℝ) / x) := by field_simp
      _ ≤ (xCoeff * mOverN) * ((1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
            4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
            (209 / 100) * (1226 / 100) / (x0Sq * alpha)) / Real.log (M : ℝ)) :=
          mul_le_mul hx_div_N hpi_div_x hpi_nn (by positivity)
      _ = _ := by ring
  -- Combine all 5 RHS terms / N <= (280/100) / L
  have hrhs_div_N :
      (((2 ^ g.primeFactors.card : ℝ) - 1) +
        2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) +
        (N : ℝ) * (1 / ((Y1 : ℝ) + 1)) +
        Real.sqrt (2 * (N : ℝ)) / 2 +
        (Nat.primeCounting pMax : ℝ) +
        (E_card : ℝ)) / (N : ℝ) ≤ (280 / 100 : ℝ) / Real.log (M : ℝ) := by
    have hsplit_N :
        (((2 ^ g.primeFactors.card : ℝ) - 1) +
          2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) +
          (N : ℝ) * (1 / ((Y1 : ℝ) + 1)) +
          Real.sqrt (2 * (N : ℝ)) / 2 +
          (Nat.primeCounting pMax : ℝ) +
          (E_card : ℝ)) / (N : ℝ) =
        (((2 ^ g.primeFactors.card : ℝ) - 1) +
          2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ)) / (N : ℝ) +
        1 / ((Y1 : ℝ) + 1) +
        (Real.sqrt (2 * (N : ℝ)) / 2) / (N : ℝ) +
        (Nat.primeCounting pMax : ℝ) / (N : ℝ) +
        (E_card : ℝ) / (N : ℝ) := by
      rw [add_div, add_div, add_div, add_div, mul_div_cancel_left₀ _ hN_posR.ne']
    rw [hsplit_N]
    have hsum_le :
        (((1233 / 100 : ℝ) * (1226 / 100) / 447) +
          ((1226 / 100 : ℝ) / 42) +
          ((1001 / 1000 : ℝ) * (1226 / 100) / 447) +
          (xCoeff * mOverN * (1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
            4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
            (209 / 100) * (1226 / 100) / (x0Sq * alpha))) +
          ((eCoeff * mOverN) * (1226 / 100) / 447)) / Real.log (M : ℝ) ≤
        (280 / 100 : ℝ) / Real.log (M : ℝ) := by
      exact div_le_div_of_nonneg_right (by linarith only [hctot]) hLM_pos.le
    have hadd_div :
        ((1233 / 100 : ℝ) * (1226 / 100) / 447) / Real.log (M : ℝ) +
          ((1226 / 100 : ℝ) / 42) / Real.log (M : ℝ) +
          ((1001 / 1000 : ℝ) * (1226 / 100) / 447) / Real.log (M : ℝ) +
          (xCoeff * mOverN * (1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
            4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
            (209 / 100) * (1226 / 100) / (x0Sq * alpha))) / Real.log (M : ℝ) +
          ((eCoeff * mOverN) * (1226 / 100) / 447) / Real.log (M : ℝ) =
        (((1233 / 100 : ℝ) * (1226 / 100) / 447) +
          ((1226 / 100 : ℝ) / 42) +
          ((1001 / 1000 : ℝ) * (1226 / 100) / 447) +
          (xCoeff * mOverN * (1387 / 1000 : ℝ) * (1 / alpha + (16 / 9 : ℝ) / (alpha * lxLo) +
            4 * (1226 / 100) / (x0Qrt * lxLo ^ 2 * alpha) +
            (209 / 100) * (1226 / 100) / (x0Sq * alpha))) +
          ((eCoeff * mOverN) * (1226 / 100) / 447)) / Real.log (M : ℝ) := by ring
    linarith only [hterm_tail, hterm_mob, hterm_sq, hterm_ext, hterm_pi, hadd_div, hsum_le]
  -- Compare (280/100)/L < phi_r * (1 - S_sm) by cubing both sides!
  obtain ⟨hmain_nn, hmain_cubed⟩ := phi_main_cubed_ge_large hg hg_odd hg_le hM Y1
  have hlt_cubed : ((280 / 100 : ℝ) / Real.log (M : ℝ)) ^ 3 < (158 / 1000 : ℝ) / Real.log (M : ℝ) := by
    rw [div_pow, div_lt_div_iff₀ (by positivity) hLM_pos]
    have hL2 : (12.188 : ℝ) ^ 2 < (Real.log (M : ℝ)) ^ 2 := by nlinarith only [hLM_gt]
    have hnum : (280 / 100 : ℝ) ^ 3 < (158 / 1000 : ℝ) * (12.188 : ℝ) ^ 2 := by norm_num
    nlinarith only [hL2, hnum, hLM_pos]
  have hlt_main : (280 / 100 : ℝ) / Real.log (M : ℝ) < phi_r * (1 - S_sm) := by
    by_contra hge
    push_neg at hge
    have h3 : (phi_r * (1 - S_sm)) ^ 3 ≤ ((280 / 100 : ℝ) / Real.log (M : ℝ)) ^ 3 := by gcongr
    linarith only [hmain_cubed, hlt_cubed, h3]
  have hrhs_lt : (((2 ^ g.primeFactors.card : ℝ) - 1) +
        2 * (S_sm_set.card : ℝ) * (2 ^ g.primeFactors.card : ℝ) +
        (N : ℝ) * (1 / ((Y1 : ℝ) + 1)) +
        Real.sqrt (2 * (N : ℝ)) / 2 +
        (Nat.primeCounting pMax : ℝ) +
        (E_card : ℝ)) / (N : ℝ) < phi_r * (1 - S_sm) := lt_of_le_of_lt hrhs_div_N hlt_main
  rw [div_lt_iff₀ hN_posR] at hrhs_lt
  linarith only [hrhs_lt]

private lemma odd_sq_mod4 (k : ℕ) (hk : k % 2 = 1) : k ^ 2 % 4 = 1 := by
  obtain ⟨t, rfl⟩ : ∃ t, k = 2 * t + 1 := ⟨k / 2, by omega⟩
  have : (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 := by ring
  omega

private lemma chk_0_1 :
    smallIntervalCheckProp 1072 500 0 (16 / 77) 21 (1156 / 1000) (578 / 1000) (32 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_0_2 :
    smallIntervalCheckProp 3000 1072 0 (192 / 1001) 38 (1156 / 1000) (578 / 1000) (22 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_0_3 :
    smallIntervalCheckProp 15000 3000 0 (3072 / 17017) 71 (1156 / 1000) (578 / 1000) (13 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_0_4 :
    smallIntervalCheckProp 100000 15000 0 (1216512 / 7436429) 265 (1156 / 1000) (578 / 1000) (6 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_1_1 :
    smallIntervalCheckProp 2144 499 16 (16 / 77) 21 (896 / 1000) (896 / 1000) (32 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_1_2 :
    smallIntervalCheckProp 6001 1072 16 (192 / 1001) 38 (896 / 1000) (896 / 1000) (22 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_1_3 :
    smallIntervalCheckProp 30001 3000 32 (3072 / 17017) 71 (896 / 1000) (896 / 1000) (13 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_1_4 :
    smallIntervalCheckProp 200001 15000 64 (1216512 / 7436429) 265 (896 / 1000) (896 / 1000) (6 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_23_1 :
    smallIntervalCheckProp 2144 999 0 (16 / 77) 21 1 0 (23 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_23_2 :
    smallIntervalCheckProp 6001 2144 0 (192 / 1001) 38 1 0 (16 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_23_3 :
    smallIntervalCheckProp 30001 6001 0 (3072 / 17017) 71 1 0 (10 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

private lemma chk_23_4 :
    smallIntervalCheckProp 200001 30001 0 (1216512 / 7436429) 265 1 0 (5 / 1000) := by
  unfold smallIntervalCheckProp; intro h3 h5 h7; dsimp only
  cases h3 <;> cases h5 <;> cases h7 <;>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> norm_num at h <;> norm_num

-- Case 1: 4 ∣ n
private lemma H2_case_mod4_0 {n M : ℕ} (hM999 : 999 ≤ M)
    (hM_lo : M ^ 2 < n) (hM_hi : n ≤ (M + 1) ^ 2) (h4n : 4 ∣ n) :
    OMA.S_oeis_a085265.IsTerm n := by
  have hn_pos : 0 < n := by nlinarith
  obtain ⟨hg_sq, hg2_dvd, hg_le, hg_iff⟩ := sq_part_props hn_pos hM_hi
  let g := ∏ p ∈ n.primeFactors.filter (fun p => p ^ 2 ∣ n), p
  have h2g : 2 ∣ g := (hg_iff 2 Nat.prime_two).mpr h4n
  let g' := g / 2
  have hg_eq : 2 * g' = g := Nat.mul_div_cancel' h2g
  have hg'_sq : Squarefree g' :=
    hg_sq.squarefree_of_dvd (show g' ∣ g by rw [← hg_eq]; exact dvd_mul_left g' 2)
  have hg'_odd : g' % 2 = 1 := by
    by_contra heven
    have h2g' : 2 ∣ g' := by omega
    have h4g : 2 * 2 ∣ g := by
      rw [← hg_eq]; exact mul_dvd_mul_left 2 h2g'
    exact Nat.prime_two.not_isUnit (hg_sq 2 h4g)
  have hg'_le : g' ≤ (M + 1) / 2 := by omega
  let N := (M + 1) / 2
  let pMax := Nat.sqrt (n / 3)
  have hN_le : ∀ j ∈ Finset.Icc 1 N, 1 ≤ 2 * j ∧ 1 ≤ 2 * j - 1 ∧ (2 * j - 1) ^ 2 < n := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hleM : 2 * j - 1 ≤ M := by omega
    exact ⟨by omega, by omega, by nlinarith⟩
  have hno4 : ∀ j ∈ Finset.Icc 1 N, ¬ 4 ∣ n - (2 * j - 1) ^ 2 := by
    intro j hj hd
    have hlt := (hN_le j hj).2.2
    have hodd : (2 * j - 1) ^ 2 % 4 = 1 :=
      odd_sq_mod4 (2 * j - 1) (by have := (Finset.mem_Icc.mp hj).1; omega)
    obtain ⟨q, hq⟩ := h4n
    obtain ⟨r, hr⟩ := hd
    omega
  have hno_g : ∀ j ∈ Finset.Icc 1 N, (2 * j - 1).Coprime g' →
      ∀ p : ℕ, p.Prime → p ∣ g' → ¬ p ^ 2 ∣ n - (2 * j - 1) ^ 2 := by
    intro j hj hcop p hp hpg' hd
    have hlt := (hN_le j hj).2.2
    have hpg : p ∣ g := hpg'.trans (by rw [← hg_eq]; exact dvd_mul_left g' 2)
    have hp2n : p ^ 2 ∣ n := (hg_iff p hp).mp hpg
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hp2n
    have hpk := (prime_sq_dvd_sub_sq_elim hp hlt hd hpn).2
    have hpd : p ∣ Nat.gcd (2 * j - 1) g' := Nat.dvd_gcd hpk hpg'
    rw [hcop] at hpd
    exact hp.not_dvd_one hpd
  have hcover : ¬ OMA.S_oeis_a085265.IsTerm n →
      ∀ j ∈ Finset.Icc 1 N, (2 * j - 1).Coprime g' →
        j ∈ (∅ : Finset ℕ) ∨
        ∃ p ∈ (Finset.Icc 3 pMax).filter (fun p => p.Prime ∧ ¬ p ∣ g' ∧ ¬ p ∣ n),
          p ^ 2 ∣ n - (2 * j - 1) ^ 2 := by
    intro hnot j hj hcop
    right
    have hlt := (hN_le j hj).2.2
    have hpos_sub : 1 ≤ n - (2 * j - 1) ^ 2 := by omega
    have hns : ¬ Squarefree (n - (2 * j - 1) ^ 2) := fun hsq =>
      hnot ⟨n - (2 * j - 1) ^ 2, 2 * j - 1, hpos_sub, hsq, (hN_le j hj).2.1, Nat.sub_add_cancel hlt.le⟩
    obtain ⟨p, hp, hp2⟩ := exists_sq_factor_of_not_squarefree hpos_sub hns
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2; exact hno4 j hj (by simpa using hp2)
    have hp_ge3 : 3 ≤ p := by have := hp.two_le; omega
    have hpn : ¬ p ∣ n := by
      intro hpn
      have hp2n := (prime_sq_dvd_sub_sq_elim hp hlt hp2 hpn).1
      have hpg : p ∣ g := (hg_iff p hp).mpr hp2n
      have hpg' : p ∣ g' := by
        rw [← hg_eq] at hpg
        have hcop_p2 : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr (by
          intro h2; have := Nat.le_of_dvd (by norm_num) h2; omega)
        exact hcop_p2.dvd_of_dvd_mul_left hpg
      exact hno_g j hj hcop p hp hpg' hp2
    have hpg' : ¬ p ∣ g' := fun h => hno_g j hj hcop p hp h hp2
    -- Prove 3 * p^2 <= n - (2j-1)^2 < n, so p <= pMax
    obtain ⟨m, hm⟩ := hp2
    have hm_ge3 : 3 ≤ m := by
      have hsub_mod4 : (n - (2 * j - 1) ^ 2) % 4 = 3 := by
        have hodd : (2 * j - 1) ^ 2 % 4 = 1 :=
          odd_sq_mod4 (2 * j - 1) (by have := (Finset.mem_Icc.mp hj).1; omega)
        obtain ⟨q, hq⟩ := h4n
        omega
      have hp2_mod4 : p ^ 2 % 4 = 1 := odd_sq_mod4 p (by have := hp.eq_two_or_odd; omega)
      have hm_mod4 : m % 4 = 3 := by
        have : (p ^ 2 * m) % 4 = 3 := by rwa [← hm]
        rw [Nat.mul_mod, hp2_mod4, one_mul] at this
        omega
      omega
    have hp_le : p ≤ pMax := by
      refine Nat.le_sqrt.mpr ?_
      have hsub_le : n - (2 * j - 1) ^ 2 ≤ n := Nat.sub_le _ _
      have h3p : 3 * (p * p) ≤ n := by rw [← sq]; nlinarith only [hm, hm_ge3, hsub_le]
      exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_ge3, hp_le⟩, hp, hpg', hpn⟩, ⟨m, hm⟩⟩
  have hpMax_N : (pMax : ℝ) ≤ (1156 / 1000 : ℝ) * (N : ℝ) + 578 / 1000 := by
    have h3 : 3 * pMax ^ 2 ≤ n := by
      have h1 : pMax * pMax ≤ n / 3 := Nat.sqrt_le (n / 3); rw [sq]; omega
    have hle : 3 * pMax ^ 2 ≤ (2 * N + 1) ^ 2 := by
      have : M + 1 ≤ 2 * N + 1 := by omega
      nlinarith
    have hleR : (3 : ℝ) * (pMax : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 1) ^ 2 := by exact_mod_cast hle
    have hsq : (pMax : ℝ) ^ 2 ≤ ((578 / 1000 : ℝ) * (2 * (N : ℝ) + 1)) ^ 2 := by nlinarith
    have hnn1 : 0 ≤ (pMax : ℝ) := by positivity
    have hnn2 : 0 ≤ (578 / 1000 : ℝ) * (2 * (N : ℝ) + 1) := by positivity
    have : (pMax : ℝ) ≤ (578 / 1000 : ℝ) * (2 * (N : ℝ) + 1) := by nlinarith
    linarith
  by_cases hM_lt : M < 200000
  · refine sieve_master_bound (Y1 := 7) (by norm_num) (by norm_num) hg'_sq hg'_odd (Or.inr rfl)
      (by norm_num) (by norm_num) hN_le hno4 hno_g ∅ hcover (81 / 1000)
      (sum_two_div_prime_sq_gt7 pMax) ?_
    simp only [Finset.card_empty]
    by_cases h1 : M ≤ 2143
    · exact small_regime_arith (e_ub := 0) hg'_sq hg'_odd (by omega) (primeCounting_le_Q11 pMax)
        (Nat.cast_pos.mpr (by omega))
        (small_interval_check (g_max := 1072) (N_lo := 500) (by omega) (by omega) hpMax_N
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (32 / 1000)
          (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_0_1)
        (by omega)
    · by_cases h2 : M ≤ 6000
      · exact small_regime_arith (e_ub := 0) hg'_sq hg'_odd (by omega) (primeCounting_le_Q13 pMax)
          (Nat.cast_pos.mpr (by omega))
          (small_interval_check (g_max := 3000) (N_lo := 1072) (by omega) (by omega) hpMax_N
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (22 / 1000)
            (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_0_2)
          (by omega)
      · by_cases h3 : M ≤ 30000
        · exact small_regime_arith (e_ub := 0) hg'_sq hg'_odd (by omega) (primeCounting_le_Q17 pMax)
            (Nat.cast_pos.mpr (by omega))
            (small_interval_check (g_max := 15000) (N_lo := 3000) (by omega) (by omega) hpMax_N
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (13 / 1000)
              (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_0_3)
            (by omega)
        · exact small_regime_arith (e_ub := 0) hg'_sq hg'_odd (by omega) (primeCounting_le_Q23 pMax)
            (Nat.cast_pos.mpr (by omega))
            (small_interval_check (g_max := 100000) (N_lo := 15000) (by omega) (by omega) hpMax_N
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (6 / 1000)
              (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_0_4)
            (by omega)
  · push_neg at hM_lt
    let s := Nat.sqrt (Nat.sqrt M)
    have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (Nat.le_sqrt.mpr (by omega))
    let Y1 := 2 * s + 1
    refine sieve_master_bound (Y1 := Y1) (by omega) (by omega) hg'_sq hg'_odd (Or.inr rfl)
      (by norm_num) (by norm_num) hN_le hno4 hno_g ∅ hcover (1 / ((Y1 : ℝ) + 1))
      (sum_two_div_odd_sq_le Y1 pMax (by omega) (by omega)) ?_
    simp only [Finset.card_empty]
    have hpMax_M : (pMax : ℝ) ≤ (5775 / 10000 : ℝ) * (M : ℝ) := by
      have h3 : 3 * pMax ^ 2 ≤ n := by have h1 : pMax * pMax ≤ n / 3 := Nat.sqrt_le (n / 3); rw [sq]; omega
      have hleR : (3 : ℝ) * (pMax : ℝ) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 := by exact_mod_cast (h3.trans hM_hi)
      have hMR : (200000 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_lt
      have hsq : (pMax : ℝ) ^ 2 ≤ ((5775 / 10000 : ℝ) * (M : ℝ)) ^ 2 := by nlinarith
      nlinarith [show (0 : ℝ) ≤ (pMax : ℝ) by positivity]
    have hlog2_gt : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog3_gt : (1.098612 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hlog3_lt : Real.log 3 < (1.098613 : ℝ) := by linarith [Real.log_three_lt_d9]
    have hlog_c : -(55 / 100 : ℝ) ≤ Real.log (5775 / 10000 : ℝ) := by
      have hsq3 : (1 / Real.sqrt 3 : ℝ) ≤ 5775 / 10000 := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num))]
        have : (1 : ℝ) ^ 2 ≤ ((5775 / 10000 : ℝ) * Real.sqrt 3) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
        nlinarith [Real.sqrt_nonneg 3]
      have hlog1 := Real.log_le_log (by positivity) hsq3
      rw [one_div, Real.log_inv, Real.log_sqrt (by norm_num)] at hlog1
      linarith
    have hLM_gt : (12.188 : ℝ) < Real.log (M : ℝ) := by
      have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (M : ℝ) := by
        have hM2 : (200000 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_lt
        have h196 : (3 : ℝ) * (2 : ℝ) ^ 16 < 200000 := by norm_num
        linarith
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hL200_gt : (12.188 : ℝ) < Real.log (200000 : ℝ) := by
      have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (200000 : ℝ) := by norm_num
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hL200_lt : Real.log (200000 : ℝ) ≤ 1226 / 100 := by
      have hlog2_lt : Real.log 2 < (0.693148 : ℝ) := by linarith [Real.log_two_lt_d9]
      have h1 : (200000 : ℝ) < (2 : ℝ) ^ 5 * (3 : ℝ) ^ 8 := by norm_num
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
      push_cast at hlog; linarith
    exact large_regime_arith (xCoeff := 5775 / 10000) (xAdd := 0) (eCoeff := 0)
      (alpha := 954 / 1000) (lxLo := 11638 / 1000) (x0Sq := 339) (x0Qrt := 18) (mOverN := 2)
      hM_lt hg'_sq hg'_odd (by omega)
      (by exact_mod_cast (by omega : M ≤ 2 * N)) (by norm_num) (by norm_num) (by omega)
      (by
        have h1 : M ≤ 2 * N + 1 := by omega
        have h1R : (M : ℝ) ≤ 2 * (N : ℝ) + 1 := by exact_mod_cast h1
        linarith)
      hpMax_M (by norm_num)
      (by rw [Real.log_mul (by norm_num) (by positivity)]; linarith only [hlog_c, hLM_gt])
      (by norm_num)
      (by rw [Real.log_mul (by norm_num) (by positivity)]; linarith only [hlog_c, hLM_gt])
      (by norm_num) (by norm_num)
      (by rw [Real.log_mul (by norm_num) (by norm_num)]; linarith only [hlog_c, hL200_gt])
      (by
        have hlt : (5775 / 10000 : ℝ) * 200000 ≤ 200000 := by norm_num
        exact le_trans (Real.log_le_log (by norm_num) hlt) hL200_lt)
      (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
      (by rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)
      (by norm_num)
      0 (by simp) (by norm_num) (by norm_num)

-- Case 2: n % 4 = 1
set_option maxHeartbeats 400000 in
private lemma H2_case_mod4_1 {n M : ℕ} (hM999 : 999 ≤ M)
    (hM_lo : M ^ 2 < n) (hM_hi : n ≤ (M + 1) ^ 2) (hn4 : n % 4 = 1) :
    OMA.S_oeis_a085265.IsTerm n := by
  have hn_pos : 0 < n := by nlinarith
  obtain ⟨hg_sq, hg2_dvd, hg_le, hg_iff⟩ := sq_part_props hn_pos hM_hi
  let g := ∏ p ∈ n.primeFactors.filter (fun p => p ^ 2 ∣ n), p
  have hg_odd : g % 2 = 1 := by
    by_contra heven
    have h2g : 2 ∣ g := by omega
    have h4n : 4 ∣ n := (hg_iff 2 Nat.prime_two).mp h2g
    omega
  let N := M / 2
  let pMax := Nat.sqrt (n / 5)
  let E := evenSqPrimeSet n M
  have hN_le : ∀ j ∈ Finset.Icc 1 N, 0 ≤ 2 * j ∧ 1 ≤ 2 * j - 0 ∧ (2 * j - 0) ^ 2 < n := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hleM : 2 * j ≤ M := by omega
    exact ⟨Nat.zero_le _, by omega, by simp only [Nat.sub_zero]; nlinarith⟩
  have hno4 : ∀ j ∈ Finset.Icc 1 N, ¬ 4 ∣ n - (2 * j - 0) ^ 2 := by
    intro j hj hd
    have hlt := (hN_le j hj).2.2
    have h4sq : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
    simp only [Nat.sub_zero] at hd hlt
    rw [h4sq] at hd hlt
    obtain ⟨r, hr⟩ := hd
    omega
  have hno_g : ∀ j ∈ Finset.Icc 1 N, (2 * j - 0).Coprime g →
      ∀ p : ℕ, p.Prime → p ∣ g → ¬ p ^ 2 ∣ n - (2 * j - 0) ^ 2 := by
    intro j hj hcop p hp hpg hd
    have hlt := (hN_le j hj).2.2
    have hp2n : p ^ 2 ∣ n := (hg_iff p hp).mp hpg
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hp2n
    have hpk := (prime_sq_dvd_sub_sq_elim hp hlt hd hpn).2
    have hpd : p ∣ Nat.gcd (2 * j - 0) g := Nat.dvd_gcd hpk hpg
    rw [hcop] at hpd
    exact hp.not_dvd_one hpd
  have hcover : ¬ OMA.S_oeis_a085265.IsTerm n →
      ∀ j ∈ Finset.Icc 1 N, (2 * j - 0).Coprime g →
        j ∈ E ∨
        ∃ p ∈ (Finset.Icc 3 pMax).filter (fun p => p.Prime ∧ ¬ p ∣ g ∧ ¬ p ∣ n),
          p ^ 2 ∣ n - (2 * j - 0) ^ 2 := by
    intro hnot j hj hcop
    have hlt := (hN_le j hj).2.2
    have hpos_sub : 1 ≤ n - (2 * j - 0) ^ 2 := by omega
    have hns : ¬ Squarefree (n - (2 * j - 0) ^ 2) := fun hsq =>
      hnot ⟨n - (2 * j - 0) ^ 2, 2 * j - 0, hpos_sub, hsq, (hN_le j hj).2.1, Nat.sub_add_cancel hlt.le⟩
    obtain ⟨p, hp, hp2⟩ := exists_sq_factor_of_not_squarefree hpos_sub hns
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2; exact hno4 j hj (by simpa using hp2)
    have hp_ge3 : 3 ≤ p := by have := hp.two_le; omega
    have hpn : ¬ p ∣ n := by
      intro hpn
      have hp2n := (prime_sq_dvd_sub_sq_elim hp hlt hp2 hpn).1
      have hpg : p ∣ g := (hg_iff p hp).mpr hp2n
      exact hno_g j hj hcop p hp hpg hp2
    have hpg : ¬ p ∣ g := fun h => hno_g j hj hcop p hp h hp2
    obtain ⟨m, hm⟩ := hp2
    have hm_mod4 : m % 4 = 1 := by
      have hsub_mod4 : (n - (2 * j - 0) ^ 2) % 4 = 1 := by
        simp only [Nat.sub_zero] at hlt ⊢
        have : (2 * j) ^ 2 = 4 * j ^ 2 := by ring
        rw [this] at hlt ⊢; omega
      have hp2_mod4 : p ^ 2 % 4 = 1 := by
        have hodd : p % 2 = 1 := by have := hp.eq_two_or_odd; omega
        obtain ⟨t, ht⟩ : ∃ t, p = 2 * t + 1 := ⟨p / 2, by omega⟩
        rw [ht]; have : (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 := by ring
        omega
      have : (p ^ 2 * m) % 4 = 1 := by rwa [← hm]
      rw [Nat.mul_mod, hp2_mod4, one_mul] at this
      simpa using this
    by_cases hm1 : m = 1
    · left
      rw [mem_evenSqPrimeSet]
      refine ⟨hj, p, hp, hpn, ?_⟩
      simp only [Nat.sub_zero] at hm hlt
      rw [hm1, mul_one] at hm
      omega
    · right
      have hm_ge5 : 5 ≤ m := by omega
      have hp_le : p ≤ pMax := by
        refine Nat.le_sqrt.mpr ?_
        have hsub_le : n - (2 * j - 0) ^ 2 ≤ n := Nat.sub_le _ _
        have h5p : 5 * (p * p) ≤ n := by rw [← sq]; nlinarith only [hm, hm_ge5, hsub_le]
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_ge3, hp_le⟩, hp, hpg, hpn⟩, ⟨m, hm⟩⟩
  have hE_info := card_even_sq_add_prime_sq_le (M := M) hn4 (by nlinarith)
  have hpMax_N : (pMax : ℝ) ≤ (896 / 1000 : ℝ) * (N : ℝ) + 896 / 1000 := by
    have h5 : 5 * pMax ^ 2 ≤ n := by have h1 : pMax * pMax ≤ n / 5 := Nat.sqrt_le (n / 5); rw [sq]; omega
    have hle : 5 * pMax ^ 2 ≤ (2 * N + 2) ^ 2 := by
      have : M + 1 ≤ 2 * N + 2 := by omega
      nlinarith
    have hleR : (5 : ℝ) * (pMax : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 2) ^ 2 := by exact_mod_cast hle
    have hsq : (pMax : ℝ) ^ 2 ≤ ((448 / 1000 : ℝ) * (2 * (N : ℝ) + 2)) ^ 2 := by nlinarith
    have hnn1 : 0 ≤ (pMax : ℝ) := by positivity
    have hnn2 : 0 ≤ (448 / 1000 : ℝ) * (2 * (N : ℝ) + 2) := by positivity
    have : (pMax : ℝ) ≤ (448 / 1000 : ℝ) * (2 * (N : ℝ) + 2) := by nlinarith
    linarith
  by_cases hM_lt : M < 200000
  · refine sieve_master_bound (Y1 := 7) (by norm_num) (by norm_num) hg_sq hg_odd (Or.inr rfl)
      (by norm_num) (by norm_num) hN_le hno4 hno_g E hcover (81 / 1000)
      (sum_two_div_prime_sq_gt7 pMax) ?_
    by_cases h1 : M ≤ 2143
    · have hE_ub : E.card ≤ 16 := by
        dsimp [E]
        rcases hE_info with h0 | ⟨h14, hle⟩
        · omega
        · have hb := (card_1mod4_primeFactors_bound hn_pos h14).1
          have hlt6 : n.primeFactors.card ≤ 5 := by
            by_contra h6; have := hb (by omega); nlinarith
          exact hle.trans ((Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : n.primeFactors.card - 1 ≤ 4)).trans (by norm_num))
      have hres := small_regime_arith (e_ub := 16) hg_sq hg_odd (by omega)
        (primeCounting_le_Q11 pMax) (Nat.cast_pos.mpr (by omega))
        (small_interval_check (g_max := 2144) (N_lo := 499) (by omega) (by omega) hpMax_N
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (32 / 1000)
          (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_1_1)
        (by omega)
      have hER : (E.card : ℝ) ≤ 16 := by exact_mod_cast hE_ub
      linarith
    · by_cases h2 : M ≤ 6000
      · have hE_ub : E.card ≤ 16 := by
          dsimp [E]
          rcases hE_info with h0 | ⟨h14, hle⟩
          · omega
          · have hb := (card_1mod4_primeFactors_bound hn_pos h14).1
            have hlt6 : n.primeFactors.card ≤ 5 := by
              by_contra h6; have := hb (by omega); nlinarith
            exact hle.trans ((Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : n.primeFactors.card - 1 ≤ 4)).trans (by norm_num))
        have hres := small_regime_arith (e_ub := 16) hg_sq hg_odd (by omega)
          (primeCounting_le_Q13 pMax) (Nat.cast_pos.mpr (by omega))
          (small_interval_check (g_max := 6001) (N_lo := 1072) (by omega) (by omega) hpMax_N
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (22 / 1000)
            (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_1_2)
          (by omega)
        have hER : (E.card : ℝ) ≤ 16 := by exact_mod_cast hE_ub
        linarith
      · by_cases h3 : M ≤ 30000
        · have hE_ub : E.card ≤ 32 := by
            dsimp [E]
            rcases hE_info with h0 | ⟨h14, hle⟩
            · omega
            · have hb := (card_1mod4_primeFactors_bound hn_pos h14).2.1
              have hlt7 : n.primeFactors.card ≤ 6 := by
                by_contra h7; have := hb (by omega); nlinarith
              exact hle.trans ((Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : n.primeFactors.card - 1 ≤ 5)).trans (by norm_num))
          have hres := small_regime_arith (e_ub := 32) hg_sq hg_odd (by omega)
            (primeCounting_le_Q17 pMax) (Nat.cast_pos.mpr (by omega))
            (small_interval_check (g_max := 30001) (N_lo := 3000) (by omega) (by omega) hpMax_N
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (13 / 1000)
              (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_1_3)
            (by omega)
          have hER : (E.card : ℝ) ≤ 32 := by exact_mod_cast hE_ub
          linarith
        · have hE_ub : E.card ≤ 64 := by
            dsimp [E]
            rcases hE_info with h0 | ⟨h14, hle⟩
            · omega
            · have hb := (card_1mod4_primeFactors_bound hn_pos h14).2.2.1
              have hlt8 : n.primeFactors.card ≤ 7 := by
                by_contra h8; have := hb (by omega); nlinarith
              exact hle.trans ((Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : n.primeFactors.card - 1 ≤ 6)).trans (by norm_num))
          have hres := small_regime_arith (e_ub := 64) hg_sq hg_odd (by omega)
            (primeCounting_le_Q23 pMax) (Nat.cast_pos.mpr (by omega))
            (small_interval_check (g_max := 200001) (N_lo := 15000) (by omega) (by omega) hpMax_N
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (6 / 1000)
              (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_1_4)
            (by omega)
          have hER : (E.card : ℝ) ≤ 64 := by exact_mod_cast hE_ub
          linarith
  · push_neg at hM_lt
    let s := Nat.sqrt (Nat.sqrt M)
    have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (Nat.le_sqrt.mpr (by omega))
    let Y1 := 2 * s + 1
    refine sieve_master_bound (Y1 := Y1) (by omega) (by omega) hg_sq hg_odd (Or.inr rfl)
      (by norm_num) (by norm_num) hN_le hno4 hno_g E hcover (1 / ((Y1 : ℝ) + 1))
      (sum_two_div_odd_sq_le Y1 pMax (by omega) (by omega)) ?_
    have hMR : (200000 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_lt
    have hE_le : (E.card : ℝ) ≤ (72 / 100 : ℝ) * Real.sqrt (M : ℝ) := by
      dsimp [E]
      rcases hE_info with h0 | ⟨h14, hle⟩
      · rw [h0, Nat.cast_zero]; positivity
      · have h65 := (card_1mod4_primeFactors_bound hn_pos h14).2.2.2
        have hpf_pos : 1 ≤ n.primeFactors.card := by
          obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (by nlinarith : n ≠ 1)
          exact Finset.card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqn, hn_pos.ne'⟩⟩
        have h2E : 2 * (evenSqPrimeSet n M).card ≤ 2 ^ n.primeFactors.card := by
          have hpow : 2 ^ n.primeFactors.card = 2 * 2 ^ (n.primeFactors.card - 1) := by
            conv_lhs => rw [← Nat.sub_add_cancel hpf_pos, pow_succ, mul_comm]
          omega
        have h4N : 65 * (2 * (evenSqPrimeSet n M).card) ^ 4 ≤ 256 * (M + 1) ^ 2 :=
          (Nat.mul_le_mul_left 65 (Nat.pow_le_pow_left h2E 4)).trans
            (h65.trans (Nat.mul_le_mul_left 256 hM_hi))
        have h4R : (65 : ℝ) * (2 * ((evenSqPrimeSet n M).card : ℝ)) ^ 4 ≤ 256 * ((M : ℝ) + 1) ^ 2 := by
          exact_mod_cast h4N
        have h4R' : (1040 : ℝ) * ((evenSqPrimeSet n M).card : ℝ) ^ 4 ≤ 256 * ((M : ℝ) + 1) ^ 2 := by
          have : (2 * ((evenSqPrimeSet n M).card : ℝ)) ^ 4 = 16 * ((evenSqPrimeSet n M).card : ℝ) ^ 4 := by ring
          linarith
        have hsq4 : ((72 / 100 : ℝ) * Real.sqrt (M : ℝ)) ^ 4 = (72 / 100 : ℝ) ^ 4 * (M : ℝ) ^ 2 := by
          rw [mul_pow, show (Real.sqrt (M : ℝ)) ^ 4 = ((Real.sqrt (M : ℝ)) ^ 2) ^ 2 by ring,
            Real.sq_sqrt (by linarith)]
        have hM1 : ((M : ℝ) + 1) ^ 2 ≤ (10001 / 10000 : ℝ) * (M : ℝ) ^ 2 := by nlinarith only [hMR]
        have hnum : (256 : ℝ) * (10001 / 10000 : ℝ) ≤ 1040 * (72 / 100 : ℝ) ^ 4 := by norm_num
        have hcmp : ((evenSqPrimeSet n M).card : ℝ) ^ 4 ≤ ((72 / 100 : ℝ) * Real.sqrt (M : ℝ)) ^ 4 := by
          rw [hsq4]
          nlinarith only [h4R', hM1, hnum, sq_nonneg (M : ℝ)]
        by_contra hlt
        push_neg at hlt
        have hnn : 0 ≤ (72 / 100 : ℝ) * Real.sqrt (M : ℝ) := by positivity
        have : ((72 / 100 : ℝ) * Real.sqrt (M : ℝ)) ^ 4 < ((evenSqPrimeSet n M).card : ℝ) ^ 4 := by gcongr
        linarith
    have hpMax_M : (pMax : ℝ) ≤ (4473 / 10000 : ℝ) * (M : ℝ) := by
      have h5 : 5 * pMax ^ 2 ≤ n := by have h1 : pMax * pMax ≤ n / 5 := Nat.sqrt_le (n / 5); rw [sq]; omega
      have hleR : (5 : ℝ) * (pMax : ℝ) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 := by exact_mod_cast (h5.trans hM_hi)
      have hsq : (pMax : ℝ) ^ 2 ≤ ((4473 / 10000 : ℝ) * (M : ℝ)) ^ 2 := by nlinarith
      nlinarith [show (0 : ℝ) ≤ (pMax : ℝ) by positivity]
    have hlog2_gt : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2_lt : Real.log 2 < (0.693148 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hlog3_gt : (1.098612 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hlog3_lt : Real.log 3 < (1.098613 : ℝ) := by linarith [Real.log_three_lt_d9]
    have hlog_c : -(811 / 1000 : ℝ) ≤ Real.log (4473 / 10000 : ℝ) := by
      have h49 : (4 / 9 : ℝ) ≤ 4473 / 10000 := by norm_num
      have hlog1 := Real.log_le_log (by norm_num) h49
      have h49_eq : Real.log (4 / 9 : ℝ) = 2 * Real.log 2 - 2 * Real.log 3 := by
        rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow, Real.log_pow]; ring
      linarith
    have hLM_gt : (12.188 : ℝ) < Real.log (M : ℝ) := by
      have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (M : ℝ) := by
        have h196 : (3 : ℝ) * (2 : ℝ) ^ 16 < 200000 := by norm_num
        linarith
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hL200_gt : (12.188 : ℝ) < Real.log (200000 : ℝ) := by
      have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (200000 : ℝ) := by norm_num
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hL200_lt : Real.log (200000 : ℝ) ≤ 1226 / 100 := by
      have h1 : (200000 : ℝ) < (2 : ℝ) ^ 5 * (3 : ℝ) ^ 8 := by norm_num
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hM_le_mN : (M : ℝ) ≤ (200002 / 100000 : ℝ) * (N : ℝ) := by
      have h1 : M ≤ 2 * N + 1 := by omega
      have h1R : (M : ℝ) ≤ 2 * (N : ℝ) + 1 := by exact_mod_cast h1
      have hN100 : (100000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 100000 ≤ N)
      linarith
    exact large_regime_arith (xCoeff := 4473 / 10000) (xAdd := 0) (eCoeff := 72 / 100)
      (alpha := 933 / 1000) (lxLo := 11377 / 1000) (x0Sq := 299) (x0Qrt := 17)
      (mOverN := 200002 / 100000)
      hM_lt hg_sq hg_odd hg_le hM_le_mN (by norm_num) (by norm_num) (by omega)
      (by
        have h1 : M ≤ 2 * N + 1 := by omega
        have h1R : (M : ℝ) ≤ 2 * (N : ℝ) + 1 := by exact_mod_cast h1
        linarith)
      hpMax_M (by norm_num)
      (by rw [Real.log_mul (by norm_num) (by positivity)]; linarith only [hlog_c, hLM_gt])
      (by norm_num)
      (by rw [Real.log_mul (by norm_num) (by positivity)]; linarith only [hlog_c, hLM_gt])
      (by norm_num) (by norm_num)
      (by rw [Real.log_mul (by norm_num) (by norm_num)]; linarith only [hlog_c, hL200_gt])
      (by
        have hlt : (4473 / 10000 : ℝ) * 200000 ≤ 200000 := by norm_num
        exact le_trans (Real.log_le_log (by norm_num) hlt) hL200_lt)
      (by rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
      (by rw [Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)
      (by norm_num)
      E.card hE_le (by norm_num) (by norm_num)

-- Case 3: n % 4 = 2 or n % 4 = 3
private lemma H2_case_mod4_23 {n M : ℕ} (hM999 : 999 ≤ M)
    (hM_lo : M ^ 2 < n) (hM_hi : n ≤ (M + 1) ^ 2) (hn4 : n % 4 = 2 ∨ n % 4 = 3) :
    OMA.S_oeis_a085265.IsTerm n := by
  have hn_pos : 0 < n := by nlinarith
  obtain ⟨hg_sq, hg2_dvd, hg_le, hg_iff⟩ := sq_part_props hn_pos hM_hi
  let g := ∏ p ∈ n.primeFactors.filter (fun p => p ^ 2 ∣ n), p
  have hg_odd : g % 2 = 1 := by
    by_contra heven
    have h2g : 2 ∣ g := by omega
    have h4n : 4 ∣ n := (hg_iff 2 Nat.prime_two).mp h2g
    omega
  have hN_le : ∀ j ∈ Finset.Icc 1 M, 0 ≤ 1 * j ∧ 1 ≤ 1 * j - 0 ∧ (1 * j - 0) ^ 2 < n := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    exact ⟨Nat.zero_le _, by omega, by simp only [one_mul, Nat.sub_zero]; nlinarith⟩
  have hno4 : ∀ j ∈ Finset.Icc 1 M, ¬ 4 ∣ n - (1 * j - 0) ^ 2 := by
    intro j hj hd
    have hlt := (hN_le j hj).2.2
    simp only [one_mul, Nat.sub_zero] at hd hlt
    have hj_sq : j ^ 2 % 4 = 0 ∨ j ^ 2 % 4 = 1 := by
      rcases Nat.even_or_odd j with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · left; have hsq : (t + t) ^ 2 = 4 * t ^ 2 := by ring
        rw [hsq]; omega
      · right; have hsq : (2 * t + 1) ^ 2 = 4 * (t ^ 2 + t) + 1 := by ring
        rw [hsq]; omega
    obtain ⟨r, hr⟩ := hd
    omega
  have hno_g : ∀ j ∈ Finset.Icc 1 M, (1 * j - 0).Coprime g →
      ∀ p : ℕ, p.Prime → p ∣ g → ¬ p ^ 2 ∣ n - (1 * j - 0) ^ 2 := by
    intro j hj hcop p hp hpg hd
    have hlt := (hN_le j hj).2.2
    have hp2n : p ^ 2 ∣ n := (hg_iff p hp).mp hpg
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p (by norm_num)) hp2n
    have hpk := (prime_sq_dvd_sub_sq_elim hp hlt hd hpn).2
    have hpd : p ∣ Nat.gcd (1 * j - 0) g := Nat.dvd_gcd hpk hpg
    rw [hcop] at hpd
    exact hp.not_dvd_one hpd
  have hcover : ¬ OMA.S_oeis_a085265.IsTerm n →
      ∀ j ∈ Finset.Icc 1 M, (1 * j - 0).Coprime g →
        j ∈ (∅ : Finset ℕ) ∨
        ∃ p ∈ (Finset.Icc 3 M).filter (fun p => p.Prime ∧ ¬ p ∣ g ∧ ¬ p ∣ n),
          p ^ 2 ∣ n - (1 * j - 0) ^ 2 := by
    intro hnot j hj hcop
    right
    have hlt := (hN_le j hj).2.2
    have hpos_sub : 1 ≤ n - (1 * j - 0) ^ 2 := by omega
    have hns : ¬ Squarefree (n - (1 * j - 0) ^ 2) := fun hsq =>
      hnot ⟨n - (1 * j - 0) ^ 2, 1 * j - 0, hpos_sub, hsq, (hN_le j hj).2.1, Nat.sub_add_cancel hlt.le⟩
    obtain ⟨p, hp, hp2⟩ := exists_sq_factor_of_not_squarefree hpos_sub hns
    have hp_ne2 : p ≠ 2 := by
      intro h2; subst h2; exact hno4 j hj (by simpa using hp2)
    have hp_ge3 : 3 ≤ p := by have := hp.two_le; omega
    have hpn : ¬ p ∣ n := by
      intro hpn
      have hp2n := (prime_sq_dvd_sub_sq_elim hp hlt hp2 hpn).1
      have hpg : p ∣ g := (hg_iff p hp).mpr hp2n
      exact hno_g j hj hcop p hp hpg hp2
    have hpg : ¬ p ∣ g := fun h => hno_g j hj hcop p hp h hp2
    have hp_le : p ≤ M := by
      have hle := Nat.le_of_dvd hpos_sub hp2
      have h1 : 1 ≤ (1 * j - 0) ^ 2 := by have := (hN_le j hj).2.1; nlinarith
      have hlt_n : p ^ 2 < n := by omega
      have hlt_sq : p ^ 2 < (M + 1) ^ 2 := lt_of_lt_of_le hlt_n hM_hi
      nlinarith
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_ge3, hp_le⟩, hp, hpg, hpn⟩, hp2⟩
  by_cases hM_lt : M < 200000
  · refine sieve_master_bound (Y1 := 7) (by norm_num) (by norm_num) hg_sq hg_odd (Or.inl rfl)
      (by norm_num) (by norm_num) hN_le hno4 hno_g ∅ hcover (81 / 1000)
      (sum_two_div_prime_sq_gt7 M) ?_
    simp only [Finset.card_empty]
    by_cases h1 : M ≤ 2143
    · exact small_regime_arith (e_ub := 0) hg_sq hg_odd (by omega) (primeCounting_le_Q11 M)
        (Nat.cast_pos.mpr (by omega))
        (small_interval_check (g_max := 2144) (N_lo := 999) (by omega) (by omega) (by linarith)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) (23 / 1000)
          (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_23_1)
        (by omega)
    · by_cases h2 : M ≤ 6000
      · exact small_regime_arith (e_ub := 0) hg_sq hg_odd (by omega) (primeCounting_le_Q13 M)
          (Nat.cast_pos.mpr (by omega))
          (small_interval_check (g_max := 6001) (N_lo := 2144) (by omega) (by omega) (by linarith)
            (by norm_num) (by norm_num) (by norm_num) (by norm_num) (16 / 1000)
            (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_23_2)
          (by omega)
      · by_cases h3 : M ≤ 30000
        · exact small_regime_arith (e_ub := 0) hg_sq hg_odd (by omega) (primeCounting_le_Q17 M)
            (Nat.cast_pos.mpr (by omega))
            (small_interval_check (g_max := 30001) (N_lo := 6001) (by omega) (by omega) (by linarith)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (10 / 1000)
              (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_23_3)
            (by omega)
        · exact small_regime_arith (e_ub := 0) hg_sq hg_odd (by omega) (primeCounting_le_Q23 M)
            (Nat.cast_pos.mpr (by omega))
            (small_interval_check (g_max := 200001) (N_lo := 30001) (by omega) (by omega) (by linarith)
              (by norm_num) (by norm_num) (by norm_num) (by norm_num) (5 / 1000)
              (sqrt_two_div_le_of_sq (by norm_num) (by norm_num) (by norm_num)) chk_23_4)
            (by omega)
  · push_neg at hM_lt
    let s := Nat.sqrt (Nat.sqrt M)
    have hs1 : 1 ≤ s := Nat.le_sqrt.mpr (Nat.le_sqrt.mpr (by omega))
    let Y1 := 2 * s + 1
    refine sieve_master_bound (Y1 := Y1) (by omega) (by omega) hg_sq hg_odd (Or.inl rfl)
      (by norm_num) (by norm_num) hN_le hno4 hno_g ∅ hcover (1 / ((Y1 : ℝ) + 1))
      (sum_two_div_odd_sq_le Y1 M (by omega) (by omega)) ?_
    simp only [Finset.card_empty]
    have hlog2_gt : (0.693147 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2_lt : Real.log 2 < (0.693148 : ℝ) := by linarith [Real.log_two_lt_d9]
    have hlog3_gt : (1.098612 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hlog3_lt : Real.log 3 < (1.098613 : ℝ) := by linarith [Real.log_three_lt_d9]
    have hLM_gt : (12.188 : ℝ) < Real.log (M : ℝ) := by
      have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (M : ℝ) := by
        have hM2 : (200000 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_lt
        have h196 : (3 : ℝ) * (2 : ℝ) ^ 16 < 200000 := by norm_num
        linarith
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hL200_gt : (12.188 : ℝ) < Real.log (200000 : ℝ) := by
      have h1 : (3 : ℝ) * (2 : ℝ) ^ 16 < (200000 : ℝ) := by norm_num
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
      push_cast at hlog; linarith
    have hL200_lt : Real.log (200000 : ℝ) ≤ 1226 / 100 := by
      have h1 : (200000 : ℝ) < (2 : ℝ) ^ 5 * (3 : ℝ) ^ 8 := by norm_num
      have hlog := Real.log_lt_log (by positivity) h1
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
      push_cast at hlog; linarith
    exact large_regime_arith (xCoeff := 1) (xAdd := 0) (eCoeff := 0)
      (alpha := 1) (lxLo := 12188 / 1000) (x0Sq := 447) (x0Qrt := 21) (mOverN := 1)
      hM_lt hg_sq hg_odd hg_le
      (by linarith) (by norm_num) (by norm_num) (by omega)
      (by
        have h1 : M ≤ 2 * M + 1 := by omega
        have h1R : (M : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast h1
        linarith)
      (by linarith) (by norm_num)
      (by simp) (by norm_num)
      (by rw [one_mul]; linarith) (by norm_num) (by norm_num)
      (by rw [one_mul]; linarith)
      (by rw [one_mul]; exact hL200_lt)
      (by rw [one_mul, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num) (by norm_num)
      (by rw [one_mul, Real.le_sqrt (by norm_num) (Real.sqrt_nonneg _), Real.le_sqrt (by norm_num) (by norm_num)]; norm_num)
      (by norm_num)
      0 (by simp) (by norm_num) (by norm_num)

private lemma H2_proof : OMA.R_oeis_a085265_R1.H2 := by
  intro n hn
  let M := Nat.sqrt (n - 1)
  have hM999 : 999 ≤ M := by
    dsimp [M]; exact Nat.le_sqrt.mpr (by omega)
  have hM_lo : M ^ 2 < n := by
    have h1 : M * M ≤ n - 1 := Nat.sqrt_le (n - 1)
    rw [sq]; omega
  have hM_hi : n ≤ (M + 1) ^ 2 := by
    have h1 : n - 1 < (M + 1) * (M + 1) := Nat.lt_succ_sqrt (n - 1)
    rw [sq]; omega
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h0 | h1 | h2 | h3
  · exact H2_case_mod4_0 hM999 hM_lo hM_hi (Nat.dvd_of_mod_eq_zero h0)
  · exact H2_case_mod4_1 hM999 hM_lo hM_hi h1
  · exact H2_case_mod4_23 hM999 hM_lo hM_hi (Or.inl h2)
  · exact H2_case_mod4_23 hM999 hM_lo hM_hi (Or.inr h3)

end A085265H2

theorem OMA.solution : OMA.R_oeis_a085265_R1.H2 := A085265H2.H2_proof

