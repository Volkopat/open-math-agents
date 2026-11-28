import OMAStatements.S_oeis_a166103
import Mathlib

namespace OMA.P_oeis_a166103

open OMA.S_oeis_a166103

/-- Weighted Jacobi character sum `D(k) = ∑_{i=0}^{k-1} J(i, k) * i`. -/
private def D (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, jacobiSym (i : ℤ) k * (i : ℤ)

/-- For any odd prime `p`, the Legendre sum `∑_{i=0}^{p-1} J(i, p) = 0`. -/
private lemma sum_jacobiSym_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∑ i ∈ Finset.range p, jacobiSym (i : ℤ) p = 0 := by
  have : Fact p.Prime := ⟨hp⟩
  -- Pick a quadratic nonresidue `a` mod `p` (`∃ a : ZMod p, ¬ IsSquare a`, since `p ≠ 2`)!
  have hnon : ∃ a : ℕ, a < p ∧ jacobiSym (a : ℤ) p = -1 := by
    obtain ⟨u, hu⟩ := FiniteField.exists_nonsquare (ZMod.ringChar_zmod_n p ▸ hp2)
    refine ⟨u.val, u.val_lt, ?_⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have hcast : ((u.val : ℤ) : ZMod p) = u := by simp
    have hns : ¬ IsSquare ((u.val : ℤ) : ZMod p) := by rwa [hcast]
    exact (legendreSym.eq_neg_one_iff p).mpr hns
  obtain ⟨a, ha_lt, ha_neg⟩ := hnon
  have hcop : Nat.Coprime a p := by
    refine (hp.coprime_iff_not_dvd.mpr fun hpa => ?_).symm
    have hz : jacobiSym (a : ℤ) p = 0 := by
      rw [jacobiSym.eq_zero_iff]
      refine ⟨hp.ne_zero, fun h1 => hp.not_dvd_one ?_⟩
      have hd : p ∣ (a : ℤ).gcd p := Nat.dvd_gcd (by simpa [Int.natAbs] using hpa) (dvd_refl p)
      rwa [h1] at hd
    omega
  have hbij : ∑ i ∈ Finset.range p, jacobiSym (i : ℤ) p =
      ∑ i ∈ Finset.range p, jacobiSym (((a * i) % p : ℕ) : ℤ) p := by
    refine (Finset.sum_bij (fun i _ => (a * i) % p) ?_ ?_ ?_ ?_).symm
    · intro i _; exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
    · intro i1 h1 i2 h2 heq
      have h1' := Finset.mem_range.mp h1
      have h2' := Finset.mem_range.mp h2
      have hmod : (a * i1 : ZMod p) = (a * i2 : ZMod p) := by
        have := congr_arg (fun x : ℕ => (x : ZMod p)) heq
        simpa [ZMod.natCast_mod] using this
      have ha_ne : (a : ZMod p) ≠ 0 := by
        intro h0
        have hd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
        have := Nat.dvd_gcd hd (dvd_refl p)
        rw [hcop.gcd_eq_one] at this
        exact hp.not_dvd_one this
      have hi : (i1 : ZMod p) = (i2 : ZMod p) := mul_left_cancel₀ ha_ne hmod
      have hval := congr_arg ZMod.val hi
      rwa [ZMod.val_natCast_of_lt h1', ZMod.val_natCast_of_lt h2'] at hval
    · intro r hr
      have hr' := Finset.mem_range.mp hr
      have ha_ne : (a : ZMod p) ≠ 0 := by
        intro h0
        have hd : p ∣ a := (ZMod.natCast_eq_zero_iff a p).mp h0
        have := Nat.dvd_gcd hd (dvd_refl p)
        rw [hcop.gcd_eq_one] at this
        exact hp.not_dvd_one this
      let x : ZMod p := (a : ZMod p)⁻¹ * (r : ZMod p)
      refine ⟨x.val, Finset.mem_range.mpr x.val_lt, ?_⟩
      have hmul : ((a * x.val : ℕ) : ZMod p) = (r : ZMod p) := by
        push_cast; simp [x, mul_inv_cancel_left₀ ha_ne]
      have hval := congr_arg ZMod.val hmul
      rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hr'] at hval
      exact hval
    · intro _ _; rfl
  have hneg : ∑ i ∈ Finset.range p, jacobiSym (((a * i) % p : ℕ) : ℤ) p =
      -(∑ i ∈ Finset.range p, jacobiSym (i : ℤ) p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hmod : (((a * i) % p : ℕ) : ℤ) = ((a * i : ℕ) : ℤ) % (p : ℤ) := by
      rw [Int.natCast_emod]
    rw [hmod, ← jacobiSym.mod_left, Nat.cast_mul, jacobiSym.mul_left, ha_neg]
    ring
  linarith

/-- For any odd `k` divisible by a prime `p` with `p ∤ (k / p)` (i.e., `k` is non-square / has an
odd-multiplicity prime factor), `∑_{i=0}^{k-1} J(i, k) = 0`. -/
private lemma sum_jacobiSym_eq_zero_of_not_sq (k : ℕ) (hk : Odd k) (hnsq : ¬ IsSquare k) :
    ∑ i ∈ Finset.range k, jacobiSym (i : ℤ) k = 0 := by
  have hk_pos : 0 < k := by obtain ⟨t, rfl⟩ := hk; omega
  -- Find a prime `p` with odd `padicValNat p k`!
  have hexp : ∃ p : ℕ, p.Prime ∧ Odd (k.factorization p) := by
    by_contra hall
    push Not at hall
    apply hnsq
    -- Every prime exponent is even, so `k` is a square!
    let m := ∏ p ∈ k.primeFactors, p ^ (k.factorization p / 2)
    refine ⟨m, ?_⟩
    have hfac := Nat.prod_factorization_pow_eq_self (Nat.ne_of_gt hk_pos)
    rw [← hfac]
    dsimp [m]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hpr : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hev : Even (k.factorization p) := Nat.not_odd_iff_even.mp (hall p hpr)
    rw [← pow_add]
    congr 1
    obtain ⟨t, ht⟩ := hev
    omega
  obtain ⟨p, hp, hodd_e⟩ := hexp
  have hp_dvd : p ∣ k := Nat.dvd_of_factorization_pos (by obtain ⟨t, ht⟩ := hodd_e; omega)
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨t, rfl⟩ := hk
    omega
  set e := k.factorization p
  set q := k / p ^ e
  have hpe_dvd : p ^ e ∣ k := Nat.ordProj_dvd k p
  have hk_eq : k = p ^ e * q := (Nat.mul_div_cancel' hpe_dvd).symm
  have hcop : Nat.Coprime (p ^ e) q := by
    have hnd : ¬ p ∣ q := Nat.not_dvd_ordCompl hp (Nat.ne_of_gt hk_pos)
    exact (hp.coprime_iff_not_dvd.mpr hnd).pow_left e
  have hpe_ne : p ^ e ≠ 0 := pow_ne_zero e hp.ne_zero
  have hq_ne : q ≠ 0 := by intro h; rw [h, mul_zero] at hk_eq; omega
  -- By CRT, `i ∈ range (p^e * q)` bijects with `(a, b) ∈ range (p^e) × range q`!
  have hsum_prod : ∑ i ∈ Finset.range k, jacobiSym (i : ℤ) k =
      (∑ a ∈ Finset.range (p ^ e), jacobiSym (a : ℤ) (p ^ e)) *
      (∑ b ∈ Finset.range q, jacobiSym (b : ℤ) q) := by
    rw [Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_bij (fun i _ => (i % (p ^ e), i % q)) ?_ ?_ ?_ ?_
    · intro i _
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero hpe_ne), Nat.mod_lt _ (Nat.pos_of_ne_zero hq_ne)⟩
    · intro i1 h1 i2 h2 heq
      have h1' := Finset.mem_range.mp h1
      have h2' := Finset.mem_range.mp h2
      have hpe_eq : i1 ≡ i2 [MOD p ^ e] := congr_arg Prod.fst heq
      have hq_eq : i1 ≡ i2 [MOD q] := congr_arg Prod.snd heq
      have hmul : i1 ≡ i2 [MOD p ^ e * q] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hpe_eq, hq_eq⟩
      rw [← hk_eq] at hmul
      change i1 % k = i2 % k at hmul
      rwa [Nat.mod_eq_of_lt h1', Nat.mod_eq_of_lt h2'] at hmul
    · rintro ⟨a, b⟩ hab
      simp only [Finset.mem_product, Finset.mem_range] at hab
      let r := Nat.chineseRemainder hcop a b
      refine ⟨r.val % k, Finset.mem_range.mpr (Nat.mod_lt _ hk_pos), ?_⟩
      ext
      · rw [hk_eq, Nat.mod_mod_of_dvd _ (dvd_mul_right _ _)]
        have h1 : r.val % p ^ e = a % p ^ e := r.property.1
        rw [h1, Nat.mod_eq_of_lt hab.1]
      · rw [hk_eq, Nat.mod_mod_of_dvd _ (dvd_mul_left _ _)]
        have h2 : r.val % q = b % q := r.property.2
        rw [h2, Nat.mod_eq_of_lt hab.2]
    · intro i _
      rw [hk_eq, jacobiSym.mul_right' _ hpe_ne hq_ne]
      have h1 : jacobiSym (i : ℤ) (p ^ e) = jacobiSym ((i % p ^ e : ℕ) : ℤ) (p ^ e) := by
        rw [jacobiSym.mod_left]; exact_mod_cast rfl
      have h2 : jacobiSym (i : ℤ) q = jacobiSym ((i % q : ℕ) : ℤ) q := by
        rw [jacobiSym.mod_left]; exact_mod_cast rfl
      rw [h1, h2]
  rw [hsum_prod]
  -- Now prove `∑ a ∈ range (p^e), J(a, p^e) = 0` since `e` is ODD!
  have hpe_zero : ∑ a ∈ Finset.range (p ^ e), jacobiSym (a : ℤ) (p ^ e) = 0 := by
    have hpow : ∀ a : ℕ, jacobiSym (a : ℤ) (p ^ e) = jacobiSym (a : ℤ) p := by
      intro a
      rw [jacobiSym.pow_right]
      rcases jacobiSym.trichotomy (a : ℤ) p with h0 | h1 | hm1
      · rw [h0, zero_pow (by obtain ⟨t, ht⟩ := hodd_e; omega)]
      · rw [h1, one_pow]
      · rw [hm1, Odd.neg_one_pow hodd_e]
    simp_rw [hpow]
    -- Split `range (p^e)` into `p^(e-1)` blocks of length `p`!
    have he1 : 1 ≤ e := by obtain ⟨t, ht⟩ := hodd_e; omega
    have hsplit : p ^ e = p ^ (e - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel he1]
    rw [hsplit]
    have hblock : ∀ r : ℕ, ∑ a ∈ Finset.range (r * p), jacobiSym (a : ℤ) p = 0 := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
        have hper : ∑ x ∈ Finset.range p, jacobiSym ((r * p + x : ℕ) : ℤ) p =
            ∑ x ∈ Finset.range p, jacobiSym (x : ℤ) p := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [jacobiSym.mod_left, jacobiSym.mod_left (x : ℤ) p]
          congr 1
          push_cast
          rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
        rw [hper, sum_jacobiSym_prime p hp hp2]
    exact hblock (p ^ (e - 1))
  rw [hpe_zero, zero_mul]

/-- Periodic block summation: if `∑_{b < k} J(b, k) = 0`, then
`∑_{i < k * t} J(i, k) * i = t * D(k)`. -/
private lemma sum_jacobiSym_mul_block (k t : ℕ) (_hk_pos : 0 < k)
    (hzero : ∑ b ∈ Finset.range k, jacobiSym (b : ℤ) k = 0) :
    ∑ i ∈ Finset.range (t * k), jacobiSym (i : ℤ) k * (i : ℤ) = (t : ℤ) * D k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    have hstep : ∑ b ∈ Finset.range k, jacobiSym ((t * k + b : ℕ) : ℤ) k * ((t * k + b : ℕ) : ℤ) =
        D k := by
      have hmod : ∀ b ∈ Finset.range k,
          jacobiSym ((t * k + b : ℕ) : ℤ) k = jacobiSym (b : ℤ) k := by
        intro b _
        rw [jacobiSym.mod_left, jacobiSym.mod_left (b : ℤ) k]
        congr 1; push_cast
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
      have hexp : ∑ b ∈ Finset.range k, jacobiSym ((t * k + b : ℕ) : ℤ) k * ((t * k + b : ℕ) : ℤ) =
          (t : ℤ) * (k : ℤ) * (∑ b ∈ Finset.range k, jacobiSym (b : ℤ) k) +
          ∑ b ∈ Finset.range k, jacobiSym (b : ℤ) k * (b : ℤ) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b hb => ?_)
        rw [hmod b hb]; push_cast; ring
      rw [hexp, hzero, mul_zero, zero_add]; rfl
    rw [hstep]; push_cast; ring

/-- Master prime-square step identity:
For any odd `k` which is not a square and any odd prime `p`,
`D(k * p^2) = p^2 * (1 - J(p, k)) * D(k)`. -/
private lemma D_mul_prime_sq (k p : ℕ) (hk : Odd k) (hnsq : ¬ IsSquare k) (hp : p.Prime) :
    D (k * p ^ 2) = (p : ℤ) ^ 2 * (1 - jacobiSym (p : ℤ) k) * D k := by
  have hk_pos : 0 < k := by obtain ⟨t, rfl⟩ := hk; omega
  have hzero := sum_jacobiSym_eq_zero_of_not_sq k hk hnsq
  have hp_ne : p ≠ 0 := hp.ne_zero
  have hJ : ∀ i : ℕ, jacobiSym (i : ℤ) (k * p ^ 2) =
      if p ∣ i then 0 else jacobiSym (i : ℤ) k := by
    intro i
    rw [jacobiSym.mul_right' _ (Nat.ne_of_gt hk_pos) (pow_ne_zero 2 hp_ne), jacobiSym.pow_right]
    by_cases hpi : p ∣ i
    · rw [if_pos hpi]
      have hz : jacobiSym (i : ℤ) p = 0 := by
        rw [jacobiSym.eq_zero_iff]
        refine ⟨hp_ne, ?_⟩
        intro h1
        have hpd : p ∣ (i : ℤ).gcd p := Nat.dvd_gcd (by simpa [Int.natAbs] using hpi) (dvd_refl p)
        rw [h1] at hpd
        exact hp.not_dvd_one hpd
      rw [hz]; simp
    · rw [if_neg hpi]
      have hcop : (i : ℤ).gcd p = 1 := by
        simpa [Int.gcd] using (hp.coprime_iff_not_dvd.mpr hpi).symm.gcd_eq_one
      rw [jacobiSym.sq_one hcop, mul_one]
  dsimp [D]
  simp_rw [hJ]
  have hsplit : ∑ i ∈ Finset.range (k * p ^ 2), (if p ∣ i then (0 : ℤ) else jacobiSym (i : ℤ) k) * (i : ℤ) =
      (∑ i ∈ Finset.range (k * p ^ 2), jacobiSym (i : ℤ) k * (i : ℤ)) -
      (∑ i ∈ (Finset.range (k * p ^ 2)).filter (fun i => p ∣ i), jacobiSym (i : ℤ) k * (i : ℤ)) := by
    have h1 : ∑ i ∈ Finset.range (k * p ^ 2), (if p ∣ i then (0 : ℤ) else jacobiSym (i : ℤ) k) * (i : ℤ) =
        ∑ i ∈ Finset.range (k * p ^ 2),
          (jacobiSym (i : ℤ) k * (i : ℤ) - if p ∣ i then jacobiSym (i : ℤ) k * (i : ℤ) else 0) :=
      Finset.sum_congr rfl (fun i _ => by split_ifs <;> ring)
    rw [h1, Finset.sum_sub_distrib, ← Finset.sum_filter]
  rw [hsplit]
  have hsum1 : ∑ i ∈ Finset.range (k * p ^ 2), jacobiSym (i : ℤ) k * (i : ℤ) =
      (p : ℤ) ^ 2 * D k := by
    rw [mul_comm k (p ^ 2)]
    have h := sum_jacobiSym_mul_block k (p ^ 2) hk_pos hzero
    push_cast at h
    exact h
  have hsum2 : ∑ i ∈ (Finset.range (k * p ^ 2)).filter (fun i => p ∣ i), jacobiSym (i : ℤ) k * (i : ℤ) =
      (p : ℤ) ^ 2 * jacobiSym (p : ℤ) k * D k := by
    have hbij : ∑ i ∈ (Finset.range (k * p ^ 2)).filter (fun i => p ∣ i), jacobiSym (i : ℤ) k * (i : ℤ) =
        ∑ j ∈ Finset.range (p * k), jacobiSym ((p * j : ℕ) : ℤ) k * ((p * j : ℕ) : ℤ) := by
      refine Finset.sum_bij (fun i _ => i / p) ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        obtain ⟨j, rfl⟩ := hi.2
        rw [Nat.mul_div_cancel_left j hp.pos]
        have : p * j < p * (p * k) := by nlinarith
        exact Nat.lt_of_mul_lt_mul_left this
      · intro i1 h1 i2 h2 heq
        simp only [Finset.mem_filter] at h1 h2
        obtain ⟨j1, rfl⟩ := h1.2
        obtain ⟨j2, rfl⟩ := h2.2
        rw [Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos] at heq
        rw [heq]
      · intro j hj
        simp only [Finset.mem_range] at hj
        refine ⟨p * j, ?_, Nat.mul_div_cancel_left j hp.pos⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by nlinarith, dvd_mul_right p j⟩
      · intro i hi
        simp only [Finset.mem_filter] at hi
        rw [Nat.mul_div_cancel' hi.2]
    rw [hbij]
    have hfac : ∑ j ∈ Finset.range (p * k), jacobiSym ((p * j : ℕ) : ℤ) k * ((p * j : ℕ) : ℤ) =
        (p : ℤ) * jacobiSym (p : ℤ) k * ∑ j ∈ Finset.range (p * k), jacobiSym (j : ℤ) k * (j : ℤ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Nat.cast_mul, jacobiSym.mul_left]; ring
    rw [hfac, sum_jacobiSym_mul_block k p hk_pos hzero]
    ring
  rw [hsum1, hsum2]; dsimp [D]; ring

/-- For any prime `p ≥ 7` with `p ≡ 3 (mod 4)` (in fact any prime `p ≥ 5`), `p ∣ D(p)`. -/
private lemma prime_dvd_D_prime (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) :
    (p : ℤ) ∣ D p := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  dsimp [D]
  push_cast
  -- In `ZMod p`, `J(i, p) = i^((p-1)/2)` by Euler's criterion (`legendreSym.eq_pow`)!
  have hterm : ∀ i ∈ Finset.range p,
      ((jacobiSym (i : ℤ) p : ℤ) : ZMod p) * (i : ZMod p) = (i : ZMod p) ^ ((p + 1) / 2) := by
    intro i _
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_pow]
    have hcast : ((i : ℤ) : ZMod p) = (i : ZMod p) := by simp
    rw [hcast, ← pow_succ]
    congr 1
    have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
    obtain ⟨t, rfl⟩ := hp_odd
    omega
  rw [Finset.sum_congr rfl hterm]
  -- `∑_{x : ZMod p} x^e = 0` for `1 ≤ e < p - 1`!
  have hsum_zmod : ∑ i ∈ Finset.range p, (i : ZMod p) ^ ((p + 1) / 2) =
      ∑ x : ZMod p, x ^ ((p + 1) / 2) := by
    refine Finset.sum_bij (fun i _ => (i : ZMod p)) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro i1 h1 i2 h2 heq
      have h1' := Finset.mem_range.mp h1
      have h2' := Finset.mem_range.mp h2
      have hv := congr_arg ZMod.val heq
      rwa [ZMod.val_natCast_of_lt h1', ZMod.val_natCast_of_lt h2'] at hv
    · intro x _; exact ⟨x.val, Finset.mem_range.mpr x.val_lt, ZMod.natCast_zmod_val x⟩
    · intro _ _; rfl
  rw [hsum_zmod]
  -- Pick a generator `g : (ZMod p)ˣ` with `orderOf g = p - 1`, so `g^e ≠ 1`!
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  set e := (p + 1) / 2
  have he_pos : 1 ≤ e := by omega
  have he_lt : e < p - 1 := by omega
  have hge_ne : (g : ZMod p) ^ e ≠ 1 := by
    intro h1
    have hu : g ^ e = 1 := Units.ext (by simpa using h1)
    have hdvd : orderOf g ∣ e := orderOf_dvd_of_pow_eq_one hu
    rw [hord] at hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hshift : (g : ZMod p) ^ e * ∑ x : ZMod p, x ^ e = ∑ x : ZMod p, x ^ e := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun x _ => (g : ZMod p) * x) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro x1 _ x2 _ heq; exact Units.mul_right_inj g |>.mp heq
    · intro y _
      refine ⟨(g⁻¹ : (ZMod p)ˣ) * y, Finset.mem_univ _, ?_⟩
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    · intro x _; rw [mul_pow]
  have hzero : ((g : ZMod p) ^ e - 1) * ∑ x : ZMod p, x ^ e = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hge_ne)

/-- For any composite odd squarefree `d`, `d ∣ D(d)`. -/
private lemma sqfree_composite_dvd_D (d : ℕ) (hd_odd : Odd d) (hd_sf : Squarefree d)
    (hd_comp : ∃ p q : ℕ, p.Prime ∧ 1 < q ∧ d = p * q) :
    (d : ℤ) ∣ D d := by
  have hd_pos : 0 < d := by obtain ⟨t, rfl⟩ := hd_odd; omega
  -- Since `d` is squarefree, it suffices to show `p ∣ D(d)` for every prime `p ∣ d`!
  have hall_p : ∀ p : ℕ, p.Prime → p ∣ d → (p : ℤ) ∣ D d := by
    intro p hp hpd
    set q := d / p
    have hd_eq : d = p * q := (Nat.mul_div_cancel' hpd).symm
    have hq_odd : Odd q := by
      have : Odd (p * q) := hd_eq ▸ hd_odd
      exact (Nat.odd_mul.mp this).2
    have hndvd : ¬ p ∣ q := by
      intro hpq
      have hsq : p * p ∣ d := by rw [hd_eq]; exact mul_dvd_mul_left p hpq
      exact hp.not_isUnit (hd_sf p hsq)
    have hq_gt1 : 1 < q := by
      rcases hd_comp with ⟨p0, q0, hp0, hq0, hd0⟩
      by_contra hq1
      have hq_eq1 : q = 1 := by
        have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hd_eq; omega
        rcases Nat.lt_trichotomy q 1 with h0 | h1 | hgt
        · exact absurd (Nat.lt_one_iff.mp h0) hq0
        · exact h1
        · exact absurd hgt hq1
      rw [hq_eq1, mul_one] at hd_eq
      rw [hd_eq] at hd0
      have h1 : p0 ∣ p := ⟨q0, hd0⟩
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact hp0.ne_one h
      · subst h; nlinarith [hp0.two_le]
    have hq_sf : Squarefree q := (hd_eq ▸ hd_sf).of_mul_right
    have hq_nsq : ¬ IsSquare q := by
      rintro ⟨r, hr⟩
      have hr1 : r ≠ 1 := by intro h; rw [h, mul_one] at hr; omega
      have hru : IsUnit r := hq_sf r (hr ▸ dvd_refl q)
      exact hr1 (Nat.isUnit_iff.mp hru)
    have hq_zero := sum_jacobiSym_eq_zero_of_not_sq q hq_odd hq_nsq
    have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hndvd
    -- Work in `ZMod p` using `i = x * p + y` (`x < q, y < p`)!
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [D]
    push_cast
    have hsplit : ∑ i ∈ Finset.range (p * q), ((jacobiSym (i : ℤ) (p * q) : ℤ) : ZMod p) * (i : ZMod p) =
        ∑ y ∈ Finset.range p,
          ((jacobiSym (y : ℤ) p : ℤ) : ZMod p) * (y : ZMod p) *
            ∑ x ∈ Finset.range q, ((jacobiSym ((x * p + y : ℕ) : ℤ) q : ℤ) : ZMod p) := by
      -- Biject `range (p * q)` with `range q × range p` via `i ↦ (i / p, i % p)`!
      have hbij : ∑ i ∈ Finset.range (p * q), ((jacobiSym (i : ℤ) (p * q) : ℤ) : ZMod p) * (i : ZMod p) =
          ∑ x ∈ Finset.range q, ∑ y ∈ Finset.range p,
            ((jacobiSym ((x * p + y : ℕ) : ℤ) (p * q) : ℤ) : ZMod p) * ((x * p + y : ℕ) : ZMod p) := by
        rw [← Finset.sum_product']
        refine Finset.sum_bij (fun i _ => (i / p, i % p)) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_product, Finset.mem_range] at hi ⊢
          exact ⟨Nat.div_lt_of_lt_mul (by linarith), Nat.mod_lt _ hp.pos⟩
        · intro i1 _ i2 _ heq
          have h1 := congr_arg Prod.fst heq
          have h2 := congr_arg Prod.snd heq
          have := Nat.div_add_mod i1 p
          have := Nat.div_add_mod i2 p
          nlinarith
        · rintro ⟨x, y⟩ hxy
          simp only [Finset.mem_product, Finset.mem_range] at hxy
          refine ⟨x * p + y, Finset.mem_range.mpr (by nlinarith), ?_⟩
          ext
          · rw [mul_comm, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hxy.2, add_zero]
          · rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hxy.2]
        · intro i _
          have hdiv : i / p * p + i % p = i := by rw [mul_comm]; exact Nat.div_add_mod i p
          rw [hdiv]
      rw [hbij, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [jacobiSym.mul_right' _ hp.ne_zero (by omega)]
      have hmodp : jacobiSym ((x * p + y : ℕ) : ℤ) p = jacobiSym (y : ℤ) p := by
        rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ) p]
        congr 1; push_cast
        rw [Int.add_emod, Int.mul_emod_left, zero_add, Int.emod_emod]
      rw [hmodp]
      have hcast : ((x * p + y : ℕ) : ZMod p) = (y : ZMod p) := by
        push_cast; simp
      rw [hcast]; push_cast; ring
    rw [hd_eq, hsplit]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    have hinner : ∑ x ∈ Finset.range q, jacobiSym ((x * p + y : ℕ) : ℤ) q = 0 := by
      have hbij : ∑ x ∈ Finset.range q, jacobiSym ((x * p + y : ℕ) : ℤ) q =
          ∑ r ∈ Finset.range q, jacobiSym (r : ℤ) q := by
        refine Finset.sum_bij (fun x _ => (x * p + y) % q) ?_ ?_ ?_ ?_
        · intro x _; exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))
        · intro x1 h1 x2 h2 heq
          have h1' := Finset.mem_range.mp h1
          have h2' := Finset.mem_range.mp h2
          have hz : ((x1 * p + y : ℕ) : ZMod q) = ((x2 * p + y : ℕ) : ZMod q) := by
            have := congr_arg (fun z : ℕ => (z : ZMod q)) heq
            simpa [ZMod.natCast_mod] using this
          push_cast at hz
          have hmul : (x1 : ZMod q) * (p : ZMod q) = (x2 : ZMod q) * (p : ZMod q) :=
            add_right_cancel hz
          have hp_unit : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hcop
          have hx : (x1 : ZMod q) = (x2 : ZMod q) := hp_unit.mul_right_cancel hmul
          have hv := congr_arg ZMod.val hx
          rwa [ZMod.val_natCast_of_lt h1', ZMod.val_natCast_of_lt h2'] at hv
        · intro r hr
          have hr' := Finset.mem_range.mp hr
          have : NeZero q := ⟨by omega⟩
          obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime p q).mpr hcop
          let x : ZMod q := ((r : ZMod q) - (y : ZMod q)) * (u⁻¹ : (ZMod q)ˣ)
          refine ⟨x.val, Finset.mem_range.mpr x.val_lt, ?_⟩
          have hz : ((x.val * p + y : ℕ) : ZMod q) = (r : ZMod q) := by
            push_cast
            rw [ZMod.natCast_zmod_val, ← hu]
            simp [x, mul_assoc]
          have hv := congr_arg ZMod.val hz
          rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hr'] at hv
          exact hv
        · intro x _
          rw [jacobiSym.mod_left]; exact_mod_cast rfl
      rw [hbij, hq_zero]
    have hinner_zmod : ∑ x ∈ Finset.range q, ((jacobiSym ((x * p + y : ℕ) : ℤ) q : ℤ) : ZMod p) = 0 := by
      have := congr_arg (fun z : ℤ => (z : ZMod p)) hinner
      simpa using this
    rw [hinner_zmod, mul_zero]
  -- Combine `p ∣ D d` over all primes `p ∈ d.primeFactors` since `d` is squarefree!
  have hd_prod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hd_sf
  conv_lhs => rw [← hd_prod, Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime ?_ (fun p hp => hall_p p (Nat.prime_of_mem_primeFactors hp)
    (Nat.dvd_of_mem_primeFactors hp))
  intro p1 h1 p2 h2 hne
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa [Int.gcd] using
      ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors h1)
        (Nat.prime_of_mem_primeFactors h2)).mpr hne).gcd_eq_one)

/-- Relating `a166100 ((k - 1) / 2)` divisibility by `k` to `k ∣ D(k)` for odd `k ≡ 3 (mod 4)`. -/
private lemma dvd_a166100_iff_dvd_D (k : ℕ) (hk : Odd k) (hk3 : k % 4 = 3) :
    k ∣ a166100 ((k - 1) / 2) ↔ (k : ℤ) ∣ D k := by
  have hk_eq : 2 * ((k - 1) / 2) + 1 = k := by obtain ⟨t, rfl⟩ := hk; omega
  have hk_ge3 : 3 ≤ k := by omega
  dsimp [a166100]
  rw [hk_eq]
  set P : ℕ := ∑ i ∈ (Finset.Icc 1 k).filter (fun (i : ℕ) => jacobiSym (i : ℤ) k = 1), i
  set M : ℕ := ∑ i ∈ (Finset.Icc 1 k).filter (fun (i : ℕ) => jacobiSym (i : ℤ) k = -1), i
  -- `J(k, k) = 0` and `J(0, k) = 0` since `k ≥ 3`.
  have hJk : jacobiSym (k : ℤ) k = 0 := by
    rw [jacobiSym.eq_zero_iff]; refine ⟨by omega, ?_⟩; simp; omega
  have hJ0 : jacobiSym (0 : ℤ) k = 0 := jacobiSym.zero_left (by omega)
  -- `D k = P - M`!
  have hD_eq : D k = (P : ℤ) - (M : ℤ) := by
    dsimp [D, P, M]
    have hsplit_range : ∑ i ∈ Finset.range k, jacobiSym (i : ℤ) k * (i : ℤ) =
        ∑ i ∈ Finset.Icc 1 k, jacobiSym (i : ℤ) k * (i : ℤ) := by
      have h1 : Finset.range k = insert 0 (Finset.Ico 1 k) := by
        ext i; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      have h2 : Finset.Icc 1 k = insert k (Finset.Ico 1 k) := by
        ext i; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [h1, h2, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
      simp only [Nat.cast_zero, hJ0, hJk, zero_mul, zero_add]
    rw [hsplit_range, Nat.cast_sum, Nat.cast_sum]
    have hrew : ∀ i ∈ Finset.Icc 1 k,
        jacobiSym (i : ℤ) k * (i : ℤ) =
          (if jacobiSym (i : ℤ) k = 1 then (i : ℤ) else 0) -
          (if jacobiSym (i : ℤ) k = -1 then (i : ℤ) else 0) := by
      intro i _
      rcases jacobiSym.trichotomy (i : ℤ) k with h0 | h1 | hm1
      · rw [h0]; simp
      · rw [h1]; simp
      · rw [hm1]; simp
    rw [Finset.sum_congr rfl hrew, Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  -- `P + M` is divisible by `k` (via pairing `i ↔ k - i` on units mod `k` and `2 ∣ φ(k)`)!
  have hk_dvd_PM : k ∣ P + M := by
    have hPM : P + M = ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), i := by
      dsimp [P, M]
      have hdisj : Disjoint ((Finset.Icc 1 k).filter (fun (i : ℕ) => jacobiSym (i : ℤ) k = 1))
          ((Finset.Icc 1 k).filter (fun (i : ℕ) => jacobiSym (i : ℤ) k = -1)) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        simp only [Finset.mem_filter] at h1 h2; omega
      rw [← Finset.sum_union hdisj]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
      constructor
      · rintro (⟨⟨hi1, hik⟩, hJ⟩ | ⟨⟨hi1, hik⟩, hJ⟩)
        · have hne : i ≠ k := by rintro rfl; rw [hJk] at hJ; omega
          have hcop : Nat.Coprime i k := by
            by_contra hnc
            have hz : jacobiSym (i : ℤ) k = 0 := by
              rw [jacobiSym.eq_zero_iff]
              exact ⟨by omega, by simpa [Int.gcd] using hnc⟩
            omega
          exact ⟨⟨hi1, by omega⟩, hcop⟩
        · have hne : i ≠ k := by rintro rfl; rw [hJk] at hJ; omega
          have hcop : Nat.Coprime i k := by
            by_contra hnc
            have hz : jacobiSym (i : ℤ) k = 0 := by
              rw [jacobiSym.eq_zero_iff]
              exact ⟨by omega, by simpa [Int.gcd] using hnc⟩
            omega
          exact ⟨⟨hi1, by omega⟩, hcop⟩
      · rintro ⟨⟨hi1, hik⟩, hcop⟩
        have hg : (i : ℤ).gcd k = 1 := by simpa [Int.gcd] using hcop.gcd_eq_one
        rcases jacobiSym.eq_one_or_neg_one hg with h1 | hm1
        · exact Or.inl ⟨⟨hi1, by omega⟩, h1⟩
        · exact Or.inr ⟨⟨hi1, by omega⟩, hm1⟩
    rw [hPM]
    have hpair : 2 * ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), i =
        k * ((Finset.Ico 1 k).filter (fun i => Nat.Coprime i k)).card := by
      have hrev : ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), i =
          ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), (k - i) := by
        refine Finset.sum_bij (fun i _ => k - i) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          exact (Nat.coprime_self_sub_left (le_of_lt hi.1.2)).mpr hi.2
        · intro i1 h1 i2 h2 heq
          simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2; omega
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_Ico] at hj
          refine ⟨k - j, ?_, by omega⟩
          simp only [Finset.mem_filter, Finset.mem_Ico]
          exact ⟨⟨by omega, by omega⟩, (Nat.coprime_self_sub_left (le_of_lt hj.1.2)).mpr hj.2⟩
        · intro i hi; simp only [Finset.mem_filter, Finset.mem_Ico] at hi; omega
      have h2 : 2 * ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), i =
          ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), (i + (k - i)) := by
        rw [two_mul, Finset.sum_add_distrib]
        congr 1
      rw [h2]
      have hk_sum : ∑ i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), (i + (k - i)) =
          ∑ _i ∈ (Finset.Ico 1 k).filter (fun i => Nat.Coprime i k), k :=
        Finset.sum_congr rfl (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_Ico] at hi; omega)
      rw [hk_sum, Finset.sum_const, smul_eq_mul, mul_comm]
    have hcard_phi : ((Finset.Ico 1 k).filter (fun i => Nat.Coprime i k)).card = Nat.totient k := by
      rw [Nat.totient_eq_card_coprime]
      congr 1; ext i
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
      constructor
      · rintro ⟨⟨_, hik⟩, hcop⟩; exact ⟨hik, hcop.symm⟩
      · rintro ⟨hik, hcop⟩
        have hi0 : i ≠ 0 := by rintro rfl; simp at hcop; omega
        exact ⟨⟨by omega, hik⟩, hcop.symm⟩
    rw [hcard_phi] at hpair
    obtain ⟨t, ht⟩ := Nat.totient_even (by omega : 2 < k)
    rw [ht] at hpair
    refine ⟨t, ?_⟩
    linarith
  -- Now `2 * P = (P + M) + D(k)` and `gcd(2, k) = 1`!
  have h2P : 2 * (P : ℤ) = ((P + M : ℕ) : ℤ) + D k := by rw [hD_eq]; push_cast; ring
  have hk_dvd_PM_Z : (k : ℤ) ∣ ((P + M : ℕ) : ℤ) := Int.ofNat_dvd.mpr hk_dvd_PM
  have hcop2 : IsCoprime (k : ℤ) 2 := Int.isCoprime_iff_gcd_eq_one.mpr (by
    simpa [Int.gcd] using (Nat.coprime_two_right.mpr hk).gcd_eq_one)
  constructor
  · intro hkP
    have hkP_Z : (k : ℤ) ∣ (P : ℤ) := Int.ofNat_dvd.mpr hkP
    have h2 : (k : ℤ) ∣ 2 * (P : ℤ) := dvd_mul_of_dvd_right hkP_Z 2
    rw [h2P] at h2
    exact (dvd_add_right hk_dvd_PM_Z).mp h2
  · intro hkD
    have h2 : (k : ℤ) ∣ 2 * (P : ℤ) := by rw [h2P]; exact dvd_add hk_dvd_PM_Z hkD
    have hkP_Z : (k : ℤ) ∣ (P : ℤ) := hcop2.dvd_of_dvd_mul_left h2
    exact Int.ofNat_dvd.mp hkP_Z

/-- For odd `k ≡ 1 (mod 4)`, `k ∣ a166100 ((k - 1) / 2)` always holds by `i ↔ k - i` pairing! -/
private lemma dvd_a166100_of_mod4_eq_one (k : ℕ) (hk : Odd k) (hk1 : k % 4 = 1) :
    k ∣ a166100 ((k - 1) / 2) := by
  by_cases h1 : k = 1
  · subst h1; simp
  have hk_eq : 2 * ((k - 1) / 2) + 1 = k := by obtain ⟨t, rfl⟩ := hk; omega
  have hk_ge5 : 5 ≤ k := by omega
  dsimp [a166100]
  rw [hk_eq]
  have hJk : jacobiSym (k : ℤ) k = 0 := by
    rw [jacobiSym.eq_zero_iff]; refine ⟨by omega, ?_⟩; simp; omega
  set S := (Finset.Icc 1 k).filter (fun (i : ℕ) => jacobiSym (i : ℤ) k = 1)
  have hneg1 : jacobiSym (-1 : ℤ) k = 1 := by
    rw [jacobiSym.at_neg_one hk]
    simp [ZMod.χ₄_nat_one_mod_four hk1]
  have hinv : ∀ i ∈ S, k - i ∈ S := by
    intro i hi
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hi ⊢
    have hne : i ≠ k := by rintro rfl; rw [hJk] at hi; omega
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have hmod : ((k - i : ℕ) : ℤ) % (k : ℤ) = (- (i : ℤ)) % (k : ℤ) := by
      have : ((k - i : ℕ) : ℤ) = (k : ℤ) - (i : ℤ) := by omega
      rw [this, show (k : ℤ) - (i : ℤ) = -(i : ℤ) + (k : ℤ) by ring, Int.add_emod_right]
    rw [jacobiSym.mod_left' hmod, show -(i : ℤ) = (-1 : ℤ) * (i : ℤ) by ring,
      jacobiSym.mul_left, hneg1, one_mul, hi.2]
  have hrev : ∑ i ∈ S, i = ∑ i ∈ S, (k - i) := by
    refine Finset.sum_bij (fun i _ => k - i) ?_ ?_ ?_ ?_
    · exact hinv
    · intro i1 h1 i2 h2 heq
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
    · intro j hj
      refine ⟨k - j, hinv j hj, ?_⟩
      simp only [S, Finset.mem_filter, Finset.mem_Icc] at hj; omega
    · intro i hi; simp only [S, Finset.mem_filter, Finset.mem_Icc] at hi; omega
  have h2sum : 2 * ∑ i ∈ S, i = k * S.card := by
    calc 2 * ∑ i ∈ S, i = ∑ i ∈ S, i + ∑ i ∈ S, (k - i) := by rw [two_mul, ← hrev]
      _ = ∑ i ∈ S, (i + (k - i)) := (Finset.sum_add_distrib).symm
      _ = ∑ _i ∈ S, k := Finset.sum_congr rfl (fun i hi => by
            simp only [S, Finset.mem_filter, Finset.mem_Icc] at hi; omega)
      _ = k * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hdvd2 : k ∣ 2 * ∑ i ∈ S, i := ⟨S.card, h2sum⟩
  exact (Nat.coprime_two_right.mpr hk).dvd_of_dvd_mul_left hdvd2

/-- Helper: `m^2 ∣ D (d * m^2)` for any odd squarefree `d ≥ 3` and odd `m ≥ 1`, and characterization
for `d = 3`. -/
private lemma D_three_mul_sq (m : ℕ) (hm_odd : Odd m) :
    ∃ R : ℤ, D (3 * m ^ 2) = (m : ℤ) ^ 2 * R ∧
      (3 ∣ R ↔ ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p % 6 = 1) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · subst hm1
      refine ⟨-1, ?_, ?_⟩
      · simp only [D, one_pow, mul_one, Finset.sum_range_succ, Finset.range_zero,
          Finset.sum_empty, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
        have h0 : jacobiSym 0 3 = 0 := jacobiSym.zero_left (by omega)
        have h1 : jacobiSym 1 3 = 1 := jacobiSym.one_left 3
        have h2 : jacobiSym 2 3 = -1 := by rw [jacobiSym.at_two (by decide : Odd 3)]; decide
        rw [h0, h1, h2]; norm_num
      · constructor
        · intro h; omega
        · rintro ⟨p, hp, hpd, _⟩; exact absurd hpd hp.not_dvd_one
    · have hm_gt1 : 1 < m := by obtain ⟨t, rfl⟩ := hm_odd; omega
      obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      set m' := m / p
      have hm_eq : m = m' * p := (Nat.mul_div_cancel' hpm).symm.trans (mul_comm p m')
      have hm'_odd : Odd m' := by
        have : Odd (m' * p) := hm_eq ▸ hm_odd
        exact (Nat.odd_mul.mp this).1
      have hp_odd : Odd p := by
        have : Odd (m' * p) := hm_eq ▸ hm_odd
        exact (Nat.odd_mul.mp this).2
      have hm'_lt : m' < m := by
        have : 0 < m' := by obtain ⟨t, ht⟩ := hm'_odd; omega
        nlinarith [hp.two_le]
      obtain ⟨R', hD', hR'⟩ := ih m' hm'_lt hm'_odd
      have hnsq : ¬ IsSquare (3 * m' ^ 2) := by
        rintro ⟨r, hr⟩
        have h3 : (3 * m' ^ 2).factorization 3 = 2 * r.factorization 3 := by
          have hm'_ne : m' ≠ 0 := by obtain ⟨t, ht⟩ := hm'_odd; omega
          have hr_ne : r ≠ 0 := by
            rintro rfl
            simp only [mul_zero] at hr
            exact mul_ne_zero (by omega) (pow_ne_zero 2 hm'_ne) hr
          rw [hr, ← sq, Nat.factorization_pow]
          rfl
        have h3' : (3 * m' ^ 2).factorization 3 = 1 + 2 * m'.factorization 3 := by
          have hm'_ne : m' ≠ 0 := by obtain ⟨t, ht⟩ := hm'_odd; omega
          rw [Nat.factorization_mul (by omega) (pow_ne_zero 2 hm'_ne), Finsupp.add_apply,
            Nat.Prime.factorization_self Nat.prime_three, Nat.factorization_pow]
          simp
        omega
      have hodd3 : Odd (3 * m' ^ 2) := by
        exact Odd.mul (by decide) (Odd.pow hm'_odd)
      have hstep := D_mul_prime_sq (3 * m' ^ 2) p hodd3 hnsq hp
      have heq_arg : 3 * m ^ 2 = (3 * m' ^ 2) * p ^ 2 := by rw [hm_eq]; ring
      rw [← heq_arg, hD'] at hstep
      refine ⟨(1 - jacobiSym (p : ℤ) (3 * m' ^ 2)) * R', ?_, ?_⟩
      · rw [hstep, hm_eq]; push_cast; ring
      · have h3p : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr Nat.prime_three
        rw [h3p.dvd_mul, hR']
        have hJ_iff : (3 : ℤ) ∣ 1 - jacobiSym (p : ℤ) (3 * m' ^ 2) ↔ ¬ p ∣ m' ∧ p % 6 = 1 := by
          have hJ_eq1 : (3 : ℤ) ∣ 1 - jacobiSym (p : ℤ) (3 * m' ^ 2) ↔
              jacobiSym (p : ℤ) (3 * m' ^ 2) = 1 := by
            rcases jacobiSym.trichotomy (p : ℤ) (3 * m' ^ 2) with h | h | h <;> rw [h] <;> decide
          rw [hJ_eq1]
          have hm'_ne : m' ≠ 0 := by obtain ⟨t, ht⟩ := hm'_odd; omega
          rw [jacobiSym.mul_right' _ (by omega : (3 : ℕ) ≠ 0) (pow_ne_zero 2 hm'_ne),
            jacobiSym.pow_right]
          by_cases hpm' : p ∣ m'
          · have hz : jacobiSym (p : ℤ) m' = 0 := by
              rw [jacobiSym.eq_zero_iff]; refine ⟨hm'_ne, ?_⟩
              intro h1
              have hpd : p ∣ (p : ℤ).gcd m' := Nat.dvd_gcd (by simp) hpm'
              rw [h1] at hpd; exact hp.not_dvd_one hpd
            rw [hz]; simp [hpm']
          · have hcop : (p : ℤ).gcd m' = 1 := by
              simpa [Int.gcd] using (hp.coprime_iff_not_dvd.mpr hpm').gcd_eq_one
            rw [jacobiSym.sq_one hcop, mul_one]
            simp only [hpm', not_false_eq_true, true_and]
            -- Evaluate `J(p, 3)` by `p % 3`: since `p` is odd, `p % 6 = 1 ↔ p % 3 = 1`!
            have hp_mod3 : jacobiSym (p : ℤ) 3 = jacobiSym ((p % 3 : ℕ) : ℤ) 3 := by
              rw [jacobiSym.mod_left]; exact_mod_cast rfl
            rw [hp_mod3]
            have hlt3 : p % 3 < 3 := Nat.mod_lt p (by omega)
            have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
            interval_cases h : p % 3
            · constructor
              · intro hJ
                have h0 : jacobiSym (0 : ℤ) 3 = 0 := jacobiSym.zero_left (by omega)
                rw [Nat.cast_zero, h0] at hJ; omega
              · intro; omega
            · constructor
              · intro _; omega
              · intro _; rw [Nat.cast_one, jacobiSym.one_left]
            · constructor
              · intro hJ
                have h2 : jacobiSym (2 : ℤ) 3 = -1 := by
                  rw [jacobiSym.at_two (by decide : Odd 3)]; decide
                rw [Nat.cast_ofNat, h2] at hJ; omega
              · intro; omega
        rw [hJ_iff]
        constructor
        · rintro (⟨_, hp6⟩ | ⟨q, hq, hqm', hq6⟩)
          · exact ⟨p, hp, hpm, hp6⟩
          · exact ⟨q, hq, dvd_trans hqm' (hm_eq ▸ dvd_mul_right m' p), hq6⟩
        · rintro ⟨q, hq, hqm, hq6⟩
          rw [hm_eq] at hqm
          rcases hq.dvd_mul.mp hqm with hqm' | hqp
          · exact Or.inr ⟨q, hq, hqm', hq6⟩
          · have hqp_eq : q = p := ((Nat.dvd_prime hp).mp hqp).resolve_left hq.ne_one
            rw [hqp_eq] at hq6
            by_cases hpm' : p ∣ m'
            · exact Or.inr ⟨p, hp, hpm', hq6⟩
            · exact Or.inl ⟨hpm', hq6⟩

/-- Squarefree-times-square decomposition of any positive integer `k`. -/
private lemma exists_sqfree_mul_sq (k : ℕ) (hk : 0 < k) :
    ∃ d m : ℕ, Squarefree d ∧ 1 ≤ m ∧ k = d * m ^ 2 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hsf : Squarefree k
    · exact ⟨k, 1, hsf, le_rfl, by ring⟩
    · rw [Squarefree] at hsf
      push Not at hsf
      obtain ⟨r, hr_dvd, hr_nu⟩ := hsf
      have hr_gt1 : 1 < r := by
        have hr_ne0 : r ≠ 0 := by rintro rfl; simp at hr_dvd; omega
        have hr_ne1 : r ≠ 1 := fun h => hr_nu (h ▸ isUnit_one)
        omega
      obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (by omega : r ≠ 1)
      have hp2_dvd : p ^ 2 ∣ k := dvd_trans (by rw [sq]; exact mul_dvd_mul hpr hpr) hr_dvd
      obtain ⟨k', hk'⟩ := hp2_dvd
      have hk'_pos : 0 < k' := by
        rcases eq_or_ne k' 0 with rfl | hne
        · simp at hk'; omega
        · omega
      have hk'_lt : k' < k := by
        have h4 : 4 ≤ p ^ 2 := by nlinarith [hp.two_le]
        rw [hk']; nlinarith
      obtain ⟨d, m', hdsf, hm'1, hdk'⟩ := ih k' hk'_lt hk'_pos
      refine ⟨d, m' * p, hdsf, by nlinarith [hp.two_le], ?_⟩
      rw [hk', hdk']; ring

/-- For any odd squarefree `d ≡ 3 (mod 4)` with `d > 3`, `d * m^2 ∣ D (d * m^2)` for all odd `m`. -/
private lemma dvd_D_of_sqfree_gt_three (d : ℕ) (hd_odd : Odd d) (hd_sf : Squarefree d)
    (hd_gt3 : 3 < d) :
    ∀ m : ℕ, Odd m → ((d * m ^ 2 : ℕ) : ℤ) ∣ D (d * m ^ 2) := by
  have hd_dvd : (d : ℤ) ∣ D d := by
    by_cases hp : d.Prime
    · exact prime_dvd_D_prime d hp (by obtain ⟨t, rfl⟩ := hd_odd; omega)
    · obtain ⟨p, hpr, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      refine sqfree_composite_dvd_D d hd_odd hd_sf ⟨p, d / p, hpr, ?_, (Nat.mul_div_cancel' hpd).symm⟩
      have hne : d / p ≠ 1 := by
        intro h1
        have := Nat.mul_div_cancel' hpd
        rw [h1, mul_one] at this
        exact hp (this ▸ hpr)
      have hpos : 0 < d / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpd) hpr.pos
      omega
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm_odd
    by_cases hm1 : m = 1
    · subst hm1; simpa using hd_dvd
    · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
      set m' := m / p
      have hm_eq : m = m' * p := (Nat.mul_div_cancel' hpm).symm.trans (mul_comm p m')
      have hm'_odd : Odd m' := (Nat.odd_mul.mp (hm_eq ▸ hm_odd)).1
      have hm'_lt : m' < m := by
        have : 0 < m' := by obtain ⟨t, ht⟩ := hm'_odd; omega
        nlinarith [hp.two_le]
      have hih := ih m' hm'_lt hm'_odd
      have hnsq : ¬ IsSquare (d * m' ^ 2) := by
        rintro ⟨r, hr⟩
        -- Since `d > 3` is squarefree, pick a prime `q ∣ d`; its valuation in `d * m'^2` is odd!
        obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hm'_ne : m' ≠ 0 := by obtain ⟨t, ht⟩ := hm'_odd; omega
        have hr_ne : r ≠ 0 := by
          rintro rfl
          simp only [mul_zero] at hr
          exact mul_ne_zero (by omega) (pow_ne_zero 2 hm'_ne) hr
        have hv1 : (d * m' ^ 2).factorization q = 2 * r.factorization q := by
          rw [hr, ← sq, Nat.factorization_pow]; rfl
        have hqd_val : d.factorization q = 1 := by
          have hpos : 0 < d.factorization q := Nat.Prime.factorization_pos_of_dvd hq (by omega) hqd
          have hle : d.factorization q ≤ 1 := by
            by_contra hgt
            have h2 : q ^ 2 ∣ d := dvd_trans (pow_dvd_pow q (by omega : 2 ≤ d.factorization q))
              (Nat.ordProj_dvd d q)
            exact hq.not_isUnit (hd_sf q (by simpa [sq] using h2))
          omega
        have hv2 : (d * m' ^ 2).factorization q = 1 + 2 * m'.factorization q := by
          rw [Nat.factorization_mul (by omega) (pow_ne_zero 2 hm'_ne), Finsupp.add_apply,
            hqd_val, Nat.factorization_pow]
          simp
        omega
      have hstep := D_mul_prime_sq (d * m' ^ 2) p (Odd.mul hd_odd (Odd.pow hm'_odd)) hnsq hp
      have heq_arg : d * m ^ 2 = (d * m' ^ 2) * p ^ 2 := by rw [hm_eq]; ring
      rw [heq_arg, hstep]
      push_cast
      obtain ⟨c, hc⟩ := hih
      rw [hc]
      refine ⟨(1 - jacobiSym (p : ℤ) (d * m' ^ 2)) * c, ?_⟩
      push_cast; ring

lemma prove_a166102 :
    ∀ k : ℕ, Odd k →
      (¬ k ∣ a166100 ((k - 1) / 2) ↔ ∃ m : ℕ, IsA166104 m ∧ k = 3 * m ^ 2) := by
  intro k hk
  have hk_pos : 0 < k := by obtain ⟨t, rfl⟩ := hk; omega
  have hmod4 : k % 4 = 1 ∨ k % 4 = 3 := by obtain ⟨t, rfl⟩ := hk; omega
  rcases hmod4 with hk1 | hk3
  · constructor
    · intro hndvd
      exact absurd (dvd_a166100_of_mod4_eq_one k hk hk1) hndvd
    · rintro ⟨m, hm, rfl⟩
      have hm_odd : Odd m := by
        have hm2 : Odd (m ^ 2) := (Nat.odd_mul.mp hk).2
        rw [sq] at hm2; exact (Nat.odd_mul.mp hm2).1
      obtain ⟨t, rfl⟩ := hm_odd
      have hsq : 3 * (2 * t + 1) ^ 2 = 4 * (3 * t ^ 2 + 3 * t) + 3 := by ring
      omega
  · rw [dvd_a166100_iff_dvd_D k hk hk3]
    obtain ⟨d, m, hd_sf, hm1, rfl⟩ := exists_sqfree_mul_sq k hk_pos
    have hd_odd : Odd d := (Nat.odd_mul.mp hk).1
    have hm_odd : Odd m := by
      have hm2 : Odd (m ^ 2) := (Nat.odd_mul.mp hk).2
      rw [sq] at hm2; exact (Nat.odd_mul.mp hm2).1
    have hd3 : d % 4 = 3 := by
      obtain ⟨a, rfl⟩ := hm_odd
      have hsq : d * (2 * a + 1) ^ 2 = 4 * (d * (a ^ 2 + a)) + d := by ring
      omega
    by_cases hd_eq3 : d = 3
    · subst hd_eq3
      obtain ⟨R, hD, hR⟩ := D_three_mul_sq m hm_odd
      have hdvd_iff : ((3 * m ^ 2 : ℕ) : ℤ) ∣ D (3 * m ^ 2) ↔ (3 : ℤ) ∣ R := by
        rw [hD]; push_cast
        have hm2_ne : (m : ℤ) ^ 2 ≠ 0 := by positivity
        constructor
        · rintro ⟨c, hc⟩
          refine ⟨c, ?_⟩
          have h1 : (m : ℤ) ^ 2 * R = (m : ℤ) ^ 2 * (3 * c) := by linarith
          exact mul_left_cancel₀ hm2_ne h1
        · rintro ⟨c, rfl⟩
          exact ⟨c, by ring⟩
      rw [hdvd_iff, hR]
      constructor
      · intro hno
        refine ⟨m, ⟨hm1, fun p hp hpm => ?_⟩, rfl⟩
        have hp_odd : Odd p := hm_odd.of_dvd_nat hpm
        have hp6_ne1 : p % 6 ≠ 1 := fun h1 => hno ⟨p, hp, hpm, h1⟩
        have hlt6 : p % 6 < 6 := Nat.mod_lt p (by omega)
        have h2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
        omega
      · rintro ⟨m0, hm0, heq⟩
        have hm_eq : m = m0 := by
          have hsq : m ^ 2 = m0 ^ 2 := by omega
          nlinarith [hm1, hm0.1]
        subst hm_eq
        rintro ⟨p, hp, hpm, hp6⟩
        rcases hm0.2 p hp hpm with h3 | h5 <;> omega
    · have hd_gt3 : 3 < d := by omega
      have hdvd := dvd_D_of_sqfree_gt_three d hd_odd hd_sf hd_gt3 m hm_odd
      constructor
      · intro hndvd; exact absurd hdvd hndvd
      · rintro ⟨m0, hm0, heq⟩
        -- `d * m^2 = 3 * m0^2` with `d` squarefree forces `d = 3`!
        exfalso
        apply hd_eq3
        -- For every prime `q`, `v_q(d) = (v_q(d * m^2)) % 2 = (v_q(3 * m0^2)) % 2 = v_q(3)`!
        have hd_pos : 0 < d := by omega
        have hm0_ne : m0 ≠ 0 := by have := hm0.1; omega
        have hm_ne : m ≠ 0 := by omega
        have hfac_eq : ∀ q : ℕ, d.factorization q = (3 : ℕ).factorization q := by
          intro q
          by_cases hq : q.Prime
          · have h1 := congr_arg (fun x : ℕ => x.factorization q) heq
            rw [Nat.factorization_mul (by omega) (pow_ne_zero 2 hm_ne),
              Nat.factorization_mul (by omega) (pow_ne_zero 2 hm0_ne),
              Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_pow, Nat.factorization_pow] at h1
            simp only [Finsupp.smul_apply, smul_eq_mul] at h1
            have hd_le1 : d.factorization q ≤ 1 := by
              by_contra hgt
              have h2 : q ^ 2 ∣ d := dvd_trans (pow_dvd_pow q (by omega : 2 ≤ d.factorization q))
                (Nat.ordProj_dvd d q)
              exact hq.not_isUnit (hd_sf q (by simpa [sq] using h2))
            have h3_le1 : (3 : ℕ).factorization q ≤ 1 := by
              by_cases hq3 : q = 3
              · subst hq3; rw [Nat.Prime.factorization_self Nat.prime_three]
              · rw [Nat.factorization_eq_zero_of_not_dvd]; omega
                intro h; exact hq3 (((Nat.dvd_prime Nat.prime_three).mp h).resolve_left hq.ne_one)
            omega
          · rw [Nat.factorization_eq_zero_of_not_prime d hq,
              Nat.factorization_eq_zero_of_not_prime 3 hq]
        have hfeq : d.factorization = (3 : ℕ).factorization := Finsupp.ext hfac_eq
        exact Nat.eq_of_factorization_eq (by omega) (by omega) (fun q => hfac_eq q)

lemma prove_a166103 :
    (∀ k : ℕ, IsA166102 k → 3 ∣ k) ∧
    (∀ x : ℕ, IsA166103 x ↔ IsA166102 (3 * x)) := by
  constructor
  · intro k ⟨hk_odd, hndvd⟩
    obtain ⟨m, _, rfl⟩ := (prove_a166102 k hk_odd).mp hndvd
    exact dvd_mul_right 3 (m ^ 2)
  · intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm_odd : Odd m := by
        rw [Nat.odd_iff]
        by_contra h
        have h2m : 2 ∣ m := by omega
        rcases hm.2 2 Nat.prime_two h2m with h3 | h5 <;> omega
      have h3m2_odd : Odd (3 * m ^ 2) := Odd.mul (by decide) (Odd.pow hm_odd)
      exact ⟨h3m2_odd, (prove_a166102 (3 * m ^ 2) h3m2_odd).mpr ⟨m, hm, rfl⟩⟩
    · rintro ⟨h3x_odd, hndvd⟩
      obtain ⟨m, hm, heq⟩ := (prove_a166102 (3 * x) h3x_odd).mp hndvd
      exact ⟨m, hm, by omega⟩

end OMA.P_oeis_a166103

theorem OMA.solution : type_of% @OMA.S_oeis_a166103.main :=
  OMA.P_oeis_a166103.prove_a166103
