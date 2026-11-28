import OMAStatements.S_oeis_a217772
import Mathlib

namespace OMA.S_oeis_a217772

private lemma ratio_eq_choose (p : ℕ) (hp : 1 ≤ p) :
    (p + 1) * Nat.factorial (3 * p) /
      (Nat.factorial (2 * p - 1) * Nat.factorial (p + 1) * (2 * p)) =
    Nat.choose (3 * p) p := by
  have hden : Nat.factorial (2 * p - 1) * Nat.factorial (p + 1) * (2 * p) =
      (p + 1) * (Nat.factorial p * Nat.factorial (2 * p)) := by
    have h1 : Nat.factorial (2 * p) = (2 * p) * Nat.factorial (2 * p - 1) := by
      conv_lhs => rw [show 2 * p = (2 * p - 1) + 1 by omega, Nat.factorial_succ]
      rw [show 2 * p - 1 + 1 = 2 * p by omega]
    have h2 : Nat.factorial (p + 1) = (p + 1) * Nat.factorial p := Nat.factorial_succ p
    rw [h1, h2]; ring
  rw [hden, Nat.mul_div_mul_left _ _ (Nat.succ_pos p)]
  have hch := Nat.choose_mul_factorial_mul_factorial (show p ≤ 3 * p by omega)
  rw [show 3 * p - p = 2 * p by omega] at hch
  rw [← hch, mul_assoc, Nat.mul_div_cancel _ (by positivity)]

private lemma choose_three_mul_eq (p : ℕ) (hp : 1 ≤ p) :
    Nat.choose (3 * p) p = 3 * Nat.choose (3 * p - 1) (p - 1) := by
  have h := Nat.add_one_mul_choose_eq (3 * p - 1) (p - 1)
  have h1 : 3 * p - 1 + 1 = 3 * p := by omega
  have h2 : p - 1 + 1 = p := by omega
  rw [h1, h2] at h
  have h3 : p * Nat.choose (3 * p) p = p * (3 * Nat.choose (3 * p - 1) (p - 1)) := by linarith
  exact Nat.eq_of_mul_eq_mul_left (by omega) h3

private lemma sum_sq_mod_p {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2) = 0 := by
  have hsum_nat : 6 * ∑ k ∈ Finset.range p, k ^ 2 = (p - 1) * p * (2 * p - 1) := by
    have h : ∀ n : ℕ, 6 * ∑ k ∈ Finset.range (n + 1), k ^ 2 = n * (n + 1) * (2 * n + 1) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        ring
    have := h (p - 1)
    rw [show p - 1 + 1 = p by omega, show 2 * (p - 1) + 1 = 2 * p - 1 by omega] at this
    exact this
  have hIco : ∑ k ∈ Finset.Ico 1 p, k ^ 2 = ∑ k ∈ Finset.range p, k ^ 2 := by
    have h0 : Finset.range p = insert 0 (Finset.Ico 1 p) := by
      ext k; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    rw [h0, Finset.sum_insert (by simp)]
    simp
  have h6p : (6 : ZMod p) * (∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2) = 0 := by
    have hcast : ((6 * ∑ k ∈ Finset.Ico 1 p, k ^ 2 : ℕ) : ZMod p) =
        (((p - 1) * p * (2 * p - 1) : ℕ) : ZMod p) := by
      rw [hIco, hsum_nat]
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat, ZMod.natCast_self,
      mul_zero, zero_mul] at hcast
    exact hcast
  let _ : Fact p.Prime := ⟨hp⟩
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro h6
    have hdvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp h6
    have hle : p ≤ 6 := Nat.le_of_dvd (by decide) hdvd
    have h56 : p = 5 ∨ p = 6 := by omega
    rcases h56 with rfl | rfl
    · exact absurd hdvd (by decide)
    · exact absurd hp (by decide)
  exact (mul_eq_zero.mp h6p).resolve_left h6ne

private lemma sum_inv_sq_mod_p {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    (∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2) = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  -- Bijection k ↦ k⁻¹ on (ZMod p)ˣ / Finset.Ico 1 p!
  have hbij : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 =
      ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 := by
    refine Finset.sum_bij (fun k _ => ((k : ZMod p)⁻¹).val) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      have hkne : (k : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff k p).mp h0
        have := Nat.le_of_dvd (by omega) this
        omega
      have hinv_ne : (k : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hkne
      have hpos : 0 < ((k : ZMod p)⁻¹).val := by
        by_contra h0
        have hv : ((k : ZMod p)⁻¹).val = 0 := by omega
        exact hinv_ne (by rw [← ZMod.natCast_zmod_val ((k : ZMod p)⁻¹), hv, Nat.cast_zero])
      exact ⟨hpos, ZMod.val_lt _⟩
    · intro k1 hk1 k2 hk2 hval
      simp only [Finset.mem_Ico] at hk1 hk2
      have hinv : (k1 : ZMod p)⁻¹ = (k2 : ZMod p)⁻¹ := by
        rw [← ZMod.natCast_zmod_val ((k1 : ZMod p)⁻¹), ← ZMod.natCast_zmod_val ((k2 : ZMod p)⁻¹),
          hval]
      have heq : (k1 : ZMod p) = (k2 : ZMod p) := inv_injective hinv
      have h1 : (k1 : ZMod p).val = k1 := ZMod.val_natCast_of_lt hk1.2
      have h2 : (k2 : ZMod p).val = k2 := ZMod.val_natCast_of_lt hk2.2
      rw [← h1, ← h2, heq]
    · intro j hj
      simp only [Finset.mem_Ico] at hj
      have hjne : (j : ZMod p) ≠ 0 := by
        intro h0
        have := (ZMod.natCast_eq_zero_iff j p).mp h0
        have := Nat.le_of_dvd (by omega) this
        omega
      have hinv_ne : (j : ZMod p)⁻¹ ≠ 0 := inv_ne_zero hjne
      have hpos : 0 < ((j : ZMod p)⁻¹).val := by
        by_contra h0
        have hv : ((j : ZMod p)⁻¹).val = 0 := by omega
        exact hinv_ne (by rw [← ZMod.natCast_zmod_val ((j : ZMod p)⁻¹), hv, Nat.cast_zero])
      refine ⟨((j : ZMod p)⁻¹).val, Finset.mem_Ico.mpr ⟨hpos, ZMod.val_lt _⟩, ?_⟩
      rw [ZMod.natCast_zmod_val, inv_inv, ZMod.val_natCast_of_lt hj.2]
    · intro k _
      rw [ZMod.natCast_zmod_val]
  rw [hbij]
  exact sum_sq_mod_p hp hp5

private lemma wolstenholme_choose {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) :
    p ^ 3 ∣ (Nat.choose (3 * p - 1) (p - 1) - 1) := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  -- Work in ZMod (p^3): ∏_{k=1}^{p-1} (2*p + k) = ∏_{k=1}^{p-1} k!
  -- First show (∏_{k=1}^{p-1} (2*p + k) : ZMod (p^3)) = (∏_{k=1}^{p-1} k : ZMod (p^3))
  have hunit : ∀ k ∈ Finset.Ico 1 p, IsUnit (k : ZMod (p ^ 3)) := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hcop : Nat.Coprime k (p ^ 3) :=
      ((hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega)).symm).pow_right 3
    exact (ZMod.isUnit_iff_coprime k (p ^ 3)).mpr hcop
  -- Choose inverse inv3 k in ZMod (p^3) for each k ∈ Ico 1 p
  let inv3 : ℕ → ZMod (p ^ 3) := fun k =>
    if h : k ∈ Finset.Ico 1 p then ((hunit k h).unit⁻¹ : (ZMod (p ^ 3))ˣ) else 0
  have hinv3_mul : ∀ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) * inv3 k = 1 := by
    intro k hk
    simp only [inv3, dif_pos hk]
    exact (hunit k hk).mul_val_inv
  -- Compute ∏_{k=1}^{p-1} (1 + 2*p * inv3 k) in ZMod (p^3)
  have hprod_expand :
      ∏ k ∈ Finset.Ico 1 p, (1 + (2 * p : ZMod (p ^ 3)) * inv3 k) =
      1 + (2 * p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Ico 1 p, inv3 k) +
      (2 * p : ZMod (p ^ 3)) ^ 2 *
        (∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) := by
    rw [Finset.prod_one_add]
    have hzero_ge3 : ∀ S ∈ (Finset.Ico 1 p).powerset, 3 ≤ S.card →
        ∏ k ∈ S, ((2 * p : ZMod (p ^ 3)) * inv3 k) = 0 := by
      intro S _ hcard
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hp3 : (2 * p : ZMod (p ^ 3)) ^ S.card = 0 := by
        rw [mul_pow, show S.card = 3 + (S.card - 3) by omega, pow_add (p : ZMod (p ^ 3))]
        have : (p : ZMod (p ^ 3)) ^ 3 = 0 := by
          rw [← Nat.cast_pow, ZMod.natCast_self]
        rw [this, zero_mul, mul_zero]
      rw [hp3, zero_mul]
    have hpow_split : (Finset.Ico 1 p).powerset =
        (Finset.Ico 1 p).powersetCard 0 ∪ (Finset.Ico 1 p).powersetCard 1 ∪
        (Finset.Ico 1 p).powersetCard 2 ∪
        ((Finset.Ico 1 p).powerset.filter (fun S => 3 ≤ S.card)) := by
      ext S
      simp only [Finset.mem_union, Finset.mem_powerset, Finset.mem_powersetCard, Finset.mem_filter]
      by_cases hsub : S ⊆ Finset.Ico 1 p
      · simp only [hsub, true_and, true_iff]; omega
      · simp [hsub]
    rw [hpow_split, Finset.sum_union, Finset.sum_union, Finset.sum_union]
    · have h0 : ∑ S ∈ (Finset.Ico 1 p).powersetCard 0,
          ∏ k ∈ S, ((2 * p : ZMod (p ^ 3)) * inv3 k) = 1 := by
        simp [Finset.powersetCard_zero]
      have h1 : ∑ S ∈ (Finset.Ico 1 p).powersetCard 1,
          ∏ k ∈ S, ((2 * p : ZMod (p ^ 3)) * inv3 k) =
          (2 * p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k := by
        rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
        simp
      have h2 : ∑ S ∈ (Finset.Ico 1 p).powersetCard 2,
          ∏ k ∈ S, ((2 * p : ZMod (p ^ 3)) * inv3 k) =
          (2 * p : ZMod (p ^ 3)) ^ 2 *
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hS).2]
      have h3 : ∑ S ∈ (Finset.Ico 1 p).powerset.filter (fun S => 3 ≤ S.card),
          ∏ k ∈ S, ((2 * p : ZMod (p ^ 3)) * inv3 k) = 0 := by
        refine Finset.sum_eq_zero fun S hS => ?_
        simp only [Finset.mem_filter] at hS
        exact hzero_ge3 S hS.1 hS.2
      rw [h0, h1, h2, h3, add_zero]
    · exact Finset.disjoint_left.mpr fun S hS1 hS2 => by
        simp only [Finset.mem_powersetCard] at hS1 hS2; omega
    · rw [Finset.disjoint_union_left]
      exact ⟨Finset.disjoint_left.mpr fun S hS1 hS2 => by
          simp only [Finset.mem_powersetCard] at hS1 hS2; omega,
        Finset.disjoint_left.mpr fun S hS1 hS2 => by
          simp only [Finset.mem_powersetCard] at hS1 hS2; omega⟩
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
      exact ⟨⟨Finset.disjoint_left.mpr fun S hS1 hS2 => by
          simp only [Finset.mem_powersetCard, Finset.mem_filter] at hS1 hS2; omega,
        Finset.disjoint_left.mpr fun S hS1 hS2 => by
          simp only [Finset.mem_powersetCard, Finset.mem_filter] at hS1 hS2; omega⟩,
        Finset.disjoint_left.mpr fun S hS1 hS2 => by
          simp only [Finset.mem_powersetCard, Finset.mem_filter] at hS1 hS2; omega⟩
  -- Step 1: p^2 divides ∑ inv3 k (i.e. (p : ZMod (p^3)) * ∑ inv3 k = 0)
  have hH1 : (p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Ico 1 p, inv3 k) = 0 := by
    have hpair : 2 * ∑ k ∈ Finset.Ico 1 p, inv3 k =
        (p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k) := by
      have hsym : ∑ k ∈ Finset.Ico 1 p, inv3 k = ∑ k ∈ Finset.Ico 1 p, inv3 (p - k) := by
        refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Ico] at hk1 hk2; omega
        · intro k hk; simp only [Finset.mem_Ico] at hk
          exact ⟨p - k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro k hk; simp only [Finset.mem_Ico] at hk
          rw [show p - (p - k) = k by omega]
      calc 2 * ∑ k ∈ Finset.Ico 1 p, inv3 k
          = ∑ k ∈ Finset.Ico 1 p, inv3 k + ∑ k ∈ Finset.Ico 1 p, inv3 (p - k) := by
              rw [← hsym]; ring
        _ = ∑ k ∈ Finset.Ico 1 p, (inv3 k + inv3 (p - k)) := (Finset.sum_add_distrib).symm
        _ = (p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k hk => ?_
              have hpk : p - k ∈ Finset.Ico 1 p := by
                simp only [Finset.mem_Ico] at hk ⊢; omega
              have hsum_k : (k : ZMod (p ^ 3)) + ((p - k : ℕ) : ZMod (p ^ 3)) = (p : ZMod (p ^ 3)) := by
                rw [← Nat.cast_add, show k + (p - k) = p by
                  simp only [Finset.mem_Ico] at hk; omega]
              calc inv3 k + inv3 (p - k)
                  = inv3 k * (((p - k : ℕ) : ZMod (p ^ 3)) * inv3 (p - k)) +
                    ((k : ZMod (p ^ 3)) * inv3 k) * inv3 (p - k) := by
                      rw [hinv3_mul _ hpk, hinv3_mul _ hk, mul_one, one_mul]
                _ = ((k : ZMod (p ^ 3)) + ((p - k : ℕ) : ZMod (p ^ 3))) *
                      (inv3 k * inv3 (p - k)) := by ring
                _ = (p : ZMod (p ^ 3)) * (inv3 k * inv3 (p - k)) := by rw [hsum_k]
    -- Show (p : ZMod (p^3)) ^ 2 * ∑ inv3 k * inv3 (p - k) = 0 using ZMod p!
    have hcast_p : ZMod.castHom (dvd_pow_self p (by omega : 3 ≠ 0)) (ZMod p)
        (∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k)) = 0 := by
      let π := ZMod.castHom (dvd_pow_self p (by omega : 3 ≠ 0)) (ZMod p)
      let _ : Fact p.Prime := ⟨hp⟩
      have hπ_inv : ∀ k ∈ Finset.Ico 1 p, π (inv3 k) = (k : ZMod p)⁻¹ := by
        intro k hk
        have h1 := congr_arg π (hinv3_mul k hk)
        simp only [map_mul, map_natCast, map_one] at h1
        have hkne : (k : ZMod p) ≠ 0 := by
          simp only [Finset.mem_Ico] at hk
          intro h0; have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0); omega
        exact mul_left_cancel₀ hkne (by rw [h1, mul_inv_cancel₀ hkne])
      rw [map_sum]
      have hterm : ∑ k ∈ Finset.Ico 1 p, π (inv3 k * inv3 (p - k)) =
          -(∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hpk : p - k ∈ Finset.Ico 1 p := by
          simp only [Finset.mem_Ico] at hk ⊢; omega
        rw [map_mul, hπ_inv k hk, hπ_inv (p - k) hpk]
        have hneg : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
          have : ((p - k : ℕ) : ZMod p) + (k : ZMod p) = 0 := by
            rw [← Nat.cast_add, show p - k + k = p by
              simp only [Finset.mem_Ico] at hk; omega, ZMod.natCast_self]
          exact eq_neg_of_add_eq_zero_left this
        rw [hneg, inv_neg]; ring
      rw [hterm, sum_inv_sq_mod_p hp hp5, neg_zero]
    have hp2_mul : (p : ZMod (p ^ 3)) ^ 2 * ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k) = 0 := by
      set S := ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k)
      have hS_dvd : p ∣ S.val := by
        have h1 : (S.val : ZMod p) = 0 := by
          have := hcast_p
          rwa [← ZMod.natCast_zmod_val S, map_natCast] at this
        exact (ZMod.natCast_eq_zero_iff S.val p).mp h1
      obtain ⟨q, hq⟩ := hS_dvd
      rw [← ZMod.natCast_zmod_val S, hq, Nat.cast_mul, ← mul_assoc, ← pow_succ]
      rw [← Nat.cast_pow, ZMod.natCast_self, zero_mul]
    have h2u : IsUnit (2 : ZMod (p ^ 3)) := by
      have hcop : Nat.Coprime 2 (p ^ 3) :=
        ((hp.coprime_iff_not_dvd.mpr (fun hd => by
          have := Nat.le_of_dvd (by omega) hd; omega)).symm).pow_right 3
      exact (ZMod.isUnit_iff_coprime 2 (p ^ 3)).mpr hcop
    have h2mul : (2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k) = 0 := by
      calc (2 : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k)
          = (p : ZMod (p ^ 3)) * (2 * ∑ k ∈ Finset.Ico 1 p, inv3 k) := by ring
        _ = (p : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k)) := by
              rw [hpair]
        _ = (p : ZMod (p ^ 3)) ^ 2 * ∑ k ∈ Finset.Ico 1 p, inv3 k * inv3 (p - k) := by ring
        _ = 0 := hp2_mul
    exact h2u.mul_left_cancel (by rw [h2mul, mul_zero])
  -- Step 2: p divides e_2(inv3) (i.e. p^2 * e_2 = 0 in ZMod (p^3))
  have hH2 : (p : ZMod (p ^ 3)) ^ 2 *
      (∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) = 0 := by
    let π := ZMod.castHom (dvd_pow_self p (by omega : 3 ≠ 0)) (ZMod p)
    let _ : Fact p.Prime := ⟨hp⟩
    have hπ_inv : ∀ k ∈ Finset.Ico 1 p, π (inv3 k) = (k : ZMod p)⁻¹ := by
      intro k hk
      have h1 := congr_arg π (hinv3_mul k hk)
      simp only [map_mul, map_natCast, map_one] at h1
      have hkne : (k : ZMod p) ≠ 0 := by
        simp only [Finset.mem_Ico] at hk
        intro h0; have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0); omega
      exact mul_left_cancel₀ hkne (by rw [h1, mul_inv_cancel₀ hkne])
    have hsum1_p : ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ = 0 := by
      have hsym : ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ =
          ∑ k ∈ Finset.Ico 1 p, ((p - k : ℕ) : ZMod p)⁻¹ := by
        refine Finset.sum_bij (fun k _ => p - k) ?_ ?_ ?_ ?_
        · intro k hk; simp only [Finset.mem_Ico] at hk ⊢; omega
        · intro k1 hk1 k2 hk2 h; simp only [Finset.mem_Ico] at hk1 hk2; omega
        · intro k hk; simp only [Finset.mem_Ico] at hk
          exact ⟨p - k, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro k hk; simp only [Finset.mem_Ico] at hk
          rw [show p - (p - k) = k by omega]
      have hneg : ∑ k ∈ Finset.Ico 1 p, ((p - k : ℕ) : ZMod p)⁻¹ =
          -(∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun k hk => ?_
        have h1 : ((p - k : ℕ) : ZMod p) = -(k : ZMod p) := by
          have : ((p - k : ℕ) : ZMod p) + (k : ZMod p) = 0 := by
            rw [← Nat.cast_add, show p - k + k = p by
              simp only [Finset.mem_Ico] at hk; omega, ZMod.natCast_self]
          exact eq_neg_of_add_eq_zero_left this
        rw [h1, inv_neg]
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h2; have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff 2 p).mp h2); omega
      have h2sum : (2 : ZMod p) * ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ = 0 := by
        have h0 : ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ +
            ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ = 0 := by
          nth_rw 2 [hsym]
          rw [hneg]
          exact add_neg_cancel _
        calc (2 : ZMod p) * ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹
            = ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ + ∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹ := by ring
          _ = 0 := h0
      exact (mul_eq_zero.mp h2sum).resolve_left h2ne
    -- 2 * e_2(f) = (∑ f)^2 - ∑ f^2 in ZMod p!
    have he2_p : π (∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) = 0 := by
      have h2e2 : (2 : ZMod p) * π (∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) =
          (∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹) ^ 2 -
          ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 := by
        have hsq : (∑ k ∈ Finset.Ico 1 p, (k : ZMod p)⁻¹) ^ 2 =
            ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 +
            ∑ ij ∈ (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 ≠ ij.2),
              (ij.1 : ZMod p)⁻¹ * (ij.2 : ZMod p)⁻¹ := by
          rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_product']
          have hsplit : Finset.Ico 1 p ×ˢ Finset.Ico 1 p =
              (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 = ij.2) ∪
              (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 ≠ ij.2) := by
            ext ij; by_cases h : ij ∈ Finset.Ico 1 p ×ˢ Finset.Ico 1 p <;> simp [h]; tauto
          conv_lhs => rw [hsplit]
          rw [Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
          congr 1
          refine Finset.sum_bij (fun ij _ => ij.1) ?_ ?_ ?_ ?_
          · intro ij hij; simp only [Finset.mem_filter, Finset.mem_product] at hij; exact hij.1.1
          · intro ij1 h1 ij2 h2 heq
            simp only [Finset.mem_filter] at h1 h2
            ext <;> omega
          · intro k hk
            exact ⟨(k, k), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hk, hk⟩, rfl⟩, rfl⟩
          · intro ij hij
            simp only [Finset.mem_filter] at hij
            rw [hij.2, pow_two]
        have hoff : ∑ ij ∈ (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 ≠ ij.2),
            (ij.1 : ZMod p)⁻¹ * (ij.2 : ZMod p)⁻¹ =
            2 * ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, (k : ZMod p)⁻¹ := by
          have hlt_gt :
              ∑ ij ∈ (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 ≠ ij.2),
                (ij.1 : ZMod p)⁻¹ * (ij.2 : ZMod p)⁻¹ =
              2 * ∑ ij ∈ (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 < ij.2),
                (ij.1 : ZMod p)⁻¹ * (ij.2 : ZMod p)⁻¹ := by
            have hsp : (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 ≠ ij.2) =
                (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 < ij.2) ∪
                (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.2 < ij.1) := by
              ext ij
              simp only [Finset.mem_union, Finset.mem_filter]
              by_cases h : ij ∈ Finset.Ico 1 p ×ˢ Finset.Ico 1 p
              · simp only [h, true_and]; omega
              · simp [h]
            rw [hsp, Finset.sum_union (Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega)]
            have hswap :
                ∑ ij ∈ (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.2 < ij.1),
                  (ij.1 : ZMod p)⁻¹ * (ij.2 : ZMod p)⁻¹ =
                ∑ ij ∈ (Finset.Ico 1 p ×ˢ Finset.Ico 1 p).filter (fun ij => ij.1 < ij.2),
                  (ij.1 : ZMod p)⁻¹ * (ij.2 : ZMod p)⁻¹ := by
              refine Finset.sum_bij (fun ij _ => (ij.2, ij.1)) ?_ ?_ ?_ ?_
              · intro ij hij; simp only [Finset.mem_filter, Finset.mem_product] at hij ⊢
                exact ⟨⟨hij.1.2, hij.1.1⟩, hij.2⟩
              · intro a _ b _ h; simp only [Prod.mk.injEq] at h; ext <;> omega
              · intro ij hij; simp only [Finset.mem_filter, Finset.mem_product] at hij
                exact ⟨(ij.2, ij.1), Finset.mem_filter.mpr
                  ⟨Finset.mem_product.mpr ⟨hij.1.2, hij.1.1⟩, hij.2⟩, rfl⟩
              · intro ij _; ring
            rw [hswap]; ring
          rw [hlt_gt]
          congr 1
          refine Finset.sum_bij (fun ij _ => ({ij.1, ij.2} : Finset ℕ)) ?_ ?_ ?_ ?_
          · intro ij hij
            simp only [Finset.mem_filter, Finset.mem_product] at hij
            rw [Finset.mem_powersetCard]
            refine ⟨?_, Finset.card_pair (by omega)⟩
            intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl <;> [exact hij.1.1; exact hij.1.2]
          · intro a ha b hb heq
            simp only [Finset.mem_filter] at ha hb
            have h1 : a.1 ∈ ({b.1, b.2} : Finset ℕ) := by rw [← heq]; simp
            have h2 : a.2 ∈ ({b.1, b.2} : Finset ℕ) := by rw [← heq]; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
            ext <;> omega
          · intro S hS
            rw [Finset.mem_powersetCard] at hS
            obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS.2
            have hx : x ∈ Finset.Ico 1 p := hS.1 (by simp)
            have hy : y ∈ Finset.Ico 1 p := hS.1 (by simp)
            rcases lt_or_gt_of_ne hxy with hlt | hgt
            · exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hlt⟩, rfl⟩
            · exact ⟨(y, x), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy, hx⟩, hgt⟩,
                Finset.pair_comm y x⟩
          · intro ij hij
            simp only [Finset.mem_filter] at hij
            rw [Finset.prod_pair (by omega)]
        have hπ_e2 : π (∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) =
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, (k : ZMod p)⁻¹ := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun S hS => ?_
          rw [map_prod]
          refine Finset.prod_congr rfl fun k hk => hπ_inv k ((Finset.mem_powersetCard.mp hS).1 hk)
        rw [hπ_e2, ← hoff, hsq]; ring
      rw [hsum1_p, sum_inv_sq_mod_p hp hp5] at h2e2
      simp only [zero_pow (by omega : 2 ≠ 0), sub_self] at h2e2
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h2; have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff 2 p).mp h2); omega
      exact (mul_eq_zero.mp h2e2).resolve_left h2ne
    set E2 := ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k
    have hE2_dvd : p ∣ E2.val := by
      have h1 : (E2.val : ZMod p) = 0 := by
        have := he2_p
        rwa [← ZMod.natCast_zmod_val E2, map_natCast] at this
      exact (ZMod.natCast_eq_zero_iff E2.val p).mp h1
    obtain ⟨q, hq⟩ := hE2_dvd
    rw [← ZMod.natCast_zmod_val E2, hq, Nat.cast_mul, ← mul_assoc, ← pow_succ,
      ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
  -- Combine Step 1 and Step 2: ∏_{k=1}^{p-1} (1 + 2*p * inv3 k) = 1 in ZMod (p^3)!
  have hprod_one : ∏ k ∈ Finset.Ico 1 p, (1 + (2 * p : ZMod (p ^ 3)) * inv3 k) = 1 := by
    rw [hprod_expand]
    have ht1 : (2 * p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k = 0 := by
      calc (2 * p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k
          = 2 * ((p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k) := by ring
        _ = 0 := by rw [hH1, mul_zero]
    have ht2 : (2 * p : ZMod (p ^ 3)) ^ 2 *
        ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k = 0 := by
      calc (2 * p : ZMod (p ^ 3)) ^ 2 *
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k
          = 4 * ((p : ZMod (p ^ 3)) ^ 2 *
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) := by ring
        _ = 0 := by rw [hH2, mul_zero]
    rw [ht1, ht2, add_zero, add_zero]
  -- Multiply by ∏ k ∈ Ico 1 p, k = (p - 1)!
  have hprod_eq : (∏ k ∈ Finset.Ico 1 p, (2 * p + k : ZMod (p ^ 3))) =
      ∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) := by
    calc (∏ k ∈ Finset.Ico 1 p, (2 * p + k : ZMod (p ^ 3)))
        = ∏ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 3)) * (1 + (2 * p : ZMod (p ^ 3)) * inv3 k)) := by
            refine Finset.prod_congr rfl fun k hk => ?_
            rw [mul_add, mul_one, mul_comm (2 * p : ZMod (p ^ 3)), ← mul_assoc, hinv3_mul k hk,
              one_mul, add_comm]
      _ = (∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3))) *
            ∏ k ∈ Finset.Ico 1 p, (1 + (2 * p : ZMod (p ^ 3)) * inv3 k) :=
            Finset.prod_mul_distrib
      _ = ∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) := by rw [hprod_one, mul_one]
  -- Relate ∏_{k=1}^{p-1} (2*p + k) to Nat.choose (3*p - 1) (p - 1) * (p - 1)!
  have hfac_eq : ∏ k ∈ Finset.Ico 1 p, k = Nat.factorial (p - 1) := by
    have : ∀ n : ℕ, ∏ k ∈ Finset.Ico 1 (n + 1), k = Nat.factorial n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_Ico_succ_top (by omega), ih, Nat.factorial_succ, mul_comm]
    simpa [show p - 1 + 1 = p by omega] using this (p - 1)
  have hdesc_eq : ∏ k ∈ Finset.Ico 1 p, (2 * p + k) =
      Nat.choose (3 * p - 1) (p - 1) * Nat.factorial (p - 1) := by
    have h1 : (∏ k ∈ Finset.Ico 1 p, (2 * p + k)) * Nat.factorial (2 * p) =
        Nat.factorial (3 * p - 1) := by
      have hgen : ∀ n : ℕ, (∏ k ∈ Finset.Ico 1 (n + 1), (2 * p + k)) * Nat.factorial (2 * p) =
          Nat.factorial (2 * p + n) := by
        intro n
        induction n with
        | zero => simp
        | succ m ih =>
          rw [Finset.prod_Ico_succ_top (by omega), mul_comm _ (2 * p + (m + 1)), mul_assoc, ih,
            show 2 * p + (m + 1) = (2 * p + m) + 1 by omega, ← Nat.factorial_succ]
      simpa [show p - 1 + 1 = p by omega, show 2 * p + (p - 1) = 3 * p - 1 by omega] using
        hgen (p - 1)
    have hch := Nat.choose_mul_factorial_mul_factorial (show p - 1 ≤ 3 * p - 1 by omega)
    rw [show 3 * p - 1 - (p - 1) = 2 * p by omega] at hch
    have hmul : (∏ k ∈ Finset.Ico 1 p, (2 * p + k)) * Nat.factorial (2 * p) =
        (Nat.choose (3 * p - 1) (p - 1) * Nat.factorial (p - 1)) * Nat.factorial (2 * p) := by
      rw [h1, hch]
    exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (2 * p)) hmul
  have hcast_eq : ((Nat.choose (3 * p - 1) (p - 1) : ZMod (p ^ 3)) - 1) *
      (Nat.factorial (p - 1) : ZMod (p ^ 3)) = 0 := by
    have h1 : (Nat.choose (3 * p - 1) (p - 1) : ZMod (p ^ 3)) *
        (Nat.factorial (p - 1) : ZMod (p ^ 3)) = (Nat.factorial (p - 1) : ZMod (p ^ 3)) := by
      rw [← Nat.cast_mul, ← hdesc_eq, ← hfac_eq, Nat.cast_prod, Nat.cast_prod]
      simpa [Nat.cast_add, Nat.cast_mul] using hprod_eq
    rw [sub_mul, one_mul, h1, sub_self]
  have hfac_unit : IsUnit (Nat.factorial (p - 1) : ZMod (p ^ 3)) := by
    rw [← hfac_eq, Nat.cast_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one
      (fun k hk => hunit k hk)
  have hch_one : (Nat.choose (3 * p - 1) (p - 1) : ZMod (p ^ 3)) = 1 := by
    have h0 : ((Nat.choose (3 * p - 1) (p - 1) : ZMod (p ^ 3)) - 1) *
        (Nat.factorial (p - 1) : ZMod (p ^ 3)) =
        0 * (Nat.factorial (p - 1) : ZMod (p ^ 3)) := by
      rw [zero_mul]; exact hcast_eq
    exact sub_eq_zero.mp (hfac_unit.mul_right_cancel h0)
  have hge1 : 1 ≤ Nat.choose (3 * p - 1) (p - 1) :=
    Nat.choose_pos (by omega)
  have hsub0 : ((Nat.choose (3 * p - 1) (p - 1) - 1 : ℕ) : ZMod (p ^ 3)) = 0 := by
    rw [Nat.cast_sub hge1, Nat.cast_one, hch_one, sub_self]
  exact (ZMod.natCast_eq_zero_iff _ _).mp hsub0

private theorem main_proved :
    ∀ p : ℕ, Nat.Prime p → Odd p →
      3 * p ^ 3 ∣ ((p + 1) * Nat.factorial (3 * p) /
        (Nat.factorial (2 * p - 1) * Nat.factorial (p + 1) * (2 * p)) - 3) := by
  intro p hp hodd
  have hp2 : 2 ≤ p := hp.two_le
  rw [ratio_eq_choose p (by omega), choose_three_mul_eq p (by omega)]
  have h3_factor : 3 * Nat.choose (3 * p - 1) (p - 1) - 3 =
      3 * (Nat.choose (3 * p - 1) (p - 1) - 1) := by
    have h1 : 1 ≤ Nat.choose (3 * p - 1) (p - 1) := Nat.choose_pos (by omega)
    omega
  rw [h3_factor]
  refine mul_dvd_mul_left 3 ?_
  by_cases hp3 : p = 3
  · subst hp3; decide
  · have hp5 : 5 ≤ p := by
      rcases hodd with ⟨k, rfl⟩
      have : k ≠ 0 := by omega
      have : k ≠ 1 := by omega
      omega
    exact wolstenholme_choose hp hp5

end OMA.S_oeis_a217772

theorem OMA.solution : type_of% @OMA.S_oeis_a217772.main :=
  OMA.S_oeis_a217772.main_proved
