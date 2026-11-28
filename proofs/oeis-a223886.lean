import OMAStatements.S_oeis_a223886
import Mathlib

namespace OMA.S_oeis_a223886

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
  have hbij : ∑ k ∈ Finset.Ico 1 p, ((k : ZMod p)⁻¹) ^ 2 =
      ∑ k ∈ Finset.Ico 1 p, (k : ZMod p) ^ 2 := by
    refine Finset.sum_bij (fun k _ => ((k : ZMod p)⁻¹).val) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      have hkne : (k : ZMod p) ≠ 0 := by
        intro h0
        have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
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
        have := Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff j p).mp h0)
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

private lemma prod_shift_mod_p3 {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (t : ℕ) :
    (∏ k ∈ Finset.Ico 1 p, (t * p + k : ZMod (p ^ 3))) =
    ∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hunit : ∀ k ∈ Finset.Ico 1 p, IsUnit (k : ZMod (p ^ 3)) := by
    intro k hk
    simp only [Finset.mem_Ico] at hk
    have hcop : Nat.Coprime k (p ^ 3) :=
      ((hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega)).symm).pow_right 3
    exact (ZMod.isUnit_iff_coprime k (p ^ 3)).mpr hcop
  let inv3 : ℕ → ZMod (p ^ 3) := fun k =>
    if h : k ∈ Finset.Ico 1 p then ((hunit k h).unit⁻¹ : (ZMod (p ^ 3))ˣ) else 0
  have hinv3_mul : ∀ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) * inv3 k = 1 := by
    intro k hk
    simp only [inv3, dif_pos hk]
    exact (hunit k hk).mul_val_inv
  have hprod_expand :
      ∏ k ∈ Finset.Ico 1 p, (1 + (t * p : ZMod (p ^ 3)) * inv3 k) =
      1 + (t * p : ZMod (p ^ 3)) * (∑ k ∈ Finset.Ico 1 p, inv3 k) +
      (t * p : ZMod (p ^ 3)) ^ 2 *
        (∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) := by
    rw [Finset.prod_one_add]
    have hzero_ge3 : ∀ S ∈ (Finset.Ico 1 p).powerset, 3 ≤ S.card →
        ∏ k ∈ S, ((t * p : ZMod (p ^ 3)) * inv3 k) = 0 := by
      intro S _ hcard
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      have hp3 : (t * p : ZMod (p ^ 3)) ^ S.card = 0 := by
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
          ∏ k ∈ S, ((t * p : ZMod (p ^ 3)) * inv3 k) = 1 := by
        simp [Finset.powersetCard_zero]
      have h1 : ∑ S ∈ (Finset.Ico 1 p).powersetCard 1,
          ∏ k ∈ S, ((t * p : ZMod (p ^ 3)) * inv3 k) =
          (t * p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k := by
        rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
        simp
      have h2 : ∑ S ∈ (Finset.Ico 1 p).powersetCard 2,
          ∏ k ∈ S, ((t * p : ZMod (p ^ 3)) * inv3 k) =
          (t * p : ZMod (p ^ 3)) ^ 2 *
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp hS).2]
      have h3 : ∑ S ∈ (Finset.Ico 1 p).powerset.filter (fun S => 3 ≤ S.card),
          ∏ k ∈ S, ((t * p : ZMod (p ^ 3)) * inv3 k) = 0 := by
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
      rw [← ZMod.natCast_zmod_val S, hq, Nat.cast_mul, ← mul_assoc, ← pow_succ,
        ← Nat.cast_pow, ZMod.natCast_self, zero_mul]
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
  have hprod_one : ∏ k ∈ Finset.Ico 1 p, (1 + (t * p : ZMod (p ^ 3)) * inv3 k) = 1 := by
    rw [hprod_expand]
    have ht1 : (t * p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k = 0 := by
      calc (t * p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k
          = (t : ZMod (p ^ 3)) * ((p : ZMod (p ^ 3)) * ∑ k ∈ Finset.Ico 1 p, inv3 k) := by ring
        _ = 0 := by rw [hH1, mul_zero]
    have ht2 : (t * p : ZMod (p ^ 3)) ^ 2 *
        ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k = 0 := by
      calc (t * p : ZMod (p ^ 3)) ^ 2 *
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k
          = (t : ZMod (p ^ 3)) ^ 2 * ((p : ZMod (p ^ 3)) ^ 2 *
            ∑ S ∈ (Finset.Ico 1 p).powersetCard 2, ∏ k ∈ S, inv3 k) := by ring
        _ = 0 := by rw [hH2, mul_zero]
    rw [ht1, ht2, add_zero, add_zero]
  calc (∏ k ∈ Finset.Ico 1 p, (t * p + k : ZMod (p ^ 3)))
      = ∏ k ∈ Finset.Ico 1 p, ((k : ZMod (p ^ 3)) * (1 + (t * p : ZMod (p ^ 3)) * inv3 k)) := by
          refine Finset.prod_congr rfl fun k hk => ?_
          rw [mul_add, mul_one, mul_comm (t * p : ZMod (p ^ 3)), ← mul_assoc, hinv3_mul k hk,
            one_mul, add_comm]
    _ = (∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3))) *
          ∏ k ∈ Finset.Ico 1 p, (1 + (t * p : ZMod (p ^ 3)) * inv3 k) :=
          Finset.prod_mul_distrib
    _ = ∏ k ∈ Finset.Ico 1 p, (k : ZMod (p ^ 3)) := by rw [hprod_one, mul_one]

private lemma factorial_block_prod (p : ℕ) (hp : 1 ≤ p) (s b : ℕ) :
    (∏ q ∈ Finset.range b, ((s + q + 1) * p * ∏ m ∈ Finset.Ico 1 p, ((s + q) * p + m))) *
      Nat.factorial (s * p) = Nat.factorial ((s + b) * p) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.prod_range_succ, mul_assoc, mul_comm _ (Nat.factorial (s * p)), ← mul_assoc, ih,
      mul_comm]
    have hstep : ∀ n : ℕ, (∏ m ∈ Finset.Ico 1 (n + 1), ((s + b) * p + m)) *
        Nat.factorial ((s + b) * p) = Nat.factorial ((s + b) * p + n) := by
      intro n
      induction n with
      | zero => simp
      | succ m ihm =>
        rw [Finset.prod_Ico_succ_top (by omega), mul_comm _ ((s + b) * p + (m + 1)), mul_assoc, ihm,
          show (s + b) * p + (m + 1) = ((s + b) * p + m) + 1 by omega, ← Nat.factorial_succ]
    have h1 := hstep (p - 1)
    rw [show p - 1 + 1 = p by omega] at h1
    rw [mul_assoc, h1, show (s + b + 1) * p = ((s + b) * p + (p - 1)) + 1 by
      have : (s + b + 1) * p = (s + b) * p + p := by ring
      omega, ← Nat.factorial_succ]
    congr 1
    have : (s + (b + 1)) * p = (s + b) * p + p := by ring
    omega

private lemma choose_mul_p_identity (p a b : ℕ) (hp : 1 ≤ p) (hba : b ≤ a) :
    Nat.choose (a * p) (b * p) * (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) =
    Nat.choose a b * (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) := by
  have h1 := factorial_block_prod p hp (a - b) b
  rw [show a - b + b = a by omega] at h1
  have h2 := factorial_block_prod p hp 0 b
  simp only [zero_add, zero_mul, Nat.factorial_zero, mul_one] at h2
  have hfac_a : (∏ q ∈ Finset.range b, (a - b + q + 1)) * Nat.factorial (a - b) =
      Nat.factorial a := by
    have hgen : ∀ n : ℕ, (∏ q ∈ Finset.range n, (a - b + q + 1)) * Nat.factorial (a - b) =
        Nat.factorial (a - b + n) := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, mul_comm _ (a - b + m + 1), mul_assoc, ih,
          show a - b + m + 1 = (a - b + m) + 1 by omega, ← Nat.factorial_succ]
        congr 1
    simpa [show a - b + b = a by omega] using hgen b
  have hfac_b : ∏ q ∈ Finset.range b, (q + 1) = Nat.factorial b := by
    have hgen : ∀ n : ℕ, ∏ q ∈ Finset.range n, (q + 1) = Nat.factorial n := by
      intro n
      induction n with
      | zero => simp
      | succ m ih =>
        rw [Finset.prod_range_succ, ih, Nat.factorial_succ, mul_comm]
    exact hgen b
  have h1' : (∏ q ∈ Finset.range b, (a - b + q + 1)) * p ^ b *
      (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
      Nat.factorial ((a - b) * p) = Nat.factorial (a * p) := by
    rw [← h1]
    congr 1
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2' : (∏ q ∈ Finset.range b, (q + 1)) * p ^ b *
      (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) = Nat.factorial (b * p) := by
    rw [← h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have hch_ap := Nat.choose_mul_factorial_mul_factorial (Nat.mul_le_mul_right p hba)
  rw [← Nat.sub_mul] at hch_ap
  have hch_a := Nat.choose_mul_factorial_mul_factorial hba
  have hpos : 0 < Nat.factorial b * p ^ b * Nat.factorial ((a - b) * p) * Nat.factorial (a - b) := by
    positivity
  have hmul :
      (Nat.choose (a * p) (b * p) *
        ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) *
      (Nat.factorial b * p ^ b * Nat.factorial ((a - b) * p) * Nat.factorial (a - b)) =
      (Nat.choose a b *
        ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
      (Nat.factorial b * p ^ b * Nat.factorial ((a - b) * p) * Nat.factorial (a - b)) := by
    have hL :
        (Nat.choose (a * p) (b * p) *
          ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) *
        (Nat.factorial b * p ^ b * Nat.factorial ((a - b) * p) * Nat.factorial (a - b)) =
        Nat.factorial (a * p) * Nat.factorial (a - b) := by
      calc _ = Nat.choose (a * p) (b * p) *
            ((∏ q ∈ Finset.range b, (q + 1)) * p ^ b *
              ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) *
            Nat.factorial ((a - b) * p) * Nat.factorial (a - b) := by
              rw [hfac_b]; ring
        _ = Nat.choose (a * p) (b * p) * Nat.factorial (b * p) *
            Nat.factorial ((a - b) * p) * Nat.factorial (a - b) := by rw [h2']
        _ = Nat.factorial (a * p) * Nat.factorial (a - b) := by rw [hch_ap]
    have hR :
        (Nat.choose a b *
          ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
        (Nat.factorial b * p ^ b * Nat.factorial ((a - b) * p) * Nat.factorial (a - b)) =
        Nat.factorial (a * p) * Nat.factorial (a - b) := by
      calc _ = (Nat.choose a b * Nat.factorial b * Nat.factorial (a - b)) *
            (p ^ b * (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
              Nat.factorial ((a - b) * p)) := by ring
        _ = Nat.factorial a *
            (p ^ b * (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
              Nat.factorial ((a - b) * p)) := by rw [hch_a]
        _ = ((∏ q ∈ Finset.range b, (a - b + q + 1)) * Nat.factorial (a - b)) *
            (p ^ b * (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
              Nat.factorial ((a - b) * p)) := by rw [← hfac_a]
        _ = ((∏ q ∈ Finset.range b, (a - b + q + 1)) * p ^ b *
            (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m)) *
            Nat.factorial ((a - b) * p)) * Nat.factorial (a - b) := by ring
        _ = Nat.factorial (a * p) * Nat.factorial (a - b) := by rw [h1']
    rw [hL, hR]
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

private lemma ljunggren_dvd {p : ℕ} (hp : Nat.Prime p) (hp5 : 5 ≤ p) (a b : ℕ) (hba : b ≤ a) :
    p ^ 3 ∣ (Nat.choose (a * p) (b * p) - Nat.choose a b) := by
  let _ : NeZero (p ^ 3) := ⟨pow_ne_zero 3 hp.ne_zero⟩
  have hid := choose_mul_p_identity p a b (by omega) hba
  have hle : Nat.choose a b ≤ Nat.choose (a * p) (b * p) := by
    have hple : (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) ≤
        ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((a - b + q) * p + m) := by
      refine Finset.prod_le_prod' fun q _ => Finset.prod_le_prod' fun m _ => ?_
      have : q * p ≤ (a - b + q) * p := Nat.mul_le_mul_right p (by omega)
      omega
    have hpos : 0 < ∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m) := by
      refine Finset.prod_pos fun q _ => Finset.prod_pos fun m hm => ?_
      simp only [Finset.mem_Ico] at hm; omega
    have h1 : Nat.choose a b * (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) ≤
        Nat.choose (a * p) (b * p) *
          (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (q * p + m)) := by
      rw [hid]
      exact Nat.mul_le_mul_left _ hple
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hP1 : (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((q : ZMod (p ^ 3)) * p + m)) =
      (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
    calc _ = ∏ _q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3)) :=
          Finset.prod_congr rfl fun q _ => prod_shift_mod_p3 hp hp5 q
      _ = (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
          rw [Finset.prod_const, Finset.card_range]
  have hP2 : (∏ q ∈ Finset.range b,
      ∏ m ∈ Finset.Ico 1 p, (((a - b + q : ℕ) : ZMod (p ^ 3)) * p + m)) =
      (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
    calc _ = ∏ _q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3)) :=
          Finset.prod_congr rfl fun q _ => prod_shift_mod_p3 hp hp5 (a - b + q)
      _ = (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
          rw [Finset.prod_const, Finset.card_range]
  simp only [← Nat.cast_add, ← Nat.cast_mul] at hP1 hP2
  have hunit : IsUnit ((∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b) := by
    refine IsUnit.pow b ?_
    refine Finset.prod_induction _ IsUnit (fun _ _ ha hb => ha.mul hb) isUnit_one fun m hm => ?_
    simp only [Finset.mem_Ico] at hm
    have hcop : Nat.Coprime m (p ^ 3) :=
      ((hp.coprime_iff_not_dvd.mpr (fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega)).symm).pow_right 3
    exact (ZMod.isUnit_iff_coprime m (p ^ 3)).mpr hcop
  have hcast' : (Nat.choose (a * p) (b * p) : ZMod (p ^ 3)) *
      (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b =
      (Nat.choose a b : ZMod (p ^ 3)) *
      (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
    have h1 : (∏ q ∈ Finset.range b, ∏ m ∈ Finset.Ico 1 p, ((q * p + m : ℕ) : ZMod (p ^ 3))) =
        (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
      simpa [Nat.cast_add, Nat.cast_mul] using hP1
    have h2 : (∏ q ∈ Finset.range b,
        ∏ m ∈ Finset.Ico 1 p, (((a - b + q) * p + m : ℕ) : ZMod (p ^ 3))) =
        (∏ m ∈ Finset.Ico 1 p, (m : ZMod (p ^ 3))) ^ b := by
      simpa [Nat.cast_add, Nat.cast_mul] using hP2
    have hcast0 := congr_arg (Nat.cast (R := ZMod (p ^ 3))) hid
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_prod, Nat.cast_prod] at hcast0
    simp_rw [Nat.cast_prod] at hcast0
    rwa [h1, h2] at hcast0
  have heq : (Nat.choose (a * p) (b * p) : ZMod (p ^ 3)) = (Nat.choose a b : ZMod (p ^ 3)) :=
    hunit.mul_right_cancel hcast'
  have hsub0 : ((Nat.choose (a * p) (b * p) - Nat.choose a b : ℕ) : ZMod (p ^ 3)) = 0 := by
    rw [Nat.cast_sub hle, heq, sub_self]
  exact (ZMod.natCast_eq_zero_iff _ _).mp hsub0

private lemma k_dvd_choose_mul (k m : ℕ) (hk : 0 < k) (hm : 0 < m) :
    k ∣ Nat.choose (m * k) m := by
  have h := Nat.add_one_mul_choose_eq (m * k - 1) (m - 1)
  have h1 : m * k - 1 + 1 = m * k := by
    have : 1 ≤ m * k := Nat.mul_pos hm hk
    omega
  have h2 : m - 1 + 1 = m := by omega
  rw [h1, h2] at h
  have h3 : m * Nat.choose (m * k) m = m * (k * Nat.choose (m * k - 1) (m - 1)) := by
    calc m * Nat.choose (m * k) m = m * k * Nat.choose (m * k - 1) (m - 1) := by linarith
      _ = m * (k * Nat.choose (m * k - 1) (m - 1)) := by ring
  have h4 := Nat.eq_of_mul_eq_mul_left hm h3
  exact ⟨Nat.choose (m * k - 1) (m - 1), h4⟩

private theorem main_proved :
    ∀ k j : ℕ, 0 < k → 0 < j →
      ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → N < p →
        k * p ^ 3 ∣ (Nat.choose (j * k * p) (j * p) - Nat.choose (k * j) j) := by
  intro k j hk hj
  refine ⟨max 3 k, fun p hp hNp => ?_⟩
  have hp3 : 3 < p := lt_of_le_of_lt (le_max_left 3 k) hNp
  have hkp : k < p := lt_of_le_of_lt (le_max_right 3 k) hNp
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have : p = 4 := by omega
    subst this
    exact absurd hp (by decide)
  rw [mul_comm k j]
  have hba : j ≤ j * k := Nat.le_mul_of_pos_right j hk
  have hp3_dvd : p ^ 3 ∣ (Nat.choose (j * k * p) (j * p) - Nat.choose (j * k) j) :=
    ljunggren_dvd hp hp5 (j * k) j hba
  have hk_dvd1 : k ∣ Nat.choose (j * k * p) (j * p) := by
    rw [show j * k * p = (j * p) * k by ring]
    exact k_dvd_choose_mul k (j * p) hk (Nat.mul_pos hj (by omega))
  have hk_dvd2 : k ∣ Nat.choose (j * k) j := k_dvd_choose_mul k j hk hj
  have hk_dvd : k ∣ (Nat.choose (j * k * p) (j * p) - Nat.choose (j * k) j) :=
    Nat.dvd_sub hk_dvd1 hk_dvd2
  have hcop : Nat.Coprime k (p ^ 3) := by
    have hcop1 : Nat.Coprime p k := hp.coprime_iff_not_dvd.mpr fun hd => by
      have := Nat.le_of_dvd hk hd; omega
    exact hcop1.symm.pow_right 3
  exact hcop.mul_dvd_of_dvd_of_dvd hk_dvd hp3_dvd

end OMA.S_oeis_a223886

theorem OMA.solution : type_of% @OMA.S_oeis_a223886.main :=
  OMA.S_oeis_a223886.main_proved
