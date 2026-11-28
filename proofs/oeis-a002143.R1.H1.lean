import OMAReductions.R_oeis_a002143_R1

namespace OMA.Proof_oeis_a002143_R1_H1

open Real

private lemma cot_sub_cot_two_mul (θ : ℝ) (hsin : sin θ ≠ 0) (hcos : cos θ ≠ 0) :
    cot θ - cot (2 * θ) = 1 / sin (2 * θ) := by
  rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, sin_two_mul, cos_two_mul]
  have h2 : (2 : ℝ) * sin θ * cos θ ≠ 0 := by positivity
  field_simp [hsin, hcos]
  have hpyth := sin_sq_add_cos_sq θ
  nlinarith

private lemma sin_two_pi_mod (p a : ℕ) (hp : p ≠ 0) :
    sin (2 * π * (a : ℝ) / p) = sin (2 * π * ((a % p : ℕ) : ℝ) / p) := by
  have hdiv : (a : ℝ) = (p : ℝ) * (a / p : ℕ) + ((a % p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a p).symm
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have harg : 2 * π * (a : ℝ) / p =
      2 * π * ((a % p : ℕ) : ℝ) / p + ((a / p : ℕ) : ℝ) * (2 * π) := by
    rw [hdiv]
    field_simp [hp0]
    ring
  rw [harg]
  exact sin_add_nat_mul_two_pi _ _

private lemma cot_pi_mod (p a : ℕ) (hp : p ≠ 0) :
    cot (π * (a : ℝ) / p) = cot (π * ((a % p : ℕ) : ℝ) / p) := by
  have hdiv : (a : ℝ) = (p : ℝ) * (a / p : ℕ) + ((a % p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod a p).symm
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have harg : π * (a : ℝ) / p =
      π * ((a % p : ℕ) : ℝ) / p + ((a / p : ℕ) : ℝ) * π := by
    rw [hdiv]
    field_simp [hp0]
    ring
  rw [harg]
  have hper : Function.Periodic Real.cot π := by
    intro x
    rw [cot_eq_cos_div_sin, cot_eq_cos_div_sin, cos_add_pi, sin_add_pi, neg_div_neg_eq]
  exact hper.nat_mul (a / p) _

private lemma legendreSym_mod (p a : ℕ) [Fact p.Prime] :
    legendreSym p ((a % p : ℕ) : ℤ) = legendreSym p (a : ℤ) := by
  rw [legendreSym.mod p ((a % p : ℕ) : ℤ), legendreSym.mod p (a : ℤ)]
  congr 1
  exact_mod_cast Nat.mod_mod a p

private lemma legendreSym_two_of_mod_eight (p : ℕ) [Fact p.Prime] (h8 : p % 8 = 3) :
    legendreSym p 2 = -1 := by
  have hp2 : p ≠ 2 := by omega
  rw [legendreSym.at_two hp2]
  have hmod : (p : ZMod 8) = 3 := by
    have : ((p % 8 : ℕ) : ZMod 8) = (p : ZMod 8) := ZMod.natCast_mod p 8
    rw [← this, h8]
    rfl
  rw [hmod]
  decide

private lemma sin_ne_zero_of_mem_Icc (p r : ℕ) (hr1 : 1 ≤ r) (hr2 : r ≤ p - 1) :
    sin (π * (r : ℝ) / p) ≠ 0 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpos : 0 < π * (r : ℝ) / p := by
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    positivity
  have hlt : π * (r : ℝ) / p < π := by
    rw [div_lt_iff₀ hp]
    have hrl : (r : ℝ) < p := by exact_mod_cast (show r < p by omega)
    nlinarith [pi_pos]
  exact (sin_pos_of_pos_of_lt_pi hpos hlt).ne'

private lemma cos_ne_zero_of_mem_Icc_odd (p r : ℕ) (hodd : p % 2 = 1)
    (_hr1 : 1 ≤ r) (_hr2 : r ≤ p - 1) :
    cos (π * (r : ℝ) / p) ≠ 0 := by
  intro h0
  rw [cos_eq_zero_iff] at h0
  obtain ⟨k, hk⟩ := h0
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hpi : π ≠ 0 := pi_ne_zero
  have heq : (2 : ℝ) * (r : ℝ) = (2 * (k : ℝ) + 1) * (p : ℝ) := by
    have h1 : (r : ℝ) / p = (2 * (k : ℝ) + 1) / 2 := by
      have h2 : π * ((r : ℝ) / p) = π * ((2 * (k : ℝ) + 1) / 2) := by
        calc π * ((r : ℝ) / p) = π * (r : ℝ) / p := by ring
          _ = (2 * (k : ℝ) + 1) * π / 2 := hk
          _ = π * ((2 * (k : ℝ) + 1) / 2) := by ring
      exact mul_left_cancel₀ hpi h2
    field_simp [hp] at h1
    linarith
  have hint : (2 * (r : ℤ)) = (2 * k + 1) * (p : ℤ) := by exact_mod_cast heq
  have hpmod : (p : ℤ) % 2 = 1 := by exact_mod_cast hodd
  have hrhs : ((2 * k + 1) * (p : ℤ)) % 2 = 1 := by
    rw [Int.mul_emod, hpmod]
    omega
  have hlhs : (2 * (r : ℤ)) % 2 = 0 := by omega
  omega

end OMA.Proof_oeis_a002143_R1_H1

theorem OMA.solution : OMA.R_oeis_a002143_R1.H1 := by
  intro p hpInst hp3 h8
  open Real OMA.Proof_oeis_a002143_R1_H1 in
  have hp : p.Prime := hpInst.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpodd : p % 2 = 1 := by omega
  let S : Finset ℕ := Finset.Icc 1 (p - 1)
  let QR : Finset ℕ := S.filter (fun r => legendreSym p (r : ℤ) = 1)
  let QNR : Finset ℕ := S.filter (fun r => legendreSym p (r : ℤ) = -1)
  have hQR_bij :
      (∑ k ∈ Finset.Icc 1 ((p - 1) / 2), 1 / sin (2 * π * (k : ℝ) ^ 2 / p)) =
        ∑ r ∈ QR, 1 / sin (2 * π * (r : ℝ) / p) := by
    refine Finset.sum_bij (fun k _ => k ^ 2 % p) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_Icc] at hk
      have hkp : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt hk.1 (by omega)
      have hk2p : ¬ p ∣ k ^ 2 := fun h => hkp (hp.dvd_of_dvd_pow h)
      have hpos : 0 < k ^ 2 % p := Nat.pos_of_ne_zero (fun h => hk2p (Nat.dvd_of_mod_eq_zero h))
      have hlt : k ^ 2 % p < p := Nat.mod_lt _ hp.pos
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rw [legendreSym_mod]
      have hne0 : ((k : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        have : (p : ℤ) ∣ (k : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (k : ℤ) p).mp h0
        exact hkp (Int.natCast_dvd_natCast.mp this)
      rw [Nat.cast_pow, sq, legendreSym.mul, ← sq]
      exact legendreSym.sq_one p hne0
    · intro k1 hk1 k2 hk2 heq
      rw [Finset.mem_Icc] at hk1 hk2
      have hmod : (k1 ^ 2 : ZMod p) = (k2 ^ 2 : ZMod p) := by
        have h1 : ((k1 ^ 2 % p : ℕ) : ZMod p) = (k1 ^ 2 : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_pow]
        have h2 : ((k2 ^ 2 % p : ℕ) : ZMod p) = (k2 ^ 2 : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_pow]
        rw [← h1, ← h2, heq]
      have hmul : ((k1 : ZMod p) - (k2 : ZMod p)) * ((k1 : ZMod p) + (k2 : ZMod p)) = 0 := by
        linear_combination hmod
      rcases mul_eq_zero.mp hmul with hsub | hadd
      · have heqz : (k1 : ZMod p) = (k2 : ZMod p) := sub_eq_zero.mp hsub
        have hlt1 : k1 < p := by omega
        have hlt2 : k2 < p := by omega
        have := congrArg ZMod.val heqz
        rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at this
        exact this
      · have hsum : ((k1 + k2 : ℕ) : ZMod p) = 0 := by simpa [Nat.cast_add] using hadd
        have hdvd : p ∣ k1 + k2 := (ZMod.natCast_eq_zero_iff (k1 + k2) p).mp hsum
        exact absurd hdvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_Icc] at hr
      obtain ⟨⟨hr1, hr2⟩, hleg⟩ := hr
      have hsq : IsSquare ((r : ℤ) : ZMod p) := (legendreSym.eq_one_iff p (by
        intro h0
        have : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp (by simpa using h0)
        exact Nat.not_dvd_of_pos_of_lt hr1 (by omega) this)).mp hleg
      obtain ⟨a, ha⟩ := hsq
      have ha0 : a ≠ 0 := by
        rintro rfl
        simp only [mul_zero] at ha
        have : p ∣ r := (ZMod.natCast_eq_zero_iff r p).mp (by simpa using ha)
        exact Nat.not_dvd_of_pos_of_lt hr1 (by omega) this
      have haval_pos : 0 < a.val := Nat.pos_of_ne_zero (fun h => ha0 (by
        have := ZMod.natCast_zmod_val a; rw [h, Nat.cast_zero] at this; exact this.symm))
      have haval_lt : a.val < p := a.val_lt
      by_cases hle : a.val ≤ (p - 1) / 2
      · refine ⟨a.val, Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
        have hz : ((a.val ^ 2 % p : ℕ) : ZMod p) = (r : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val, sq, ← ha]
          simp
        have := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_natCast_of_lt (by omega)] at this
        exact this
      · refine ⟨p - a.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        have hpa : ((p - a.val : ℕ) : ZMod p) = -a := by
          rw [Nat.cast_sub haval_lt.le, ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val]
        have hz : (((p - a.val) ^ 2 % p : ℕ) : ZMod p) = (r : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_pow, hpa, neg_sq, sq, ← ha]
          simp
        have := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_natCast_of_lt (by omega)] at this
        exact this
    · intro k _
      have hcast : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by push_cast; rfl
      rw [← hcast, sin_two_pi_mod p (k ^ 2) hp0]
  have h2_bij :
      (∑ r ∈ QR, cot (2 * π * (r : ℝ) / p)) = ∑ s ∈ QNR, cot (π * (s : ℝ) / p) := by
    have hleg2 : legendreSym p 2 = -1 := legendreSym_two_of_mod_eight p h8
    refine Finset.sum_bij (fun r _ => 2 * r % p) ?_ ?_ ?_ ?_
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_Icc] at hr
      obtain ⟨⟨hr1, hr2⟩, hlegr⟩ := hr
      have h2rp : ¬ p ∣ 2 * r := fun h => by
        rcases hp.dvd_mul.mp h with h2 | hrp
        · exact absurd (Nat.le_of_dvd (by decide) h2) (by omega)
        · exact Nat.not_dvd_of_pos_of_lt hr1 (by omega) hrp
      have hpos : 0 < 2 * r % p := Nat.pos_of_ne_zero (fun h => h2rp (Nat.dvd_of_mod_eq_zero h))
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by have := Nat.mod_lt (2 * r) hp.pos; omega⟩, ?_⟩
      rw [legendreSym_mod]
      push_cast
      rw [legendreSym.mul, hleg2, hlegr]
      ring
    · intro r1 hr1 r2 hr2 heq
      rw [Finset.mem_filter, Finset.mem_Icc] at hr1 hr2
      have hz : ((2 : ZMod p) * (r1 : ZMod p)) = (2 : ZMod p) * (r2 : ZMod p) := by
        have h1 : ((2 * r1 % p : ℕ) : ZMod p) = (2 : ZMod p) * (r1 : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
        have h2 : ((2 * r2 % p : ℕ) : ZMod p) = (2 : ZMod p) * (r2 : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
        rw [← h1, ← h2, heq]
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h0
        have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
        exact absurd (Nat.le_of_dvd (by decide) this) (by omega)
      have hr12 : (r1 : ZMod p) = (r2 : ZMod p) := mul_left_cancel₀ h2ne hz
      have := congrArg ZMod.val hr12
      rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
      exact this
    · intro s hs
      rw [Finset.mem_filter, Finset.mem_Icc] at hs
      obtain ⟨⟨hs1, hs2⟩, hlegs⟩ := hs
      let r : ℕ := ((p + 1) / 2 * s) % p
      have h2inv : 2 * ((p + 1) / 2) = p + 1 := by omega
      have h2r_mod : 2 * r % p = s := by
        have hz : ((2 * r % p : ℕ) : ZMod p) = (s : ZMod p) := by
          rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_mul, ← mul_assoc,
            ← Nat.cast_mul, h2inv]
          simp
        have := congrArg ZMod.val hz
        rw [ZMod.val_natCast_of_lt (Nat.mod_lt _ hp.pos), ZMod.val_natCast_of_lt (by omega)] at this
        exact this
      have hr1 : 1 ≤ r := by
        by_contra h0
        have hr0 : r = 0 := by omega
        rw [hr0] at h2r_mod
        simp at h2r_mod
        omega
      have hr2 : r ≤ p - 1 := by have := Nat.mod_lt ((p + 1) / 2 * s) hp.pos; omega
      have hlegr : legendreSym p (r : ℤ) = 1 := by
        have hmul : legendreSym p (2 * (r : ℤ)) = legendreSym p (s : ℤ) := by
          have : legendreSym p ((2 * r % p : ℕ) : ℤ) = legendreSym p (2 * (r : ℤ)) := by
            simpa [Nat.cast_mul] using legendreSym_mod p (2 * r)
          rw [← this, h2r_mod]
        rw [legendreSym.mul, hleg2, hlegs] at hmul
        omega
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr1, hr2⟩, hlegr⟩, h2r_mod⟩
    · intro r _
      have hmul : 2 * π * (r : ℝ) / p = π * ((2 * r : ℕ) : ℝ) / p := by push_cast; ring
      rw [hmul, cot_pi_mod p (2 * r) hp0]
  have hQR_eval :
      (∑ r ∈ QR, 1 / sin (2 * π * (r : ℝ) / p)) =
        (∑ r ∈ QR, cot (π * (r : ℝ) / p)) - ∑ r ∈ QR, cot (2 * π * (r : ℝ) / p) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    have harg : 2 * π * (r : ℝ) / p = 2 * (π * (r : ℝ) / p) := by ring
    rw [harg, ← cot_sub_cot_two_mul (π * (r : ℝ) / p)
      (sin_ne_zero_of_mem_Icc p r hr.1.1 hr.1.2)
      (cos_ne_zero_of_mem_Icc_odd p r hpodd hr.1.1 hr.1.2)]
  have hpart : S = QR ∪ QNR := by
    ext k
    simp only [Finset.mem_union, QR, QNR, Finset.mem_filter]
    constructor
    · intro hk
      have hk' := Finset.mem_Icc.mp hk
      have hne0 : ((k : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        have : p ∣ k := (ZMod.natCast_eq_zero_iff k p).mp (by simpa using h0)
        exact Nat.not_dvd_of_pos_of_lt hk'.1 (by omega) this
      rcases legendreSym.eq_one_or_neg_one p hne0 with h1 | hm1
      · exact Or.inl ⟨hk, h1⟩
      · exact Or.inr ⟨hk, hm1⟩
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  have hdisj : Disjoint QR QNR := by
    rw [Finset.disjoint_filter]
    intro k _ h1 hm1
    omega
  rw [hQR_bij, hQR_eval, h2_bij]
  change (∑ r ∈ QR, cot (π * (r : ℝ) / p)) - ∑ s ∈ QNR, cot (π * (s : ℝ) / p) =
    ∑ k ∈ S, (legendreSym p (k : ℤ) : ℝ) * cot (π * (k : ℝ) / p)
  rw [hpart, Finset.sum_union hdisj]
  have hsum1 : ∑ r ∈ QR, (legendreSym p (r : ℤ) : ℝ) * cot (π * (r : ℝ) / p) =
      ∑ r ∈ QR, cot (π * (r : ℝ) / p) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2]
    simp
  have hsum2 : ∑ s ∈ QNR, (legendreSym p (s : ℤ) : ℝ) * cot (π * (s : ℝ) / p) =
      -∑ s ∈ QNR, cot (π * (s : ℝ) / p) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [(Finset.mem_filter.mp hs).2]
    simp
  rw [hsum1, hsum2, sub_eq_add_neg]
