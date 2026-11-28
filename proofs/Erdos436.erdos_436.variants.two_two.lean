import FormalConjectures.ErdosProblems.«436»

/-! The bound comes from small squares and is attained on a prime progression. -/

open Erdos436 Filter

lemma OMA.cast_ne_zero_of_small {p a : ℕ} (ha : 0 < a) (hp : a < p) :
    (a : ZMod p) ≠ 0 := by
  intro h
  exact hp.not_ge (Nat.le_of_dvd ha ((ZMod.natCast_eq_zero_iff a p).mp h))

lemma OMA.small_square_residue {p a b : ℕ} (hsq : b ^ 2 = a := by decide) (ha : 0 < a := by decide)
    (hp : a < p := by omega) :
    IsPowerResidue 2 p a := by
  refine ⟨OMA.cast_ne_zero_of_small ha hp, (b : ZMod p), ?_⟩
  rw [← Nat.cast_pow, hsq]

lemma OMA.square_of_residue {p a : ℕ} (h : IsPowerResidue 2 p a) :
    IsSquare (a : ZMod p) := by
  obtain ⟨_, x, hx⟩ := h
  exact (isSquare_iff_exists_sq _).mpr ⟨x, hx.symm⟩

lemma OMA.residue_iff_legendre {p a : ℕ} [Fact p.Prime] (ha : (a : ZMod p) ≠ 0) :
    IsPowerResidue 2 p a ↔ legendreSym p (a : ℤ) = 1 := by
  rw [legendreSym.eq_one_iff' p ha]
  refine ⟨OMA.square_of_residue, ?_⟩
  intro h
  obtain ⟨x, hx⟩ := (isSquare_iff_exists_sq _).mp h
  exact ⟨ha, x, hx.symm⟩

lemma OMA.residue_pair_bound (p n : ℕ)
    (h₀ : IsPowerResidue 2 p n) (h₁ : IsPowerResidue 2 p (n + 1)) (hn : 1 ≤ n := by decide) :
    r 2 2 p ≤ (n : ℕ∞) := by
  refine iInf₂_le n ⟨hn, ?_⟩
  intro i hi
  interval_cases i
  · simpa only [Nat.add_zero] using h₀
  · exact h₁

lemma OMA.quadratic_pair_upper (p : ℕ) (hp : p.Prime) (hp₁₀ : 10 < p) :
    r 2 2 p ≤ 9 := by
  let : Fact p.Prime := ⟨hp⟩
  have h1 : IsPowerResidue 2 p 1 :=
    OMA.small_square_residue (b := 1)
  have h4 : IsPowerResidue 2 p 4 :=
    OMA.small_square_residue (b := 2)
  have h9 : IsPowerResidue 2 p 9 :=
    OMA.small_square_residue (b := 3)
  by_cases h2 : IsPowerResidue 2 p 2
  · exact (OMA.residue_pair_bound p 1 h1 h2).trans (by decide)
  by_cases h3 : IsPowerResidue 2 p 3
  · exact (OMA.residue_pair_bound p 3 h3 h4).trans (by decide)
  by_cases h5 : IsPowerResidue 2 p 5
  · exact (OMA.residue_pair_bound p 4 h4 h5).trans (by decide)
  have hz (a : ℕ) (ha : 0 < a) (ha' : a ≤ 10) : (a : ZMod p) ≠ 0 :=
    OMA.cast_ne_zero_of_small ha (ha'.trans_lt hp₁₀)
  have hneg (a : ℕ) (ha : 0 < a) (ha' : a ≤ 10) (h : ¬ IsPowerResidue 2 p a) :
      legendreSym p (a : ℤ) = -1 := by
    have ha0 := hz a ha ha'
    apply (legendreSym.eq_neg_one_iff_not_one p (a := (a : ℤ))
      (by exact_mod_cast ha0)).mpr
    exact fun he => h ((OMA.residue_iff_legendre ha0).mpr he)
  have hL2 : legendreSym p 2 = -1 := hneg 2 (by decide) (by decide) h2
  have hL5 : legendreSym p 5 = -1 := hneg 5 (by decide) (by decide) h5
  have hL10 : legendreSym p 10 = 1 := by
    rw [show (10 : ℤ) = 2 * 5 by decide, legendreSym.mul, hL2, hL5]
    norm_num
  have h10 : IsPowerResidue 2 p 10 :=
    (OMA.residue_iff_legendre (hz 10 (by decide) (by decide))).mpr hL10
  exact OMA.residue_pair_bound p 9 h9 h10

lemma OMA.nonresidue_by_reciprocity {p q a : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp4 : p % 4 = 1) (hmod : p ≡ a [MOD q]) (hq : q ≠ 2 := by decide)
    (hno : ¬ IsSquare (a : ZMod q) := by rw [isSquare_iff_exists_sq]; decide) :
    ¬ IsPowerResidue 2 p q := by
  intro hr
  have hs := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := q)
    hp4 hq).mp (OMA.square_of_residue hr)
  have heq : (p : ZMod q) = (a : ZMod q) := (ZMod.natCast_eq_natCast_iff p a q).mpr hmod
  exact hno (heq ▸ hs)

lemma OMA.quadratic_pair_lower (p : ℕ) (hp : p.Prime) (hp₁₀ : 10 < p)
    (hpmod : p ≡ 437 [MOD 840]) : 9 ≤ r 2 2 p := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp4 : p % 4 = 1 := Nat.ModEq.of_dvd (by decide : 4 ∣ 840) hpmod
  have hp8 : p % 8 = 5 := Nat.ModEq.of_dvd (by decide : 8 ∣ 840) hpmod
  have hp3 : p ≡ 2 [MOD 3] := by
    unfold Nat.ModEq at *; omega
  have hp5 : p ≡ 2 [MOD 5] := by
    unfold Nat.ModEq at *; omega
  have hp7 : p ≡ 3 [MOD 7] := by
    unfold Nat.ModEq at *; omega
  have hs2 : ¬ IsSquare (2 : ZMod p) := by
    intro h
    have hmod := (ZMod.exists_sq_eq_two_iff (p := p) (by omega : p ≠ 2)).mp h
    omega
  have h2 : ¬ IsPowerResidue 2 p 2 := fun h => hs2 (OMA.square_of_residue h)
  have h3 : ¬ IsPowerResidue 2 p 3 :=
    OMA.nonresidue_by_reciprocity hp4 hp3
  have h5 : ¬ IsPowerResidue 2 p 5 :=
    OMA.nonresidue_by_reciprocity hp4 hp5
  have h7 : ¬ IsPowerResidue 2 p 7 :=
    OMA.nonresidue_by_reciprocity hp4 hp7
  have hL2 : legendreSym p 2 = -1 := (legendreSym.eq_neg_one_iff' p (a := 2)).mpr hs2
  have hL4 : legendreSym p 4 = 1 := by
    have hz : ((4 : ℕ) : ZMod p) ≠ 0 :=
      OMA.cast_ne_zero_of_small (by decide) (by omega : 4 < p)
    exact (OMA.residue_iff_legendre hz).mp
      (OMA.small_square_residue (b := 2))
  have hL8 : legendreSym p 8 = -1 := by
    rw [show (8 : ℤ) = 2 * 4 by decide, legendreSym.mul, hL2, hL4, mul_one]
  have h8 : ¬ IsPowerResidue 2 p 8 := fun h =>
    (legendreSym.eq_neg_one_iff' p (a := 8)).mp hL8 (OMA.square_of_residue h)
  refine le_iInf₂ ?_
  rintro n ⟨hn, h⟩
  have hn' : 9 ≤ n := by
    by_contra hlt
    interval_cases n
    · exact h2 (h 1 (by decide))
    · exact h2 (h 0 (by decide))
    · exact h3 (h 0 (by decide))
    · exact h5 (h 1 (by decide))
    · exact h5 (h 0 (by decide))
    · exact h7 (h 1 (by decide))
    · exact h7 (h 0 (by decide))
    · exact h8 (h 0 (by decide))
  exact_mod_cast hn'

theorem OMA.solution : type_of% @Erdos436.erdos_436.variants.two_two := by
  rw [Erdos436.runLimsup, Filter.limsup_eq]
  apply le_antisymm
  · apply sInf_le
    change ∀ᶠ p in (atTop ⊓ 𝓟 {p : ℕ | p.Prime}), r 2 2 p ≤ 9
    apply eventually_inf_principal.mpr
    filter_upwards [eventually_ge_atTop (11 : ℕ)] with p hp hprime
    exact OMA.quadratic_pair_upper p hprime (by omega)
  · apply le_sInf
    intro b hb
    have he : ∀ᶠ p in (atTop ⊓ 𝓟 {p : ℕ | p.Prime}), r 2 2 p ≤ b := hb
    have hu : ∀ᶠ p in atTop, p.Prime → r 2 2 p ≤ b := eventually_inf_principal.mp he
    obtain ⟨B, hB⟩ := eventually_atTop.mp hu
    obtain ⟨p, hp, hprime, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq (max B 10)
      (q := 840) (a := 437) (by decide) (by decide)
    exact (OMA.quadratic_pair_lower p hprime
      ((le_max_right B 10).trans_lt hp) hmod).trans
      (hB p ((le_max_left B 10).trans hp.le) hprime)