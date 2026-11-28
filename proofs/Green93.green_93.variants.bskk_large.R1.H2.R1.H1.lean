import OMAReductions.R_Green93_green_93_variants_bskk_large_R1_H2_R1
import Mathlib

/-!
Elementary proof of the single-prime finite-field polynomial divisor-of-degree-`d` bound `H1`
(Ford 2008; Eberhard-Ford-Green 2016; Pemantle-Peres-Rivin 2016; Bary-Soroker-Kozma 2020; BSKK23).

We take universal exponent `δ = 1 / 20`, threshold `k = ⌊(3 / 2) * log d⌋₊`, and moment parameters
`y = 3 / 2` (for `Ω_d(f) > k`) and `z = 3 / 4` (for `Ω_d(f) ≤ k`), using:
1. An exact degree-weighted double-counting recurrence for multiplicative weights on monic
   polynomials over `ZMod p` (yielding also `∑_{r ∣ j} r * |Irred r| = p^j`).
2. Strong induction against the binomial sequence `c_k = ∏_{i < k} (z + i) / (i + 1) ≤ k^{z - 1}`
   for `w_d(f) = z^{Ω_d(f)}`.
3. Finite-set Euler product induction for `y^{Ω_S(f)}` with `y = 3 / 2`.
4. Elementary exponential bounds `exp(2/5) ≤ 3/2` and `4/3 ≤ exp(29/100)`.
-/

namespace Green93H1

open Polynomial UniqueFactorizationMonoid
open scoped Classical

section MonicAndFactorization

variable {p : ℕ} [Fact p.Prime]

private lemma prime_ge_two (p : ℕ) [hp : Fact p.Prime] : 2 ≤ p := hp.out.two_le

private lemma p_real_ge_two (p : ℕ) [hp : Fact p.Prime] : (2 : ℝ) ≤ (p : ℝ) := by
  exact_mod_cast hp.out.two_le

private lemma p_real_pos (p : ℕ) [hp : Fact p.Prime] : (0 : ℝ) < (p : ℝ) := by
  have := p_real_ge_two p
  linarith

private noncomputable def monicPoly (p m : ℕ) (b : Fin m → ZMod p) : (ZMod p)[X] :=
  X ^ m + ∑ i : Fin m, C (b i) * X ^ (i : ℕ)

private lemma coeff_monicPoly_lt (m : ℕ) (b : Fin m → ZMod p) {k : ℕ} (hk : k < m) :
    (monicPoly p m b).coeff k = b ⟨k, hk⟩ := by
  unfold monicPoly
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hk), zero_add, finsetSum_coeff]
  have hterm : ∀ i : Fin m, (C (b i) * X ^ (i : ℕ)).coeff k = if i = ⟨k, hk⟩ then b i else 0 := by
    intro i
    rw [coeff_C_mul_X_pow]
    by_cases h : k = (i : ℕ)
    · have hi : i = ⟨k, hk⟩ := Fin.ext h.symm
      rw [if_pos h, if_pos hi]
    · have hi : i ≠ ⟨k, hk⟩ := fun heq => h (congrArg Fin.val heq).symm
      rw [if_neg h, if_neg hi]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  simp

private lemma coeff_monicPoly_self (m : ℕ) (b : Fin m → ZMod p) :
    (monicPoly p m b).coeff m = 1 := by
  unfold monicPoly
  rw [coeff_add, coeff_X_pow, if_pos rfl, finsetSum_coeff]
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin m)), (C (b i) * X ^ (i : ℕ)).coeff m = 0 := by
    intro i _
    rw [coeff_C_mul_X_pow, if_neg (Nat.ne_of_gt i.isLt)]
  rw [Finset.sum_eq_zero hzero, add_zero]

private lemma coeff_monicPoly_gt (m : ℕ) (b : Fin m → ZMod p) {k : ℕ} (hk : m < k) :
    (monicPoly p m b).coeff k = 0 := by
  unfold monicPoly
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_gt hk), zero_add, finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul_X_pow, if_neg (Nat.ne_of_gt (lt_trans i.isLt hk))]

private lemma natDegree_monicPoly (m : ℕ) (b : Fin m → ZMod p) :
    (monicPoly p m b).natDegree = m := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact coeff_monicPoly_gt m b hk
  · rw [coeff_monicPoly_self]
    exact one_ne_zero

private lemma monic_monicPoly (m : ℕ) (b : Fin m → ZMod p) :
    (monicPoly p m b).Monic := by
  show (monicPoly p m b).leadingCoeff = 1
  rw [leadingCoeff, natDegree_monicPoly, coeff_monicPoly_self]

private lemma monicPoly_injective (m : ℕ) :
    Function.Injective (monicPoly p m) := by
  intro b₁ b₂ h
  funext i
  have hc := congrArg (fun f => f.coeff i.val) h
  simpa [coeff_monicPoly_lt m b₁ i.isLt, coeff_monicPoly_lt m b₂ i.isLt] using hc

private lemma eq_monicPoly_of_monic_natDegree {m : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hd : f.natDegree = m) :
    f = monicPoly p m (fun i => f.coeff i.val) := by
  ext k
  rcases lt_trichotomy k m with hlt | rfl | hgt
  · rw [coeff_monicPoly_lt m _ hlt]
  · rw [coeff_monicPoly_self, ← hd]
    exact hf.leadingCoeff
  · rw [coeff_monicPoly_gt m _ hgt]
    exact coeff_eq_zero_of_natDegree_lt (hd.symm ▸ hgt)

private noncomputable def M (p : ℕ) [Fact p.Prime] (m : ℕ) : Finset (ZMod p)[X] :=
  Finset.univ.image (monicPoly p m)

private lemma mem_M_iff {m : ℕ} {f : (ZMod p)[X]} :
    f ∈ M p m ↔ f.Monic ∧ f.natDegree = m := by
  constructor
  · intro hf
    rcases Finset.mem_image.mp hf with ⟨b, _, rfl⟩
    exact ⟨monic_monicPoly m b, natDegree_monicPoly m b⟩
  · rintro ⟨hf, hd⟩
    refine Finset.mem_image.mpr ⟨fun i => f.coeff i.val, Finset.mem_univ _, ?_⟩
    exact (eq_monicPoly_of_monic_natDegree hf hd).symm

private lemma card_M (m : ℕ) : (M p m).card = p ^ m := by
  rw [M, Finset.card_image_of_injective _ (monicPoly_injective m),
    Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

private lemma M_zero : M p 0 = {1} := by
  ext f
  rw [mem_M_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hd⟩
    exact eq_one_of_monic_natDegree_zero hf hd
  · rintro rfl
    exact ⟨monic_one, natDegree_one⟩

private lemma mul_mem_M {m₁ m₂ : ℕ} {f g : (ZMod p)[X]}
    (hf : f ∈ M p m₁) (hg : g ∈ M p m₂) : f * g ∈ M p (m₁ + m₂) := by
  rw [mem_M_iff] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, ?_⟩
  rw [hf.1.natDegree_mul hg.1, hf.2, hg.2]

private lemma pow_mem_M {m : ℕ} {f : (ZMod p)[X]} (hf : f ∈ M p m) (e : ℕ) :
    f ^ e ∈ M p (e * m) := by
  rw [mem_M_iff] at hf ⊢
  refine ⟨hf.1.pow e, ?_⟩
  rw [hf.1.natDegree_pow, hf.2]

private lemma dvd_mem_M {n d : ℕ} {f g : (ZMod p)[X]}
    (hf : f ∈ M p n) (hg : g ∈ M p d) (hdvd : g ∣ f) :
    ∃ h ∈ M p (n - d), f = g * h := by
  rw [mem_M_iff] at hf hg
  obtain ⟨h, rfl⟩ := hdvd
  have hne_g : g ≠ 0 := hg.1.ne_zero
  have hne_gh : g * h ≠ 0 := hf.1.ne_zero
  have hne_h : h ≠ 0 := right_ne_zero_of_mul hne_gh
  have hm_h : h.Monic := by
    show h.leadingCoeff = 1
    have hlc := hf.1.leadingCoeff
    rw [leadingCoeff_mul, hg.1.leadingCoeff, one_mul] at hlc
    exact hlc
  have hdeg : d + h.natDegree = n := by
    have h1 := hf.2
    rw [natDegree_mul hne_g hne_h, hg.2] at h1
    exact h1
  refine ⟨h, mem_M_iff.mpr ⟨hm_h, by omega⟩, rfl⟩

private noncomputable def Irred (p : ℕ) [Fact p.Prime] (r : ℕ) : Finset (ZMod p)[X] :=
  (M p r).filter Irreducible

private lemma mem_Irred_iff {r : ℕ} {P : (ZMod p)[X]} :
    P ∈ Irred p r ↔ P.Monic ∧ P.natDegree = r ∧ Irreducible P := by
  simp [Irred, mem_M_iff, and_assoc]

private lemma pos_natDegree_of_irreducible {P : (ZMod p)[X]} (hP : Irreducible P) :
    1 ≤ P.natDegree := by
  by_contra hlt
  have h0 : P.natDegree = 0 := by omega
  have hne : P ≠ 0 := hP.ne_zero
  have hC : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero h0
  have hc0 : P.coeff 0 ≠ 0 := by
    intro hz
    apply hne
    rw [hC, hz, map_zero]
  have hu : IsUnit P := by
    rw [hC]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0)
  exact hP.not_isUnit hu

private lemma Irred_zero : Irred p 0 = ∅ := by
  ext P
  simp only [mem_Irred_iff, Finset.notMem_empty, iff_false]
  rintro ⟨_, hd, hi⟩
  have := pos_natDegree_of_irreducible hi
  omega

private lemma eq_of_associated_of_monic {f g : (ZMod p)[X]}
    (hf : f.Monic) (hg : g.Monic) (h : Associated f g) : f = g := by
  obtain ⟨u, hu⟩ := h
  have hu0 : (u : (ZMod p)[X]) ≠ 0 := u.ne_zero
  have hlc : (u : (ZMod p)[X]).leadingCoeff = 1 := by
    have := congrArg Polynomial.leadingCoeff hu
    rw [leadingCoeff_mul, hf.leadingCoeff, hg.leadingCoeff, one_mul] at this
    exact this
  have hdeg : (u : (ZMod p)[X]).natDegree = 0 := by
    have hmul : (u : (ZMod p)[X]) * (↑u⁻¹ : (ZMod p)[X]) = 1 := u.mul_inv
    have h1 := congrArg Polynomial.natDegree hmul
    rw [natDegree_mul u.ne_zero u⁻¹.ne_zero, natDegree_one] at h1
    omega
  have hu1 : (u : (ZMod p)[X]) = 1 := by
    rw [eq_C_of_natDegree_eq_zero hdeg]
    have hc : (u : (ZMod p)[X]).coeff 0 = 1 := by
      rw [← hdeg]
      exact hlc
    rw [hc, map_one]
  rw [hu1, mul_one] at hu
  exact hu

private lemma normalize_eq_self_of_monic {f : (ZMod p)[X]} (hf : f.Monic) :
    normalize f = f := by
  refine eq_of_associated_of_monic ?_ hf (normalize_associated f)
  exact monic_normalize hf.ne_zero

private lemma monic_of_mem_normalizedFactors {f P : (ZMod p)[X]}
    (hP : P ∈ normalizedFactors f) : P.Monic := by
  have hirr : Irreducible P := irreducible_of_normalized_factor P hP
  have hnorm : normalize P = P := normalize_normalized_factor P hP
  rw [← hnorm]
  exact monic_normalize hirr.ne_zero

private lemma monic_multiset_prod {s : Multiset (ZMod p)[X]}
    (hs : ∀ P ∈ s, P.Monic) : s.prod.Monic := by
  induction s using Multiset.induction_on with
  | empty => simp [monic_one]
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact (hs a (Multiset.mem_cons_self a s)).mul
      (ih fun P hP => hs P (Multiset.mem_cons_of_mem hP))

private lemma prod_normalizedFactors_eq_of_monic {f : (ZMod p)[X]} (hf : f.Monic) :
    (normalizedFactors f).prod = f := by
  refine eq_of_associated_of_monic ?_ hf (prod_normalizedFactors hf.ne_zero)
  exact monic_multiset_prod fun P hP => monic_of_mem_normalizedFactors hP

private lemma natDegree_multiset_prod_of_monic {s : Multiset (ZMod p)[X]}
    (hs : ∀ P ∈ s, P.Monic) :
    s.prod.natDegree = (s.map Polynomial.natDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a.Monic := hs a (Multiset.mem_cons_self a s)
    have hs' : ∀ P ∈ s, P.Monic := fun P hP => hs P (Multiset.mem_cons_of_mem hP)
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
      ha.natDegree_mul (monic_multiset_prod hs'), ih hs']

private lemma natDegree_eq_sum_normalizedFactors {f : (ZMod p)[X]} (hf : f.Monic) :
    f.natDegree = ((normalizedFactors f).map Polynomial.natDegree).sum := by
  conv_lhs => rw [← prod_normalizedFactors_eq_of_monic hf]
  exact natDegree_multiset_prod_of_monic fun P hP => monic_of_mem_normalizedFactors hP

private lemma normalizedFactors_irred_of_monic {P : (ZMod p)[X]}
    (hPm : P.Monic) (hPi : Irreducible P) :
    normalizedFactors P = {P} := by
  rw [normalizedFactors_irreducible hPi, normalize_eq_self_of_monic hPm]

private lemma normalizedFactors_pow_of_monic_irred {P : (ZMod p)[X]}
    (hPm : P.Monic) (hPi : Irreducible P) (e : ℕ) :
    normalizedFactors (P ^ e) = Multiset.replicate e P := by
  induction e with
  | zero => simp [normalizedFactors_one]
  | succ e ih =>
    rw [pow_succ', normalizedFactors_mul hPm.ne_zero (hPm.pow e).ne_zero,
      normalizedFactors_irred_of_monic hPm hPi, ih, Multiset.replicate_succ]
    simp

private lemma pow_dvd_iff_le_count {P f : (ZMod p)[X]}
    (hPm : P.Monic) (hPi : Irreducible P) (hf : f.Monic) (e : ℕ) :
    P ^ e ∣ f ↔ e ≤ (normalizedFactors f).count P := by
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g ≠ 0 := right_ne_zero_of_mul hf.ne_zero
    rw [normalizedFactors_mul (hPm.pow e).ne_zero hg,
      normalizedFactors_pow_of_monic_irred hPm hPi e, Multiset.count_add,
      Multiset.count_replicate_self]
    omega
  · intro hle
    have hsub : Multiset.replicate e P ≤ normalizedFactors f :=
      Multiset.le_iff_count.mpr fun Q => by
        by_cases hQP : Q = P
        · subst hQP
          simpa [Multiset.count_replicate_self] using hle
        · simp [Multiset.count_replicate, Ne.symm hQP]
    obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hsub
    have hprod : (Multiset.replicate e P).prod * t.prod = f := by
      rw [← Multiset.prod_add, ← ht, prod_normalizedFactors_eq_of_monic hf]
    rw [Multiset.prod_replicate] at hprod
    exact ⟨t.prod, hprod.symm⟩

private lemma dvd_iff_pos_count {P f : (ZMod p)[X]}
    (hPm : P.Monic) (hPi : Irreducible P) (hf : f.Monic) :
    P ∣ f ↔ 1 ≤ (normalizedFactors f).count P := by
  simpa using pow_dvd_iff_le_count hPm hPi hf 1

private lemma count_mul_natDegree_le {P f : (ZMod p)[X]}
    (hPm : P.Monic) (hPi : Irreducible P) (hf : f.Monic) :
    (normalizedFactors f).count P * P.natDegree ≤ f.natDegree := by
  have hdvd : P ^ ((normalizedFactors f).count P) ∣ f :=
    (pow_dvd_iff_le_count hPm hPi hf _).mpr le_rfl
  obtain ⟨g, hg⟩ := hdvd
  have hgne : g ≠ 0 := right_ne_zero_of_mul (hg ▸ hf.ne_zero)
  have hdeg := congrArg Polynomial.natDegree hg
  rw [natDegree_mul (hPm.pow _).ne_zero hgne, hPm.natDegree_pow] at hdeg
  omega

private noncomputable def omegaS (S : Finset (ZMod p)[X]) (f : (ZMod p)[X]) : ℕ :=
  ((normalizedFactors f).filter (· ∈ S)).card

private lemma omegaS_empty (f : (ZMod p)[X]) : omegaS (∅ : Finset (ZMod p)[X]) f = 0 := by
  simp [omegaS]

private lemma omegaS_one (S : Finset (ZMod p)[X]) : omegaS S (1 : (ZMod p)[X]) = 0 := by
  simp [omegaS, normalizedFactors_one]

private lemma omegaS_mul (S : Finset (ZMod p)[X]) {f g : (ZMod p)[X]}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    omegaS S (f * g) = omegaS S f + omegaS S g := by
  simp [omegaS, normalizedFactors_mul hf hg, Multiset.filter_add]

private lemma omegaS_pow (S : Finset (ZMod p)[X]) {f : (ZMod p)[X]}
    (hf : f ≠ 0) (e : ℕ) :
    omegaS S (f ^ e) = e * omegaS S f := by
  induction e with
  | zero => simp [omegaS_one]
  | succ e ih =>
    rw [pow_succ', omegaS_mul S hf (pow_ne_zero e hf), ih]
    ring

private lemma omegaS_irred (S : Finset (ZMod p)[X]) {P : (ZMod p)[X]}
    (hPm : P.Monic) (hPi : Irreducible P) :
    omegaS S P = if P ∈ S then 1 else 0 := by
  unfold omegaS
  rw [normalizedFactors_irred_of_monic hPm hPi]
  by_cases h : P ∈ S
  · rw [if_pos h, Multiset.filter_singleton, if_pos h, Multiset.card_singleton]
  · rw [if_neg h, Multiset.filter_singleton, if_neg h]
    simp

private lemma omegaS_insert {P : (ZMod p)[X]} {S : Finset (ZMod p)[X]}
    (hPS : P ∉ S) (f : (ZMod p)[X]) :
    omegaS (insert P S) f = omegaS S f + (normalizedFactors f).count P := by
  unfold omegaS
  generalize normalizedFactors f = m
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases haP : a = P
    · subst haP
      rw [Multiset.filter_cons_of_pos _ (Finset.mem_insert_self a S),
        Multiset.filter_cons_of_neg _ hPS, Multiset.card_cons, Multiset.count_cons_self, ih]
      exact Nat.add_assoc _ _ _
    · by_cases haS : a ∈ S
      · rw [Multiset.filter_cons_of_pos _ (Finset.mem_insert_of_mem haS),
          Multiset.filter_cons_of_pos _ haS, Multiset.card_cons, Multiset.card_cons,
          Multiset.count_cons_of_ne (Ne.symm haP), ih]
        exact (Nat.add_right_comm _ _ _).symm
      · have hnot : a ∉ insert P S := by simp [haP, haS]
        rw [Multiset.filter_cons_of_neg _ hnot, Multiset.filter_cons_of_neg _ haS,
          Multiset.count_cons_of_ne (Ne.symm haP), ih]

private noncomputable def Sd (p : ℕ) [Fact p.Prime] (d : ℕ) : Finset (ZMod p)[X] :=
  (Finset.Icc 1 d).biUnion (Irred p)

private lemma mem_Sd_iff {d : ℕ} {P : (ZMod p)[X]} :
    P ∈ Sd p d ↔ P.Monic ∧ Irreducible P ∧ P.natDegree ≤ d := by
  simp only [Sd, Finset.mem_biUnion, Finset.mem_Icc, mem_Irred_iff]
  constructor
  · rintro ⟨r, ⟨_, hrd⟩, hPm, hdeg, hPi⟩
    exact ⟨hPm, hPi, hdeg ▸ hrd⟩
  · rintro ⟨hPm, hPi, hd⟩
    exact ⟨P.natDegree, ⟨pos_natDegree_of_irreducible hPi, hd⟩, hPm, rfl, hPi⟩

private lemma pairwiseDisjoint_Irred (p : ℕ) [Fact p.Prime] :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) (Irred p) := by
  intro r₁ _ r₂ _ hne
  show Disjoint (Irred p r₁) (Irred p r₂)
  rw [Finset.disjoint_left]
  intro P hP₁ hP₂
  rw [mem_Irred_iff] at hP₁ hP₂
  exact hne (hP₁.2.1.symm.trans hP₂.2.1)

end MonicAndFactorization

section Step1Recurrence

variable {p : ℕ} [Fact p.Prime]

private noncomputable def weightedAvg (p : ℕ) [Fact p.Prime] (w : (ZMod p)[X] → ℝ) (k : ℕ) : ℝ :=
  (p : ℝ) ^ (-(k : ℤ)) * ∑ f ∈ M p k, w f

private noncomputable def weightedB (p : ℕ) [Fact p.Prime] (w : (ZMod p)[X] → ℝ) (j : ℕ) : ℝ :=
  (p : ℝ) ^ (-(j : ℤ)) *
    ∑ r ∈ j.divisors, (r : ℝ) * ∑ P ∈ Irred p r, (w P) ^ (j / r)

private lemma weightedAvg_zero (w : (ZMod p)[X] → ℝ) (hw1 : w 1 = 1) :
    weightedAvg p w 0 = 1 := by
  simp [weightedAvg, M_zero, hw1]

private lemma weight_pow_of_mult {w : (ZMod p)[X] → ℝ}
    (hw1 : w 1 = 1) (hwm : ∀ f g, f.Monic → g.Monic → w (f * g) = w f * w g)
    {P : (ZMod p)[X]} (hPm : P.Monic) (e : ℕ) :
    w (P ^ e) = (w P) ^ e := by
  induction e with
  | zero => simp [hw1]
  | succ e ih =>
    rw [pow_succ', pow_succ', hwm P (P ^ e) hPm (hPm.pow e), ih]

private lemma sum_filter_pow_dvd {w : (ZMod p)[X] → ℝ}
    (hw1 : w 1 = 1) (hwm : ∀ f g, f.Monic → g.Monic → w (f * g) = w f * w g)
    {r e k : ℕ} {P : (ZMod p)[X]} (hP : P ∈ Irred p r) (her : e * r ≤ k) :
    ∑ f ∈ (M p k).filter (fun f => P ^ e ∣ f), w f =
      (w P) ^ e * ∑ g ∈ M p (k - e * r), w g := by
  have hPm : P.Monic := (mem_Irred_iff.mp hP).1
  have hPr : P.natDegree = r := (mem_Irred_iff.mp hP).2.1
  have hPM : P ∈ M p r := mem_M_iff.mpr ⟨hPm, hPr⟩
  have hPeM : P ^ e ∈ M p (e * r) := pow_mem_M hPM e
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij (fun g _ => P ^ e * g) ?_ ?_ ?_ ?_
  · intro g hg
    refine Finset.mem_filter.mpr ⟨?_, dvd_mul_right _ _⟩
    have hmul := mul_mem_M hPeM hg
    rwa [Nat.add_sub_of_le her] at hmul
  · intro g₁ _ g₂ _ h
    exact mul_left_cancel₀ (hPm.pow e).ne_zero h
  · intro f hf
    rcases Finset.mem_filter.mp hf with ⟨hfM, hdvd⟩
    obtain ⟨g, hgM, rfl⟩ := dvd_mem_M hfM hPeM hdvd
    exact ⟨g, hgM, rfl⟩
  · intro g hg
    have hgm : g.Monic := (mem_M_iff.mp hg).1
    rw [hwm (P ^ e) g (hPm.pow e) hgm, weight_pow_of_mult hw1 hwm hPm e]

private lemma multiset_map_sum_eq_sum_toFinset {α : Type*} [DecidableEq α]
    (m : Multiset α) (g : α → ℕ) :
    (m.map g).sum = ∑ a ∈ m.toFinset, m.count a * g a := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    by_cases ha : a ∈ m
    · have hto : (a ::ₘ m).toFinset = m.toFinset := by
        ext x
        simp only [Multiset.mem_toFinset, Multiset.mem_cons]
        exact ⟨fun h => h.elim (fun h' => h' ▸ ha) id, Or.inr⟩
      rw [hto]
      have ha_fin : a ∈ m.toFinset := Multiset.mem_toFinset.mpr ha
      rw [← Finset.add_sum_erase _ _ ha_fin, ← Finset.add_sum_erase _ _ ha_fin]
      have hrest :
          ∑ x ∈ m.toFinset.erase a, Multiset.count x (a ::ₘ m) * g x =
            ∑ x ∈ m.toFinset.erase a, Multiset.count x m * g x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hne : x ≠ a := (Finset.mem_erase.mp hx).1
        rw [Multiset.count_cons_of_ne hne]
      rw [hrest, Multiset.count_cons_self]
      ring
    · have ha_fin : a ∉ m.toFinset := fun h => ha (Multiset.mem_toFinset.mp h)
      rw [Multiset.toFinset_cons, Finset.sum_insert ha_fin, Multiset.count_cons_self,
        Multiset.count_eq_zero.mpr ha, zero_add, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      have hne : x ≠ a := fun h => ha_fin (h ▸ hx)
      rw [Multiset.count_cons_of_ne hne]

private lemma natDegree_eq_triple_sum {k : ℕ} {f : (ZMod p)[X]} (hf : f ∈ M p k) :
    (k : ℝ) = ∑ r ∈ Finset.Icc 1 k, ∑ P ∈ Irred p r, ∑ e ∈ Finset.Icc 1 (k / r),
      if P ^ e ∣ f then (r : ℝ) else 0 := by
  have hfm : f.Monic := (mem_M_iff.mp hf).1
  have hfd : f.natDegree = k := (mem_M_iff.mp hf).2
  have hnat : k = ∑ r ∈ Finset.Icc 1 k, ∑ P ∈ Irred p r, ∑ e ∈ Finset.Icc 1 (k / r),
      if P ^ e ∣ f then r else 0 := by
    have h1 : k = ((normalizedFactors f).map Polynomial.natDegree).sum := by
      rw [← hfd, natDegree_eq_sum_normalizedFactors hfm]
    have h2 : ((normalizedFactors f).map Polynomial.natDegree).sum =
        ∑ P ∈ (normalizedFactors f).toFinset, (normalizedFactors f).count P * P.natDegree :=
      multiset_map_sum_eq_sum_toFinset (normalizedFactors f) Polynomial.natDegree
    have hsub : (normalizedFactors f).toFinset ⊆ Sd p k := by
      intro P hP
      have hPm_mem : P ∈ normalizedFactors f := Multiset.mem_toFinset.mp hP
      have hPm : P.Monic := monic_of_mem_normalizedFactors hPm_mem
      have hPi : Irreducible P := irreducible_of_normalized_factor P hPm_mem
      have hcnt : 1 ≤ (normalizedFactors f).count P := Multiset.count_pos.mpr hPm_mem
      have hle := count_mul_natDegree_le hPm hPi hfm
      have hdeg_le : P.natDegree ≤ k := by
        calc
          P.natDegree = 1 * P.natDegree := (one_mul _).symm
          _ ≤ (normalizedFactors f).count P * P.natDegree := Nat.mul_le_mul_right _ hcnt
          _ ≤ f.natDegree := hle
          _ = k := hfd
      exact mem_Sd_iff.mpr ⟨hPm, hPi, hdeg_le⟩
    have h3 : ∑ P ∈ (normalizedFactors f).toFinset, (normalizedFactors f).count P * P.natDegree =
        ∑ P ∈ Sd p k, (normalizedFactors f).count P * P.natDegree := by
      refine Finset.sum_subset hsub fun P _ hPnot => ?_
      have hcnt0 : (normalizedFactors f).count P = 0 :=
        Multiset.count_eq_zero.mpr (fun h => hPnot (Multiset.mem_toFinset.mpr h))
      simp [hcnt0]
    have h4 : ∑ P ∈ Sd p k, (normalizedFactors f).count P * P.natDegree =
        ∑ r ∈ Finset.Icc 1 k, ∑ P ∈ Irred p r, (normalizedFactors f).count P * r := by
      rw [Sd, Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun P hP => ?_
        rw [(mem_Irred_iff.mp hP).2.1]
      · intro r₁ _ r₂ _ hne
        exact pairwiseDisjoint_Irred p (Set.mem_univ r₁) (Set.mem_univ r₂) hne
    conv_lhs => rw [h1, h2, h3, h4]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun P hP => ?_
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    rcases mem_Irred_iff.mp hP with ⟨hPm, hPr, hPi⟩
    have hcnt_le : (normalizedFactors f).count P ≤ k / r := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have hle := count_mul_natDegree_le hPm hPi hfm
      rwa [hPr, hfd] at hle
    have hflt : (Finset.Icc 1 (k / r)).filter (fun e => P ^ e ∣ f) =
        Finset.Icc 1 ((normalizedFactors f).count P) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_Icc, pow_dvd_iff_le_count hPm hPi hfm]
      omega
    rw [← Finset.sum_filter, hflt, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    have hsub1 : (normalizedFactors f).count P + 1 - 1 = (normalizedFactors f).count P := by omega
    rw [hsub1]
  have hcast := congrArg (Nat.cast (R := ℝ)) hnat
  push_cast at hcast
  exact hcast

private lemma weightedAvg_recurrence {w : (ZMod p)[X] → ℝ}
    (hw1 : w 1 = 1) (hwm : ∀ f g, f.Monic → g.Monic → w (f * g) = w f * w g) (k : ℕ) :
    (k : ℝ) * weightedAvg p w k =
      ∑ j ∈ Finset.Icc 1 k, weightedB p w j * weightedAvg p w (k - j) := by
  have hp_ne : (p : ℝ) ≠ 0 := (p_real_pos p).ne'
  have hsum_raw : (k : ℝ) * ∑ f ∈ M p k, w f =
      ∑ j ∈ Finset.Icc 1 k,
        (∑ r ∈ j.divisors, (r : ℝ) * ∑ P ∈ Irred p r, (w P) ^ (j / r)) *
          (∑ g ∈ M p (k - j), w g) := by
    have hstep1 : (k : ℝ) * ∑ f ∈ M p k, w f =
        ∑ r ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 (k / r),
          (r : ℝ) * (∑ P ∈ Irred p r, (w P) ^ e) * (∑ g ∈ M p (k - e * r), w g) := by
      rw [Finset.mul_sum]
      calc
        ∑ f ∈ M p k, (k : ℝ) * w f
          = ∑ f ∈ M p k,
              (∑ r ∈ Finset.Icc 1 k, ∑ P ∈ Irred p r, ∑ e ∈ Finset.Icc 1 (k / r),
                if P ^ e ∣ f then (r : ℝ) * w f else 0) := by
              refine Finset.sum_congr rfl fun f hf => ?_
              rw [natDegree_eq_triple_sum hf, Finset.sum_mul]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun P _ => ?_
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun e _ => ?_
              split_ifs <;> simp
        _ = ∑ r ∈ Finset.Icc 1 k, ∑ P ∈ Irred p r, ∑ e ∈ Finset.Icc 1 (k / r),
              ∑ f ∈ M p k, if P ^ e ∣ f then (r : ℝ) * w f else 0 := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun P _ => ?_
              rw [Finset.sum_comm]
        _ = ∑ r ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 (k / r),
              ∑ P ∈ Irred p r, ∑ f ∈ (M p k).filter (fun f => P ^ e ∣ f), (r : ℝ) * w f := by
              refine Finset.sum_congr rfl fun r _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun P _ => ?_
              rw [Finset.sum_filter]
        _ = ∑ r ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 (k / r),
              (r : ℝ) * (∑ P ∈ Irred p r, (w P) ^ e) * (∑ g ∈ M p (k - e * r), w g) := by
              refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun e he => ?_
              have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
              have he_le : e ≤ k / r := (Finset.mem_Icc.mp he).2
              have her : e * r ≤ k := (Nat.le_div_iff_mul_le (by omega)).mp he_le
              calc
                ∑ P ∈ Irred p r, ∑ f ∈ (M p k).filter (fun f => P ^ e ∣ f), (r : ℝ) * w f
                  = ∑ P ∈ Irred p r,
                      (r : ℝ) * ((w P) ^ e * ∑ g ∈ M p (k - e * r), w g) := by
                    refine Finset.sum_congr rfl fun P hP => ?_
                    rw [← Finset.mul_sum, sum_filter_pow_dvd hw1 hwm hP her]
                _ = (r : ℝ) * ∑ P ∈ Irred p r, (w P) ^ e * ∑ g ∈ M p (k - e * r), w g := by
                    rw [← Finset.mul_sum]
                _ = (r : ℝ) * (∑ P ∈ Irred p r, (w P) ^ e) * (∑ g ∈ M p (k - e * r), w g) := by
                    rw [← Finset.sum_mul, mul_assoc]
    rw [hstep1]
    have hsigma1 :
        ∑ r ∈ Finset.Icc 1 k, ∑ e ∈ Finset.Icc 1 (k / r),
          (r : ℝ) * (∑ P ∈ Irred p r, (w P) ^ e) * (∑ g ∈ M p (k - e * r), w g) =
        ∑ x ∈ (Finset.Icc 1 k).sigma (fun r => Finset.Icc 1 (k / r)),
          (x.1 : ℝ) * (∑ P ∈ Irred p x.1, (w P) ^ x.2) * (∑ g ∈ M p (k - x.2 * x.1), w g) := by
      rw [Finset.sum_sigma]
    have hsigma2 :
        ∑ j ∈ Finset.Icc 1 k,
          (∑ r ∈ j.divisors, (r : ℝ) * ∑ P ∈ Irred p r, (w P) ^ (j / r)) *
            (∑ g ∈ M p (k - j), w g) =
        ∑ y ∈ (Finset.Icc 1 k).sigma (fun j => j.divisors),
          (y.2 : ℝ) * (∑ P ∈ Irred p y.2, (w P) ^ (y.1 / y.2)) * (∑ g ∈ M p (k - y.1), w g) := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
    rw [hsigma1, hsigma2]
    refine Finset.sum_bij (fun x _ => ⟨x.2 * x.1, x.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨r, e⟩ hx
      rw [Finset.mem_sigma] at hx ⊢
      dsimp at hx ⊢
      rcases Finset.mem_Icc.mp hx.1 with ⟨hr1, _⟩
      rcases Finset.mem_Icc.mp hx.2 with ⟨he1, he_le⟩
      have her : e * r ≤ k := (Nat.le_div_iff_mul_le (by omega)).mp he_le
      have her1 : 1 ≤ e * r := Nat.mul_pos (by omega) (by omega)
      refine ⟨Finset.mem_Icc.mpr ⟨her1, her⟩, Nat.mem_divisors.mpr ⟨dvd_mul_left r e, by omega⟩⟩
    · rintro ⟨r₁, e₁⟩ hx₁ ⟨r₂, e₂⟩ hx₂ h
      rw [Finset.mem_sigma] at hx₁ hx₂
      dsimp at hx₁ hx₂
      have hr1 : 1 ≤ r₁ := (Finset.mem_Icc.mp hx₁.1).1
      have hfst : e₁ * r₁ = e₂ * r₂ := congrArg Sigma.fst h
      have hsnd : r₁ = r₂ := by
        simpa using congrArg Sigma.snd h
      subst hsnd
      have he : e₁ = e₂ := Nat.eq_of_mul_eq_mul_right (by omega) hfst
      subst he
      rfl
    · rintro ⟨j, r⟩ hy
      rw [Finset.mem_sigma] at hy
      dsimp at hy
      rcases Finset.mem_Icc.mp hy.1 with ⟨hj1, hjk⟩
      rcases Nat.mem_divisors.mp hy.2 with ⟨hrj, hj0⟩
      have hrpos : 1 ≤ r := Nat.pos_of_dvd_of_pos hrj (by omega)
      have hrk : r ≤ k := (Nat.le_of_dvd (by omega) hrj).trans hjk
      have hdiv_mul : (j / r) * r = j := Nat.div_mul_cancel hrj
      have hdiv_pos : 1 ≤ j / r :=
        Nat.div_pos (Nat.le_of_dvd (by omega) hrj) hrpos
      have hdiv_le : j / r ≤ k / r := Nat.div_le_div_right hjk
      refine ⟨⟨r, j / r⟩, Finset.mem_sigma.mpr
        ⟨Finset.mem_Icc.mpr ⟨hrpos, hrk⟩, Finset.mem_Icc.mpr ⟨hdiv_pos, hdiv_le⟩⟩, ?_⟩
      simp [hdiv_mul]
    · rintro ⟨r, e⟩ hx
      rw [Finset.mem_sigma] at hx
      dsimp at hx
      have hrpos : 0 < r := (Finset.mem_Icc.mp hx.1).1
      simp [Nat.mul_div_cancel e hrpos]
  calc
    (k : ℝ) * weightedAvg p w k
      = (p : ℝ) ^ (-(k : ℤ)) * ((k : ℝ) * ∑ f ∈ M p k, w f) := by
          unfold weightedAvg; ring
    _ = (p : ℝ) ^ (-(k : ℤ)) *
          ∑ j ∈ Finset.Icc 1 k,
            (∑ r ∈ j.divisors, (r : ℝ) * ∑ P ∈ Irred p r, (w P) ^ (j / r)) *
              (∑ g ∈ M p (k - j), w g) := by
          rw [hsum_raw]
    _ = ∑ j ∈ Finset.Icc 1 k, weightedB p w j * weightedAvg p w (k - j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjk : j ≤ k := (Finset.mem_Icc.mp hj).2
          have hexp : -(k : ℤ) = -(j : ℤ) + -((k - j : ℕ) : ℤ) := by omega
          unfold weightedB weightedAvg
          rw [hexp, zpow_add₀ hp_ne]
          ring

private lemma weightedAvg_one (k : ℕ) : weightedAvg p (fun _ => (1 : ℝ)) k = 1 := by
  have hp_ne : (p : ℝ) ≠ 0 := (p_real_pos p).ne'
  unfold weightedAvg
  rw [Finset.sum_const, card_M, nsmul_eq_mul, mul_one, zpow_neg, zpow_natCast,
    Nat.cast_pow, inv_mul_cancel₀ (pow_ne_zero k hp_ne)]

private lemma weightedB_one {j : ℕ} (hj : 1 ≤ j) :
    weightedB p (fun _ => (1 : ℝ)) j = 1 := by
  have hrec : ∀ k : ℕ, (k : ℝ) = ∑ i ∈ Finset.Icc 1 k, weightedB p (fun _ => (1 : ℝ)) i := by
    intro k
    have h := weightedAvg_recurrence (p := p) (w := fun _ => (1 : ℝ)) rfl
      (fun _ _ _ _ => by ring) k
    simpa [weightedAvg_one] using h
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
  have h1 := hrec (m + 1)
  have h2 := hrec m
  have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnotmem : m + 1 ∉ Finset.Icc 1 m := by simp
  rw [hIcc, Finset.sum_insert hnotmem, ← h2] at h1
  push_cast at h1
  linarith

private lemma card_Irred_mul_le {r : ℕ} (hr : 1 ≤ r) :
    (r : ℝ) * ((Irred p r).card : ℝ) ≤ (p : ℝ) ^ r := by
  have hB := weightedB_one (p := p) hr
  unfold weightedB at hB
  have hpow_pos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (p_real_pos p) r
  have hsum : ∑ d ∈ r.divisors, (d : ℝ) * ((Irred p d).card : ℝ) = (p : ℝ) ^ r := by
    have h1 : (p : ℝ) ^ (-(r : ℤ)) * ∑ d ∈ r.divisors, (d : ℝ) * ((Irred p d).card : ℝ) = 1 := by
      simpa using hB
    rw [zpow_neg, zpow_natCast] at h1
    have h2 := congrArg (fun x => (p : ℝ) ^ r * x) h1
    rwa [← mul_assoc, mul_inv_cancel₀ hpow_pos.ne', one_mul, mul_one] at h2
  rw [← hsum]
  exact Finset.single_le_sum (f := fun d : ℕ => (d : ℝ) * ((Irred p d).card : ℝ))
    (fun d _ => mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg _))
    (Nat.mem_divisors_self r (by omega))

private lemma card_Irred_le {r : ℕ} (hr : 1 ≤ r) :
    ((Irred p r).card : ℝ) ≤ (p : ℝ) ^ r / (r : ℝ) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  rw [le_div_iff₀ hrpos, mul_comm]
  exact card_Irred_mul_le hr

end Step1Recurrence

section Step2SubunitMoment

private noncomputable def binomSeq (z : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => (z + (k : ℝ)) / ((k : ℝ) + 1) * binomSeq z k

private lemma binomSeq_pos {z : ℝ} (hz : 0 < z) (k : ℕ) : 0 < binomSeq z k := by
  induction k with
  | zero => simp [binomSeq]
  | succ k ih =>
    simp only [binomSeq]
    positivity

private lemma mul_binomSeq_eq (z : ℝ) (k : ℕ) :
    (k : ℝ) * binomSeq z k = z * ∑ i ∈ Finset.range k, binomSeq z i := by
  induction k with
  | zero => simp [binomSeq]
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih]
    simp only [binomSeq]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp [hk1]
    ring

private lemma log_add_one_le_harmonic (k : ℕ) :
    Real.log ((k : ℝ) + 1) ≤ ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hstep : Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
      rw [← Real.log_div hk2.ne' hk1.ne']
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk2 hk1)
      have hdiv : ((k : ℝ) + 2) / ((k : ℝ) + 1) - 1 = 1 / ((k : ℝ) + 1) := by
        field_simp [hk1.ne']
        ring
      linarith
    push_cast
    rw [show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring]
    linarith

private lemma binomSeq_le_exp_harmonic {z : ℝ} (hz0 : 0 < z) (k : ℕ) :
    binomSeq z k ≤ Real.exp (-(1 - z) * ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1)) := by
  induction k with
  | zero => simp [binomSeq]
  | succ k ih =>
    unfold binomSeq
    rw [Finset.sum_range_succ, mul_add, Real.exp_add]
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hfrac : (z + (k : ℝ)) / ((k : ℝ) + 1) ≤ Real.exp (-(1 - z) * (1 / ((k : ℝ) + 1))) := by
      have heq : (z + (k : ℝ)) / ((k : ℝ) + 1) = -(1 - z) * (1 / ((k : ℝ) + 1)) + 1 := by
        field_simp [hk1.ne']
        ring
      rw [heq]
      exact Real.add_one_le_exp _
    calc
      (z + (k : ℝ)) / ((k : ℝ) + 1) * binomSeq z k
        ≤ Real.exp (-(1 - z) * (1 / ((k : ℝ) + 1))) *
            Real.exp (-(1 - z) * ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1)) :=
          mul_le_mul hfrac ih (binomSeq_pos hz0 k).le (Real.exp_pos _).le
      _ = Real.exp (-(1 - z) * ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1)) *
            Real.exp (-(1 - z) * (1 / ((k : ℝ) + 1))) := mul_comm _ _

private lemma binomSeq_le_rpow {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) {k : ℕ} (hk : 1 ≤ k) :
    binomSeq z k ≤ (k : ℝ) ^ (z - 1) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 := binomSeq_le_exp_harmonic hz0 k
  have h2 : -(1 - z) * ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1) ≤
      Real.log ((k : ℝ) + 1) * (z - 1) := by
    have hhar := log_add_one_le_harmonic k
    nlinarith
  calc
    binomSeq z k
      ≤ Real.exp (-(1 - z) * ∑ i ∈ Finset.range k, (1 : ℝ) / ((i : ℝ) + 1)) := h1
    _ ≤ Real.exp (Real.log ((k : ℝ) + 1) * (z - 1)) := Real.exp_le_exp.mpr h2
    _ = ((k : ℝ) + 1) ^ (z - 1) := (Real.rpow_def_of_pos hk1pos _).symm
    _ ≤ (k : ℝ) ^ (z - 1) :=
        Real.rpow_le_rpow_of_nonpos hkpos (by linarith) (by linarith)

variable {p : ℕ} [Fact p.Prime]

private lemma weightedAvg_wz_nonneg (d : ℕ) {z : ℝ} (hz0 : 0 < z) (k : ℕ) :
    0 ≤ weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k := by
  unfold weightedAvg
  have hp : (0 : ℝ) ≤ (p : ℝ) ^ (-(k : ℤ)) := zpow_nonneg (p_real_pos p).le _
  exact mul_nonneg hp (Finset.sum_nonneg fun _ _ => pow_nonneg hz0.le _)

private lemma weightedB_wz_nonneg (d : ℕ) {z : ℝ} (hz0 : 0 < z) (j : ℕ) :
    0 ≤ weightedB p (fun f => z ^ omegaS (Sd p d) f) j := by
  unfold weightedB
  have hp : (0 : ℝ) ≤ (p : ℝ) ^ (-(j : ℤ)) := zpow_nonneg (p_real_pos p).le _
  refine mul_nonneg hp (Finset.sum_nonneg fun r _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg r) (Finset.sum_nonneg fun _ _ => pow_nonneg (pow_nonneg hz0.le _) _)

private lemma weightedB_wz_le_z {d j : ℕ} {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (hj1 : 1 ≤ j) (hjd : j ≤ d) :
    weightedB p (fun f => z ^ omegaS (Sd p d) f) j ≤ z := by
  have hB1 := weightedB_one (p := p) hj1
  calc
    weightedB p (fun f => z ^ omegaS (Sd p d) f) j
      ≤ z * weightedB p (fun _ => (1 : ℝ)) j := by
        unfold weightedB
        rw [← mul_assoc, mul_comm z, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (p_real_pos p).le _)
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun r hr => ?_
        rcases Nat.mem_divisors.mp hr with ⟨hrj, hj0⟩
        have hr_le_j : r ≤ j := Nat.le_of_dvd (by omega) hrj
        have hdiv_ge : 1 ≤ j / r :=
          Nat.div_pos hr_le_j (Nat.pos_of_dvd_of_pos hrj (by omega))
        rw [← mul_assoc, mul_comm z, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun P hP => ?_
        rcases mem_Irred_iff.mp hP with ⟨hPm, hPr, hPi⟩
        have hPSd : P ∈ Sd p d := mem_Sd_iff.mpr ⟨hPm, hPi, by omega⟩
        dsimp only
        rw [omegaS_irred _ hPm hPi, if_pos hPSd, pow_one, one_pow, mul_one]
        calc
          z ^ (j / r) ≤ z ^ 1 := pow_le_pow_of_le_one hz0.le hz1.le hdiv_ge
          _ = z := pow_one z
    _ = z := by rw [hB1, mul_one]

private lemma weightedB_wz_le_one {d j : ℕ} {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (hj1 : 1 ≤ j) :
    weightedB p (fun f => z ^ omegaS (Sd p d) f) j ≤ 1 := by
  have hB1 := weightedB_one (p := p) hj1
  rw [← hB1]
  unfold weightedB
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => ?_)
    (zpow_nonneg (p_real_pos p).le _)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun P _ => ?_)
    (Nat.cast_nonneg r)
  rw [one_pow]
  exact pow_le_one₀ (pow_nonneg hz0.le _) (pow_le_one₀ hz0.le hz1.le)

private lemma sum_Icc_sub_eq_sum_range (k : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ Finset.Icc 1 k, f (k - j) = ∑ i ∈ Finset.range k, f i := by
  refine Finset.sum_bij (fun j _ => k - j) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
    exact Finset.mem_range.mpr (by omega)
  · intro j₁ hj₁ j₂ hj₂ h
    rcases Finset.mem_Icc.mp hj₁ with ⟨_, hj₁k⟩
    rcases Finset.mem_Icc.mp hj₂ with ⟨_, hj₂k⟩
    omega
  · intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    exact ⟨k - i, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
  · intro _ _
    rfl

private lemma weightedAvg_wz_le_binomSeq {d : ℕ} {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    ∀ k : ℕ, k ≤ d → weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k ≤ binomSeq z k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkd
    by_cases hk0 : k = 0
    · subst hk0
      rw [weightedAvg_zero _ (by simp [omegaS_one]), binomSeq]
    · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
      have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
      have hrec := weightedAvg_recurrence (p := p) (w := fun f => z ^ omegaS (Sd p d) f)
        (by simp [omegaS_one])
        (fun f g hf hg => by rw [omegaS_mul _ hf.ne_zero hg.ne_zero, pow_add]) k
      have hmul : (k : ℝ) * weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k ≤
          (k : ℝ) * binomSeq z k := by
        rw [hrec, mul_binomSeq_eq, ← sum_Icc_sub_eq_sum_range k (binomSeq z), Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => ?_
        rcases Finset.mem_Icc.mp hj with ⟨hj1, hjk⟩
        have hB := weightedB_wz_le_z (p := p) (d := d) hz0 hz1 hj1 (hjk.trans hkd)
        have hih := ih (k - j) (by omega) (by omega)
        exact mul_le_mul hB hih (weightedAvg_wz_nonneg d hz0 _) hz0.le
      exact le_of_mul_le_mul_left hmul hkpos

private lemma weightedAvg_wz_le_of_ge {d : ℕ} {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) (hd : 1 ≤ d) :
    ∀ k : ℕ, d ≤ k →
      weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k ≤ binomSeq z d / z := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hdk
    have hk1 : 1 ≤ k := hd.trans hdk
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    let M0 : ℝ := binomSeq z d / z
    have hrec := weightedAvg_recurrence (p := p) (w := fun f => z ^ omegaS (Sd p d) f)
      (by simp [omegaS_one])
      (fun f g hf hg => by rw [omegaS_mul _ hf.ne_zero hg.ne_zero, pow_add]) k
    have hstep1 : (k : ℝ) * weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k ≤
        ∑ i ∈ Finset.range k, weightedAvg p (fun f => z ^ omegaS (Sd p d) f) i := by
      rw [hrec, ← sum_Icc_sub_eq_sum_range k]
      refine Finset.sum_le_sum fun j hj => ?_
      rcases Finset.mem_Icc.mp hj with ⟨hj1, _⟩
      have hB := weightedB_wz_le_one (p := p) (d := d) hz0 hz1 hj1
      have hu := weightedAvg_wz_nonneg (p := p) d hz0 (k - j)
      calc
        weightedB p (fun f => z ^ omegaS (Sd p d) f) j *
            weightedAvg p (fun f => z ^ omegaS (Sd p d) f) (k - j)
          ≤ 1 * weightedAvg p (fun f => z ^ omegaS (Sd p d) f) (k - j) :=
            mul_le_mul_of_nonneg_right hB hu
        _ = weightedAvg p (fun f => z ^ omegaS (Sd p d) f) (k - j) := one_mul _
    have hsplit : Finset.range k = Finset.range d ∪ Finset.Ico d k := by
      ext i
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range d) (Finset.Ico d k) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_range] at hi1
      rw [Finset.mem_Ico] at hi2
      omega
    have hsum_d : ∑ i ∈ Finset.range d, binomSeq z i = (d : ℝ) * M0 := by
      have h := mul_binomSeq_eq z d
      dsimp [M0]
      field_simp [hz0.ne']
      linarith
    have hmul : (k : ℝ) * weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k ≤ (k : ℝ) * M0 := by
      calc
        (k : ℝ) * weightedAvg p (fun f => z ^ omegaS (Sd p d) f) k
          ≤ ∑ i ∈ Finset.range k, weightedAvg p (fun f => z ^ omegaS (Sd p d) f) i := hstep1
        _ = (∑ i ∈ Finset.range d, weightedAvg p (fun f => z ^ omegaS (Sd p d) f) i) +
              (∑ i ∈ Finset.Ico d k, weightedAvg p (fun f => z ^ omegaS (Sd p d) f) i) := by
              rw [hsplit, Finset.sum_union hdisj]
        _ ≤ (∑ i ∈ Finset.range d, binomSeq z i) + ∑ _i ∈ Finset.Ico d k, M0 := by
              refine add_le_add ?_ ?_
              · refine Finset.sum_le_sum fun i hi => ?_
                exact weightedAvg_wz_le_binomSeq hz0 hz1 i (Nat.le_of_lt (Finset.mem_range.mp hi))
              · refine Finset.sum_le_sum fun i hi => ?_
                rcases Finset.mem_Ico.mp hi with ⟨hdi, hik⟩
                exact ih i hik hdi
        _ = (d : ℝ) * M0 + ((k - d : ℕ) : ℝ) * M0 := by
              rw [hsum_d, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ = (k : ℝ) * M0 := by
              rw [← add_mul, ← Nat.cast_add, Nat.add_sub_of_le hdk]
    exact le_of_mul_le_mul_left hmul hkpos

end Step2SubunitMoment

section Step3SuperunitMoment

variable {p : ℕ} [Fact p.Prime]

private noncomputable def eulerFactor (p : ℕ) (y : ℝ) (P : (ZMod p)[X]) : ℝ :=
  (1 - (p : ℝ) ^ (-(P.natDegree : ℤ))) / (1 - y * (p : ℝ) ^ (-(P.natDegree : ℤ)))

private lemma eulerFactor_pos {y : ℝ} (hy1 : 1 < y) (hy2 : y < 2)
    {P : (ZMod p)[X]} (hPi : Irreducible P) :
    0 < eulerFactor p y P := by
  have hr : 1 ≤ P.natDegree := pos_natDegree_of_irreducible hPi
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := p_real_ge_two p
  have hpr : (2 : ℝ) ≤ (p : ℝ) ^ P.natDegree := by
    calc
      (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ (p : ℝ) ^ 1 := pow_le_pow_left₀ (by norm_num) hp2 1
      _ ≤ (p : ℝ) ^ P.natDegree := pow_le_pow_right₀ (by linarith) hr
  have ha_pos : 0 < (p : ℝ) ^ (-(P.natDegree : ℤ)) := zpow_pos (p_real_pos p) _
  have ha_le : (p : ℝ) ^ (-(P.natDegree : ℤ)) ≤ 1 / 2 := by
    rw [zpow_neg, zpow_natCast, one_div]
    exact inv_anti₀ (by norm_num) hpr
  unfold eulerFactor
  have hnum : 0 < 1 - (p : ℝ) ^ (-(P.natDegree : ℤ)) := by linarith
  have hden : 0 < 1 - y * (p : ℝ) ^ (-(P.natDegree : ℤ)) := by nlinarith
  exact div_pos hnum hden

private lemma weightedAvg_insert_step {y : ℝ} (hy1 : 1 < y) (hy2 : y < 2)
    {P : (ZMod p)[X]} {S : Finset (ZMod p)[X]}
    (hPS : P ∉ S) (hPm : P.Monic) (hPi : Irreducible P)
    {MS : ℝ} (hMS_nonneg : 0 ≤ MS)
    (hS_bound : ∀ m : ℕ, weightedAvg p (fun f => y ^ omegaS S f) m ≤ MS)
    (k : ℕ) :
    weightedAvg p (fun f => y ^ omegaS (insert P S) f) k ≤ MS * eulerFactor p y P := by
  set r : ℕ := P.natDegree
  have hr1 : 1 ≤ r := pos_natDegree_of_irreducible hPi
  have hp_pos : (0 : ℝ) < (p : ℝ) := p_real_pos p
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := p_real_ge_two p
  set a : ℝ := (p : ℝ) ^ (-(r : ℤ))
  have ha_pos : 0 < a := zpow_pos hp_pos _
  have hpr : (2 : ℝ) ≤ (p : ℝ) ^ r := by
    calc
      (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ (p : ℝ) ^ 1 := pow_le_pow_left₀ (by norm_num) hp2 1
      _ ≤ (p : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr1
  have ha_le : a ≤ 1 / 2 := by
    dsimp [a]
    rw [zpow_neg, zpow_natCast, one_div]
    exact inv_anti₀ (by norm_num) hpr
  have hya_lt : y * a < 1 := by nlinarith
  have hya_nonneg : 0 ≤ y * a := by positivity
  let U : ℕ → ℝ := fun m => weightedAvg p (fun f => y ^ omegaS S f) m
  let G : ℕ → Finset (ZMod p)[X] := fun m => (M p m).filter (fun g => ¬ P ∣ g)
  let V : ℕ → ℝ := fun m => (p : ℝ) ^ (-(m : ℤ)) * ∑ g ∈ G m, y ^ omegaS S g
  have hV_lt : ∀ m : ℕ, m < r → V m = U m := by
    intro m hm
    have hGeq : G m = M p m := by
      refine Finset.filter_true_of_mem fun g hg hdvd => ?_
      have hgm : g.Monic := (mem_M_iff.mp hg).1
      have hgd : g.natDegree = m := (mem_M_iff.mp hg).2
      have hle : r ≤ m := by
        obtain ⟨q, rfl⟩ := hdvd
        have hqne : q ≠ 0 := right_ne_zero_of_mul hgm.ne_zero
        have hdeg := hgd
        rw [natDegree_mul hPm.ne_zero hqne] at hdeg
        omega
      omega
    simp [V, U, weightedAvg, hGeq]
  have hV_ge : ∀ m : ℕ, r ≤ m → V m = U m - a * U (m - r) := by
    intro m hm
    have hsplit : ∑ g ∈ M p m, y ^ omegaS S g =
        (∑ g ∈ G m, y ^ omegaS S g) +
          ∑ g ∈ (M p m).filter (fun g => P ∣ g), y ^ omegaS S g := by
      have := Finset.sum_filter_add_sum_filter_not (M p m) (fun g => P ∣ g)
        (fun g => y ^ omegaS S g)
      dsimp [G]
      linarith
    have hdvd_sum : ∑ g ∈ (M p m).filter (fun g => P ∣ g), y ^ omegaS S g =
        ∑ g' ∈ M p (m - r), y ^ omegaS S g' := by
      have hP_irred : P ∈ Irred p r := mem_Irred_iff.mpr ⟨hPm, rfl, hPi⟩
      have h1 := sum_filter_pow_dvd (p := p) (w := fun f => y ^ omegaS S f)
        (by simp [omegaS_one])
        (fun f g hf hg => by rw [omegaS_mul _ hf.ne_zero hg.ne_zero, pow_add])
        (e := 1) (k := m) hP_irred (by simpa using hm)
      have hwP : y ^ omegaS S P = 1 := by
        rw [omegaS_irred S hPm hPi, if_neg hPS, pow_zero]
      simpa [hwP] using h1
    have hG_sum : ∑ g ∈ G m, y ^ omegaS S g =
        (∑ g ∈ M p m, y ^ omegaS S g) - ∑ g' ∈ M p (m - r), y ^ omegaS S g' := by
      linarith
    have hexp : -(m : ℤ) = -(r : ℤ) + -((m - r : ℕ) : ℤ) := by omega
    dsimp [V, U, weightedAvg, a]
    rw [hG_sum, mul_sub]
    congr 1
    rw [hexp, zpow_add₀ hp_ne, mul_assoc]
  set N : ℕ := k / r
  have hdecomp : weightedAvg p (fun f => y ^ omegaS (insert P S) f) k =
      ∑ e ∈ Finset.range (N + 1), (y * a) ^ e * V (k - e * r) := by
    have hfib : ∑ f ∈ M p k, y ^ omegaS (insert P S) f =
        ∑ e ∈ Finset.range (N + 1),
          ∑ f ∈ (M p k).filter (fun f => (normalizedFactors f).count P = e),
            y ^ omegaS (insert P S) f := by
      symm
      refine Finset.sum_fiberwise_of_maps_to (g := fun f => (normalizedFactors f).count P) ?_ _
      intro f hf
      have hfm : f.Monic := (mem_M_iff.mp hf).1
      have hfd : f.natDegree = k := (mem_M_iff.mp hf).2
      have hle := count_mul_natDegree_le hPm hPi hfm
      rw [hfd] at hle
      have hdiv : (normalizedFactors f).count P ≤ N := (Nat.le_div_iff_mul_le (by omega)).mpr hle
      exact Finset.mem_range.mpr (by omega)
    have hterm : ∀ e ∈ Finset.range (N + 1),
        ∑ f ∈ (M p k).filter (fun f => (normalizedFactors f).count P = e),
          y ^ omegaS (insert P S) f =
        y ^ e * ∑ g ∈ G (k - e * r), y ^ omegaS S g := by
      intro e he
      have heN : e ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
      have her : e * r ≤ k := (Nat.le_div_iff_mul_le (by omega)).mp heN
      have hPeM : P ^ e ∈ M p (e * r) := pow_mem_M (mem_M_iff.mpr ⟨hPm, rfl⟩) e
      rw [Finset.mul_sum]
      symm
      refine Finset.sum_bij (fun g _ => P ^ e * g) ?_ ?_ ?_ ?_
      · intro g hg
        rcases Finset.mem_filter.mp hg with ⟨hgM, hndvd⟩
        have hgm : g.Monic := (mem_M_iff.mp hgM).1
        have hcnt_g : (normalizedFactors g).count P = 0 := by
          by_contra hne
          exact hndvd ((dvd_iff_pos_count hPm hPi hgm).mpr (Nat.pos_of_ne_zero hne))
        have hcnt_mul : (normalizedFactors (P ^ e * g)).count P = e := by
          rw [normalizedFactors_mul (hPm.pow e).ne_zero hgm.ne_zero,
            normalizedFactors_pow_of_monic_irred hPm hPi e,
            Multiset.count_add, Multiset.count_replicate_self, hcnt_g, add_zero]
        refine Finset.mem_filter.mpr ⟨?_, hcnt_mul⟩
        have hmul := mul_mem_M hPeM hgM
        rwa [Nat.add_sub_of_le her] at hmul
      · intro g₁ _ g₂ _ h
        exact mul_left_cancel₀ (hPm.pow e).ne_zero h
      · intro f hf
        rcases Finset.mem_filter.mp hf with ⟨hfM, hcnt⟩
        have hfm : f.Monic := (mem_M_iff.mp hfM).1
        have hdvd : P ^ e ∣ f := (pow_dvd_iff_le_count hPm hPi hfm e).mpr hcnt.ge
        obtain ⟨g, hgM, rfl⟩ := dvd_mem_M hfM hPeM hdvd
        have hgm : g.Monic := (mem_M_iff.mp hgM).1
        have hcnt_g : (normalizedFactors g).count P = 0 := by
          rw [normalizedFactors_mul (hPm.pow e).ne_zero hgm.ne_zero,
            normalizedFactors_pow_of_monic_irred hPm hPi e,
            Multiset.count_add, Multiset.count_replicate_self] at hcnt
          omega
        have hndvd : ¬ P ∣ g := by
          intro hdg
          have := (dvd_iff_pos_count hPm hPi hgm).mp hdg
          omega
        exact ⟨g, Finset.mem_filter.mpr ⟨hgM, hndvd⟩, rfl⟩
      · intro g hg
        rcases Finset.mem_filter.mp hg with ⟨hgM, hndvd⟩
        have hgm : g.Monic := (mem_M_iff.mp hgM).1
        have hcnt_g : (normalizedFactors g).count P = 0 := by
          by_contra hne
          exact hndvd ((dvd_iff_pos_count hPm hPi hgm).mpr (Nat.pos_of_ne_zero hne))
        have hcnt_mul : (normalizedFactors (P ^ e * g)).count P = e := by
          rw [normalizedFactors_mul (hPm.pow e).ne_zero hgm.ne_zero,
            normalizedFactors_pow_of_monic_irred hPm hPi e,
            Multiset.count_add, Multiset.count_replicate_self, hcnt_g, add_zero]
        have hOmP : omegaS S (P ^ e) = 0 := by
          rw [omegaS_pow S hPm.ne_zero e, omegaS_irred S hPm hPi, if_neg hPS, mul_zero]
        rw [omegaS_insert hPS, hcnt_mul, omegaS_mul S (hPm.pow e).ne_zero hgm.ne_zero,
          hOmP, zero_add, add_comm, pow_add]
    unfold weightedAvg
    rw [hfib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hterm e he]
    have heN : e ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp he)
    have her : e * r ≤ k := (Nat.le_div_iff_mul_le (by omega)).mp heN
    have hexp : -(k : ℤ) = -((e * r : ℕ) : ℤ) + -((k - e * r : ℕ) : ℤ) := by omega
    have hapow : a ^ e = (p : ℝ) ^ (-((e * r : ℕ) : ℤ)) := by
      dsimp [a]
      rw [← zpow_natCast ((p : ℝ) ^ (-(r : ℤ))) e, ← zpow_mul]
      congr 1
      ring
    dsimp [V]
    rw [hexp, zpow_add₀ hp_ne, ← hapow, mul_pow]
    ring
  have htelescope : weightedAvg p (fun f => y ^ omegaS (insert P S) f) k =
      U k + ∑ e ∈ Finset.range N, (y - 1) * a * (y * a) ^ e * U (k - (e + 1) * r) := by
    rw [hdecomp, Finset.sum_range_succ]
    have hVlast : V (k - N * r) = U (k - N * r) := by
      refine hV_lt (k - N * r) ?_
      have hmod : k - N * r = k % r := by
        have h := Nat.div_add_mod k r
        dsimp [N]
        rw [mul_comm (k / r) r]
        omega
      rw [hmod]
      exact Nat.mod_lt k (by omega)
    have hsum_mid : ∑ e ∈ Finset.range N, (y * a) ^ e * V (k - e * r) =
        (∑ e ∈ Finset.range N, (y * a) ^ e * U (k - e * r)) -
          ∑ e ∈ Finset.range N, (y * a) ^ e * a * U (k - (e + 1) * r) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun e he => ?_
      have heN : e < N := Finset.mem_range.mp he
      have hge : r ≤ k - e * r := by
        have h1 : (e + 1) * r ≤ N * r := Nat.mul_le_mul_right r (by omega)
        have h2 : N * r ≤ k := Nat.div_mul_le_self k r
        have h3 : (e + 1) * r = e * r + r := by ring
        omega
      rw [hV_ge (k - e * r) hge]
      have hsub : k - e * r - r = k - (e + 1) * r := by
        have h3 : (e + 1) * r = e * r + r := by ring
        omega
      rw [hsub]
      ring
    rw [hVlast, hsum_mid]
    have hshift :
        (∑ e ∈ Finset.range N, (y * a) ^ e * U (k - e * r)) + (y * a) ^ N * U (k - N * r) =
        U k + ∑ e ∈ Finset.range N, (y * a) ^ (e + 1) * U (k - (e + 1) * r) := by
      rw [← Finset.sum_range_succ (f := fun e => (y * a) ^ e * U (k - e * r)) N,
        Finset.sum_range_succ']
      simp [add_comm]
    have hcomb :
        (U k + ∑ e ∈ Finset.range N, (y * a) ^ (e + 1) * U (k - (e + 1) * r)) -
          ∑ e ∈ Finset.range N, (y * a) ^ e * a * U (k - (e + 1) * r) =
        U k + ∑ e ∈ Finset.range N, (y - 1) * a * (y * a) ^ e * U (k - (e + 1) * r) := by
      rw [add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [pow_succ]
      ring
    linarith
  have hgeom' : ∑ e ∈ Finset.range N, (y * a) ^ e ≤ 1 / (1 - y * a) := by
    have h1 : 0 < 1 - y * a := by linarith
    rw [le_div_iff₀ h1]
    have hmul : (∑ e ∈ Finset.range N, (y * a) ^ e) * (1 - y * a) = 1 - (y * a) ^ N := by
      have hg := geom_sum_eq hya_lt.ne N
      rw [hg]
      have hne : y * a - 1 ≠ 0 := by linarith
      field_simp [hne]
      ring
    rw [hmul]
    have hpow : 0 ≤ (y * a) ^ N := pow_nonneg hya_nonneg N
    linarith
  have hbound1 : weightedAvg p (fun f => y ^ omegaS (insert P S) f) k ≤
      MS * (1 + (y - 1) * a * ∑ e ∈ Finset.range N, (y * a) ^ e) := by
    rw [htelescope, mul_add, mul_one]
    have hsum_le :
        ∑ e ∈ Finset.range N, (y - 1) * a * (y * a) ^ e * U (k - (e + 1) * r) ≤
        MS * ((y - 1) * a * ∑ e ∈ Finset.range N, (y * a) ^ e) := by
      calc
        ∑ e ∈ Finset.range N, (y - 1) * a * (y * a) ^ e * U (k - (e + 1) * r)
          ≤ ∑ e ∈ Finset.range N, (y - 1) * a * (y * a) ^ e * MS := by
              refine Finset.sum_le_sum fun e _ => ?_
              have hcoef : 0 ≤ (y - 1) * a * (y * a) ^ e := by positivity
              exact mul_le_mul_of_nonneg_left (hS_bound _) hcoef
        _ = MS * ((y - 1) * a * ∑ e ∈ Finset.range N, (y * a) ^ e) := by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun e _ => by ring
    linarith [hS_bound k, hsum_le]
  have hfactor : 1 + (y - 1) * a * ∑ e ∈ Finset.range N, (y * a) ^ e ≤ eulerFactor p y P := by
    have h1 : 0 < 1 - y * a := by linarith
    have hstep : 1 + (y - 1) * a * ∑ e ∈ Finset.range N, (y * a) ^ e ≤
        1 + (y - 1) * a * (1 / (1 - y * a)) := by
      have hc : 0 ≤ (y - 1) * a := mul_nonneg (by linarith) ha_pos.le
      linarith [mul_le_mul_of_nonneg_left hgeom' hc]
    have heq : 1 + (y - 1) * a * (1 / (1 - y * a)) = eulerFactor p y P := by
      unfold eulerFactor
      have h1' : 1 - y * (p : ℝ) ^ (-(P.natDegree : ℤ)) ≠ 0 := h1.ne'
      dsimp [a, r]
      field_simp [h1']
      ring
    linarith
  exact hbound1.trans (mul_le_mul_of_nonneg_left hfactor hMS_nonneg)

private lemma weightedAvg_le_prod_eulerFactor {y : ℝ} (hy1 : 1 < y) (hy2 : y < 2)
    (S : Finset (ZMod p)[X]) (hS : ∀ P ∈ S, P.Monic ∧ Irreducible P) :
    ∀ k : ℕ, weightedAvg p (fun f => y ^ omegaS S f) k ≤ ∏ P ∈ S, eulerFactor p y P := by
  induction S using Finset.induction_on with
  | empty =>
    intro k
    simpa [omegaS_empty] using (weightedAvg_one (p := p) k).le
  | insert P S hPS ih =>
    intro k
    have hPm : P.Monic := (hS P (Finset.mem_insert_self P S)).1
    have hPi : Irreducible P := (hS P (Finset.mem_insert_self P S)).2
    have hS' : ∀ Q ∈ S, Q.Monic ∧ Irreducible Q := fun Q hQ =>
      hS Q (Finset.mem_insert_of_mem hQ)
    have hprod_nonneg : 0 ≤ ∏ Q ∈ S, eulerFactor p y Q :=
      Finset.prod_nonneg fun Q hQ => (eulerFactor_pos hy1 hy2 (hS' Q hQ).2).le
    rw [Finset.prod_insert hPS, mul_comm]
    exact weightedAvg_insert_step hy1 hy2 hPS hPm hPi hprod_nonneg (ih hS') k

private lemma harmonic_Icc_two_le_log {d : ℕ} (hd : 1 ≤ d) :
    ∑ r ∈ Finset.Icc 2 d, (1 : ℝ) / (r : ℝ) ≤ Real.log (d : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hd
  induction m with
  | zero => simp
  | succ m ih =>
    have hIcc : Finset.Icc 2 (m + 1 + 1) = insert (m + 2) (Finset.Icc 2 (m + 1)) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnotmem : m + 2 ∉ Finset.Icc 2 (m + 1) := by simp
    rw [hIcc, Finset.sum_insert hnotmem]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hstep : (1 : ℝ) / ((m : ℝ) + 2) ≤ Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) := by
      have hlog := Real.log_le_sub_one_of_pos (div_pos hm1 hm2)
      rw [Real.log_div hm1.ne' hm2.ne'] at hlog
      have hdiv : ((m : ℝ) + 1) / ((m : ℝ) + 2) - 1 = -(1 / ((m : ℝ) + 2)) := by
        field_simp [hm2.ne']
        ring
      linarith
    have ih' : ∑ r ∈ Finset.Icc 2 (m + 1), (1 : ℝ) / (r : ℝ) ≤ Real.log ((m : ℝ) + 1) := by
      simpa [Nat.cast_add, Nat.cast_one] using ih
    have hcast1 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    rw [hcast1]
    linarith

private lemma geom_half_Icc_two_le (d : ℕ) :
    ∑ r ∈ Finset.Icc 2 d, ((1 / 2 : ℝ) ^ r) ≤ 2 := by
  have hsub : Finset.Icc 2 d ⊆ Finset.range (d + 1) := by
    intro r hr
    rcases Finset.mem_Icc.mp hr with ⟨_, hrd⟩
    exact Finset.mem_range.mpr (by omega)
  have hle : ∑ r ∈ Finset.Icc 2 d, ((1 / 2 : ℝ) ^ r) ≤
      ∑ r ∈ Finset.range (d + 1), ((1 / 2 : ℝ) ^ r) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have hgeom : ∑ r ∈ Finset.range (d + 1), ((1 / 2 : ℝ) ^ r) = 2 * (1 - (1 / 2 : ℝ) ^ (d + 1)) := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    ring
  have hpow : 0 ≤ (1 / 2 : ℝ) ^ (d + 1) := by positivity
  linarith

private lemma prod_eulerFactor_Sd_le {d : ℕ} (hd : 1 ≤ d) :
    ∏ P ∈ Sd p d, eulerFactor p (3 / 2) P ≤ (4 : ℝ) ^ p * Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := p_real_pos p
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := p_real_ge_two p
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hprod_biUnion :
      ∏ P ∈ Sd p d, eulerFactor p (3 / 2) P =
        ∏ r ∈ Finset.Icc 1 d,
          ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
            (Irred p r).card := by
    rw [Sd, Finset.prod_biUnion]
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl fun P hP => ?_
      unfold eulerFactor
      rw [(mem_Irred_iff.mp hP).2.1]
    · intro r₁ _ r₂ _ hne
      exact pairwiseDisjoint_Irred p (Set.mem_univ r₁) (Set.mem_univ r₂) hne
  have hIcc_split : Finset.Icc 1 d = insert 1 (Finset.Icc 2 d) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1_notmem : 1 ∉ Finset.Icc 2 d := by simp
  rw [hprod_biUnion, hIcc_split, Finset.prod_insert h1_notmem]
  have h1_bound :
      ((1 - (p : ℝ) ^ (-(1 : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 : ℤ)))) ^
        (Irred p 1).card ≤ (4 : ℝ) ^ p := by
    set a1 : ℝ := (p : ℝ) ^ (-(1 : ℤ))
    have ha1_pos : 0 < a1 := zpow_pos hp_pos _
    have ha1_le : a1 ≤ 1 / 2 := by
      dsimp [a1]
      rw [zpow_neg, zpow_one, one_div]
      exact inv_anti₀ (by norm_num) hp2
    have hden_ge : 1 / 4 ≤ 1 - (3 / 2 : ℝ) * a1 := by linarith
    have hnum_nonneg : 0 ≤ 1 - a1 := by linarith
    have hfrac_le : (1 - a1) / (1 - (3 / 2 : ℝ) * a1) ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hcard_le : (Irred p 1).card ≤ p := by
      have h := card_Irred_mul_le (p := p) (r := 1) le_rfl
      simp only [Nat.cast_one, one_mul, pow_one] at h
      exact_mod_cast h
    calc
      ((1 - a1) / (1 - (3 / 2 : ℝ) * a1)) ^ (Irred p 1).card
        ≤ (4 : ℝ) ^ (Irred p 1).card :=
          pow_le_pow_left₀ (div_nonneg hnum_nonneg (by linarith)) hfrac_le _
      _ ≤ (4 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) hcard_le
  have htail_bound :
      ∏ r ∈ Finset.Icc 2 d,
        ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
          (Irred p r).card ≤ Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by
    have hterm_le : ∀ r ∈ Finset.Icc 2 d,
        ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
          (Irred p r).card ≤
        Real.exp (((Irred p r).card : ℝ) *
          ((1 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)) + 2 * ((p : ℝ) ^ (-(r : ℤ))) ^ 2)) := by
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      set ar : ℝ := (p : ℝ) ^ (-(r : ℤ))
      have har_pos : 0 < ar := zpow_pos hp_pos _
      have hpr4 : (4 : ℝ) ≤ (p : ℝ) ^ r := by
        calc
          (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hp2 2
          _ ≤ (p : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr2
      have har_le : ar ≤ 1 / 4 := by
        dsimp [ar]
        rw [zpow_neg, zpow_natCast]
        have : (4 : ℝ)⁻¹ = (1 / 4 : ℝ) := by norm_num
        rw [← this]
        exact inv_anti₀ (by norm_num) hpr4
      have hden_pos : 0 < 1 - (3 / 2 : ℝ) * ar := by linarith
      have hnum_nonneg : 0 ≤ 1 - ar := by linarith
      have hpoly : (1 - ar) / (1 - (3 / 2 : ℝ) * ar) ≤ 1 + (1 / 2 : ℝ) * ar + 2 * ar ^ 2 := by
        rw [div_le_iff₀ hden_pos]
        have hsq : 0 ≤ ar ^ 2 * (5 / 4 - 3 * ar) :=
          mul_nonneg (sq_nonneg ar) (by linarith)
        linarith
      have hexp1 : (1 - ar) / (1 - (3 / 2 : ℝ) * ar) ≤
          Real.exp ((1 / 2 : ℝ) * ar + 2 * ar ^ 2) := by
        have hadd := Real.add_one_le_exp ((1 / 2 : ℝ) * ar + 2 * ar ^ 2)
        linarith
      calc
        ((1 - ar) / (1 - (3 / 2 : ℝ) * ar)) ^ (Irred p r).card
          ≤ (Real.exp ((1 / 2 : ℝ) * ar + 2 * ar ^ 2)) ^ (Irred p r).card :=
            pow_le_pow_left₀ (div_nonneg hnum_nonneg hden_pos.le) hexp1 _
        _ = Real.exp (((Irred p r).card : ℝ) * ((1 / 2 : ℝ) * ar + 2 * ar ^ 2)) :=
            (Real.exp_nat_mul _ _).symm
    have hprod_le :
        ∏ r ∈ Finset.Icc 2 d,
          ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
            (Irred p r).card ≤
        Real.exp (∑ r ∈ Finset.Icc 2 d,
          ((Irred p r).card : ℝ) *
            ((1 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)) + 2 * ((p : ℝ) ^ (-(r : ℤ))) ^ 2)) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod (fun r hr => ?_) hterm_le
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpr4 : (4 : ℝ) ≤ (p : ℝ) ^ r := by
        calc
          (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hp2 2
          _ ≤ (p : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr2
      have har_le : (p : ℝ) ^ (-(r : ℤ)) ≤ 1 / 4 := by
        rw [zpow_neg, zpow_natCast]
        have : (4 : ℝ)⁻¹ = (1 / 4 : ℝ) := by norm_num
        rw [← this]
        exact inv_anti₀ (by norm_num) hpr4
      exact pow_nonneg (div_nonneg (by linarith) (by linarith)) _
    have hexp_bound :
        ∑ r ∈ Finset.Icc 2 d,
          ((Irred p r).card : ℝ) *
            ((1 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)) + 2 * ((p : ℝ) ^ (-(r : ℤ))) ^ 2) ≤
        4 + (1 / 2 : ℝ) * Real.log (d : ℝ) := by
      have hsplit_sum :
          ∑ r ∈ Finset.Icc 2 d,
            ((Irred p r).card : ℝ) *
              ((1 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)) + 2 * ((p : ℝ) ^ (-(r : ℤ))) ^ 2) ≤
          (1 / 2 : ℝ) * (∑ r ∈ Finset.Icc 2 d, (1 : ℝ) / (r : ℝ)) +
            2 * ∑ r ∈ Finset.Icc 2 d, ((1 / 2 : ℝ) ^ r) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun r hr => ?_
        have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
        have hr1 : 1 ≤ r := by omega
        have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
        have hpr_pos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos hp_pos r
        have hcard := card_Irred_le (p := p) hr1
        have h1 : ((Irred p r).card : ℝ) * (p : ℝ) ^ (-(r : ℤ)) ≤ 1 / (r : ℝ) := by
          rw [zpow_neg, zpow_natCast]
          calc
            ((Irred p r).card : ℝ) * ((p : ℝ) ^ r)⁻¹
              ≤ ((p : ℝ) ^ r / (r : ℝ)) * ((p : ℝ) ^ r)⁻¹ :=
                mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hpr_pos.le)
            _ = 1 / (r : ℝ) := by field_simp [hpr_pos.ne', hrpos.ne']
        have har_half : (p : ℝ) ^ (-(r : ℤ)) ≤ (1 / 2 : ℝ) ^ r := by
          rw [zpow_neg, zpow_natCast, one_div, inv_pow]
          exact inv_anti₀ (pow_pos (by norm_num) r) (pow_le_pow_left₀ (by norm_num) hp2 r)
        have h2 : ((Irred p r).card : ℝ) * ((p : ℝ) ^ (-(r : ℤ))) ^ 2 ≤ (1 / 2 : ℝ) ^ r := by
          have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
          have hinv_le1 : 1 / (r : ℝ) ≤ 1 := by
            rw [div_le_one hrpos]
            exact hr_ge1
          calc
            ((Irred p r).card : ℝ) * ((p : ℝ) ^ (-(r : ℤ))) ^ 2
              = (((Irred p r).card : ℝ) * (p : ℝ) ^ (-(r : ℤ))) * (p : ℝ) ^ (-(r : ℤ)) := by ring
            _ ≤ (1 / (r : ℝ)) * (1 / 2 : ℝ) ^ r :=
                mul_le_mul h1 har_half (zpow_nonneg hp_pos.le _) (by positivity)
            _ ≤ 1 * (1 / 2 : ℝ) ^ r :=
                mul_le_mul_of_nonneg_right hinv_le1 (by positivity)
            _ = (1 / 2 : ℝ) ^ r := one_mul _
        linarith
      linarith [hsplit_sum, harmonic_Icc_two_le_log hd, geom_half_Icc_two_le d]
    calc
      ∏ r ∈ Finset.Icc 2 d,
          ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
            (Irred p r).card
        ≤ Real.exp (∑ r ∈ Finset.Icc 2 d,
            ((Irred p r).card : ℝ) *
              ((1 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)) + 2 * ((p : ℝ) ^ (-(r : ℤ))) ^ 2)) := hprod_le
      _ ≤ Real.exp (4 + (1 / 2 : ℝ) * Real.log (d : ℝ)) := Real.exp_le_exp.mpr hexp_bound
      _ = Real.exp 4 * Real.exp (Real.log (d : ℝ) * (1 / 2 : ℝ)) := by
            rw [Real.exp_add, mul_comm (1 / 2 : ℝ)]
      _ = Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_def_of_pos hd_pos]
  have htail_nonneg : 0 ≤ ∏ r ∈ Finset.Icc 2 d,
      ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
        (Irred p r).card := by
    refine Finset.prod_nonneg fun r hr => ?_
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    have hpr4 : (4 : ℝ) ≤ (p : ℝ) ^ r := by
      calc
        (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (p : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hp2 2
        _ ≤ (p : ℝ) ^ r := pow_le_pow_right₀ (by linarith) hr2
    have har_le : (p : ℝ) ^ (-(r : ℤ)) ≤ 1 / 4 := by
      rw [zpow_neg, zpow_natCast]
      have : (4 : ℝ)⁻¹ = (1 / 4 : ℝ) := by norm_num
      rw [← this]
      exact inv_anti₀ (by norm_num) hpr4
    exact pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  calc
    ((1 - (p : ℝ) ^ (-(1 : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(1 : ℤ)))) ^ (Irred p 1).card *
        ∏ r ∈ Finset.Icc 2 d,
          ((1 - (p : ℝ) ^ (-(r : ℤ))) / (1 - (3 / 2 : ℝ) * (p : ℝ) ^ (-(r : ℤ)))) ^
            (Irred p r).card
      ≤ (4 : ℝ) ^ p * (Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ)) :=
        mul_le_mul h1_bound htail_bound htail_nonneg (by positivity)
    _ = (4 : ℝ) ^ p * Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by ring

private lemma weightedAvg_three_halves_Sd_le {d : ℕ} (hd : 1 ≤ d) (k : ℕ) :
    weightedAvg p (fun f => (3 / 2 : ℝ) ^ omegaS (Sd p d) f) k ≤
      (4 : ℝ) ^ p * Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ) := by
  have hS : ∀ P ∈ Sd p d, P.Monic ∧ Irreducible P := fun P hP => by
    rcases mem_Sd_iff.mp hP with ⟨hPm, hPi, _⟩
    exact ⟨hPm, hPi⟩
  exact (weightedAvg_le_prod_eulerFactor (p := p) (y := 3 / 2) (by norm_num) (by norm_num)
    (Sd p d) hS k).trans (prod_eulerFactor_Sd_le hd)

end Step3SuperunitMoment

section Step4Assembly

private lemma two_fifths_le_log_three_halves : (2 / 5 : ℝ) ≤ Real.log (3 / 2) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have hexp1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hexp2 : Real.exp 2 ≤ (3 / 2 : ℝ) ^ (5 : ℕ) := by
    have h2 : Real.exp 2 = (Real.exp 1) ^ (2 : ℕ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h2]
    have hpos : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have hsq : (Real.exp 1) ^ (2 : ℕ) ≤ (2.7182818286 : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hpos hexp1.le 2
    linarith [hsq, show (2.7182818286 : ℝ) ^ (2 : ℕ) ≤ (3 / 2 : ℝ) ^ (5 : ℕ) by norm_num]
  have hpow5 : (Real.exp (2 / 5 : ℝ)) ^ (5 : ℕ) ≤ (3 / 2 : ℝ) ^ (5 : ℕ) := by
    rw [← Real.exp_nat_mul]
    have h5 : (5 : ℕ) * (2 / 5 : ℝ) = 2 := by norm_num
    rw [h5]
    exact hexp2
  exact le_of_pow_le_pow_left₀ (by norm_num : 5 ≠ 0) (by norm_num : (0 : ℝ) ≤ 3 / 2) hpow5

private lemma log_four_thirds_le : Real.log (4 / 3) ≤ 29 / 100 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have hsum := Real.sum_le_exp_of_nonneg (x := (29 / 100 : ℝ)) (by norm_num) 4
  have hnum : (4 / 3 : ℝ) ≤
      ∑ i ∈ Finset.range 4, (29 / 100 : ℝ) ^ i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  exact hnum.trans hsum

private lemma main_bound (p : ℕ) [Fact p.Prime] (n d : ℕ) (hd : 1 ≤ d) (h2d : 2 * d ≤ n) :
    (((Finset.univ : Finset (Fin n → ZMod p)).filter fun b =>
      ∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree = d ∧
        g ∣ (X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ))).card : ℝ) ≤
      ((4 : ℝ) ^ p * Real.exp 4 + 4 / 3) * (d : ℝ) ^ (-(1 / 20 : ℝ)) * (p : ℝ) ^ n := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := p_real_pos p
  have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos hp_pos n
  have hd_ge1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd_pos : (0 : ℝ) < (d : ℝ) := by linarith
  have hlogd_nonneg : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd_ge1
  let Bad : Finset (ZMod p)[X] := (M p n).filter fun f => ∃ g ∈ M p d, g ∣ f
  have hcard_eq :
      ((Finset.univ : Finset (Fin n → ZMod p)).filter fun b =>
        ∃ g : (ZMod p)[X], g.Monic ∧ g.natDegree = d ∧
          g ∣ (X ^ n + ∑ i : Fin n, C (b i) * X ^ (i : ℕ))).card = Bad.card := by
    refine Finset.card_bij (fun b _ => monicPoly p n b) ?_ ?_ ?_
    · intro b hb
      rcases (Finset.mem_filter.mp hb).2 with ⟨g, hgm, hgd, hdvd⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩, ?_⟩
      exact ⟨g, mem_M_iff.mpr ⟨hgm, hgd⟩, hdvd⟩
    · intro b₁ _ b₂ _ h
      exact monicPoly_injective n h
    · intro f hf
      rcases Finset.mem_filter.mp hf with ⟨hfM, g, hgM, hdvd⟩
      rcases Finset.mem_image.mp hfM with ⟨b, _, rfl⟩
      rcases mem_M_iff.mp hgM with ⟨hgm, hgd⟩
      exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨g, hgm, hgd, hdvd⟩⟩, rfl⟩
  rw [hcard_eq]
  set k : ℕ := Nat.floor ((3 / 2 : ℝ) * Real.log (d : ℝ))
  have hk_le : (k : ℝ) ≤ (3 / 2 : ℝ) * Real.log (d : ℝ) :=
    Nat.floor_le (by positivity)
  have hk_gt : (3 / 2 : ℝ) * Real.log (d : ℝ) < (k : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  let Bad1 : Finset (ZMod p)[X] := Bad.filter fun f => k < omegaS (Sd p d) f
  let Bad2 : Finset (ZMod p)[X] := Bad.filter fun f => omegaS (Sd p d) f ≤ k
  have hBad_split : Bad.card = Bad1.card + Bad2.card := by
    have hunion : Bad = Bad1 ∪ Bad2 := by
      ext f
      simp only [Bad1, Bad2, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hf
        by_cases h : k < omegaS (Sd p d) f
        · exact Or.inl ⟨hf, h⟩
        · exact Or.inr ⟨hf, by omega⟩
      · rintro (⟨hf, _⟩ | ⟨hf, _⟩) <;> exact hf
    have hdisj : Disjoint Bad1 Bad2 := by
      rw [Finset.disjoint_left]
      intro f hf1 hf2
      have h1 := (Finset.mem_filter.mp hf1).2
      have h2 := (Finset.mem_filter.mp hf2).2
      omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
  -- Case 1: Bad1 (omega_d f > k)
  have hBad1 : (Bad1.card : ℝ) / (p : ℝ) ^ n ≤
      (4 : ℝ) ^ p * Real.exp 4 * (d : ℝ) ^ (-(1 / 20 : ℝ)) := by
    have hy_pos : (0 : ℝ) < (3 / 2 : ℝ) := by norm_num
    have hy_ge1 : (1 : ℝ) ≤ (3 / 2 : ℝ) := by norm_num
    have hpow_pos : (0 : ℝ) < (3 / 2 : ℝ) ^ (k + 1) := pow_pos hy_pos (k + 1)
    have hsum1 : (3 / 2 : ℝ) ^ (k + 1) * (Bad1.card : ℝ) ≤
        ∑ f ∈ M p n, (3 / 2 : ℝ) ^ omegaS (Sd p d) f := by
      calc
        (3 / 2 : ℝ) ^ (k + 1) * (Bad1.card : ℝ)
          = ∑ _f ∈ Bad1, (3 / 2 : ℝ) ^ (k + 1) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ f ∈ Bad1, (3 / 2 : ℝ) ^ omegaS (Sd p d) f := by
              refine Finset.sum_le_sum fun f hf => ?_
              have hlt : k < omegaS (Sd p d) f := (Finset.mem_filter.mp hf).2
              exact pow_le_pow_right₀ hy_ge1 hlt
        _ ≤ ∑ f ∈ M p n, (3 / 2 : ℝ) ^ omegaS (Sd p d) f := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
              intro f hf
              exact (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
    have hdiv1 : (Bad1.card : ℝ) / (p : ℝ) ^ n ≤
        ((3 / 2 : ℝ) ^ (k + 1))⁻¹ * weightedAvg p (fun f => (3 / 2 : ℝ) ^ omegaS (Sd p d) f) n := by
      unfold weightedAvg
      rw [zpow_neg, zpow_natCast, div_eq_inv_mul]
      have h1 : (Bad1.card : ℝ) ≤
          ((3 / 2 : ℝ) ^ (k + 1))⁻¹ * ∑ f ∈ M p n, (3 / 2 : ℝ) ^ omegaS (Sd p d) f := by
        rw [← div_eq_inv_mul, le_div_iff₀ hpow_pos, mul_comm]
        exact hsum1
      calc
        ((p : ℝ) ^ n)⁻¹ * (Bad1.card : ℝ)
          ≤ ((p : ℝ) ^ n)⁻¹ *
              (((3 / 2 : ℝ) ^ (k + 1))⁻¹ * ∑ f ∈ M p n, (3 / 2 : ℝ) ^ omegaS (Sd p d) f) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpn_pos.le)
        _ = ((3 / 2 : ℝ) ^ (k + 1))⁻¹ *
              (((p : ℝ) ^ n)⁻¹ * ∑ f ∈ M p n, (3 / 2 : ℝ) ^ omegaS (Sd p d) f) := by ring
    have hinv_le : ((3 / 2 : ℝ) ^ (k + 1))⁻¹ ≤ (d : ℝ) ^ (-(3 / 2 : ℝ) * Real.log (3 / 2)) := by
      have hlog_pos : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
      have hpow_ge : (d : ℝ) ^ ((3 / 2 : ℝ) * Real.log (3 / 2)) ≤ (3 / 2 : ℝ) ^ (k + 1) := by
        rw [Real.rpow_def_of_pos hd_pos]
        have hcast : ((3 / 2 : ℝ) ^ (k + 1)) = Real.exp (Real.log (3 / 2) * ((k : ℝ) + 1)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hy_pos]
          push_cast
          rfl
        rw [hcast]
        refine Real.exp_le_exp.mpr ?_
        have hmul : Real.log (3 / 2) * ((3 / 2 : ℝ) * Real.log (d : ℝ)) ≤
            Real.log (3 / 2) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hk_gt.le hlog_pos.le
        linarith
      have hinv := inv_anti₀ (Real.rpow_pos_of_pos hd_pos _) hpow_ge
      rwa [← Real.rpow_neg hd_pos.le, show -((3 / 2 : ℝ) * Real.log (3 / 2)) =
        -(3 / 2 : ℝ) * Real.log (3 / 2) by ring] at hinv
    have hU := weightedAvg_three_halves_Sd_le (p := p) hd n
    have hU_nonneg : 0 ≤ weightedAvg p (fun f => (3 / 2 : ℝ) ^ omegaS (Sd p d) f) n := by
      unfold weightedAvg
      exact mul_nonneg (zpow_nonneg hp_pos.le _) (Finset.sum_nonneg fun _ _ => by positivity)
    have hexp1 : (1 / 2 : ℝ) - (3 / 2 : ℝ) * Real.log (3 / 2) ≤ -(1 / 20 : ℝ) := by
      linarith [two_fifths_le_log_three_halves]
    calc
      (Bad1.card : ℝ) / (p : ℝ) ^ n
        ≤ ((3 / 2 : ℝ) ^ (k + 1))⁻¹ *
            weightedAvg p (fun f => (3 / 2 : ℝ) ^ omegaS (Sd p d) f) n := hdiv1
      _ ≤ (d : ℝ) ^ (-(3 / 2 : ℝ) * Real.log (3 / 2)) *
            ((4 : ℝ) ^ p * Real.exp 4 * (d : ℝ) ^ (1 / 2 : ℝ)) :=
          mul_le_mul hinv_le hU hU_nonneg (Real.rpow_pos_of_pos hd_pos _).le
      _ = (4 : ℝ) ^ p * Real.exp 4 *
            ((d : ℝ) ^ (1 / 2 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ) * Real.log (3 / 2))) := by ring
      _ = (4 : ℝ) ^ p * Real.exp 4 *
            (d : ℝ) ^ ((1 / 2 : ℝ) - (3 / 2 : ℝ) * Real.log (3 / 2)) := by
          rw [← Real.rpow_add hd_pos]
          congr 2
          ring
      _ ≤ (4 : ℝ) ^ p * Real.exp 4 * (d : ℝ) ^ (-(1 / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hd_ge1 hexp1) (by positivity)
  -- Case 2: Bad2 (omega_d f <= k)
  have hBad2 : (Bad2.card : ℝ) / (p : ℝ) ^ n ≤ (4 / 3 : ℝ) * (d : ℝ) ^ (-(1 / 20 : ℝ)) := by
    let Pairs : Finset ((ZMod p)[X] × (ZMod p)[X]) :=
      ((M p d) ×ˢ (M p (n - d))).filter fun gh =>
        omegaS (Sd p d) gh.1 + omegaS (Sd p d) gh.2 ≤ k
    have hBad2_sub : Bad2 ⊆ Pairs.image (fun gh => gh.1 * gh.2) := by
      intro f hf
      rcases Finset.mem_filter.mp hf with ⟨hfBad, hfOm⟩
      rcases Finset.mem_filter.mp hfBad with ⟨hfM, g, hgM, hdvd⟩
      obtain ⟨h, hhM, rfl⟩ := dvd_mem_M hfM hgM hdvd
      have hgm : g.Monic := (mem_M_iff.mp hgM).1
      have hhm : h.Monic := (mem_M_iff.mp hhM).1
      rw [omegaS_mul _ hgm.ne_zero hhm.ne_zero] at hfOm
      refine Finset.mem_image.mpr ⟨(g, h), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hgM, hhM⟩, hfOm⟩
    have hcard_le : (Bad2.card : ℝ) ≤ (Pairs.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hBad2_sub).trans Finset.card_image_le
    have hz_pos : (0 : ℝ) < (3 / 4 : ℝ) := by norm_num
    have hz_lt1 : (3 / 4 : ℝ) < 1 := by norm_num
    have hzk_pos : (0 : ℝ) < (3 / 4 : ℝ) ^ k := pow_pos hz_pos k
    have hsum2 : (3 / 4 : ℝ) ^ k * (Pairs.card : ℝ) ≤
        (∑ g ∈ M p d, (3 / 4 : ℝ) ^ omegaS (Sd p d) g) *
          (∑ h ∈ M p (n - d), (3 / 4 : ℝ) ^ omegaS (Sd p d) h) := by
      calc
        (3 / 4 : ℝ) ^ k * (Pairs.card : ℝ)
          = ∑ _gh ∈ Pairs, (3 / 4 : ℝ) ^ k := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ gh ∈ Pairs,
              (3 / 4 : ℝ) ^ omegaS (Sd p d) gh.1 * (3 / 4 : ℝ) ^ omegaS (Sd p d) gh.2 := by
              refine Finset.sum_le_sum fun gh hgh => ?_
              have hle : omegaS (Sd p d) gh.1 + omegaS (Sd p d) gh.2 ≤ k :=
                (Finset.mem_filter.mp hgh).2
              rw [← pow_add]
              exact pow_le_pow_of_le_one hz_pos.le hz_lt1.le hle
        _ ≤ ∑ gh ∈ (M p d) ×ˢ (M p (n - d)),
              (3 / 4 : ℝ) ^ omegaS (Sd p d) gh.1 * (3 / 4 : ℝ) ^ omegaS (Sd p d) gh.2 := by
              refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun _ _ _ => by positivity)
        _ = (∑ g ∈ M p d, (3 / 4 : ℝ) ^ omegaS (Sd p d) g) *
              (∑ h ∈ M p (n - d), (3 / 4 : ℝ) ^ omegaS (Sd p d) h) := by
              rw [Finset.sum_product, Finset.sum_mul_sum]
    have hdiv2 : (Bad2.card : ℝ) / (p : ℝ) ^ n ≤
        (4 / 3 : ℝ) ^ k *
          weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) d *
          weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) (n - d) := by
      have hpn_split : (p : ℝ) ^ n = (p : ℝ) ^ d * (p : ℝ) ^ (n - d) := by
        rw [← pow_add, Nat.add_sub_of_le (by omega)]
      have hinv_z : ((3 / 4 : ℝ) ^ k)⁻¹ = (4 / 3 : ℝ) ^ k := by
        rw [← inv_pow]
        norm_num
      have hPair_le : (Pairs.card : ℝ) ≤
          (4 / 3 : ℝ) ^ k *
            ((∑ g ∈ M p d, (3 / 4 : ℝ) ^ omegaS (Sd p d) g) *
              (∑ h ∈ M p (n - d), (3 / 4 : ℝ) ^ omegaS (Sd p d) h)) := by
        rw [← hinv_z, ← div_eq_inv_mul, le_div_iff₀ hzk_pos, mul_comm]
        exact hsum2
      unfold weightedAvg
      rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast]
      calc
        (Bad2.card : ℝ) / (p : ℝ) ^ n
          ≤ (Pairs.card : ℝ) / (p : ℝ) ^ n :=
            div_le_div_of_nonneg_right hcard_le hpn_pos.le
        _ ≤ ((4 / 3 : ℝ) ^ k *
              ((∑ g ∈ M p d, (3 / 4 : ℝ) ^ omegaS (Sd p d) g) *
                (∑ h ∈ M p (n - d), (3 / 4 : ℝ) ^ omegaS (Sd p d) h))) /
              ((p : ℝ) ^ d * (p : ℝ) ^ (n - d)) := by
            rw [← hpn_split]
            exact div_le_div_of_nonneg_right hPair_le hpn_pos.le
        _ = (4 / 3 : ℝ) ^ k *
              (((p : ℝ) ^ d)⁻¹ * ∑ g ∈ M p d, (3 / 4 : ℝ) ^ omegaS (Sd p d) g) *
              (((p : ℝ) ^ (n - d))⁻¹ * ∑ h ∈ M p (n - d), (3 / 4 : ℝ) ^ omegaS (Sd p d) h) := by
            field_simp [(pow_pos hp_pos d).ne', (pow_pos hp_pos (n - d)).ne']
    have hu_d : weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) d ≤
        (d : ℝ) ^ (-(1 / 4 : ℝ)) := by
      have h1 := weightedAvg_wz_le_binomSeq (p := p) (d := d) hz_pos hz_lt1 d le_rfl
      have h2 := binomSeq_le_rpow hz_pos hz_lt1 hd
      have h3 : (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) := by norm_num
      rw [h3] at h2
      exact h1.trans h2
    have hu_nd : weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) (n - d) ≤
        (4 / 3 : ℝ) * (d : ℝ) ^ (-(1 / 4 : ℝ)) := by
      have h1 := weightedAvg_wz_le_of_ge (p := p) (d := d) hz_pos hz_lt1 hd (n - d) (by omega)
      have h2 := binomSeq_le_rpow hz_pos hz_lt1 hd
      have h3 : (3 / 4 : ℝ) - 1 = -(1 / 4 : ℝ) := by norm_num
      rw [h3] at h2
      calc
        weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) (n - d)
          ≤ binomSeq (3 / 4) d / (3 / 4 : ℝ) := h1
        _ ≤ (d : ℝ) ^ (-(1 / 4 : ℝ)) / (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_right h2 hz_pos.le
        _ = (4 / 3 : ℝ) * (d : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
    have hpow43 : (4 / 3 : ℝ) ^ k ≤ (d : ℝ) ^ ((3 / 2 : ℝ) * Real.log (4 / 3)) := by
      have hlog43_pos : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4 / 3),
        Real.rpow_def_of_pos hd_pos]
      refine Real.exp_le_exp.mpr ?_
      have hmul : Real.log (4 / 3) * (k : ℝ) ≤
          Real.log (4 / 3) * ((3 / 2 : ℝ) * Real.log (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hk_le hlog43_pos.le
      linarith
    have hexp2 : -(1 / 2 : ℝ) + (3 / 2 : ℝ) * Real.log (4 / 3) ≤ -(1 / 20 : ℝ) := by
      linarith [log_four_thirds_le]
    have hu_d_nonneg := weightedAvg_wz_nonneg (p := p) d hz_pos d
    have hu_nd_nonneg := weightedAvg_wz_nonneg (p := p) d hz_pos (n - d)
    calc
      (Bad2.card : ℝ) / (p : ℝ) ^ n
        ≤ (4 / 3 : ℝ) ^ k *
            weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) d *
            weightedAvg p (fun f => (3 / 4 : ℝ) ^ omegaS (Sd p d) f) (n - d) := hdiv2
      _ ≤ (d : ℝ) ^ ((3 / 2 : ℝ) * Real.log (4 / 3)) *
            (d : ℝ) ^ (-(1 / 4 : ℝ)) *
            ((4 / 3 : ℝ) * (d : ℝ) ^ (-(1 / 4 : ℝ))) := by
          refine mul_le_mul ?_ hu_nd hu_nd_nonneg (by positivity)
          exact mul_le_mul hpow43 hu_d hu_d_nonneg (Real.rpow_pos_of_pos hd_pos _).le
      _ = (4 / 3 : ℝ) *
            ((d : ℝ) ^ (-(1 / 4 : ℝ)) * (d : ℝ) ^ (-(1 / 4 : ℝ)) *
              (d : ℝ) ^ ((3 / 2 : ℝ) * Real.log (4 / 3))) := by ring
      _ = (4 / 3 : ℝ) *
            (d : ℝ) ^ (-(1 / 2 : ℝ) + (3 / 2 : ℝ) * Real.log (4 / 3)) := by
          rw [← Real.rpow_add hd_pos, ← Real.rpow_add hd_pos]
          congr 2
          ring
      _ ≤ (4 / 3 : ℝ) * (d : ℝ) ^ (-(1 / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hd_ge1 hexp2) (by norm_num)
  have htot : (Bad.card : ℝ) / (p : ℝ) ^ n ≤
      ((4 : ℝ) ^ p * Real.exp 4 + 4 / 3) * (d : ℝ) ^ (-(1 / 20 : ℝ)) := by
    rw [hBad_split, Nat.cast_add, add_div]
    linarith
  exact (div_le_iff₀ hpn_pos).mp htot

end Step4Assembly

end Green93H1

theorem OMA.solution : OMA.R_Green93_green_93_variants_bskk_large_R1_H2_R1.H1 := by
  classical
  refine ⟨1 / 20, by norm_num, ?_⟩
  intro p _
  refine ⟨(4 : ℝ) ^ p * Real.exp 4 + 4 / 3, by positivity, ?_⟩
  intro n d hd h2d
  convert Green93H1.main_bound p n d hd h2d using 2
