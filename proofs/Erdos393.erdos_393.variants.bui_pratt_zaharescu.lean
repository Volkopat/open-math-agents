import FormalConjectures.ErdosProblems.«393»
import Mathlib

/-! Formalization of Bui-Pratt-Zaharescu (arXiv:2204.08423) for Erdos Problem 393. -/

namespace BPZ

open Finset Filter Asymptotics Real Polynomial PowerSeries
open scoped Topology

noncomputable def negInvBinom (r : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => negInvBinom r k * ((k : ℝ) + 1 / (r : ℝ)) / ((k + 1 : ℕ) : ℝ)

noncomputable def binomPS (r : ℕ) (c : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => negInvBinom r k * c ^ k

noncomputable def omegaPS (r β : ℕ) : PowerSeries ℝ :=
  ∏ j ∈ Finset.Ico 1 β, binomPS r (j : ℝ)

def beta3 (β₁ β₂ : ℕ) : Fin 3 → ℕ := ![1, β₁, β₂]

noncomputable def omega3PS (r β₁ β₂ : ℕ) (i : Fin 3) : PowerSeries ℝ :=
  omegaPS r (beta3 β₁ β₂ i)

noncomputable def omegaVal (r β : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.Ico 1 β, (1 - (j : ℝ) * x) ^ (-(1 : ℝ) / (r : ℝ))

noncomputable def omega3Val (r β₁ β₂ : ℕ) (x : ℝ) (i : Fin 3) : ℝ :=
  omegaVal r (beta3 β₁ β₂ i) x

noncomputable def Tpoly (r M : ℕ) : Polynomial ℤ :=
  Polynomial.C (r : ℤ) * ∏ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℤ) * Polynomial.X)

noncomputable def TApoly (r M β : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.Ico 1 β,
    Polynomial.C (j : ℤ) * ∏ l ∈ (Finset.Icc 1 M).erase j, (1 - Polynomial.C (l : ℤ) * Polynomial.X)

noncomputable def TA3 (r M β₁ β₂ : ℕ) (i : Fin 3) : Polynomial ℤ :=
  TApoly r M (beta3 β₁ β₂ i)

noncomputable def P_sq (r M β₁ β₂ : ℕ) (P : Fin 3 → Polynomial ℤ) : ℕ → Fin 3 → Polynomial ℤ
  | 0, i => P i
  | k + 1, i =>
      Tpoly r M * (P_sq r M β₁ β₂ P k i).derivative +
      TA3 r M β₁ β₂ i * P_sq r M β₁ β₂ P k i

noncomputable def Delta (r M β₁ β₂ : ℕ) (P : Fin 3 → Polynomial ℤ) : Polynomial ℤ :=
  Matrix.det (Matrix.of fun (k i : Fin 3) => P_sq r M β₁ β₂ P k.val i)

noncomputable def Q_raw (r : ℕ) : ℕ → ℕ → Polynomial ℝ
  | 0, l => if l = 0 then 1 else 0
  | 1, l => if l = 0 then 1 else 0
  | β + 2, l =>
      ∑ a ∈ Finset.range (l + 1),
        Q_raw r (β + 1) a *
        (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)) *
        Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)) *
        (1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a

noncomputable def Qpoly (r M β l : ℕ) : Polynomial ℝ :=
  Polynomial.C ((r : ℝ) ^ l) *
  (∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l) *
  Q_raw r β l

noncomputable def P_ang (r M β₁ β₂ : ℕ) (P : Fin 3 → Polynomial ℤ) (k : ℕ) (i : Fin 3) :
    Polynomial ℝ :=
  ∑ l ∈ Finset.range (k + 1),
    (((Tpoly r M).map (Int.castRingHom ℝ)) ^ (k - l) *
      Polynomial.C (1 / ((k - l).factorial : ℝ)) *
      (Polynomial.derivative^[k - l] ((P i).map (Int.castRingHom ℝ)))) *
    Qpoly r M (beta3 β₁ β₂ i) l

noncomputable def R_ps (r β₁ β₂ : ℕ) (P : Fin 3 → Polynomial ℤ) : PowerSeries ℝ :=
  ∑ i : Fin 3, ((P i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i


section Mod1
-- Part 1: Properties of negInvBinom

theorem negInvBinom_pos {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < negInvBinom r k := by
  induction k with
  | zero => simp [negInvBinom]
  | succ k ih =>
    simp only [negInvBinom]
    have hr' : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (by omega)
    have hnum : (0 : ℝ) < (k : ℝ) + 1 / (r : ℝ) := by
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hinv : (0 : ℝ) < 1 / (r : ℝ) := one_div_pos.mpr hr'
      linarith
    have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
    exact div_pos (mul_pos ih hnum) hden

theorem negInvBinom_le_one {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : negInvBinom r k ≤ 1 := by
  induction k with
  | zero => simp [negInvBinom]
  | succ k ih =>
    simp only [negInvBinom]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
    have hinv : 1 / (r : ℝ) ≤ 1 := div_le_one_of_le₀ hr1 (by linarith)
    have hden : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos k)
    have hnum_le : (k : ℝ) + 1 / (r : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    rw [div_le_iff₀ hden]
    calc negInvBinom r k * ((k : ℝ) + 1 / (r : ℝ))
        ≤ 1 * ((k + 1 : ℕ) : ℝ) := by
          apply mul_le_mul ih hnum_le
          · have : (0 : ℝ) < 1 / (r : ℝ) := one_div_pos.mpr (by linarith)
            have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
            linarith
          · linarith
      _ = 1 * ((k + 1 : ℕ) : ℝ) := rfl

private lemma negInvBinom_eq_prod {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    negInvBinom r k =
      (∏ j ∈ Finset.range k, ((j * r + 1 : ℕ) : ℝ)) / ((r : ℝ) ^ k * (k.factorial : ℝ)) := by
  induction k with
  | zero => simp [negInvBinom]
  | succ k ih =>
    simp only [negInvBinom, Finset.prod_range_succ, pow_succ]
    rw [ih]
    have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfac0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hk10 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    have hstep : (k : ℝ) + 1 / (r : ℝ) = ((k * r + 1 : ℕ) : ℝ) / (r : ℝ) := by
      push_cast
      field_simp
    have hfac_succ : (((k + 1).factorial : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hstep, hfac_succ]
    field_simp

private lemma prod_Icc_eq_factorial (k : ℕ) : ∏ i ∈ Finset.Icc 1 k, i = k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmem : k + 1 ∉ Finset.Icc 1 k := by simp
    have hset : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.prod_insert hmem, ih, Nat.factorial_succ]

private lemma factorization_factorial_le {p : ℕ} (hp : p.Prime) :
    ∀ k : ℕ, (k.factorial).factorization p ≤ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hprod : (k.factorial).factorization p = ∑ i ∈ Finset.Icc 1 k, i.factorization p := by
        rw [← prod_Icc_eq_factorial]
        have hnz : ∀ i ∈ Finset.Icc 1 k, i ≠ 0 := by
          intro i hi
          simp only [Finset.mem_Icc] at hi
          omega
        rw [Nat.factorization_prod hnz]
        simp [Finsupp.finsetSum_apply]
      rw [hprod, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 k) (fun i => p ∣ i)]
      have hnot : ∑ i ∈ (Finset.Icc 1 k).filter (fun i => ¬ p ∣ i), i.factorization p = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_filter] at hi
        exact Nat.factorization_eq_zero_of_not_dvd hi.2
      rw [hnot, add_zero]
      have hfilt :
          (Finset.Icc 1 k).filter (fun i => p ∣ i) =
            (Finset.Icc 1 (k / p)).image (fun j => p * j) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨hi1, hik⟩, ⟨j, rfl⟩⟩
          refine ⟨j, ⟨?_, ?_⟩, rfl⟩
          · rcases Nat.eq_zero_or_pos j with rfl | hj
            · omega
            · exact hj
          · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [mul_comm]; exact hik)
        · rintro ⟨j, ⟨hj1, hjk⟩, rfl⟩
          refine ⟨⟨?_, ?_⟩, dvd_mul_right p j⟩
          · have hp2 : 2 ≤ p := hp.two_le
            nlinarith
          · calc p * j ≤ p * (k / p) := Nat.mul_le_mul_left p hjk
              _ ≤ k := Nat.mul_div_le k p
      rw [hfilt, Finset.sum_image (by
        intro a _ b _ hab
        exact mul_left_cancel₀ hp.ne_zero hab)]
      have hterm :
          ∑ j ∈ Finset.Icc 1 (k / p), (p * j).factorization p =
            (k / p) + ∑ j ∈ Finset.Icc 1 (k / p), j.factorization p := by
        have h1 :
            ∑ j ∈ Finset.Icc 1 (k / p), (p * j).factorization p =
              ∑ j ∈ Finset.Icc 1 (k / p), (1 + j.factorization p) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_Icc] at hj
          have hj0 : j ≠ 0 := by omega
          rw [Nat.factorization_mul hp.ne_zero hj0, Finsupp.add_apply, hp.factorization_self]
        rw [h1, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc]
        simp
      rw [hterm]
      have hfac_div :
          ∑ j ∈ Finset.Icc 1 (k / p), j.factorization p = ((k / p).factorial).factorization p := by
        rw [← prod_Icc_eq_factorial]
        have hnz : ∀ j ∈ Finset.Icc 1 (k / p), j ≠ 0 := by
          intro j hj
          simp only [Finset.mem_Icc] at hj
          omega
        rw [Nat.factorization_prod hnz]
        simp [Finsupp.finsetSum_apply]
      rw [hfac_div]
      have hlt : k / p < k := Nat.div_lt_self hk hp.one_lt
      have hih : ((k / p).factorial).factorization p ≤ k / p := ih (k / p) hlt
      have hp2 : 2 ≤ p := hp.two_le
      have hmul : p * (k / p) ≤ k := Nat.mul_div_le k p
      calc k / p + ((k / p).factorial).factorization p
          ≤ k / p + k / p := Nat.add_le_add_left hih _
        _ = 2 * (k / p) := by ring
        _ ≤ p * (k / p) := Nat.mul_le_mul_right (k / p) hp2
        _ ≤ k := hmul

private lemma exists_mul_add_one_dvd_pow {p r μ : ℕ} (hp : p.Prime) (hpr : ¬ p ∣ r) (hμ : 1 ≤ μ) :
    ∃ l : ℕ, 1 ≤ l ∧ l < p ^ μ ∧ p ^ μ ∣ r * l + 1 := by
  have hcop : Nat.Coprime r (p ^ μ) := (hp.coprime_iff_not_dvd.mpr hpr).symm.pow_right μ
  have hm2 : 2 ≤ p ^ μ := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ μ := Nat.pow_le_pow_right hp.pos hμ
  set mNat : ℕ := p ^ μ
  set mInt : ℤ := (mNat : ℤ)
  have hm_pos : (0 : ℤ) < mInt := Int.natCast_pos.mpr (by omega)
  have hbez : (1 : ℤ) = (r : ℤ) * Nat.gcdA r mNat + mInt * Nat.gcdB r mNat := by
    have h := Nat.gcd_eq_gcd_ab r mNat
    rw [hcop.gcd_eq_one] at h
    simpa [mInt] using h
  set lInt : ℤ := (-Nat.gcdA r mNat) % mInt
  have hl_nonneg : 0 ≤ lInt := Int.emod_nonneg _ (ne_of_gt hm_pos)
  have hl_lt : lInt < mInt := Int.emod_lt_of_pos _ hm_pos
  have hdvd_int : mInt ∣ (r : ℤ) * lInt + 1 := by
    have hdiff : mInt ∣ lInt - (-Nat.gcdA r mNat) := by
      have hq := Int.emod_add_mul_ediv (-Nat.gcdA r mNat) mInt
      refine ⟨-((-Nat.gcdA r mNat) / mInt), ?_⟩
      linarith
    rcases hdiff with ⟨t, ht⟩
    refine ⟨Nat.gcdB r mNat + (r : ℤ) * t, ?_⟩
    have h1 : (r : ℤ) * (-Nat.gcdA r mNat) + 1 = mInt * Nat.gcdB r mNat := by
      linarith
    calc (r : ℤ) * lInt + 1
        = (r : ℤ) * ((-Nat.gcdA r mNat) + mInt * t) + 1 := by
          have : lInt = (-Nat.gcdA r mNat) + mInt * t := by linarith
          rw [this]
      _ = ((r : ℤ) * (-Nat.gcdA r mNat) + 1) + mInt * ((r : ℤ) * t) := by ring
      _ = mInt * Nat.gcdB r mNat + mInt * ((r : ℤ) * t) := by rw [h1]
      _ = mInt * (Nat.gcdB r mNat + (r : ℤ) * t) := by ring
  have hl_pos : 1 ≤ lInt := by
    by_contra h
    have hl0 : lInt = 0 := by omega
    rw [hl0, mul_zero, zero_add] at hdvd_int
    have h1 : mNat ∣ 1 := by
      dsimp only [mInt] at hdvd_int
      exact_mod_cast hdvd_int
    have hle : mNat ≤ 1 := Nat.le_of_dvd Nat.one_pos h1
    omega
  refine ⟨lInt.toNat, ?_, ?_, ?_⟩
  · omega
  · dsimp only [mInt] at hl_lt
    omega
  · have hcast : ((r * lInt.toNat + 1 : ℕ) : ℤ) = (r : ℤ) * lInt + 1 := by
      push_cast
      rw [Int.toNat_of_nonneg hl_nonneg]
    change mNat ∣ r * lInt.toNat + 1
    rw [← Int.ofNat_dvd, hcast]
    exact hdvd_int

private lemma factorial_dvd_pow_mul_prod {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    k.factorial ∣ r ^ k * ∏ j ∈ Finset.range k, (j * r + 1) := by
  have hN_ne : r ^ k * ∏ j ∈ Finset.range k, (j * r + 1) ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero k (by omega))
    rw [Finset.prod_ne_zero_iff]
    intro j _
    omega
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero k) hN_ne]
  intro p
  by_cases hp : p.Prime
  · have hprod_ne : ∏ j ∈ Finset.range k, (j * r + 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j _
      omega
    rw [Nat.factorization_mul (pow_ne_zero k (by omega)) hprod_ne, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hpr : p ∣ r
    · have hr_fac : 1 ≤ r.factorization p :=
        (hp.pow_dvd_iff_le_factorization (by omega)).mp (by simpa using hpr)
      calc (k.factorial).factorization p
          ≤ k := factorization_factorial_le hp k
        _ ≤ k * r.factorization p := Nat.le_mul_of_pos_right k (by omega)
        _ ≤ k * r.factorization p + (∏ j ∈ Finset.range k, (j * r + 1)).factorization p :=
            Nat.le_add_right _ _
    · set μ : ℕ := k * r + 1
      have hμ : 1 ≤ μ := by omega
      have hkr_lt : k * r < p ^ μ := by
        calc k * r < 2 ^ (k * r) := Nat.lt_two_pow_self
          _ ≤ 2 ^ μ := Nat.pow_le_pow_right (by omega) (by omega)
          _ ≤ p ^ μ := Nat.pow_le_pow_left hp.two_le μ
      obtain ⟨l, hl1, hl_lt, hl_dvd⟩ := exists_mul_add_one_dvd_pow hp hpr hμ
      have hkl : k ≤ l := by
        have hle : p ^ μ ≤ r * l + 1 := Nat.le_of_dvd (by omega) hl_dvd
        have h1 : k * r ≤ r * l := by omega
        rw [mul_comm r l] at h1
        exact Nat.le_of_mul_le_mul_right h1 (by omega)
      have hpl : ¬ p ∣ l := by
        intro hdiv
        have h1 : p ∣ r * l := dvd_mul_of_dvd_right hdiv r
        have h2 : p ∣ r * l + 1 := dvd_trans (dvd_pow_self p (by omega)) hl_dvd
        have h3 : p ∣ 1 := (Nat.dvd_add_right h1).mp h2
        exact hp.not_dvd_one h3
      have hdesc_eq : ∏ j ∈ Finset.range k, (l - j) = l.descFactorial k :=
        (Nat.descFactorial_eq_prod_range l k).symm
      have hdesc_ne : ∏ j ∈ Finset.range k, (l - j) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro j hj
        rw [Finset.mem_range] at hj
        omega
      have hfac_dvd_desc : k.factorial ∣ ∏ j ∈ Finset.range k, (l - j) := by
        rw [hdesc_eq, Nat.descFactorial_eq_factorial_mul_choose]
        exact dvd_mul_right _ _
      have hfac_le_desc :
          (k.factorial).factorization p ≤ (∏ j ∈ Finset.range k, (l - j)).factorization p :=
        (Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero k) hdesc_ne).mpr hfac_dvd_desc p
      have hdesc_le_prod :
          (∏ j ∈ Finset.range k, (l - j)).factorization p ≤
            (∏ j ∈ Finset.range k, (j * r + 1)).factorization p := by
        rw [Nat.factorization_prod (by
          intro j hj; rw [Finset.mem_range] at hj; omega)]
        rw [Nat.factorization_prod (by
          intro j _; omega)]
        simp only [Finsupp.finsetSum_apply]
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · simp [Nat.factorization_eq_zero_of_not_dvd hpl]
        · set b : ℕ := (l - j).factorization p
          have hlj_pos : 0 < l - j := by omega
          have hpb_dvd : p ^ b ∣ l - j := Nat.ordProj_dvd (l - j) p
          have hpb_lt : p ^ b < p ^ μ := by
            calc p ^ b ≤ l - j := Nat.le_of_dvd hlj_pos hpb_dvd
              _ < l := by omega
              _ < p ^ μ := hl_lt
          have hb_le : b ≤ μ := by
            by_contra hgt
            have hlt : μ < b := Nat.lt_of_not_ge hgt
            have : p ^ μ ≤ p ^ b := Nat.pow_le_pow_right hp.pos (le_of_lt hlt)
            omega
          have hpb_dvd_sum : p ^ b ∣ (j * r + 1) + r * (l - j) := by
            have heq : (j * r + 1) + r * (l - j) = r * l + 1 := by
              have h1 : j * r + r * (l - j) = r * l := by
                rw [mul_comm j r, ← mul_add, Nat.add_sub_of_le (by omega)]
              omega
            rw [heq]
            exact dvd_trans (Nat.pow_dvd_pow p hb_le) hl_dvd
          have hpb_dvd_term : p ^ b ∣ j * r + 1 :=
            (Nat.dvd_add_left (dvd_mul_of_dvd_right hpb_dvd r)).mp hpb_dvd_sum
          exact (hp.pow_dvd_iff_le_factorization (by omega)).mp hpb_dvd_term
      exact le_trans (le_trans hfac_le_desc hdesc_le_prod) (Nat.le_add_left _ _)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem negInvBinom_denom {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    ∃ m : ℤ, ((r : ℝ) ^ (2 * k)) * negInvBinom r k = (m : ℝ) := by
  obtain ⟨q, hq⟩ := factorial_dvd_pow_mul_prod hr k
  refine ⟨(q : ℤ), ?_⟩
  rw [negInvBinom_eq_prod (by omega)]
  have hfac0 : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq_real :
      (r : ℝ) ^ k * (∏ j ∈ Finset.range k, ((j * r + 1 : ℕ) : ℝ)) =
        (k.factorial : ℝ) * (q : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hq
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_prod] using h
  have hpow : (r : ℝ) ^ (2 * k) = (r : ℝ) ^ k * (r : ℝ) ^ k := by
    rw [two_mul, pow_add]
  rw [hpow]
  have hsimp :
      (r : ℝ) ^ k * (r : ℝ) ^ k *
          ((∏ j ∈ Finset.range k, ((j * r + 1 : ℕ) : ℝ)) / ((r : ℝ) ^ k * (k.factorial : ℝ))) =
        ((r : ℝ) ^ k * (∏ j ∈ Finset.range k, ((j * r + 1 : ℕ) : ℝ))) / (k.factorial : ℝ) := by
    field_simp
  rw [hsimp, hq_real, mul_div_cancel_left₀ _ hfac0]
  simp

-- Part 2: Properties of omegaPS

private lemma omegaPS_zero (r : ℕ) : omegaPS r 0 = 1 := by
  simp [omegaPS]

private lemma omegaPS_one (r : ℕ) : omegaPS r 1 = 1 := by
  simp [omegaPS]

private lemma omegaPS_succ (r : ℕ) {β : ℕ} (hβ : 1 ≤ β) :
    omegaPS r (β + 1) = omegaPS r β * binomPS r (β : ℝ) := by
  simp only [omegaPS, Finset.prod_Ico_succ_top hβ]

private lemma coeff_binomPS (r : ℕ) (c : ℝ) (k : ℕ) :
    PowerSeries.coeff k (binomPS r c) = negInvBinom r k * c ^ k := by
  simp [binomPS]

private lemma exists_int_sum {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, ∃ m : ℤ, f x = (m : ℝ)) :
    ∃ m : ℤ, ∑ x ∈ s, f x = (m : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨m1, hm1⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨m2, hm2⟩ := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    refine ⟨m1 + m2, ?_⟩
    rw [Finset.sum_insert ha, hm1, hm2]
    push_cast
    ring

theorem omegaPS_coeff_nonneg {r : ℕ} (hr : 1 ≤ r) (β l : ℕ) :
    0 ≤ PowerSeries.coeff l (omegaPS r β) := by
  induction β generalizing l with
  | zero =>
    rw [omegaPS_zero]
    by_cases hl : l = 0
    · subst hl; simp
    · simp [PowerSeries.coeff_one, hl]
  | succ β ih =>
    rcases Nat.eq_zero_or_pos β with rfl | hβ
    · rw [omegaPS_one]
      by_cases hl : l = 0
      · subst hl; simp
      · simp [PowerSeries.coeff_one, hl]
    · rw [omegaPS_succ r hβ, PowerSeries.coeff_mul]
      apply Finset.sum_nonneg
      intro p _
      rw [coeff_binomPS]
      apply mul_nonneg (ih p.1)
      exact mul_nonneg (le_of_lt (negInvBinom_pos hr p.2)) (pow_nonneg (Nat.cast_nonneg β) p.2)

theorem omegaPS_coeff_denom {r : ℕ} (hr : 2 ≤ r) (β l : ℕ) :
    ∃ m : ℤ, ((r : ℝ) ^ (2 * l)) * PowerSeries.coeff l (omegaPS r β) = (m : ℝ) := by
  induction β generalizing l with
  | zero =>
    rw [omegaPS_zero]
    by_cases hl : l = 0
    · subst hl; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [PowerSeries.coeff_one, hl]⟩
  | succ β ih =>
    rcases Nat.eq_zero_or_pos β with rfl | hβ
    · rw [omegaPS_one]
      by_cases hl : l = 0
      · subst hl; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [PowerSeries.coeff_one, hl]⟩
    · rw [omegaPS_succ r hβ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
      apply exists_int_sum
      intro a ha
      rw [Finset.mem_range] at ha
      rw [coeff_binomPS]
      have hsum : a + (l - a) = l := by omega
      have hpow : (r : ℝ) ^ (2 * l) = (r : ℝ) ^ (2 * a) * (r : ℝ) ^ (2 * (l - a)) := by
        rw [← pow_add, ← mul_add, hsum]
      obtain ⟨m1, hm1⟩ := ih a
      obtain ⟨m2, hm2⟩ := negInvBinom_denom hr (l - a)
      refine ⟨m1 * m2 * (β : ℤ) ^ (l - a), ?_⟩
      calc (r : ℝ) ^ (2 * l) *
            (PowerSeries.coeff a (omegaPS r β) * (negInvBinom r (l - a) * (β : ℝ) ^ (l - a)))
          = ((r : ℝ) ^ (2 * a) * PowerSeries.coeff a (omegaPS r β)) *
              ((r : ℝ) ^ (2 * (l - a)) * negInvBinom r (l - a)) * (β : ℝ) ^ (l - a) := by
            rw [hpow]; ring
        _ = (m1 : ℝ) * (m2 : ℝ) * (β : ℝ) ^ (l - a) := by rw [hm1, hm2]
        _ = ((m1 * m2 * (β : ℤ) ^ (l - a) : ℤ) : ℝ) := by push_cast; ring

private lemma hockey_stick (β l : ℕ) :
    ∑ a ∈ Finset.range (l + 1), (a + β).choose a = (l + (β + 1)).choose l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : l + (β + 1) = l + 1 + β := by omega
    have h2 : l + 1 + (β + 1) = (l + 1 + β) + 1 := by omega
    rw [h1, h2, Nat.choose_succ_succ]

private lemma omegaPS_coeff_le_choose {r M : ℕ} (hr : 1 ≤ r) (β : ℕ) (hβ : β ≤ M) (l : ℕ) :
    PowerSeries.coeff l (omegaPS r β) ≤ ((l + β).choose l : ℝ) * (M : ℝ) ^ l := by
  induction β generalizing l with
  | zero =>
    rw [omegaPS_zero]
    by_cases hl : l = 0
    · subst hl; simp
    · simp only [PowerSeries.coeff_one, hl, ↓reduceIte]
      positivity
  | succ β ih =>
    rcases Nat.eq_zero_or_pos β with rfl | hβpos
    · rw [omegaPS_one]
      by_cases hl : l = 0
      · subst hl; simp
      · simp only [PowerSeries.coeff_one, hl, ↓reduceIte]
        positivity
    · rw [omegaPS_succ r hβpos, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have hterm :
          ∑ a ∈ Finset.range (l + 1),
              PowerSeries.coeff a (omegaPS r β) * PowerSeries.coeff (l - a) (binomPS r (β : ℝ))
            ≤ ∑ a ∈ Finset.range (l + 1),
                (((a + β).choose a : ℝ) * (M : ℝ) ^ l) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Finset.mem_range] at ha
        rw [coeff_binomPS]
        have hsum : a + (l - a) = l := by omega
        have h1 : PowerSeries.coeff a (omegaPS r β) ≤ ((a + β).choose a : ℝ) * (M : ℝ) ^ a :=
          ih (by omega) a
        have h2 : negInvBinom r (l - a) * (β : ℝ) ^ (l - a) ≤ (M : ℝ) ^ (l - a) := by
          have hle1 : negInvBinom r (l - a) ≤ 1 := negInvBinom_le_one hr (l - a)
          have hβM : (β : ℝ) ≤ (M : ℝ) := Nat.cast_le.mpr (by omega)
          have hpow : (β : ℝ) ^ (l - a) ≤ (M : ℝ) ^ (l - a) :=
            pow_le_pow_left₀ (Nat.cast_nonneg β) hβM (l - a)
          calc negInvBinom r (l - a) * (β : ℝ) ^ (l - a)
              ≤ 1 * (M : ℝ) ^ (l - a) :=
                mul_le_mul hle1 hpow (pow_nonneg (Nat.cast_nonneg β) (l - a)) zero_le_one
            _ = (M : ℝ) ^ (l - a) := one_mul _
        have hnonneg2 : 0 ≤ negInvBinom r (l - a) * (β : ℝ) ^ (l - a) :=
          mul_nonneg (le_of_lt (negInvBinom_pos hr (l - a))) (pow_nonneg (Nat.cast_nonneg β) (l - a))
        calc PowerSeries.coeff a (omegaPS r β) * (negInvBinom r (l - a) * (β : ℝ) ^ (l - a))
            ≤ (((a + β).choose a : ℝ) * (M : ℝ) ^ a) * (M : ℝ) ^ (l - a) :=
              mul_le_mul h1 h2 hnonneg2 (by positivity)
          _ = ((a + β).choose a : ℝ) * (M : ℝ) ^ l := by
              rw [mul_assoc, ← pow_add, hsum]
      refine le_trans hterm ?_
      rw [← Finset.sum_mul]
      have hhs :
          (∑ a ∈ Finset.range (l + 1), ((a + β).choose a : ℝ)) =
            ((l + (β + 1)).choose l : ℝ) := by
        exact_mod_cast hockey_stick β l
      rw [hhs]

private lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    calc n.choose k
        ≤ ∑ i ∈ Finset.range (n + 1), n.choose i :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

theorem omegaPS_coeff_bound {r M β : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M) (hβ : β ≤ M) (l : ℕ) :
    |PowerSeries.coeff l (omegaPS r β)| ≤ (2 : ℝ) ^ M * (2 * (M : ℝ)) ^ l := by
  have _ := hM
  rw [abs_of_nonneg (omegaPS_coeff_nonneg hr β l)]
  have h1 := omegaPS_coeff_le_choose hr β hβ l
  have hch : ((l + β).choose l : ℝ) ≤ (2 : ℝ) ^ (l + β) := by
    exact_mod_cast choose_le_two_pow (l + β) l
  have h2pow : (2 : ℝ) ^ β ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hβ
  calc PowerSeries.coeff l (omegaPS r β)
      ≤ ((l + β).choose l : ℝ) * (M : ℝ) ^ l := h1
    _ ≤ (2 : ℝ) ^ (l + β) * (M : ℝ) ^ l :=
        mul_le_mul_of_nonneg_right hch (pow_nonneg (Nat.cast_nonneg M) l)
    _ = (2 : ℝ) ^ β * (2 * (M : ℝ)) ^ l := by
        rw [pow_add, mul_pow]
        ring
    _ ≤ (2 : ℝ) ^ M * (2 * (M : ℝ)) ^ l :=
        mul_le_mul_of_nonneg_right h2pow (pow_nonneg (by positivity) l)

-- Part 3: Siegel Lemma

theorem siegel_lemma {m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) (A : Fin m → Fin n → ℤ)
    {B : ℕ} (hB : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ (B : ℤ)) :
    ∃ x : Fin n → ℤ, (∃ j, x j ≠ 0) ∧ (∀ i, ∑ j, A i j * x j = 0) ∧
      ∀ j, (|x j| : ℝ) ≤ (3 * (B : ℝ) * (n : ℝ)) ^ ((m : ℝ) / ((n - m : ℕ) : ℝ)) := by
  set R : ℝ := (3 * (B : ℝ) * (n : ℝ)) ^ ((m : ℝ) / ((n - m : ℕ) : ℝ))
  have hbase_pos : (0 : ℝ) < 3 * (B : ℝ) * (n : ℝ) := by
    have hB' : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr (by omega)
    have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
    nlinarith
  have hR_pos : 0 < R := Real.rpow_pos_of_pos hbase_pos _
  set W : ℕ := ⌊R⌋₊ + 1
  have hW_pos : 1 ≤ W := Nat.succ_le_succ (Nat.zero_le _)
  have hR_lt_W : R < (W : ℝ) := by
    change R < ((⌊R⌋₊ + 1 : ℕ) : ℝ)
    push_cast
    exact Nat.lt_floor_add_one R
  have hW_sub_le : ((W - 1 : ℕ) : ℝ) ≤ R := by
    have hsub : W - 1 = ⌊R⌋₊ := Nat.add_sub_cancel ⌊R⌋₊ 1
    rw [hsub]
    exact Nat.floor_le (le_of_lt hR_pos)
  have hcard_lt : (2 * B * n * W + 1) ^ m < W ^ n := by
    have hnm_pos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hpow_lt : R ^ ((n - m : ℕ) : ℝ) < (W : ℝ) ^ ((n - m : ℕ) : ℝ) :=
      Real.rpow_lt_rpow (le_of_lt hR_pos) hR_lt_W hnm_pos
    have hR_pow : R ^ ((n - m : ℕ) : ℝ) = (3 * (B : ℝ) * (n : ℝ)) ^ m := by
      dsimp only [R]
      rw [← Real.rpow_mul (le_of_lt hbase_pos), div_mul_cancel₀ _ (ne_of_gt hnm_pos),
        Real.rpow_natCast]
    rw [hR_pow, Real.rpow_natCast] at hpow_lt
    have hW_real_pos : (0 : ℝ) < (W : ℝ) := Nat.cast_pos.mpr (by omega)
    have hmul_lt : (3 * (B : ℝ) * (n : ℝ) * (W : ℝ)) ^ m < (W : ℝ) ^ n := by
      have h1 : (3 * (B : ℝ) * (n : ℝ)) ^ m * (W : ℝ) ^ m < (W : ℝ) ^ (n - m) * (W : ℝ) ^ m :=
        mul_lt_mul_of_pos_right hpow_lt (pow_pos hW_real_pos m)
      rw [← mul_pow, ← pow_add, Nat.sub_add_cancel (le_of_lt hmn)] at h1
      exact h1
    have h2_le_3 : (2 * B * n * W + 1 : ℕ) ≤ 3 * B * n * W := by
      have hprod : 1 ≤ B * n * W := by
        have h1 : 1 ≤ B * n := Nat.mul_pos (by omega) (by omega)
        exact Nat.mul_pos h1 hW_pos
      have h2eq : 2 * B * n * W = 2 * (B * n * W) := by ring
      have h3eq : 3 * B * n * W = 3 * (B * n * W) := by ring
      omega
    have hreal_lt : (((2 * B * n * W + 1) ^ m : ℕ) : ℝ) < ((W ^ n : ℕ) : ℝ) := by
      have hle : (((2 * B * n * W + 1 : ℕ) : ℝ)) ^ m ≤ (3 * (B : ℝ) * (n : ℝ) * (W : ℝ)) ^ m := by
        apply pow_le_pow_left₀ (Nat.cast_nonneg _)
        have hc : ((2 * B * n * W + 1 : ℕ) : ℝ) ≤ ((3 * B * n * W : ℕ) : ℝ) :=
          Nat.cast_le.mpr h2_le_3
        simpa [Nat.cast_mul] using hc
      push_cast
      exact lt_of_le_of_lt (by simpa using hle) hmul_lt
    exact Nat.cast_lt.mp hreal_lt
  set S : Finset (Fin n → ℤ) := Fintype.piFinset (fun _ : Fin n => Finset.Ico (0 : ℤ) (W : ℤ))
  set Mbound : ℤ := (B : ℤ) * (n : ℤ) * (W : ℤ)
  set T : Finset (Fin m → ℤ) := Fintype.piFinset (fun _ : Fin m => Finset.Icc (-Mbound) Mbound)
  set f : (Fin n → ℤ) → (Fin m → ℤ) := fun y i => ∑ j, A i j * y j
  have hS_card : S.card = W ^ n := by
    simp only [S, Fintype.card_piFinset, Int.card_Ico, sub_zero, Int.toNat_natCast,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hT_card : T.card = (2 * B * n * W + 1) ^ m := by
    simp only [T, Fintype.card_piFinset, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    have heq : Mbound + 1 - -Mbound = ((2 * B * n * W + 1 : ℕ) : ℤ) := by
      dsimp only [Mbound]
      push_cast
      ring
    rw [heq, Int.toNat_natCast]
  have hmaps : ∀ y ∈ S, f y ∈ T := by
    intro y hy
    rw [Fintype.mem_piFinset] at hy ⊢
    intro i
    rw [Finset.mem_Icc]
    have habs : |f y i| ≤ Mbound := by
      calc |∑ j : Fin n, A i j * y j|
          ≤ ∑ j : Fin n, |A i j * y j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, |A i j| * |y j| := by
            apply Finset.sum_congr rfl
            intro j _
            exact abs_mul _ _
        _ ≤ ∑ _j : Fin n, (B : ℤ) * (W : ℤ) := by
            apply Finset.sum_le_sum
            intro j _
            have hyj := hy j
            rw [Finset.mem_Ico] at hyj
            have habsy : |y j| ≤ (W : ℤ) := by
              rw [abs_of_nonneg hyj.1]
              exact le_of_lt hyj.2
            exact mul_le_mul (hA i j) habsy (abs_nonneg _) (Int.natCast_nonneg B)
        _ = Mbound := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Mbound]
            ring
    exact abs_le.mp habs
  have hTS : T.card < S.card := by
    rw [hT_card, hS_card]
    exact hcard_lt
  obtain ⟨y1, hy1, y2, hy2, hne, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hTS hmaps
  refine ⟨fun j => y1 j - y2 j, ?_, ?_, ?_⟩
  · by_contra hall
    apply hne
    funext j
    have hj : y1 j - y2 j = 0 := by
      by_contra hnz
      exact hall ⟨j, hnz⟩
    omega
  · intro i
    have hi : f y1 i = f y2 i := congrFun hfeq i
    dsimp only [f] at hi
    calc ∑ j : Fin n, A i j * (y1 j - y2 j)
        = ∑ j : Fin n, (A i j * y1 j - A i j * y2 j) := by
          apply Finset.sum_congr rfl; intro j _; ring
      _ = (∑ j : Fin n, A i j * y1 j) - (∑ j : Fin n, A i j * y2 j) := by
          rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hi
  · intro j
    rw [Fintype.mem_piFinset] at hy1 hy2
    have h1 := Finset.mem_Ico.mp (hy1 j)
    have h2 := Finset.mem_Ico.mp (hy2 j)
    have habs_int : |y1 j - y2 j| ≤ ((W - 1 : ℕ) : ℤ) := by
      have hWcast : ((W - 1 : ℕ) : ℤ) = (W : ℤ) - 1 := by omega
      rw [hWcast, abs_le]
      omega
    have habs_real : ((|y1 j - y2 j| : ℤ) : ℝ) ≤ ((W - 1 : ℕ) : ℝ) := by
      exact_mod_cast habs_int
    rw [Int.cast_abs] at habs_real
    exact le_trans habs_real hW_sub_le

-- Part 4: Initial Pade polynomials

private lemma six_mul_succ_le_two_pow {D : ℕ} (hD : 10 ≤ D) : 6 * (D + 1) ≤ 2 ^ D := by
  induction D, hD using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    calc 6 * (k + 1 + 1) ≤ 2 * (6 * (k + 1)) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [pow_succ']

private lemma poly_from_coeffs_natDegree (D : ℕ) (c : ℕ → ℤ) :
    (∑ k ∈ Finset.range (D + 1), Polynomial.monomial k (c k)).natDegree ≤ D := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro k hk
  rw [Finset.mem_range] at hk
  exact le_trans (Polynomial.natDegree_monomial_le (c k)) (by omega)

private lemma poly_from_coeffs_coeff (D : ℕ) (c : ℕ → ℤ) (v : ℕ) :
    (∑ k ∈ Finset.range (D + 1), Polynomial.monomial k (c k)).coeff v =
      if v ≤ D then c v else 0 := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  by_cases hv : v ≤ D
  · rw [if_pos hv, Finset.sum_eq_single v]
    · simp
    · intro k _ hkv
      simp [hkv]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have : k ≠ v := by omega
    simp [this]

private lemma coeff_map_cast_poly (p : Polynomial ℤ) (v : ℕ) :
    PowerSeries.coeff v ((p.map (Int.castRingHom ℝ) : Polynomial ℝ) : PowerSeries ℝ) =
      (p.coeff v : ℝ) := by
  rw [Polynomial.coeff_coe, Polynomial.coeff_map]
  simp

private lemma coeff_R_ps (r β₁ β₂ : ℕ) (P : Fin 3 → Polynomial ℤ) (v : ℕ) :
    PowerSeries.coeff v (R_ps r β₁ β₂ P) =
      ((P 0).coeff v : ℝ) +
      (∑ k ∈ Finset.range (v + 1),
        ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)) +
      (∑ k ∈ Finset.range (v + 1),
        ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)) := by
  simp only [R_ps, Fin.sum_univ_three, map_add, omega3PS, beta3, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    omegaPS_one, mul_one]
  rw [coeff_map_cast_poly]
  have h1 :
      PowerSeries.coeff v
          ((((P 1).map (Int.castRingHom ℝ) : Polynomial ℝ) : PowerSeries ℝ) * omegaPS r β₁) =
        ∑ k ∈ Finset.range (v + 1),
          ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_map_cast_poly]
  have h2 :
      PowerSeries.coeff v
          ((((P 2).map (Int.castRingHom ℝ) : Polynomial ℝ) : PowerSeries ℝ) * omegaPS r β₂) =
        ∑ k ∈ Finset.range (v + 1),
          ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) := by
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_map_cast_poly]
  rw [h1, h2]

private lemma omegaPS_coeff_denom_le {r : ℕ} (hr : 2 ≤ r) (β l O : ℕ) (hl : l ≤ O) :
    ∃ m : ℤ, ((r : ℝ) ^ (2 * O)) * PowerSeries.coeff l (omegaPS r β) = (m : ℝ) := by
  obtain ⟨m0, hm0⟩ := omegaPS_coeff_denom hr β l
  refine ⟨(r : ℤ) ^ (2 * O - 2 * l) * m0, ?_⟩
  have hpow : (r : ℝ) ^ (2 * O) = (r : ℝ) ^ (2 * O - 2 * l) * (r : ℝ) ^ (2 * l) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  rw [hpow, mul_assoc, hm0]
  push_cast
  ring

private lemma siegel_bound_pade {r M D : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M) (hD : 10 ≤ D) :
    let O : ℕ := (29 * D) / 12
    let m : ℕ := O - D
    let n : ℕ := 2 * D + 2
    let B : ℕ := 2 ^ M * (2 * r ^ 2 * M) ^ O
    (3 * (B : ℝ) * (n : ℝ)) ^ ((m : ℝ) / ((n - m : ℕ) : ℝ)) ≤
      (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
        (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
  intro O m n B
  have h2D_le_O : 2 * D ≤ O := by dsimp only [O]; omega
  have hnm_pos : 0 < n - m := by dsimp only [n, m, O]; omega
  have hratio : (m : ℝ) / ((n - m : ℕ) : ℝ) ≤ (17 / 7 : ℝ) := by
    have hnat : 7 * m ≤ 17 * (n - m) := by dsimp only [n, m, O]; omega
    have hreal : (7 : ℝ) * (m : ℝ) ≤ (17 : ℝ) * ((n - m : ℕ) : ℝ) := by exact_mod_cast hnat
    have hpos : (0 : ℝ) < ((n - m : ℕ) : ℝ) := Nat.cast_pos.mpr hnm_pos
    rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 7)]
    linarith
  have h6D : (6 * (D + 1 : ℕ) : ℝ) ≤ (3 / 2 : ℝ) ^ O := by
    have h1 : ((6 * (D + 1) : ℕ) : ℝ) ≤ ((2 ^ D : ℕ) : ℝ) :=
      Nat.cast_le.mpr (six_mul_succ_le_two_pow hD)
    have h2 : (2 : ℝ) ^ D ≤ ((3 / 2 : ℝ) ^ 2) ^ D :=
      pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ (3 / 2 : ℝ) ^ 2) D
    have h3 : (3 / 2 : ℝ) ^ (2 * D) ≤ (3 / 2 : ℝ) ^ O :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) h2D_le_O
    calc (6 * (D + 1 : ℕ) : ℝ)
        = ((6 * (D + 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (2 : ℝ) ^ D := by simpa using h1
      _ ≤ ((3 / 2 : ℝ) ^ 2) ^ D := h2
      _ = (3 / 2 : ℝ) ^ (2 * D) := by rw [← pow_mul]
      _ ≤ (3 / 2 : ℝ) ^ O := h3
  have hbase_le :
      3 * (B : ℝ) * (n : ℝ) ≤ (2 : ℝ) ^ M * (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O := by
    have hBn : 3 * (B : ℝ) * (n : ℝ) =
        (6 * (D + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ M * (2 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O) := by
      dsimp only [B, n]
      push_cast
      ring
    rw [hBn]
    have hnonneg : 0 ≤ (2 : ℝ) ^ M * (2 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O := by positivity
    have h32 : (3 / 2 : ℝ) * (2 * (r : ℝ) ^ 2 * (M : ℝ)) = 3 * (r : ℝ) ^ 2 * (M : ℝ) := by ring
    calc (6 * (D + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ M * (2 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O)
        ≤ (3 / 2 : ℝ) ^ O * ((2 : ℝ) ^ M * (2 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O) :=
          mul_le_mul_of_nonneg_right h6D hnonneg
      _ = (2 : ℝ) ^ M * ((3 / 2 : ℝ) ^ O * (2 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O) := by ring
      _ = (2 : ℝ) ^ M * ((3 / 2 : ℝ) * (2 * (r : ℝ) ^ 2 * (M : ℝ))) ^ O := by rw [← mul_pow]
      _ = (2 : ℝ) ^ M * (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O := by rw [h32]
  have hbase1 : (1 : ℝ) ≤ 3 * (B : ℝ) * (n : ℝ) := by
    have hB1 : 1 ≤ B := by
      dsimp only [B]
      exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by omega) M) (pow_pos (by nlinarith) O))
    have hn1 : 1 ≤ n := by dsimp only [n]; omega
    have h1 : 1 ≤ 3 * B * n := by nlinarith
    have h2 : ((1 : ℕ) : ℝ) ≤ ((3 * B * n : ℕ) : ℝ) := Nat.cast_le.mpr h1
    simpa [Nat.cast_mul] using h2
  have hbase_nonneg : 0 ≤ 3 * (B : ℝ) * (n : ℝ) := by linarith
  have hexp_le :
      (3 * (B : ℝ) * (n : ℝ)) ^ ((m : ℝ) / ((n - m : ℕ) : ℝ)) ≤
        (3 * (B : ℝ) * (n : ℝ)) ^ (17 / 7 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 hratio
  have hrpow_mono :
      (3 * (B : ℝ) * (n : ℝ)) ^ (17 / 7 : ℝ) ≤
        ((2 : ℝ) ^ M * (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O) ^ (17 / 7 : ℝ) :=
    Real.rpow_le_rpow hbase_nonneg hbase_le (by norm_num)
  have hsplit :
      ((2 : ℝ) ^ M * (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O) ^ (17 / 7 : ℝ) =
        (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
    have h1 : 0 ≤ (2 : ℝ) ^ M := by positivity
    have h2 : 0 ≤ (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ O := by positivity
    rw [Real.mul_rpow h1 h2, ← Real.rpow_natCast (2 : ℝ) M,
      ← Real.rpow_natCast (3 * (r : ℝ) ^ 2 * (M : ℝ)) O,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 3 * (r : ℝ) ^ 2 * (M : ℝ))]
    ring_nf
  exact le_trans (le_trans hexp_le hrpow_mono) (le_of_eq hsplit)

private lemma pade_scale_bound {r M O : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M) :
    ((r : ℝ) ^ (2 * O)) *
        ((2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))) ≤
      (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
        (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
  have _ := hM
  have hr1 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr (by omega)
    nlinarith
  have hO_le : (O : ℝ) ≤ (17 / 7 : ℝ) * (O : ℝ) := by
    have hO0 : (0 : ℝ) ≤ (O : ℝ) := Nat.cast_nonneg O
    linarith
  have hrpow : (r : ℝ) ^ (2 * O) ≤ ((r : ℝ) ^ 2) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
    calc (r : ℝ) ^ (2 * O)
        = ((r : ℝ) ^ 2) ^ O := by rw [pow_mul]
      _ = ((r : ℝ) ^ 2) ^ (O : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ ((r : ℝ) ^ 2) ^ ((17 / 7 : ℝ) * (O : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hr1 hO_le
  have hmul :
      ((r : ℝ) ^ 2) ^ ((17 / 7 : ℝ) * (O : ℝ)) *
          (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) =
        (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have hnonneg :
      0 ≤ (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
            (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by positivity
  calc ((r : ℝ) ^ (2 * O)) *
        ((2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)))
      ≤ ((r : ℝ) ^ 2) ^ ((17 / 7 : ℝ) * (O : ℝ)) *
          ((2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
            (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))) :=
        mul_le_mul_of_nonneg_right hrpow hnonneg
    _ = (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (((r : ℝ) ^ 2) ^ ((17 / 7 : ℝ) * (O : ℝ)) *
            (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))) := by ring
    _ = (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by rw [hmul]

private lemma pade_final_bound {r M D : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M) (hD : 10 ≤ D) :
    let O : ℕ := (29 * D) / 12
    (2 * (D + 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))) *
        (2 : ℝ) ^ M ≤
      (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) := by
  intro O
  have h2D_le_O : 2 * D ≤ O := by dsimp only [O]; omega
  have h12O_le : 12 * O ≤ 29 * D := by dsimp only [O]; omega
  have hO_exp : (17 / 7 : ℝ) * (O : ℝ) ≤ (493 / 84 : ℝ) * (D : ℝ) := by
    have hreal : (12 : ℝ) * (O : ℝ) ≤ (29 : ℝ) * (D : ℝ) := by exact_mod_cast h12O_le
    linarith
  have h2M :
      (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) * (2 : ℝ) ^ M ≤ (16 : ℝ) ^ M := by
    rw [← Real.rpow_natCast (2 : ℝ) M, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hexp : (17 / 7 : ℝ) * (M : ℝ) + (M : ℝ) ≤ 4 * (M : ℝ) := by
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    calc (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ) + (M : ℝ))
        ≤ (2 : ℝ) ^ (4 * (M : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
      _ = ((2 : ℝ) ^ (4 : ℝ)) ^ (M : ℝ) := by rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (16 : ℝ) ^ M := by
          rw [show (2 : ℝ) ^ (4 : ℝ) = (16 : ℝ) by norm_num, Real.rpow_natCast]
  have h2D_bound :
      (2 * (D + 1 : ℕ) : ℝ) ≤ (4 / 3 : ℝ) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
    have h1 : (2 * (D + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ D := by
      have hnat : 2 * (D + 1) ≤ 2 ^ D := le_trans (by omega) (six_mul_succ_le_two_pow hD)
      have hc : ((2 * (D + 1) : ℕ) : ℝ) ≤ ((2 ^ D : ℕ) : ℝ) := Nat.cast_le.mpr hnat
      simpa [Nat.cast_mul, Nat.cast_add] using hc
    have h2 : (2 : ℝ) ^ D ≤ ((4 / 3 : ℝ) ^ 4) ^ D :=
      pow_le_pow_left₀ (by norm_num) (by norm_num : (2 : ℝ) ≤ (4 / 3 : ℝ) ^ 4) D
    have h3 : (4 : ℝ) * (D : ℝ) ≤ (17 / 7 : ℝ) * (O : ℝ) := by
      have h2Dr : (2 : ℝ) * (D : ℝ) ≤ (O : ℝ) := by exact_mod_cast h2D_le_O
      have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
      linarith
    calc (2 * (D + 1 : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ D := h1
      _ ≤ ((4 / 3 : ℝ) ^ 4) ^ D := h2
      _ = (4 / 3 : ℝ) ^ (4 * D) := by rw [← pow_mul]
      _ = (4 / 3 : ℝ) ^ ((4 * D : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ = (4 / 3 : ℝ) ^ ((4 : ℝ) * (D : ℝ)) := by push_cast; rfl
      _ ≤ (4 / 3 : ℝ) ^ ((17 / 7 : ℝ) * (O : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4 / 3) h3
  have h4rM1 : (1 : ℝ) ≤ 4 * (r : ℝ) ^ 4 * (M : ℝ) := by
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr (by omega)
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
    have hr4 : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ hr1
    nlinarith
  have hbase_step :
      (2 * (D + 1 : ℕ) : ℝ) * (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) ≤
        (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) := by
    calc (2 * (D + 1 : ℕ) : ℝ) * (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))
        ≤ (4 / 3 : ℝ) ^ ((17 / 7 : ℝ) * (O : ℝ)) *
            (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) :=
          mul_le_mul_of_nonneg_right h2D_bound (by positivity)
      _ = ((4 / 3 : ℝ) * (3 * (r : ℝ) ^ 4 * (M : ℝ))) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
          rw [← Real.mul_rpow (by norm_num) (by positivity)]
      _ = (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by ring_nf
      _ ≤ (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le h4rM1 hO_exp
  calc (2 * (D + 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
          (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))) *
        (2 : ℝ) ^ M
      = ((2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) * (2 : ℝ) ^ M) *
          ((2 * (D + 1 : ℕ) : ℝ) *
            (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))) := by ring
    _ ≤ (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) :=
        mul_le_mul h2M hbase_step (by positivity) (by positivity)

theorem exists_initial_pade {r M β₁ β₂ D : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M)
    (hβ1 : 1 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M) (hD : 10 ≤ D) :
    ∃ P : Fin 3 → Polynomial ℤ,
      (∀ i, (P i).natDegree ≤ D) ∧
      (∃ i, P i ≠ 0) ∧
      (∀ i v, (|(P i).coeff v| : ℝ) ≤
        (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) *
          (2 * (M : ℝ)) ^ v) ∧
      (∀ v ≤ (29 * D) / 12, PowerSeries.coeff v (R_ps r β₁ β₂ P) = 0) ∧
      (∀ v, |PowerSeries.coeff v (R_ps r β₁ β₂ P)| ≤
        (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) *
          (2 * (M : ℝ)) ^ v) := by
  have _ := hβ1
  set O : ℕ := (29 * D) / 12
  set m : ℕ := O - D
  set n : ℕ := 2 * D + 2
  set B : ℕ := 2 ^ M * (2 * r ^ 2 * M) ^ O
  have hm : 1 ≤ m := by dsimp only [m, O]; omega
  have hmn : m < n := by dsimp only [m, n, O]; omega
  have hB : 1 ≤ B := by
    dsimp only [B]
    exact Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by omega) M) (pow_pos (by nlinarith) O))
  have hβ1M : β₁ ≤ M := le_trans (le_of_lt hβ12) hβ2
  -- Integer scaled coefficients of omegaPS r β₁ and omegaPS r β₂ for l ≤ O
  let b1Int : ℕ → ℤ := fun l =>
    if hl : l ≤ O then Classical.choose (omegaPS_coeff_denom_le hr β₁ l O hl) else 0
  let b2Int : ℕ → ℤ := fun l =>
    if hl : l ≤ O then Classical.choose (omegaPS_coeff_denom_le hr β₂ l O hl) else 0
  have hb1Int_eq :
      ∀ l ≤ O, ((b1Int l : ℤ) : ℝ) = ((r : ℝ) ^ (2 * O)) * PowerSeries.coeff l (omegaPS r β₁) := by
    intro l hl
    simp only [b1Int, dif_pos hl]
    exact (Classical.choose_spec (omegaPS_coeff_denom_le hr β₁ l O hl)).symm
  have hb2Int_eq :
      ∀ l ≤ O, ((b2Int l : ℤ) : ℝ) = ((r : ℝ) ^ (2 * O)) * PowerSeries.coeff l (omegaPS r β₂) := by
    intro l hl
    simp only [b2Int, dif_pos hl]
    exact (Classical.choose_spec (omegaPS_coeff_denom_le hr β₂ l O hl)).symm
  have hb1Int_bound : ∀ l ≤ O, |b1Int l| ≤ (B : ℤ) := by
    intro l hl
    have hreal : (|b1Int l| : ℝ) ≤ (B : ℝ) := by
      rw [hb1Int_eq l hl, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg r) _)]
      have hcb := omegaPS_coeff_bound (r := r) (by omega) hM hβ1M l
      have h2M1 : (1 : ℝ) ≤ 2 * (M : ℝ) := by
        have : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
        linarith
      have hpowl : (2 * (M : ℝ)) ^ l ≤ (2 * (M : ℝ)) ^ O := pow_le_pow_right₀ h2M1 hl
      calc (r : ℝ) ^ (2 * O) * |PowerSeries.coeff l (omegaPS r β₁)|
          ≤ (r : ℝ) ^ (2 * O) * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ l) :=
            mul_le_mul_of_nonneg_left hcb (by positivity)
        _ ≤ (r : ℝ) ^ (2 * O) * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ O) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowl (by positivity)) (by positivity)
        _ = (B : ℝ) := by
            dsimp only [B]
            push_cast
            rw [pow_mul]
            ring
    have hreal' : ((|b1Int l| : ℤ) : ℝ) ≤ ((B : ℤ) : ℝ) := by
      simpa [Int.cast_abs] using hreal
    exact Int.cast_le.mp hreal'
  have hb2Int_bound : ∀ l ≤ O, |b2Int l| ≤ (B : ℤ) := by
    intro l hl
    have hreal : (|b2Int l| : ℝ) ≤ (B : ℝ) := by
      rw [hb2Int_eq l hl, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg r) _)]
      have hcb := omegaPS_coeff_bound (r := r) (by omega) hM hβ2 l
      have h2M1 : (1 : ℝ) ≤ 2 * (M : ℝ) := by
        have : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
        linarith
      have hpowl : (2 * (M : ℝ)) ^ l ≤ (2 * (M : ℝ)) ^ O := pow_le_pow_right₀ h2M1 hl
      calc (r : ℝ) ^ (2 * O) * |PowerSeries.coeff l (omegaPS r β₂)|
          ≤ (r : ℝ) ^ (2 * O) * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ l) :=
            mul_le_mul_of_nonneg_left hcb (by positivity)
        _ ≤ (r : ℝ) ^ (2 * O) * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ O) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpowl (by positivity)) (by positivity)
        _ = (B : ℝ) := by
            dsimp only [B]
            push_cast
            rw [pow_mul]
            ring
    have hreal' : ((|b2Int l| : ℤ) : ℝ) ≤ ((B : ℤ) : ℝ) := by
      simpa [Int.cast_abs] using hreal
    exact Int.cast_le.mp hreal'
  -- Matrix for equations D + 1 ≤ v ≤ O
  let A : Fin m → Fin n → ℤ := fun i j =>
    let v := D + 1 + i.val
    if j.val < D + 1 then b1Int (v - j.val)
    else b2Int (v - (j.val - (D + 1)))
  have hA : ∀ i j, |A i j| ≤ (B : ℤ) := by
    intro i j
    dsimp only [A]
    split_ifs with h
    · exact hb1Int_bound _ (by omega)
    · exact hb2Int_bound _ (by omega)
  obtain ⟨x, ⟨j0, hj0⟩, hAx, hx_bound⟩ := siegel_lemma hm hmn A hB hA
  -- Extract q1, q2 : ℕ → ℤ supported on 0..D
  let q1 : ℕ → ℤ := fun k => if hk : k < D + 1 then x ⟨k, by dsimp only [n]; omega⟩ else 0
  let q2 : ℕ → ℤ := fun k => if hk : k < D + 1 then x ⟨D + 1 + k, by dsimp only [n]; omega⟩ else 0
  let p1 : ℕ → ℤ := fun k => (r : ℤ) ^ (2 * O) * q1 k
  let p2 : ℕ → ℤ := fun k => (r : ℤ) ^ (2 * O) * q2 k
  let p0 : ℕ → ℤ := fun v =>
    -(∑ k ∈ Finset.range (v + 1), (q1 k * b1Int (v - k) + q2 k * b2Int (v - k)))
  let P : Fin 3 → Polynomial ℤ :=
    ![∑ k ∈ Finset.range (D + 1), Polynomial.monomial k (p0 k),
      ∑ k ∈ Finset.range (D + 1), Polynomial.monomial k (p1 k),
      ∑ k ∈ Finset.range (D + 1), Polynomial.monomial k (p2 k)]
  -- Basic coefficient properties of P
  have hP_deg : ∀ i, (P i).natDegree ≤ D := by
    intro i
    fin_cases i
    · exact poly_from_coeffs_natDegree D p0
    · exact poly_from_coeffs_natDegree D p1
    · exact poly_from_coeffs_natDegree D p2
  have hP0_coeff : ∀ v, (P 0).coeff v = if v ≤ D then p0 v else 0 := fun v =>
    poly_from_coeffs_coeff D p0 v
  have hP1_coeff : ∀ v, (P 1).coeff v = if v ≤ D then p1 v else 0 := fun v =>
    poly_from_coeffs_coeff D p1 v
  have hP2_coeff : ∀ v, (P 2).coeff v = if v ≤ D then p2 v else 0 := fun v =>
    poly_from_coeffs_coeff D p2 v
  -- Nonzero polynomial
  have hP_ne : ∃ i, P i ≠ 0 := by
    by_cases hj : j0.val < D + 1
    · refine ⟨1, ?_⟩
      intro hzero
      have hc := congrArg (fun p : Polynomial ℤ => p.coeff j0.val) hzero
      rw [hP1_coeff, if_pos (by omega), Polynomial.coeff_zero] at hc
      dsimp only [p1, q1] at hc
      rw [dif_pos hj] at hc
      have hr0 : (r : ℤ) ^ (2 * O) ≠ 0 := pow_ne_zero _ (by omega)
      have hx0 : x j0 = 0 := by
        have h1 : x ⟨j0.val, _⟩ = 0 := (mul_eq_zero.mp hc).resolve_left hr0
        simpa using h1
      exact hj0 hx0
    · refine ⟨2, ?_⟩
      intro hzero
      set k0 := j0.val - (D + 1)
      have hk0 : k0 < D + 1 := by dsimp only [k0, n] at *; omega
      have hc := congrArg (fun p : Polynomial ℤ => p.coeff k0) hzero
      rw [hP2_coeff, if_pos (by omega), Polynomial.coeff_zero] at hc
      dsimp only [p2, q2] at hc
      rw [dif_pos hk0] at hc
      have hr0 : (r : ℤ) ^ (2 * O) ≠ 0 := pow_ne_zero _ (by omega)
      have h1 : x ⟨D + 1 + k0, _⟩ = 0 := (mul_eq_zero.mp hc).resolve_left hr0
      have heq : (⟨D + 1 + k0, by dsimp only [n]; omega⟩ : Fin n) = j0 := by
        ext; dsimp only [k0]; omega
      rw [heq] at h1
      exact hj0 h1
  -- Intermediate bound Qbound on |p1 k|, |p2 k|
  set Qbound : ℝ :=
    (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
      (3 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ))
  have hq_le : ∀ k, (|q1 k| : ℝ) ≤
      (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
        (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) ∧
      (|q2 k| : ℝ) ≤
      (2 : ℝ) ^ ((17 / 7 : ℝ) * (M : ℝ)) *
        (3 * (r : ℝ) ^ 2 * (M : ℝ)) ^ ((17 / 7 : ℝ) * (O : ℝ)) := by
    intro k
    have hsb := siegel_bound_pade hr hM hD
    constructor
    · dsimp only [q1]
      split_ifs with hk
      · exact le_trans (hx_bound _) hsb
      · simp; positivity
    · dsimp only [q2]
      split_ifs with hk
      · exact le_trans (hx_bound _) hsb
      · simp; positivity
  have hp12_le : ∀ k, (|(P 1).coeff k| : ℝ) ≤ Qbound ∧ (|(P 2).coeff k| : ℝ) ≤ Qbound := by
    intro k
    have hsc := pade_scale_bound (O := O) hr hM
    constructor
    · rw [hP1_coeff]
      split_ifs with hk
      · dsimp only [p1]
        rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, abs_mul,
          abs_of_nonneg (pow_nonneg (Nat.cast_nonneg r) _)]
        exact le_trans (mul_le_mul_of_nonneg_left (hq_le k).1 (by positivity)) hsc
      · simp; positivity
    · rw [hP2_coeff]
      split_ifs with hk
      · dsimp only [p2]
        rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, abs_mul,
          abs_of_nonneg (pow_nonneg (Nat.cast_nonneg r) _)]
        exact le_trans (mul_le_mul_of_nonneg_left (hq_le k).2 (by positivity)) hsc
      · simp; positivity
  -- Common bound on the double convolution sum for ANY v
  have hconv_bound : ∀ v : ℕ,
      |((∑ k ∈ Finset.range (v + 1),
          ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)) +
        (∑ k ∈ Finset.range (v + 1),
          ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)))| ≤
        (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) *
          (2 * (M : ℝ)) ^ v := by
    intro v
    have h1_trunc :
        ∑ k ∈ Finset.range (v + 1),
          ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) =
        ∑ k ∈ Finset.range (min (v + 1) (D + 1)),
          ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
      intro k hk hnot
      rw [Finset.mem_range] at hk hnot
      have hgt : ¬ k ≤ D := by omega
      rw [hP1_coeff, if_neg hgt]
      simp
    have h2_trunc :
        ∑ k ∈ Finset.range (v + 1),
          ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) =
        ∑ k ∈ Finset.range (min (v + 1) (D + 1)),
          ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
      intro k hk hnot
      rw [Finset.mem_range] at hk hnot
      have hgt : ¬ k ≤ D := by omega
      rw [hP2_coeff, if_neg hgt]
      simp
    rw [h1_trunc, h2_trunc]
    have h2M1 : (1 : ℝ) ≤ 2 * (M : ℝ) := by
      have : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
      linarith
    have hterm1 :
        |∑ k ∈ Finset.range (min (v + 1) (D + 1)),
            ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)| ≤
          ((D + 1 : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
      calc |∑ k ∈ Finset.range (min (v + 1) (D + 1)),
              ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)|
          ≤ ∑ k ∈ Finset.range (min (v + 1) (D + 1)),
              |((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range (min (v + 1) (D + 1)),
              (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul]
            have hc1 : |((P 1).coeff k : ℝ)| ≤ Qbound := (hp12_le k).1
            have hc2 : |PowerSeries.coeff (v - k) (omegaPS r β₁)| ≤
                (2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v := by
              refine le_trans (omegaPS_coeff_bound (r := r) (by omega) hM hβ1M (v - k)) ?_
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ h2M1 (Nat.sub_le v k)) (by positivity)
            exact mul_le_mul hc1 hc2 (abs_nonneg _) (by positivity)
        _ = ((min (v + 1) (D + 1) : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((D + 1 : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact Nat.cast_le.mpr (min_le_right _ _)
    have hterm2 :
        |∑ k ∈ Finset.range (min (v + 1) (D + 1)),
            ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)| ≤
          ((D + 1 : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
      calc |∑ k ∈ Finset.range (min (v + 1) (D + 1)),
              ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)|
          ≤ ∑ k ∈ Finset.range (min (v + 1) (D + 1)),
              |((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range (min (v + 1) (D + 1)),
              (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
            apply Finset.sum_le_sum
            intro k _
            rw [abs_mul]
            have hc1 : |((P 2).coeff k : ℝ)| ≤ Qbound := (hp12_le k).2
            have hc2 : |PowerSeries.coeff (v - k) (omegaPS r β₂)| ≤
                (2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v := by
              refine le_trans (omegaPS_coeff_bound (r := r) (by omega) hM hβ2 (v - k)) ?_
              exact mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ h2M1 (Nat.sub_le v k)) (by positivity)
            exact mul_le_mul hc1 hc2 (abs_nonneg _) (by positivity)
        _ = ((min (v + 1) (D + 1) : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
            simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((D + 1 : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact Nat.cast_le.mpr (min_le_right _ _)
    have hfb := pade_final_bound hr hM hD
    calc |((∑ k ∈ Finset.range (min (v + 1) (D + 1)),
            ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)) +
          (∑ k ∈ Finset.range (min (v + 1) (D + 1)),
            ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)))|
        ≤ |∑ k ∈ Finset.range (min (v + 1) (D + 1)),
            ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)| +
          |∑ k ∈ Finset.range (min (v + 1) (D + 1)),
            ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂)| :=
          abs_add_le _ _
      _ ≤ ((D + 1 : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) +
          ((D + 1 : ℕ) : ℝ) * (Qbound * ((2 : ℝ) ^ M * (2 * (M : ℝ)) ^ v)) :=
          add_le_add hterm1 hterm2
      _ = ((2 * (D + 1 : ℕ) : ℝ) * Qbound * (2 : ℝ) ^ M) * (2 * (M : ℝ)) ^ v := by ring
      _ ≤ ((16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ))) *
            (2 * (M : ℝ)) ^ v :=
          mul_le_mul_of_nonneg_right hfb (by positivity)
  -- Vanishing of R_ps for v ≤ O
  have hR_zero : ∀ v ≤ O, PowerSeries.coeff v (R_ps r β₁ β₂ P) = 0 := by
    intro v hvO
    rw [coeff_R_ps]
    by_cases hvD : v ≤ D
    · rw [hP0_coeff, if_pos hvD]
      have hconv1 :
          ∑ k ∈ Finset.range (v + 1),
              ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) =
            ∑ k ∈ Finset.range (v + 1), (q1 k : ℝ) * (b1Int (v - k) : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hP1_coeff, if_pos (by omega)]
        dsimp only [p1]
        rw [hb1Int_eq (v - k) (by omega)]
        push_cast
        ring
      have hconv2 :
          ∑ k ∈ Finset.range (v + 1),
              ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) =
            ∑ k ∈ Finset.range (v + 1), (q2 k : ℝ) * (b2Int (v - k) : ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hP2_coeff, if_pos (by omega)]
        dsimp only [p2]
        rw [hb2Int_eq (v - k) (by omega)]
        push_cast
        ring
      rw [hconv1, hconv2]
      dsimp only [p0]
      push_cast
      rw [Finset.sum_add_distrib]
      ring
    · rw [hP0_coeff, if_neg hvD]
      simp only [Int.cast_zero, zero_add]
      set idx : Fin m := ⟨v - (D + 1), by dsimp only [m]; omega⟩
      have hv_eq : D + 1 + idx.val = v := by dsimp only [idx]; omega
      have hsum_zero : ∑ j : Fin n, A idx j * x j = 0 := hAx idx
      have hsplit_fin :
          ∑ j : Fin n, A idx j * x j =
            (∑ k ∈ Finset.range (D + 1), b1Int (v - k) * q1 k) +
            (∑ k ∈ Finset.range (D + 1), b2Int (v - k) * q2 k) := by
        have hn_eq : n = (D + 1) + (D + 1) := by dsimp only [n]; omega
        rw [← Fin.sum_univ_eq_sum_range (fun k => b1Int (v - k) * q1 k) (D + 1),
          ← Fin.sum_univ_eq_sum_range (fun k => b2Int (v - k) * q2 k) (D + 1)]
        have hcast_sum :
            ∑ j : Fin n, A idx j * x j =
              ∑ j : Fin ((D + 1) + (D + 1)),
                A idx (Fin.cast hn_eq.symm j) * x (Fin.cast hn_eq.symm j) := by
          exact (Equiv.sum_comp (finCongr hn_eq.symm) (fun j => A idx j * x j)).symm
        rw [hcast_sum, Fin.sum_univ_add]
        congr 1
        · apply Finset.sum_congr rfl
          intro k _
          have hval : (Fin.cast hn_eq.symm (Fin.castAdd (D + 1) k)).val = k.val := by simp
          dsimp only [A, q1]
          rw [hv_eq, hval, if_pos k.isLt, dif_pos k.isLt]
          congr 1
        · apply Finset.sum_congr rfl
          intro k _
          have hval : (Fin.cast hn_eq.symm (Fin.natAdd (D + 1) k)).val = D + 1 + k.val := by
            simp [add_comm]
          have hnot : ¬ D + 1 + k.val < D + 1 := by omega
          have hsub : D + 1 + k.val - (D + 1) = k.val := by omega
          dsimp only [A, q2]
          rw [hv_eq, hval, if_neg hnot, hsub, dif_pos k.isLt]
          congr 1
      rw [hsplit_fin] at hsum_zero
      have h1_eq :
          ∑ k ∈ Finset.range (v + 1),
              ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) =
            ∑ k ∈ Finset.range (D + 1), (b1Int (v - k) : ℝ) * (q1 k : ℝ) := by
        have hsub :
            ∑ k ∈ Finset.range (v + 1),
                ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) =
              ∑ k ∈ Finset.range (D + 1),
                ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁) := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro k hk hnot
          rw [Finset.mem_range] at hk hnot
          rw [hP1_coeff, if_neg (by omega)]
          simp
        rw [hsub]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hP1_coeff, if_pos (by omega)]
        dsimp only [p1]
        rw [hb1Int_eq (v - k) (by omega)]
        push_cast
        ring
      have h2_eq :
          ∑ k ∈ Finset.range (v + 1),
              ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) =
            ∑ k ∈ Finset.range (D + 1), (b2Int (v - k) : ℝ) * (q2 k : ℝ) := by
        have hsub :
            ∑ k ∈ Finset.range (v + 1),
                ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) =
              ∑ k ∈ Finset.range (D + 1),
                ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂) := by
          symm
          apply Finset.sum_subset (Finset.range_mono (by omega))
          intro k hk hnot
          rw [Finset.mem_range] at hk hnot
          rw [hP2_coeff, if_neg (by omega)]
          simp
        rw [hsub]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hP2_coeff, if_pos (by omega)]
        dsimp only [p2]
        rw [hb2Int_eq (v - k) (by omega)]
        push_cast
        ring
      rw [h1_eq, h2_eq]
      have hreal :
          (((∑ k ∈ Finset.range (D + 1), b1Int (v - k) * q1 k) +
            (∑ k ∈ Finset.range (D + 1), b2Int (v - k) * q2 k) : ℤ) : ℝ) = 0 := by
        exact_mod_cast hsum_zero
      simpa [Int.cast_add, Int.cast_sum, Int.cast_mul] using hreal
  -- Bounds on coefficients of P i
  have hP_bound : ∀ i v, (|(P i).coeff v| : ℝ) ≤
      (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) *
        (2 * (M : ℝ)) ^ v := by
    intro i v
    have hQ_le_target :
        Qbound ≤
          (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) *
            (2 * (M : ℝ)) ^ v := by
      have hfb := pade_final_bound hr hM hD
      have h1 : (1 : ℝ) ≤ (2 * (D + 1 : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := Nat.one_le_cast.mpr (Nat.succ_pos D)
        linarith
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
      have h3 : (1 : ℝ) ≤ (2 * (M : ℝ)) ^ v := by
        apply one_le_pow₀
        have : (1 : ℝ) ≤ (M : ℝ) := Nat.one_le_cast.mpr hM
        linarith
      calc Qbound
          = 1 * Qbound * 1 := by ring
        _ ≤ (2 * (D + 1 : ℕ) : ℝ) * Qbound * (2 : ℝ) ^ M := by
            have hstep : 1 * Qbound ≤ (2 * (D + 1 : ℕ) : ℝ) * Qbound :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
            exact mul_le_mul hstep h2 (by norm_num) (by positivity)
        _ ≤ (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) := hfb
        _ = ((16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ))) * 1 :=
            (mul_one _).symm
        _ ≤ ((16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ))) *
              (2 * (M : ℝ)) ^ v :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    fin_cases i
    · change |((P 0).coeff v : ℝ)| ≤ _
      by_cases hvD : v ≤ D
      · have hzero := hR_zero v (by dsimp only [O]; omega)
        rw [coeff_R_ps] at hzero
        have heq : ((P 0).coeff v : ℝ) =
            -((∑ k ∈ Finset.range (v + 1),
                ((P 1).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₁)) +
              (∑ k ∈ Finset.range (v + 1),
                ((P 2).coeff k : ℝ) * PowerSeries.coeff (v - k) (omegaPS r β₂))) := by
          linarith
        rw [heq, abs_neg]
        exact hconv_bound v
      · rw [hP0_coeff, if_neg hvD]
        simp
        positivity
    · change |((P 1).coeff v : ℝ)| ≤ _
      exact le_trans (hp12_le v).1 hQ_le_target
    · change |((P 2).coeff v : ℝ)| ≤ _
      exact le_trans (hp12_le v).2 hQ_le_target
  -- Bound on coefficients of R_ps
  have hR_bound : ∀ v, |PowerSeries.coeff v (R_ps r β₁ β₂ P)| ≤
      (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) *
        (2 * (M : ℝ)) ^ v := by
    intro v
    by_cases hvO : v ≤ O
    · rw [hR_zero v hvO, abs_zero]
      positivity
    · rw [coeff_R_ps, hP0_coeff, if_neg (by dsimp only [O] at hvO; omega)]
      simp only [Int.cast_zero, zero_add]
      exact hconv_bound v
  exact ⟨P, hP_deg, hP_ne, hP_bound, hR_zero, hR_bound⟩

end Mod1

section Mod2

/- Part 2A: Degree bounds for `Tpoly`, `TApoly`, `P_sq`, and `Delta`. -/

private lemma natDegree_one_sub_C_mul_X_le (a : ℤ) :
    (1 - Polynomial.C a * Polynomial.X).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
  exact Polynomial.natDegree_mul_le.trans (by simp)

private lemma natDegree_prod_linear_le (s : Finset ℕ) :
    (∏ j ∈ s, (1 - Polynomial.C (j : ℤ) * Polynomial.X)).natDegree ≤ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := natDegree_one_sub_C_mul_X_le (a : ℤ)
    have h2 := Polynomial.natDegree_mul_le
      (p := 1 - Polynomial.C (a : ℤ) * Polynomial.X)
      (q := ∏ j ∈ s, (1 - Polynomial.C (j : ℤ) * Polynomial.X))
    omega

private lemma Tpoly_natDegree_le (r M : ℕ) : (Tpoly r M).natDegree ≤ M := by
  unfold Tpoly
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  exact (natDegree_prod_linear_le (Finset.Icc 1 M)).trans (by simp)

private lemma TApoly_natDegree_le (r M β : ℕ) : (TApoly r M β).natDegree ≤ M := by
  unfold TApoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le fun j _ => ?_
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine (natDegree_prod_linear_le _).trans ?_
  exact (Finset.card_erase_le).trans (by simp)

private lemma P_sq_natDegree_le {r M β₁ β₂ D : ℕ}
    (P : Fin 3 → Polynomial ℤ) (hdeg : ∀ i, (P i).natDegree ≤ D) (k : ℕ) (i : Fin 3) :
    (P_sq r M β₁ β₂ P k i).natDegree ≤ D + k * M := by
  induction k with
  | zero =>
    simpa [P_sq] using hdeg i
  | succ k ih =>
    simp only [P_sq]
    have hkm : (k + 1) * M = k * M + M := by ring
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h1 := Tpoly_natDegree_le r M
      have h2 := Polynomial.natDegree_derivative_le (P_sq r M β₁ β₂ P k i)
      omega
    · refine (Polynomial.natDegree_mul_le).trans ?_
      have h1 : (TA3 r M β₁ β₂ i).natDegree ≤ M := TApoly_natDegree_le r M (beta3 β₁ β₂ i)
      omega

theorem Delta_natDegree_le {r M β₁ β₂ D : ℕ} (hM : 1 ≤ M) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (hdeg : ∀ i, (P i).natDegree ≤ D) :
    (Delta r M β₁ β₂ P).natDegree ≤ 3 * D + 3 * M := by
  have _ := hM
  have _ := hβ2
  unfold Delta
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.sup_le fun σ _ => ?_
  dsimp only [Function.comp_apply]
  have hsign : (Equiv.Perm.sign σ • ∏ i : Fin 3,
      (Matrix.of fun (k i : Fin 3) => P_sq r M β₁ β₂ P k.val i) (σ i) i).natDegree =
      (∏ i : Fin 3, P_sq r M β₁ β₂ P (σ i).val i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hsign]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i : Fin 3, (P_sq r M β₁ β₂ P (σ i).val i).natDegree
      ≤ ∑ i : Fin 3, (D + (σ i).val * M) :=
        Finset.sum_le_sum fun i _ => P_sq_natDegree_le P hdeg (σ i).val i
    _ = ∑ i : Fin 3, D + (∑ i : Fin 3, (σ i).val) * M := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = 3 * D + (∑ i : Fin 3, i.val) * M := by
        rw [Equiv.sum_comp σ (fun i : Fin 3 => i.val)]
        simp
    _ = 3 * D + 3 * M := by
        rw [Fin.sum_univ_three]
        simp

/- Part 2B: Formal power series derivative helpers and `P_ang_powerSeries_eq`. -/

private lemma ps_deriv_mul (f g : PowerSeries ℝ) :
    PowerSeries.derivative ℝ (f * g) =
      PowerSeries.derivative ℝ f * g + f * PowerSeries.derivative ℝ g := by
  rw [(PowerSeries.derivative ℝ).leibniz f g]
  simp only [smul_eq_mul]
  ring

private lemma ps_deriv_pow_mul (f : PowerSeries ℝ) (n : ℕ) :
    f * PowerSeries.derivative ℝ (f ^ n) = (n : ℝ) • (f ^ n * PowerSeries.derivative ℝ f) := by
  cases n with
  | zero =>
    simp
  | succ n =>
    rw [PowerSeries.derivative_pow]
    simp only [Nat.add_sub_cancel]
    rw [Algebra.smul_def, PowerSeries.algebraMap_eq]
    have hnat : ((n + 1 : ℕ) : PowerSeries ℝ) = PowerSeries.C ((n + 1 : ℕ) : ℝ) := by
      simp [map_natCast]
    rw [hnat]
    ring

private lemma ps_deriv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → PowerSeries ℝ) :
    PowerSeries.derivative ℝ (∏ i ∈ s, f i) =
      ∑ i ∈ s, PowerSeries.derivative ℝ (f i) * ∏ j ∈ s.erase i, f j := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, ps_deriv_mul, ih, Finset.sum_insert ha,
      Finset.erase_insert ha, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i ≠ a := fun h => ha (h ▸ hi)
    have hnot : a ∉ s.erase i := fun h => ha (Finset.mem_of_mem_erase h)
    rw [Finset.erase_insert_of_ne hne.symm, Finset.prod_insert hnot]
    ring

private lemma ps_iterate_deriv_add (f g : PowerSeries ℝ) (k : ℕ) :
    (PowerSeries.derivative ℝ)^[k] (f + g) =
      (PowerSeries.derivative ℝ)^[k] f + (PowerSeries.derivative ℝ)^[k] g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih, map_add]

private lemma ps_iterate_deriv_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ) (k : ℕ) :
    (PowerSeries.derivative ℝ)^[k] (∑ i ∈ s, f i) =
      ∑ i ∈ s, (PowerSeries.derivative ℝ)^[k] (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [Finset.sum_empty] at ih ⊢
      rw [Function.iterate_succ_apply', ih, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ps_iterate_deriv_add, ih, Finset.sum_insert ha]

private lemma ps_iterate_deriv_smul (c : ℝ) (f : PowerSeries ℝ) (k : ℕ) :
    (PowerSeries.derivative ℝ)^[k] (c • f) = c • (PowerSeries.derivative ℝ)^[k] f := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      (PowerSeries.derivative ℝ).map_smul]

private lemma ps_iterate_deriv_coe (p : Polynomial ℝ) (k : ℕ) :
    (PowerSeries.derivative ℝ)^[k] (p : PowerSeries ℝ) =
      ((Polynomial.derivative^[k] p : Polynomial ℝ) : PowerSeries ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, PowerSeries.derivative_coe]

private lemma ps_iterate_deriv_one (k : ℕ) :
    (PowerSeries.derivative ℝ)^[k] (1 : PowerSeries ℝ) = if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    rw [Function.iterate_succ_apply, PowerSeries.derivative_one]
    induction k with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]

private lemma ps_iterate_deriv_mul (f g : PowerSeries ℝ) (k : ℕ) :
    (PowerSeries.derivative ℝ)^[k] (f * g) =
      ∑ a ∈ Finset.range (k + 1),
        (Nat.choose k a : ℝ) •
          ((PowerSeries.derivative ℝ)^[a] f * (PowerSeries.derivative ℝ)^[k - a] g) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    have hstep :
        ∑ a ∈ Finset.range (k + 1),
          PowerSeries.derivative ℝ
            ((Nat.choose k a : ℝ) •
              ((PowerSeries.derivative ℝ)^[a] f * (PowerSeries.derivative ℝ)^[k - a] g)) =
        ∑ a ∈ Finset.range (k + 1),
          (Nat.choose k a : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) +
        ∑ a ∈ Finset.range (k + 1),
          (Nat.choose k a : ℝ) •
            ((PowerSeries.derivative ℝ)^[a] f * (PowerSeries.derivative ℝ)^[k - a + 1] g) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [(PowerSeries.derivative ℝ).map_smul, ps_deriv_mul, smul_add,
        Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [hstep]
    rw [Finset.sum_range_succ' _ (k + 1)]
    have h1 :
        ∑ a ∈ Finset.range (k + 1),
          (Nat.choose k a : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) =
        ∑ a ∈ Finset.range k,
          (Nat.choose k a : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) +
        (PowerSeries.derivative ℝ)^[k + 1] f * g := by
      rw [Finset.sum_range_succ]
      simp
    have h2 :
        ∑ a ∈ Finset.range (k + 1),
          (Nat.choose k a : ℝ) •
            ((PowerSeries.derivative ℝ)^[a] f * (PowerSeries.derivative ℝ)^[k - a + 1] g) =
        ∑ a ∈ Finset.range k,
          (Nat.choose k (a + 1) : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) +
        f * (PowerSeries.derivative ℝ)^[k + 1] g := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, Function.iterate_zero, id_eq,
        Nat.sub_zero]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      have hak : a < k := Finset.mem_range.mp ha
      have hsub : k - (a + 1) + 1 = k - a := by omega
      rw [hsub]
    rw [h1, h2]
    have h3 :
        ∑ a ∈ Finset.range (k + 1),
          (Nat.choose (k + 1) (a + 1) : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k + 1 - (a + 1)] g) =
        ∑ a ∈ Finset.range k,
          (Nat.choose (k + 1) (a + 1) : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) +
        (PowerSeries.derivative ℝ)^[k + 1] f * g := by
      rw [Finset.sum_range_succ]
      simp only [Nat.choose_self, Nat.cast_one, one_smul, Nat.sub_self, Function.iterate_zero, id_eq,
        Nat.succ_sub_succ_eq_sub]
    rw [h3]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, Function.iterate_zero, id_eq,
      Nat.sub_zero]
    have hcomb :
        ∑ a ∈ Finset.range k,
          (Nat.choose k a : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) +
        ∑ a ∈ Finset.range k,
          (Nat.choose k (a + 1) : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) =
        ∑ a ∈ Finset.range k,
          (Nat.choose (k + 1) (a + 1) : ℝ) •
            ((PowerSeries.derivative ℝ)^[a + 1] f * (PowerSeries.derivative ℝ)^[k - a] g) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.choose_succ_succ, Nat.cast_add]
    rw [← hcomb]
    abel

private lemma binomPS_constantCoeff (r : ℕ) (c : ℝ) :
    PowerSeries.constantCoeff (binomPS r c) = 1 := by
  simp [binomPS, negInvBinom]

private lemma omegaPS_constantCoeff (r β : ℕ) :
    PowerSeries.constantCoeff (omegaPS r β) = 1 := by
  unfold omegaPS
  rw [map_prod]
  exact Finset.prod_eq_one fun j _ => binomPS_constantCoeff r (j : ℝ)

private lemma omega3PS_constantCoeff (r β₁ β₂ : ℕ) (i : Fin 3) :
    PowerSeries.constantCoeff (omega3PS r β₁ β₂ i) = 1 :=
  omegaPS_constantCoeff r (beta3 β₁ β₂ i)

private lemma binomPS_diff_eq (r : ℕ) (c : ℝ) :
    (1 - PowerSeries.C c * PowerSeries.X) * PowerSeries.derivative ℝ (binomPS r c) =
      PowerSeries.C (c / (r : ℝ)) * binomPS r c := by
  ext n
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_derivative]
  cases n with
  | zero =>
    simp [binomPS, negInvBinom]
    ring
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    simp only [binomPS, PowerSeries.coeff_mk, negInvBinom]
    have hn2 : ((n + 1 + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpow : c ^ (n + 1 + 1) = c * c ^ (n + 1) := by ring
    rw [hpow]
    field_simp [hn2]
    push_cast
    ring

private lemma binomPS_pow_r_eq_one {r : ℕ} (hr : 1 ≤ r) (c : ℝ) :
    (1 - PowerSeries.C c * PowerSeries.X) * (binomPS r c) ^ r = 1 := by
  apply PowerSeries.derivative.ext
  · rw [ps_deriv_mul, map_sub, PowerSeries.derivative_one, ps_deriv_mul, PowerSeries.derivative_C,
      zero_mul, zero_add, PowerSeries.derivative_X, mul_one, zero_sub, PowerSeries.derivative_pow]
    have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpow : (binomPS r c) ^ (r - 1) * binomPS r c = (binomPS r c) ^ r := by
      rw [← pow_succ, Nat.sub_add_cancel hr]
    have hnat : (r : PowerSeries ℝ) = PowerSeries.C (r : ℝ) := by simp [map_natCast]
    have hstep :
        (1 - PowerSeries.C c * PowerSeries.X) *
          ((r : PowerSeries ℝ) * (binomPS r c) ^ (r - 1) * PowerSeries.derivative ℝ (binomPS r c)) =
        PowerSeries.C (r : ℝ) * (binomPS r c) ^ (r - 1) *
          ((1 - PowerSeries.C c * PowerSeries.X) * PowerSeries.derivative ℝ (binomPS r c)) := by
      rw [hnat]; ring
    rw [hstep, binomPS_diff_eq]
    have hmul :
        PowerSeries.C (r : ℝ) * (binomPS r c) ^ (r - 1) *
          (PowerSeries.C (c / (r : ℝ)) * binomPS r c) =
        PowerSeries.C ((r : ℝ) * (c / (r : ℝ))) * ((binomPS r c) ^ (r - 1) * binomPS r c) := by
      rw [map_mul]; ring
    rw [hmul, hpow, mul_div_cancel₀ c hr0]
    ring
  · simp [binomPS_constantCoeff]

private lemma binomPS_iterate_deriv (r : ℕ) (c : ℝ) (k : ℕ) :
    (1 - PowerSeries.C c * PowerSeries.X) ^ k *
        (PowerSeries.derivative ℝ)^[k] (binomPS r c) =
      (k.factorial : ℝ) • (PowerSeries.C (negInvBinom r k * c ^ k) * binomPS r c) := by
  set u : PowerSeries ℝ := 1 - PowerSeries.C c * PowerSeries.X
  have hdu : PowerSeries.derivative ℝ u = -PowerSeries.C c := by
    simp [u, PowerSeries.derivative_C, PowerSeries.derivative_X]
  induction k with
  | zero =>
    simp [negInvBinom]
  | succ k ih =>
    have hd := congrArg (fun F => u * PowerSeries.derivative ℝ F) ih
    rw [ps_deriv_mul, mul_add, ← mul_assoc, ps_deriv_pow_mul, hdu,
      show u * (u ^ k * PowerSeries.derivative ℝ ((PowerSeries.derivative ℝ)^[k] (binomPS r c))) =
        u ^ (k + 1) * (PowerSeries.derivative ℝ)^[k + 1] (binomPS r c) by
        rw [pow_succ', Function.iterate_succ_apply']; ring] at hd
    rw [(PowerSeries.derivative ℝ).map_smul, ps_deriv_mul, PowerSeries.derivative_C, zero_mul,
      zero_add, mul_smul_comm, ← mul_assoc, mul_comm u (PowerSeries.C _), mul_assoc,
      binomPS_diff_eq] at hd
    have h1 :
        (k : ℝ) • (u ^ k * -PowerSeries.C c) * (PowerSeries.derivative ℝ)^[k] (binomPS r c) =
        -(k : ℝ) • (PowerSeries.C c * (u ^ k * (PowerSeries.derivative ℝ)^[k] (binomPS r c))) := by
      rw [smul_mul_assoc, neg_smul, ← smul_neg]
      congr 1; ring
    rw [h1, ih] at hd
    have h2 :
        u ^ (k + 1) * (PowerSeries.derivative ℝ)^[k + 1] (binomPS r c) =
        (k.factorial : ℝ) •
          (PowerSeries.C (negInvBinom r k * c ^ k) * (PowerSeries.C (c / (r : ℝ)) * binomPS r c)) +
        (k : ℝ) •
          (PowerSeries.C c * ((k.factorial : ℝ) •
            (PowerSeries.C (negInvBinom r k * c ^ k) * binomPS r c))) := by
      rw [neg_smul] at hd
      linear_combination hd
    rw [h2]
    simp only [Algebra.smul_def, PowerSeries.algebraMap_eq]
    have hcomb :
        PowerSeries.C (k.factorial : ℝ) *
          (PowerSeries.C (negInvBinom r k * c ^ k) * (PowerSeries.C (c / (r : ℝ)) * binomPS r c)) +
        PowerSeries.C (k : ℝ) *
          (PowerSeries.C c * (PowerSeries.C (k.factorial : ℝ) *
            (PowerSeries.C (negInvBinom r k * c ^ k) * binomPS r c))) =
        PowerSeries.C ((k.factorial : ℝ) * (negInvBinom r k * c ^ k) * (c / (r : ℝ)) +
          (k : ℝ) * c * ((k.factorial : ℝ) * (negInvBinom r k * c ^ k))) * binomPS r c := by
      simp only [map_add, map_mul]
      ring
    rw [hcomb, ← mul_assoc (PowerSeries.C ((k + 1).factorial : ℝ)), ← map_mul]
    congr 2
    simp only [negInvBinom, Nat.factorial_succ, Nat.cast_mul]
    have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    field_simp [hk1]
    ring

private lemma coe_prod_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) :
    ((∏ i ∈ s, f i : Polynomial ℝ) : PowerSeries ℝ) = ∏ i ∈ s, (f i : PowerSeries ℝ) :=
  map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℝ)) f s

private lemma coe_sum_poly {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ) :
    ((∑ i ∈ s, f i : Polynomial ℝ) : PowerSeries ℝ) = ∑ i ∈ s, (f i : PowerSeries ℝ) :=
  map_sum (Polynomial.coeToPowerSeries.ringHom (R := ℝ)) f s

private lemma Q_raw_powerSeries_eq (r β l : ℕ) :
    (((∏ j ∈ Finset.Ico 1 β, (1 - Polynomial.C (j : ℝ) * Polynomial.X)) : Polynomial ℝ) :
        PowerSeries ℝ) ^ l *
        (PowerSeries.derivative ℝ)^[l] (omegaPS r β) =
      (l.factorial : ℝ) • ((Q_raw r β l : PowerSeries ℝ) * omegaPS r β) := by
  induction β generalizing l with
  | zero =>
    simp only [Finset.Ico_eq_empty (by omega : ¬ 1 < 0), Finset.prod_empty, Polynomial.coe_one,
      one_pow, one_mul, omegaPS, Q_raw, ps_iterate_deriv_one]
    split_ifs with hl
    · subst hl; simp
    · simp
  | succ β ih =>
    cases β with
    | zero =>
      simp only [Finset.Ico_self, Finset.prod_empty, Polynomial.coe_one, one_pow, one_mul, omegaPS,
        Q_raw, ps_iterate_deriv_one]
      split_ifs with hl
      · subst hl; simp
      · simp
    | succ β =>
      have hIco : Finset.Ico 1 (β + 2) = insert (β + 1) (Finset.Ico 1 (β + 1)) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnotmem : β + 1 ∉ Finset.Ico 1 (β + 1) := by simp
      have homega : omegaPS r (β + 2) =
          omegaPS r (β + 1) * binomPS r ((β + 1 : ℕ) : ℝ) := by
        unfold omegaPS
        rw [hIco, Finset.prod_insert hnotmem, mul_comm]
      have hprod :
          (((∏ j ∈ Finset.Ico 1 (β + 2), (1 - Polynomial.C (j : ℝ) * Polynomial.X)) :
              Polynomial ℝ) : PowerSeries ℝ) =
          (((∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X)) :
              Polynomial ℝ) : PowerSeries ℝ) *
            (1 - PowerSeries.C ((β + 1 : ℕ) : ℝ) * PowerSeries.X) := by
        rw [hIco, Finset.prod_insert hnotmem, Polynomial.coe_mul, mul_comm]
        simp only [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
          Polynomial.coe_X]
      rw [hprod, mul_pow, homega, ps_iterate_deriv_mul, Finset.mul_sum]
      set U : PowerSeries ℝ :=
        (((∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X)) :
          Polynomial ℝ) : PowerSeries ℝ)
      set V : PowerSeries ℝ := 1 - PowerSeries.C ((β + 1 : ℕ) : ℝ) * PowerSeries.X
      have hterm : ∀ a ∈ Finset.range (l + 1),
          U ^ l * V ^ l *
            ((Nat.choose l a : ℝ) •
              ((PowerSeries.derivative ℝ)^[a] (omegaPS r (β + 1)) *
                (PowerSeries.derivative ℝ)^[l - a] (binomPS r ((β + 1 : ℕ) : ℝ)))) =
          (l.factorial : ℝ) •
            (((Q_raw r (β + 1) a *
              (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)) *
              Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)) *
              (1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a : Polynomial ℝ) :
              PowerSeries ℝ) * (omegaPS r (β + 1) * binomPS r ((β + 1 : ℕ) : ℝ))) := by
        intro a ha
        have hal : a ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        have hUl : U ^ l = U ^ (l - a) * U ^ a := by rw [← pow_add, Nat.sub_add_cancel hal]
        have hVl : V ^ l = V ^ a * V ^ (l - a) := by rw [← pow_add, Nat.add_sub_cancel' hal]
        rw [mul_smul_comm, hUl, hVl]
        have hregroup :
            U ^ (l - a) * U ^ a * (V ^ a * V ^ (l - a)) *
              ((PowerSeries.derivative ℝ)^[a] (omegaPS r (β + 1)) *
                (PowerSeries.derivative ℝ)^[l - a] (binomPS r ((β + 1 : ℕ) : ℝ))) =
            U ^ (l - a) * V ^ a *
              (U ^ a * (PowerSeries.derivative ℝ)^[a] (omegaPS r (β + 1))) *
              (V ^ (l - a) * (PowerSeries.derivative ℝ)^[l - a] (binomPS r ((β + 1 : ℕ) : ℝ))) := by
          ring
        rw [hregroup, ih a, binomPS_iterate_deriv]
        have hch : (Nat.choose l a : ℝ) * (a.factorial : ℝ) * ((l - a).factorial : ℝ) =
            (l.factorial : ℝ) := by
          exact_mod_cast Nat.choose_mul_factorial_mul_factorial hal
        have hUpow :
            U ^ (l - a) =
              (((∏ j ∈ Finset.Ico 1 (β + 1),
                  (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)) : Polynomial ℝ) :
                PowerSeries ℝ) := by
          simp only [U, ← Polynomial.coe_pow, Finset.prod_pow]
        have hVpow :
            V ^ a =
              (((1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a : Polynomial ℝ) :
                PowerSeries ℝ) := by
          simp only [V, Polynomial.coe_pow, Polynomial.coe_sub, Polynomial.coe_one,
            Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_X]
        rw [hUpow, hVpow]
        simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, Polynomial.coe_mul, Polynomial.coe_C]
        have hfac :
            PowerSeries.C (Nat.choose l a : ℝ) *
              (PowerSeries.C (a.factorial : ℝ) * PowerSeries.C ((l - a).factorial : ℝ)) =
            PowerSeries.C (l.factorial : ℝ) := by
          rw [← map_mul, ← map_mul, ← mul_assoc, hch]
        calc PowerSeries.C (Nat.choose l a : ℝ) *
              ((((∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a) :
                  Polynomial ℝ) : PowerSeries ℝ) *
                (((1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a : Polynomial ℝ) :
                  PowerSeries ℝ) *
                (PowerSeries.C (a.factorial : ℝ) *
                  ((Q_raw r (β + 1) a : PowerSeries ℝ) * omegaPS r (β + 1)))) *
                (PowerSeries.C ((l - a).factorial : ℝ) *
                  (PowerSeries.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)) *
                    binomPS r ((β + 1 : ℕ) : ℝ))))
            = (PowerSeries.C (Nat.choose l a : ℝ) *
                (PowerSeries.C (a.factorial : ℝ) * PowerSeries.C ((l - a).factorial : ℝ))) *
              (((Q_raw r (β + 1) a : PowerSeries ℝ) *
                ((∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a) :
                  Polynomial ℝ) : PowerSeries ℝ) *
                PowerSeries.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)) *
                (((1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a : Polynomial ℝ) :
                  PowerSeries ℝ)) *
                (omegaPS r (β + 1) * binomPS r ((β + 1 : ℕ) : ℝ))) := by ring
          _ = PowerSeries.C (l.factorial : ℝ) * _ := by rw [hfac]
      rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.sum_mul, ← coe_sum_poly]
      rfl

private lemma Tpoly_map_cast (r M : ℕ) :
    (Tpoly r M).map (Int.castRingHom ℝ) =
      Polynomial.C (r : ℝ) * ∏ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) := by
  unfold Tpoly
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  simp

private lemma Qpoly_powerSeries_eq {r M β : ℕ} (hβM : β ≤ M + 1) (l : ℕ) :
    (((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) ^ l) *
        (PowerSeries.derivative ℝ)^[l] (omegaPS r β) =
      (l.factorial : ℝ) • ((Qpoly r M β l : PowerSeries ℝ) * omegaPS r β) := by
  have hTsplit :
      (Tpoly r M).map (Int.castRingHom ℝ) =
        (Polynomial.C (r : ℝ) * ∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X)) *
        (∏ j ∈ Finset.Ico 1 β, (1 - Polynomial.C (j : ℝ) * Polynomial.X)) := by
    by_cases hβ0 : β = 0
    · subst hβ0
      have hIcc : Finset.Icc 0 M = insert 0 (Finset.Icc 1 M) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have h0not : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
      rw [Tpoly_map_cast, hIcc, Finset.prod_insert h0not]
      simp
    · have hsplit : Finset.Icc 1 M = Finset.Icc β M ∪ Finset.Ico 1 β := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico]; omega
      have hdisj : Disjoint (Finset.Icc β M) (Finset.Ico 1 β) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        simp only [Finset.mem_Icc, Finset.mem_Ico] at hj1 hj2
        omega
      rw [Tpoly_map_cast, hsplit, Finset.prod_union hdisj, mul_assoc]
  rw [hTsplit, Polynomial.coe_mul, mul_pow, mul_assoc, Q_raw_powerSeries_eq, mul_smul_comm]
  congr 1
  rw [← mul_assoc]
  congr 1
  unfold Qpoly
  simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, mul_pow, ← map_pow,
    Finset.prod_pow]

theorem P_ang_powerSeries_eq {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    (hβ1 : 1 ≤ β₁) (hβ1M : β₁ ≤ M) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (k : ℕ) (i : Fin 3) :
    (((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) ^ k) *
        ((PowerSeries.derivative ℝ)^[k]
          (((P i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i)) =
      (k.factorial : ℝ) • ((P_ang r M β₁ β₂ P k i : PowerSeries ℝ) * omega3PS r β₁ β₂ i) := by
  have _ := hr
  have _ := hM
  have _ := hβ1
  have hβ_le : beta3 β₁ β₂ i ≤ M + 1 := by
    fin_cases i <;> simp [beta3] <;> omega
  set T_ps : PowerSeries ℝ := ((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ)
  set P_R : Polynomial ℝ := (P i).map (Int.castRingHom ℝ)
  rw [mul_comm (P_R : PowerSeries ℝ) (omega3PS r β₁ β₂ i), ps_iterate_deriv_mul, Finset.mul_sum]
  have hterm : ∀ l ∈ Finset.range (k + 1),
      T_ps ^ k *
        ((Nat.choose k l : ℝ) •
          ((PowerSeries.derivative ℝ)^[l] (omega3PS r β₁ β₂ i) *
            (PowerSeries.derivative ℝ)^[k - l] (P_R : PowerSeries ℝ))) =
      (k.factorial : ℝ) •
        ((((((Tpoly r M).map (Int.castRingHom ℝ)) ^ (k - l) *
            Polynomial.C (1 / ((k - l).factorial : ℝ)) *
            (Polynomial.derivative^[k - l] P_R)) *
          Qpoly r M (beta3 β₁ β₂ i) l : Polynomial ℝ) : PowerSeries ℝ) *
          omega3PS r β₁ β₂ i) := by
    intro l hl
    have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hTk : T_ps ^ k = T_ps ^ (k - l) * T_ps ^ l := by
      rw [← pow_add, Nat.sub_add_cancel hlk]
    rw [mul_smul_comm, hTk]
    have hre :
        T_ps ^ (k - l) * T_ps ^ l *
          ((PowerSeries.derivative ℝ)^[l] (omega3PS r β₁ β₂ i) *
            (PowerSeries.derivative ℝ)^[k - l] (P_R : PowerSeries ℝ)) =
        T_ps ^ (k - l) * (PowerSeries.derivative ℝ)^[k - l] (P_R : PowerSeries ℝ) *
          (T_ps ^ l * (PowerSeries.derivative ℝ)^[l] (omega3PS r β₁ β₂ i)) := by ring
    rw [hre, ps_iterate_deriv_coe]
    change (Nat.choose k l : ℝ) •
        (T_ps ^ (k - l) * ((Polynomial.derivative^[k - l] P_R : Polynomial ℝ) : PowerSeries ℝ) *
          (T_ps ^ l * (PowerSeries.derivative ℝ)^[l] (omegaPS r (beta3 β₁ β₂ i)))) = _
    rw [Qpoly_powerSeries_eq hβ_le l]
    have hfac : (Nat.choose k l : ℝ) * (l.factorial : ℝ) =
        (k.factorial : ℝ) * (1 / ((k - l).factorial : ℝ)) := by
      have h0 : ((k - l).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h1 : (Nat.choose k l : ℝ) * (l.factorial : ℝ) * ((k - l).factorial : ℝ) =
          (k.factorial : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hlk
      field_simp [h0]
      linarith
    simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C]
    have hCeq :
        PowerSeries.C (Nat.choose k l : ℝ) * PowerSeries.C (l.factorial : ℝ) =
        PowerSeries.C (k.factorial : ℝ) * PowerSeries.C (1 / ((k - l).factorial : ℝ)) := by
      rw [← map_mul, ← map_mul, hfac]
    calc PowerSeries.C (Nat.choose k l : ℝ) *
          (T_ps ^ (k - l) * ((Polynomial.derivative^[k - l] P_R : Polynomial ℝ) : PowerSeries ℝ) *
            (PowerSeries.C (l.factorial : ℝ) *
              ((Qpoly r M (beta3 β₁ β₂ i) l : PowerSeries ℝ) * omegaPS r (beta3 β₁ β₂ i))))
        = (PowerSeries.C (Nat.choose k l : ℝ) * PowerSeries.C (l.factorial : ℝ)) *
          (T_ps ^ (k - l) * ((Polynomial.derivative^[k - l] P_R : Polynomial ℝ) : PowerSeries ℝ) *
            (Qpoly r M (beta3 β₁ β₂ i) l : PowerSeries ℝ) * omega3PS r β₁ β₂ i) := by
          unfold omega3PS; ring
      _ = (PowerSeries.C (k.factorial : ℝ) * PowerSeries.C (1 / ((k - l).factorial : ℝ))) * _ := by
          rw [hCeq]
      _ = PowerSeries.C (k.factorial : ℝ) * _ := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.smul_sum, ← Finset.sum_mul, ← coe_sum_poly]
  rfl

theorem R_ps_deriv_eq_P_ang {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    (hβ1 : 1 ≤ β₁) (hβ1M : β₁ ≤ M) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (k : ℕ) :
    (((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) ^ k) *
        ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) =
      (k.factorial : ℝ) • ∑ i : Fin 3,
        (P_ang r M β₁ β₂ P k i : PowerSeries ℝ) * omega3PS r β₁ β₂ i := by
  unfold R_ps
  rw [ps_iterate_deriv_sum, Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact P_ang_powerSeries_eq hr hM hβ1 hβ1M hβ2 P k i

/- Part 2C: Generalized differential equation and shifted `P_sq` identities. -/

private noncomputable def T_gen (r : ℕ) (S : Finset ℕ) (lam : ℕ → ℝ) : Polynomial ℝ :=
  Polynomial.C (r : ℝ) * ∏ j ∈ S, (1 - Polynomial.C (lam j) * Polynomial.X)

private noncomputable def TA_gen (S I : Finset ℕ) (lam : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ I, Polynomial.C (lam j) * ∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X)

private noncomputable def omega_gen (r : ℕ) (I : Finset ℕ) (lam : ℕ → ℝ) : PowerSeries ℝ :=
  ∏ j ∈ I, binomPS r (lam j)

private lemma omega_gen_constantCoeff (r : ℕ) (I : Finset ℕ) (lam : ℕ → ℝ) :
    PowerSeries.constantCoeff (omega_gen r I lam) = 1 := by
  unfold omega_gen
  rw [map_prod]
  exact Finset.prod_eq_one fun j _ => binomPS_constantCoeff r (lam j)

private lemma omega_gen_ne_zero (r : ℕ) (I : Finset ℕ) (lam : ℕ → ℝ) :
    omega_gen r I lam ≠ 0 := by
  intro h
  have h1 := congrArg PowerSeries.constantCoeff h
  rw [omega_gen_constantCoeff, map_zero] at h1
  exact one_ne_zero h1

private lemma T_gen_deriv_omega_gen {r : ℕ} (hr : 1 ≤ r) {S I : Finset ℕ} (hIS : I ⊆ S)
    (lam : ℕ → ℝ) :
    (T_gen r S lam : PowerSeries ℝ) * PowerSeries.derivative ℝ (omega_gen r I lam) =
      (TA_gen S I lam : PowerSeries ℝ) * omega_gen r I lam := by
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold omega_gen
  rw [ps_deriv_prod, Finset.mul_sum]
  unfold TA_gen
  rw [coe_sum_poly, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjS : j ∈ S := hIS hj
  have hT_split :
      (T_gen r S lam : PowerSeries ℝ) =
        PowerSeries.C (r : ℝ) *
          ((∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X) : Polynomial ℝ) :
            PowerSeries ℝ) *
          (1 - PowerSeries.C (lam j) * PowerSeries.X) := by
    unfold T_gen
    rw [← Finset.mul_prod_erase S _ hjS]
    simp only [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_X]
    ring
  have hprod_j : binomPS r (lam j) * ∏ l ∈ I.erase j, binomPS r (lam l) =
      ∏ l ∈ I, binomPS r (lam l) :=
    Finset.mul_prod_erase I (fun l => binomPS r (lam l)) hj
  rw [hT_split]
  have hre :
      PowerSeries.C (r : ℝ) *
        ((∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X) : Polynomial ℝ) :
          PowerSeries ℝ) *
        (1 - PowerSeries.C (lam j) * PowerSeries.X) *
        (PowerSeries.derivative ℝ (binomPS r (lam j)) * ∏ l ∈ I.erase j, binomPS r (lam l)) =
      PowerSeries.C (r : ℝ) *
        ((∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X) : Polynomial ℝ) :
          PowerSeries ℝ) *
        ((1 - PowerSeries.C (lam j) * PowerSeries.X) *
          PowerSeries.derivative ℝ (binomPS r (lam j))) *
        ∏ l ∈ I.erase j, binomPS r (lam l) := by ring
  rw [hre, binomPS_diff_eq]
  simp only [Polynomial.coe_mul, Polynomial.coe_C]
  have hCr : PowerSeries.C (r : ℝ) * PowerSeries.C (lam j / (r : ℝ)) = PowerSeries.C (lam j) := by
    rw [← map_mul, mul_div_cancel₀ _ hr0]
  calc PowerSeries.C (r : ℝ) *
        ((∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X) : Polynomial ℝ) :
          PowerSeries ℝ) *
        (PowerSeries.C (lam j / (r : ℝ)) * binomPS r (lam j)) *
        ∏ l ∈ I.erase j, binomPS r (lam l)
      = (PowerSeries.C (r : ℝ) * PowerSeries.C (lam j / (r : ℝ))) *
        ((∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X) : Polynomial ℝ) :
          PowerSeries ℝ) *
        (binomPS r (lam j) * ∏ l ∈ I.erase j, binomPS r (lam l)) := by ring
    _ = PowerSeries.C (lam j) *
        ((∏ l ∈ S.erase j, (1 - Polynomial.C (lam l) * Polynomial.X) : Polynomial ℝ) :
          PowerSeries ℝ) *
        ∏ l ∈ I, binomPS r (lam l) := by rw [hCr, hprod_j]

private lemma TApoly_map_cast (r M β : ℕ) :
    (TApoly r M β).map (Int.castRingHom ℝ) =
      TA_gen (Finset.Icc 1 M) (Finset.Ico 1 β) (fun j => (j : ℝ)) := by
  unfold TApoly TA_gen
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod]
  simp

private lemma Tpoly_deriv_omegaPS {r M β : ℕ} (hr : 1 ≤ r) (hβM : β ≤ M + 1) :
    ((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
        PowerSeries.derivative ℝ (omegaPS r β) =
      ((TApoly r M β).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omegaPS r β := by
  have hsub : Finset.Ico 1 β ⊆ Finset.Icc 1 M := by
    intro j hj
    simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢
    omega
  rw [Tpoly_map_cast, TApoly_map_cast]
  exact T_gen_deriv_omega_gen hr hsub (fun j => (j : ℝ))

private lemma Tpoly_shift_deriv_omega {r M β : ℕ} (hr : 1 ≤ r) (hβM : β ≤ M + 1)
    {α : ℝ} (hα : ∀ j ∈ Finset.Icc 1 M, 1 - (j : ℝ) * α ≠ 0) :
    let lam : ℕ → ℝ := fun j => (j : ℝ) / (1 - (j : ℝ) * α)
    ((((Tpoly r M).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) : Polynomial ℝ) :
        PowerSeries ℝ) *
      PowerSeries.derivative ℝ (omega_gen r (Finset.Ico 1 β) lam) =
    ((((TApoly r M β).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) : Polynomial ℝ) :
        PowerSeries ℝ) *
      omega_gen r (Finset.Ico 1 β) lam := by
  intro lam
  set c : ℕ → ℝ := fun j => 1 - (j : ℝ) * α
  set K : ℝ := ∏ j ∈ Finset.Icc 1 M, c j
  have hlin : ∀ j ∈ Finset.Icc 1 M,
      (1 - Polynomial.C (j : ℝ) * Polynomial.X).comp (Polynomial.C α + Polynomial.X) =
        Polynomial.C (c j) * (1 - Polynomial.C (lam j) * Polynomial.X) := by
    intro j hj
    have hcj : c j ≠ 0 := hα j hj
    rw [Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_comp, mul_sub, mul_one, ← mul_assoc, ← map_mul]
    have hmul : c j * lam j = (j : ℝ) := mul_div_cancel₀ (j : ℝ) hcj
    rw [hmul]
    simp only [c, map_sub, map_one, map_mul]
    ring
  have hTshift :
      ((Tpoly r M).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) =
        Polynomial.C K * T_gen r (Finset.Icc 1 M) lam := by
    rw [Tpoly_map_cast, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.prod_comp]
    rw [Finset.prod_congr rfl hlin, Finset.prod_mul_distrib]
    unfold T_gen K
    rw [map_prod]
    ring
  have hTAshift :
      ((TApoly r M β).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) =
        Polynomial.C K * TA_gen (Finset.Icc 1 M) (Finset.Ico 1 β) lam := by
    rw [TApoly_map_cast]
    unfold TA_gen
    rw [Polynomial.sum_comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjM : j ∈ Finset.Icc 1 M := by
      simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢; omega
    have hcj : c j ≠ 0 := hα j hjM
    rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.prod_comp]
    have hlin' : ∀ l ∈ (Finset.Icc 1 M).erase j,
        (1 - Polynomial.C (l : ℝ) * Polynomial.X).comp (Polynomial.C α + Polynomial.X) =
          Polynomial.C (c l) * (1 - Polynomial.C (lam l) * Polynomial.X) :=
      fun l hl => hlin l (Finset.mem_of_mem_erase hl)
    rw [Finset.prod_congr rfl hlin', Finset.prod_mul_distrib]
    have hK : K * lam j = (j : ℝ) * ∏ l ∈ (Finset.Icc 1 M).erase j, c l := by
      have hKsplit : K = c j * ∏ l ∈ (Finset.Icc 1 M).erase j, c l :=
        (Finset.mul_prod_erase (Finset.Icc 1 M) c hjM).symm
      rw [hKsplit]
      have hmul : c j * lam j = (j : ℝ) := mul_div_cancel₀ (j : ℝ) hcj
      calc c j * (∏ l ∈ (Finset.Icc 1 M).erase j, c l) * lam j
          = (c j * lam j) * ∏ l ∈ (Finset.Icc 1 M).erase j, c l := by ring
        _ = (j : ℝ) * ∏ l ∈ (Finset.Icc 1 M).erase j, c l := by rw [hmul]
    have hCprod : ∏ l ∈ (Finset.Icc 1 M).erase j, Polynomial.C (c l) =
        Polynomial.C (∏ l ∈ (Finset.Icc 1 M).erase j, c l) := (map_prod Polynomial.C _ _).symm
    rw [hCprod]
    calc Polynomial.C (j : ℝ) *
          (Polynomial.C (∏ l ∈ (Finset.Icc 1 M).erase j, c l) *
            ∏ l ∈ (Finset.Icc 1 M).erase j, (1 - Polynomial.C (lam l) * Polynomial.X))
        = Polynomial.C ((j : ℝ) * ∏ l ∈ (Finset.Icc 1 M).erase j, c l) *
            ∏ l ∈ (Finset.Icc 1 M).erase j, (1 - Polynomial.C (lam l) * Polynomial.X) := by
          rw [map_mul]; ring
      _ = Polynomial.C (K * lam j) *
            ∏ l ∈ (Finset.Icc 1 M).erase j, (1 - Polynomial.C (lam l) * Polynomial.X) := by
          rw [hK]
      _ = Polynomial.C K *
            (Polynomial.C (lam j) *
              ∏ l ∈ (Finset.Icc 1 M).erase j, (1 - Polynomial.C (lam l) * Polynomial.X)) := by
          rw [map_mul]; ring
  have hsub : Finset.Ico 1 β ⊆ Finset.Icc 1 M := by
    intro j hj; simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢; omega
  rw [hTshift, hTAshift, Polynomial.coe_mul, Polynomial.coe_mul, mul_assoc, mul_assoc,
    T_gen_deriv_omega_gen hr hsub lam]

private lemma comp_shift_derivative (p : Polynomial ℝ) (α : ℝ) :
    (p.comp (Polynomial.C α + Polynomial.X)).derivative =
      p.derivative.comp (Polynomial.C α + Polynomial.X) := by
  rw [Polynomial.derivative_comp]
  simp

private lemma P_sq_shift_iter_eq {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hβ1M : β₁ ≤ M + 1)
    (hβ2M : β₂ ≤ M + 1) (P : Fin 3 → Polynomial ℤ)
    {α : ℝ} (hα : ∀ j ∈ Finset.Icc 1 M, 1 - (j : ℝ) * α ≠ 0) (k : ℕ) (i : Fin 3) :
    let lam : ℕ → ℝ := fun j => (j : ℝ) / (1 - (j : ℝ) * α)
    let T_s : Polynomial ℝ :=
      ((Tpoly r M).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X)
    let ω_s : PowerSeries ℝ := omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam
    (fun F => (T_s : PowerSeries ℝ) * PowerSeries.derivative ℝ F)^[k]
        ((((P i).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) : PowerSeries ℝ) *
          ω_s) =
      ((((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) :
        PowerSeries ℝ) * ω_s) := by
  intro lam T_s ω_s
  have hβM : beta3 β₁ β₂ i ≤ M + 1 := by
    fin_cases i <;> simp [beta3] <;> omega
  induction k with
  | zero =>
    simp [P_sq]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ps_deriv_mul, mul_add, PowerSeries.derivative_coe]
    have hre :
        (T_s : PowerSeries ℝ) *
          ((((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) :
            PowerSeries ℝ) * PowerSeries.derivative ℝ ω_s) =
        (((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ)).comp (Polynomial.C α + Polynomial.X) :
          PowerSeries ℝ) * ((T_s : PowerSeries ℝ) * PowerSeries.derivative ℝ ω_s) := by ring
    rw [hre, Tpoly_shift_deriv_omega hr hβM hα, comp_shift_derivative]
    simp only [P_sq, Polynomial.map_add, Polynomial.map_mul, Polynomial.derivative_map,
      Polynomial.add_comp, Polynomial.mul_comp, Polynomial.coe_add, Polynomial.coe_mul, T_s, TA3]
    ring

private lemma P_sq_iter_eq {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hβ1M : β₁ ≤ M + 1)
    (hβ2M : β₂ ≤ M + 1) (P : Fin 3 → Polynomial ℤ) (k : ℕ) (i : Fin 3) :
    (fun F => ((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
        PowerSeries.derivative ℝ F)^[k]
        (((P i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) =
      ((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i := by
  have h0 : ∀ j ∈ Finset.Icc 1 M, 1 - (j : ℝ) * (0 : ℝ) ≠ 0 := by
    intro j _; norm_num
  have h := P_sq_shift_iter_eq hr hβ1M hβ2M P h0 k i
  have hlam : (fun j : ℕ => (j : ℝ) / (1 - (j : ℝ) * (0 : ℝ))) = fun j : ℕ => (j : ℝ) := by
    ext j; simp
  simpa [hlam, omega_gen, omega3PS, omegaPS] using h

private lemma R_ps_iter_eq {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hβ1M : β₁ ≤ M + 1)
    (hβ2M : β₂ ≤ M + 1) (P : Fin 3 → Polynomial ℤ) (k : ℕ) :
    (fun F => ((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
        PowerSeries.derivative ℝ F)^[k] (R_ps r β₁ β₂ P) =
      ∑ i : Fin 3,
        ((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
          omega3PS r β₁ β₂ i := by
  have hadd : ∀ (A : PowerSeries ℝ) (n : ℕ) (F G : PowerSeries ℝ),
      (fun H => A * PowerSeries.derivative ℝ H)^[n] (F + G) =
        (fun H => A * PowerSeries.derivative ℝ H)^[n] F +
        (fun H => A * PowerSeries.derivative ℝ H)^[n] G := by
    intro A n F G
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
        ih, map_add, mul_add]
  have hsum : ∀ (A : PowerSeries ℝ) (n : ℕ) (f : Fin 3 → PowerSeries ℝ),
      (fun H => A * PowerSeries.derivative ℝ H)^[n] (∑ i : Fin 3, f i) =
        ∑ i : Fin 3, (fun H => A * PowerSeries.derivative ℝ H)^[n] (f i) := by
    intro A n f
    simp only [Fin.sum_univ_three, hadd]
  unfold R_ps
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => P_sq_iter_eq hr hβ1M hβ2M P k i

/- Part 2D: Purely algebraic linear independence of shifted omega series over `Polynomial ℝ`. -/

private lemma rootMultiplicity_one_sub_C_mul_X {c : ℝ} (hc : c ≠ 0) :
    (1 - Polynomial.C c * Polynomial.X).rootMultiplicity c⁻¹ = 1 := by
  have hfac : 1 - Polynomial.C c * Polynomial.X =
      Polynomial.C (-c) * (Polynomial.X - Polynomial.C c⁻¹) := by
    simp only [mul_sub, ← map_mul, neg_mul, mul_inv_cancel₀ hc, map_neg, map_one]
    ring
  rw [hfac, Polynomial.rootMultiplicity_mul]
  · have h1 : (Polynomial.C (-c)).rootMultiplicity c⁻¹ = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff]
      intro h
      simp [Polynomial.IsRoot, hc] at h
    have h2 : (Polynomial.X - Polynomial.C c⁻¹).rootMultiplicity c⁻¹ = 1 :=
      Polynomial.rootMultiplicity_X_sub_C_self
    rw [h1, h2, zero_add]
  · exact mul_ne_zero (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr hc)) (Polynomial.X_sub_C_ne_zero _)

private lemma rootMultiplicity_pow_eq (p : Polynomial ℝ) (y : ℝ) (n : ℕ) :
    (p ^ n).rootMultiplicity y = n * p.rootMultiplicity y := by
  by_cases hp : p = 0
  · subst hp
    cases n with
    | zero => simp
    | succ n => simp [zero_pow (Nat.succ_ne_zero n)]
  · induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hp) hp), ih]
      ring

private lemma omega_gen_lin_indep_two {r β : ℕ} (hr : 2 ≤ r) (hβ : 2 ≤ β)
    {lam : ℕ → ℝ} (hlam_ne : ∀ j ∈ Finset.Ico 1 β, lam j ≠ 0)
    (hlam_inj : Set.InjOn lam (Finset.Ico 1 β))
    {U V : Polynomial ℝ}
    (hrel : (U : PowerSeries ℝ) + (V : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 β) lam = 0) :
    U = 0 ∧ V = 0 := by
  by_cases hV : V = 0
  · subst hV
    simp only [Polynomial.coe_zero, zero_mul, add_zero] at hrel
    exact ⟨Polynomial.coe_injective ℝ hrel, rfl⟩
  exfalso
  have hU : U ≠ 0 := by
    intro hU0
    subst hU0
    simp only [Polynomial.coe_zero, zero_add] at hrel
    have hVps : (V : PowerSeries ℝ) = 0 :=
      (mul_eq_zero.mp hrel).resolve_right (omega_gen_ne_zero r _ lam)
    exact hV (Polynomial.coe_injective ℝ hVps)
  have heq1 : ((-U : Polynomial ℝ) : PowerSeries ℝ) =
      (V : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 β) lam := by
    rw [Polynomial.coe_neg]
    exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; linear_combination -hrel)
  have heq_pow := congrArg (fun F => F ^ r) heq1
  rw [mul_pow, ← Polynomial.coe_pow, ← Polynomial.coe_pow] at heq_pow
  set Q : Polynomial ℝ := ∏ j ∈ Finset.Ico 1 β, (1 - Polynomial.C (lam j) * Polynomial.X)
  have hQ_omega : (Q : PowerSeries ℝ) * (omega_gen r (Finset.Ico 1 β) lam) ^ r = 1 := by
    unfold Q omega_gen
    rw [coe_prod_poly, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun j _ => ?_
    simpa [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X] using binomPS_pow_r_eq_one (by omega : 1 ≤ r) (lam j)
  have hpoly_ps : (((-U) ^ r * Q : Polynomial ℝ) : PowerSeries ℝ) = ((V ^ r : Polynomial ℝ) : PowerSeries ℝ) := by
    calc (((-U) ^ r * Q : Polynomial ℝ) : PowerSeries ℝ)
        = ((V ^ r : Polynomial ℝ) : PowerSeries ℝ) *
            ((Q : PowerSeries ℝ) * (omega_gen r (Finset.Ico 1 β) lam) ^ r) := by
          rw [Polynomial.coe_mul, heq_pow]; ring
      _ = ((V ^ r : Polynomial ℝ) : PowerSeries ℝ) := by rw [hQ_omega, mul_one]
  have hpoly : (-U) ^ r * Q = V ^ r := Polynomial.coe_injective ℝ hpoly_ps
  have h1mem : 1 ∈ Finset.Ico 1 β := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  have hlam1 : lam 1 ≠ 0 := hlam_ne 1 h1mem
  set y0 : ℝ := (lam 1)⁻¹
  have hQ_ne : Q ≠ 0 := by
    intro hQ0
    have hev := congrArg (Polynomial.eval 0) hQ0
    simp only [Q, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, mul_zero, sub_zero,
      Finset.prod_const_one, Polynomial.eval_zero] at hev
    exact one_ne_zero hev
  have hQ_mult : Q.rootMultiplicity y0 = 1 := by
    have hQsplit : Q = (1 - Polynomial.C (lam 1) * Polynomial.X) *
        ∏ j ∈ (Finset.Ico 1 β).erase 1, (1 - Polynomial.C (lam j) * Polynomial.X) :=
      (Finset.mul_prod_erase (Finset.Ico 1 β) _ h1mem).symm
    have hR_eval : (∏ j ∈ (Finset.Ico 1 β).erase 1,
        (1 - Polynomial.C (lam j) * Polynomial.X)).eval y0 ≠ 0 := by
      rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro j hj
      have hj_ne : j ≠ 1 := (Finset.mem_erase.mp hj).1
      have hj_mem : j ∈ Finset.Ico 1 β := Finset.mem_of_mem_erase hj
      simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      intro hzero
      have hmul : lam j * y0 = 1 := sub_eq_zero.mp hzero |>.symm
      have hlam_eq : lam j = lam 1 := by
        have := congrArg (· * lam 1) hmul
        dsimp only [y0] at this
        rw [mul_assoc, inv_mul_cancel₀ hlam1, mul_one, one_mul] at this
        exact this
      exact hj_ne (hlam_inj hj_mem h1mem hlam_eq)
    have hR_ne : (∏ j ∈ (Finset.Ico 1 β).erase 1, (1 - Polynomial.C (lam j) * Polynomial.X)) ≠ 0 :=
      fun h0 => hR_eval (by rw [h0, Polynomial.eval_zero])
    have h1_ne : (1 - Polynomial.C (lam 1) * Polynomial.X) ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.eval 0) h0
      simp at this
    rw [hQsplit, Polynomial.rootMultiplicity_mul (mul_ne_zero h1_ne hR_ne),
      rootMultiplicity_one_sub_C_mul_X hlam1]
    have hR_mult : (∏ j ∈ (Finset.Ico 1 β).erase 1,
        (1 - Polynomial.C (lam j) * Polynomial.X)).rootMultiplicity y0 = 0 := by
      rw [Polynomial.rootMultiplicity_eq_zero_iff]
      intro hroot
      exact absurd hroot hR_eval
    rw [hR_mult, add_zero]
  have hmult := congrArg (Polynomial.rootMultiplicity y0) hpoly
  rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero r (neg_ne_zero.mpr hU)) hQ_ne),
    rootMultiplicity_pow_eq, rootMultiplicity_pow_eq, hQ_mult] at hmult
  have hmod := congrArg (· % r) hmult
  simp only [Nat.mul_add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt (by omega : 1 < r)] at hmod
  exact one_ne_zero hmod

private lemma linear_mul_deriv_pow_mul (y : ℝ) (n : ℕ) (F : Polynomial ℝ) :
    (Polynomial.X - Polynomial.C y) * ((Polynomial.X - Polynomial.C y) ^ n * F).derivative =
      (Polynomial.X - Polynomial.C y) ^ n *
        (Polynomial.C (n : ℝ) * F + (Polynomial.X - Polynomial.C y) * F.derivative) := by
  set q : Polynomial ℝ := Polynomial.X - Polynomial.C y
  have hq : q.derivative = 1 := by simp [q]
  cases n with
  | zero =>
    simp [q]
  | succ n =>
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow, hq]
    simp only [Nat.add_sub_cancel, mul_one, Polynomial.C_eq_natCast]
    rw [pow_succ']
    ring

private lemma omega_gen_lin_indep_three {r β₁ β₂ : ℕ} (hr : 2 ≤ r) (hβ1 : 2 ≤ β₁) (hβ12 : β₁ < β₂)
    {lam : ℕ → ℝ} (hlam_ne : ∀ j ∈ Finset.Ico 1 β₂, lam j ≠ 0)
    (hlam_inj : Set.InjOn lam (Finset.Ico 1 β₂))
    {U V W : Polynomial ℝ}
    (hrel : (U : PowerSeries ℝ) +
        (V : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 β₁) lam +
        (W : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 β₂) lam = 0) :
    U = 0 ∧ V = 0 ∧ W = 0 := by
  have hsub1 : Finset.Ico 1 β₁ ⊆ Finset.Ico 1 β₂ := by
    intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
  have hlam1_ne : ∀ j ∈ Finset.Ico 1 β₁, lam j ≠ 0 := fun j hj => hlam_ne j (hsub1 hj)
  have hlam1_inj : Set.InjOn lam (Finset.Ico 1 β₁) := hlam_inj.mono (by exact_mod_cast hsub1)
  by_cases hW : W = 0
  · subst hW
    simp only [Polynomial.coe_zero, zero_mul, add_zero] at hrel
    obtain ⟨hU, hV⟩ := omega_gen_lin_indep_two hr hβ1 hlam1_ne hlam1_inj hrel
    exact ⟨hU, hV, rfl⟩
  by_cases hV : V = 0
  · subst hV
    simp only [Polynomial.coe_zero, zero_mul, add_zero] at hrel
    obtain ⟨hU, hW0⟩ := omega_gen_lin_indep_two hr (by omega : 2 ≤ β₂) hlam_ne hlam_inj hrel
    exact ⟨hU, rfl, hW0⟩
  exfalso
  set S2 : Finset ℕ := Finset.Ico 1 β₂
  set S1 : Finset ℕ := Finset.Ico 1 β₁
  set Tt : Polynomial ℝ := T_gen r S2 lam
  set TA1 : Polynomial ℝ := TA_gen S2 S1 lam
  set TA2 : Polynomial ℝ := TA_gen S2 S2 lam
  set ω1 : PowerSeries ℝ := omega_gen r S1 lam
  set ω2 : PowerSeries ℝ := omega_gen r S2 lam
  have hd1 : (Tt : PowerSeries ℝ) * PowerSeries.derivative ℝ ω1 = (TA1 : PowerSeries ℝ) * ω1 :=
    T_gen_deriv_omega_gen (by omega : 1 ≤ r) hsub1 lam
  have hd2 : (Tt : PowerSeries ℝ) * PowerSeries.derivative ℝ ω2 = (TA2 : PowerSeries ℝ) * ω2 :=
    T_gen_deriv_omega_gen (by omega : 1 ≤ r) (Finset.Subset.refl _) lam
  have hdiff :
      ((Tt * U.derivative : Polynomial ℝ) : PowerSeries ℝ) +
      ((Tt * V.derivative + TA1 * V : Polynomial ℝ) : PowerSeries ℝ) * ω1 +
      ((Tt * W.derivative + TA2 * W : Polynomial ℝ) : PowerSeries ℝ) * ω2 = 0 := by
    have h0 := congrArg (fun F => (Tt : PowerSeries ℝ) * PowerSeries.derivative ℝ F) hrel
    rw [map_zero, mul_zero, map_add, map_add, ps_deriv_mul, ps_deriv_mul,
      PowerSeries.derivative_coe, PowerSeries.derivative_coe, PowerSeries.derivative_coe] at h0
    have hcalc :
        (Tt : PowerSeries ℝ) *
          ((U.derivative : PowerSeries ℝ) +
            ((V.derivative : PowerSeries ℝ) * ω1 + (V : PowerSeries ℝ) * PowerSeries.derivative ℝ ω1) +
            ((W.derivative : PowerSeries ℝ) * ω2 + (W : PowerSeries ℝ) * PowerSeries.derivative ℝ ω2)) =
        (Tt : PowerSeries ℝ) * (U.derivative : PowerSeries ℝ) +
        ((Tt : PowerSeries ℝ) * (V.derivative : PowerSeries ℝ) * ω1 +
          (V : PowerSeries ℝ) * ((Tt : PowerSeries ℝ) * PowerSeries.derivative ℝ ω1)) +
        ((Tt : PowerSeries ℝ) * (W.derivative : PowerSeries ℝ) * ω2 +
          (W : PowerSeries ℝ) * ((Tt : PowerSeries ℝ) * PowerSeries.derivative ℝ ω2)) := by ring
    rw [hcalc, hd1, hd2] at h0
    simp only [Polynomial.coe_add, Polynomial.coe_mul]
    linear_combination h0
  set Q0 : Polynomial ℝ := W * (Tt * U.derivative) - (Tt * W.derivative + TA2 * W) * U
  set Q1 : Polynomial ℝ := Tt * (W * V.derivative - W.derivative * V) + (TA1 - TA2) * W * V
  have hQrel : (Q0 : PowerSeries ℝ) + (Q1 : PowerSeries ℝ) * ω1 = 0 := by
    have helim :
        (W : PowerSeries ℝ) *
          (((Tt * U.derivative : Polynomial ℝ) : PowerSeries ℝ) +
            ((Tt * V.derivative + TA1 * V : Polynomial ℝ) : PowerSeries ℝ) * ω1 +
            ((Tt * W.derivative + TA2 * W : Polynomial ℝ) : PowerSeries ℝ) * ω2) -
        ((Tt * W.derivative + TA2 * W : Polynomial ℝ) : PowerSeries ℝ) *
          ((U : PowerSeries ℝ) + (V : PowerSeries ℝ) * ω1 + (W : PowerSeries ℝ) * ω2) = 0 := by
      rw [hdiff, hrel]; ring
    simp only [Q0, Q1, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_mul] at helim ⊢
    linear_combination helim
  have hQ1 : Q1 = 0 := (omega_gen_lin_indep_two hr hβ1 hlam1_ne hlam1_inj hQrel).2
  have hβ1_mem : β₁ ∈ S2 := by simp [S2, hβ12]; omega
  have hlamβ : lam β₁ ≠ 0 := hlam_ne β₁ hβ1_mem
  set y : ℝ := (lam β₁)⁻¹
  set q : Polynomial ℝ := Polynomial.X - Polynomial.C y
  obtain ⟨V1, hV_eq, hV1_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd V hV y
  obtain ⟨W1, hW_eq, hW1_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd W hW y
  set a : ℕ := V.rootMultiplicity y
  set b : ℕ := W.rootMultiplicity y
  have hV1_ev : V1.eval y ≠ 0 := by rwa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] at hV1_ndvd
  have hW1_ev : W1.eval y ≠ 0 := by rwa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] at hW1_ndvd
  set Pstar : Polynomial ℝ := ∏ l ∈ S2.erase β₁, (1 - Polynomial.C (lam l) * Polynomial.X)
  have hPstar_ev : Pstar.eval y ≠ 0 := by
    rw [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro l hl
    have hl_ne : l ≠ β₁ := (Finset.mem_erase.mp hl).1
    have hl_mem : l ∈ S2 := Finset.mem_of_mem_erase hl
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    intro hzero
    have hmul : lam l * y = 1 := (sub_eq_zero.mp hzero).symm
    have hlam_eq : lam l = lam β₁ := by
      have := congrArg (· * lam β₁) hmul
      dsimp only [y] at this
      rw [mul_assoc, inv_mul_cancel₀ hlamβ, mul_one, one_mul] at this
      exact this
    exact hl_ne (hlam_inj hl_mem hβ1_mem hlam_eq)
  set S : Polynomial ℝ := Polynomial.C ((r : ℝ) * (-lam β₁)) * Pstar
  have hTt_fac : Tt = q * S := by
    unfold Tt T_gen
    rw [← Finset.mul_prod_erase S2 _ hβ1_mem]
    have hlin : 1 - Polynomial.C (lam β₁) * Polynomial.X = Polynomial.C (-lam β₁) * q := by
      simp only [q, y, mul_sub, ← map_mul, neg_mul, mul_inv_cancel₀ hlamβ, map_neg, map_one]
      ring
    rw [hlin]
    simp only [S, Pstar, map_mul]
    ring
  have hTA1_ev : TA1.eval y = 0 := by
    unfold TA1 TA_gen
    rw [Polynomial.eval_finsetSum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj_ne : j ≠ β₁ := by simp only [S1, Finset.mem_Ico] at hj; omega
    have hβ_in : β₁ ∈ S2.erase j := Finset.mem_erase.mpr ⟨hj_ne.symm, hβ1_mem⟩
    rw [Polynomial.eval_mul, Polynomial.eval_prod]
    have hprod0 : ∏ l ∈ S2.erase j, (1 - Polynomial.C (lam l) * Polynomial.X).eval y = 0 := by
      refine Finset.prod_eq_zero hβ_in ?_
      simp [y, mul_inv_cancel₀ hlamβ]
    rw [hprod0, mul_zero]
  have hTA2_ev : TA2.eval y = lam β₁ * Pstar.eval y := by
    unfold TA2 TA_gen
    rw [Polynomial.eval_finsetSum, ← Finset.add_sum_erase _ _ hβ1_mem]
    have hrest : ∑ j ∈ S2.erase β₁,
        (Polynomial.C (lam j) * ∏ l ∈ S2.erase j, (1 - Polynomial.C (lam l) * Polynomial.X)).eval y = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj_ne : j ≠ β₁ := (Finset.mem_erase.mp hj).1
      have hβ_in : β₁ ∈ S2.erase j := Finset.mem_erase.mpr ⟨hj_ne.symm, hβ1_mem⟩
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      have hprod0 : ∏ l ∈ S2.erase j, (1 - Polynomial.C (lam l) * Polynomial.X).eval y = 0 := by
        refine Finset.prod_eq_zero hβ_in ?_
        simp [y, mul_inv_cancel₀ hlamβ]
      rw [hprod0, mul_zero]
    rw [hrest, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
  have hQ1_fac :
      Q1 = q ^ (a + b) *
        ((S * Polynomial.C ((a : ℝ) - (b : ℝ)) + (TA1 - TA2)) * V1 * W1 +
          q * S * (W1 * V1.derivative - V1 * W1.derivative)) := by
    have hqV : q * V.derivative =
        q ^ a * (Polynomial.C (a : ℝ) * V1 + q * V1.derivative) := by
      rw [hV_eq]; exact linear_mul_deriv_pow_mul y a V1
    have hqW : q * W.derivative =
        q ^ b * (Polynomial.C (b : ℝ) * W1 + q * W1.derivative) := by
      rw [hW_eq]; exact linear_mul_deriv_pow_mul y b W1
    have h1 : Tt * (W * V.derivative - W.derivative * V) =
        S * (W * (q * V.derivative) - V * (q * W.derivative)) := by
      rw [hTt_fac]; ring
    dsimp only [Q1]
    rw [h1, hqV, hqW, hV_eq, hW_eq, pow_add, map_sub]
    ring
  rw [hQ1] at hQ1_fac
  have hq_ne : q ^ (a + b) ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero y)
  have hinner :
      (S * Polynomial.C ((a : ℝ) - (b : ℝ)) + (TA1 - TA2)) * V1 * W1 +
        q * S * (W1 * V1.derivative - V1 * W1.derivative) = 0 :=
    (mul_eq_zero.mp hQ1_fac.symm).resolve_left hq_ne
  have hev := congrArg (Polynomial.eval y) hinner
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_zero, q, Polynomial.eval_X, sub_self, zero_mul, add_zero, S, hTA1_ev,
    hTA2_ev, zero_sub] at hev
  have hfac_ev :
      (-lam β₁ * Pstar.eval y) * ((r : ℝ) * ((a : ℝ) - (b : ℝ)) + 1) * V1.eval y * W1.eval y = 0 := by
    linear_combination hev
  have hlin0 : (r : ℝ) * ((a : ℝ) - (b : ℝ)) + 1 = 0 := by
    have h1 : (-lam β₁ * Pstar.eval y) * ((r : ℝ) * ((a : ℝ) - (b : ℝ)) + 1) * V1.eval y = 0 :=
      (mul_eq_zero.mp hfac_ev).resolve_right hW1_ev
    have h2 : (-lam β₁ * Pstar.eval y) * ((r : ℝ) * ((a : ℝ) - (b : ℝ)) + 1) = 0 :=
      (mul_eq_zero.mp h1).resolve_right hV1_ev
    exact (mul_eq_zero.mp h2).resolve_left (mul_ne_zero (neg_ne_zero.mpr hlamβ) hPstar_ev)
  have hint : ((r : ℤ) * ((a : ℤ) - (b : ℤ)) + 1 : ℤ) = 0 := by
    have hcast : (((r : ℤ) * ((a : ℤ) - (b : ℤ)) + 1 : ℤ) : ℝ) = 0 := by
      push_cast; exact hlin0
    exact_mod_cast hcast
  have hdvd : (r : ℤ) ∣ 1 := ⟨(b : ℤ) - (a : ℤ), by linarith⟩
  have hle : (r : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
  omega

/- Part 2E: Formal power series ODE uniqueness and `Delta_ne_zero`. -/

private lemma ascFactorial_pos_of_pos (a n : ℕ) (ha : 0 < a) : 0 < a.ascFactorial n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.ascFactorial_succ]
    exact Nat.mul_pos (by omega) ih

private lemma ps_ode_unique {μ : ℕ} (D : Fin (μ + 1) → Polynomial ℝ)
    (hD0 : (D (Fin.last μ)).coeff 0 ≠ 0) (G : PowerSeries ℝ)
    (hode : ∑ j : Fin (μ + 1), (D j : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[j.val] G = 0)
    (hinit : ∀ k < μ, PowerSeries.coeff k G = 0) :
    G = 0 := by
  ext n
  rw [map_zero]
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < μ
    · exact hinit n hn
    · push Not at hn
      set m : ℕ := n - μ
      have hmn : m + μ = n := Nat.sub_add_cancel hn
      have hcoeff := congrArg (PowerSeries.coeff m) hode
      rw [map_zero, map_sum] at hcoeff
      have hlt_zero : ∀ j : Fin (μ + 1), j ≠ Fin.last μ →
          PowerSeries.coeff m ((D j : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[j.val] G) = 0 := by
        intro j hj
        have hjlt : j.val < μ := by
          have := j.isLt
          have hne : j.val ≠ μ := fun h => hj (Fin.ext h)
          omega
        rw [PowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp2 : p.2 ≤ m := by
          have := mem_antidiagonal.mp hp; omega
        rw [PowerSeries.coeff_iterate_derivative, ih (p.2 + j.val) (by omega), mul_zero, mul_zero]
      rw [Finset.sum_eq_single (Fin.last μ) (fun j _ hj => hlt_zero j hj) (by simp)] at hcoeff
      rw [PowerSeries.coeff_mul] at hcoeff
      have h0mem : (0, m) ∈ antidiagonal m := by simp
      rw [Finset.sum_eq_single (0, m)] at hcoeff
      · simp only [Fin.val_last, Polynomial.coeff_coe, PowerSeries.coeff_iterate_derivative,
          hmn] at hcoeff
        have hasc : (((m + 1).ascFactorial μ : ℕ) : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (ascFactorial_pos_of_pos (m + 1) μ (by omega)))
        have hmul0 : (D (Fin.last μ)).coeff 0 * (((m + 1).ascFactorial μ : ℕ) : ℝ) ≠ 0 :=
          mul_ne_zero hD0 hasc
        rw [← mul_assoc] at hcoeff
        exact (mul_eq_zero.mp hcoeff).resolve_left hmul0
      · intro p hp hpne
        have hp12 : p.1 + p.2 = m := mem_antidiagonal.mp hp
        have hp2lt : p.2 < m := by
          by_contra hge
          push Not at hge
          have hp1 : p.1 = 0 := by omega
          have hp2 : p.2 = m := by omega
          exact hpne (Prod.ext hp1 hp2)
        simp only [Fin.val_last]
        rw [PowerSeries.coeff_iterate_derivative, ih (p.2 + μ) (by omega), mul_zero, mul_zero]
      · intro hnot; exact absurd h0mem hnot

private lemma ps_ode_lin_dep {μ m : ℕ} (hμm : μ < m)
    (D : Fin (μ + 1) → Polynomial ℝ) (hD0 : (D (Fin.last μ)).coeff 0 ≠ 0)
    (F : Fin m → PowerSeries ℝ)
    (hsol : ∀ i : Fin m,
      ∑ j : Fin (μ + 1), (D j : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[j.val] (F i) = 0) :
    ∃ c : Fin m → ℝ, c ≠ 0 ∧ ∑ i : Fin m, c i • F i = 0 := by
  let φ : (Fin m → ℝ) →ₗ[ℝ] (Fin μ → ℝ) :=
    { toFun := fun c k => ∑ i : Fin m, c i * PowerSeries.coeff k.val (F i)
      map_add' := fun c₁ c₂ => by
        ext k; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        ext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum] }
  have hker_pos : 0 < Module.finrank ℝ (LinearMap.ker φ) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker φ
    have hdom : Module.finrank ℝ (Fin m → ℝ) = m := Module.finrank_fin_fun ℝ
    have hrg : Module.finrank ℝ (LinearMap.range φ) ≤ μ := by
      calc Module.finrank ℝ (LinearMap.range φ)
          ≤ Module.finrank ℝ (Fin μ → ℝ) := Submodule.finrank_le _
        _ = μ := Module.finrank_fin_fun ℝ
    omega
  have hker_ne : LinearMap.ker φ ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at hker_pos
    exact lt_irrefl 0 hker_pos
  obtain ⟨c, hc_mem, hc_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨c, hc_ne, ?_⟩
  apply ps_ode_unique D hD0 (∑ i : Fin m, c i • F i)
  · have hsum :
        ∑ j : Fin (μ + 1),
          (D j : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[j.val] (∑ i : Fin m, c i • F i) =
        ∑ i : Fin m, c i •
          ∑ j : Fin (μ + 1), (D j : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[j.val] (F i) := by
      simp_rw [ps_iterate_deriv_sum, ps_iterate_deriv_smul, Finset.mul_sum, mul_smul_comm,
        Finset.smul_sum]
      exact Finset.sum_comm
    rw [hsum]
    exact Finset.sum_eq_zero fun i _ => by rw [hsol i, smul_zero]
  · intro k hk
    have h0 : φ c ⟨k, hk⟩ = 0 := congrFun (LinearMap.mem_ker.mp hc_mem) ⟨k, hk⟩
    simpa [φ, map_sum, map_smul, smul_eq_mul] using h0

private lemma poly_exists_eval_ne_zero {f : Polynomial ℝ} (hf : f ≠ 0) :
    ∃ α : ℝ, f.eval α ≠ 0 := by
  by_contra hall
  push Not at hall
  exact hf (Polynomial.funext fun x => by simp [hall x])

private lemma poly_comp_shift_ne_zero {f : Polynomial ℝ} (hf : f ≠ 0) (α : ℝ) :
    f.comp (Polynomial.C α + Polynomial.X) ≠ 0 := by
  intro h0
  have hinv : (f.comp (Polynomial.C α + Polynomial.X)).comp (Polynomial.C (-α) + Polynomial.X) = f := by
    rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
    have : Polynomial.C α + (Polynomial.C (-α) + Polynomial.X) = Polynomial.X := by
      rw [← add_assoc, ← map_add, add_neg_cancel, map_zero, zero_add]
    rw [this, Polynomial.comp_X]
  rw [h0, Polynomial.zero_comp] at hinv
  exact hf hinv.symm

private lemma Tpoly_map_cast_ne_zero {r M : ℕ} (hr : 1 ≤ r) :
    (Tpoly r M).map (Int.castRingHom ℝ) ≠ 0 := by
  intro h0
  have hev := congrArg (Polynomial.eval 0) h0
  rw [Tpoly_map_cast] at hev
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, mul_zero, sub_zero, Finset.prod_const_one, mul_one,
    Polynomial.eval_zero] at hev
  exact (Nat.cast_ne_zero.mpr (by omega : r ≠ 0)) hev

private lemma shift_lam_properties {r M : ℕ} {α : ℝ}
    (hTα : ((Tpoly r M).map (Int.castRingHom ℝ)).eval α ≠ 0) :
    (∀ j ∈ Finset.Icc 1 M, 1 - (j : ℝ) * α ≠ 0) ∧
    (∀ j ∈ Finset.Icc 1 M, (j : ℝ) / (1 - (j : ℝ) * α) ≠ 0) ∧
    Set.InjOn (fun j : ℕ => (j : ℝ) / (1 - (j : ℝ) * α)) (Finset.Icc 1 M) := by
  have hden : ∀ j ∈ Finset.Icc 1 M, 1 - (j : ℝ) * α ≠ 0 := by
    rw [Tpoly_map_cast, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod] at hTα
    have hprod_ne : ∏ j ∈ Finset.Icc 1 M, (1 - (j : ℝ) * α) ≠ 0 := by
      have := (mul_ne_zero_iff.mp hTα).2
      simpa using this
    intro j hj
    exact (Finset.prod_ne_zero_iff.mp hprod_ne) j hj
  refine ⟨hden, ?_, ?_⟩
  · intro j hj
    have hj1 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hj).1; omega)
    exact div_ne_zero hj1 (hden j hj)
  · intro j₁ hj₁ j₂ hj₂ heq
    have h1 : 1 - (j₁ : ℝ) * α ≠ 0 := hden j₁ (by simpa using hj₁)
    have h2 : 1 - (j₂ : ℝ) * α ≠ 0 := hden j₂ (by simpa using hj₂)
    have hcross : (j₁ : ℝ) * (1 - (j₂ : ℝ) * α) = (j₂ : ℝ) * (1 - (j₁ : ℝ) * α) := by
      have := (div_eq_div_iff h1 h2).mp heq
      exact this
    have hj_real : (j₁ : ℝ) = (j₂ : ℝ) := by linarith
    exact_mod_cast hj_real

private lemma omega_gen_lin_indep_fin3 {r β₁ β₂ : ℕ} (hr : 2 ≤ r) (hβ1 : 2 ≤ β₁) (hβ12 : β₁ < β₂)
    {lam : ℕ → ℝ} (hlam_ne : ∀ j ∈ Finset.Ico 1 β₂, lam j ≠ 0)
    (hlam_inj : Set.InjOn lam (Finset.Ico 1 β₂))
    {f : Fin 3 → Polynomial ℝ}
    (hrel : ∑ i : Fin 3, (f i : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam = 0) :
    ∀ i : Fin 3, f i = 0 := by
  rw [Fin.sum_univ_three] at hrel
  have h0 : omega_gen r (Finset.Ico 1 (1 : ℕ)) lam = 1 := by
    simp [omega_gen]
  simp only [beta3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, h0, mul_one] at hrel
  obtain ⟨hf0, hf1, hf2⟩ := omega_gen_lin_indep_three hr hβ1 hβ12 hlam_ne hlam_inj hrel
  intro i
  fin_cases i
  · exact hf0
  · exact hf1
  · exact hf2

private lemma two_by_two_det_ne_zero {r M β₁ β₂ : ℕ} (hr : 2 ≤ r) (hβ1 : 2 ≤ β₁)
    (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M) (P : Fin 3 → Polynomial ℤ)
    {i₀ i₁ : Fin 3} (hne_idx : i₀ ≠ i₁) (hP0 : P i₀ ≠ 0) (hP1 : P i₁ ≠ 0) :
    P_sq r M β₁ β₂ P 0 i₀ * P_sq r M β₁ β₂ P 1 i₁ -
      P_sq r M β₁ β₂ P 1 i₀ * P_sq r M β₁ β₂ P 0 i₁ ≠ 0 := by
  intro hdet0
  let A : ℕ → Fin 3 → Polynomial ℝ := fun k i => (P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ)
  have hdetR : A 0 i₀ * A 1 i₁ - A 1 i₀ * A 0 i₁ = 0 := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) hdet0
    simpa [A] using h
  have hA0_ne : A 0 i₀ ≠ 0 := by
    intro h0
    apply hP0
    have h0' : (P i₀).map (Int.castRingHom ℝ) = 0 := by simpa [A, P_sq] using h0
    exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h0')
  have hA1_ne : A 0 i₁ ≠ 0 := by
    intro h0
    apply hP1
    have h0' : (P i₁).map (Int.castRingHom ℝ) = 0 := by simpa [A, P_sq] using h0
    exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h0')
  let T_R : Polynomial ℝ := (Tpoly r M).map (Int.castRingHom ℝ)
  have hT_ne : T_R ≠ 0 := Tpoly_map_cast_ne_zero (by omega : 1 ≤ r)
  let B0 : Polynomial ℝ := -A 1 i₀
  let B1 : Polynomial ℝ := A 0 i₀
  obtain ⟨α, hα⟩ := poly_exists_eval_ne_zero (mul_ne_zero hA0_ne hT_ne)
  have hTα : T_R.eval α ≠ 0 := (mul_ne_zero_iff.mp (by simpa [Polynomial.eval_mul] using hα)).2
  obtain ⟨hden, hlam_ne_M, hlam_inj_M⟩ := shift_lam_properties hTα
  let lam : ℕ → ℝ := fun j => (j : ℝ) / (1 - (j : ℝ) * α)
  let sh : Polynomial ℝ → Polynomial ℝ := fun p => p.comp (Polynomial.C α + Polynomial.X)
  let D : Fin 2 → Polynomial ℝ := ![sh B0, sh B1 * sh T_R]
  have hD0 : (D (Fin.last 1)).coeff 0 ≠ 0 := by
    have hev : (D (Fin.last 1)).eval 0 = (B1 * T_R).eval α := by
      simp [D, sh, B1, Polynomial.eval_mul, Polynomial.eval_comp]
    rw [Polynomial.coeff_zero_eq_eval_zero, hev]
    exact hα
  let idx : Fin 2 → Fin 3 := ![i₀, i₁]
  let F : Fin 2 → PowerSeries ℝ := fun j =>
    (sh (A 0 (idx j)) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam
  have hsol : ∀ j : Fin 2,
      ∑ l : Fin 2, (D l : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[l.val] (F j) = 0 := by
    intro j
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Function.iterate_zero, id_eq, Function.iterate_one,
      D, Matrix.cons_val_zero, Matrix.cons_val_one, Polynomial.coe_mul]
    have hstep := P_sq_shift_iter_eq (by omega : 1 ≤ r) (by omega : β₁ ≤ M + 1)
      (by omega : β₂ ≤ M + 1) P hden 1 (idx j)
    dsimp only at hstep
    rw [Function.iterate_one] at hstep
    have hmul :
        (sh B0 : PowerSeries ℝ) * F j +
          (sh B1 : PowerSeries ℝ) * (sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (F j) =
        (sh B0 : PowerSeries ℝ) * F j +
          (sh B1 : PowerSeries ℝ) * ((sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (F j)) := by
      ring
    rw [hmul]
    change (sh B0 : PowerSeries ℝ) * F j +
      (sh B1 : PowerSeries ℝ) *
        ((sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ
          ((sh (A 0 (idx j)) : PowerSeries ℝ) *
            omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam)) = 0
    have hF1 :
        (sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ
          ((sh (A 0 (idx j)) : PowerSeries ℝ) *
            omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam) =
        (sh (A 1 (idx j)) : PowerSeries ℝ) *
          omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam := by
      simpa [A, P_sq, sh, T_R, lam] using hstep
    rw [hF1]
    have hlin : B0 * A 0 (idx j) + B1 * A 1 (idx j) = 0 := by
      fin_cases j
      · change (-A 1 i₀) * A 0 i₀ + A 0 i₀ * A 1 i₀ = 0; ring
      · change (-A 1 i₀) * A 0 i₁ + A 0 i₀ * A 1 i₁ = 0; linear_combination hdetR
    have hlin_s : sh B0 * sh (A 0 (idx j)) + sh B1 * sh (A 1 (idx j)) = 0 := by
      have := congrArg sh hlin
      simpa [sh, Polynomial.add_comp, Polynomial.mul_comp] using this
    dsimp only [F]
    calc (sh B0 : PowerSeries ℝ) *
          ((sh (A 0 (idx j)) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam) +
        (sh B1 : PowerSeries ℝ) *
          ((sh (A 1 (idx j)) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam)
        = (((sh B0 * sh (A 0 (idx j)) + sh B1 * sh (A 1 (idx j)) : Polynomial ℝ) : PowerSeries ℝ)) *
          omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ (idx j))) lam := by
          simp only [Polynomial.coe_add, Polynomial.coe_mul]; ring
      _ = 0 := by rw [hlin_s, Polynomial.coe_zero, zero_mul]
  obtain ⟨c, hc_ne, hc_sum⟩ := ps_ode_lin_dep (by omega : 1 < 2) D hD0 F hsol
  let f : Fin 3 → Polynomial ℝ := fun i =>
    if i = i₀ then Polynomial.C (c 0) * sh (A 0 i₀)
    else if i = i₁ then Polynomial.C (c 1) * sh (A 0 i₁)
    else 0
  have hf_sum :
      ∑ i : Fin 3, (f i : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam = 0 := by
    have hpair :
        ∑ i : Fin 3, (f i : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam =
        (f i₀ : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i₀)) lam +
        (f i₁ : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i₁)) lam := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have hi1_mem : i₁ ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hne_idx.symm, Finset.mem_univ _⟩
      rw [← Finset.add_sum_erase _ _ hi1_mem]
      have hrest : ∑ i ∈ (Finset.univ.erase i₀).erase i₁,
          (f i : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have h1 : i ≠ i₁ := (Finset.mem_erase.mp hi).1
        have h0 : i ≠ i₀ := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hi)).1
        simp [f, h0, h1]
      rw [hrest, add_zero]
    rw [hpair]
    simp only [f, ↓reduceIte, hne_idx.symm, Polynomial.coe_mul, Polynomial.coe_C]
    rw [Fin.sum_univ_two] at hc_sum
    simpa [F, idx, Algebra.smul_def, PowerSeries.algebraMap_eq, mul_assoc] using hc_sum
  have hsubM : Finset.Ico 1 β₂ ⊆ Finset.Icc 1 M := by
    intro j hj; simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢; omega
  have hfall := omega_gen_lin_indep_fin3 hr hβ1 hβ12
    (fun j hj => hlam_ne_M j (hsubM hj))
    (hlam_inj_M.mono (by exact_mod_cast hsubM)) hf_sum
  have hc0 : c 0 = 0 := by
    have h0 := hfall i₀
    simp only [f, ↓reduceIte] at h0
    have hC0 : Polynomial.C (c 0) = 0 :=
      (mul_eq_zero.mp h0).resolve_right (poly_comp_shift_ne_zero hA0_ne α)
    exact Polynomial.C_eq_zero.mp hC0
  have hc1 : c 1 = 0 := by
    have h1 := hfall i₁
    simp only [f, hne_idx.symm, ↓reduceIte] at h1
    have hC1 : Polynomial.C (c 1) = 0 :=
      (mul_eq_zero.mp h1).resolve_right (poly_comp_shift_ne_zero hA1_ne α)
    exact Polynomial.C_eq_zero.mp hC1
  apply hc_ne
  ext j
  fin_cases j
  · exact hc0
  · exact hc1

private lemma Delta_ne_zero_of_all_ne_zero {r M β₁ β₂ : ℕ} (hr : 2 ≤ r) (hβ1 : 2 ≤ β₁)
    (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M) (P : Fin 3 → Polynomial ℤ)
    (hall : ∀ i : Fin 3, P i ≠ 0) :
    Delta r M β₁ β₂ P ≠ 0 := by
  intro hΔ0
  let A : ℕ → Fin 3 → Polynomial ℝ := fun k i => (P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ)
  have hA0_ne : ∀ i : Fin 3, A 0 i ≠ 0 := by
    intro i h0
    apply hall i
    have h0' : (P i).map (Int.castRingHom ℝ) = 0 := by simpa [A, P_sq] using h0
    exact Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h0')
  let B0 : Polynomial ℝ := A 1 0 * A 2 1 - A 2 0 * A 1 1
  let B1 : Polynomial ℝ := A 2 0 * A 0 1 - A 0 0 * A 2 1
  let B2 : Polynomial ℝ := A 0 0 * A 1 1 - A 1 0 * A 0 1
  have hB2_ne : B2 ≠ 0 := by
    have hZ := two_by_two_det_ne_zero hr hβ1 hβ12 hβ2 P (by decide : (0 : Fin 3) ≠ 1)
      (hall 0) (hall 1)
    intro h0
    apply hZ
    apply Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
    simpa [B2, A] using h0
  have hΔR :
      A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) -
      A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
      A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0) = 0 := by
    have hmap := congrArg (Polynomial.map (Int.castRingHom ℝ)) hΔ0
    unfold Delta at hmap
    rw [Matrix.det_fin_three] at hmap
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_zero,
      Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two] at hmap
    change A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
        A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 = 0 at hmap
    linear_combination hmap
  have hBlin : ∀ i : Fin 3, B0 * A 0 i + B1 * A 1 i + B2 * A 2 i = 0 := by
    intro i
    fin_cases i
    · change B0 * A 0 0 + B1 * A 1 0 + B2 * A 2 0 = 0; dsimp only [B0, B1, B2]; ring
    · change B0 * A 0 1 + B1 * A 1 1 + B2 * A 2 1 = 0; dsimp only [B0, B1, B2]; ring
    · change B0 * A 0 2 + B1 * A 1 2 + B2 * A 2 2 = 0; dsimp only [B0, B1, B2]; linear_combination hΔR
  let T_R : Polynomial ℝ := (Tpoly r M).map (Int.castRingHom ℝ)
  have hT_ne : T_R ≠ 0 := Tpoly_map_cast_ne_zero (by omega : 1 ≤ r)
  obtain ⟨α, hα⟩ := poly_exists_eval_ne_zero (mul_ne_zero hB2_ne (pow_ne_zero 2 hT_ne))
  have hTα : T_R.eval α ≠ 0 := by
    have h2 : (T_R ^ 2).eval α ≠ 0 :=
      (mul_ne_zero_iff.mp (by simpa [Polynomial.eval_mul] using hα)).2
    rw [Polynomial.eval_pow] at h2
    exact fun h0 => h2 (by simp [h0])
  obtain ⟨hden, hlam_ne_M, hlam_inj_M⟩ := shift_lam_properties hTα
  let lam : ℕ → ℝ := fun j => (j : ℝ) / (1 - (j : ℝ) * α)
  let sh : Polynomial ℝ → Polynomial ℝ := fun p => p.comp (Polynomial.C α + Polynomial.X)
  let D : Fin 3 → Polynomial ℝ :=
    ![sh B0, sh B1 * sh T_R + sh B2 * sh T_R * (sh T_R).derivative, sh B2 * sh T_R ^ 2]
  have hD0 : (D (Fin.last 2)).coeff 0 ≠ 0 := by
    have hev : (D (Fin.last 2)).eval 0 = (B2 * T_R ^ 2).eval α := by
      simp [D, sh, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_comp]
    rw [Polynomial.coeff_zero_eq_eval_zero, hev]
    exact hα
  let F : Fin 3 → PowerSeries ℝ := fun i =>
    (sh (A 0 i) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam
  have hsol : ∀ i : Fin 3,
      ∑ j : Fin 3, (D j : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[j.val] (F i) = 0 := by
    intro i
    have hstep1 :
        (sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (F i) =
          (sh (A 1 i) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam := by
      have h := P_sq_shift_iter_eq (by omega : 1 ≤ r) (by omega : β₁ ≤ M + 1)
        (by omega : β₂ ≤ M + 1) P hden 1 i
      simpa [A, P_sq, sh, T_R, lam, F] using h
    have hstep2 :
        (sh T_R : PowerSeries ℝ) *
          PowerSeries.derivative ℝ ((sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (F i)) =
          (sh (A 2 i) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam := by
      have h := P_sq_shift_iter_eq (by omega : 1 ≤ r) (by omega : β₁ ≤ M + 1)
        (by omega : β₂ ≤ M + 1) P hden 2 i
      simpa [A, P_sq, sh, T_R, lam, F, Function.iterate_succ_apply'] using h
    have hexpand2 :
        (sh T_R : PowerSeries ℝ) *
          PowerSeries.derivative ℝ ((sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (F i)) =
        ((sh T_R * (sh T_R).derivative : Polynomial ℝ) : PowerSeries ℝ) *
          PowerSeries.derivative ℝ (F i) +
        ((sh T_R ^ 2 : Polynomial ℝ) : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[2] (F i) := by
      rw [ps_deriv_mul, PowerSeries.derivative_coe, mul_add]
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Function.iterate_succ_apply',
        Function.iterate_zero, id_eq]
      ring
    have hlin_s : sh B0 * sh (A 0 i) + sh B1 * sh (A 1 i) + sh B2 * sh (A 2 i) = 0 := by
      have := congrArg sh (hBlin i)
      simpa [sh, Polynomial.add_comp, Polynomial.mul_comp] using this
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, Function.iterate_zero, id_eq,
      Function.iterate_one, D, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Polynomial.coe_add, Polynomial.coe_mul,
      Polynomial.coe_pow]
    have hcomb :
        (sh B0 : PowerSeries ℝ) * F i +
        ((sh B1 : PowerSeries ℝ) * (sh T_R : PowerSeries ℝ) +
          (sh B2 : PowerSeries ℝ) * (sh T_R : PowerSeries ℝ) *
            ((sh T_R).derivative : PowerSeries ℝ)) * PowerSeries.derivative ℝ (F i) +
        (sh B2 : PowerSeries ℝ) * (sh T_R : PowerSeries ℝ) ^ 2 *
          (PowerSeries.derivative ℝ)^[2] (F i) =
        (sh B0 : PowerSeries ℝ) * F i +
        (sh B1 : PowerSeries ℝ) * ((sh T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (F i)) +
        (sh B2 : PowerSeries ℝ) *
          (((sh T_R * (sh T_R).derivative : Polynomial ℝ) : PowerSeries ℝ) *
            PowerSeries.derivative ℝ (F i) +
          ((sh T_R ^ 2 : Polynomial ℝ) : PowerSeries ℝ) * (PowerSeries.derivative ℝ)^[2] (F i)) := by
      simp only [Polynomial.coe_mul, Polynomial.coe_pow]; ring
    rw [hcomb, ← hexpand2, hstep2, hstep1]
    dsimp only [F]
    calc (sh B0 : PowerSeries ℝ) *
          ((sh (A 0 i) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam) +
        (sh B1 : PowerSeries ℝ) *
          ((sh (A 1 i) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam) +
        (sh B2 : PowerSeries ℝ) *
          ((sh (A 2 i) : PowerSeries ℝ) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam)
        = (((sh B0 * sh (A 0 i) + sh B1 * sh (A 1 i) + sh B2 * sh (A 2 i) : Polynomial ℝ) :
            PowerSeries ℝ)) * omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam := by
          simp only [Polynomial.coe_add, Polynomial.coe_mul]; ring
      _ = 0 := by rw [hlin_s, Polynomial.coe_zero, zero_mul]
  obtain ⟨c, hc_ne, hc_sum⟩ := ps_ode_lin_dep (by omega : 2 < 3) D hD0 F hsol
  have hf_sum :
      ∑ i : Fin 3, ((Polynomial.C (c i) * sh (A 0 i) : Polynomial ℝ) : PowerSeries ℝ) *
        omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) lam = 0 := by
    simpa [F, Polynomial.coe_mul, Polynomial.coe_C, Algebra.smul_def, PowerSeries.algebraMap_eq,
      mul_assoc] using hc_sum
  have hsubM : Finset.Ico 1 β₂ ⊆ Finset.Icc 1 M := by
    intro j hj; simp only [Finset.mem_Ico, Finset.mem_Icc] at hj ⊢; omega
  have hfall := omega_gen_lin_indep_fin3 hr hβ1 hβ12
    (fun j hj => hlam_ne_M j (hsubM hj))
    (hlam_inj_M.mono (by exact_mod_cast hsubM)) hf_sum
  apply hc_ne
  ext i
  have hi := hfall i
  have hC0 : Polynomial.C (c i) = 0 :=
    (mul_eq_zero.mp hi).resolve_right (poly_comp_shift_ne_zero (hA0_ne i) α)
  exact Polynomial.C_eq_zero.mp hC0

private lemma exists_coeff_ne_zero_mul_ps {Q : Polynomial ℝ} (hQ : Q ≠ 0)
    {ω : PowerSeries ℝ} (hω : PowerSeries.constantCoeff ω ≠ 0) :
    ∃ v ≤ Q.natDegree, PowerSeries.coeff v ((Q : PowerSeries ℝ) * ω) ≠ 0 := by
  refine ⟨Q.natTrailingDegree, Polynomial.natTrailingDegree_le_natDegree Q, ?_⟩
  rw [PowerSeries.coeff_mul]
  have hmem : (Q.natTrailingDegree, 0) ∈ antidiagonal Q.natTrailingDegree := by simp
  rw [Finset.sum_eq_single (Q.natTrailingDegree, 0)]
  · simp only [Polynomial.coeff_coe, PowerSeries.coeff_zero_eq_constantCoeff]
    have htc : Q.coeff Q.natTrailingDegree ≠ 0 := by
      simpa [Polynomial.trailingCoeff] using Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hQ
    exact mul_ne_zero htc hω
  · intro p hp hpne
    have hp12 : p.1 + p.2 = Q.natTrailingDegree := mem_antidiagonal.mp hp
    have hp1lt : p.1 < Q.natTrailingDegree := by
      by_contra hge
      push Not at hge
      have h1 : p.1 = Q.natTrailingDegree := by omega
      have h2 : p.2 = 0 := by omega
      exact hpne (Prod.ext h1 h2)
    simp only [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hp1lt,
      zero_mul]
  · intro hnot; exact absurd hmem hnot

private lemma coeff_mul_eq_zero_of_vanish {N : ℕ} (A F : PowerSeries ℝ)
    (hF : ∀ v ≤ N, PowerSeries.coeff v F = 0) :
    ∀ v ≤ N, PowerSeries.coeff v (A * F) = 0 := by
  intro v hv
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp2 : p.2 ≤ N := by
    have := mem_antidiagonal.mp hp; omega
  rw [hF p.2 hp2, mul_zero]

theorem Delta_ne_zero {r M β₁ β₂ D : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M)
    (hβ1 : 2 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M)
    (hD : 10 ≤ D) (hDM : 3 * M + 20 ≤ D)
    (P : Fin 3 → Polynomial ℤ) (hdeg : ∀ i, (P i).natDegree ≤ D)
    (hne : ∃ i, P i ≠ 0)
    (hvan : ∀ v ≤ (29 * D) / 12, PowerSeries.coeff v (R_ps r β₁ β₂ P) = 0) :
    Delta r M β₁ β₂ P ≠ 0 := by
  have _ := hM
  have _ := hD
  by_cases hall : ∀ i : Fin 3, P i ≠ 0
  · exact Delta_ne_zero_of_all_ne_zero hr hβ1 hβ12 hβ2 P hall
  exfalso
  push Not at hall
  obtain ⟨i₂, hi₂⟩ := hall
  obtain ⟨i₀, hi₀⟩ := hne
  have hi02 : i₀ ≠ i₂ := fun h => hi₀ (h ▸ hi₂)
  obtain ⟨i₁, hi10, hi12⟩ : ∃ i₁ : Fin 3, i₁ ≠ i₀ ∧ i₁ ≠ i₂ := by
    fin_cases i₀ <;> fin_cases i₂ <;> first | exact absurd rfl hi02 | (refine ⟨0, by decide, by decide⟩) | (refine ⟨1, by decide, by decide⟩) | (refine ⟨2, by decide, by decide⟩)
  have huniv : ∀ f : Fin 3 → PowerSeries ℝ,
      ∑ i : Fin 3, f i = f i₀ + f i₁ + f i₂ := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have hi1_mem : i₁ ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hi10, Finset.mem_univ _⟩
    rw [← Finset.add_sum_erase _ _ hi1_mem]
    have hrest : (Finset.univ.erase i₀).erase i₁ = {i₂} := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_singleton]
      fin_cases i₀ <;> fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j <;> simp_all
    rw [hrest, Finset.sum_singleton, add_assoc]
  by_cases hi₁ : P i₁ = 0
  · have hR : R_ps r β₁ β₂ P =
        ((P i₀).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i₀ := by
      unfold R_ps
      rw [huniv, hi₁, hi₂]
      simp
    have hPR_ne : (P i₀).map (Int.castRingHom ℝ) ≠ 0 := by
      intro h0
      exact hi₀ (Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h0))
    have hω : PowerSeries.constantCoeff (omega3PS r β₁ β₂ i₀) ≠ 0 := by
      rw [omega3PS_constantCoeff]; exact one_ne_zero
    obtain ⟨v, hv_deg, hv_ne⟩ := exists_coeff_ne_zero_mul_ps hPR_ne hω
    have hv_le : v ≤ (29 * D) / 12 := by
      have h1 : ((P i₀).map (Int.castRingHom ℝ)).natDegree ≤ D :=
        Polynomial.natDegree_map_le.trans (hdeg i₀)
      omega
    rw [← hR] at hv_ne
    exact hv_ne (hvan v hv_le)
  · set Δt : Polynomial ℤ :=
      P_sq r M β₁ β₂ P 0 i₀ * P_sq r M β₁ β₂ P 1 i₁ -
        P_sq r M β₁ β₂ P 1 i₀ * P_sq r M β₁ β₂ P 0 i₁
    have hΔt_ne : Δt ≠ 0 := two_by_two_det_ne_zero hr hβ1 hβ12 hβ2 P hi10.symm hi₀ hi₁
    have hΔt_deg : Δt.natDegree ≤ 2 * D + M := by
      refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h0 := P_sq_natDegree_le (r := r) (M := M) (β₁ := β₁) (β₂ := β₂) P hdeg 0 i₀
        have h1 := P_sq_natDegree_le (r := r) (M := M) (β₁ := β₁) (β₂ := β₂) P hdeg 1 i₁
        omega
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have h0 := P_sq_natDegree_le (r := r) (M := M) (β₁ := β₁) (β₂ := β₂) P hdeg 1 i₀
        have h1 := P_sq_natDegree_le (r := r) (M := M) (β₁ := β₁) (β₂ := β₂) P hdeg 0 i₁
        omega
    have hPsq_zero : ∀ k : ℕ, P_sq r M β₁ β₂ P k i₂ = 0 := by
      intro k
      induction k with
      | zero => simpa [P_sq] using hi₂
      | succ k ih => simp [P_sq, ih]
    set R0 : PowerSeries ℝ := R_ps r β₁ β₂ P
    set R1 : PowerSeries ℝ :=
      ((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) * PowerSeries.derivative ℝ R0
    have hR0_eq : R0 =
        ((P_sq r M β₁ β₂ P 0 i₀).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i₀ +
        ((P_sq r M β₁ β₂ P 0 i₁).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i₁ := by
      dsimp only [R0]; unfold R_ps
      rw [huniv, hi₂]
      simp [P_sq]
    have hR1_eq : R1 =
        ((P_sq r M β₁ β₂ P 1 i₀).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i₀ +
        ((P_sq r M β₁ β₂ P 1 i₁).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i₁ := by
      have h := R_ps_iter_eq (by omega : 1 ≤ r) (by omega : β₁ ≤ M + 1) (by omega : β₂ ≤ M + 1) P 1
      rw [Function.iterate_one, huniv, hPsq_zero 1] at h
      simpa [R1, R0] using h
    have hident :
        ((Δt.map (Int.castRingHom ℝ) : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i₀ =
        ((P_sq r M β₁ β₂ P 1 i₁).map (Int.castRingHom ℝ) : PowerSeries ℝ) * R0 -
        ((P_sq r M β₁ β₂ P 0 i₁).map (Int.castRingHom ℝ) : PowerSeries ℝ) * R1 := by
      rw [hR0_eq, hR1_eq]
      simp only [Δt, Polynomial.map_sub, Polynomial.map_mul, Polynomial.coe_sub, Polynomial.coe_mul]
      ring
    have hR1_van : ∀ v ≤ (29 * D) / 12 - 1, PowerSeries.coeff v R1 = 0 := by
      apply coeff_mul_eq_zero_of_vanish
      intro v hv
      rw [PowerSeries.coeff_derivative, hvan (v + 1) (by omega), zero_mul]
    have hΔt_van : ∀ v ≤ (29 * D) / 12 - 1,
        PowerSeries.coeff v (((Δt.map (Int.castRingHom ℝ) : Polynomial ℝ) : PowerSeries ℝ) *
          omega3PS r β₁ β₂ i₀) = 0 := by
      intro v hv
      rw [hident, map_sub]
      have h1 := coeff_mul_eq_zero_of_vanish
        ((P_sq r M β₁ β₂ P 1 i₁).map (Int.castRingHom ℝ) : PowerSeries ℝ) R0
        (fun u hu => hvan u (by omega)) v hv
      have h2 := coeff_mul_eq_zero_of_vanish
        ((P_sq r M β₁ β₂ P 0 i₁).map (Int.castRingHom ℝ) : PowerSeries ℝ) R1 hR1_van v hv
      rw [h1, h2, sub_self]
    have hΔtR_ne : Δt.map (Int.castRingHom ℝ) ≠ 0 := by
      intro h0
      exact hΔt_ne (Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa using h0))
    have hω : PowerSeries.constantCoeff (omega3PS r β₁ β₂ i₀) ≠ 0 := by
      rw [omega3PS_constantCoeff]; exact one_ne_zero
    obtain ⟨v, hv_deg, hv_ne⟩ := exists_coeff_ne_zero_mul_ps hΔtR_ne hω
    have hv_le : v ≤ (29 * D) / 12 - 1 := by
      have h1 : (Δt.map (Int.castRingHom ℝ)).natDegree ≤ 2 * D + M :=
        Polynomial.natDegree_map_le.trans hΔt_deg
      omega
    exact hv_ne (hΔt_van v hv_le)

/- Part 2F: Lower-triangular relation, Cramer differentiation, and `P_ang_full_rank`. -/

private noncomputable def q_poly (T : Polynomial ℝ) : ℕ → ℕ → Polynomial ℝ
  | 0, j => if j = 0 then 1 else 0
  | _ + 1, 0 => 0
  | k + 1, j + 1 =>
      T * (q_poly T k (j + 1)).derivative +
      Polynomial.C ((j + 1 : ℕ) : ℝ) * q_poly T k (j + 1) * T.derivative +
      q_poly T k j

private lemma q_poly_eq_zero_of_gt (T : Polynomial ℝ) :
    ∀ k j : ℕ, k < j → q_poly T k j = 0 := by
  intro k
  induction k with
  | zero =>
    intro j hj
    simp [q_poly, Nat.ne_of_gt hj]
  | succ k ih =>
    intro j hj
    cases j with
    | zero => omega
    | succ j =>
      simp only [q_poly, ih (j + 1) (by omega), ih j (by omega), Polynomial.derivative_zero,
        mul_zero, zero_mul, add_zero]

private lemma q_poly_zero_deriv (T : Polynomial ℝ) (k : ℕ) :
    (q_poly T k 0).derivative = 0 := by
  cases k <;> simp [q_poly]

private lemma iter_T_deriv_eq_sum_q_poly (T : Polynomial ℝ) (k : ℕ) (F : PowerSeries ℝ) :
    (fun G => (T : PowerSeries ℝ) * PowerSeries.derivative ℝ G)^[k] F =
      ∑ j ∈ Finset.range (k + 1),
        (q_poly T k j : PowerSeries ℝ) * (T : PowerSeries ℝ) ^ j *
          (PowerSeries.derivative ℝ)^[j] F := by
  induction k with
  | zero =>
    simp [q_poly]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_sum, Finset.mul_sum]
    have hterm : ∀ j : ℕ,
        (T : PowerSeries ℝ) *
          PowerSeries.derivative ℝ
            ((q_poly T k j : PowerSeries ℝ) * (T : PowerSeries ℝ) ^ j *
              (PowerSeries.derivative ℝ)^[j] F) =
        (((T * (q_poly T k j).derivative +
            Polynomial.C (j : ℝ) * q_poly T k j * T.derivative : Polynomial ℝ) : PowerSeries ℝ) *
          (T : PowerSeries ℝ) ^ j * (PowerSeries.derivative ℝ)^[j] F) +
        (q_poly T k j : PowerSeries ℝ) * (T : PowerSeries ℝ) ^ (j + 1) *
          (PowerSeries.derivative ℝ)^[j + 1] F := by
      intro j
      rw [ps_deriv_mul, ps_deriv_mul, add_mul, mul_add, mul_add, PowerSeries.derivative_coe]
      have hpow :
          (T : PowerSeries ℝ) *
            ((q_poly T k j : PowerSeries ℝ) * PowerSeries.derivative ℝ ((T : PowerSeries ℝ) ^ j) *
              (PowerSeries.derivative ℝ)^[j] F) =
          (q_poly T k j : PowerSeries ℝ) *
            ((T : PowerSeries ℝ) * PowerSeries.derivative ℝ ((T : PowerSeries ℝ) ^ j)) *
            (PowerSeries.derivative ℝ)^[j] F := by ring
      rw [hpow, ps_deriv_pow_mul, PowerSeries.derivative_coe]
      simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, Polynomial.coe_add, Polynomial.coe_mul,
        Polynomial.coe_C, Function.iterate_succ_apply', pow_succ']
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    have hfirst :
        ∑ j ∈ Finset.range (k + 1),
          (((T * (q_poly T k j).derivative +
              Polynomial.C (j : ℝ) * q_poly T k j * T.derivative : Polynomial ℝ) : PowerSeries ℝ) *
            (T : PowerSeries ℝ) ^ j * (PowerSeries.derivative ℝ)^[j] F) =
        ∑ j ∈ Finset.range (k + 1),
          (((T * (q_poly T k (j + 1)).derivative +
              Polynomial.C ((j + 1 : ℕ) : ℝ) * q_poly T k (j + 1) * T.derivative : Polynomial ℝ) :
              PowerSeries ℝ) *
            (T : PowerSeries ℝ) ^ (j + 1) * (PowerSeries.derivative ℝ)^[j + 1] F) := by
      rw [Finset.sum_range_succ' _ k]
      have hz0 :
          (((T * (q_poly T k 0).derivative +
              Polynomial.C ((0 : ℕ) : ℝ) * q_poly T k 0 * T.derivative : Polynomial ℝ) :
              PowerSeries ℝ) *
            (T : PowerSeries ℝ) ^ 0 * (PowerSeries.derivative ℝ)^[0] F) = 0 := by
        simp [q_poly_zero_deriv]
      rw [hz0, add_zero, Finset.sum_range_succ _ k]
      have htop :
          (((T * (q_poly T k (k + 1)).derivative +
              Polynomial.C ((k + 1 : ℕ) : ℝ) * q_poly T k (k + 1) * T.derivative : Polynomial ℝ) :
              PowerSeries ℝ) *
            (T : PowerSeries ℝ) ^ (k + 1) * (PowerSeries.derivative ℝ)^[k + 1] F) = 0 := by
        rw [q_poly_eq_zero_of_gt T k (k + 1) (by omega)]
        simp
      rw [htop, add_zero]
    rw [hfirst, ← Finset.sum_add_distrib, Finset.sum_range_succ' _ (k + 1)]
    simp only [q_poly, Polynomial.coe_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_C]
    ring

private lemma P_sq_eq_sum_P_ang {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    (hβ1 : 1 ≤ β₁) (hβ1M : β₁ ≤ M) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (k : ℕ) (i : Fin 3) :
    (P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ) =
      ∑ j ∈ Finset.range (k + 1),
        (Polynomial.C (j.factorial : ℝ) *
          q_poly ((Tpoly r M).map (Int.castRingHom ℝ)) k j) * P_ang r M β₁ β₂ P j i := by
  set T_R : Polynomial ℝ := (Tpoly r M).map (Int.castRingHom ℝ)
  set F : PowerSeries ℝ := ((P i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i
  have h1 := P_sq_iter_eq hr (by omega : β₁ ≤ M + 1) (by omega : β₂ ≤ M + 1) P k i
  have h2 := iter_T_deriv_eq_sum_q_poly T_R k F
  have h3 :
      ((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i =
      (((∑ j ∈ Finset.range (k + 1),
          (Polynomial.C (j.factorial : ℝ) * q_poly T_R k j) *
            P_ang r M β₁ β₂ P j i : Polynomial ℝ) : PowerSeries ℝ)) * omega3PS r β₁ β₂ i := by
    rw [← h1, h2, coe_sum_poly, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, P_ang_powerSeries_eq hr hM hβ1 hβ1M hβ2 P j i]
    simp only [Algebra.smul_def, PowerSeries.algebraMap_eq, Polynomial.coe_mul, Polynomial.coe_C]
    ring
  have hω_ne : omega3PS r β₁ β₂ i ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [omega3PS_constantCoeff, map_zero] at this
    exact one_ne_zero this
  have hps_eq :
      ((P_sq r M β₁ β₂ P k i).map (Int.castRingHom ℝ) : PowerSeries ℝ) =
      ((∑ j ∈ Finset.range (k + 1),
          (Polynomial.C (j.factorial : ℝ) * q_poly T_R k j) *
            P_ang r M β₁ β₂ P j i : Polynomial ℝ) : PowerSeries ℝ) := by
    exact mul_right_cancel₀ hω_ne h3
  exact Polynomial.coe_injective ℝ hps_eq

private lemma eval_iterate_deriv_pow_mul (α : ℝ) :
    ∀ (n m : ℕ) (h : Polynomial ℝ),
      (n < m → (Polynomial.derivative^[n] ((Polynomial.X - Polynomial.C α) ^ m * h)).eval α = 0) ∧
      (n = m → (Polynomial.derivative^[n] ((Polynomial.X - Polynomial.C α) ^ m * h)).eval α =
        (m.factorial : ℝ) * h.eval α) := by
  intro n
  induction n with
  | zero =>
    intro m h
    constructor
    · intro hlt
      simp only [Function.iterate_zero, id_eq, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
      rw [zero_pow (by omega), zero_mul]
    · intro heq
      subst heq
      simp
  | succ n ih =>
    intro m h
    cases m with
    | zero =>
      exact ⟨fun hlt => by omega, fun heq => by omega⟩
    | succ m =>
      have hderiv :
          Polynomial.derivative ((Polynomial.X - Polynomial.C α) ^ (m + 1) * h) =
            (Polynomial.X - Polynomial.C α) ^ m *
              (Polynomial.C ((m + 1 : ℕ) : ℝ) * h +
                (Polynomial.X - Polynomial.C α) * h.derivative) := by
        rw [Polynomial.derivative_mul, Polynomial.derivative_pow]
        simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
          sub_zero, mul_one, Nat.add_sub_cancel, Polynomial.C_eq_natCast]
        rw [pow_succ']
        ring
      have hiter :
          Polynomial.derivative^[n + 1] ((Polynomial.X - Polynomial.C α) ^ (m + 1) * h) =
          Polynomial.derivative^[n]
            ((Polynomial.X - Polynomial.C α) ^ m *
              (Polynomial.C ((m + 1 : ℕ) : ℝ) * h +
                (Polynomial.X - Polynomial.C α) * h.derivative)) := by
        rw [Function.iterate_succ_apply, hderiv]
      rw [hiter]
      constructor
      · intro hlt
        exact (ih m _).1 (by omega)
      · intro heq
        have hnm : n = m := by omega
        rw [(ih m _).2 hnm]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
          Polynomial.eval_X, sub_self, zero_mul, add_zero, Nat.factorial_succ, Nat.cast_mul]
        ring

private lemma rootMultiplicity_deriv_props {f : Polynomial ℝ} (hf : f ≠ 0) (α : ℝ) :
    let a := f.rootMultiplicity α
    (∀ j < a, (Polynomial.derivative^[j] f).eval α = 0) ∧
    (Polynomial.derivative^[a] f).eval α ≠ 0 := by
  intro a
  obtain ⟨g, hfg, hg_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf α
  have hg_ev : g.eval α ≠ 0 := by rwa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] at hg_ndvd
  constructor
  · intro j hj
    rw [hfg]
    exact (eval_iterate_deriv_pow_mul α j a g).1 hj
  · rw [hfg, (eval_iterate_deriv_pow_mul α a a g).2 rfl]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)) hg_ev

private lemma cramer_iter_identity {r M β₁ β₂ : ℕ} (hr : 1 ≤ r) (hβ1M : β₁ ≤ M + 1)
    (hβ2M : β₂ ≤ M + 1) (P : Fin 3 → Polynomial ℤ) (k : Fin 3) (J : ℕ) :
    let T_R : Polynomial ℝ := (Tpoly r M).map (Int.castRingHom ℝ)
    let Δ_R : Polynomial ℝ := (Delta r M β₁ β₂ P).map (Int.castRingHom ℝ)
    let R_sq : ℕ → PowerSeries ℝ := fun l =>
      ∑ i : Fin 3, ((P_sq r M β₁ β₂ P l i).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
        omega3PS r β₁ β₂ i
    ∃ (L : Fin J → Fin 3 → Polynomial ℝ) (Mc : Fin (J + 3) → Polynomial ℝ),
      ((T_R ^ J * (Polynomial.derivative^[J] Δ_R) : Polynomial ℝ) : PowerSeries ℝ) *
          omega3PS r β₁ β₂ k +
        ∑ j : Fin J,
          ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3, (L j i : PowerSeries ℝ) * omega3PS r β₁ β₂ i =
      ∑ l : Fin (J + 3), (Mc l : PowerSeries ℝ) * R_sq l.val := by
  intro T_R Δ_R R_sq
  have hTA_deriv : ∀ i : Fin 3,
      (T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (omega3PS r β₁ β₂ i) =
        ((TA3 r M β₁ β₂ i).map (Int.castRingHom ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i := by
    intro i
    have hβM : beta3 β₁ β₂ i ≤ M + 1 := by fin_cases i <;> simp [beta3] <;> omega
    exact Tpoly_deriv_omegaPS hr hβM
  have hR_step : ∀ l : ℕ,
      (T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (R_sq l) = R_sq (l + 1) := by
    intro l
    have h1 := R_ps_iter_eq hr hβ1M hβ2M P l
    have h2 := R_ps_iter_eq hr hβ1M hβ2M P (l + 1)
    dsimp only [R_sq]
    rw [← h1, ← h2, Function.iterate_succ_apply']
  induction J with
  | zero =>
    let M_sq : Matrix (Fin 3) (Fin 3) (Polynomial ℝ) :=
      Matrix.of fun l i => (P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ)
    have hdet_eq : Matrix.det M_sq = Δ_R := by
      dsimp only [Δ_R, Delta, M_sq]
      rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
      rfl
    refine ⟨Fin.elim0, fun l => Matrix.adjugate M_sq k l, ?_⟩
    simp only [pow_zero, Function.iterate_zero, id_eq, one_mul, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero]
    have hmul :
        ∑ l : Fin 3, ((Matrix.adjugate M_sq k l : Polynomial ℝ) : PowerSeries ℝ) * R_sq l.val =
        ∑ i : Fin 3,
          (((∑ l : Fin 3, Matrix.adjugate M_sq k l * M_sq l i : Polynomial ℝ) : PowerSeries ℝ)) *
            omega3PS r β₁ β₂ i := by
      dsimp only [R_sq]
      simp_rw [Finset.mul_sum, coe_sum_poly, Finset.sum_mul, Polynomial.coe_mul, mul_assoc]
      exact Finset.sum_comm
    rw [hmul]
    have hadj : ∀ i : Fin 3,
        ∑ l : Fin 3, Matrix.adjugate M_sq k l * M_sq l i = if k = i then Δ_R else 0 := by
      intro i
      have h := congrFun (congrFun (Matrix.adjugate_mul M_sq) k) i
      simpa [Matrix.mul_apply, Matrix.one_apply, hdet_eq] using h
    simp_rw [hadj]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hik; simp [hik.symm]
    · intro hnot; exact absurd (Finset.mem_univ k) hnot
  | succ J ih =>
    obtain ⟨L, Mc, hIH⟩ := ih
    let TA_R : Fin 3 → Polynomial ℝ := fun i => (TA3 r M β₁ β₂ i).map (Int.castRingHom ℝ)
    let L' : Fin (J + 1) → Fin 3 → Polynomial ℝ := fun m i =>
      (if m.val = J then (if i = k then T_R * (T_R ^ J).derivative + T_R ^ J * TA_R k else 0)
        else 0) +
      (if h : m.val < J then T_R * (L ⟨m.val, h⟩ i).derivative + TA_R i * L ⟨m.val, h⟩ i else 0) +
      (if h : 0 < m.val then T_R * L ⟨m.val - 1, by omega⟩ i else 0)
    let Mc' : Fin (J + 1 + 3) → Polynomial ℝ := fun l =>
      (if h : l.val < J + 3 then T_R * (Mc ⟨l.val, h⟩).derivative else 0) +
      (if h : 0 < l.val then Mc ⟨l.val - 1, by omega⟩ else 0)
    refine ⟨L', Mc', ?_⟩
    have hstep := congrArg (fun G => (T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ G) hIH
    rw [map_add, mul_add] at hstep
    have hRHS :
        (T_R : PowerSeries ℝ) *
          PowerSeries.derivative ℝ (∑ l : Fin (J + 3), (Mc l : PowerSeries ℝ) * R_sq l.val) =
        ∑ l : Fin (J + 1 + 3), (Mc' l : PowerSeries ℝ) * R_sq l.val := by
      rw [map_sum, Finset.mul_sum]
      have h1 :
          ∑ l : Fin (J + 3),
            (T_R : PowerSeries ℝ) *
              PowerSeries.derivative ℝ ((Mc l : PowerSeries ℝ) * R_sq l.val) =
          ∑ l : Fin (J + 3),
            ((T_R * (Mc l).derivative : Polynomial ℝ) : PowerSeries ℝ) * R_sq l.val +
          ∑ l : Fin (J + 3), (Mc l : PowerSeries ℝ) * R_sq (l.val + 1) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [ps_deriv_mul, mul_add, PowerSeries.derivative_coe, Polynomial.coe_mul]
        have hre : (T_R : PowerSeries ℝ) * ((Mc l : PowerSeries ℝ) * PowerSeries.derivative ℝ (R_sq l.val)) =
            (Mc l : PowerSeries ℝ) * ((T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (R_sq l.val)) := by ring
        rw [hre, hR_step l.val]
        ring
      rw [h1]
      have hsplit :
          ∑ l : Fin (J + 1 + 3), (Mc' l : PowerSeries ℝ) * R_sq l.val =
          ∑ l : Fin (J + 1 + 3),
            ((if h : l.val < J + 3 then T_R * (Mc ⟨l.val, h⟩).derivative else 0 : Polynomial ℝ) :
              PowerSeries ℝ) * R_sq l.val +
          ∑ l : Fin (J + 1 + 3),
            ((if h : 0 < l.val then Mc ⟨l.val - 1, by omega⟩ else 0 : Polynomial ℝ) :
              PowerSeries ℝ) * R_sq l.val := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Mc', Polynomial.coe_add, add_mul]
      rw [hsplit]
      congr 1
      · symm
        rw [Fin.sum_univ_castSucc]
        have hlast : ¬ (Fin.last (J + 3)).val < J + 3 := by simp
        simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, hlast, Polynomial.coe_zero, zero_mul,
          add_zero]
      · symm
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, lt_self_iff_false, ↓reduceDIte, Polynomial.coe_zero, zero_mul,
          zero_add, Fin.val_succ, Nat.succ_pos, Nat.add_sub_cancel]
    have hLHS1 :
        (T_R : PowerSeries ℝ) *
          PowerSeries.derivative ℝ
            (((T_R ^ J * (Polynomial.derivative^[J] Δ_R) : Polynomial ℝ) : PowerSeries ℝ) *
              omega3PS r β₁ β₂ k) =
        ((T_R ^ (J + 1) * (Polynomial.derivative^[J + 1] Δ_R) : Polynomial ℝ) : PowerSeries ℝ) *
          omega3PS r β₁ β₂ k +
        ((Polynomial.derivative^[J] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
          (((T_R * (T_R ^ J).derivative + T_R ^ J * TA_R k : Polynomial ℝ) : PowerSeries ℝ) *
            omega3PS r β₁ β₂ k) := by
      rw [ps_deriv_mul, mul_add, PowerSeries.derivative_coe, Polynomial.derivative_mul]
      have hre :
          (T_R : PowerSeries ℝ) *
            (((T_R ^ J * Polynomial.derivative^[J] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              PowerSeries.derivative ℝ (omega3PS r β₁ β₂ k)) =
          ((T_R ^ J * Polynomial.derivative^[J] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ((T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (omega3PS r β₁ β₂ k)) := by ring
      rw [hre, hTA_deriv k]
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow,
        Function.iterate_succ_apply', pow_succ', TA_R]
      ring
    have hLHS2 :
        (T_R : PowerSeries ℝ) *
          PowerSeries.derivative ℝ
            (∑ j : Fin J,
              ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
                ∑ i : Fin 3, (L j i : PowerSeries ℝ) * omega3PS r β₁ β₂ i) =
        ∑ j : Fin J,
          ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3,
              (((T_R * (L j i).derivative + TA_R i * L j i : Polynomial ℝ) : PowerSeries ℝ) *
                omega3PS r β₁ β₂ i) +
        ∑ j : Fin J,
          ((Polynomial.derivative^[j.val + 1] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3,
              (((T_R * L j i : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) := by
      rw [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ps_deriv_mul, mul_add, PowerSeries.derivative_coe, map_sum]
      have hpart1 :
          (T_R : PowerSeries ℝ) *
            (((Polynomial.derivative (Polynomial.derivative^[j.val] Δ_R) : Polynomial ℝ) :
                PowerSeries ℝ) *
              ∑ i : Fin 3, (L j i : PowerSeries ℝ) * omega3PS r β₁ β₂ i) =
          ((Polynomial.derivative^[j.val + 1] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3,
              (((T_R * L j i : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) := by
        rw [Function.iterate_succ_apply', Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Polynomial.coe_mul]; ring
      have hpart2 :
          (T_R : PowerSeries ℝ) *
            (((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              ∑ i : Fin 3,
                PowerSeries.derivative ℝ ((L j i : PowerSeries ℝ) * omega3PS r β₁ β₂ i)) =
          ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3,
              (((T_R * (L j i).derivative + TA_R i * L j i : Polynomial ℝ) : PowerSeries ℝ) *
                omega3PS r β₁ β₂ i) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ps_deriv_mul, PowerSeries.derivative_coe]
        have hre :
            (T_R : PowerSeries ℝ) *
              (((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
                ((L j i).derivative * omega3PS r β₁ β₂ i +
                  (L j i : PowerSeries ℝ) * PowerSeries.derivative ℝ (omega3PS r β₁ β₂ i))) =
            ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              ((T_R : PowerSeries ℝ) * ((L j i).derivative : PowerSeries ℝ) * omega3PS r β₁ β₂ i +
                (L j i : PowerSeries ℝ) *
                  ((T_R : PowerSeries ℝ) * PowerSeries.derivative ℝ (omega3PS r β₁ β₂ i))) := by
          ring
        rw [hre, hTA_deriv i]
        simp only [Polynomial.coe_add, Polynomial.coe_mul, TA_R]
        ring
      rw [hpart1, hpart2, add_comm]
    have hL'_sum :
        ∑ m : Fin (J + 1),
          ((Polynomial.derivative^[m.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3, (L' m i : PowerSeries ℝ) * omega3PS r β₁ β₂ i =
        ((Polynomial.derivative^[J] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
          (((T_R * (T_R ^ J).derivative + T_R ^ J * TA_R k : Polynomial ℝ) : PowerSeries ℝ) *
            omega3PS r β₁ β₂ k) +
        ∑ j : Fin J,
          ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3,
              (((T_R * (L j i).derivative + TA_R i * L j i : Polynomial ℝ) : PowerSeries ℝ) *
                omega3PS r β₁ β₂ i) +
        ∑ j : Fin J,
          ((Polynomial.derivative^[j.val + 1] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
            ∑ i : Fin 3,
              (((T_R * L j i : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) := by
      have hsplitL' :
          ∑ m : Fin (J + 1),
            ((Polynomial.derivative^[m.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              ∑ i : Fin 3, (L' m i : PowerSeries ℝ) * omega3PS r β₁ β₂ i =
          (∑ m : Fin (J + 1),
            ((Polynomial.derivative^[m.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              ∑ i : Fin 3,
                ((if m.val = J then
                    (if i = k then T_R * (T_R ^ J).derivative + T_R ^ J * TA_R k else 0)
                  else 0 : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) +
          (∑ m : Fin (J + 1),
            ((Polynomial.derivative^[m.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              ∑ i : Fin 3,
                ((if h : m.val < J then
                    T_R * (L ⟨m.val, h⟩ i).derivative + TA_R i * L ⟨m.val, h⟩ i
                  else 0 : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) +
          (∑ m : Fin (J + 1),
            ((Polynomial.derivative^[m.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              ∑ i : Fin 3,
                ((if h : 0 < m.val then
                    T_R * L ⟨m.val - 1, by omega⟩ i
                  else 0 : Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [L', Polynomial.coe_add, add_mul]
      rw [hsplitL']
      congr 1
      · congr 1
        · rw [Finset.sum_eq_single (Fin.last J)]
          · simp only [Fin.val_last, ↓reduceIte]
            congr 1
            rw [Finset.sum_eq_single k]
            · simp
            · intro i _ hik; simp [hik]
            · intro hnot; exact absurd (Finset.mem_univ k) hnot
          · intro m _ hm
            have hmne : m.val ≠ J := fun h => hm (Fin.ext h)
            simp [hmne]
          · intro hnot; exact absurd (Finset.mem_univ _) hnot
        · rw [Fin.sum_univ_castSucc]
          have hlast : ¬ (Fin.last J).val < J := by simp
          simp only [Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, hlast, Polynomial.coe_zero, zero_mul,
            Finset.sum_const_zero, mul_zero, add_zero]
      · rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, lt_self_iff_false, ↓reduceDIte, Polynomial.coe_zero, zero_mul,
          Finset.sum_const_zero, mul_zero, zero_add, Fin.val_succ, Nat.succ_pos,
          Nat.add_sub_cancel]
    rw [hLHS1, hLHS2, hRHS] at hstep
    rw [hL'_sum]
    linear_combination hstep

private lemma exists_three_rows_det_ne_zero {N : ℕ} (v : Fin N → (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    ∃ k : Fin 3 → Fin N, Matrix.det (Matrix.of fun (j i : Fin 3) => v (k j) i) ≠ 0 := by
  obtain ⟨s, hs_sub, hspan_s, hli_s⟩ := exists_linearIndependent ℝ (Set.range v)
  rw [hspan] at hspan_s
  have : Fintype s := Set.Finite.fintype ((Set.finite_range v).subset hs_sub)
  let b : Module.Basis s ℝ (Fin 3 → ℝ) :=
    Module.Basis.mk hli_s (by rw [Subtype.range_coe]; exact hspan_s.ge)
  have hcard : Fintype.card s = 3 := by
    have h1 := Module.finrank_eq_card_basis b
    have h2 : Module.finrank ℝ (Fin 3 → ℝ) = 3 := Module.finrank_fin_fun ℝ
    omega
  let e : Fin 3 ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ j : Fin 3, ∃ idx : Fin N, v idx = (e j).val := fun j => hs_sub (e j).property
  choose k hk using hmem
  refine ⟨k, ?_⟩
  let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun j i => v (k j) i
  have hli_rows : LinearIndependent ℝ A := by
    have hA_eq : A = fun j => (e j).val := by
      ext j i
      exact congrFun (hk j) i
    rw [hA_eq]
    exact hli_s.comp e e.injective
  intro hdet0
  have hdetT : A.transpose.det = 0 := by rw [Matrix.det_transpose, hdet0]
  obtain ⟨c, hc_ne, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetT
  have hsum0 : ∑ j : Fin 3, c j • A j = 0 := by
    ext i
    have hi := congrFun hmul i
    simpa [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  have hc0 : ∀ j : Fin 3, c j = 0 := by
    intro j
    exact Fintype.linearIndependent_iff.mp hli_rows c hsum0 j
  exact hc_ne (funext hc0)

theorem P_ang_full_rank {r M β₁ β₂ : ℕ} (hr : 2 ≤ r) (hM : 1 ≤ M)
    (hβ1 : 2 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (hΔ : Delta r M β₁ β₂ P ≠ 0)
    {α : ℝ} (hTα : ((Tpoly r M).map (Int.castRingHom ℝ)).eval α ≠ 0) :
    let a := ((Delta r M β₁ β₂ P).map (Int.castRingHom ℝ)).rootMultiplicity α
    ∃ k : Fin 3 → ℕ, (∀ j, k j ≤ a + 2) ∧
      Matrix.det (Matrix.of fun (j i : Fin 3) => (P_ang r M β₁ β₂ P (k j) i).eval α) ≠ 0 := by
  intro a
  set T_R : Polynomial ℝ := (Tpoly r M).map (Int.castRingHom ℝ)
  set Δ_R : Polynomial ℝ := (Delta r M β₁ β₂ P).map (Int.castRingHom ℝ)
  have hΔR_ne : Δ_R ≠ 0 := by
    intro h0
    exact hΔ (Polynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective (by simpa [Δ_R] using h0))
  obtain ⟨hΔ_lt, hΔ_eq⟩ := rootMultiplicity_deriv_props hΔR_ne α
  let v_ang : Fin (a + 3) → (Fin 3 → ℝ) := fun l i => (P_ang r M β₁ β₂ P l.val i).eval α
  let v_sq : Fin (a + 3) → (Fin 3 → ℝ) := fun l i =>
    ((P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ)).eval α
  have hv_sq_mem : ∀ l : Fin (a + 3), v_sq l ∈ Submodule.span ℝ (Set.range v_ang) := by
    intro l
    have hrel : v_sq l = ∑ j ∈ Finset.range (l.val + 1),
        ((j.factorial : ℝ) * (q_poly T_R l.val j).eval α) •
          (fun i => (P_ang r M β₁ β₂ P j i).eval α) := by
      ext i
      dsimp only [v_sq]
      rw [P_sq_eq_sum_P_ang (by omega : 1 ≤ r) hM (by omega : 1 ≤ β₁) (by omega : β₁ ≤ M) hβ2 P l.val i]
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, T_R]
    rw [hrel]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    have hj_lt : j < a + 3 := by
      have := Finset.mem_range.mp hj
      have := l.isLt
      omega
    exact Submodule.subset_span ⟨⟨j, hj_lt⟩, rfl⟩
  have hspan_top : Submodule.span ℝ (Set.range v_ang) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx_decomp : x = ∑ k : Fin 3, x k • Pi.single k (1 : ℝ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hx_decomp]
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    obtain ⟨L, Mc, hcr⟩ :=
      cramer_iter_identity (by omega : 1 ≤ r) (by omega : β₁ ≤ M + 1) (by omega : β₂ ≤ M + 1) P k a
    have hcoeff_eq : ∀ i : Fin 3,
        (if i = k then T_R ^ a * Polynomial.derivative^[a] Δ_R else 0) +
          ∑ j : Fin a, Polynomial.derivative^[j.val] Δ_R * L j i -
          ∑ l : Fin (a + 3), Mc l * (P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ) = 0 := by
      let f : Fin 3 → Polynomial ℝ := fun i =>
        (if i = k then T_R ^ a * Polynomial.derivative^[a] Δ_R else 0) +
          ∑ j : Fin a, Polynomial.derivative^[j.val] Δ_R * L j i -
          ∑ l : Fin (a + 3), Mc l * (P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ)
      have hf_sum :
          ∑ i : Fin 3, (f i : PowerSeries ℝ) *
            omega_gen r (Finset.Ico 1 (beta3 β₁ β₂ i)) (fun j => (j : ℝ)) = 0 := by
        have h1 :
            ∑ i : Fin 3, ((if i = k then T_R ^ a * Polynomial.derivative^[a] Δ_R else 0 :
                Polynomial ℝ) : PowerSeries ℝ) * omega3PS r β₁ β₂ i =
            ((T_R ^ a * Polynomial.derivative^[a] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              omega3PS r β₁ β₂ k := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro i _ hik; simp [hik]
          · intro hnot; exact absurd (Finset.mem_univ k) hnot
        have h2 :
            ∑ i : Fin 3,
              (((∑ j : Fin a, Polynomial.derivative^[j.val] Δ_R * L j i : Polynomial ℝ) :
                PowerSeries ℝ)) * omega3PS r β₁ β₂ i =
            ∑ j : Fin a,
              ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
                ∑ i : Fin 3, (L j i : PowerSeries ℝ) * omega3PS r β₁ β₂ i := by
          simp_rw [coe_sum_poly, Finset.sum_mul, Finset.mul_sum, Polynomial.coe_mul, mul_assoc]
          exact Finset.sum_comm
        have h3 :
            ∑ i : Fin 3,
              (((∑ l : Fin (a + 3), Mc l * (P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ) :
                Polynomial ℝ) : PowerSeries ℝ)) * omega3PS r β₁ β₂ i =
            ∑ l : Fin (a + 3), (Mc l : PowerSeries ℝ) *
              ∑ i : Fin 3, ((P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
                omega3PS r β₁ β₂ i := by
          simp_rw [coe_sum_poly, Finset.sum_mul, Finset.mul_sum, Polynomial.coe_mul, mul_assoc]
          exact Finset.sum_comm
        have hsum_f :
            ∑ i : Fin 3, (f i : PowerSeries ℝ) * omega3PS r β₁ β₂ i =
            ((T_R ^ a * Polynomial.derivative^[a] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
              omega3PS r β₁ β₂ k +
            ∑ j : Fin a,
              ((Polynomial.derivative^[j.val] Δ_R : Polynomial ℝ) : PowerSeries ℝ) *
                ∑ i : Fin 3, (L j i : PowerSeries ℝ) * omega3PS r β₁ β₂ i -
            ∑ l : Fin (a + 3), (Mc l : PowerSeries ℝ) *
              ∑ i : Fin 3, ((P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ) : PowerSeries ℝ) *
                omega3PS r β₁ β₂ i := by
          rw [← h1, ← h2, ← h3, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [f, Polynomial.coe_sub, Polynomial.coe_add]
          ring
        have h0 : ∑ i : Fin 3, (f i : PowerSeries ℝ) * omega3PS r β₁ β₂ i = 0 := by
          rw [hsum_f, sub_eq_zero]
          exact hcr
        simpa [omega_gen, omega3PS, omegaPS] using h0
      have hnat_ne : ∀ j ∈ Finset.Ico 1 β₂, (j : ℝ) ≠ 0 := by
        intro j hj
        exact Nat.cast_ne_zero.mpr (by have := (Finset.mem_Ico.mp hj).1; omega)
      have hnat_inj : Set.InjOn (fun j : ℕ => (j : ℝ)) (Finset.Ico 1 β₂) :=
        fun j₁ _ j₂ _ h => Nat.cast_injective h
      exact omega_gen_lin_indep_fin3 hr hβ1 hβ12 hnat_ne hnat_inj hf_sum
    set cstar : ℝ := (T_R.eval α) ^ a * (Polynomial.derivative^[a] Δ_R).eval α
    have hcstar_ne : cstar ≠ 0 := mul_ne_zero (pow_ne_zero a hTα) hΔ_eq
    have hsingle :
        Pi.single k (1 : ℝ) = ∑ l : Fin (a + 3), (cstar⁻¹ * (Mc l).eval α) • v_sq l := by
      ext i
      have hi := congrArg (Polynomial.eval α) (hcoeff_eq i)
      simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_zero] at hi
      have hsum_j : ∑ j : Fin a, (Polynomial.derivative^[j.val] Δ_R).eval α * (L j i).eval α = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [hΔ_lt j.val j.isLt, zero_mul]
      rw [hsum_j, add_zero, sub_eq_zero] at hi
      have hlhs :
          (if i = k then T_R ^ a * Polynomial.derivative^[a] Δ_R else 0).eval α =
            if i = k then cstar else 0 := by
        split_ifs <;> simp [cstar]
      rw [hlhs] at hi
      simp only [Pi.single_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v_sq]
      have hsum_eq :
          ∑ l : Fin (a + 3), cstar⁻¹ * (Mc l).eval α *
            ((P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ)).eval α =
          cstar⁻¹ * ∑ l : Fin (a + 3), (Mc l).eval α *
            ((P_sq r M β₁ β₂ P l.val i).map (Int.castRingHom ℝ)).eval α := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
      rw [hsum_eq, ← hi]
      split_ifs
      · exact (inv_mul_cancel₀ hcstar_ne).symm
      · simp
    rw [hsingle]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hv_sq_mem l)
  obtain ⟨kidx, hdet⟩ := exists_three_rows_det_ne_zero v_ang hspan_top
  refine ⟨fun j => (kidx j).val, fun j => by dsimp only; have := (kidx j).isLt; omega, ?_⟩
  exact hdet

end Mod2

section Mod3
private lemma natDegree_one_sub_C_mul_X_le' {R : Type*} [CommRing R] (a : R) :
    (1 - Polynomial.C a * Polynomial.X).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le

private lemma Q_raw_natDegree_le (r β l : ℕ) :
    (Q_raw r β l).natDegree ≤ (β - 1) * l := by
  induction β generalizing l with
  | zero =>
    simp only [Q_raw, Nat.zero_sub, zero_mul]
    split_ifs <;> simp
  | succ β ih =>
    cases β with
    | zero =>
      simp only [Q_raw, Nat.sub_self, zero_mul]
      split_ifs <;> simp
    | succ β =>
      simp only [Q_raw]
      refine (Polynomial.natDegree_sum_le _ _).trans ?_
      refine Finset.sup_le fun a ha => ?_
      have hal : a ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have h1 : (Q_raw r (β + 1) a).natDegree ≤ β * a := by
        simpa [Nat.add_sub_cancel] using ih a
      have h2 : (∏ j ∈ Finset.Ico 1 (β + 1),
          (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)).natDegree ≤ β * (l - a) := by
        refine (Polynomial.natDegree_prod_le _ _).trans ?_
        have hterm : ∀ j ∈ Finset.Ico 1 (β + 1),
            ((1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)).natDegree ≤ l - a := fun j _ =>
          Polynomial.natDegree_pow_le.trans (by have := natDegree_one_sub_C_mul_X_le' (j : ℝ); nlinarith)
        exact (Finset.sum_le_sum hterm).trans (by simp)
      have h3 : (Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a))).natDegree = 0 :=
        Polynomial.natDegree_C _
      have h4 : ((1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a).natDegree ≤ a :=
        Polynomial.natDegree_pow_le.trans
          (by have := natDegree_one_sub_C_mul_X_le' (((β + 1 : ℕ) : ℝ)); nlinarith)
      have e1 := Polynomial.natDegree_mul_le (p := Q_raw r (β + 1) a *
        (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)) *
        Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)))
        (q := (1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a)
      have e2 := Polynomial.natDegree_mul_le (p := Q_raw r (β + 1) a *
        (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)))
        (q := Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)))
      have e3 := Polynomial.natDegree_mul_le (p := Q_raw r (β + 1) a)
        (q := ∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a))
      have hsum : β * a + β * (l - a) = β * l := by
        calc β * a + β * (l - a) = β * (a + (l - a)) := by ring
          _ = β * l := by rw [Nat.add_sub_of_le hal]
      dsimp only [Function.comp_apply]
      rw [show β + 1 + 1 - 1 = β + 1 by omega]
      nlinarith

private lemma Qpoly_natDegree_le {r M β l : ℕ} (hβ1 : 1 ≤ β) (hβM : β ≤ M) :
    (Qpoly r M β l).natDegree ≤ M * l := by
  unfold Qpoly
  have h1 : (Polynomial.C ((r : ℝ) ^ l)).natDegree = 0 := Polynomial.natDegree_C _
  have h2 : (∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l).natDegree ≤
      (M + 1 - β) * l := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have hterm : ∀ j ∈ Finset.Icc β M,
        ((1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l).natDegree ≤ l := fun j _ =>
      Polynomial.natDegree_pow_le.trans (by have := natDegree_one_sub_C_mul_X_le' (j : ℝ); nlinarith)
    exact (Finset.sum_le_sum hterm).trans (by simp [Nat.card_Icc])
  have h3 := Q_raw_natDegree_le r β l
  have e1 := Polynomial.natDegree_mul_le
    (p := Polynomial.C ((r : ℝ) ^ l) * ∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l)
    (q := Q_raw r β l)
  have e2 := Polynomial.natDegree_mul_le (p := Polynomial.C ((r : ℝ) ^ l))
    (q := ∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l)
  have hsum : (M + 1 - β) + (β - 1) = M := by omega
  calc (Polynomial.C ((r : ℝ) ^ l) *
          (∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l) *
          Q_raw r β l).natDegree
      ≤ (M + 1 - β) * l + (β - 1) * l := by omega
    _ = ((M + 1 - β) + (β - 1)) * l := by ring
    _ = M * l := by rw [hsum]

private lemma map_one_sub_nat_C_X (j : ℕ) :
    (1 - Polynomial.C (j : ℤ) * Polynomial.X).map (Int.castRingHom ℝ) =
      1 - Polynomial.C (j : ℝ) * Polynomial.X := by
  rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
  simp

private lemma Q_raw_int_mul {r : ℕ}
    (hdenom : ∀ k : ℕ, ∃ m : ℤ, ((r : ℝ) ^ (2 * k)) * negInvBinom r k = (m : ℝ))
    (β l : ℕ) :
    ∃ q : Polynomial ℤ, Polynomial.C ((r : ℝ) ^ (2 * l)) * Q_raw r β l = q.map (Int.castRingHom ℝ) := by
  induction β generalizing l with
  | zero =>
    simp only [Q_raw]
    split_ifs with hl
    · subst hl; exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
  | succ β ih =>
    cases β with
    | zero =>
      simp only [Q_raw]
      split_ifs with hl
      · subst hl; exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    | succ β =>
      simp only [Q_raw, Finset.mul_sum]
      have hterm : ∀ a ∈ Finset.range (l + 1), ∃ qa : Polynomial ℤ,
          Polynomial.C ((r : ℝ) ^ (2 * l)) *
            (Q_raw r (β + 1) a *
              (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)) *
              Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)) *
              (1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a) =
            qa.map (Int.castRingHom ℝ) := by
        intro a ha
        have hal : a ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        obtain ⟨q1, hq1⟩ := ih a
        obtain ⟨m, hm⟩ := hdenom (l - a)
        refine ⟨q1 *
          (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℤ) * Polynomial.X) ^ (l - a)) *
          Polynomial.C (m * ((β + 1 : ℕ) : ℤ) ^ (l - a)) *
          (1 - Polynomial.C ((β + 1 : ℕ) : ℤ) * Polynomial.X) ^ a, ?_⟩
        have hpow : (r : ℝ) ^ (2 * l) = (r : ℝ) ^ (2 * a) * (r : ℝ) ^ (2 * (l - a)) := by
          rw [← pow_add]; congr 1; omega
        rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
          Polynomial.map_prod, Polynomial.map_pow, Polynomial.map_C, map_one_sub_nat_C_X]
        have hprod_map : ∏ j ∈ Finset.Ico 1 (β + 1),
              ((1 - Polynomial.C (j : ℤ) * Polynomial.X) ^ (l - a)).map (Int.castRingHom ℝ) =
            ∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a) :=
          Finset.prod_congr rfl fun j _ => by rw [Polynomial.map_pow, map_one_sub_nat_C_X]
        rw [hprod_map, ← hq1, eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          ← hm, hpow, Polynomial.C_mul, Polynomial.C_mul, Polynomial.C_mul, Polynomial.C_mul]
        ring
      choose f hf using hterm
      refine ⟨∑ a ∈ (Finset.range (l + 1)).attach, f a.1 a.2, ?_⟩
      rw [Polynomial.map_sum, ← Finset.sum_attach (Finset.range (l + 1))]
      exact Finset.sum_congr rfl fun a _ => hf a.1 a.2

private lemma Qpoly_int_mul {r M β l : ℕ}
    (hdenom : ∀ k : ℕ, ∃ m : ℤ, ((r : ℝ) ^ (2 * k)) * negInvBinom r k = (m : ℝ)) :
    ∃ q : Polynomial ℤ, Polynomial.C ((r : ℝ) ^ l) * Qpoly r M β l = q.map (Int.castRingHom ℝ) := by
  obtain ⟨q0, hq0⟩ := Q_raw_int_mul hdenom β l
  refine ⟨(∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℤ) * Polynomial.X) ^ l) * q0, ?_⟩
  unfold Qpoly
  rw [Polynomial.map_mul, Polynomial.map_prod]
  have hprod_map : ∏ j ∈ Finset.Icc β M,
        ((1 - Polynomial.C (j : ℤ) * Polynomial.X) ^ l).map (Int.castRingHom ℝ) =
      ∏ j ∈ Finset.Icc β M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ l :=
    Finset.prod_congr rfl fun j _ => by rw [Polynomial.map_pow, map_one_sub_nat_C_X]
  rw [hprod_map, ← hq0]
  have hpow : (r : ℝ) ^ (2 * l) = (r : ℝ) ^ l * (r : ℝ) ^ l := by
    rw [← pow_add]; congr 1; omega
  rw [hpow, Polynomial.C_mul]
  ring

private lemma Q_raw_eval_bound {r M : ℕ}
    (hpos : ∀ k, 0 < negInvBinom r k) (hle : ∀ k, negInvBinom r k ≤ 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hxM : (M : ℝ) * x ≤ 1)
    {β : ℕ} (hβM : β ≤ M) (l : ℕ) :
    |(Q_raw r β l).eval x| ≤ ((l + β).choose l : ℝ) * (M : ℝ) ^ l := by
  induction β generalizing l with
  | zero =>
    simp only [Q_raw, add_zero, Nat.choose_self, Nat.cast_one, one_mul]
    split_ifs with hl
    · subst hl; simp
    · simp
  | succ β ih =>
    cases β with
    | zero =>
      simp only [Q_raw]
      split_ifs with hl
      · subst hl; simp
      · simp; positivity
    | succ β =>
      simp only [Q_raw, Polynomial.eval_finsetSum]
      have hlin_le : ∀ j : ℕ, j ≤ M → |1 - (j : ℝ) * x| ≤ 1 := by
        intro j hj
        have hjx0 : 0 ≤ (j : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx0
        have hjx1 : (j : ℝ) * x ≤ 1 :=
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) hx0).trans hxM
        rw [abs_of_nonneg (by linarith)]
        linarith
      have hstep : ∀ a ∈ Finset.range (l + 1),
          |(Q_raw r (β + 1) a *
              (∏ j ∈ Finset.Ico 1 (β + 1), (1 - Polynomial.C (j : ℝ) * Polynomial.X) ^ (l - a)) *
              Polynomial.C (negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)) *
              (1 - Polynomial.C ((β + 1 : ℕ) : ℝ) * Polynomial.X) ^ a).eval x| ≤
            ((a + (β + 1)).choose a : ℝ) * (M : ℝ) ^ l := by
        intro a ha
        have hal : a ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
        simp only [Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X,
          abs_mul, abs_prod, abs_pow]
        have h1 : |(Q_raw r (β + 1) a).eval x| ≤ ((a + (β + 1)).choose a : ℝ) * (M : ℝ) ^ a :=
          ih (by omega) a
        have h2 : ∏ j ∈ Finset.Ico 1 (β + 1), |1 - (j : ℝ) * x| ^ (l - a) ≤ 1 := by
          refine Finset.prod_le_one (fun j _ => by positivity) (fun j hj => ?_)
          exact pow_le_one₀ (abs_nonneg _) (hlin_le j (by have := (Finset.mem_Ico.mp hj).2; omega))
        have h3 : |negInvBinom r (l - a)| * |((β + 1 : ℕ) : ℝ)| ^ (l - a) ≤ (M : ℝ) ^ (l - a) := by
          rw [abs_of_pos (hpos _), abs_of_nonneg (Nat.cast_nonneg _)]
          calc negInvBinom r (l - a) * ((β + 1 : ℕ) : ℝ) ^ (l - a)
              ≤ 1 * (M : ℝ) ^ (l - a) :=
                mul_le_mul (hle _) (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show β + 1 ≤ M by omega)) _)
                  (by positivity) (by norm_num)
            _ = (M : ℝ) ^ (l - a) := one_mul _
        have h4 : |1 - ((β + 1 : ℕ) : ℝ) * x| ^ a ≤ 1 :=
          pow_le_one₀ (abs_nonneg _) (hlin_le (β + 1) (by omega))
        have hpowM : (M : ℝ) ^ a * (M : ℝ) ^ (l - a) = (M : ℝ) ^ l := by
          rw [← pow_add, Nat.add_sub_of_le hal]
        calc |(Q_raw r (β + 1) a).eval x| *
              (∏ j ∈ Finset.Ico 1 (β + 1), |1 - (j : ℝ) * x| ^ (l - a)) *
              (|negInvBinom r (l - a)| * |((β + 1 : ℕ) : ℝ)| ^ (l - a)) *
              |1 - ((β + 1 : ℕ) : ℝ) * x| ^ a
            ≤ (((a + (β + 1)).choose a : ℝ) * (M : ℝ) ^ a) * 1 * (M : ℝ) ^ (l - a) * 1 := by
              have hb0 : 0 ≤ ∏ j ∈ Finset.Ico 1 (β + 1), |1 - (j : ℝ) * x| ^ (l - a) :=
                Finset.prod_nonneg fun _ _ => by positivity
              have hc0 : 0 ≤ |negInvBinom r (l - a)| * |((β + 1 : ℕ) : ℝ)| ^ (l - a) := by positivity
              have hd0 : 0 ≤ |1 - ((β + 1 : ℕ) : ℝ) * x| ^ a := by positivity
              have p1 : |(Q_raw r (β + 1) a).eval x| *
                  (∏ j ∈ Finset.Ico 1 (β + 1), |1 - (j : ℝ) * x| ^ (l - a)) ≤
                  (((a + (β + 1)).choose a : ℝ) * (M : ℝ) ^ a) * 1 :=
                mul_le_mul h1 h2 hb0 (by positivity)
              have p2 := mul_le_mul p1 h3 hc0 (by positivity)
              exact mul_le_mul p2 h4 hd0 (by positivity)
          _ = ((a + (β + 1)).choose a : ℝ) * ((M : ℝ) ^ a * (M : ℝ) ^ (l - a)) := by ring
          _ = ((a + (β + 1)).choose a : ℝ) * (M : ℝ) ^ l := by rw [hpowM]
      have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hstep)
      have hhock : ∀ n : ℕ, ∑ a ∈ Finset.range (n + 1), (a + (β + 1)).choose a = (n + (β + 2)).choose n := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          rw [Finset.sum_range_succ, ihn]
          have hc : (n + (β + 2) + 1).choose (n + 1) =
              (n + (β + 2)).choose n + (n + (β + 2)).choose (n + 1) :=
            Nat.choose_succ_succ (n + (β + 2)) n
          have h1 : n + 1 + (β + 2) = n + (β + 2) + 1 := by omega
          have h2 : n + 1 + (β + 1) = n + (β + 2) := by omega
          rw [h1, h2, hc]
      calc |∑ a ∈ Finset.range (l + 1), _|
          ≤ ∑ a ∈ Finset.range (l + 1), ((a + (β + 1)).choose a : ℝ) * (M : ℝ) ^ l := hsum
        _ = (∑ a ∈ Finset.range (l + 1), ((a + (β + 1)).choose a : ℝ)) * (M : ℝ) ^ l := by
            rw [Finset.sum_mul]
        _ = ((l + (β + 2)).choose l : ℝ) * (M : ℝ) ^ l := by
            congr 1; exact_mod_cast hhock l

private lemma Qpoly_eval_bound {r M : ℕ}
    (hpos : ∀ k, 0 < negInvBinom r k) (hle : ∀ k, negInvBinom r k ≤ 1)
    {x : ℝ} (hx0 : 0 ≤ x) (hxM : (M : ℝ) * x ≤ 1)
    {β : ℕ} (hβM : β ≤ M) (l : ℕ) :
    |(Qpoly r M β l).eval x| ≤ (2 : ℝ) ^ M * (2 * (r : ℝ) * (M : ℝ)) ^ l := by
  unfold Qpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, abs_mul, abs_prod, abs_pow]
  have hprod : ∏ j ∈ Finset.Icc β M, |1 - (j : ℝ) * x| ^ l ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => by positivity) (fun j hj => ?_)
    have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
    have hjx1 : (j : ℝ) * x ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hjM) hx0).trans hxM
    have habs : |1 - (j : ℝ) * x| ≤ 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith [mul_nonneg (Nat.cast_nonneg j) hx0]
    exact pow_le_one₀ (abs_nonneg _) habs
  have hraw := Q_raw_eval_bound hpos hle hx0 hxM hβM l
  have hchoose : ((l + β).choose l : ℝ) ≤ (2 : ℝ) ^ (l + M) := by
    have hc1 : (l + β).choose l ≤ 2 ^ (l + β) := Nat.choose_le_two_pow _ _
    have hc2 : 2 ^ (l + β) ≤ 2 ^ (l + M) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast hc1.trans hc2
  rw [abs_of_nonneg (Nat.cast_nonneg r)]
  calc (r : ℝ) ^ l * (∏ j ∈ Finset.Icc β M, |1 - (j : ℝ) * x| ^ l) * |(Q_raw r β l).eval x|
      ≤ (r : ℝ) ^ l * 1 * (((l + β).choose l : ℝ) * (M : ℝ) ^ l) := by
        have p1 : (r : ℝ) ^ l * (∏ j ∈ Finset.Icc β M, |1 - (j : ℝ) * x| ^ l) ≤ (r : ℝ) ^ l * 1 :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
        exact mul_le_mul p1 hraw (abs_nonneg _) (by positivity)
    _ ≤ (r : ℝ) ^ l * 1 * ((2 : ℝ) ^ (l + M) * (M : ℝ) ^ l) := by
        gcongr
    _ = (2 : ℝ) ^ M * (2 * (r : ℝ) * (M : ℝ)) ^ l := by
        rw [pow_add]; ring

private lemma iterate_deriv_poly_eq (f : Polynomial ℝ) (n : ℕ) :
    (Polynomial.derivative^[n] f) =
      ∑ v ∈ Finset.range (f.natDegree + 1),
        Polynomial.C (f.coeff v * ((v.descFactorial n : ℕ) : ℝ)) * Polynomial.X ^ (v - n) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, Nat.descFactorial_zero, Nat.cast_one, mul_one,
      Nat.sub_zero]
    exact Polynomial.as_sum_range_C_mul_X_pow f
  | succ n ihn =>
    rw [Function.iterate_succ_apply', ihn, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Polynomial.derivative_C_mul_X_pow]
    by_cases hvn : n < v
    · have hsub : v - n - 1 = v - (n + 1) := by omega
      have hdesc : v.descFactorial (n + 1) = (v - n) * v.descFactorial n := Nat.descFactorial_succ v n
      rw [hsub, hdesc, Nat.cast_mul]
      congr 1; congr 1; ring
    · have h0 : v - n = 0 := by omega
      have hdesc : v.descFactorial (n + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [h0, hdesc]; simp

private lemma iterate_deriv_div_factorial_int (p : Polynomial ℤ) (h : ℕ) :
    ∃ q : Polynomial ℤ,
      Polynomial.C (1 / (h.factorial : ℝ)) *
        (Polynomial.derivative^[h] (p.map (Int.castRingHom ℝ))) =
        q.map (Int.castRingHom ℝ) ∧
      q.natDegree ≤ p.natDegree := by
  refine ⟨∑ v ∈ Finset.range (p.natDegree + 1),
      Polynomial.C (p.coeff v * (v.choose h : ℤ)) * Polynomial.X ^ (v - h), ?_, ?_⟩
  · have hdeg_map : (p.map (Int.castRingHom ℝ)).natDegree ≤ p.natDegree :=
      Polynomial.natDegree_map_le
    rw [iterate_deriv_poly_eq, Finset.mul_sum, Polynomial.map_sum]
    have heq_sum : ∑ v ∈ Finset.range ((p.map (Int.castRingHom ℝ)).natDegree + 1),
          Polynomial.C (1 / (h.factorial : ℝ)) *
            (Polynomial.C ((p.map (Int.castRingHom ℝ)).coeff v * ((v.descFactorial h : ℕ) : ℝ)) *
              Polynomial.X ^ (v - h)) =
        ∑ v ∈ Finset.range (p.natDegree + 1),
          Polynomial.C (1 / (h.factorial : ℝ)) *
            (Polynomial.C ((p.map (Int.castRingHom ℝ)).coeff v * ((v.descFactorial h : ℕ) : ℝ)) *
              Polynomial.X ^ (v - h)) := by
      refine Finset.sum_subset (Finset.range_mono (by omega)) fun v _ hv => ?_
      have hgt : (p.map (Int.castRingHom ℝ)).natDegree < v := by
        simp only [Finset.mem_range, not_lt] at hv; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]; simp
    rw [heq_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.coeff_map, eq_intCast, eq_intCast, Int.cast_mul, Int.cast_natCast,
      ← mul_assoc, ← Polynomial.C_mul]
    congr 2
    have hch : (v.descFactorial h : ℝ) = (v.choose h : ℝ) * (h.factorial : ℝ) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose v h).trans (mul_comm _ _)
    rw [hch]
    have hfac : (h.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)
    field_simp [hfac]
  · refine (Polynomial.natDegree_sum_le _ _).trans ?_
    refine Finset.sup_le fun v hv => ?_
    have hv' : v ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
    calc (Polynomial.C (p.coeff v * (v.choose h : ℤ)) * Polynomial.X ^ (v - h)).natDegree
        ≤ (Polynomial.C (p.coeff v * (v.choose h : ℤ))).natDegree + (Polynomial.X ^ (v - h)).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ 0 + (v - h) := by rw [Polynomial.natDegree_C]; simp
      _ ≤ p.natDegree := by omega

private lemma Tpoly_natDegree_le' (r M : ℕ) :
    (Tpoly r M).natDegree ≤ M := by
  unfold Tpoly
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [Polynomial.natDegree_C, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h1 : ∀ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℤ) * Polynomial.X).natDegree ≤ 1 :=
    fun j _ => natDegree_one_sub_C_mul_X_le' (j : ℤ)
  exact (Finset.sum_le_sum h1).trans (by simp)

private lemma P_ang_int_mul_and_deg {r M β₁ β₂ D : ℕ}
    (hdenom : ∀ k : ℕ, ∃ m : ℤ, ((r : ℝ) ^ (2 * k)) * negInvBinom r k = (m : ℝ))
    (hβ1 : 1 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (hdeg : ∀ i, (P i).natDegree ≤ D) (k : ℕ) (i : Fin 3) :
    ∃ q : Polynomial ℤ,
      Polynomial.C ((r : ℝ) ^ k) * P_ang r M β₁ β₂ P k i = q.map (Int.castRingHom ℝ) ∧
      q.natDegree ≤ D + k * M := by
  unfold P_ang
  rw [Finset.mul_sum]
  have hbeta_ge : 1 ≤ beta3 β₁ β₂ i := by
    fin_cases i <;> simp [beta3] <;> omega
  have hbeta_le : beta3 β₁ β₂ i ≤ M := by
    fin_cases i <;> simp [beta3] <;> omega
  have hterm : ∀ l ∈ Finset.range (k + 1), ∃ ql : Polynomial ℤ,
      Polynomial.C ((r : ℝ) ^ k) *
        ((((Tpoly r M).map (Int.castRingHom ℝ)) ^ (k - l) *
          Polynomial.C (1 / ((k - l).factorial : ℝ)) *
          (Polynomial.derivative^[k - l] ((P i).map (Int.castRingHom ℝ)))) *
          Qpoly r M (beta3 β₁ β₂ i) l) =
        ql.map (Int.castRingHom ℝ) ∧
      ql.natDegree ≤ D + k * M := by
    intro l hl
    have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    obtain ⟨qP, hqP, hqPdeg⟩ := iterate_deriv_div_factorial_int (P i) (k - l)
    obtain ⟨qQ, hqQ⟩ := Qpoly_int_mul (M := M) (β := beta3 β₁ β₂ i) (l := l) hdenom
    have hqQdeg : qQ.natDegree ≤ M * l := by
      have hmap_deg : (qQ.map (Int.castRingHom ℝ)).natDegree = qQ.natDegree :=
        Polynomial.natDegree_map_eq_of_injective Int.cast_injective _
      rw [← hmap_deg, ← hqQ]
      exact (Polynomial.natDegree_C_mul_le _ _).trans (Qpoly_natDegree_le hbeta_ge hbeta_le)
    refine ⟨Polynomial.C ((r : ℤ) ^ (k - l)) * (Tpoly r M) ^ (k - l) * qP * qQ, ?_, ?_⟩
    · have hpow : (r : ℝ) ^ k = (r : ℝ) ^ (k - l) * (r : ℝ) ^ l := by
        rw [← pow_add, Nat.sub_add_cancel hlk]
      rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_pow, eq_intCast, Int.cast_pow, Int.cast_natCast,
        ← hqP, ← hqQ, hpow, Polynomial.C_mul]
      ring
    · have hTdeg : ((Tpoly r M) ^ (k - l)).natDegree ≤ (k - l) * M :=
        Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (Tpoly_natDegree_le' r M))
      have h1 := Polynomial.natDegree_mul_le (p := Polynomial.C ((r : ℤ) ^ (k - l)) * (Tpoly r M) ^ (k - l) * qP) (q := qQ)
      have h2 := Polynomial.natDegree_mul_le (p := Polynomial.C ((r : ℤ) ^ (k - l)) * (Tpoly r M) ^ (k - l)) (q := qP)
      have h3 := Polynomial.natDegree_mul_le (p := Polynomial.C ((r : ℤ) ^ (k - l))) (q := (Tpoly r M) ^ (k - l))
      rw [Polynomial.natDegree_C] at h3
      have hdegP : (P i).natDegree ≤ D := hdeg i
      have hmul_sum : (k - l) * M + M * l = k * M := by
        calc (k - l) * M + M * l = (k - l + l) * M := by ring
          _ = k * M := by rw [Nat.sub_add_cancel hlk]
      omega
  choose f hf1 hf2 using hterm
  refine ⟨∑ l ∈ (Finset.range (k + 1)).attach, f l.1 l.2, ?_, ?_⟩
  · rw [Polynomial.map_sum, ← Finset.sum_attach (Finset.range (k + 1))]
    exact Finset.sum_congr rfl fun l _ => hf1 l.1 l.2
  · refine (Polynomial.natDegree_sum_le _ _).trans ?_
    exact Finset.sup_le fun l _ => hf2 l.1 l.2

private lemma int_poly_eval_inv_nat_mul_pow (q : Polynomial ℤ) {d n : ℕ}
    (hdeg : q.natDegree ≤ d) (hn : 1 ≤ n) :
    ∃ m : ℤ, ((n : ℝ) ^ d) * (q.map (Int.castRingHom ℝ)).eval (1 / (n : ℝ)) = (m : ℝ) := by
  refine ⟨∑ v ∈ Finset.range (d + 1), q.coeff v * (n : ℤ) ^ (d - v), ?_⟩
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans hdeg))]
  rw [Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun v hv => ?_
  have hvd : v ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hv)
  rw [Polynomial.coeff_map, eq_intCast]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpow : (n : ℝ) ^ d * (1 / (n : ℝ)) ^ v = (n : ℝ) ^ (d - v) := by
    have hsplit : (n : ℝ) ^ d = (n : ℝ) ^ (d - v) * (n : ℝ) ^ v := by
      rw [← pow_add, Nat.sub_add_cancel hvd]
    rw [hsplit, one_div, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero v hn0), mul_one]
  calc (n : ℝ) ^ d * ((q.coeff v : ℝ) * (1 / (n : ℝ)) ^ v)
      = (q.coeff v : ℝ) * ((n : ℝ) ^ d * (1 / (n : ℝ)) ^ v) := by ring
    _ = (q.coeff v : ℝ) * (n : ℝ) ^ (d - v) := by rw [hpow]

private lemma P_ang_denom_int {r M β₁ β₂ D : ℕ}
    (hdenom : ∀ k : ℕ, ∃ m : ℤ, ((r : ℝ) ^ (2 * k)) * negInvBinom r k = (m : ℝ))
    (hβ1 : 1 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M)
    (P : Fin 3 → Polynomial ℤ) (hdeg : ∀ i, (P i).natDegree ≤ D) (k n : ℕ) (hn : 1 ≤ n) (i : Fin 3) :
    ∃ m : ℤ, ((r : ℝ) ^ k * (n : ℝ) ^ (D + k * M)) *
        (P_ang r M β₁ β₂ P k i).eval (1 / (n : ℝ)) = (m : ℝ) := by
  obtain ⟨q, hq, hqdeg⟩ := P_ang_int_mul_and_deg hdenom hβ1 hβ12 hβ2 P hdeg k i
  obtain ⟨m, hm⟩ := int_poly_eval_inv_nat_mul_pow q hqdeg hn
  refine ⟨m, ?_⟩
  have hev := congrArg (Polynomial.eval (1 / (n : ℝ))) hq
  simp only [Polynomial.eval_mul, Polynomial.eval_C] at hev
  rw [← hm, ← hev]
  ring

private lemma Tpoly_eval_inv_le {r M n : ℕ} (hMn : M ≤ n) (hn : 1 ≤ n) :
    |((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))| ≤ (r : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hxM : (M : ℝ) * (1 / (n : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hn_pos]; exact_mod_cast hMn
  unfold Tpoly
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, eq_intCast, Int.cast_natCast]
  have hprod_map : ∏ j ∈ Finset.Icc 1 M,
        (1 - Polynomial.C (j : ℤ) * Polynomial.X).map (Int.castRingHom ℝ) =
      ∏ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) :=
    Finset.prod_congr rfl fun j _ => map_one_sub_nat_C_X j
  rw [hprod_map, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, abs_mul, abs_prod,
    abs_of_nonneg (Nat.cast_nonneg r)]
  have hpr : ∏ j ∈ Finset.Icc 1 M, |(1 - Polynomial.C (j : ℝ) * Polynomial.X).eval (1 / (n : ℝ))| ≤ 1 := by
    refine Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j hj => ?_)
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
    have hjn : (j : ℝ) * (1 / (n : ℝ)) ≤ 1 :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hjM) hx0).trans hxM
    rw [abs_of_nonneg (by linarith)]
    linarith [mul_nonneg (Nat.cast_nonneg j) hx0]
  calc (r : ℝ) * ∏ j ∈ Finset.Icc 1 M, |(1 - Polynomial.C (j : ℝ) * Polynomial.X).eval (1 / (n : ℝ))|
      ≤ (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg r)
    _ = (r : ℝ) := mul_one _

private lemma nat_succ_le_two_pow (m : ℕ) : ((m + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    push_cast at ih ⊢
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
    rw [pow_succ]; linarith

private lemma P_ang_eval_bound {r M β₁ β₂ D N n k : ℕ}
    (hpos : ∀ j, 0 < negInvBinom r j) (hle : ∀ j, negInvBinom r j ≤ 1)
    (hM : 1 ≤ M) (hβ1 : 1 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M)
    (hMN : 8 * M ≤ N) (hNn : N ≤ n) (hn2N : n < 2 * N)
    (P : Fin 3 → Polynomial ℤ) (hdeg : ∀ i, (P i).natDegree ≤ D)
    {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hPbd : ∀ i v, (|(P i).coeff v| : ℝ) ≤ C0 * (2 * (M : ℝ)) ^ v)
    (i : Fin 3) :
    |(P_ang r M β₁ β₂ P k i).eval (1 / (n : ℝ))| ≤
      (4 * (r : ℝ) * (N : ℝ)) ^ k * (4 : ℝ) ^ M * C0 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hxM : (M : ℝ) * (1 / (n : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hn_pos]; exact_mod_cast (show M ≤ n by omega)
  have h4Mn : 4 * (M : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (show 4 * M * 2 ≤ 1 * n by omega)
  have hTeval : |((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))| ≤ (r : ℝ) :=
    Tpoly_eval_inv_le (by omega) (by omega)
  have hPderiv : ∀ h : ℕ,
      |(Polynomial.C (1 / (h.factorial : ℝ)) *
          (Polynomial.derivative^[h] ((P i).map (Int.castRingHom ℝ)))).eval (1 / (n : ℝ))| ≤
        2 * (n : ℝ) ^ h * C0 := by
    intro h
    have hiter_eval :
        (Polynomial.C (1 / (h.factorial : ℝ)) *
          (Polynomial.derivative^[h] ((P i).map (Int.castRingHom ℝ)))).eval (1 / (n : ℝ)) =
        ∑ v ∈ Finset.range ((P i).natDegree + 1),
          ((P i).coeff v : ℝ) * (v.choose h : ℝ) * (1 / (n : ℝ)) ^ (v - h) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, iterate_deriv_poly_eq, Polynomial.eval_finsetSum,
        Finset.mul_sum]
      have hdeg_le : ((P i).map (Int.castRingHom ℝ)).natDegree ≤ (P i).natDegree :=
        Polynomial.natDegree_map_le
      have hsub_sum :
          ∑ v ∈ Finset.range (((P i).map (Int.castRingHom ℝ)).natDegree + 1),
            1 / (h.factorial : ℝ) *
              (Polynomial.C (((P i).map (Int.castRingHom ℝ)).coeff v * ((v.descFactorial h : ℕ) : ℝ)) *
                Polynomial.X ^ (v - h)).eval (1 / (n : ℝ)) =
          ∑ v ∈ Finset.range ((P i).natDegree + 1),
            1 / (h.factorial : ℝ) *
              (Polynomial.C (((P i).map (Int.castRingHom ℝ)).coeff v * ((v.descFactorial h : ℕ) : ℝ)) *
                Polynomial.X ^ (v - h)).eval (1 / (n : ℝ)) := by
        refine Finset.sum_subset (Finset.range_mono (by omega)) fun v _ hv => ?_
        have hgt : ((P i).map (Int.castRingHom ℝ)).natDegree < v := by
          simp only [Finset.mem_range, not_lt] at hv; omega
        simp [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
      rw [hsub_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.coeff_map, eq_intCast]
      have hch : (v.descFactorial h : ℝ) = (v.choose h : ℝ) * (h.factorial : ℝ) := by
        exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose v h).trans (mul_comm _ _)
      have hfac : (h.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)
      rw [hch]; field_simp [hfac]
    rw [hiter_eval]
    have hterm_bd : ∀ v ∈ Finset.range ((P i).natDegree + 1),
        |((P i).coeff v : ℝ) * (v.choose h : ℝ) * (1 / (n : ℝ)) ^ (v - h)| ≤
          (n : ℝ) ^ h * C0 * (1 / 2 : ℝ) ^ v := by
      intro v _
      by_cases hhv : h ≤ v
      · have hch0 : (0 : ℝ) ≤ (v.choose h : ℝ) := Nat.cast_nonneg _
        have hpow0 : (0 : ℝ) ≤ (1 / (n : ℝ)) ^ (v - h) := pow_nonneg hx0 _
        rw [abs_mul, abs_mul, abs_of_nonneg hch0, abs_of_nonneg hpow0]
        have hch : (v.choose h : ℝ) ≤ (2 : ℝ) ^ v := by exact_mod_cast Nat.choose_le_two_pow v h
        have hpow_n : (1 / (n : ℝ)) ^ (v - h) = (n : ℝ) ^ h * (1 / (n : ℝ)) ^ v := by
          have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
          have hsplit : (n : ℝ) ^ v = (n : ℝ) ^ (v - h) * (n : ℝ) ^ h := by
            rw [← pow_add, Nat.sub_add_cancel hhv]
          rw [one_div, inv_pow, inv_pow, hsplit, mul_inv, mul_left_comm,
            mul_inv_cancel₀ (pow_ne_zero h hn0), mul_one]
        have hpv : |((P i).coeff v : ℝ)| ≤ C0 * (2 * (M : ℝ)) ^ v := by
          simpa using hPbd i v
        calc |((P i).coeff v : ℝ)| * (v.choose h : ℝ) * (1 / (n : ℝ)) ^ (v - h)
            ≤ (C0 * (2 * (M : ℝ)) ^ v) * (2 : ℝ) ^ v * ((n : ℝ) ^ h * (1 / (n : ℝ)) ^ v) := by
              rw [← hpow_n]
              have p1 := mul_le_mul hpv hch (Nat.cast_nonneg _) (by positivity)
              exact mul_le_mul_of_nonneg_right p1 (pow_nonneg hx0 _)
          _ = (n : ℝ) ^ h * C0 * (4 * (M : ℝ) / (n : ℝ)) ^ v := by
              have h4 : (4 * (M : ℝ) / (n : ℝ)) ^ v = (2 * (M : ℝ)) ^ v * (2 : ℝ) ^ v * (1 / (n : ℝ)) ^ v := by
                rw [div_pow, one_div, inv_pow, ← mul_pow, div_eq_mul_inv,
                  show (4 : ℝ) * (M : ℝ) = 2 * (M : ℝ) * 2 by ring]
              rw [h4]; ring
          _ ≤ (n : ℝ) ^ h * C0 * (1 / 2 : ℝ) ^ v := by
              gcongr
      · have hch0 : v.choose h = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [hch0]; simp; positivity
    calc |∑ v ∈ Finset.range ((P i).natDegree + 1), _|
        ≤ ∑ v ∈ Finset.range ((P i).natDegree + 1), (n : ℝ) ^ h * C0 * (1 / 2 : ℝ) ^ v :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm_bd)
      _ = (n : ℝ) ^ h * C0 * ∑ v ∈ Finset.range ((P i).natDegree + 1), (1 / 2 : ℝ) ^ v := by
          rw [← Finset.mul_sum]
      _ ≤ (n : ℝ) ^ h * C0 * 2 := by
          have hgeom : ∑ v ∈ Finset.range ((P i).natDegree + 1), (1 / 2 : ℝ) ^ v ≤ 2 := by
            rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
            have h0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ ((P i).natDegree + 1) := by positivity
            have hdiv : ((1 / 2 : ℝ) ^ ((P i).natDegree + 1) - 1) / (1 / 2 - 1) =
                2 - 2 * (1 / 2 : ℝ) ^ ((P i).natDegree + 1) := by ring
            linarith
          exact mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 2 * (n : ℝ) ^ h * C0 := by ring
  unfold P_ang
  rw [Polynomial.eval_finsetSum]
  have hbeta_le : beta3 β₁ β₂ i ≤ M := by
    fin_cases i <;> simp [beta3] <;> omega
  have hterm : ∀ l ∈ Finset.range (k + 1),
      |((((Tpoly r M).map (Int.castRingHom ℝ)) ^ (k - l) *
          Polynomial.C (1 / ((k - l).factorial : ℝ)) *
          (Polynomial.derivative^[k - l] ((P i).map (Int.castRingHom ℝ)))) *
        Qpoly r M (beta3 β₁ β₂ i) l).eval (1 / (n : ℝ))| ≤
      2 * (2 : ℝ) ^ M * ((r : ℝ) * (n : ℝ)) ^ k * C0 := by
    intro l hl
    have hlk : l ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
    have hmul_assoc :
        (((Tpoly r M).map (Int.castRingHom ℝ)) ^ (k - l) *
          Polynomial.C (1 / ((k - l).factorial : ℝ)) *
          (Polynomial.derivative^[k - l] ((P i).map (Int.castRingHom ℝ)))) *
        Qpoly r M (beta3 β₁ β₂ i) l =
        ((Tpoly r M).map (Int.castRingHom ℝ)) ^ (k - l) *
          (Polynomial.C (1 / ((k - l).factorial : ℝ)) *
            (Polynomial.derivative^[k - l] ((P i).map (Int.castRingHom ℝ)))) *
          Qpoly r M (beta3 β₁ β₂ i) l := by ring
    rw [hmul_assoc]
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow, abs_mul, abs_mul, abs_pow]
    have hTkl : |((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))| ^ (k - l) ≤
        (r : ℝ) ^ (k - l) := pow_le_pow_left₀ (abs_nonneg _) hTeval _
    have hPd := hPderiv (k - l)
    have hQ := Qpoly_eval_bound hpos hle hx0 hxM hbeta_le l
    have h2rM : (2 * (r : ℝ) * (M : ℝ)) ^ l ≤ ((r : ℝ) * (n : ℝ)) ^ l := by
      refine pow_le_pow_left₀ (by positivity) ?_ l
      have h2Mn : (2 * M : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 2 * M ≤ n by omega)
      nlinarith [Nat.cast_nonneg (α := ℝ) r]
    have hQ' : |(Qpoly r M (beta3 β₁ β₂ i) l).eval (1 / (n : ℝ))| ≤
        (2 : ℝ) ^ M * ((r : ℝ) * (n : ℝ)) ^ l :=
      hQ.trans (mul_le_mul_of_nonneg_left h2rM (by positivity))
    have hrn_pow : (r : ℝ) ^ (k - l) * (n : ℝ) ^ (k - l) * ((r : ℝ) * (n : ℝ)) ^ l =
        ((r : ℝ) * (n : ℝ)) ^ k := by
      rw [← mul_pow, ← pow_add, Nat.sub_add_cancel hlk]
    calc |((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))| ^ (k - l) *
            |(Polynomial.C (1 / ((k - l).factorial : ℝ)) *
              (Polynomial.derivative^[k - l] ((P i).map (Int.castRingHom ℝ)))).eval (1 / (n : ℝ))| *
            |(Qpoly r M (beta3 β₁ β₂ i) l).eval (1 / (n : ℝ))|
        ≤ (r : ℝ) ^ (k - l) * (2 * (n : ℝ) ^ (k - l) * C0) * ((2 : ℝ) ^ M * ((r : ℝ) * (n : ℝ)) ^ l) := by
          have p1 := mul_le_mul hTkl hPd (abs_nonneg _) (by positivity)
          exact mul_le_mul p1 hQ' (abs_nonneg _) (by positivity)
      _ = 2 * (2 : ℝ) ^ M * ((r : ℝ) ^ (k - l) * (n : ℝ) ^ (k - l) * ((r : ℝ) * (n : ℝ)) ^ l) * C0 := by ring
      _ = 2 * (2 : ℝ) ^ M * ((r : ℝ) * (n : ℝ)) ^ k * C0 := by rw [hrn_pow]
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := nat_succ_le_two_pow k
  have h2M : (2 : ℝ) * (2 : ℝ) ^ M ≤ (4 : ℝ) ^ M := by
    have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ M := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (2 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hM
    calc (2 : ℝ) * (2 : ℝ) ^ M ≤ (2 : ℝ) ^ M * (2 : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (4 : ℝ) ^ M := by rw [← mul_pow]; norm_num
  have hn_le : ((r : ℝ) * (n : ℝ)) ^ k ≤ (2 * (r : ℝ) * (N : ℝ)) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    have : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (show n ≤ 2 * N by omega)
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  calc |∑ l ∈ Finset.range (k + 1), _|
      ≤ ((k + 1 : ℕ) : ℝ) * (2 * (2 : ℝ) ^ M * ((r : ℝ) * (n : ℝ)) ^ k * C0) := hsum
    _ ≤ (2 : ℝ) ^ k * ((4 : ℝ) ^ M * (2 * (r : ℝ) * (N : ℝ)) ^ k * C0) := by
        have p1 : 2 * (2 : ℝ) ^ M * ((r : ℝ) * (n : ℝ)) ^ k ≤ (4 : ℝ) ^ M * (2 * (r : ℝ) * (N : ℝ)) ^ k :=
          mul_le_mul h2M hn_le (by positivity) (by positivity)
        have p2 := mul_le_mul_of_nonneg_right p1 hC0
        exact mul_le_mul hk1 p2 (by positivity) (by positivity)
    _ = (4 * (r : ℝ) * (N : ℝ)) ^ k * (4 : ℝ) ^ M * C0 := by
        rw [show (4 * (r : ℝ) * (N : ℝ)) ^ k = (2 : ℝ) ^ k * (2 * (r : ℝ) * (N : ℝ)) ^ k by
          rw [← mul_pow]; congr 1; ring]
        ring


private def EvalAt (f : PowerSeries ℝ) (x s : ℝ) : Prop :=
  Summable (fun n => ‖PowerSeries.coeff n f * x ^ n‖) ∧
  (∑' n, PowerSeries.coeff n f * x ^ n) = s

private lemma EvalAt.unique {f : PowerSeries ℝ} {x s₁ s₂ : ℝ}
    (h1 : EvalAt f x s₁) (h2 : EvalAt f x s₂) : s₁ = s₂ :=
  h1.2.symm.trans h2.2

private lemma EvalAt_zero (x : ℝ) : EvalAt 0 x 0 := by
  refine ⟨by simp, by simp⟩

private lemma EvalAt_one (x : ℝ) : EvalAt 1 x 1 := by
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    simp only [Finset.mem_singleton] at hn
    simp [PowerSeries.coeff_one, hn]
  · rw [tsum_eq_single 0]
    · simp [PowerSeries.coeff_one]
    · intro n hn; simp [PowerSeries.coeff_one, hn]

private lemma EvalAt_poly (p : Polynomial ℝ) (x : ℝ) :
    EvalAt (p : PowerSeries ℝ) x (p.eval x) := by
  refine ⟨?_, ?_⟩
  · refine summable_of_ne_finset_zero (s := Finset.range (p.natDegree + 1)) fun n hn => ?_
    simp only [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  · rw [tsum_eq_sum (s := Finset.range (p.natDegree + 1))]
    · rw [Polynomial.eval_eq_sum_range]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Polynomial.coeff_coe]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

private lemma EvalAt_add {f g : PowerSeries ℝ} {x sf sg : ℝ}
    (hf : EvalAt f x sf) (hg : EvalAt g x sg) :
    EvalAt (f + g) x (sf + sg) := by
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hf.1.add hg.1)
    rw [map_add, add_mul]
    exact norm_add_le _ _
  · simp_rw [map_add, add_mul]
    rw [Summable.tsum_add hf.1.of_norm hg.1.of_norm, hf.2, hg.2]

private lemma EvalAt_smul {f : PowerSeries ℝ} {x sf : ℝ} (c : ℝ)
    (hf : EvalAt f x sf) :
    EvalAt (c • f) x (c * sf) := by
  refine ⟨?_, ?_⟩
  · have : (fun n => ‖PowerSeries.coeff n (c • f) * x ^ n‖) =
        fun n => ‖c‖ * ‖PowerSeries.coeff n f * x ^ n‖ := by
      ext n; rw [map_smul, smul_eq_mul, mul_assoc, norm_mul]
    rw [this]
    exact hf.1.mul_left _
  · simp_rw [map_smul, smul_eq_mul, mul_assoc]
    rw [tsum_mul_left, hf.2]

private lemma EvalAt_mul {f g : PowerSeries ℝ} {x sf sg : ℝ}
    (hf : EvalAt f x sf) (hg : EvalAt g x sg) :
    EvalAt (f * g) x (sf * sg) := by
  have hrange : ∀ n, PowerSeries.coeff n (f * g) * x ^ n =
      ∑ k ∈ Finset.range (n + 1),
        (PowerSeries.coeff k f * x ^ k) * (PowerSeries.coeff (n - k) g * x ^ (n - k)) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun k l => PowerSeries.coeff k f * PowerSeries.coeff l g * x ^ n)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hpow : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add, Nat.add_sub_of_le hkn]
    rw [hpow]; ring
  refine ⟨?_, ?_⟩
  · have h1 := summable_norm_sum_mul_range_of_summable_norm hf.1 hg.1
    simpa only [hrange] using h1
  · have h2 := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.1 hg.1
    rw [hf.2, hg.2] at h2
    simpa only [hrange] using h2.symm

private lemma EvalAt_pow {f : PowerSeries ℝ} {x sf : ℝ} (hf : EvalAt f x sf) (k : ℕ) :
    EvalAt (f ^ k) x (sf ^ k) := by
  induction k with
  | zero => simpa using EvalAt_one x
  | succ k ih => rw [pow_succ, pow_succ]; exact EvalAt_mul ih hf

private lemma EvalAt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ)
    (v : ι → ℝ) (x : ℝ) (h : ∀ i ∈ s, EvalAt (f i) x (v i)) :
    EvalAt (∑ i ∈ s, f i) x (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EvalAt_zero x
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact EvalAt_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma EvalAt_finset_prod {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℝ)
    (v : ι → ℝ) (x : ℝ) (h : ∀ i ∈ s, EvalAt (f i) x (v i)) :
    EvalAt (∏ i ∈ s, f i) x (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using EvalAt_one x
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact EvalAt_mul (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private lemma negInvBinom_pos_local {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : 0 < negInvBinom r k := by
  induction k with
  | zero => simp [negInvBinom]
  | succ k ih =>
    simp only [negInvBinom]
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
    positivity

private lemma negInvBinom_le_one_local {r : ℕ} (hr : 1 ≤ r) (k : ℕ) : negInvBinom r k ≤ 1 := by
  induction k with
  | zero => simp [negInvBinom]
  | succ k ih =>
    simp only [negInvBinom]
    have hpos : 0 < negInvBinom r k := negInvBinom_pos_local hr k
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hinv : (1 : ℝ) / (r : ℝ) ≤ 1 := div_le_one_of_le₀ hr1 (by positivity)
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_one hk1]
    have hnum : (k : ℝ) + 1 / (r : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
    calc negInvBinom r k * ((k : ℝ) + 1 / (r : ℝ))
        ≤ 1 * ((k + 1 : ℕ) : ℝ) := mul_le_mul ih hnum (by positivity) (by norm_num)
      _ = ((k + 1 : ℕ) : ℝ) := one_mul _

private lemma binomPS_pow_eq_one_local {r : ℕ} (hr : 1 ≤ r) (c : ℝ) :
    ((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) * (binomPS r c) ^ r = 1 := by
  have hdiff : ((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) *
      PowerSeries.derivative ℝ (binomPS r c) =
      PowerSeries.C (c / (r : ℝ)) * binomPS r c := by
    ext k
    rw [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X, sub_mul, one_mul, map_sub, PowerSeries.coeff_derivative,
      PowerSeries.coeff_C_mul]
    have hX : PowerSeries.coeff k (PowerSeries.C c * PowerSeries.X * PowerSeries.derivative ℝ (binomPS r c)) =
        c * (k : ℝ) * negInvBinom r k * c ^ k := by
      cases k with
      | zero =>
        rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul]
        simp
      | succ k =>
        rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative]
        simp only [binomPS, PowerSeries.coeff_mk]
        push_cast; ring
    rw [hX]
    simp only [binomPS, PowerSeries.coeff_mk, negInvBinom]
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp [hk1]
    ring
  have hderiv0 : PowerSeries.derivative ℝ
      (((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) * (binomPS r c) ^ r) = 0 := by
    rw [Derivation.leibniz, PowerSeries.derivative_pow]
    have hd1 : PowerSeries.derivative ℝ ((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) =
        -PowerSeries.C c := by
      rw [PowerSeries.derivative_coe]
      simp [Polynomial.derivative_C_mul_X]
    rw [hd1]
    have hr_cast : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpow_r : (binomPS r c) ^ r = (binomPS r c) ^ (r - 1) * binomPS r c := by
      rw [← pow_succ, Nat.sub_add_cancel hr]
    simp only [smul_eq_mul]
    calc ((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) *
            ((r : PowerSeries ℝ) * (binomPS r c) ^ (r - 1) * PowerSeries.derivative ℝ (binomPS r c)) +
            (binomPS r c) ^ r * (-PowerSeries.C c)
        = (r : PowerSeries ℝ) * (binomPS r c) ^ (r - 1) *
            (((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) *
              PowerSeries.derivative ℝ (binomPS r c)) -
            PowerSeries.C c * (binomPS r c) ^ r := by ring
      _ = (r : PowerSeries ℝ) * (binomPS r c) ^ (r - 1) * (PowerSeries.C (c / (r : ℝ)) * binomPS r c) -
            PowerSeries.C c * (binomPS r c) ^ r := by rw [hdiff]
      _ = (PowerSeries.C (r : ℝ) * PowerSeries.C (c / (r : ℝ))) * ((binomPS r c) ^ (r - 1) * binomPS r c) -
            PowerSeries.C c * (binomPS r c) ^ r := by
          rw [show (r : PowerSeries ℝ) = PowerSeries.C (r : ℝ) by simp]
          ring
      _ = 0 := by
          rw [← map_mul, mul_div_cancel₀ _ hr_cast, ← hpow_r, sub_self]
  refine PowerSeries.derivative.ext (R := ℝ) (by rw [hderiv0, PowerSeries.derivative_one]) ?_
  rw [map_mul, map_pow, PowerSeries.constantCoeff_one]
  have hc1 : PowerSeries.constantCoeff ((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) = 1 := by
    rw [Polynomial.constantCoeff_coe]; simp
  have hc2 : PowerSeries.constantCoeff (binomPS r c) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, binomPS, PowerSeries.coeff_mk, pow_zero, mul_one]
    rfl
  rw [hc1, hc2, one_pow, mul_one]

private lemma EvalAt_binomPS {r : ℕ} (hr : 1 ≤ r) {c x : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x)
    (hcx : c * x < 1) :
    EvalAt (binomPS r c) x ((1 - c * x) ^ (-(1 : ℝ) / (r : ℝ))) := by
  have hterm_nonneg : ∀ k : ℕ, 0 ≤ PowerSeries.coeff k (binomPS r c) * x ^ k := by
    intro k
    simp only [binomPS, PowerSeries.coeff_mk]
    exact mul_nonneg (mul_nonneg (negInvBinom_pos_local hr k).le (pow_nonneg hc k)) (pow_nonneg hx k)
  have hterm_le : ∀ k : ℕ, ‖PowerSeries.coeff k (binomPS r c) * x ^ k‖ ≤ (c * x) ^ k := by
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (hterm_nonneg k)]
    simp only [binomPS, PowerSeries.coeff_mk, mul_pow]
    have hle := negInvBinom_le_one_local hr k
    calc negInvBinom r k * c ^ k * x ^ k
        = negInvBinom r k * (c ^ k * x ^ k) := by ring
      _ ≤ 1 * (c ^ k * x ^ k) := mul_le_mul_of_nonneg_right hle (mul_nonneg (pow_nonneg hc k) (pow_nonneg hx k))
      _ = c ^ k * x ^ k := one_mul _
  have hsum : Summable (fun k => ‖PowerSeries.coeff k (binomPS r c) * x ^ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le
      (summable_geometric_of_lt_one (mul_nonneg hc hx) hcx)
  set s := ∑' k, PowerSeries.coeff k (binomPS r c) * x ^ k
  have hs_eval : EvalAt (binomPS r c) x s := ⟨hsum, rfl⟩
  have hlin_eval : (1 - Polynomial.C c * Polynomial.X : Polynomial ℝ).eval x = 1 - c * x := by
    simp
  have hlin : EvalAt ((1 - Polynomial.C c * Polynomial.X : Polynomial ℝ) : PowerSeries ℝ) x (1 - c * x) :=
    hlin_eval ▸ EvalAt_poly (1 - Polynomial.C c * Polynomial.X) x
  have hprod : EvalAt (1 : PowerSeries ℝ) x ((1 - c * x) * s ^ r) := by
    rw [← binomPS_pow_eq_one_local hr c]
    exact EvalAt_mul hlin (EvalAt_pow hs_eval r)
  have heq1 : (1 - c * x) * s ^ r = 1 := hprod.unique (EvalAt_one x)
  have hs_nonneg : 0 ≤ s := tsum_nonneg hterm_nonneg
  have h1cx : 0 < 1 - c * x := by linarith
  have htarget_nonneg : 0 ≤ (1 - c * x) ^ (-(1 : ℝ) / (r : ℝ)) :=
    Real.rpow_nonneg h1cx.le _
  have hpow_eq : s ^ r = ((1 - c * x) ^ (-(1 : ℝ) / (r : ℝ))) ^ r := by
    have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [← Real.rpow_natCast ((1 - c * x) ^ (-(1 : ℝ) / (r : ℝ))) r, ← Real.rpow_mul h1cx.le]
    have hexp : -(1 : ℝ) / (r : ℝ) * (r : ℝ) = -1 := by field_simp [hr0]
    rw [hexp, Real.rpow_neg_one]
    have h1ne : (1 - c * x) ≠ 0 := h1cx.ne'
    calc s ^ r = ((1 - c * x) * s ^ r) * (1 - c * x)⁻¹ := by
          rw [mul_comm (1 - c * x), mul_assoc, mul_inv_cancel₀ h1ne, mul_one]
      _ = 1 * (1 - c * x)⁻¹ := by rw [heq1]
      _ = (1 - c * x)⁻¹ := one_mul _
  have hs_eq : s = (1 - c * x) ^ (-(1 : ℝ) / (r : ℝ)) :=
    (pow_left_inj₀ hs_nonneg htarget_nonneg (by omega : r ≠ 0)).mp hpow_eq
  exact hs_eq ▸ hs_eval

private lemma EvalAt_omegaPS {r M β : ℕ} (hr : 1 ≤ r) (hβM : β ≤ M)
    {x : ℝ} (hx : 0 ≤ x) (hxM : (M : ℝ) * x < 1) :
    EvalAt (omegaPS r β) x (omegaVal r β x) := by
  unfold omegaPS omegaVal
  refine EvalAt_finset_prod _ _ _ _ fun j hj => ?_
  have hj_lt : j < β := (Finset.mem_Ico.mp hj).2
  have hjx : (j : ℝ) * x < 1 :=
    (mul_le_mul_of_nonneg_right (by exact_mod_cast (show j ≤ M by omega)) hx).trans_lt hxM
  exact EvalAt_binomPS hr (Nat.cast_nonneg j) hx hjx

private lemma coeff_iterate_derivative_eq (f : PowerSeries ℝ) (k m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] f) =
      ((m + k).descFactorial k : ℝ) * PowerSeries.coeff (m + k) f := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', PowerSeries.coeff_derivative, ih (m + 1)]
    have h1 : m + 1 + k = m + (k + 1) := by omega
    rw [h1]
    have hdesc : (m + (k + 1)).descFactorial (k + 1) =
        (m + 1) * (m + (k + 1)).descFactorial k := by
      have := Nat.descFactorial_succ (m + (k + 1)) k
      have hsub : m + (k + 1) - k = m + 1 := by omega
      rw [hsub] at this
      exact this
    rw [hdesc, Nat.cast_mul]; push_cast; ring

private lemma P_ang_linearForm_bound {r M β₁ β₂ D N n k : ℕ}
    (hr : 1 ≤ r) (hM : 1 ≤ M) (hβ1 : 1 ≤ β₁) (hβ12 : β₁ < β₂) (hβ2 : β₂ ≤ M)
    (hMN : 8 * M ≤ N) (hNn : N ≤ n) (hn2N : n < 2 * N)
    (P : Fin 3 → Polynomial ℤ)
    (hR_eq : (((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) ^ k) *
        ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) =
      (k.factorial : ℝ) • ∑ i : Fin 3, (P_ang r M β₁ β₂ P k i : PowerSeries ℝ) * omega3PS r β₁ β₂ i)
    {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hvan : ∀ v ≤ (29 * D) / 12, PowerSeries.coeff v (R_ps r β₁ β₂ P) = 0)
    (hRbd : ∀ v, |PowerSeries.coeff v (R_ps r β₁ β₂ P)| ≤ C0 * (2 * (M : ℝ)) ^ v) :
    |∑ i : Fin 3, (P_ang r M β₁ β₂ P k i).eval (1 / (n : ℝ)) * omega3Val r β₁ β₂ (1 / (n : ℝ)) i| ≤
      2 * (2 * (r : ℝ) * (N : ℝ)) ^ k * C0 * (4 * (M : ℝ) / (N : ℝ)) ^ ((29 * D) / 12 + 1) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx0 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hxM : (M : ℝ) * (1 / (n : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one hn_pos]; exact_mod_cast (show M < n by omega)
  have h4Mn : 4 * (M : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hn_pos (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (show 4 * M * 2 ≤ 1 * n by omega)
  have hq0 : 0 ≤ 4 * (M : ℝ) / (n : ℝ) := by positivity
  have hq1 : 4 * (M : ℝ) / (n : ℝ) < 1 := by linarith
  set O := (29 * D) / 12
  set q := 4 * (M : ℝ) / (n : ℝ)
  have hterm_bd : ∀ m : ℕ,
      ‖PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m‖ ≤
        (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * (if O < m + k then q ^ (m + k) else 0) := by
    intro m
    rw [coeff_iterate_derivative_eq, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ ((m + k).descFactorial k : ℝ) from Nat.cast_nonneg _),
      abs_of_nonneg (pow_nonneg hx0 m)]
    by_cases hO : O < m + k
    · rw [if_pos hO]
      have hdesc : ((m + k).descFactorial k : ℝ) = (k.factorial : ℝ) * ((m + k).choose k : ℝ) := by
        exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose (m + k) k
      have hch : ((m + k).choose k : ℝ) ≤ (2 : ℝ) ^ (m + k) := by
        exact_mod_cast Nat.choose_le_two_pow (m + k) k
      have hpow_n : (1 / (n : ℝ)) ^ m = (n : ℝ) ^ k * (1 / (n : ℝ)) ^ (m + k) := by
        have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
        rw [pow_add, one_div, inv_pow, inv_pow]; field_simp [hn0]
      rw [hdesc, hpow_n]
      calc (k.factorial : ℝ) * ((m + k).choose k : ℝ) *
              |PowerSeries.coeff (m + k) (R_ps r β₁ β₂ P)| *
              ((n : ℝ) ^ k * (1 / (n : ℝ)) ^ (m + k))
          ≤ (k.factorial : ℝ) * (2 : ℝ) ^ (m + k) * (C0 * (2 * (M : ℝ)) ^ (m + k)) *
              ((n : ℝ) ^ k * (1 / (n : ℝ)) ^ (m + k)) := by
            have p1 := mul_le_mul_of_nonneg_left hch (Nat.cast_nonneg k.factorial)
            have p2 := mul_le_mul p1 (hRbd (m + k)) (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_right p2 (by positivity)
        _ = (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * q ^ (m + k) := by
            have hqpow : q ^ (m + k) = (2 : ℝ) ^ (m + k) * (2 * (M : ℝ)) ^ (m + k) * (1 / (n : ℝ)) ^ (m + k) := by
              dsimp only [q]
              rw [div_pow, one_div, inv_pow, ← mul_pow, show (2 : ℝ) * (2 * (M : ℝ)) = 4 * (M : ℝ) by ring]
              ring
            rw [hqpow]; ring
    · rw [if_neg hO, hvan (m + k) (by omega)]
      simp
  have hsum_q : Summable (fun v : ℕ => if O < v then q ^ v else 0) := by
    refine Summable.of_nonneg_of_le (fun v => by split_ifs <;> positivity)
      (fun v => by split_ifs <;> [exact le_rfl; positivity])
      (summable_geometric_of_lt_one hq0 hq1)
  have hsum_shift : Summable (fun m : ℕ => if O < m + k then q ^ (m + k) else 0) :=
    hsum_q.comp_injective (fun a b h => by omega)
  have hsum_deriv : Summable (fun m =>
      ‖PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_bd (hsum_shift.mul_left _)
  -- Evaluate both sides of hR_eq at 1/n:
  have hLHS_eval : EvalAt
      ((((Tpoly r M).map (Int.castRingHom ℝ) : PowerSeries ℝ) ^ k) *
        ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)))
      (1 / (n : ℝ))
      ((((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))) ^ k *
        ∑' m, PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m) :=
    EvalAt_mul (EvalAt_pow (EvalAt_poly _ _) k) ⟨hsum_deriv, rfl⟩
  have hRHS_eval : EvalAt
      ((k.factorial : ℝ) • ∑ i : Fin 3, (P_ang r M β₁ β₂ P k i : PowerSeries ℝ) * omega3PS r β₁ β₂ i)
      (1 / (n : ℝ))
      ((k.factorial : ℝ) * ∑ i : Fin 3, (P_ang r M β₁ β₂ P k i).eval (1 / (n : ℝ)) * omega3Val r β₁ β₂ (1 / (n : ℝ)) i) := by
    refine EvalAt_smul _ (EvalAt_finset_sum _ _ _ _ fun i _ => ?_)
    have hbi : beta3 β₁ β₂ i ≤ M := by fin_cases i <;> simp [beta3] <;> omega
    exact EvalAt_mul (EvalAt_poly _ _) (EvalAt_omegaPS hr hbi hx0 hxM)
  rw [hR_eq] at hLHS_eval
  have heval_eq :
      (k.factorial : ℝ) * ∑ i : Fin 3, (P_ang r M β₁ β₂ P k i).eval (1 / (n : ℝ)) * omega3Val r β₁ β₂ (1 / (n : ℝ)) i =
      (((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))) ^ k *
        ∑' m, PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m :=
    hRHS_eval.unique hLHS_eval
  -- Bound tsum of shifted indicator:
  have htsum_le : ∑' m, (if O < m + k then q ^ (m + k) else 0) ≤ 2 * q ^ (O + 1) := by
    have h1 : ∑' m, (if O < m + k then q ^ (m + k) else 0) ≤ ∑' v, (if O < v then q ^ v else 0) := by
      have hsplitk := hsum_q.sum_add_tsum_nat_add k
      have hfin_nn : 0 ≤ ∑ v ∈ Finset.range k, (if O < v then q ^ v else 0) :=
        Finset.sum_nonneg fun v _ => by split_ifs <;> positivity
      linarith
    have h2 : ∑' v, (if O < v then q ^ v else 0) = q ^ (O + 1) * ∑' t : ℕ, q ^ t := by
      have hsplit := hsum_q.sum_add_tsum_nat_add (O + 1)
      have hfin0 : ∑ v ∈ Finset.range (O + 1), (if O < v then q ^ v else 0) = 0 := by
        refine Finset.sum_eq_zero fun v hv => ?_
        have : ¬ O < v := by simp only [Finset.mem_range] at hv; omega
        simp [this]
      rw [hfin0, zero_add] at hsplit
      rw [← hsplit, ← tsum_mul_left]
      congr 1; ext t
      have hlt : O < t + (O + 1) := by omega
      rw [if_pos hlt, add_comm, pow_add]
    rw [h2, tsum_geometric_of_lt_one hq0 hq1] at h1
    have hden : (1 / 2 : ℝ) ≤ 1 - q := by linarith
    have hdiv : (1 - q)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith
    calc ∑' m, (if O < m + k then q ^ (m + k) else 0)
        ≤ q ^ (O + 1) * (1 - q)⁻¹ := h1
      _ ≤ q ^ (O + 1) * 2 := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = 2 * q ^ (O + 1) := mul_comm _ _
  have hderiv_abs : |∑' m, PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m| ≤
      2 * (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * q ^ (O + 1) := by
    calc |∑' m, PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m|
        ≤ ∑' m, ‖PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m‖ := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsum_deriv
      _ ≤ ∑' m, (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * (if O < m + k then q ^ (m + k) else 0) :=
          Summable.tsum_le_tsum hterm_bd hsum_deriv (hsum_shift.mul_left _)
      _ = (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * ∑' m, (if O < m + k then q ^ (m + k) else 0) :=
          tsum_mul_left
      _ ≤ (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * (2 * q ^ (O + 1)) :=
          mul_le_mul_of_nonneg_left htsum_le (by positivity)
      _ = 2 * (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * q ^ (O + 1) := by ring
  have hTeval : |((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))| ≤ (r : ℝ) := by
    unfold Tpoly
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, eq_intCast, Int.cast_natCast]
    have hprod_map : ∏ j ∈ Finset.Icc 1 M,
          (1 - Polynomial.C (j : ℤ) * Polynomial.X).map (Int.castRingHom ℝ) =
        ∏ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) :=
      Finset.prod_congr rfl fun j _ => by
        rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
        simp
    rw [hprod_map, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod, abs_mul, abs_prod,
      abs_of_nonneg (Nat.cast_nonneg r)]
    have hpr : ∏ j ∈ Finset.Icc 1 M, |(1 - Polynomial.C (j : ℝ) * Polynomial.X).eval (1 / (n : ℝ))| ≤ 1 := by
      refine Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j hj => ?_)
      simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
      have hjn : (j : ℝ) * (1 / (n : ℝ)) ≤ 1 :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hjM) hx0).trans hxM.le
      rw [abs_of_nonneg (by linarith)]
      linarith [mul_nonneg (Nat.cast_nonneg j) hx0]
    calc (r : ℝ) * ∏ j ∈ Finset.Icc 1 M, |(1 - Polynomial.C (j : ℝ) * Polynomial.X).eval (1 / (n : ℝ))|
        ≤ (r : ℝ) * 1 := mul_le_mul_of_nonneg_left hpr (Nat.cast_nonneg r)
      _ = (r : ℝ) := mul_one _
  have hfac_pos : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have habs_eq := congrArg abs heval_eq
  rw [abs_mul, abs_of_pos hfac_pos, abs_mul, abs_pow] at habs_eq
  have hbound_k : (k.factorial : ℝ) *
      |∑ i : Fin 3, (P_ang r M β₁ β₂ P k i).eval (1 / (n : ℝ)) * omega3Val r β₁ β₂ (1 / (n : ℝ)) i| ≤
      (k.factorial : ℝ) * (2 * (2 * (r : ℝ) * (N : ℝ)) ^ k * C0 * (4 * (M : ℝ) / (N : ℝ)) ^ (O + 1)) := by
    have hqN : q ≤ 4 * (M : ℝ) / (N : ℝ) := by
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      exact div_le_div_of_nonneg_left (by positivity) hN_pos (by exact_mod_cast hNn)
    have hnN : (r : ℝ) ^ k * (n : ℝ) ^ k ≤ (2 * (r : ℝ) * (N : ℝ)) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (show n ≤ 2 * N by omega)
      nlinarith [Nat.cast_nonneg (α := ℝ) r]
    calc (k.factorial : ℝ) * |∑ i : Fin 3, _|
        = |((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ))| ^ k *
            |∑' m, PowerSeries.coeff m ((PowerSeries.derivative ℝ)^[k] (R_ps r β₁ β₂ P)) * (1 / (n : ℝ)) ^ m| := habs_eq
      _ ≤ (r : ℝ) ^ k * (2 * (k.factorial : ℝ) * (n : ℝ) ^ k * C0 * q ^ (O + 1)) :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hTeval k) hderiv_abs (abs_nonneg _) (by positivity)
      _ = (k.factorial : ℝ) * (2 * ((r : ℝ) ^ k * (n : ℝ) ^ k) * C0 * q ^ (O + 1)) := by ring
      _ ≤ (k.factorial : ℝ) * (2 * (2 * (r : ℝ) * (N : ℝ)) ^ k * C0 * (4 * (M : ℝ) / (N : ℝ)) ^ (O + 1)) := by
          have p1 : (r : ℝ) ^ k * (n : ℝ) ^ k * q ^ (O + 1) ≤
              (2 * (r : ℝ) * (N : ℝ)) ^ k * (4 * (M : ℝ) / (N : ℝ)) ^ (O + 1) :=
            mul_le_mul hnN (pow_le_pow_left₀ hq0 hqN _) (by positivity) (by positivity)
          have : 2 * ((r : ℝ) ^ k * (n : ℝ) ^ k) * C0 * q ^ (O + 1) =
              2 * C0 * ((r : ℝ) ^ k * (n : ℝ) ^ k * q ^ (O + 1)) := by ring
          have : 2 * (2 * (r : ℝ) * (N : ℝ)) ^ k * C0 * (4 * (M : ℝ) / (N : ℝ)) ^ (O + 1) =
              2 * C0 * ((2 * (r : ℝ) * (N : ℝ)) ^ k * (4 * (M : ℝ) / (N : ℝ)) ^ (O + 1)) := by ring
          nlinarith [mul_le_mul_of_nonneg_left p1 (show 0 ≤ 2 * C0 by linarith)]
  exact le_of_mul_le_mul_left hbound_k hfac_pos

/- #### Part 3C: Elementary helpers (factorial bounds, root multiplicity sum, simultaneous approx) -/

private lemma factorial_le_pow (n : ℕ) : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
  have hnat : n.factorial ≤ n ^ n := by
    rw [← Finset.prod_Ico_id_eq_factorial]
    calc ∏ i ∈ Finset.Ico 1 (n + 1), i
        ≤ ∏ _i ∈ Finset.Ico 1 (n + 1), n :=
          Finset.prod_le_prod' fun i hi => by have := (Finset.mem_Ico.mp hi).2; omega
      _ = n ^ n := by simp
  exact_mod_cast hnat

private lemma pow_half_le_factorial (n : ℕ) : ((n / 2 : ℕ) : ℝ) ^ (n / 2) ≤ (n.factorial : ℝ) := by
  have hnat : (n / 2) ^ (n / 2) ≤ n.factorial := by
    set h := n / 2
    rw [← Finset.prod_Ico_id_eq_factorial]
    have hsub : Finset.Ico (n + 1 - h) (n + 1) ⊆ Finset.Ico 1 (n + 1) := by
      intro i hi
      simp only [Finset.mem_Ico] at hi ⊢
      omega
    calc h ^ h
        = ∏ _i ∈ Finset.Ico (n + 1 - h) (n + 1), h := by
          rw [Finset.prod_const, Nat.card_Ico]; congr 1; omega
      _ ≤ ∏ i ∈ Finset.Ico (n + 1 - h) (n + 1), i :=
          Finset.prod_le_prod' fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega
      _ ≤ ∏ i ∈ Finset.Ico 1 (n + 1), i :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub fun i hi _ => (Finset.mem_Ico.mp hi).1
  exact_mod_cast hnat

private lemma sum_rootMultiplicity_le_natDegree {p : Polynomial ℝ} (hp : p ≠ 0)
    (s : Finset ℕ) (f : ℕ → ℝ) (hinj : Set.InjOn f ↑s) :
    ∑ n ∈ s, p.rootMultiplicity (f n) ≤ p.natDegree := by
  have hcnt : ∀ n ∈ s, p.rootMultiplicity (f n) = p.roots.count (f n) :=
    fun n _ => (Polynomial.count_roots p).symm
  rw [Finset.sum_congr rfl hcnt, ← Finset.sum_image (f := fun a => p.roots.count a) hinj]
  have hle_card : ∀ (t : Finset ℝ) (m : Multiset ℝ), ∑ a ∈ t, m.count a ≤ m.card := by
    intro t m
    classical
    induction t using Finset.induction_on generalizing m with
    | empty => simp
    | insert a t hat ih =>
      rw [Finset.sum_insert hat]
      have h1 : ∑ x ∈ t, m.count x = ∑ x ∈ t, (m.filter (· ≠ a)).count x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxa : x ≠ a := fun h => hat (h ▸ hx)
        exact (Multiset.count_filter_of_pos (p := fun y => y ≠ a) hxa).symm
      rw [h1]
      have h2 := ih (m.filter (· ≠ a))
      have h3 : m.count a + (m.filter (· ≠ a)).card = m.card := by
        have hf := congrArg Multiset.card (Multiset.filter_add_not (fun y => a = y) m)
        rw [Multiset.card_add, ← Multiset.count_eq_card_filter_eq] at hf
        have hfeq : m.filter (fun y => ¬ a = y) = m.filter (· ≠ a) := by
          congr 1; ext y; exact ne_comm
        rwa [hfeq] at hf
      omega
  exact (hle_card _ _).trans (Polynomial.card_roots' p)

private lemma incompatible {Y D w z : ℝ} (hY : 0 < Y) (hD : 0 < D)
    {x : ℕ} (hx : 0 < x) (hxy : (x : ℝ) ≤ 2 * Y) {p q : ℤ}
    (hp : |(x : ℝ) * w - (p : ℝ)| ≤ 1 / D) (hq : |(x : ℝ) * z - (q : ℝ)| ≤ 1 / D)
    (A : Matrix (Fin 3) (Fin 3) ℤ) (hdet : A.det ≠ 0)
    (hs : ∀ i j, |(A i j : ℝ)| ≤ D / 8)
    (he : ∀ i, |(A i 0 : ℝ) + (A i 1 : ℝ) * w + (A i 2 : ℝ) * z| ≤ 1 / (8 * Y)) : False := by
  let v : Fin 3 → ℤ := ![(x : ℤ), p, q]
  have hAv : A.mulVec v = 0 := by
    funext i
    have h1 : |(x : ℝ) * ((A i 0 : ℝ) + (A i 1 : ℝ) * w + (A i 2 : ℝ) * z)| ≤ 1 / 4 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg x)]
      calc (x : ℝ) * |(A i 0 : ℝ) + (A i 1 : ℝ) * w + (A i 2 : ℝ) * z|
          ≤ (2 * Y) * (1 / (8 * Y)) := mul_le_mul hxy (he i) (abs_nonneg _) (by positivity)
        _ = 1 / 4 := by
            have hYne : Y ≠ 0 := hY.ne'
            field_simp [hYne]; norm_num
    have h2 : |(A i 1 : ℝ) * ((x : ℝ) * w - (p : ℝ))| ≤ 1 / 8 := by
      rw [abs_mul]
      calc |(A i 1 : ℝ)| * |(x : ℝ) * w - (p : ℝ)|
          ≤ (D / 8) * (1 / D) := mul_le_mul (hs i 1) hp (abs_nonneg _) (by positivity)
        _ = 1 / 8 := by field_simp [hD.ne']
    have h3 : |(A i 2 : ℝ) * ((x : ℝ) * z - (q : ℝ))| ≤ 1 / 8 := by
      rw [abs_mul]
      calc |(A i 2 : ℝ)| * |(x : ℝ) * z - (q : ℝ)|
          ≤ (D / 8) * (1 / D) := mul_le_mul (hs i 2) hq (abs_nonneg _) (by positivity)
        _ = 1 / 8 := by field_simp [hD.ne']
    have hval : ((A.mulVec v i : ℤ) : ℝ) =
        (x : ℝ) * ((A i 0 : ℝ) + (A i 1 : ℝ) * w + (A i 2 : ℝ) * z) -
        (A i 1 : ℝ) * ((x : ℝ) * w - (p : ℝ)) -
        (A i 2 : ℝ) * ((x : ℝ) * z - (q : ℝ)) := by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, v, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      push_cast; ring
    have hlt1 : |((A.mulVec v i : ℤ) : ℝ)| < 1 := by
      rw [hval]
      have t1 := abs_sub ((x : ℝ) * ((A i 0 : ℝ) + (A i 1 : ℝ) * w + (A i 2 : ℝ) * z) -
        (A i 1 : ℝ) * ((x : ℝ) * w - (p : ℝ))) ((A i 2 : ℝ) * ((x : ℝ) * z - (q : ℝ)))
      have t2 := abs_sub ((x : ℝ) * ((A i 0 : ℝ) + (A i 1 : ℝ) * w + (A i 2 : ℝ) * z))
        ((A i 1 : ℝ) * ((x : ℝ) * w - (p : ℝ)))
      linarith
    have hint : |A.mulVec v i| < 1 := by exact_mod_cast hlt1
    obtain ⟨hl, hr⟩ := abs_lt.mp hint
    simp only [Pi.zero_apply]
    omega
  have hmul := congrArg (A.adjugate.mulVec) hAv
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_zero,
    Matrix.smul_mulVec, Matrix.one_mulVec] at hmul
  have h0 := congrFun hmul 0
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v, Matrix.cons_val_zero] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact hdet h
  · omega

/- #### Part 3D: Simultaneous rational approximation (BPZ Lemma 3.3 without complex roots!) -/

private lemma centered_poly_diff_bound (T : Finset ℕ) (hT : 2 ≤ T.card) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, 1 ≤ y →
      |(∏ i ∈ T, (y + ((T.card : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ)))) - y ^ T.card| ≤
        K * y ^ (T.card - 2) := by
  let c : ℕ → ℝ := fun i => (T.card : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ)
  let P : Polynomial ℝ := ∏ i ∈ T, (Polynomial.X + Polynomial.C (c i))
  have hsum_c : ∑ i ∈ T, c i = 0 := by
    simp only [c, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hmonic : P.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _
  have hdeg : P.natDegree = T.card := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
    simp [Polynomial.natDegree_X_add_C]
  -- Prove coeff (T.card - 1) P = ∑ i ∈ T, c i = 0 by induction on finite sets!
  have hnext_coeff : ∀ (s : Finset ℕ), 1 ≤ s.card →
      (∏ i ∈ s, (Polynomial.X + Polynomial.C (c i))).coeff (s.card - 1) = ∑ i ∈ s, c i := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => intro h; simp at h
    | insert a s ha ih =>
      intro _
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
      simp only [Nat.add_sub_cancel]
      set Q := ∏ i ∈ s, (Polynomial.X + Polynomial.C (c i))
      have hQdeg : Q.natDegree = s.card := by
        rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
        simp [Polynomial.natDegree_X_add_C]
      have hQmon : Q.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _
      have hQlead : Q.coeff s.card = 1 := by rw [← hQdeg]; exact hQmon.leadingCoeff
      rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul, hQlead, mul_one]
      cases hs : s.card with
      | zero =>
        have hse : s = ∅ := Finset.card_eq_zero.mp hs
        subst hse
        simp [Q]
      | succ k =>
        have hih := ih (by omega)
        rw [hs, Nat.add_sub_cancel] at hih
        rw [Polynomial.coeff_X_mul]
        change Q.coeff k + c a = c a + ∑ i ∈ s, c i
        rw [hih, add_comm]
  let R : Polynomial ℝ := P - Polynomial.X ^ T.card
  have hRdeg : R.natDegree ≤ T.card - 2 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun k hk => ?_
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    by_cases hk1 : k = T.card
    · subst hk1
      rw [if_pos rfl, ← hdeg, ← Polynomial.leadingCoeff, hmonic.leadingCoeff, sub_self]
    · by_cases hk2 : k = T.card - 1
      · subst hk2
        rw [if_neg (by omega), hnext_coeff T (by omega), hsum_c, sub_zero]
      · have hgt : P.natDegree < k := by omega
        rw [if_neg hk1, Polynomial.coeff_eq_zero_of_natDegree_lt hgt, sub_zero]
  refine ⟨∑ k ∈ Finset.range (T.card - 2 + 1), |R.coeff k|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun y hy => ?_⟩
  have hev : (∏ i ∈ T, (y + c i)) - y ^ T.card = R.eval y := by
    simp [R, P, Polynomial.eval_prod]
  rw [hev, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hRdeg)]
  calc |∑ k ∈ Finset.range (T.card - 2 + 1), R.coeff k * y ^ k|
      ≤ ∑ k ∈ Finset.range (T.card - 2 + 1), |R.coeff k * y ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (T.card - 2 + 1), |R.coeff k| * y ^ (T.card - 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkle : k ≤ T.card - 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hy0 : 0 ≤ y := by linarith
        rw [abs_mul, abs_of_nonneg (pow_nonneg hy0 k)]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hy hkle) (abs_nonneg _)
    _ = (∑ k ∈ Finset.range (T.card - 2 + 1), |R.coeff k|) * y ^ (T.card - 2) := by
        rw [Finset.sum_mul]

set_option maxHeartbeats 800000 in
private lemma simul_approx_of_sol (T : Finset ℕ) (hT : 2 ≤ T.card) (η : ℝ) (hη : 0 < η) :
    let r := T.card
    let Y := fun n : ℕ => (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))
    let sol := fun n y : ℕ =>
      (r : ℤ) ^ r * (n.factorial : ℤ) = ∏ i ∈ T, ((y : ℤ) + (r : ℤ) * (i : ℤ) - ∑ j ∈ T, (j : ℤ))
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.Ico N (2 * N), ∀ y : ℕ, sol n y →
      0 < y ∧ (y : ℝ) ≤ 2 * Y n ∧
      ∀ b : ℕ, 0 < b → b ≤ n → b ≤ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ → r ∣ b →
        (∃ z : ℕ, sol (n - b) z) →
        ∃ p : ℤ, |(y : ℝ) * omegaVal r b (1 / (n : ℝ)) - (p : ℝ)| ≤ 1 / (Y n) ^ (1 - η) := by
  intro r Y sol
  obtain ⟨K, hK0, hK⟩ := centered_poly_diff_bound T hT
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hY_tendsto : Tendsto Y atTop atTop := by
    have hpow_t : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) ^ (n / 2)) atTop atTop := by
      refine tendsto_atTop_mono' atTop (f₁ := fun n : ℕ => ((n / 2 : ℕ) : ℝ)) ?_ ?_
      · filter_upwards [eventually_ge_atTop 2] with n hn
        have h1 : 1 ≤ n / 2 := by omega
        calc ((n / 2 : ℕ) : ℝ) = ((n / 2 : ℕ) : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ ((n / 2 : ℕ) : ℝ) ^ (n / 2) := pow_le_pow_right₀ (by exact_mod_cast h1) h1
      · refine tendsto_atTop_atTop.mpr fun B => ⟨2 * (Nat.ceil B + 1), fun n hn => ?_⟩
        have : Nat.ceil B ≤ n / 2 := by omega
        exact (Nat.le_ceil B).trans (by exact_mod_cast this)
    have hfac_t : Tendsto (fun n : ℕ => (n.factorial : ℝ)) atTop atTop :=
      tendsto_atTop_mono pow_half_le_factorial hpow_t
    have hrpow_t : Tendsto (fun n : ℕ => (n.factorial : ℝ) ^ (1 / (r : ℝ))) atTop atTop :=
      (tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (r : ℝ))).comp hfac_t
    exact Tendsto.const_mul_atTop hr_pos hrpow_t
  -- Show (2 * K * 2^(3*r) + 16) * (2 * N)^(2 * M) ≤ (Y N)^η eventually via log comparison
  let Kbig : ℝ := 2 * K * (2 : ℝ) ^ (3 * r) + 16
  have hKbig_pos : 0 < Kbig := by dsimp [Kbig]; positivity
  have hsmall_err : ∀ᶠ N : ℕ in atTop,
      Kbig * (2 * (N : ℝ)) ^ (2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊) ≤ (Y N) ^ η := by
    have hpow_van : Tendsto (fun N : ℕ =>
        (Real.log Kbig + 200 * (N : ℝ) ^ (1 / 17 : ℝ)) / (N : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => Real.log Kbig / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have h2 : Tendsto (fun N : ℕ => 200 * (N : ℝ) ^ (-(16 / 17 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 16 / 17)).comp
          tendsto_natCast_atTop_atTop |>.const_mul 200
      have hsum : Tendsto (fun N : ℕ =>
          Real.log Kbig / (N : ℝ) + 200 * (N : ℝ) ^ (-(16 / 17 : ℝ))) atTop (𝓝 0) := by
        simpa using h1.add h2
      refine hsum.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      rw [add_div, mul_div_assoc]
      congr 2
      rw [eq_div_iff hNpos.ne', ← Real.rpow_add_one hNpos.ne']
      congr 1; norm_num
    have hlt_ev : ∀ᶠ N : ℕ in atTop,
        (Real.log Kbig + 200 * (N : ℝ) ^ (1 / 17 : ℝ)) / (N : ℝ) < η / (4 * (r : ℝ)) :=
      hpow_van.eventually (gt_mem_nhds (by positivity))
    filter_upwards [eventually_ge_atTop 10, hlt_ev] with N hN hlt
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h2N_pos : (0 : ℝ) < 2 * (N : ℝ) := by positivity
    have hYN_pos : 0 < Y N := by dsimp [Y]; positivity
    rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hYN_pos _)]
    rw [Real.log_mul hKbig_pos.ne' (by positivity), Real.log_pow, Real.log_rpow hYN_pos]
    have hM_le : (⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ) :=
      Nat.floor_le (by positivity)
    have hlog2N : Real.log (2 * (N : ℝ)) ≤ 34 * (2 * (N : ℝ)) ^ (1 / 34 : ℝ) := by
      have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
        (by norm_num : (0 : ℝ) < 1 / 34)
      linarith
    have h2pow : (2 : ℝ) ^ (1 / 34 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 34 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hMlog : ((2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ : ℕ) : ℝ) * Real.log (2 * (N : ℝ)) ≤
        200 * (N : ℝ) ^ (1 / 17 : ℝ) := by
      push_cast
      have hlog0 : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
        linarith)
      have h1 : 2 * (⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ : ℝ) * Real.log (2 * (N : ℝ)) ≤
          2 * (N : ℝ) ^ (1 / 34 : ℝ) * (34 * (2 * (N : ℝ)) ^ (1 / 34 : ℝ)) := by
        have p1 := mul_le_mul_of_nonneg_left hM_le (by norm_num : (0 : ℝ) ≤ 2)
        exact mul_le_mul p1 hlog2N hlog0 (by positivity)
      rw [Real.mul_rpow (by norm_num) hN_pos.le] at h1
      have hsq : (N : ℝ) ^ (1 / 34 : ℝ) * (N : ℝ) ^ (1 / 34 : ℝ) = (N : ℝ) ^ (1 / 17 : ℝ) := by
        rw [← Real.rpow_add hN_pos]; norm_num
      calc 2 * (⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ : ℝ) * Real.log (2 * (N : ℝ))
          ≤ 68 * (2 : ℝ) ^ (1 / 34 : ℝ) * ((N : ℝ) ^ (1 / 34 : ℝ) * (N : ℝ) ^ (1 / 34 : ℝ)) := by linarith
        _ = 68 * (2 : ℝ) ^ (1 / 34 : ℝ) * (N : ℝ) ^ (1 / 17 : ℝ) := by rw [hsq]
        _ ≤ 68 * 2 * (N : ℝ) ^ (1 / 17 : ℝ) := by
            have := mul_le_mul_of_nonneg_left h2pow (by norm_num : (0 : ℝ) ≤ 68)
            exact mul_le_mul_of_nonneg_right this (by positivity)
        _ ≤ 200 * (N : ℝ) ^ (1 / 17 : ℝ) := by
            have : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 17 : ℝ) := by positivity
            linarith
    have hlogYN : (N : ℝ) / (4 * (r : ℝ)) ≤ Real.log (Y N) := by
      have hN2 : (3 : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ N / 2 by omega)
      have hlog3 : (1 : ℝ) ≤ Real.log ((N / 2 : ℕ) : ℝ) := by
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log ((N / 2 : ℕ) : ℝ) := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      have hfac := pow_half_le_factorial N
      have h1 : (((N / 2 : ℕ) : ℝ) ^ (N / 2)) ^ (1 / (r : ℝ)) ≤ Y N := by
        have hY1 : (N.factorial : ℝ) ^ (1 / (r : ℝ)) ≤ Y N := by
          dsimp [Y]
          have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
          calc (N.factorial : ℝ) ^ (1 / (r : ℝ))
              = 1 * (N.factorial : ℝ) ^ (1 / (r : ℝ)) := (one_mul _).symm
            _ ≤ (r : ℝ) * (N.factorial : ℝ) ^ (1 / (r : ℝ)) :=
                mul_le_mul_of_nonneg_right hr1 (by positivity)
        exact (Real.rpow_le_rpow (by positivity) hfac (by positivity)).trans hY1
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_rpow (by positivity), Real.log_pow] at h2
      have hN4 : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) := by
        have : N ≤ 4 * (N / 2) := by omega
        have hR : (N : ℝ) ≤ 4 * ((N / 2 : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      have hstep : (N : ℝ) / 4 ≤ ((N / 2 : ℕ) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_left hlog3 (show 0 ≤ ((N / 2 : ℕ) : ℝ) by positivity)]
      have hstep2 : (1 / (r : ℝ)) * ((N : ℝ) / 4) ≤
          (1 / (r : ℝ)) * (((N / 2 : ℕ) : ℝ) * Real.log ((N / 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      have hring : (N : ℝ) / (4 * (r : ℝ)) = (1 / (r : ℝ)) * ((N : ℝ) / 4) := by ring
      linarith
    have hlt' : Real.log Kbig + 200 * (N : ℝ) ^ (1 / 17 : ℝ) ≤ η * ((N : ℝ) / (4 * (r : ℝ))) := by
      have h := (div_lt_iff₀ hN_pos).mp hlt
      have : η / (4 * (r : ℝ)) * (N : ℝ) = η * ((N : ℝ) / (4 * (r : ℝ))) := by ring
      linarith
    have hmul_eta := mul_le_mul_of_nonneg_left hlogYN hη.le
    linarith
  let B0 : ℝ := max (4 * K + 4) (|∏ i ∈ T, ((r : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ))| + 2)
  have hY_half_large : ∀ᶠ N : ℕ in atTop, B0 ≤ Y (N / 2) := by
    have hhalf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun n hn => by omega⟩
    exact (hY_tendsto.comp hhalf).eventually (eventually_ge_atTop B0)
  have hN_ge_M : ∀ᶠ N : ℕ in atTop, 2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ + 2 ≤ N := by
    have hlim : Tendsto (fun N : ℕ => (2 * (N : ℝ) ^ (1 / 34 : ℝ) + 2) / (N : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => 2 * (N : ℝ) ^ (-(33 / 34 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 33 / 34)).comp
          tendsto_natCast_atTop_atTop |>.const_mul 2
      have h2 : Tendsto (fun N : ℕ => (2 : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hadd : Tendsto (fun N : ℕ => 2 * (N : ℝ) ^ (-(33 / 34 : ℝ)) + (2 : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
        simpa using h1.add h2
      refine hadd.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      rw [add_div, mul_div_assoc]; congr 2
      rw [eq_div_iff hNpos.ne', ← Real.rpow_add_one hNpos.ne']; congr 1; norm_num
    filter_upwards [eventually_ge_atTop 10, hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hN hlt
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have h1 := (div_lt_iff₀ hNpos).mp hlt
    have hM_le : (⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ) := Nat.floor_le (by positivity)
    have hR : (2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ + 2 : ℝ) < (N : ℝ) := by linarith
    have hnat : 2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ + 2 < N := by exact_mod_cast hR
    omega
  filter_upwards [eventually_ge_atTop 10, hsmall_err, hY_half_large, hN_ge_M] with N hN10 herr hYlg hNM
  intro n hn y hy
  obtain ⟨hNn, hn2N⟩ := Finset.mem_Ico.mp hn
  have hY_mono : ∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → Y m₁ ≤ Y m₂ := by
    intro m₁ m₂ hm
    dsimp [Y]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hm) (by positivity))
      hr_pos.le
  have hsol_real : ∀ m z : ℕ, sol m z →
      (Y m) ^ r = ∏ i ∈ T, ((z : ℝ) + ((r : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ))) := by
    intro m z hz
    have hZ : ((r : ℝ) ^ r * (m.factorial : ℝ)) =
        ∏ i ∈ T, ((z : ℝ) + ((r : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ))) := by
      have hcast := congrArg (Int.cast (R := ℝ)) hz
      simp only [Int.cast_prod, Int.cast_sum, Int.cast_pow, Int.cast_mul, Int.cast_add,
        Int.cast_sub, Int.cast_natCast] at hcast
      rw [hcast]
      exact Finset.prod_congr rfl fun _ _ => by ring
    rw [← hZ]
    dsimp [Y]
    rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
      one_div_mul_cancel hr_pos.ne', Real.rpow_one]
  -- Helper: any solution z for m ≥ N/2 satisfies 0 < z, Y m / 2 ≤ z ≤ 2 * Y m, and |(Y m)^r - z^r| ≤ K * z^(r-2)
  have hsol_props : ∀ m z : ℕ, N / 2 ≤ m → sol m z →
      0 < z ∧ Y m / 2 ≤ (z : ℝ) ∧ (z : ℝ) ≤ 2 * Y m ∧ |(Y m) ^ r - (z : ℝ) ^ r| ≤ K * (z : ℝ) ^ (r - 2) := by
    intro m z hm hz
    have hYm_B0 : B0 ≤ Y m := hYlg.trans (hY_mono (N / 2) m hm)
    have hYm_K : 4 * K + 4 ≤ Y m := (le_max_left _ _).trans hYm_B0
    have hYm_0 : |∏ i ∈ T, ((r : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ))| + 2 ≤ Y m := (le_max_right _ _).trans hYm_B0
    have hYm_pos : 0 < Y m := by linarith
    have hz_pos : 0 < z := by
      by_contra hz0
      have hzeq : z = 0 := by omega
      subst hzeq
      have h := hsol_real m 0 hz
      simp only [Nat.cast_zero, zero_add] at h
      have hpow_ge : Y m ≤ (Y m) ^ r := by
        calc Y m = (Y m) ^ 1 := (pow_one _).symm
          _ ≤ (Y m) ^ r := pow_le_pow_right₀ (by linarith) (by omega)
      have habs := le_abs_self (∏ i ∈ T, ((r : ℝ) * (i : ℝ) - ∑ j ∈ T, (j : ℝ)))
      linarith
    have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_pos
    have hdiff : |(Y m) ^ r - (z : ℝ) ^ r| ≤ K * (z : ℝ) ^ (r - 2) := by
      rw [hsol_real m z hz]; exact hK (z : ℝ) hz1
    have hz_le : (z : ℝ) ≤ 2 * Y m := by
      by_contra hgt; push_neg at hgt
      have h2r : (4 : ℝ) ≤ (2 : ℝ) ^ r := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hT
      have hY_pow : (Y m) ^ r ≤ (z : ℝ) ^ r / 4 := by
        have h1 : (2 * Y m) ^ r ≤ (z : ℝ) ^ r := pow_le_pow_left₀ (by positivity) hgt.le r
        rw [mul_pow] at h1
        have h2 : 4 * (Y m) ^ r ≤ (2 : ℝ) ^ r * (Y m) ^ r :=
          mul_le_mul_of_nonneg_right h2r (by positivity)
        linarith
      have hKz : K * (z : ℝ) ^ (r - 2) ≤ (z : ℝ) ^ r / 2 := by
        have hz_sq : (z : ℝ) ^ r = (z : ℝ) ^ 2 * (z : ℝ) ^ (r - 2) := by
          rw [← pow_add, show 2 + (r - 2) = r by omega]
        rw [hz_sq]
        have hK_sq : K ≤ (z : ℝ) ^ 2 / 2 := by nlinarith
        have := mul_le_mul_of_nonneg_right hK_sq (show 0 ≤ (z : ℝ) ^ (r - 2) by positivity)
        linarith
      have habs_low : (z : ℝ) ^ r - (Y m) ^ r ≤ |(Y m) ^ r - (z : ℝ) ^ r| := by
        rw [abs_sub_comm]; exact le_abs_self _
      have hzpow_pos : 0 < (z : ℝ) ^ r := by positivity
      linarith
    have hz_ge : Y m / 2 ≤ (z : ℝ) := by
      by_contra hlt; push_neg at hlt
      have h2r : (4 : ℝ) ≤ (2 : ℝ) ^ r := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hT
      have hz_pow : (z : ℝ) ^ r ≤ (Y m) ^ r / 4 := by
        have h1 : (z : ℝ) ^ r ≤ (Y m / 2) ^ r := pow_le_pow_left₀ (by positivity) hlt.le r
        rw [div_pow] at h1
        have h2 : (Y m) ^ r / (2 : ℝ) ^ r ≤ (Y m) ^ r / 4 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) h2r
        exact h1.trans h2
      have hKz : K * (z : ℝ) ^ (r - 2) ≤ (Y m) ^ r / 4 := by
        have hY_sq : (Y m) ^ r = (Y m) ^ 2 * (Y m) ^ (r - 2) := by
          rw [← pow_add, show 2 + (r - 2) = r by omega]
        rw [hY_sq]
        have hK_sq : K ≤ (Y m) ^ 2 / 4 := by nlinarith
        have hzY : (z : ℝ) ^ (r - 2) ≤ (Y m) ^ (r - 2) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
        have h1 := mul_le_mul hK_sq hzY (by positivity) (by positivity)
        linarith
      have habs_low : (Y m) ^ r - (z : ℝ) ^ r ≤ |(Y m) ^ r - (z : ℝ) ^ r| := le_abs_self _
      have hYpow_pos : 0 < (Y m) ^ r := by positivity
      linarith
    exact ⟨hz_pos, hz_ge, hz_le, hdiff⟩
  obtain ⟨hy_pos, hy_ge, hy_le, hy_diff⟩ := hsol_props n y (by omega) hy
  refine ⟨hy_pos, hy_le, fun b hb0 hbn hbM hrb ⟨z, hz⟩ => ?_⟩
  obtain ⟨hz_pos, hz_ge, hz_le, hz_diff⟩ := hsol_props (n - b) z (by omega) hz
  have hYn_pos : 0 < Y n := by dsimp [Y]; positivity
  have hYnb_le : Y (n - b) ≤ Y n := hY_mono (n - b) n (by omega)
  have hz_le_2Y : (z : ℝ) ≤ 2 * Y n := hz_le.trans (by linarith)
  -- Step 1: bound |((n - b)! / n!) * y^r - z^r|
  have hratio_eq : ((n - b).factorial : ℝ) / (n.factorial : ℝ) = (Y (n - b)) ^ r / (Y n) ^ r := by
    dsimp [Y]
    rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
      ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
      one_div_mul_cancel hr_pos.ne', Real.rpow_one, Real.rpow_one]
    have hrpow_ne : (r : ℝ) ^ r ≠ 0 := pow_ne_zero _ hr_pos.ne'
    field_simp [hrpow_ne]
  have hpow_diff : |(((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (y : ℝ) ^ r - (z : ℝ) ^ r| ≤
      2 * K * (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2) := by
    rw [hratio_eq]
    have hYnr : (Y n) ^ r ≠ 0 := pow_ne_zero _ hYn_pos.ne'
    have hid : (Y (n - b)) ^ r / (Y n) ^ r * (y : ℝ) ^ r - (z : ℝ) ^ r =
        (((Y (n - b)) ^ r - (z : ℝ) ^ r) * (y : ℝ) ^ r - ((Y n) ^ r - (y : ℝ) ^ r) * (z : ℝ) ^ r) / (Y n) ^ r := by
      field_simp [hYnr]; ring
    rw [hid, abs_div, abs_of_pos (pow_pos hYn_pos r)]
    have hnum : |((Y (n - b)) ^ r - (z : ℝ) ^ r) * (y : ℝ) ^ r - ((Y n) ^ r - (y : ℝ) ^ r) * (z : ℝ) ^ r| ≤
        2 * K * (2 * Y n) ^ (2 * r - 2) := by
      have h1 : |((Y (n - b)) ^ r - (z : ℝ) ^ r) * (y : ℝ) ^ r| ≤ K * (2 * Y n) ^ (2 * r - 2) := by
        have hyr0 : (0 : ℝ) ≤ (y : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg y) r
        rw [abs_mul, abs_of_nonneg hyr0]
        have hp : (2 * Y n) ^ (r - 2) * (2 * Y n) ^ r = (2 * Y n) ^ (2 * r - 2) := by
          rw [← pow_add]; congr 1; omega
        calc |(Y (n - b)) ^ r - (z : ℝ) ^ r| * (y : ℝ) ^ r
            ≤ (K * (z : ℝ) ^ (r - 2)) * (2 * Y n) ^ r :=
              mul_le_mul hz_diff (pow_le_pow_left₀ (Nat.cast_nonneg _) hy_le r) (by positivity) (by positivity)
          _ ≤ (K * (2 * Y n) ^ (r - 2)) * (2 * Y n) ^ r := by
              have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hz_le_2Y (r - 2)) hK0
              exact mul_le_mul_of_nonneg_right this (by positivity)
          _ = K * ((2 * Y n) ^ (r - 2) * (2 * Y n) ^ r) := by ring
          _ = K * (2 * Y n) ^ (2 * r - 2) := by rw [hp]
      have h2 : |((Y n) ^ r - (y : ℝ) ^ r) * (z : ℝ) ^ r| ≤ K * (2 * Y n) ^ (2 * r - 2) := by
        have hzr0 : (0 : ℝ) ≤ (z : ℝ) ^ r := pow_nonneg (Nat.cast_nonneg z) r
        rw [abs_mul, abs_of_nonneg hzr0]
        have hp : (2 * Y n) ^ (r - 2) * (2 * Y n) ^ r = (2 * Y n) ^ (2 * r - 2) := by
          rw [← pow_add]; congr 1; omega
        calc |(Y n) ^ r - (y : ℝ) ^ r| * (z : ℝ) ^ r
            ≤ (K * (y : ℝ) ^ (r - 2)) * (2 * Y n) ^ r :=
              mul_le_mul hy_diff (pow_le_pow_left₀ (Nat.cast_nonneg _) hz_le_2Y r) (by positivity) (by positivity)
          _ ≤ (K * (2 * Y n) ^ (r - 2)) * (2 * Y n) ^ r := by
              have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hy_le (r - 2)) hK0
              exact mul_le_mul_of_nonneg_right this (by positivity)
          _ = K * ((2 * Y n) ^ (r - 2) * (2 * Y n) ^ r) := by ring
          _ = K * (2 * Y n) ^ (2 * r - 2) := by rw [hp]
      have htri := abs_sub (((Y (n - b)) ^ r - (z : ℝ) ^ r) * (y : ℝ) ^ r) (((Y n) ^ r - (y : ℝ) ^ r) * (z : ℝ) ^ r)
      linarith
    rw [div_le_iff₀ (pow_pos hYn_pos r)]
    have hsplit : (2 * Y n) ^ (2 * r - 2) = (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2) * (Y n) ^ r := by
      rw [mul_pow, mul_assoc, ← pow_add]; congr 2; omega
    calc |((Y (n - b)) ^ r - (z : ℝ) ^ r) * (y : ℝ) ^ r - ((Y n) ^ r - (y : ℝ) ^ r) * (z : ℝ) ^ r|
        ≤ 2 * K * (2 * Y n) ^ (2 * r - 2) := hnum
      _ = 2 * K * (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2) * (Y n) ^ r := by rw [hsplit]; ring
  -- Step 2: Factor A^r - z^r = (A - z) * ∑ A^j * z^(r - 1 - j)
  set A : ℝ := (((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ (1 / (r : ℝ)) * (y : ℝ)
  have hfac_ratio_pos : 0 < ((n - b).factorial : ℝ) / (n.factorial : ℝ) := by positivity
  have hfac_ratio_le1 : ((n - b).factorial : ℝ) / (n.factorial : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast Nat.factorial_le (by omega)
  have hA_pos : 0 < A := by dsimp [A]; positivity
  have hA_pow : A ^ r = (((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (y : ℝ) ^ r := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast hfac_ratio_pos.le,
      one_div_mul_cancel hr_pos.ne', Real.rpow_one]
  have hgeom_ge : A ^ (r - 1) ≤ ∑ j ∈ Finset.range r, A ^ j * (z : ℝ) ^ (r - 1 - j) := by
    have hmem : r - 1 ∈ Finset.range r := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum (f := fun j => A ^ j * (z : ℝ) ^ (r - 1 - j))
      (fun j _ => by positivity) hmem
    simpa [Nat.sub_self] using hsingle
  have hgeom_pos : 0 < ∑ j ∈ Finset.range r, A ^ j * (z : ℝ) ^ (r - 1 - j) :=
    lt_of_lt_of_le (pow_pos hA_pos _) hgeom_ge
  have hfactor : A ^ r - (z : ℝ) ^ r = (A - (z : ℝ)) * ∑ j ∈ Finset.range r, A ^ j * (z : ℝ) ^ (r - 1 - j) := by
    have := geom_sum₂_mul A (z : ℝ) r
    linarith
  have hA_r1_ge : (((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (Y n / 2) ^ (r - 1) ≤ A ^ (r - 1) := by
    dsimp [A]
    rw [mul_pow, ← Real.rpow_mul_natCast hfac_ratio_pos.le]
    have hexp_le : (1 / (r : ℝ)) * ((r - 1 : ℕ) : ℝ) ≤ 1 := by
      have : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show r - 1 ≤ r by omega)
      rw [one_div_mul_eq_div, div_le_one hr_pos]; exact this
    have hrpow_ge : ((n - b).factorial : ℝ) / (n.factorial : ℝ) ≤
        (((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ ((1 / (r : ℝ)) * ((r - 1 : ℕ) : ℝ)) := by
      calc ((n - b).factorial : ℝ) / (n.factorial : ℝ)
          = (((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ ((1 / (r : ℝ)) * ((r - 1 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_ge hfac_ratio_pos hfac_ratio_le1 hexp_le
    exact mul_le_mul hrpow_ge (pow_le_pow_left₀ (by positivity) hy_ge (r - 1)) (by positivity) (by positivity)
  have hAz_le : |A - (z : ℝ)| ≤ 2 * K * (2 : ℝ) ^ (3 * r) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) / Y n := by
    have hmul_le : |A - (z : ℝ)| * ((((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (Y n / 2) ^ (r - 1)) ≤
        2 * K * (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2) := by
      calc |A - (z : ℝ)| * ((((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (Y n / 2) ^ (r - 1))
          ≤ |A - (z : ℝ)| * A ^ (r - 1) := mul_le_mul_of_nonneg_left hA_r1_ge (abs_nonneg _)
        _ ≤ |A - (z : ℝ)| * ∑ j ∈ Finset.range r, A ^ j * (z : ℝ) ^ (r - 1 - j) :=
            mul_le_mul_of_nonneg_left hgeom_ge (abs_nonneg _)
        _ = |A ^ r - (z : ℝ) ^ r| := by rw [hfactor, abs_mul, abs_of_pos hgeom_pos]
        _ ≤ 2 * K * (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2) := by rw [hA_pow]; exact hpow_diff
    rw [le_div_iff₀ hYn_pos]
    have h1 : |A - (z : ℝ)| * Y n ≤
        (2 * K * (2 : ℝ) ^ (2 * r - 2) * (2 : ℝ) ^ (r - 1)) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) := by
      have hpos_den : 0 < (((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (Y n / 2) ^ (r - 1) := by positivity
      have hdiv := (le_div_iff₀ hpos_den).mpr hmul_le
      have hrw : (2 * K * (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2)) /
          ((((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (Y n / 2) ^ (r - 1)) * Y n =
          (2 * K * (2 : ℝ) ^ (2 * r - 2) * (2 : ℝ) ^ (r - 1)) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) := by
        have hYpow : (Y n) ^ (r - 1) = (Y n) ^ (r - 2) * Y n := by
          rw [← pow_succ]; congr 1; omega
        rw [div_pow, hYpow]
        have hf1 : ((n - b).factorial : ℝ) ≠ 0 := by positivity
        have hf2 : (n.factorial : ℝ) ≠ 0 := by positivity
        have hYne : (Y n) ^ (r - 2) ≠ 0 := pow_ne_zero _ hYn_pos.ne'
        have h2ne : (2 : ℝ) ^ (r - 1) ≠ 0 := by positivity
        field_simp [hf1, hf2, hYne, hYn_pos.ne', h2ne]
      calc |A - (z : ℝ)| * Y n
          ≤ (2 * K * (2 : ℝ) ^ (2 * r - 2) * (Y n) ^ (r - 2)) /
              ((((n - b).factorial : ℝ) / (n.factorial : ℝ)) * (Y n / 2) ^ (r - 1)) * Y n :=
            mul_le_mul_of_nonneg_right hdiv hYn_pos.le
        _ = (2 * K * (2 : ℝ) ^ (2 * r - 2) * (2 : ℝ) ^ (r - 1)) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) := hrw
    have h2pow_le : (2 : ℝ) ^ (2 * r - 2) * (2 : ℝ) ^ (r - 1) ≤ (2 : ℝ) ^ (3 * r) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc |A - (z : ℝ)| * Y n
        ≤ (2 * K * ((2 : ℝ) ^ (2 * r - 2) * (2 : ℝ) ^ (r - 1))) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) := by
          linarith
      _ ≤ (2 * K * (2 : ℝ) ^ (3 * r)) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) := by
          have := mul_le_mul_of_nonneg_left h2pow_le (show 0 ≤ 2 * K by linarith)
          exact mul_le_mul_of_nonneg_right this (by positivity)
  -- Step 3: Multiply by n^(b / r) and identify n^(b/r) * A = y * omegaVal r b (1 / n)
  obtain ⟨q, hq⟩ := hrb
  have hnb_eq : (n.factorial : ℝ) / ((n - b).factorial : ℝ) =
      ∏ j ∈ Finset.range b, ((n : ℝ) - (j : ℝ)) := by
    have hnat_gen : ∀ (b' n' : ℕ), b' ≤ n' →
        n'.factorial = (n' - b').factorial * ∏ j ∈ Finset.range b', (n' - j) := by
      intro b'
      induction b' with
      | zero => intro n' _; simp
      | succ b' ih =>
        intro n' hle'
        have h1 : n' - (b' + 1) = (n' - 1) - b' := by omega
        have h2 : n'.factorial = n' * (n' - 1).factorial := by
          cases n' with
          | zero => omega
          | succ m => simp [Nat.factorial_succ]
        rw [h2, ih (n' - 1) (by omega), Finset.prod_range_succ']
        simp only [Nat.sub_zero]
        have h3 : ∏ k ∈ Finset.range b', (n' - (k + 1)) = ∏ k ∈ Finset.range b', (n' - 1 - k) :=
          Finset.prod_congr rfl fun k _ => by omega
        rw [h3, h1]; ring
    have hnat := hnat_gen b n hbn
    have hR : (n.factorial : ℝ) = ((n - b).factorial : ℝ) * ∏ j ∈ Finset.range b, ((n : ℝ) - (j : ℝ)) := by
      have hcast := congrArg (Nat.cast (R := ℝ)) hnat
      push_cast at hcast
      rw [hcast]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j < b := Finset.mem_range.mp hj
      rw [Nat.cast_sub (by omega)]
    rw [hR, mul_div_cancel_left₀ _ (by positivity)]
  have hAw_eq : (n : ℝ) ^ q * A = (y : ℝ) * omegaVal r b (1 / (n : ℝ)) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hprod_eq : (n : ℝ) ^ b * (((n - b).factorial : ℝ) / (n.factorial : ℝ)) =
        ∏ j ∈ Finset.Ico 1 b, (1 - (j : ℝ) * (1 / (n : ℝ)))⁻¹ := by
      have hinv : ((n - b).factorial : ℝ) / (n.factorial : ℝ) =
          (∏ j ∈ Finset.range b, ((n : ℝ) - (j : ℝ)))⁻¹ := by
        rw [← hnb_eq, inv_div]
      have hnpow : (n : ℝ) ^ b = ∏ _j ∈ Finset.range b, (n : ℝ) := by simp
      rw [hinv, hnpow, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      rw [Finset.prod_range_eq_mul_Ico _ hb0]
      simp only [Nat.cast_zero, sub_zero, mul_inv_cancel₀ hn_pos.ne', one_mul]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j < b := (Finset.mem_Ico.mp hj).2
      have hnj_pos : 0 < (n : ℝ) - (j : ℝ) := by
        have : (j : ℝ) < (n : ℝ) := by exact_mod_cast (show j < n by omega)
        linarith
      field_simp [hn_pos.ne', hnj_pos.ne']
    have hnb_rpow : (n : ℝ) ^ q * (((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ (1 / (r : ℝ)) =
        omegaVal r b (1 / (n : ℝ)) := by
      have hnq : (n : ℝ) ^ q = ((n : ℝ) ^ b) ^ (1 / (r : ℝ)) := by
        rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hn_pos.le]
        congr 1; push_cast; field_simp [hr_pos.ne']
      rw [hnq, ← Real.mul_rpow (by positivity) hfac_ratio_pos.le, hprod_eq]
      unfold omegaVal
      rw [← Real.finset_prod_rpow (Finset.Ico 1 b) (fun j => (1 - (j : ℝ) * (1 / (n : ℝ)))⁻¹) (fun j hj => by
        have hj' : j < b := (Finset.mem_Ico.mp hj).2
        have h1 : (j : ℝ) * (1 / (n : ℝ)) < 1 := by
          rw [mul_one_div, div_lt_one hn_pos]; exact_mod_cast (show j < n by omega)
        positivity)]
      refine Finset.prod_congr rfl fun j hj => ?_
      have hj' : j < b := (Finset.mem_Ico.mp hj).2
      have h1 : 0 < 1 - (j : ℝ) * (1 / (n : ℝ)) := by
        have : (j : ℝ) * (1 / (n : ℝ)) < 1 := by
          rw [mul_one_div, div_lt_one hn_pos]; exact_mod_cast (show j < n by omega)
        linarith
      rw [Real.inv_rpow h1.le, ← Real.rpow_neg h1.le, neg_div]
    dsimp [A]
    calc (n : ℝ) ^ q * ((((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ (1 / (r : ℝ)) * (y : ℝ))
        = (y : ℝ) * ((n : ℝ) ^ q * (((n - b).factorial : ℝ) / (n.factorial : ℝ)) ^ (1 / (r : ℝ))) := by ring
      _ = (y : ℝ) * omegaVal r b (1 / (n : ℝ)) := by rw [hnb_rpow]
  refine ⟨((n ^ q * z : ℕ) : ℤ), ?_⟩
  have hcast : (((n ^ q * z : ℕ) : ℤ) : ℝ) = (n : ℝ) ^ q * (z : ℝ) := by push_cast; ring
  rw [hcast, ← hAw_eq, ← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg (Nat.cast_nonneg n) q)]
  have hnq_le : (n : ℝ) ^ q ≤ (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ := by
    have hqb : q ≤ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ := by
      have : q ≤ b := by rw [hq]; exact Nat.le_mul_of_pos_left q (by omega)
      exact this.trans hbM
    calc (n : ℝ) ^ q ≤ (2 * (N : ℝ)) ^ q :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show n ≤ 2 * N by omega)) q
      _ ≤ (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * N by omega)) hqb
  have hfac_le : (n.factorial : ℝ) / ((n - b).factorial : ℝ) ≤ (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ := by
    rw [hnb_eq]
    calc ∏ j ∈ Finset.range b, ((n : ℝ) - (j : ℝ))
        ≤ ∏ _j ∈ Finset.range b, (2 * (N : ℝ)) := by
          refine Finset.prod_le_prod (fun j hj => ?_) (fun j _ => ?_)
          · have : j < b := Finset.mem_range.mp hj
            have : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show j ≤ n by omega)
            linarith
          · have : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast (show n ≤ 2 * N by omega)
            linarith [Nat.cast_nonneg (α := ℝ) j]
      _ = (2 * (N : ℝ)) ^ b := by simp
      _ ≤ (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ :=
          pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 2 * N by omega)) hbM
  have herr_n : Kbig * (2 * (N : ℝ)) ^ (2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊) ≤ (Y n) ^ η :=
    herr.trans (Real.rpow_le_rpow (by dsimp [Y]; positivity) (hY_mono N n hNn) hη.le)
  have hpow2M : (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ * (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ =
      (2 * (N : ℝ)) ^ (2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊) := by
    rw [← pow_add]; congr 1; ring
  have hK_le_Kbig : 2 * K * (2 : ℝ) ^ (3 * r) ≤ Kbig := by dsimp [Kbig]; linarith
  have hrpow_div : (Y n) ^ η / Y n = 1 / (Y n) ^ (1 - η) := by
    rw [Real.rpow_sub hYn_pos, Real.rpow_one, one_div_div]
  calc (n : ℝ) ^ q * |A - (z : ℝ)|
      ≤ (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ *
          (2 * K * (2 : ℝ) ^ (3 * r) * ((n.factorial : ℝ) / ((n - b).factorial : ℝ)) / Y n) :=
        mul_le_mul hnq_le hAz_le (abs_nonneg _) (by positivity)
    _ ≤ (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ *
          (Kbig * (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ / Y n) := by
        have p1 := mul_le_mul hK_le_Kbig hfac_le (by positivity) hKbig_pos.le
        have p2 := div_le_div_of_nonneg_right p1 hYn_pos.le
        exact mul_le_mul_of_nonneg_left p2 (by positivity)
    _ = Kbig * ((2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊ * (2 * (N : ℝ)) ^ ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊) / Y n := by
        ring
    _ = Kbig * (2 * (N : ℝ)) ^ (2 * ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊) / Y n := by rw [hpow2M]
    _ ≤ (Y n) ^ η / Y n := div_le_div_of_nonneg_right herr_n hYn_pos.le
    _ = 1 / (Y n) ^ (1 - η) := hrpow_div

/- #### Part 3E: Block pigeonhole, dyadic summation, and Erdos 393 reductions -/

private lemma block_pigeonhole_bound (r N M : ℕ) (hr : 2 ≤ r) (hM : 1 ≤ M)
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico N (2 * N)) (K : ℝ) (hK : 0 ≤ K)
    (hcount : ∀ u v : ℕ, 0 < u → u < v → v ≤ M → r ∣ u → r ∣ v →
      ((S.filter (fun n => v ≤ n ∧ n - u ∈ S ∧ n - v ∈ S)).card : ℝ) ≤ K * (N : ℝ) / (M : ℝ) ^ 3) :
    (S.card : ℝ) ≤ (2 * (r : ℝ) + K) * (N : ℝ) / (M : ℝ) + 4 * (r : ℝ) := by
  classical
  let key : ℕ → ℕ × ℕ := fun n => (n / M, n % r)
  let hasTwo : ℕ → Prop := fun n => ∃ x ∈ S, ∃ y ∈ S, x < y ∧ y < n ∧ key x = key n ∧ key y = key n
  let E := S.filter hasTwo
  let G := S.filter (fun n => ¬ hasTwo n)
  have hScard : S.card = E.card + G.card := (Finset.card_filter_add_card_filter_not _).symm
  -- Bound E.card by union over pairs (u, v)
  let P := ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter (fun uv : ℕ × ℕ => uv.1 < uv.2 ∧ r ∣ uv.1 ∧ r ∣ uv.2)
  have hE_sub : E ⊆ P.biUnion (fun uv => S.filter (fun n => uv.2 ≤ n ∧ n - uv.1 ∈ S ∧ n - uv.2 ∈ S)) := by
    intro n hn
    obtain ⟨hnS, x, hxS, y, hyS, hxy, hyn, hkx, hky⟩ := Finset.mem_filter.mp hn
    have hkx1 : x / M = n / M := congrArg Prod.fst hkx
    have hkx2 : x % r = n % r := congrArg Prod.snd hkx
    have hky1 : y / M = n / M := congrArg Prod.fst hky
    have hky2 : y % r = n % r := congrArg Prod.snd hky
    have hnx_lt : n - x < M := by
      have h1 := Nat.div_add_mod n M
      have h2 := Nat.div_add_mod x M
      have h3 := Nat.mod_lt n (by omega : 0 < M)
      rw [← hkx1] at h1; omega
    have hny_lt : n - y < M := by
      have h1 := Nat.div_add_mod n M
      have h2 := Nat.div_add_mod y M
      have h3 := Nat.mod_lt n (by omega : 0 < M)
      rw [← hky1] at h1; omega
    refine Finset.mem_biUnion.mpr ⟨(n - y, n - x), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩,
        by omega, (Nat.modEq_iff_dvd' (by omega)).mp hky2, (Nat.modEq_iff_dvd' (by omega)).mp hkx2⟩
    · refine Finset.mem_filter.mpr ⟨hnS, by omega, ?_, ?_⟩
      · rwa [Nat.sub_sub_self (by omega)]
      · rwa [Nat.sub_sub_self (by omega)]
  have hE_card : (E.card : ℝ) ≤ K * (N : ℝ) / (M : ℝ) := by
    have h1 : E.card ≤ ∑ uv ∈ P, (S.filter (fun n => uv.2 ≤ n ∧ n - uv.1 ∈ S ∧ n - uv.2 ∈ S)).card :=
      (Finset.card_le_card hE_sub).trans Finset.card_biUnion_le
    have h1R : (E.card : ℝ) ≤ ∑ uv ∈ P, ((S.filter (fun n => uv.2 ≤ n ∧ n - uv.1 ∈ S ∧ n - uv.2 ∈ S)).card : ℝ) := by
      exact_mod_cast h1
    have hPcard : P.card ≤ M * M := by
      calc P.card ≤ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).card := Finset.card_filter_le _ _
        _ = M * M := by simp
    have h2 : ∑ uv ∈ P, ((S.filter (fun n => uv.2 ≤ n ∧ n - uv.1 ∈ S ∧ n - uv.2 ∈ S)).card : ℝ) ≤
        (P.card : ℝ) * (K * (N : ℝ) / (M : ℝ) ^ 3) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun uv huv => ?_
      obtain ⟨huvP, hlt, du, dv⟩ := Finset.mem_filter.mp huv
      obtain ⟨hu, hv⟩ := Finset.mem_product.mp huvP
      exact hcount uv.1 uv.2 (by have := (Finset.mem_Icc.mp hu).1; omega) hlt
        (Finset.mem_Icc.mp hv).2 du dv
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    calc (E.card : ℝ) ≤ (P.card : ℝ) * (K * (N : ℝ) / (M : ℝ) ^ 3) := h1R.trans h2
      _ ≤ ((M : ℝ) * (M : ℝ)) * (K * (N : ℝ) / (M : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hPcard) (by positivity)
      _ = K * (N : ℝ) / (M : ℝ) := by field_simp [hMpos.ne']
  -- Bound G.card: at most 2 elements per fiber of `key` on `Ico (N / M) (2 * N / M + 1) × range r`
  let cells := (Finset.Icc (N / M) ((2 * N) / M)) ×ˢ (Finset.range r)
  have hG_fiber : ∀ c ∈ cells, (G.filter (fun n => key n = c)).card ≤ 2 := by
    intro c _
    by_contra hgt
    push Not at hgt
    have h3 : 3 ≤ (G.filter (fun n => key n = c)).card := hgt
    -- Extract 3 distinct elements from the fiber
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < (G.filter (fun n => key n = c)).card)
    have hcard1 : 2 ≤ ((G.filter (fun n => key n = c)).erase a).card := by
      rw [Finset.card_erase_of_mem ha]; omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < ((G.filter (fun n => key n = c)).erase a).card)
    have hcard2 : 1 ≤ (((G.filter (fun n => key n = c)).erase a).erase b).card := by
      rw [Finset.card_erase_of_mem hb]; omega
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (((G.filter (fun n => key n = c)).erase a).erase b).card)
    have hab : b ≠ a := (Finset.mem_erase.mp hb).1
    have hdb : d ≠ b := (Finset.mem_erase.mp hd).1
    have hda : d ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).1
    have hbF := (Finset.mem_erase.mp hb).2
    have hdF := (Finset.mem_erase.mp (Finset.mem_erase.mp hd).2).2
    obtain ⟨haG, hka⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbG, hkb⟩ := Finset.mem_filter.mp hbF
    obtain ⟨hdG, hkd⟩ := Finset.mem_filter.mp hdF
    obtain ⟨haS, hna⟩ := Finset.mem_filter.mp haG
    obtain ⟨hbS, hnb⟩ := Finset.mem_filter.mp hbG
    obtain ⟨hdS, hnd⟩ := Finset.mem_filter.mp hdG
    -- Whichever of a, b, d is largest has two strictly smaller elements in S with the same key!
    by_cases h1 : a < b
    · by_cases h2 : b < d
      · exact hnd ⟨a, haS, b, hbS, h1, h2, hka.trans hkd.symm, hkb.trans hkd.symm⟩
      · by_cases h3' : a < d
        · exact hnb ⟨a, haS, d, hdS, h3', by omega, hka.trans hkb.symm, hkd.trans hkb.symm⟩
        · exact hnb ⟨d, hdS, a, haS, by omega, h1, hkd.trans hkb.symm, hka.trans hkb.symm⟩
    · by_cases h2 : a < d
      · exact hnd ⟨b, hbS, a, haS, by omega, h2, hkb.trans hkd.symm, hka.trans hkd.symm⟩
      · by_cases h3' : b < d
        · exact hna ⟨b, hbS, d, hdS, h3', by omega, hkb.trans hka.symm, hkd.trans hka.symm⟩
        · exact hna ⟨d, hdS, b, hbS, by omega, by omega, hkd.trans hka.symm, hkb.trans hka.symm⟩
  have hG_maps : ∀ n ∈ G, key n ∈ cells := by
    intro n hn
    have hnS := (Finset.mem_filter.mp hn).1
    have hnIco := hS hnS
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hnIco
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.div_le_div_right h1, Nat.div_le_div_right h2.le⟩,
      Finset.mem_range.mpr (Nat.mod_lt n (by omega))⟩
  have hG_card : G.card ≤ 2 * cells.card := by
    rw [Finset.card_eq_sum_card_fiberwise hG_maps]
    calc ∑ c ∈ cells, (G.filter (fun n => key n = c)).card
        ≤ ∑ _c ∈ cells, 2 := Finset.sum_le_sum hG_fiber
      _ = 2 * cells.card := by simp [mul_comm]
  have hcells_card : (cells.card : ℝ) ≤ (N : ℝ) / (M : ℝ) * (r : ℝ) + 2 * (r : ℝ) := by
    have hnat : cells.card = ((2 * N) / M + 1 - N / M) * r := by
      simp [cells, Nat.card_Icc]
    have hdiv_bound : ((2 * N) / M + 1 - N / M : ℕ) * M ≤ N + 2 * M := by
      have h1 := Nat.div_mul_le_self (2 * N) M
      have h2 := Nat.lt_div_mul_add (a := N) (b := M) (by omega)
      have hle : N / M ≤ (2 * N) / M := Nat.div_le_div_right (by omega)
      have hsub : ((2 * N) / M + 1 - N / M) * M = (2 * N) / M * M + M - N / M * M := by
        rw [Nat.sub_mul, Nat.add_mul, one_mul]
      omega
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hR : (((2 * N) / M + 1 - N / M : ℕ) : ℝ) ≤ (N : ℝ) / (M : ℝ) + 2 := by
      rw [show (N : ℝ) / (M : ℝ) + 2 = ((N : ℝ) + 2 * (M : ℝ)) / (M : ℝ) by field_simp [hMpos.ne']]
      rw [le_div_iff₀ hMpos]
      have hcast : (((2 * N) / M + 1 - N / M : ℕ) : ℝ) * (M : ℝ) ≤ (N : ℝ) + 2 * (M : ℝ) := by
        exact_mod_cast hdiv_bound
      linarith
    rw [hnat, Nat.cast_mul]
    have := mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg r)
    linarith
  have hScardR : (S.card : ℝ) = (E.card : ℝ) + (G.card : ℝ) := by exact_mod_cast hScard
  have hGcardR : (G.card : ℝ) ≤ 2 * (cells.card : ℝ) := by exact_mod_cast hG_card
  have hring : (2 * (r : ℝ) + K) * (N : ℝ) / (M : ℝ) + 4 * (r : ℝ) =
      K * (N : ℝ) / (M : ℝ) + 2 * ((N : ℝ) / (M : ℝ) * (r : ℝ) + 2 * (r : ℝ)) := by ring
  linarith

private lemma dyadic_count_bound {P : ℕ → Prop} [DecidablePred P] {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α)
    (hb : ∀ N : ℕ, 1 ≤ N → (((Finset.Ico N (2 * N)).filter P).card : ℝ) ≤ c * (N : ℝ) ^ α) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, 1 ≤ N → (((Finset.range (N + 1)).filter P).card : ℝ) ≤ D * (N : ℝ) ^ α := by
  let q : ℝ := (2 : ℝ) ^ α
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) hα
  let d : ℝ := 1 + c / (q - 1)
  have hd1 : 1 ≤ d := by dsimp [d]; linarith [div_nonneg hc (sub_nonneg.mpr hq.le)]
  have hstep : d + c ≤ d * q := by
    have he := div_mul_cancel₀ c (sub_ne_zero.mpr hq.ne')
    dsimp [d]; linarith
  have hpow : ∀ j : ℕ, (((Finset.range (2 ^ j)).filter P).card : ℝ) ≤ d * q ^ j := by
    intro j
    induction j with
    | zero =>
      simp only [pow_zero, mul_one]
      have hcard : ((Finset.range 1).filter P).card ≤ 1 :=
        (Finset.card_filter_le _ _).trans_eq (Finset.card_range 1)
      exact (by exact_mod_cast hcard : (((Finset.range 1).filter P).card : ℝ) ≤ 1).trans hd1
    | succ j ih =>
      let L := 2 ^ j
      have hsub : (Finset.range (2 ^ (j + 1))).filter P ⊆
          (Finset.range L).filter P ∪ (Finset.Ico L (2 * L)).filter P := by
        intro n hn
        obtain ⟨hlt, hP⟩ := Finset.mem_filter.mp hn
        have hlt' : n < 2 * L := by
          have := Finset.mem_range.mp hlt; dsimp [L]; rw [pow_succ, mul_comm] at this; exact this
        by_cases h : n < L
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h, hP⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hlt'⟩, hP⟩)
      have hub : (((Finset.range (2 ^ (j + 1))).filter P).card : ℝ) ≤
          (((Finset.range L).filter P).card : ℝ) + (((Finset.Ico L (2 * L)).filter P).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hL_rpow : (L : ℝ) ^ α = q ^ j := by
        dsimp [L, q]
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
          mul_comm, Real.rpow_mul_natCast (by norm_num)]
      have hblock := hb L (Nat.one_le_pow j 2 (by norm_num))
      rw [hL_rpow] at hblock
      have hmul := mul_le_mul_of_nonneg_right hstep (show 0 ≤ q ^ j by positivity)
      rw [show d * q ^ (j + 1) = d * q * q ^ j by ring]
      linarith
  refine ⟨d * q, mul_nonneg (by linarith) (by linarith), fun N hN => ?_⟩
  let j := Nat.log 2 N
  have hlt : N < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  have hge : 2 ^ j ≤ N := Nat.pow_log_le_self 2 (by omega)
  have hsub : (Finset.range (N + 1)).filter P ⊆ (Finset.range (2 ^ (j + 1))).filter P :=
    Finset.filter_subset_filter _ (Finset.range_mono (by omega))
  have hqj : q ^ j ≤ (N : ℝ) ^ α := by
    have h1 : ((2 ^ j : ℕ) : ℝ) ^ α = q ^ j := by
      dsimp [q]; rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num),
        mul_comm, Real.rpow_mul_natCast (by norm_num)]
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hge) hα.le
  calc (((Finset.range (N + 1)).filter P).card : ℝ)
      ≤ (((Finset.range (2 ^ (j + 1))).filter P).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ d * q ^ (j + 1) := hpow (j + 1)
    _ = d * q * q ^ j := by ring
    _ ≤ d * q * (N : ℝ) ^ α := mul_le_mul_of_nonneg_left hqj (mul_nonneg (by linarith) (by linarith))

private lemma erdos393_factor_pattern {n m : ℕ} (hn : 2 ≤ n) (hm : Erdos393.f n = m) :
    ∃ T ∈ (Finset.Icc 0 m).powerset, 2 ≤ T.card ∧
      ∃ y : ℕ, (T.card : ℤ) ^ T.card * (n.factorial : ℤ) =
        ∏ i ∈ T, ((y : ℤ) + (T.card : ℤ) * (i : ℤ) - ∑ j ∈ T, (j : ℤ)) := by
  let D := {w : ℕ | 1 ≤ w ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + w),
    a ∈ s ∧ a + w ∈ s ∧ ∏ i ∈ s, i = n.factorial}
  have hDne : D.Nonempty := by
    refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_, Finset.prod_Ico_id_eq_factorial n⟩
    · intro i hi
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
    · exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hmD : m ∈ D := hm ▸ Nat.sInf_mem hDne
  obtain ⟨hm1, a, s, hs, ha, hb, hprod⟩ := hmD
  let T := s.image (fun i => i - a)
  have hge : ∀ i ∈ s, a ≤ i := fun i hi => (Finset.mem_Icc.mp (hs hi)).1
  have hinj : Set.InjOn (fun i : ℕ => i - a) ↑s := by
    intro i hi j hj heq
    dsimp only at heq
    have := hge i hi; have := hge j hj; omega
  have hTmem : T ∈ (Finset.Icc 0 m).powerset := by
    refine Finset.mem_powerset.mpr fun i hi => ?_
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by have := (Finset.mem_Icc.mp (hs hj)).2; omega⟩
  have hTcard : 2 ≤ T.card := by
    have h2 : 1 < s.card := Finset.one_lt_card.mpr ⟨a, ha, a + m, hb, by omega⟩
    rw [Finset.card_image_of_injOn hinj]; omega
  have hTprod : ∏ i ∈ T, (a + i) = n.factorial := by
    dsimp only [T]
    rw [Finset.prod_image hinj]
    exact (Finset.prod_congr rfl fun i hi => by have := hge i hi; omega).trans hprod
  refine ⟨T, hTmem, hTcard, T.card * a + ∑ j ∈ T, j, ?_⟩
  have hZ : ∏ i ∈ T, ((a : ℤ) + (i : ℤ)) = (n.factorial : ℤ) := by exact_mod_cast hTprod
  push_cast
  rw [← hZ, ← Finset.prod_const (s := T) (T.card : ℤ), ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun _ _ => by ring


private lemma eventually_rpow_gt_const (C α : ℝ) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ α :=
  ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop C)

private lemma log_le_100_rpow (x : ℝ) (hx : 0 ≤ x) :
    Real.log x ≤ 100 * x ^ (1 / 100 : ℝ) := by
  have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 100)
  linarith

private lemma log_Y_lower {r n : ℕ} (hr : 1 ≤ r) (hn : 10 ≤ n) :
    (n : ℝ) / (4 * (r : ℝ)) * Real.log (n : ℝ) ≤
      Real.log ((r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hfac : ((n / 2 : ℕ) : ℝ) ^ (n / 2) ≤ (n.factorial : ℝ) := by
    have hnat : (n / 2) ^ (n / 2) ≤ n.factorial := by
      set h := n / 2
      rw [← Finset.prod_Ico_id_eq_factorial]
      have hsub : Finset.Ico (n + 1 - h) (n + 1) ⊆ Finset.Ico 1 (n + 1) := by
        intro i hi; simp only [Finset.mem_Ico] at hi ⊢; omega
      calc h ^ h
          = ∏ _i ∈ Finset.Ico (n + 1 - h) (n + 1), h := by
            rw [Finset.prod_const, Nat.card_Ico]; congr 1; omega
        _ ≤ ∏ i ∈ Finset.Ico (n + 1 - h) (n + 1), i :=
            Finset.prod_le_prod' fun i hi => by have := (Finset.mem_Ico.mp hi).1; omega
        _ ≤ ∏ i ∈ Finset.Ico 1 (n + 1), i :=
            Finset.prod_le_prod_of_subset_of_one_le' hsub fun i hi _ => (Finset.mem_Ico.mp hi).1
    exact_mod_cast hnat
  have hN2_pos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n / 2 by omega)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : (((n / 2 : ℕ) : ℝ) ^ (n / 2)) ^ (1 / (r : ℝ)) ≤
      (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ)) := by
    calc (((n / 2 : ℕ) : ℝ) ^ (n / 2)) ^ (1 / (r : ℝ))
        ≤ (n.factorial : ℝ) ^ (1 / (r : ℝ)) :=
          Real.rpow_le_rpow (by positivity) hfac (by positivity)
      _ = 1 * (n.factorial : ℝ) ^ (1 / (r : ℝ)) := (one_mul _).symm
      _ ≤ (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ)) :=
          mul_le_mul_of_nonneg_right hr1 (by positivity)
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_rpow (by positivity), Real.log_pow] at h2
  -- Show (n/2) * log(n/2) ≥ (n/4) * log n for n ≥ 10:
  -- Indeed n ≤ (n/2)^2 for n ≥ 10 (5^2 = 25 ≥ 10), wait: for n ≥ 10, n/2 ≥ 5, (n/2)^2 ≥ 2*n > n, so log n ≤ 2 * log(n/2)!
  -- Wait: that gives (n/2) * log(n/2) ≥ (n/2) * (1/2) * log n = (n/4) * log n?
  -- Carefully: n/2 ≥ (n - 1) / 2 ≥ 9/20 * n, so (n/2) * log(n/2) ≥ (9/20 * n) * (1/2 * log n) = 9/40 * n * log n...
  -- Actually for n ≥ 10: (n/2) ≥ 5, and n ≤ (n/2)^2 / 2? Check n = 10: n/2 = 5, 5^2 = 25 ≥ 10!
  -- Even sharper: n^3 ≤ (n/2)^5? Check n = 10: 1000 ≤ 3125! Then 3 log n ≤ 5 log(n/2), and n/2 ≥ 9/20 n, (9/20)*(3/5) = 27/100 > 1/4!
  have hlog_cmp : (3 : ℝ) / 5 * Real.log (n : ℝ) ≤ Real.log ((n / 2 : ℕ) : ℝ) := by
    have hpow : (n : ℝ) ^ 3 ≤ ((n / 2 : ℕ) : ℝ) ^ 5 := by
      have hnat : n ^ 3 ≤ (n / 2) ^ 5 := by
        have hq : 5 ≤ n / 2 := by omega
        have hnle : n ≤ 2 * (n / 2) + 1 := by omega
        -- (2k + 1)^3 = 8k^3 + 12k^2 + 6k + 1 ≤ k^5 for k ≥ 5 (k=5: 1331 ≤ 3125)
        set k := n / 2
        have h1 : n ^ 3 ≤ (2 * k + 1) ^ 3 := Nat.pow_le_pow_left hnle 3
        have h2 : (2 * k + 1) ^ 3 ≤ k ^ 5 := by
          have hk2 : 25 ≤ k * k := by nlinarith
          have hk1 : k ≤ k ^ 2 := by nlinarith
          have hk23 : k ^ 2 ≤ k ^ 3 := by nlinarith
          calc (2 * k + 1) ^ 3 = 8 * k ^ 3 + 12 * k ^ 2 + 6 * k + 1 := by ring
            _ ≤ 8 * k ^ 3 + 12 * k ^ 3 + 5 * k ^ 3 := by nlinarith
            _ = 25 * k ^ 3 := by ring
            _ ≤ (k * k) * k ^ 3 := Nat.mul_le_mul_right _ hk2
            _ = k ^ 5 := by ring
        exact h1.trans h2
      exact_mod_cast hnat
    have hlogp := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow, Real.log_pow] at hlogp
    push_cast at hlogp
    linarith
  have hn2_ge : (9 : ℝ) / 20 * (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
    have : 9 * n ≤ 20 * (n / 2) := by omega
    have hR : (9 : ℝ) * (n : ℝ) ≤ 20 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hprod_ge : (n : ℝ) / 4 * Real.log (n : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ) := by
    have hmul := mul_le_mul hn2_ge hlog_cmp (by positivity) (by positivity)
    have hnn : 0 ≤ (n : ℝ) * Real.log (n : ℝ) := mul_nonneg (Nat.cast_nonneg n) hlogn_nonneg
    nlinarith
  have hdiv_ge : (1 / (r : ℝ)) * ((n : ℝ) / 4 * Real.log (n : ℝ)) ≤
      (1 / (r : ℝ)) * (((n / 2 : ℕ) : ℝ) * Real.log ((n / 2 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hprod_ge (by positivity)
  have hring : (n : ℝ) / (4 * (r : ℝ)) * Real.log (n : ℝ) =
      (1 / (r : ℝ)) * ((n : ℝ) / 4 * Real.log (n : ℝ)) := by ring
  linarith

private lemma log_Y_upper {r n : ℕ} (hr : 1 ≤ r) (hn : 2 ≤ n) :
    Real.log ((r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))) ≤
      Real.log (r : ℝ) + ((n : ℝ) / (r : ℝ)) * Real.log (n : ℝ) := by
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
    have hnat : n.factorial ≤ n ^ n := by
      rw [← Finset.prod_Ico_id_eq_factorial]
      calc ∏ i ∈ Finset.Ico 1 (n + 1), i
          ≤ ∏ _i ∈ Finset.Ico 1 (n + 1), n :=
            Finset.prod_le_prod' fun i hi => by have := (Finset.mem_Ico.mp hi).2; omega
        _ = n ^ n := by simp
    exact_mod_cast hnat
  have h1 : (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ)) ≤
      (r : ℝ) * ((n : ℝ) ^ n) ^ (1 / (r : ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hfac (by positivity)) hr_pos.le
  have h2 := Real.log_le_log (by positivity) h1
  have hRHS : Real.log ((r : ℝ) * ((n : ℝ) ^ n) ^ (1 / (r : ℝ))) =
      Real.log (r : ℝ) + ((n : ℝ) / (r : ℝ)) * Real.log (n : ℝ) := by
    rw [Real.log_mul hr_pos.ne' (Real.rpow_pos_of_pos (pow_pos hn_pos n) _).ne',
      Real.log_rpow (pow_pos hn_pos n), Real.log_pow]
    ring
  linarith

private lemma rpow_prod_CU {N : ℝ} (hN : 0 < N) :
    N ^ (1 / 8568 : ℝ) * (N * N ^ (493 / 2856 : ℝ)) = N ^ (10048 / 8568 : ℝ) := by
  have h1 : N * N ^ (493 / 2856 : ℝ) = N ^ (1 + 493 / 2856 : ℝ) := by
    rw [Real.rpow_add hN, Real.rpow_one]
  rw [h1, ← Real.rpow_add hN]; norm_num

private lemma rpow_prod_WC {N : ℝ} (hN : 0 < N) :
    N ^ (10049 / 8568 : ℝ) * (N ^ (1 / 8568 : ℝ) * (N * N ^ (58 / 238 : ℝ))) = N ^ (29 / 12 : ℝ) := by
  have h1 : N * N ^ (58 / 238 : ℝ) = N ^ (1 + 58 / 238 : ℝ) := by
    rw [Real.rpow_add hN, Real.rpow_one]
  rw [h1, ← Real.rpow_add hN, ← Real.rpow_add hN]; norm_num

set_option maxHeartbeats 800000 in
private lemma pade_big_log_bound {r N M K_max : ℕ} (hr : 2 ≤ r) (hN : 10000 ≤ N)
    (hM_le : (M : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ))
    (hK_def : K_max = ⌈(M : ℝ) ^ 3 * Real.log (N : ℝ)⌉₊)
    {W_b C_b : ℝ} (hWC_ge1 : (1 : ℝ) ≤ W_b / C_b) (hWC_le_N3 : W_b / C_b ≤ (N : ℝ) ^ (3 : ℕ)) :
    let c := (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1))
    let u_c := (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (64 : ℝ) ^ M
    let w_c := 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (16 : ℝ) ^ M
    Real.log (8 * c * u_c * ((W_b / C_b) * 8 * c * w_c)) ≤
      (10000000 * (Real.log (4 * (r : ℝ)) + 200)) * (N : ℝ) ^ (1 / 4 : ℝ) := by
  dsimp only
  set c := (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1))
  set u_c := (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (64 : ℝ) ^ M
  set w_c := 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (16 : ℝ) ^ M
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hlog_pos : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN_ge1
  have hlog_le_100 : Real.log (N : ℝ) ≤ 100 * (N : ℝ) ^ (1 / 100 : ℝ) := log_le_100_rpow _ hN_pos.le
  have hL4r : 0 ≤ Real.log (4 * (r : ℝ)) := Real.log_nonneg (by linarith)
  have hK_le : (K_max : ℝ) ≤ 100 * (N : ℝ) ^ (1 / 10 : ℝ) + 1 := by
    rw [hK_def]
    have hceil := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (M : ℝ) ^ 3 * Real.log (N : ℝ))).le
    have hM3 : (M : ℝ) ^ 3 ≤ (N : ℝ) ^ (3 / 34 : ℝ) := by
      calc (M : ℝ) ^ 3 ≤ ((N : ℝ) ^ (1 / 34 : ℝ)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hM_le 3
        _ = (N : ℝ) ^ (3 / 34 : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
    have hprod : (M : ℝ) ^ 3 * Real.log (N : ℝ) ≤ 100 * (N : ℝ) ^ (1 / 10 : ℝ) := by
      calc (M : ℝ) ^ 3 * Real.log (N : ℝ)
          ≤ (N : ℝ) ^ (3 / 34 : ℝ) * (100 * (N : ℝ) ^ (1 / 100 : ℝ)) :=
            mul_le_mul hM3 hlog_le_100 hlog_pos (by positivity)
        _ = 100 * ((N : ℝ) ^ (3 / 34 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ)) := by ring
        _ = 100 * (N : ℝ) ^ (3 / 34 + 1 / 100 : ℝ) := by rw [← Real.rpow_add hN_pos]
        _ ≤ 100 * (N : ℝ) ^ (1 / 10 : ℝ) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)) (by norm_num)
    linarith
  have hK2 : ((K_max + 2 : ℕ) : ℝ) ≤ 200 * (N : ℝ) ^ (1 / 10 : ℝ) := by
    push_cast
    have h10 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
    linarith
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 34 : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
    linarith
  have hKM : (((K_max + 2) * (M + 1) : ℕ) : ℝ) ≤ 400 * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h1 := mul_le_mul hK2 hM1 (Nat.cast_nonneg _) (by positivity)
    have h2 : (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 34 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) := by
      rw [← Real.rpow_add hN_pos]
      exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
    rw [Nat.cast_mul]
    calc ((K_max + 2 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ)
        ≤ 400 * ((N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (1 / 34 : ℝ)) := by linarith
      _ ≤ 400 * (N : ℝ) ^ (1 / 5 : ℝ) := mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hlog4rN : Real.log (4 * (r : ℝ) * (N : ℝ)) ≤ (Real.log (4 * (r : ℝ)) + 100) * (N : ℝ) ^ (1 / 100 : ℝ) := by
    rw [Real.log_mul (by positivity) hN_pos.ne']
    have h100 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 100 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
    nlinarith
  have hlog2rN : Real.log (2 * (r : ℝ) * (N : ℝ)) ≤ Real.log (4 * (r : ℝ) * (N : ℝ)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hu_pos : 0 < u_c := by dsimp [u_c]; positivity
  have hw_pos : 0 < w_c := by dsimp [w_c]; positivity
  have hWC_pos : 0 < W_b / C_b := by linarith
  have hpow5100 : (N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hN_pos]; exact Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
  have hlog_c : Real.log c ≤ 400 * (Real.log (4 * (r : ℝ)) + 100) * (N : ℝ) ^ (1 / 4 : ℝ) := by
    dsimp [c]; rw [Real.log_pow]
    have h1 := mul_le_mul hKM (hlog2rN.trans hlog4rN) (Real.log_nonneg (by nlinarith)) (by positivity)
    calc (((K_max + 2) * (M + 1) : ℕ) : ℝ) * Real.log (2 * (r : ℝ) * (N : ℝ))
        ≤ 400 * (Real.log (4 * (r : ℝ)) + 100) * ((N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ)) := by linarith
      _ ≤ 400 * (Real.log (4 * (r : ℝ)) + 100) * (N : ℝ) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hpow5100 (by linarith)
  have hl2 : Real.log 2 ≤ 1 := by
    calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
      _ = 1 := Real.log_exp 1
  have hl64 : Real.log 64 ≤ 6 := by
    rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; push_cast; linarith
  have hlog_u : Real.log u_c ≤ 400 * (Real.log (4 * (r : ℝ)) + 100) * (N : ℝ) ^ (1 / 4 : ℝ) + 6 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    dsimp [u_c]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have hK_le' : ((K_max + 2 : ℕ) : ℝ) ≤ 400 * (N : ℝ) ^ (1 / 5 : ℝ) := by
      have : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      linarith
    have h1 : ((K_max + 2 : ℕ) : ℝ) * Real.log (4 * (r : ℝ) * (N : ℝ)) ≤
        400 * (Real.log (4 * (r : ℝ)) + 100) * (N : ℝ) ^ (1 / 4 : ℝ) := by
      have hmul := mul_le_mul hK_le' hlog4rN (Real.log_nonneg (by nlinarith)) (by positivity)
      calc ((K_max + 2 : ℕ) : ℝ) * Real.log (4 * (r : ℝ) * (N : ℝ))
          ≤ 400 * (Real.log (4 * (r : ℝ)) + 100) * ((N : ℝ) ^ (1 / 5 : ℝ) * (N : ℝ) ^ (1 / 100 : ℝ)) := by linarith
        _ ≤ 400 * (Real.log (4 * (r : ℝ)) + 100) * (N : ℝ) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow5100 (by linarith)
    have hM_le4 : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
      hM_le.trans (Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num))
    have h2 : (M : ℝ) * Real.log 64 ≤ 6 * (N : ℝ) ^ (1 / 4 : ℝ) := by
      have := mul_le_mul hM_le4 hl64 (Real.log_nonneg (by norm_num)) (by positivity)
      linarith
    linarith
  have hlog_w : Real.log w_c ≤ Real.log 2 + Real.log u_c := by
    have hwle : w_c ≤ 2 * u_c := by
      dsimp [w_c, u_c]
      have h1 : (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) ≤ (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) :=
        pow_le_pow_left₀ (by positivity) (by nlinarith) _
      have h2 : (16 : ℝ) ^ M ≤ (64 : ℝ) ^ M := pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
      linarith
    rw [← Real.log_mul (by norm_num) hu_pos.ne']
    exact Real.log_le_log hw_pos hwle
  have hlog_WC : Real.log (W_b / C_b) ≤ 300 * (N : ℝ) ^ (1 / 4 : ℝ) := by
    calc Real.log (W_b / C_b) ≤ Real.log ((N : ℝ) ^ (3 : ℕ)) := Real.log_le_log hWC_pos hWC_le_N3
      _ = 3 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num
      _ ≤ 3 * (100 * (N : ℝ) ^ (1 / 100 : ℝ)) := by linarith
      _ ≤ 300 * (N : ℝ) ^ (1 / 4 : ℝ) := by
          have := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num : (1 / 100 : ℝ) ≤ 1 / 4)
          linarith
  have h14 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
  have hprod_log : Real.log (8 * c * u_c * ((W_b / C_b) * 8 * c * w_c)) =
      Real.log 64 + 2 * Real.log c + Real.log u_c + Real.log (W_b / C_b) + Real.log w_c := by
    have hrew : 8 * c * u_c * ((W_b / C_b) * 8 * c * w_c) =
        64 * (c * c) * u_c * (W_b / C_b) * w_c := by ring
    rw [hrew, Real.log_mul (by positivity) hw_pos.ne',
      Real.log_mul (by positivity) hWC_pos.ne',
      Real.log_mul (by positivity) hu_pos.ne',
      Real.log_mul (by norm_num) (by positivity),
      Real.log_mul hc_pos.ne' hc_pos.ne']
    ring
  rw [hprod_log]
  nlinarith

set_option maxHeartbeats 800000 in
private lemma eventually_pade_params (r : ℕ) (hr : 2 ≤ r) :
    let Y := fun n : ℕ => (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))
    ∀ᶠ N : ℕ in atTop,
      let M := ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊
      let L := ⌊(N : ℝ) / Real.log (N : ℝ)⌋₊
      let K_max := ⌈(M : ℝ) ^ 3 * Real.log (N : ℝ)⌉₊
      let c := (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1))
      let u_c := (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (64 : ℝ) ^ M
      let w_c := 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (16 : ℝ) ^ M
      let C_b := 2 * (N : ℝ)
      let U_b := (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (493 / 84 : ℝ)
      let W_b := (N : ℝ) ^ (29 / 12 : ℝ) / (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (58 / 7 : ℝ)
      10 ≤ N ∧ 1 ≤ M ∧ 8 * M ≤ N ∧ 1 ≤ L ∧ L ≤ N ∧
      2 ≤ Real.log (N : ℝ) ∧
      ((N / L + 1 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) ∧
      C_b * U_b ≤ (N : ℝ) ^ (10048 / 8568 : ℝ) ∧
      (N : ℝ) ^ (10049 / 8568 : ℝ) ≤ W_b / C_b ∧
      W_b / C_b ≤ (N : ℝ) ^ (3 : ℕ) ∧
      (1 : ℝ) ≤ W_b / C_b ∧
      -- Log bounds for D and error terms:
      Real.log (8 * c * w_c) + Real.log (r : ℝ) + (2 * (N : ℝ) / (r : ℝ)) * Real.log (2 * (N : ℝ)) ≤
        3 * (N : ℝ) * Real.log (N : ℝ) ∧
      (3 * (M : ℝ) + 20) * (3 * Real.log (N : ℝ)) ≤ (N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ) ∧
      10 * (3 * Real.log (N : ℝ)) ≤ (N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ) ∧
      (2 * (N : ℝ) / (r : ℝ)) ≤ (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ)) ∧
      Real.log (8 * c * u_c * ((W_b / C_b) * 8 * c * w_c)) ≤
        (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ)) := by
  intro Y
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  -- Helper: N^α ≥ B eventually for α > 0
  have hEv1 : ∀ᶠ N : ℕ in atTop, (100 : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ) :=
    eventually_rpow_gt_const 100 (1 / 34) (by norm_num)
  have hEv2 : ∀ᶠ N : ℕ in atTop, (2 * (4 * (r : ℝ) ^ 4) ^ (493 / 84 : ℝ)) ≤ (N : ℝ) ^ (1 / 8568 : ℝ) :=
    eventually_rpow_gt_const _ (1 / 8568) (by norm_num)
  have hEv3 : ∀ᶠ N : ℕ in atTop, (2 * (4 * (r : ℝ) ^ 4) ^ (58 / 7 : ℝ)) ≤ (N : ℝ) ^ (1 / 8568 : ℝ) :=
    eventually_rpow_gt_const _ (1 / 8568) (by norm_num)
  have hEv4 : ∀ᶠ N : ℕ in atTop, (1000000 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1000000)
  have hEv5 : ∀ᶠ N : ℕ in atTop, (1000 * (r : ℝ) + 1000000) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    eventually_rpow_gt_const _ (1 / 2) (by norm_num)
  -- Polynomial growth bound for log(8 * c * u_c * (W_b / C_b) * 8 * c * w_c) ≤ C_r * N^(1/4)
  -- and C_r * N^(1/4) ≤ (1 / 100000) * (N / (4 * r)) eventually!
  let Cr : ℝ := 10000000 * (Real.log (4 * (r : ℝ)) + 200)
  have hEv6 : ∀ᶠ N : ℕ in atTop, (400000 * (r : ℝ) * (Cr + 10)) ≤ (N : ℝ) ^ (3 / 4 : ℝ) :=
    eventually_rpow_gt_const _ (3 / 4) (by norm_num)
  have hEv7 : ∀ᶠ N : ℕ in atTop, (Real.log (r : ℝ) + 1000) ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [eventually_ge_atTop 10000, hEv1, hEv2, hEv3, hEv4, hEv5, hEv6, hEv7]
    with N hN10k h1 h2 h3 h4 h5 h6 h7
  dsimp only
  set M := ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊
  set L := ⌊(N : ℝ) / Real.log (N : ℝ)⌋₊
  set K_max := ⌈(M : ℝ) ^ 3 * Real.log (N : ℝ)⌉₊
  set c := (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1))
  set u_c := (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (64 : ℝ) ^ M
  set w_c := 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (16 : ℝ) ^ M
  set C_b := 2 * (N : ℝ)
  set U_b := (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (493 / 84 : ℝ)
  set W_b := (N : ℝ) ^ (29 / 12 : ℝ) / (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (58 / 7 : ℝ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlog_ge2 : 2 ≤ Real.log (N : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (N : ℝ) := by linarith
  have hM_le : (M : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ) := Nat.floor_le (by positivity)
  have hM_ge1 : 1 ≤ M := Nat.one_le_floor_iff _ |>.mpr (by linarith)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_ge1
  have hN134_le : (N : ℝ) ^ (1 / 34 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
  have h8M_le_N : 8 * M ≤ N := by
    have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hN_pos]; norm_num
    have hR : 8 * (M : ℝ) ≤ (N : ℝ) := by nlinarith
    exact_mod_cast hR
  have hlog_le_100 : Real.log (N : ℝ) ≤ 100 * (N : ℝ) ^ (1 / 100 : ℝ) := log_le_100_rpow _ hN_pos.le
  have hNdivlog_ge : (10 : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) := by
    rw [le_div_iff₀ hlog_pos]
    have h100_le : (N : ℝ) ^ (1 / 100 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
    have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hN_pos]; norm_num
    nlinarith
  have hL_ge1 : 1 ≤ L := Nat.one_le_floor_iff _ |>.mpr (by linarith)
  have hL_le : (L : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) := Nat.floor_le (by positivity)
  have hL_le_N : L ≤ N := by
    have hR : (L : ℝ) ≤ (N : ℝ) := hL_le.trans (div_le_self hN_pos.le (by linarith))
    exact_mod_cast hR
  have hL_ge_half : (N : ℝ) / (2 * Real.log (N : ℝ)) ≤ (L : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((N : ℝ) / Real.log (N : ℝ))
    have hhalf : (N : ℝ) / (2 * Real.log (N : ℝ)) = ((N : ℝ) / Real.log (N : ℝ)) / 2 := by ring
    linarith
  have hNdivL : ((N / L + 1 : ℕ) : ℝ) ≤ 3 * Real.log (N : ℝ) := by
    push_cast
    have hdiv_le : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / (L : ℝ) := by
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_ge1
      rw [le_div_iff₀ hLpos]
      exact_mod_cast Nat.div_mul_le_self N L
    have hNL : (N : ℝ) / (L : ℝ) ≤ 2 * Real.log (N : ℝ) := by
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_ge1
      rw [div_le_iff₀ hLpos]
      have h1 := mul_le_mul_of_nonneg_left hL_ge_half (show 0 ≤ 2 * Real.log (N : ℝ) by positivity)
      have h2 : 2 * Real.log (N : ℝ) * ((N : ℝ) / (2 * Real.log (N : ℝ))) = (N : ℝ) := by
        field_simp [hlog_pos.ne']
      linarith
    linarith
  -- Bounds on C_b * U_b and W_b / C_b:
  have hCU : C_b * U_b ≤ (N : ℝ) ^ (10048 / 8568 : ℝ) := by
    dsimp [C_b, U_b]
    rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg M)]
    have hMpow : (M : ℝ) ^ (493 / 84 : ℝ) ≤ (N : ℝ) ^ (493 / 2856 : ℝ) := by
      calc (M : ℝ) ^ (493 / 84 : ℝ)
          ≤ ((N : ℝ) ^ (1 / 34 : ℝ)) ^ (493 / 84 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg M) hM_le (by norm_num)
        _ = (N : ℝ) ^ (493 / 2856 : ℝ) := by rw [← Real.rpow_mul hN_pos.le]; norm_num
    calc 2 * (N : ℝ) * ((4 * (r : ℝ) ^ 4) ^ (493 / 84 : ℝ) * (M : ℝ) ^ (493 / 84 : ℝ))
        = (2 * (4 * (r : ℝ) ^ 4) ^ (493 / 84 : ℝ)) * ((N : ℝ) * (M : ℝ) ^ (493 / 84 : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ (1 / 8568 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (493 / 2856 : ℝ)) := by
          have p1 := mul_le_mul_of_nonneg_left hMpow hN_pos.le
          exact mul_le_mul h2 p1 (by positivity) (by positivity)
      _ = (N : ℝ) ^ (10048 / 8568 : ℝ) := rpow_prod_CU hN_pos
  have hWC : (N : ℝ) ^ (10049 / 8568 : ℝ) ≤ W_b / C_b := by
    dsimp [W_b, C_b]
    rw [div_div, Real.mul_rpow (by positivity) (Nat.cast_nonneg M)]
    have hMpow : (M : ℝ) ^ (58 / 7 : ℝ) ≤ (N : ℝ) ^ (58 / 238 : ℝ) := by
      calc (M : ℝ) ^ (58 / 7 : ℝ)
          ≤ ((N : ℝ) ^ (1 / 34 : ℝ)) ^ (58 / 7 : ℝ) :=
            Real.rpow_le_rpow (Nat.cast_nonneg M) hM_le (by norm_num)
        _ = (N : ℝ) ^ (58 / 238 : ℝ) := by rw [← Real.rpow_mul hN_pos.le]; norm_num
    have hden_pos : 0 < (4 * (r : ℝ) ^ 4) ^ (58 / 7 : ℝ) * (M : ℝ) ^ (58 / 7 : ℝ) * (2 * (N : ℝ)) := by
      positivity
    rw [le_div_iff₀ hden_pos]
    have hden_le : (4 * (r : ℝ) ^ 4) ^ (58 / 7 : ℝ) * (M : ℝ) ^ (58 / 7 : ℝ) * (2 * (N : ℝ)) ≤
        (N : ℝ) ^ (1 / 8568 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (58 / 238 : ℝ)) := by
      have p1 := mul_le_mul_of_nonneg_left hMpow hN_pos.le
      calc (4 * (r : ℝ) ^ 4) ^ (58 / 7 : ℝ) * (M : ℝ) ^ (58 / 7 : ℝ) * (2 * (N : ℝ))
          = (2 * (4 * (r : ℝ) ^ 4) ^ (58 / 7 : ℝ)) * ((N : ℝ) * (M : ℝ) ^ (58 / 7 : ℝ)) := by ring
        _ ≤ (N : ℝ) ^ (1 / 8568 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (58 / 238 : ℝ)) :=
            mul_le_mul h3 p1 (by positivity) (by positivity)
    calc (N : ℝ) ^ (10049 / 8568 : ℝ) * ((4 * (r : ℝ) ^ 4) ^ (58 / 7 : ℝ) * (M : ℝ) ^ (58 / 7 : ℝ) * (2 * (N : ℝ)))
        ≤ (N : ℝ) ^ (10049 / 8568 : ℝ) * ((N : ℝ) ^ (1 / 8568 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (58 / 238 : ℝ))) :=
          mul_le_mul_of_nonneg_left hden_le (by positivity)
      _ = (N : ℝ) ^ (29 / 12 : ℝ) := rpow_prod_WC hN_pos
  have hWC_le_N3 : W_b / C_b ≤ (N : ℝ) ^ (3 : ℕ) := by
    dsimp [W_b, C_b]
    have hden1 : (1 : ℝ) ≤ (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (58 / 7 : ℝ) := by
      refine Real.one_le_rpow ?_ (by norm_num)
      have : (1 : ℝ) ≤ (r : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ r by omega))
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge1
      nlinarith
    have hWle : (N : ℝ) ^ (29 / 12 : ℝ) / (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (58 / 7 : ℝ) ≤ (N : ℝ) ^ (29 / 12 : ℝ) :=
      div_le_self (by positivity) hden1
    calc (N : ℝ) ^ (29 / 12 : ℝ) / (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (58 / 7 : ℝ) / (2 * (N : ℝ))
        ≤ (N : ℝ) ^ (29 / 12 : ℝ) / 1 := by
          refine div_le_div₀ (by positivity) hWle (by norm_num) (by linarith)
      _ = (N : ℝ) ^ (29 / 12 : ℝ) := div_one _
      _ ≤ (N : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN_ge1 (by norm_num)
      _ = (N : ℝ) ^ (3 : ℕ) := Real.rpow_natCast _ 3
  have hWC_ge1 : (1 : ℝ) ≤ W_b / C_b := by
    calc (1 : ℝ) ≤ (N : ℝ) ^ (10049 / 8568 : ℝ) := Real.one_le_rpow hN_ge1 (by norm_num)
      _ ≤ W_b / C_b := hWC
  have hbig_log : Real.log (8 * c * u_c * ((W_b / C_b) * 8 * c * w_c)) ≤ Cr * (N : ℝ) ^ (1 / 4 : ℝ) :=
    pade_big_log_bound hr hN10k hM_le rfl hWC_ge1 hWC_le_N3
  -- Deduce the final 5 inequalities from hbig_log and h4, h5, h6, h7:
  have hCrN14_le : Cr * (N : ℝ) ^ (1 / 4 : ℝ) ≤ (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ)) := by
    have hN_split : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hN_pos]; norm_num
    have h1 : 400000 * (r : ℝ) * Cr * (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) := by
      have hCr0 : 0 ≤ Cr := by
        dsimp [Cr]
        have : 0 ≤ Real.log (4 * (r : ℝ)) := Real.log_nonneg (by
          have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
          linarith)
        linarith
      have h6' : 400000 * (r : ℝ) * Cr ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by nlinarith
      calc 400000 * (r : ℝ) * Cr * (N : ℝ) ^ (1 / 4 : ℝ)
          ≤ (N : ℝ) ^ (3 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right h6' (by positivity)
        _ = (N : ℝ) := by rw [mul_comm, hN_split]
    have h2 : Cr * (N : ℝ) ^ (1 / 4 : ℝ) ≤ (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ))) := by
      have hden : (0 : ℝ) < 400000 * (r : ℝ) := by positivity
      have h3 : Cr * (N : ℝ) ^ (1 / 4 : ℝ) ≤ (N : ℝ) / (400000 * (r : ℝ)) :=
        (le_div_iff₀ hden).mpr (by linarith)
      have hring : (N : ℝ) / (400000 * (r : ℝ)) = (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ))) := by ring
      linarith
    nlinarith [show 0 ≤ (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ))) by positivity]
  have hlog8cw : Real.log (8 * c * w_c) ≤ Real.log (8 * c * u_c * ((W_b / C_b) * 8 * c * w_c)) := by
    have hc1 : 1 ≤ c := one_le_pow₀ (by
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
      nlinarith)
    have hu1 : 1 ≤ u_c := by
      dsimp [u_c]
      have p1 : (1 : ℝ) ≤ (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) := one_le_pow₀ (by
        have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
        nlinarith)
      have p2 : (1 : ℝ) ≤ (64 : ℝ) ^ M := one_le_pow₀ (by norm_num)
      nlinarith
    have hw1 : 1 ≤ w_c := by
      dsimp [w_c]
      have p1 : (1 : ℝ) ≤ (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) := one_le_pow₀ (by
        have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
        nlinarith)
      have p2 : (1 : ℝ) ≤ (16 : ℝ) ^ M := one_le_pow₀ (by norm_num)
      nlinarith
    refine Real.log_le_log (by positivity) ?_
    have hprod1 : 1 ≤ 8 * c * u_c * (W_b / C_b) := by
      have p1 : 1 ≤ 8 * c := by linarith
      have p2 : 1 ≤ 8 * c * u_c := one_le_mul_of_one_le_of_one_le p1 hu1
      exact one_le_mul_of_one_le_of_one_le p2 hWC_ge1
    have h8cw_nn : 0 ≤ 8 * c * w_c := by positivity
    have hrew : 8 * c * u_c * ((W_b / C_b) * 8 * c * w_c) = (8 * c * u_c * (W_b / C_b)) * (8 * c * w_c) := by ring
    rw [hrew]
    calc 8 * c * w_c = 1 * (8 * c * w_c) := (one_mul _).symm
      _ ≤ (8 * c * u_c * (W_b / C_b)) * (8 * c * w_c) := mul_le_mul_of_nonneg_right hprod1 h8cw_nn
  have hlog2N : Real.log (2 * (N : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num) hN_pos.ne']
    have hl2 : Real.log 2 ≤ 1 := by
      calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
        _ = 1 := Real.log_exp 1
    linarith
  refine ⟨by omega, hM_ge1, h8M_le_N, hL_ge1, hL_le_N, hlog_ge2, hNdivL, hCU, hWC, hWC_le_N3, hWC_ge1, ?_, ?_, ?_, ?_, ?_⟩
  · -- log(8*c*w_c) + log r + (2*N/r) * log(2*N) ≤ 3 * N * log N
    have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2Nr : 2 * (N : ℝ) / (r : ℝ) ≤ (N : ℝ) := by
      rw [div_le_iff₀ hr_pos]; nlinarith
    have hterm3 : 2 * (N : ℝ) / (r : ℝ) * Real.log (2 * (N : ℝ)) ≤ 2 * (N : ℝ) * Real.log (N : ℝ) := by
      have h1 := mul_le_mul h2Nr hlog2N (Real.log_nonneg (by linarith)) hN_pos.le
      linarith
    have hterm1 : Real.log (8 * c * w_c) ≤ (1 / 2 : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by
      have hle := hlog8cw.trans (hbig_log.trans hCrN14_le)
      have : (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ)) ≤
          (1 / 2 : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by
        have : (N : ℝ) / (4 * (r : ℝ)) ≤ (N : ℝ) := div_le_self hN_pos.le (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right this hlog_pos.le]
      linarith
    have hterm2 : Real.log (r : ℝ) ≤ (1 / 2 : ℝ) * (N : ℝ) * Real.log (N : ℝ) := by
      nlinarith
    linarith
  · -- (3*M + 20) * (3 * log N) ≤ (N / (4*r)) * log N
    have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hN_pos]; norm_num
    have h1 : 12 * (r : ℝ) * (3 * (M : ℝ) + 20) ≤ (N : ℝ) := by
      have hM_le_h : (M : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := hM_le.trans hN134_le
      nlinarith
    have h2 : 3 * (3 * (M : ℝ) + 20) ≤ (N : ℝ) / (4 * (r : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (r : ℝ))]; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hlog_pos.le
    linarith
  · -- 10 * (3 * log N) ≤ (N / (4*r)) * log N
    have hsq : (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hN_pos]; norm_num
    have h1 : 120 * (r : ℝ) ≤ (N : ℝ) := by nlinarith
    have h2 : (30 : ℝ) ≤ (N : ℝ) / (4 * (r : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (r : ℝ))]; linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hlog_pos.le
    linarith
  · -- 2*N/r ≤ (1/100000) * (N / (4*r) * log N)
    have h0 : 0 ≤ (N : ℝ) / (4 * (r : ℝ)) := by positivity
    have h1 : (8 : ℝ) ≤ (1 / 100000 : ℝ) * Real.log (N : ℝ) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 h0
    have hring1 : (N : ℝ) / (4 * (r : ℝ)) * 8 = 2 * (N : ℝ) / (r : ℝ) := by ring
    have hring2 : (N : ℝ) / (4 * (r : ℝ)) * ((1 / 100000 : ℝ) * Real.log (N : ℝ)) =
        (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ)) := by ring
    rw [hring1, hring2] at h2
    exact h2
  · exact hbig_log.trans hCrN14_le


private lemma Y_block_ratio_le {r N L N₀ N₁ n : ℕ} (hr : 2 ≤ r) (hN : 10 ≤ N)
    (hL : (L : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ))
    (hlog : 2 ≤ Real.log (N : ℝ))
    (hN0 : N ≤ N₀) (hNn : N₀ ≤ n) (hnN1 : n ≤ N₁) (hN1_2N : N₁ ≤ 2 * N) (hdiff : N₁ - N₀ ≤ L)
    (h2Nr : 2 * (N : ℝ) / (r : ℝ) ≤ (1 / 100000 : ℝ) * ((N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ))) :
    (r : ℝ) * (N₁.factorial : ℝ) ^ (1 / (r : ℝ)) ≤
      ((r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))) ^ (1 + 1 / 100000 : ℝ) := by
  set Y := fun m : ℕ => (r : ℝ) * (m.factorial : ℝ) ^ (1 / (r : ℝ))
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hYn_pos : 0 < Y n := by dsimp [Y]; positivity
  have hYN1_pos : 0 < Y N₁ := by dsimp [Y]; positivity
  rw [← Real.log_le_log_iff hYN1_pos (Real.rpow_pos_of_pos hYn_pos _), Real.log_rpow hYn_pos]
  -- Bound log(Y N₁) - log(Y n) = (1/r) * log(N₁! / n!) ≤ (L / r) * log(2 * N) ≤ 2 * N / r
  have hfac_div : (N₁.factorial : ℝ) ≤ (n.factorial : ℝ) * (2 * (N : ℝ)) ^ L := by
    have hnat : N₁.factorial ≤ n.factorial * (2 * N) ^ (N₁ - n) := by
      have h1 : N₁ = n + (N₁ - n) := by omega
      have hrec : ∀ d : ℕ, (n + d).factorial ≤ n.factorial * (n + d) ^ d := by
        intro d
        induction d with
        | zero => simp
        | succ d ih =>
          rw [← Nat.add_assoc, Nat.factorial_succ, pow_succ]
          have hpow : (n + d) ^ d ≤ (n + d + 1) ^ d := Nat.pow_le_pow_left (by omega) d
          calc (n + d + 1) * (n + d).factorial
              ≤ (n + d + 1) * (n.factorial * (n + d) ^ d) := Nat.mul_le_mul_left _ ih
            _ ≤ (n + d + 1) * (n.factorial * (n + d + 1) ^ d) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hpow)
            _ = n.factorial * ((n + d + 1) ^ d * (n + d + 1)) := by ring
      have h2 := hrec (N₁ - n)
      rw [← h1] at h2
      exact h2.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN1_2N _))
    have hpowL : (2 * N) ^ (N₁ - n) ≤ (2 * N) ^ L :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast hnat.trans (Nat.mul_le_mul_left _ hpowL)
  have hYN1_le : Y N₁ ≤ Y n * ((2 * (N : ℝ)) ^ L) ^ (1 / (r : ℝ)) := by
    dsimp [Y]
    have h1 := Real.rpow_le_rpow (Nat.cast_nonneg _) hfac_div (by positivity : (0 : ℝ) ≤ 1 / (r : ℝ))
    rw [Real.mul_rpow (Nat.cast_nonneg _) (by positivity)] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 hr_pos.le
    linarith
  have hlog_diff : Real.log (Y N₁) ≤ Real.log (Y n) + (L : ℝ) / (r : ℝ) * Real.log (2 * (N : ℝ)) := by
    have h1 := Real.log_le_log hYN1_pos hYN1_le
    rw [Real.log_mul hYn_pos.ne' (by positivity), Real.log_rpow (by positivity), Real.log_pow] at h1
    have hring : 1 / (r : ℝ) * ((L : ℝ) * Real.log (2 * (N : ℝ))) = (L : ℝ) / (r : ℝ) * Real.log (2 * (N : ℝ)) := by
      ring
    linarith
  have hlog2N : Real.log (2 * (N : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num) hN_pos.ne']
    have hl2 : Real.log 2 ≤ 1 := by
      calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])
        _ = 1 := Real.log_exp 1
    linarith
  have hLr : (L : ℝ) / (r : ℝ) * Real.log (2 * (N : ℝ)) ≤ 2 * (N : ℝ) / (r : ℝ) := by
    have h1 : (L : ℝ) / (r : ℝ) ≤ (N : ℝ) / Real.log (N : ℝ) / (r : ℝ) :=
      div_le_div_of_nonneg_right hL hr_pos.le
    have h2 := mul_le_mul h1 hlog2N (Real.log_nonneg (by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
      linarith)) (by positivity)
    have hlog_ne : Real.log (N : ℝ) ≠ 0 := by linarith
    have hring : (N : ℝ) / Real.log (N : ℝ) / (r : ℝ) * (2 * Real.log (N : ℝ)) = 2 * (N : ℝ) / (r : ℝ) := by
      field_simp [hlog_ne, hr_pos.ne']
    linarith
  have hlogYn : (N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ) ≤ Real.log (Y n) := by
    have h1 : Y N ≤ Y n := by
      dsimp [Y]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le (by omega)) (by positivity))
        hr_pos.le
    exact (log_Y_lower (by omega : 1 ≤ r) hN).trans (Real.log_le_log (by positivity) h1)
  linarith

private lemma pade_entry_bound {N c u_c w_c C_b U_b W_b Y_n Y_N1 a : ℝ} {D : ℕ}
    (hN : 0 < N) (hc : 1 ≤ c) (hu : 1 ≤ u_c) (hw : 1 ≤ w_c)
    (hCb : 0 < C_b) (hUb : 0 ≤ U_b) (hWC1 : 1 ≤ W_b / C_b)
    (hYn : 1 ≤ Y_n) (hYN1 : 0 < Y_N1)
    (h8a : 8 * |a| ≤ 8 * c * u_c * (C_b * U_b) ^ D)
    (hCU : C_b * U_b ≤ N ^ (10048 / 8568 : ℝ))
    (hWC : N ^ (10049 / 8568 : ℝ) ≤ W_b / C_b)
    (hWC_D_le : (W_b / C_b) ^ D ≤ (W_b / C_b) * (8 * c * w_c * Y_N1))
    (hbig : 8 * c * u_c * ((W_b / C_b) * 8 * c * w_c) ≤ Y_n ^ (1 / 100000 : ℝ))
    (hYN1_le : Y_N1 ≤ Y_n ^ (1 + 1 / 100000 : ℝ)) :
    |a| ≤ Y_n ^ (1 - 1 / 20000 : ℝ) / 8 := by
  have hYn_pos : 0 < Y_n := by linarith
  have hWC_nn : 0 ≤ W_b / C_b := by linarith
  have hCUD : (C_b * U_b) ^ D ≤ ((W_b / C_b) ^ D) ^ (10048 / 10049 : ℝ) := by
    have h1 : (C_b * U_b) ^ D ≤ (N ^ (10048 / 8568 : ℝ)) ^ D :=
      pow_le_pow_left₀ (by positivity) hCU D
    have h2 : (N ^ (10048 / 8568 : ℝ)) ^ D =
        ((N ^ (10049 / 8568 : ℝ)) ^ D) ^ (10048 / 10049 : ℝ) := by
      rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_mul_natCast hN.le, ← Real.rpow_mul hN.le]
      congr 1; ring
    have h3 : ((N ^ (10049 / 8568 : ℝ)) ^ D) ^ (10048 / 10049 : ℝ) ≤
        ((W_b / C_b) ^ D) ^ (10048 / 10049 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ (by positivity) hWC D) (by norm_num)
    exact h1.trans (h2 ▸ h3)
  have hWCD_rpow : ((W_b / C_b) ^ D) ^ (10048 / 10049 : ℝ) ≤
      ((W_b / C_b) * 8 * c * w_c) * Y_N1 ^ (10048 / 10049 : ℝ) := by
    have h1 : ((W_b / C_b) ^ D) ^ (10048 / 10049 : ℝ) ≤
        (((W_b / C_b) * 8 * c * w_c) * Y_N1) ^ (10048 / 10049 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by positivity) hYN1.le] at h1
    have hge1 : (1 : ℝ) ≤ (W_b / C_b) * 8 * c * w_c := by
      have p1 : (1 : ℝ) ≤ (W_b / C_b) * 8 := by linarith
      have p2 : (1 : ℝ) ≤ (W_b / C_b) * 8 * c := one_le_mul_of_one_le_of_one_le p1 hc
      exact one_le_mul_of_one_le_of_one_le p2 hw
    have hdrop : ((W_b / C_b) * 8 * c * w_c) ^ (10048 / 10049 : ℝ) ≤ (W_b / C_b) * 8 * c * w_c := by
      calc ((W_b / C_b) * 8 * c * w_c) ^ (10048 / 10049 : ℝ)
          ≤ ((W_b / C_b) * 8 * c * w_c) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hge1 (by norm_num)
        _ = (W_b / C_b) * 8 * c * w_c := Real.rpow_one _
    exact h1.trans (mul_le_mul_of_nonneg_right hdrop (by positivity))
  have hYN1_rpow : Y_N1 ^ (10048 / 10049 : ℝ) ≤ Y_n ^ ((1 + 1 / 100000 : ℝ) * (10048 / 10049 : ℝ)) := by
    rw [Real.rpow_mul hYn_pos.le]
    exact Real.rpow_le_rpow hYN1.le hYN1_le (by norm_num)
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  calc |a| * 8 = 8 * |a| := mul_comm _ _
    _ ≤ 8 * c * u_c * (C_b * U_b) ^ D := h8a
    _ ≤ 8 * c * u_c * ((W_b / C_b) ^ D) ^ (10048 / 10049 : ℝ) :=
        mul_le_mul_of_nonneg_left hCUD (by positivity)
    _ ≤ 8 * c * u_c * (((W_b / C_b) * 8 * c * w_c) * Y_N1 ^ (10048 / 10049 : ℝ)) :=
        mul_le_mul_of_nonneg_left hWCD_rpow (by positivity)
    _ = (8 * c * u_c * ((W_b / C_b) * 8 * c * w_c)) * Y_N1 ^ (10048 / 10049 : ℝ) := by ring
    _ ≤ Y_n ^ (1 / 100000 : ℝ) * Y_n ^ ((1 + 1 / 100000 : ℝ) * (10048 / 10049 : ℝ)) :=
        mul_le_mul hbig hYN1_rpow (by positivity) (by positivity)
    _ = Y_n ^ (1 / 100000 + (1 + 1 / 100000) * (10048 / 10049) : ℝ) :=
        (Real.rpow_add hYn_pos _ _).symm
    _ ≤ Y_n ^ (1 - 1 / 20000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYn (by norm_num)

private lemma pade_linform_bound {r M N Z coef c w_c C_b U_b W_b Y_n Y_N1 S : ℝ} {D : ℕ}
    (hr1 : 1 ≤ r) (hM : 0 < M) (hN : 0 < N) (h4MN : 4 * M ≤ N)
    (hc : 1 ≤ c) (hw : 1 ≤ w_c) (hCb : 0 < C_b) (hUb : 0 ≤ U_b)
    (hYn_pos : 0 < Y_n) (hYn_le : Y_n ≤ Y_N1) (hcoef_nn : 0 ≤ coef)
    (hUb_eq : U_b = (4 * r ^ 4 * M) ^ (493 / 84 : ℝ))
    (hWb_eq : W_b = N ^ (29 / 12 : ℝ) / (4 * r ^ 4 * M) ^ (58 / 7 : ℝ))
    (hZ_le : Z ≤ c * C_b ^ D)
    (hWC_D_ge : 8 * c * w_c * Y_N1 ≤ (W_b / C_b) ^ D)
    (hcoef_le : coef ≤ w_c)
    (hRlin : |S| ≤ coef * U_b ^ D * (4 * M / N) ^ ((29 * D) / 12 + 1)) :
    Z * |S| ≤ 1 / (8 * Y_n) := by
  have hYN1_pos : 0 < Y_N1 := lt_of_lt_of_le hYn_pos hYn_le
  have h4MN_le1 : 4 * M / N ≤ 1 := (div_le_one hN).mpr h4MN
  have h4MN_pos : 0 < 4 * M / N := by positivity
  have hO_ge : (29 / 12 : ℝ) * (D : ℝ) ≤ (((29 * D) / 12 + 1 : ℕ) : ℝ) := by
    have hnat : 29 * D < 12 * ((29 * D) / 12 + 1) := by omega
    have hR : (29 : ℝ) * (D : ℝ) < 12 * (((29 * D) / 12 + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have h4MN_pow : (4 * M / N) ^ ((29 * D) / 12 + 1) ≤ (4 * M / N) ^ ((29 / 12 : ℝ) * (D : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge h4MN_pos h4MN_le1 hO_ge
  have hUW : U_b ^ D * (4 * M / N) ^ ((29 / 12 : ℝ) * (D : ℝ)) ≤ (W_b ^ D)⁻¹ := by
    have hbase : U_b * (4 * M / N) ^ (29 / 12 : ℝ) ≤ W_b⁻¹ := by
      rw [hUb_eq, hWb_eq, inv_div, Real.div_rpow (by positivity) hN.le, ← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have hr4 : 4 * M ≤ 4 * r ^ 4 * M := by
        have : (1 : ℝ) ≤ r ^ 4 := one_le_pow₀ hr1
        nlinarith
      have h1 := Real.rpow_le_rpow (by positivity) hr4 (by norm_num : (0 : ℝ) ≤ 29 / 12)
      calc (4 * r ^ 4 * M) ^ (493 / 84 : ℝ) * (4 * M) ^ (29 / 12 : ℝ)
          ≤ (4 * r ^ 4 * M) ^ (493 / 84 : ℝ) * (4 * r ^ 4 * M) ^ (29 / 12 : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (4 * r ^ 4 * M) ^ (58 / 7 : ℝ) := by
            rw [← Real.rpow_add (by positivity)]; norm_num
    have hpow := pow_le_pow_left₀ (by positivity) hbase D
    rw [mul_pow, ← Real.rpow_mul_natCast h4MN_pos.le, inv_pow] at hpow
    exact hpow
  calc Z * |S|
      ≤ (c * C_b ^ D) * (coef * U_b ^ D * (4 * M / N) ^ ((29 * D) / 12 + 1)) :=
        mul_le_mul hZ_le hRlin (abs_nonneg _) (by positivity)
    _ ≤ (c * C_b ^ D) * (w_c * (W_b ^ D)⁻¹) := by
        have h1 := mul_le_mul_of_nonneg_left h4MN_pow (show 0 ≤ U_b ^ D by positivity)
        have h2 := h1.trans hUW
        have h3 := mul_le_mul hcoef_le h2 (by positivity) (by positivity)
        rw [mul_assoc coef]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (c * w_c) / (W_b / C_b) ^ D := by
        rw [div_pow, div_div_eq_mul_div, inv_eq_one_div]; ring
    _ ≤ (c * w_c) / (8 * c * w_c * Y_N1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hWC_D_ge
    _ = 1 / (8 * Y_N1) := by
        have hcw_ne : c * w_c ≠ 0 := by positivity
        field_simp [hcw_ne, hYN1_pos.ne']
    _ ≤ 1 / (8 * Y_n) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

open scoped Classical in
set_option maxHeartbeats 800000 in
private lemma pade_exceptional_bound (r : ℕ) (hr : 2 ≤ r) :
    let Y := fun n : ℕ => (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))
    ∀ᶠ N : ℕ in atTop,
      let M := ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊
      ∀ u v : ℕ, 0 < u → u < v → v ≤ M → r ∣ u → r ∣ v →
        let cert := fun n : ℕ => ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det ≠ 0 ∧
          (∀ i j, |(A i j : ℝ)| ≤ (Y n) ^ (1 - 1 / 20000 : ℝ) / 8) ∧
          ∀ i, |(A i 0 : ℝ) + (A i 1 : ℝ) * omegaVal r u (1 / (n : ℝ)) +
                (A i 2 : ℝ) * omegaVal r v (1 / (n : ℝ))| ≤ 1 / (8 * Y n)
        (((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card : ℝ) ≤
          100 * (N : ℝ) / (M : ℝ) ^ 3 := by
  intro Y
  filter_upwards [eventually_pade_params r hr] with N hpar
  obtain ⟨hN10, hM1, h8MN, hL1, hLN, hlog2, hNdivL, hCU, hWC, hWC_N3, hWC1,
    hD_up, hD_lowM, hD_low10, h2Nr, hbig_log⟩ := hpar
  dsimp only
  set M := ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊
  set L := ⌊(N : ℝ) / Real.log (N : ℝ)⌋₊
  set K_max := ⌈(M : ℝ) ^ 3 * Real.log (N : ℝ)⌉₊
  set c := (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1))
  set u_c := (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (64 : ℝ) ^ M
  set w_c := 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (16 : ℝ) ^ M
  set C_b := 2 * (N : ℝ)
  set U_b := (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (493 / 84 : ℝ)
  set W_b := (N : ℝ) ^ (29 / 12 : ℝ) / (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ (58 / 7 : ℝ)
  intro u v hu huv hvM hru hrv
  let cert : ℕ → Prop := fun n => ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det ≠ 0 ∧
    (∀ i j, |(A i j : ℝ)| ≤ (Y n) ^ (1 - 1 / 20000 : ℝ) / 8) ∧
    ∀ i, |(A i 0 : ℝ) + (A i 1 : ℝ) * omegaVal r u (1 / (n : ℝ)) +
          (A i 2 : ℝ) * omegaVal r v (1 / (n : ℝ))| ≤ 1 / (8 * Y n)
  change (((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card : ℝ) ≤
    100 * (N : ℝ) / (M : ℝ) ^ 3
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hlog_pos : 0 < Real.log (N : ℝ) := by linarith only [hlog2]
  have hu2 : 2 ≤ u := by
    obtain ⟨q, hq⟩ := hru
    have hq1 : 1 ≤ q := by nlinarith only [hu, hq]
    nlinarith only [hr, hq, hq1]
  have hlogWC_ge : Real.log (N : ℝ) ≤ Real.log (W_b / C_b) := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hN_pos _) hWC
    rw [Real.log_rpow hN_pos] at h1
    nlinarith only [h1, hlog_pos]
  have hlogWC_pos : 0 < Real.log (W_b / C_b) := by linarith only [hlog_pos, hlogWC_ge]
  have hlogWC_le : Real.log (W_b / C_b) ≤ 3 * Real.log (N : ℝ) := by
    have h1 := Real.log_le_log (by linarith only [hWC1]) hWC_N3
    rw [Real.log_pow] at h1; push_cast at h1; linarith only [h1]
  have hr_ge1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hc_ge1 : 1 ≤ c := one_le_pow₀ (by nlinarith only [hr_ge1, hN_ge1])
  have hu_ge1 : 1 ≤ u_c := by
    dsimp [u_c]
    have p1 : (1 : ℝ) ≤ (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) := one_le_pow₀ (by nlinarith only [hr_ge1, hN_ge1])
    have p2 : (1 : ℝ) ≤ (64 : ℝ) ^ M := one_le_pow₀ (by norm_num)
    nlinarith only [p1, p2]
  have hw_ge1 : 1 ≤ w_c := by
    dsimp [w_c]
    have p1 : (1 : ℝ) ≤ (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) := one_le_pow₀ (by nlinarith only [hr_ge1, hN_ge1])
    have p2 : (1 : ℝ) ≤ (16 : ℝ) ^ M := one_le_pow₀ (by norm_num)
    nlinarith only [p1, p2]
  -- Per-block bound: for each t < N / L + 1, at most 16 * N / (M^3 * log N) failures in block t
  let block : ℕ → Finset ℕ := fun t => Finset.Ico (N + t * L) (min (N + (t + 1) * L) (2 * N))
  have hcover : (Finset.Ico N (2 * N)).filter (fun n => ¬ cert n) ⊆
      (Finset.range (N / L + 1)).biUnion (fun t => (block t).filter (fun n => ¬ cert n)) := by
    intro n hn
    obtain ⟨hnI, hnc⟩ := Finset.mem_filter.mp hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hnI
    refine Finset.mem_biUnion.mpr ⟨(n - N) / L, ?_, ?_⟩
    · refine Finset.mem_range.mpr ?_
      have : (n - N) / L ≤ N / L := Nat.div_le_div_right (by omega)
      omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hnc⟩
      · have := Nat.div_mul_le_self (n - N) L; omega
      · refine lt_min ?_ h2
        have := Nat.lt_div_mul_add (a := n - N) (b := L) (by omega)
        have hmul : ((n - N) / L + 1) * L = (n - N) / L * L + L := by ring
        omega
  have hblock_bound : ∀ t ∈ Finset.range (N / L + 1),
      (((block t).filter (fun n => ¬ cert n)).card : ℝ) ≤
        16 * (N : ℝ) / ((M : ℝ) ^ 3 * Real.log (N : ℝ)) := by
    intro t _
    set N₀ := N + t * L
    set N₁ := min (N + (t + 1) * L) (2 * N)
    by_cases hempty : N₁ ≤ N₀
    · have h0 : block t = ∅ := Finset.Ico_eq_empty (by omega)
      simp only [h0, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
      positivity
    push Not at hempty
    have hN1_ge_N : N ≤ N₁ := by omega
    have hN1_le_2N : N₁ ≤ 2 * N := min_le_right _ _
    have hN1_diff : N₁ - N₀ ≤ L := by
      have : N₁ ≤ N + (t + 1) * L := min_le_left _ _
      have : N + (t + 1) * L = N₀ + L := by dsimp [N₀]; ring
      omega
    have hYN1_pos : 0 < Y N₁ := by dsimp [Y]; positivity
    have hYN1_ge_YN : Y N ≤ Y N₁ := by
      dsimp [Y]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hN1_ge_N) (by positivity))
        hr_pos.le
    have hlog8cwYN1_ge : (N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ) ≤ Real.log (8 * c * w_c * Y N₁) := by
      have h1 : Y N ≤ 8 * c * w_c * Y N₁ := by
        have h8cw : 1 ≤ 8 * c * w_c := by nlinarith only [hc_ge1, hw_ge1]
        nlinarith only [h8cw, hYN1_ge_YN, hYN1_pos]
      exact (log_Y_lower (by omega : 1 ≤ r) hN10).trans (Real.log_le_log (by positivity) h1)
    have hlog8cwYN1_le : Real.log (8 * c * w_c * Y N₁) ≤ 3 * (N : ℝ) * Real.log (N : ℝ) := by
      rw [Real.log_mul (by positivity) hYN1_pos.ne']
      have hY2N : Y N₁ ≤ Y (2 * N) := by
        dsimp [Y]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hN1_le_2N) (by positivity))
          hr_pos.le
      have hlogY2N := (Real.log_le_log hYN1_pos hY2N).trans (log_Y_upper (by omega : 1 ≤ r) (by omega : 2 ≤ 2 * N))
      push_cast at hlogY2N
      have hD_up' := hD_up
      dsimp only [C_b] at hD_up'
      linarith only [hlogY2N, hD_up']
    set D : ℕ := 1 + ⌊Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b)⌋₊
    have hD_pos_ratio : 0 ≤ Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b) :=
      div_nonneg (by linarith only [hlog8cwYN1_ge, show 0 ≤ (N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ) by positivity])
        hlogWC_pos.le
    have hD_ge_ratio : Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b) ≤ (D : ℝ) := by
      dsimp [D]; push_cast; linarith only [Nat.lt_floor_add_one (Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b))]
    have hD_sub1_le : ((D - 1 : ℕ) : ℝ) ≤ Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b) := by
      have : D - 1 = ⌊Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b)⌋₊ := by omega
      rw [this]; exact Nat.floor_le hD_pos_ratio
    have hD_le_4N : D ≤ 4 * N := by
      have h1 : Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b) ≤ 3 * (N : ℝ) := by
        rw [div_le_iff₀ hlogWC_pos]
        have hmul := mul_le_mul_of_nonneg_left hlogWC_ge (show 0 ≤ 3 * (N : ℝ) by positivity)
        linarith only [hmul, hlog8cwYN1_le]
      have hfl : ⌊Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b)⌋₊ ≤ 3 * N :=
        Nat.floor_le_of_le (by exact_mod_cast h1)
      omega
    have hD_ge_10 : 10 ≤ D := by
      have h1 : (10 : ℝ) ≤ Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b) := by
        rw [le_div_iff₀ hlogWC_pos]
        linarith only [hlogWC_le, hD_low10, hlog8cwYN1_ge]
      have hR : (10 : ℝ) ≤ (D : ℝ) := h1.trans hD_ge_ratio
      exact_mod_cast hR
    have hD_ge_3M : 3 * M + 20 ≤ D := by
      have h1 : (3 * (M : ℝ) + 20) ≤ Real.log (8 * c * w_c * Y N₁) / Real.log (W_b / C_b) := by
        rw [le_div_iff₀ hlogWC_pos]
        have hmul := mul_le_mul_of_nonneg_left hlogWC_le (show 0 ≤ 3 * (M : ℝ) + 20 by positivity)
        linarith only [hmul, hD_lowM, hlog8cwYN1_ge]
      have hR : ((3 * M + 20 : ℕ) : ℝ) ≤ (D : ℝ) := by push_cast; linarith only [h1, hD_ge_ratio]
      exact_mod_cast hR
    -- Construct initial Pade polynomials via Module 1!
    obtain ⟨P, hPdeg, hPne, hPbd, hRvan, hRbd⟩ :=
      exists_initial_pade hr hM1 (by omega : 1 ≤ u) huv hvM hD_ge_10
    -- Nonvanishing and degree bound of Delta via Module 2!
    have hΔne : Delta r M u v P ≠ 0 :=
      Delta_ne_zero hr hM1 hu2 huv hvM hD_ge_10 hD_ge_3M P hPdeg hPne hRvan
    have hΔdeg : (Delta r M u v P).natDegree ≤ 16 * N := by
      have h1 := @Delta_natDegree_le r M u v D hM1 hvM P hPdeg
      omega
    set ΔR : Polynomial ℝ := (Delta r M u v P).map (Int.castRingHom ℝ)
    have hΔR_ne : ΔR ≠ 0 := by
      intro h0; apply hΔne; ext idx
      have hidx := congrArg (fun p => p.coeff idx) h0
      simp only [ΔR, Polynomial.coeff_map, eq_intCast, Polynomial.coeff_zero, Int.cast_eq_zero] at hidx
      exact hidx
    have hΔR_deg : ΔR.natDegree ≤ 16 * N := Polynomial.natDegree_map_le.trans hΔdeg
    -- Every n in block t with rootMultiplicity ≤ K_max satisfies cert n!
    have hgood_cert : ∀ n ∈ block t, ΔR.rootMultiplicity (1 / (n : ℝ)) ≤ K_max → cert n := by
      intro n hn ha_le
      obtain ⟨hN0n, hnN1⟩ := Finset.mem_Ico.mp hn
      have hNn : N ≤ n := by omega
      have hn2N : n < 2 * N := lt_of_lt_of_le hnN1 hN1_le_2N
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hTn_ne : ((Tpoly r M).map (Int.castRingHom ℝ)).eval (1 / (n : ℝ)) ≠ 0 := by
        unfold Tpoly
        rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod, eq_intCast, Int.cast_natCast]
        have hprod_map : ∏ j ∈ Finset.Icc 1 M,
              (1 - Polynomial.C (j : ℤ) * Polynomial.X).map (Int.castRingHom ℝ) =
            ∏ j ∈ Finset.Icc 1 M, (1 - Polynomial.C (j : ℝ) * Polynomial.X) :=
          Finset.prod_congr rfl fun j _ => map_one_sub_nat_C_X j
        rw [hprod_map, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
        refine mul_ne_zero hr_pos.ne' (Finset.prod_ne_zero_iff.mpr fun j hj => ?_)
        simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_X]
        have hjM : j ≤ M := (Finset.mem_Icc.mp hj).2
        have hjn : (j : ℝ) * (1 / (n : ℝ)) < 1 := by
          rw [mul_one_div, div_lt_one hn_pos]; exact_mod_cast (show j < n by omega)
        linarith only [hjn]
      -- Full rank via Module 2!
      obtain ⟨k, hk_le, hdet_ne⟩ := P_ang_full_rank hr hM1 hu2 huv hvM P hΔne hTn_ne
      have hk_le_K : ∀ j : Fin 3, k j ≤ K_max + 2 := fun j =>
        (hk_le j).trans (Nat.add_le_add_right ha_le 2)
      -- Clear denominators with common factor Znat:
      set Znat : ℕ := r ^ (K_max + 2) * n ^ (D + (K_max + 2) * M)
      have hZ_pos : (0 : ℝ) < (Znat : ℝ) :=
        Nat.cast_pos.mpr (Nat.mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _))
      have hex_int : ∀ j i : Fin 3, ∃ m : ℤ,
          (Znat : ℝ) * (P_ang r M u v P (k j) i).eval (1 / (n : ℝ)) = (m : ℝ) := by
        intro j i
        obtain ⟨m0, hm0⟩ := P_ang_denom_int (fun l => negInvBinom_denom hr l)
          (by omega : 1 ≤ u) huv hvM P hPdeg (k j) n (by omega : 1 ≤ n) i
        have hkj_le : k j ≤ K_max + 2 := hk_le_K j
        set d : ℕ := K_max + 2 - k j
        refine ⟨((r ^ d * n ^ (d * M) : ℕ) : ℤ) * m0, ?_⟩
        rw [Int.cast_mul, Int.cast_natCast, ← hm0]
        dsimp only [Znat]
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
        have hr_pow : (r : ℝ) ^ (K_max + 2) = (r : ℝ) ^ d * (r : ℝ) ^ (k j) := by
          rw [← pow_add]; congr 1; omega
        have hn_pow : (n : ℝ) ^ (D + (K_max + 2) * M) =
            (n : ℝ) ^ (d * M) * (n : ℝ) ^ (D + k j * M) := by
          rw [← pow_add]; congr 1
          have hdk : d + k j = K_max + 2 := by omega
          rw [← hdk]; ring
        rw [hr_pow, hn_pow]; ring
      choose Afun hAfun using hex_int
      let A : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of Afun
      have hA_det : A.det ≠ 0 := by
        intro h0
        have hR0 : (A.map (Int.castRingHom ℝ)).det = 0 := by
          change ((Int.castRingHom ℝ).mapMatrix A).det = 0
          rw [← RingHom.map_det, h0, map_zero]
        let B : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun j i => (P_ang r M u v P (k j) i).eval (1 / (n : ℝ))
        have hAB : A.map (Int.castRingHom ℝ) = (Znat : ℝ) • B := by
          ext j i
          simp only [Matrix.map_apply, eq_intCast, Matrix.smul_apply, smul_eq_mul, A, B, Matrix.of_apply]
          exact (hAfun j i).symm
        rw [hAB, Matrix.det_smul, Fintype.card_fin] at hR0
        rcases mul_eq_zero.mp hR0 with hZ0 | hB0
        · exact (pow_ne_zero 3 hZ_pos.ne') hZ0
        · exact hdet_ne hB0
      have hZ_le : (Znat : ℝ) ≤ c * C_b ^ D := by
        dsimp only [Znat, c, C_b]
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, pow_add (n : ℝ)]
        have hr_le : (r : ℝ) ^ (K_max + 2) ≤ (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by nlinarith only [hr_pos, hN_ge1]) _
        have hn_M : (n : ℝ) ^ ((K_max + 2) * M) ≤ (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * M) :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by
            have hn2 : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn2N.le
            nlinarith only [hn2, hr_ge1, hN_pos]) _
        have hn_D : (n : ℝ) ^ D ≤ (2 * (N : ℝ)) ^ D :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hn2N.le) _
        have hpow_c : (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * M) =
            (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1)) := by
          rw [← pow_add]; congr 1; ring
        calc (r : ℝ) ^ (K_max + 2) * ((n : ℝ) ^ D * (n : ℝ) ^ ((K_max + 2) * M))
            = ((r : ℝ) ^ (K_max + 2) * (n : ℝ) ^ ((K_max + 2) * M)) * (n : ℝ) ^ D := by ring
          _ ≤ ((2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * M)) *
                (2 * (N : ℝ)) ^ D :=
              mul_le_mul (mul_le_mul hr_le hn_M (by positivity) (by positivity)) hn_D (by positivity) (by positivity)
          _ = (2 * (r : ℝ) * (N : ℝ)) ^ ((K_max + 2) * (M + 1)) * (2 * (N : ℝ)) ^ D := by rw [hpow_c]
      -- Bound (W_b / C_b)^D from both sides:
      have hWC_D_ge : 8 * c * w_c * Y N₁ ≤ (W_b / C_b) ^ D := by
        rw [← Real.log_le_log_iff (by positivity) (pow_pos (by linarith only [hWC1]) D), Real.log_pow]
        exact (div_le_iff₀ hlogWC_pos).mp hD_ge_ratio
      have hWC_D_le : (W_b / C_b) ^ D ≤ (W_b / C_b) * (8 * c * w_c * Y N₁) := by
        have hDsub : (W_b / C_b) ^ (D - 1) ≤ 8 * c * w_c * Y N₁ := by
          rw [← Real.log_le_log_iff (pow_pos (by linarith only [hWC1]) _) (by positivity), Real.log_pow]
          exact (le_div_iff₀ hlogWC_pos).mp hD_sub1_le
        have hDsplit : (W_b / C_b) ^ D = (W_b / C_b) * (W_b / C_b) ^ (D - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ D)]
        rw [hDsplit]
        exact mul_le_mul_of_nonneg_left hDsub (by linarith only [hWC1])
      have hC0_eq : (16 : ℝ) ^ M * (4 * (r : ℝ) ^ 4 * (M : ℝ)) ^ ((493 / 84 : ℝ) * (D : ℝ)) =
          (16 : ℝ) ^ M * U_b ^ D := by
        dsimp only [U_b]
        rw [← Real.rpow_mul_natCast (by positivity)]
      have hYn_pos : 0 < Y n := by dsimp [Y]; positivity
      have hYn_ge1 : 1 ≤ Y n := by
        dsimp [Y]
        have hf1 : (1 : ℝ) ≤ (n.factorial : ℝ) ^ (1 / (r : ℝ)) :=
          Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos n) (by positivity)
        nlinarith only [hr_ge1, hf1]
      have hbig_le_Yn : 8 * c * u_c * ((W_b / C_b) * 8 * c * w_c) ≤ (Y n) ^ (1 / 100000 : ℝ) := by
        rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hYn_pos _), Real.log_rpow hYn_pos]
        have hlogYn : (N : ℝ) / (4 * (r : ℝ)) * Real.log (N : ℝ) ≤ Real.log (Y n) := by
          have h1 : Y N ≤ Y n := by
            dsimp [Y]
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hNn) (by positivity))
              hr_pos.le
          exact (log_Y_lower (by omega : 1 ≤ r) hN10).trans (Real.log_le_log (by positivity) h1)
        linarith only [hbig_log, hlogYn]
      have hYN1_le_Yn : Y N₁ ≤ (Y n) ^ (1 + 1 / 100000 : ℝ) :=
        Y_block_ratio_le hr hN10 (Nat.floor_le (by positivity)) hlog2 (by omega) hN0n hnN1.le hN1_le_2N hN1_diff h2Nr
      have hYn_le_YN1 : Y n ≤ Y N₁ := by
        dsimp [Y]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.factorial_le hnN1.le) (by positivity))
          hr_pos.le
      refine ⟨A, hA_det, ?_, ?_⟩
      · -- Entry size bound: |(A j i : ℝ)| ≤ (Y n)^(1 - 1/20000) / 8
        intro j i
        have hkj_le : k j ≤ K_max + 2 := hk_le_K j
        have hPeval := P_ang_eval_bound (negInvBinom_pos (by omega : 1 ≤ r)) (negInvBinom_le_one (by omega : 1 ≤ r))
          hM1 (by omega : 1 ≤ u) huv hvM h8MN hNn hn2N P hPdeg (by positivity) hPbd i (k := k j)
        rw [hC0_eq] at hPeval
        have h4rN_le : (4 * (r : ℝ) * (N : ℝ)) ^ (k j) ≤ (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) :=
          pow_le_pow_right₀ (by nlinarith only [hr_ge1, hN_ge1]) hkj_le
        have hPeval' : |(P_ang r M u v P (k j) i).eval (1 / (n : ℝ))| ≤ u_c * U_b ^ D := by
          calc |(P_ang r M u v P (k j) i).eval (1 / (n : ℝ))|
              ≤ (4 * (r : ℝ) * (N : ℝ)) ^ (k j) * (4 : ℝ) ^ M * ((16 : ℝ) ^ M * U_b ^ D) := hPeval
            _ = (4 * (r : ℝ) * (N : ℝ)) ^ (k j) * (64 : ℝ) ^ M * U_b ^ D := by
                have h416 : (4 : ℝ) ^ M * (16 : ℝ) ^ M = (64 : ℝ) ^ M := by rw [← mul_pow]; norm_num
                rw [← h416]; ring
            _ ≤ (4 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) * (64 : ℝ) ^ M * U_b ^ D := by
                have := mul_le_mul_of_nonneg_right h4rN_le (show 0 ≤ (64 : ℝ) ^ M by positivity)
                exact mul_le_mul_of_nonneg_right this (by positivity)
        have h8A : 8 * |(A j i : ℝ)| ≤ 8 * c * u_c * (C_b * U_b) ^ D := by
          have hAeq : (A j i : ℝ) = (Znat : ℝ) * (P_ang r M u v P (k j) i).eval (1 / (n : ℝ)) :=
            (hAfun j i).symm
          rw [hAeq, abs_mul, abs_of_pos hZ_pos, mul_pow]
          have h1 := mul_le_mul hZ_le hPeval' (abs_nonneg _) (by positivity)
          linarith only [h1]
        exact pade_entry_bound hN_pos hc_ge1 hu_ge1 hw_ge1 (by positivity) (by positivity) hWC1
          hYn_ge1 hYN1_pos h8A hCU hWC hWC_D_le hbig_le_Yn hYN1_le_Yn
      · -- Linear form bound: |A j 0 + A j 1 * w u + A j 2 * w v| ≤ 1 / (8 * Y n)
        intro j
        have hkj_le : k j ≤ K_max + 2 := hk_le_K j
        have hRlin := P_ang_linearForm_bound (by omega : 1 ≤ r) hM1 (by omega : 1 ≤ u) huv hvM h8MN hNn hn2N P
          (R_ps_deriv_eq_P_ang (by omega : 1 ≤ r) hM1 (by omega : 1 ≤ u) (by omega : u ≤ M) hvM P (k j))
          (by positivity) hRvan hRbd
        rw [hC0_eq] at hRlin
        have hRlin' : |∑ i : Fin 3, (P_ang r M u v P (k j) i).eval (1 / (n : ℝ)) *
            omega3Val r u v (1 / (n : ℝ)) i| ≤
            (2 * (2 * (r : ℝ) * (N : ℝ)) ^ (k j) * (16 : ℝ) ^ M) * U_b ^ D *
            (4 * (M : ℝ) / (N : ℝ)) ^ ((29 * D) / 12 + 1) := by
          calc |∑ i : Fin 3, (P_ang r M u v P (k j) i).eval (1 / (n : ℝ)) *
                  omega3Val r u v (1 / (n : ℝ)) i|
              ≤ 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (k j) * ((16 : ℝ) ^ M * U_b ^ D) *
                  (4 * (M : ℝ) / (N : ℝ)) ^ ((29 * D) / 12 + 1) := hRlin
            _ = (2 * (2 * (r : ℝ) * (N : ℝ)) ^ (k j) * (16 : ℝ) ^ M) * U_b ^ D *
                  (4 * (M : ℝ) / (N : ℝ)) ^ ((29 * D) / 12 + 1) := by ring
        have hsum_eq : (A j 0 : ℝ) + (A j 1 : ℝ) * omegaVal r u (1 / (n : ℝ)) +
            (A j 2 : ℝ) * omegaVal r v (1 / (n : ℝ)) =
            (Znat : ℝ) * ∑ i : Fin 3, (P_ang r M u v P (k j) i).eval (1 / (n : ℝ)) *
              omega3Val r u v (1 / (n : ℝ)) i := by
          rw [Fin.sum_univ_three]
          have h0 : omega3Val r u v (1 / (n : ℝ)) 0 = 1 := by
            simp [omega3Val, omegaVal, beta3]
          have h1 : omega3Val r u v (1 / (n : ℝ)) 1 = omegaVal r u (1 / (n : ℝ)) := rfl
          have h2 : omega3Val r u v (1 / (n : ℝ)) 2 = omegaVal r v (1 / (n : ℝ)) := rfl
          have ha0 : (A j 0 : ℝ) = (Znat : ℝ) * (P_ang r M u v P (k j) 0).eval (1 / (n : ℝ)) := (hAfun j 0).symm
          have ha1 : (A j 1 : ℝ) = (Znat : ℝ) * (P_ang r M u v P (k j) 1).eval (1 / (n : ℝ)) := (hAfun j 1).symm
          have ha2 : (A j 2 : ℝ) = (Znat : ℝ) * (P_ang r M u v P (k j) 2).eval (1 / (n : ℝ)) := (hAfun j 2).symm
          rw [h0, h1, h2, ha0, ha1, ha2]; ring
        rw [hsum_eq, abs_mul, abs_of_pos hZ_pos]
        have h2rN_le : 2 * (2 * (r : ℝ) * (N : ℝ)) ^ (k j) * (16 : ℝ) ^ M ≤ w_c := by
          dsimp only [w_c]
          have h1 : (2 * (r : ℝ) * (N : ℝ)) ^ (k j) ≤ (2 * (r : ℝ) * (N : ℝ)) ^ (K_max + 2) :=
            pow_le_pow_right₀ (by nlinarith only [hr_ge1, hN_ge1]) hkj_le
          have h2 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
        exact pade_linform_bound hr_ge1 hM_pos hN_pos
          (by exact_mod_cast (show 4 * M ≤ N by omega)) hc_ge1 hw_ge1 (by positivity) (by positivity)
          hYn_pos hYn_le_YN1 (by positivity) rfl rfl hZ_le hWC_D_ge h2rN_le hRlin'
    -- Count failures in block t via root multiplicity sum!
    set bad := (block t).filter (fun n => ¬ cert n)
    have hbad_mult : ∀ n ∈ bad, K_max + 1 ≤ ΔR.rootMultiplicity (1 / (n : ℝ)) := by
      intro n hn
      obtain ⟨hnB, hnc⟩ := Finset.mem_filter.mp hn
      by_contra hle
      exact hnc (hgood_cert n hnB (by omega))
    have hinj : Set.InjOn (fun n : ℕ => 1 / (n : ℝ)) ↑bad := by
      intro a _ b _ heq
      have hR : (a : ℝ) = (b : ℝ) := by
        simpa [one_div] using congrArg Inv.inv heq
      exact_mod_cast hR
    have hcard_mul : bad.card * (K_max + 1) ≤ 16 * N := by
      calc bad.card * (K_max + 1)
          = ∑ _n ∈ bad, (K_max + 1) := by simp
        _ ≤ ∑ n ∈ bad, ΔR.rootMultiplicity (1 / (n : ℝ)) := Finset.sum_le_sum hbad_mult
        _ ≤ ΔR.natDegree := sum_rootMultiplicity_le_natDegree hΔR_ne bad _ hinj
        _ ≤ 16 * N := hΔR_deg
    have hK_ge : (M : ℝ) ^ 3 * Real.log (N : ℝ) ≤ ((K_max + 1 : ℕ) : ℝ) := by
      have hceil := Nat.le_ceil ((M : ℝ) ^ 3 * Real.log (N : ℝ))
      push_cast; linarith
    rw [le_div_iff₀ (by positivity)]
    have hcast : (bad.card : ℝ) * ((K_max + 1 : ℕ) : ℝ) ≤ 16 * (N : ℝ) := by exact_mod_cast hcard_mul
    calc (bad.card : ℝ) * ((M : ℝ) ^ 3 * Real.log (N : ℝ))
        ≤ (bad.card : ℝ) * ((K_max + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hK_ge (Nat.cast_nonneg _)
      _ ≤ 16 * (N : ℝ) := hcast
  -- Sum hblock_bound over t ∈ range (N / L + 1)!
  have htotal : (((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card : ℝ) ≤
      ((N / L + 1 : ℕ) : ℝ) * (16 * (N : ℝ) / ((M : ℝ) ^ 3 * Real.log (N : ℝ))) := by
    have h1 : ((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card ≤
        ∑ t ∈ Finset.range (N / L + 1), ((block t).filter (fun n => ¬ cert n)).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h1R : (((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card : ℝ) ≤
        ∑ t ∈ Finset.range (N / L + 1), (((block t).filter (fun n => ¬ cert n)).card : ℝ) := by
      exact_mod_cast h1
    have h2 : ∑ t ∈ Finset.range (N / L + 1), (((block t).filter (fun n => ¬ cert n)).card : ℝ) ≤
        ((Finset.range (N / L + 1)).card : ℝ) * (16 * (N : ℝ) / ((M : ℝ) ^ 3 * Real.log (N : ℝ))) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum hblock_bound
    rw [Finset.card_range] at h2
    exact h1R.trans h2
  calc (((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card : ℝ)
      ≤ ((N / L + 1 : ℕ) : ℝ) * (16 * (N : ℝ) / ((M : ℝ) ^ 3 * Real.log (N : ℝ))) := htotal
    _ ≤ (3 * Real.log (N : ℝ)) * (16 * (N : ℝ) / ((M : ℝ) ^ 3 * Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hNdivL (by positivity)
    _ = 48 * (N : ℝ) / (M : ℝ) ^ 3 := by field_simp [hlog_pos.ne']; ring
    _ ≤ 100 * (N : ℝ) / (M : ℝ) ^ 3 := by
        refine div_le_div_of_nonneg_right (by linarith) (by positivity)

/- #### Part 3F: Final assembly of BOTH Erdos 393 theorems! -/

open scoped Classical in
private lemma single_pattern_dyadic_bound (T : Finset ℕ) (hT : 2 ≤ T.card) :
    let r := T.card
    let sol := fun n y : ℕ =>
      (r : ℤ) ^ r * (n.factorial : ℤ) = ∏ i ∈ T, ((y : ℤ) + (r : ℤ) * (i : ℤ) - ∑ j ∈ T, (j : ℤ))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => ∃ y : ℕ, sol n y)).card : ℝ) ≤
        C * (N : ℝ) ^ (33 / 34 : ℝ) := by
  intro r sol
  let Y := fun n : ℕ => (r : ℝ) * (n.factorial : ℝ) ^ (1 / (r : ℝ))
  have h1 := pade_exceptional_bound r hT
  have h2 := simul_approx_of_sol T hT (1 / 20000) (by norm_num)
  have h3 : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ (1 / 34 : ℝ) :=
    eventually_rpow_gt_const 4 (1 / 34) (by norm_num)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (h1.and (h2.and h3))
  let C_blk : ℝ := max (2 * (2 * (r : ℝ) + 100) + 4 * (r : ℝ)) ((B : ℝ) + 2)
  have hC_blk_nn : 0 ≤ C_blk := le_trans (by positivity) (le_max_left _ _)
  have hblock : ∀ N : ℕ, 1 ≤ N →
      (((Finset.Ico N (2 * N)).filter (fun n => ∃ y : ℕ, sol n y)).card : ℝ) ≤
        C_blk * (N : ℝ) ^ (33 / 34 : ℝ) := by
    intro N hN1
    set S := (Finset.Ico N (2 * N)).filter (fun n => ∃ y : ℕ, sol n y)
    by_cases hBN : B ≤ N
    · obtain ⟨hpade, happrox, hN4⟩ := hB N hBN
      set M := ⌊(N : ℝ) ^ (1 / 34 : ℝ)⌋₊
      have hM1 : 1 ≤ M := Nat.one_le_floor_iff _ |>.mpr (by linarith)
      have hM_ge_half : (N : ℝ) ^ (1 / 34 : ℝ) / 2 ≤ (M : ℝ) := by
        have hlt := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 34 : ℝ))
        linarith
      have hcount : ∀ u v : ℕ, 0 < u → u < v → v ≤ M → r ∣ u → r ∣ v →
          ((S.filter (fun n => v ≤ n ∧ n - u ∈ S ∧ n - v ∈ S)).card : ℝ) ≤
            100 * (N : ℝ) / (M : ℝ) ^ 3 := by
        intro u v hu huv hvM hru hrv
        let cert := fun n : ℕ => ∃ A : Matrix (Fin 3) (Fin 3) ℤ, A.det ≠ 0 ∧
          (∀ i j, |(A i j : ℝ)| ≤ (Y n) ^ (1 - 1 / 20000 : ℝ) / 8) ∧
          ∀ i, |(A i 0 : ℝ) + (A i 1 : ℝ) * omegaVal r u (1 / (n : ℝ)) +
                (A i 2 : ℝ) * omegaVal r v (1 / (n : ℝ))| ≤ 1 / (8 * Y n)
        have hsub : S.filter (fun n => v ≤ n ∧ n - u ∈ S ∧ n - v ∈ S) ⊆
            (Finset.Ico N (2 * N)).filter (fun n => ¬ cert n) := by
          intro n hn
          obtain ⟨hnS, hvn, hnuS, hnvS⟩ := Finset.mem_filter.mp hn
          obtain ⟨hnI, ⟨y, hy⟩⟩ := Finset.mem_filter.mp hnS
          obtain ⟨_, hu_sol⟩ := Finset.mem_filter.mp hnuS
          obtain ⟨_, hv_sol⟩ := Finset.mem_filter.mp hnvS
          refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
          rintro ⟨A, hdet, hAsize, hAlin⟩
          obtain ⟨hy0, hyle, hsim⟩ := happrox n hnI y hy
          obtain ⟨p, hp⟩ := hsim u hu (by omega) (by omega) hru hu_sol
          obtain ⟨q, hq⟩ := hsim v (by omega) hvn hvM hrv hv_sol
          have hYn_pos : 0 < Y n := by
            dsimp [Y]
            have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
            positivity
          exact incompatible hYn_pos (Real.rpow_pos_of_pos hYn_pos _) hy0 hyle hp hq A hdet hAsize hAlin
        calc ((S.filter (fun n => v ≤ n ∧ n - u ∈ S ∧ n - v ∈ S)).card : ℝ)
            ≤ (((Finset.Ico N (2 * N)).filter (fun n => ¬ cert n)).card : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ ≤ 100 * (N : ℝ) / (M : ℝ) ^ 3 := hpade u v hu huv hvM hru hrv
      have hpig := block_pigeonhole_bound r N M hT hM1 S (Finset.filter_subset _ _) 100 (by norm_num) hcount
      have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      have hNdivM : (N : ℝ) / (M : ℝ) ≤ 2 * (N : ℝ) ^ (33 / 34 : ℝ) := by
        have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
        calc (N : ℝ) / (M : ℝ)
            ≤ (N : ℝ) / ((N : ℝ) ^ (1 / 34 : ℝ) / 2) :=
              div_le_div_of_nonneg_left hN_pos.le (by positivity) hM_ge_half
          _ = 2 * ((N : ℝ) / (N : ℝ) ^ (1 / 34 : ℝ)) := by ring
          _ = 2 * (N : ℝ) ^ (33 / 34 : ℝ) := by
              congr 1
              rw [div_eq_iff (Real.rpow_pos_of_pos hN_pos _).ne', ← Real.rpow_add hN_pos,
                show (33 / 34 : ℝ) + 1 / 34 = 1 by norm_num, Real.rpow_one]
      have h1_le_N33 : (1 : ℝ) ≤ (N : ℝ) ^ (33 / 34 : ℝ) :=
        Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
      have hcoef : (2 * (r : ℝ) + 100) * (N : ℝ) / (M : ℝ) + 4 * (r : ℝ) ≤
          (2 * (2 * (r : ℝ) + 100) + 4 * (r : ℝ)) * (N : ℝ) ^ (33 / 34 : ℝ) := by
        have h1 : (2 * (r : ℝ) + 100) * ((N : ℝ) / (M : ℝ)) ≤
            (2 * (r : ℝ) + 100) * (2 * (N : ℝ) ^ (33 / 34 : ℝ)) :=
          mul_le_mul_of_nonneg_left hNdivM (by positivity)
        have h2 : 4 * (r : ℝ) ≤ 4 * (r : ℝ) * (N : ℝ) ^ (33 / 34 : ℝ) := by
          nlinarith [Nat.cast_nonneg (α := ℝ) r]
        have hring : (2 * (r : ℝ) + 100) * (N : ℝ) / (M : ℝ) = (2 * (r : ℝ) + 100) * ((N : ℝ) / (M : ℝ)) := by
          ring
        linarith
      exact hpig.trans (hcoef.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
    · have hScard : S.card ≤ N := by
        calc S.card ≤ (Finset.Ico N (2 * N)).card := Finset.card_filter_le _ _
          _ = N := by rw [Nat.card_Ico]; omega
      have h1_le_N33 : (1 : ℝ) ≤ (N : ℝ) ^ (33 / 34 : ℝ) :=
        Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
      have hNB : (N : ℝ) ≤ C_blk :=
        (show (N : ℝ) ≤ (B : ℝ) + 2 by exact_mod_cast (show N ≤ B + 2 by omega)).trans (le_max_right _ _)
      calc (S.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hScard
        _ ≤ C_blk := hNB
        _ = C_blk * 1 := (mul_one _).symm
        _ ≤ C_blk * (N : ℝ) ^ (33 / 34 : ℝ) := mul_le_mul_of_nonneg_left h1_le_N33 hC_blk_nn
  exact dyadic_count_bound hC_blk_nn (by norm_num) hblock

theorem erdos_393_bui_pratt_zaharescu_proved (m : ℕ) :
    (fun N : ℕ ↦ (({n : ℕ | Erdos393.f n = m} ∩ Set.Iic N).ncard : ℝ)) =O[atTop]
      (fun N : ℕ ↦ (N : ℝ) ^ (33 / 34 : ℝ)) := by
  classical
  -- For m = 0, {n | f n = 0} ⊆ {0, 1}
  by_cases hm0 : m = 0
  · subst hm0
    rw [Asymptotics.isBigO_iff]
    refine ⟨2, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hsub : {n : ℕ | Erdos393.f n = 0} ∩ Set.Iic N ⊆ ({0, 1} : Set ℕ) := by
      intro n hn
      rcases hn with ⟨hfn, _⟩
      change Erdos393.f n = 0 at hfn
      by_contra h2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h2
      have hge := Erdos393.one_le_f n (by omega)
      omega
    have hnc : ({n : ℕ | Erdos393.f n = 0} ∩ Set.Iic N).ncard ≤ 2 := by
      calc ({n : ℕ | Erdos393.f n = 0} ∩ Set.Iic N).ncard
          ≤ ({0, 1} : Set ℕ).ncard := Set.ncard_le_ncard hsub (by simp)
        _ ≤ 2 := by
            have : ({0, 1} : Set ℕ) = ↑({0, 1} : Finset ℕ) := by simp
            rw [this, Set.ncard_coe_finset]; decide
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (33 / 34 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (({n : ℕ | Erdos393.f n = 0} ∩ Set.Iic N).ncard : ℝ) ≤ 2 := by exact_mod_cast hnc
      _ ≤ 2 * (N : ℝ) ^ (33 / 34 : ℝ) := by linarith
  -- For m ≥ 1, union over finitely many T ∈ (Icc 0 m).powerset with 2 ≤ T.card
  let pats := (Finset.Icc 0 m).powerset.filter (fun T => 2 ≤ T.card)
  have hex : ∀ T ∈ pats, ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => ∃ y : ℕ,
        (T.card : ℤ) ^ T.card * (n.factorial : ℤ) =
          ∏ i ∈ T, ((y : ℤ) + (T.card : ℤ) * (i : ℤ) - ∑ j ∈ T, (j : ℤ)))).card : ℝ) ≤
        C * (N : ℝ) ^ (33 / 34 : ℝ) := fun T hT =>
    single_pattern_dyadic_bound T (Finset.mem_filter.mp hT).2
  choose Cfun hCnn hCbd using hex
  let Ctot : ℝ := 2 + ∑ T ∈ pats.attach, Cfun T.1 T.2
  rw [Asymptotics.isBigO_iff]
  refine ⟨Ctot, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hset_eq : ({n : ℕ | Erdos393.f n = m} ∩ Set.Iic N) =
      ↑((Finset.range (N + 1)).filter (fun n => Erdos393.f n = m)) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Iic, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_range]
    omega
  rw [hset_eq, Set.ncard_coe_finset, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hsub : (Finset.range (N + 1)).filter (fun n => Erdos393.f n = m) ⊆
      ({0, 1} : Finset ℕ) ∪ pats.attach.biUnion (fun T => (Finset.range (N + 1)).filter (fun n => ∃ y : ℕ,
        (T.1.card : ℤ) ^ T.1.card * (n.factorial : ℤ) =
          ∏ i ∈ T.1, ((y : ℤ) + (T.1.card : ℤ) * (i : ℤ) - ∑ j ∈ T.1, (j : ℤ)))) := by
    intro n hn
    obtain ⟨hnR, hfn⟩ := Finset.mem_filter.mp hn
    by_cases hn2 : n < 2
    · exact Finset.mem_union_left _ (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    · refine Finset.mem_union_right _ ?_
      obtain ⟨T, hTpow, hTcard, y, hy⟩ := erdos393_factor_pattern (by omega) hfn
      have hTpats : T ∈ pats := Finset.mem_filter.mpr ⟨hTpow, hTcard⟩
      exact Finset.mem_biUnion.mpr ⟨⟨T, hTpats⟩, Finset.mem_attach _ _,
        Finset.mem_filter.mpr ⟨hnR, y, hy⟩⟩
  have hcard : ((Finset.range (N + 1)).filter (fun n => Erdos393.f n = m)).card ≤
      2 + ∑ T ∈ pats.attach, ((Finset.range (N + 1)).filter (fun n => ∃ y : ℕ,
        (T.1.card : ℤ) ^ T.1.card * (n.factorial : ℤ) =
          ∏ i ∈ T.1, ((y : ℤ) + (T.1.card : ℤ) * (i : ℤ) - ∑ j ∈ T.1, (j : ℤ)))).card := by
    calc ((Finset.range (N + 1)).filter (fun n => Erdos393.f n = m)).card
        ≤ ({0, 1} : Finset ℕ).card +
            (pats.attach.biUnion _).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      _ ≤ 2 + ∑ T ∈ pats.attach, _ :=
          Nat.add_le_add (by decide) Finset.card_biUnion_le
  have hcardR : (((Finset.range (N + 1)).filter (fun n => Erdos393.f n = m)).card : ℝ) ≤
      2 + ∑ T ∈ pats.attach, (((Finset.range (N + 1)).filter (fun n => ∃ y : ℕ,
        (T.1.card : ℤ) ^ T.1.card * (n.factorial : ℤ) =
          ∏ i ∈ T.1, ((y : ℤ) + (T.1.card : ℤ) * (i : ℤ) - ∑ j ∈ T.1, (j : ℤ)))).card : ℝ) := by
    exact_mod_cast hcard
  have h1_le : (1 : ℝ) ≤ (N : ℝ) ^ (33 / 34 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hsum_le : ∑ T ∈ pats.attach, (((Finset.range (N + 1)).filter (fun n => ∃ y : ℕ,
        (T.1.card : ℤ) ^ T.1.card * (n.factorial : ℤ) =
          ∏ i ∈ T.1, ((y : ℤ) + (T.1.card : ℤ) * (i : ℤ) - ∑ j ∈ T.1, (j : ℤ)))).card : ℝ) ≤
      (∑ T ∈ pats.attach, Cfun T.1 T.2) * (N : ℝ) ^ (33 / 34 : ℝ) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun T _ => hCbd T.1 T.2 N hN
  dsimp only [Ctot]
  linarith

theorem erdos_393_berend_osgood_proved (m : ℕ) :
    {n : ℕ | Erdos393.f n = m}.HasDensity 0 := by
  have hO := erdos_393_bui_pratt_zaharescu_proved m
  rw [Asymptotics.isBigO_iff] at hO
  obtain ⟨C, hC⟩ := hO
  have hCnn : 0 ≤ C := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp hC
    have h1 := hN (max N 1) (le_max_left _ _)
    have hpos : (0 : ℝ) < ((max N 1 : ℕ) : ℝ) ^ (33 / 34 : ℝ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < max N 1 by omega)) _
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_pos hpos] at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) ({n : ℕ | Erdos393.f n = m} ∩ Set.Iic (max N 1)).ncard]
  unfold Set.HasDensity Set.partialDensity
  have hlim : Tendsto (fun N : ℕ => C * (N : ℝ) ^ (-(1 / 34 : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 34)).comp
      tendsto_natCast_atTop_atTop |>.const_mul C
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 1, hC] with N hN hCN
    have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hden : (Set.univ ∩ Set.Iio N).ncard = N := by
      have : (Set.univ ∩ Set.Iio N) = ↑(Finset.range N) := by
        ext k; simp
      rw [this, Set.ncard_coe_finset, Finset.card_range]
    have hnum_le : (({n : ℕ | Erdos393.f n = m} ∩ Set.univ) ∩ Set.Iio N).ncard ≤
        ({n : ℕ | Erdos393.f n = m} ∩ Set.Iic N).ncard := by
      refine Set.ncard_le_ncard ?_ ((Set.finite_Iic N).subset Set.inter_subset_right)
      intro k hk
      exact ⟨hk.1.1, Set.mem_Iic.mpr (le_of_lt (Set.mem_Iio.mp hk.2))⟩
    rw [hden]
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hCN
    calc ((({n : ℕ | Erdos393.f n = m} ∩ Set.univ) ∩ Set.Iio N).ncard : ℝ) / (N : ℝ)
        ≤ (({n : ℕ | Erdos393.f n = m} ∩ Set.Iic N).ncard : ℝ) / (N : ℝ) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hnum_le) hN_pos.le
      _ ≤ (C * (N : ℝ) ^ (33 / 34 : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right hCN hN_pos.le
      _ = C * (N : ℝ) ^ (-(1 / 34 : ℝ)) := by
          rw [mul_div_assoc]; congr 1
          rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hN_pos]; norm_num
end Mod3

end BPZ

theorem OMA.solution : type_of% @Erdos393.erdos_393.variants.bui_pratt_zaharescu :=
  BPZ.erdos_393_bui_pratt_zaharescu_proved
