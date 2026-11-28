import OMAStatements.S_mo_221284

-- Problem: The Hermite remainder point for the reciprocal square
-- Upstream: statements/mo-221284.lean (declaration OMA.S_mo_221284.main)
-- Credit: @FrancoisCharroin
-- Part 1 via root multiplicity counting on R = X^2 * p - 1 + (1 + 2*(sum t_i^-1)*X)/(prod t_i^2) * W.
-- Part 2 via the two-sided bound scale <= (point / eps)^(2n+2) <= (2n+1) * scale^2.

namespace OMA.Mo221284

open Polynomial Filter Finset OMA.S_mo_221284
open scoped Topology

lemma two_le_rootMultiplicity_of_eval_and_deriv {f : ℝ[X]} (hf : f ≠ 0) (a : ℝ)
    (h0 : f.eval a = 0) (h1 : f.derivative.eval a = 0) :
    2 ≤ f.rootMultiplicity a := by
  have hdvd1 : (X - C a) ∣ f := Polynomial.dvd_iff_isRoot.mpr h0
  rcases hdvd1 with ⟨g, rfl⟩
  have hderiv : (X - C a).derivative * g + (X - C a) * g.derivative = ((X - C a) * g).derivative := by
    rw [Polynomial.derivative_mul]
  have hg0 : g.eval a = 0 := by
    have := h1
    rw [Polynomial.derivative_mul] at this
    simp at this
    exact this
  have hdvd2 : (X - C a) ∣ g := Polynomial.dvd_iff_isRoot.mpr hg0
  rcases hdvd2 with ⟨h, rfl⟩
  have hdvd_sq : (X - C a) ^ 2 ∣ (X - C a) * ((X - C a) * h) := by
    refine ⟨h, ?_⟩
    ring
  exact (Polynomial.le_rootMultiplicity_iff hf).mpr hdvd_sq

lemma deriv_prod_sq_eval_zero_finset {n : ℕ} (t : Fin n → ℝ) (ht : ∀ i, 0 < t i)
    (s : Finset (Fin n)) :
    (derivative (∏ i ∈ s, (X - C (t i)) ^ 2)).eval 0 =
      -2 * (∏ i ∈ s, (t i) ^ 2) * ∑ i ∈ s, (t i)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Polynomial.derivative_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_mul, ih, Finset.prod_insert ha, Finset.sum_insert ha]
    have hda : (derivative ((X - C (t a)) ^ 2)).eval 0 = -2 * t a := by
      have hd : derivative ((X - C (t a)) ^ 2) = 2 * (X - C (t a)) := by
        rw [pow_two, Polynomial.derivative_mul, Polynomial.derivative_sub,
          Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul, mul_one]
        ring
      rw [hd]
      simp [Polynomial.eval_mul, Polynomial.eval_sub]
    have hea : ((X - C (t a)) ^ 2).eval 0 = (t a) ^ 2 := by simp
    have hps : (∏ i ∈ s, (X - C (t i)) ^ 2).eval 0 = ∏ i ∈ s, (t i) ^ 2 := by
      simp [Polynomial.eval_prod]
    rw [hda, hea, hps]
    have hta : t a ≠ 0 := (ht a).ne'
    field_simp [hta]
    ring

lemma deriv_prod_sq_eval_zero {n : ℕ} (t : Fin n → ℝ) (ht : ∀ i, 0 < t i) :
    (derivative (∏ i : Fin n, (X - C (t i)) ^ 2)).eval 0 =
      -2 * (∏ i : Fin n, (t i) ^ 2) * ∑ i : Fin n, (t i)⁻¹ :=
  deriv_prod_sq_eval_zero_finset t ht Finset.univ

lemma poly_identity {n : ℕ} (t : Fin n → ℝ) (p : ℝ[X])
    (hinj : Function.Injective t) (ht : ∀ i, 0 < t i) (hint : Interpolates p t) :
    ∀ x : ℝ, 1 - x ^ 2 * p.eval x =
      (1 + 2 * x * ∑ i, (t i)⁻¹) / (∏ i, (t i) ^ 2) * ∏ i, (x - t i) ^ 2 := by
  have hn : 0 < n := by
    have := hint.1
    omega
  let W : ℝ[X] := ∏ i : Fin n, (X - C (t i)) ^ 2
  let P0 : ℝ := ∏ i : Fin n, (t i) ^ 2
  let S0 : ℝ := ∑ i : Fin n, (t i)⁻¹
  have hP0_pos : 0 < P0 := Finset.prod_pos fun i _ => sq_pos_of_pos (ht i)
  have hP0_ne : P0 ≠ 0 := hP0_pos.ne'
  let R : ℝ[X] := X ^ 2 * p - 1 + C P0⁻¹ * (1 + C (2 * S0) * X) * W
  have hW_deg : W.natDegree = 2 * n := by
    have hmon : ∀ i ∈ (Finset.univ : Finset (Fin n)), ((X - C (t i)) ^ 2).Monic :=
      fun i _ => (Polynomial.monic_X_sub_C (t i)).pow 2
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
    have hdeg1 : ∀ i : Fin n, ((X - C (t i)) ^ 2).natDegree = 2 := by
      intro i
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    simp [hdeg1, mul_comm]
  have hR_deg : R.natDegree ≤ 2 * n + 1 := by
    have h1 : (X ^ 2 * p - 1).natDegree ≤ 2 * n + 1 := by
      calc
        (X ^ 2 * p - 1).natDegree ≤ max (X ^ 2 * p).natDegree (1 : ℝ[X]).natDegree :=
          Polynomial.natDegree_sub_le _ _
        _ ≤ max (2 + p.natDegree) 0 := by
          gcongr
          · calc
              (X ^ 2 * p).natDegree ≤ (X ^ 2 : ℝ[X]).natDegree + p.natDegree :=
                Polynomial.natDegree_mul_le
              _ = 2 + p.natDegree := by simp
          · simp
        _ ≤ 2 * n + 1 := by
          have := hint.1
          omega
    have h2 : (C P0⁻¹ * (1 + C (2 * S0) * X) * W).natDegree ≤ 2 * n + 1 := by
      calc
        (C P0⁻¹ * (1 + C (2 * S0) * X) * W).natDegree
            ≤ (C P0⁻¹ * (1 + C (2 * S0) * X)).natDegree + W.natDegree :=
              Polynomial.natDegree_mul_le
        _ ≤ (C P0⁻¹ : ℝ[X]).natDegree + (1 + C (2 * S0) * X).natDegree + 2 * n := by
              rw [hW_deg]
              gcongr
              exact Polynomial.natDegree_mul_le
        _ ≤ 0 + 1 + 2 * n := by
              have hlin : (1 + C (2 * S0) * X).natDegree ≤ 1 := by
                calc
                  (1 + C (2 * S0) * X).natDegree ≤
                      max (1 : ℝ[X]).natDegree (C (2 * S0) * X).natDegree :=
                    Polynomial.natDegree_add_le _ _
                  _ ≤ max 0 ((C (2 * S0) : ℝ[X]).natDegree + (X : ℝ[X]).natDegree) := by
                    gcongr
                    · simp
                    · exact Polynomial.natDegree_mul_le
                  _ ≤ 1 := by
                    rw [Polynomial.natDegree_C, Polynomial.natDegree_X]
                    omega
              simp only [Polynomial.natDegree_C]
              omega
        _ = 2 * n + 1 := by omega
    exact le_trans (Polynomial.natDegree_add_le _ _) (max_le h1 h2)
  have hR_zero : R = 0 := by
    by_contra hRne
    have hW0 : W.eval 0 = P0 := by
      simp [W, P0, Polynomial.eval_prod]
    have hR0 : R.eval 0 = 0 := by
      simp [R, hW0, hP0_ne]
    have hR0' : R.derivative.eval 0 = 0 := by
      have hW0' : W.derivative.eval 0 = -2 * P0 * S0 := deriv_prod_sq_eval_zero t ht
      have hd : R.derivative =
          ((X ^ 2 : ℝ[X]).derivative * p + X ^ 2 * p.derivative) +
          C P0⁻¹ * (C (2 * S0) * W + (1 + C (2 * S0) * X) * W.derivative) := by
        dsimp only [R]
        simp [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul]
        ring
      rw [hd]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, Polynomial.derivative_pow,
        Polynomial.derivative_X, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, add_zero,
        hW0, hW0']
      field_simp [hP0_ne]
      ring
    have hmul0 : 2 ≤ R.rootMultiplicity 0 :=
      two_le_rootMultiplicity_of_eval_and_deriv hRne 0 hR0 hR0'
    have hmult : ∀ i : Fin n, 2 ≤ R.rootMultiplicity (t i) := by
      intro i
      have hWi : W.eval (t i) = 0 := by
        rw [show W = ∏ j : Fin n, (X - C (t j)) ^ 2 from rfl, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
      have hWi' : W.derivative.eval (t i) = 0 := by
        have hdvd : (X - C (t i)) ^ 2 ∣ W :=
          Finset.dvd_prod_of_mem (fun j => (X - C (t j)) ^ 2) (Finset.mem_univ i)
        rcases hdvd with ⟨q, hq⟩
        rw [hq, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
          Polynomial.derivative_X, Polynomial.derivative_C]
        simp
      have hti : t i ≠ 0 := (ht i).ne'
      have hpi := (hint.2 i).1
      have hpi' := (hint.2 i).2
      have hRi : R.eval (t i) = 0 := by
        dsimp only [R]
        simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, hWi, mul_zero, add_zero,
          hpi]
        field_simp [hti]
        ring
      have hRi' : R.derivative.eval (t i) = 0 := by
        have hd : R.derivative =
            (C 2 * X * p + X ^ 2 * p.derivative) +
            C P0⁻¹ * (C (2 * S0) * W + (1 + C (2 * S0) * X) * W.derivative) := by
          dsimp only [R]
          simp [Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
            Polynomial.derivative_pow]
          ring
        rw [hd]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one, hWi, hWi', hpi, hpi',
          mul_zero, add_zero]
        field_simp [hti]
        ring
      exact two_le_rootMultiplicity_of_eval_and_deriv hRne (t i) hRi hRi'
    let rootsSet : Finset ℝ := insert 0 (Finset.univ.image t)
    have h0not : (0 : ℝ) ∉ Finset.univ.image t := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro i
      exact (ht i).ne'
    have hcard_set : rootsSet.card = n + 1 := by
      rw [Finset.card_insert_of_notMem h0not, Finset.card_image_of_injective _ hinj,
        Finset.card_fin]
    have hcount_ge : ∀ r ∈ rootsSet, 2 ≤ R.roots.count r := by
      intro r hr
      rw [Polynomial.count_roots]
      rcases Finset.mem_insert.mp hr with rfl | hmem
      · exact hmul0
      · rcases Finset.mem_image.mp hmem with ⟨i, _, rfl⟩
        exact hmult i
    have hle_roots : ∑ r ∈ rootsSet, R.roots.count r ≤ R.roots.card := by
      have hsub : rootsSet.val.bind (fun r => Multiset.replicate (R.roots.count r) r) ≤ R.roots := by
        rw [Multiset.le_iff_count]
        intro a
        rw [Multiset.count_bind]
        by_cases ha : a ∈ rootsSet
        · have hterm : ∀ r ∈ rootsSet,
              Multiset.count a (Multiset.replicate (R.roots.count r) r) =
                if r = a then R.roots.count a else 0 := by
            intro r _
            by_cases hra : r = a
            · subst hra; simp
            · simp [hra, Multiset.count_replicate]
          have hsum : (rootsSet.val.map fun r => Multiset.count a (Multiset.replicate (R.roots.count r) r)).sum =
              ∑ r ∈ rootsSet, Multiset.count a (Multiset.replicate (R.roots.count r) r) := rfl
          rw [hsum, Finset.sum_congr rfl hterm]
          simp [ha]
        · have hterm : ∀ r ∈ rootsSet,
              Multiset.count a (Multiset.replicate (R.roots.count r) r) = 0 := by
            intro r hr
            have hra : r ≠ a := fun h => ha (h ▸ hr)
            rw [Multiset.count_replicate, if_neg hra]
          have hsum : (rootsSet.val.map fun r => Multiset.count a (Multiset.replicate (R.roots.count r) r)).sum =
              ∑ r ∈ rootsSet, Multiset.count a (Multiset.replicate (R.roots.count r) r) := rfl
          rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_const_zero]
          exact Nat.zero_le _
      have hcard_le := Multiset.card_le_card hsub
      rw [Multiset.card_bind] at hcard_le
      simpa using hcard_le
    have hsum_ge : 2 * (n + 1) ≤ ∑ r ∈ rootsSet, R.roots.count r := by
      calc
        2 * (n + 1) = ∑ _r ∈ rootsSet, 2 := by simp [hcard_set, mul_comm]
        _ ≤ ∑ r ∈ rootsSet, R.roots.count r := Finset.sum_le_sum hcount_ge
    have hcard_deg : R.roots.card ≤ R.natDegree := Polynomial.card_roots' R
    omega
  intro x
  have hRx : R.eval x = 0 := by rw [hR_zero]; simp
  dsimp only [R, W, P0, S0] at hRx
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_prod] at hRx
  have hdiv : (∏ i : Fin n, (t i) ^ 2)⁻¹ * (1 + 2 * (∑ i : Fin n, (t i)⁻¹) * x) =
      (1 + 2 * x * ∑ i : Fin n, (t i)⁻¹) / ∏ i : Fin n, (t i) ^ 2 := by
    rw [div_eq_inv_mul]
    ring
  rw [hdiv] at hRx
  linarith

lemma part1 (n : ℕ) (t : Fin n → ℝ) (p : ℝ[X]) (x τ : ℝ)
    (hinj : Function.Injective t) (ht : ∀ i, 0 < t i) (hint : Interpolates p t)
    (hx : 0 < x) (hxt : ∀ i, x ≠ t i) (hτ : 0 < τ) :
    Remainder p t x τ ↔ τ = point t x := by
  have hid := poly_identity t p hinj ht hint x
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx.ne'
  have hWpos : 0 < ∏ i : Fin n, (x - t i) ^ 2 :=
    Finset.prod_pos fun i _ => sq_pos_of_ne_zero (sub_ne_zero.mpr (hxt i))
  have hPpos : 0 < ∏ i : Fin n, (t i) ^ 2 :=
    Finset.prod_pos fun i _ => sq_pos_of_pos (ht i)
  have hSnonneg : 0 ≤ ∑ i : Fin n, (t i)⁻¹ :=
    Finset.sum_nonneg fun i _ => inv_nonneg.mpr (ht i).le
  have hden_pos : 0 < 1 + 2 * x * ∑ i : Fin n, (t i)⁻¹ := by nlinarith
  have hbase_pos :
      0 < ((2 * n + 1 : ℕ) : ℝ) * x ^ 2 * (∏ i, (t i) ^ 2) / (1 + 2 * x * ∑ i, (t i)⁻¹) := by
    positivity
  have hrem_iff :
      Remainder p t x τ ↔
        τ ^ (2 * n + 2) =
          ((2 * n + 1 : ℕ) : ℝ) * x ^ 2 * (∏ i, (t i) ^ 2) / (1 + 2 * x * ∑ i, (t i)⁻¹) := by
    unfold Remainder
    have hdiff : 1 / x ^ 2 - p.eval x =
        (1 + 2 * x * ∑ i, (t i)⁻¹) / (x ^ 2 * ∏ i, (t i) ^ 2) * ∏ i, (x - t i) ^ 2 := by
      have h1 : 1 / x ^ 2 - p.eval x = (1 - x ^ 2 * p.eval x) / x ^ 2 := by
        field_simp [hx2]
      rw [h1, hid]
      field_simp [hx2, hPpos.ne']
    constructor
    · intro hr
      have heq : (1 + 2 * x * ∑ i, (t i)⁻¹) / (x ^ 2 * ∏ i, (t i) ^ 2) * ∏ i, (x - t i) ^ 2 =
          ((2 * n + 1 : ℕ) : ℝ) / τ ^ (2 * n + 2) * ∏ i, (x - t i) ^ 2 := by
        linarith
      have hcancel := mul_right_cancel₀ hWpos.ne' heq
      have hτp : τ ^ (2 * n + 2) ≠ 0 := pow_ne_zero _ hτ.ne'
      field_simp [hx2, hPpos.ne', hden_pos.ne', hτp] at hcancel ⊢
      linarith
    · intro hpow
      have hτp : τ ^ (2 * n + 2) ≠ 0 := pow_ne_zero _ hτ.ne'
      have hcoeff : ((2 * n + 1 : ℕ) : ℝ) / τ ^ (2 * n + 2) =
          (1 + 2 * x * ∑ i, (t i)⁻¹) / (x ^ 2 * ∏ i, (t i) ^ 2) := by
        rw [hpow]
        field_simp [hx2, hPpos.ne', hden_pos.ne']
      rw [hcoeff]
      linarith
  rw [hrem_iff]
  have hpoint_pow :
      (point t x) ^ (2 * n + 2) =
        ((2 * n + 1 : ℕ) : ℝ) * x ^ 2 * (∏ i, (t i) ^ 2) / (1 + 2 * x * ∑ i, (t i)⁻¹) := by
    unfold point
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_pos.le]
    have hne : ((2 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [inv_mul_cancel₀ hne, Real.rpow_one]
  have hpoint_pos : 0 < point t x := by
    unfold point
    exact Real.rpow_pos_of_pos hbase_pos _
  constructor
  · intro hpow
    have heq : τ ^ (2 * n + 2) = (point t x) ^ (2 * n + 2) := hpow.trans hpoint_pow.symm
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (pow_lt_pow_left₀ hlt hτ.le (by omega)).ne heq
    · exact (pow_lt_pow_left₀ hgt hpoint_pos.le (by omega)).ne heq.symm
  · intro h
    rw [h, hpoint_pow]

lemma point_div_pow_bounds {n : ℕ} {ε x : ℝ} {t : Fin n → ℝ}
    (hε : 0 < ε) (hxε : ε ≤ x) (htε : ∀ i, ε ≤ t i) :
    scale ε x t ≤ (point t x / ε) ^ (2 * n + 2) ∧
      (point t x / ε) ^ (2 * n + 2) ≤ ((2 * n + 1 : ℕ) : ℝ) * (scale ε x t) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le hε hxε
  have htpos : ∀ i, 0 < t i := fun i => lt_of_lt_of_le hε (htε i)
  have hSnonneg : 0 ≤ ∑ i : Fin n, (t i)⁻¹ :=
    Finset.sum_nonneg fun i _ => inv_nonneg.mpr (htpos i).le
  have hden_pos : 0 < 1 + 2 * x * ∑ i : Fin n, (t i)⁻¹ := by nlinarith
  have hPpos : 0 < ∏ i : Fin n, (t i) ^ 2 :=
    Finset.prod_pos fun i _ => sq_pos_of_pos (htpos i)
  have hbase_pos :
      0 < ((2 * n + 1 : ℕ) : ℝ) * x ^ 2 * (∏ i, (t i) ^ 2) / (1 + 2 * x * ∑ i, (t i)⁻¹) := by
    positivity
  have hpoint_pow :
      (point t x) ^ (2 * n + 2) =
        ((2 * n + 1 : ℕ) : ℝ) * x ^ 2 * (∏ i, (t i) ^ 2) / (1 + 2 * x * ∑ i, (t i)⁻¹) := by
    unfold point
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_pos.le]
    have hne : ((2 * n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [inv_mul_cancel₀ hne, Real.rpow_one]
  have hprod_div : (∏ i : Fin n, (t i) ^ 2) / ε ^ (2 * n) = ∏ i : Fin n, (t i / ε) ^ 2 := by
    have hεp : ε ^ (2 * n) = ∏ _i : Fin n, ε ^ 2 := by
      rw [Finset.prod_const, Finset.card_fin, ← pow_mul]
    rw [hεp, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun i _ => by rw [div_pow]
  have hrew :
      (point t x / ε) ^ (2 * n + 2) =
        ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * (∏ i, (t i / ε) ^ 2) /
          (1 + 2 * x * ∑ i, (t i)⁻¹) := by
    rw [div_pow, hpoint_pow, ← hprod_div]
    have hpow_split : ε ^ (2 * n + 2) = ε ^ 2 * ε ^ (2 * n) := by
      rw [pow_add, mul_comm]
    rw [hpow_split]
    field_simp [hε.ne', hden_pos.ne']
  have hx1 : 1 ≤ x / ε := (one_le_div hε).mpr hxε
  have ht1 : ∀ i, 1 ≤ t i / ε := fun i => (one_le_div hε).mpr (htε i)
  have hprod1 : 1 ≤ ∏ i : Fin n, (t i / ε) ^ 2 :=
    Finset.one_le_prod fun i _ => one_le_pow₀ (ht1 i)
  have hden_le : 1 + 2 * x * ∑ i : Fin n, (t i)⁻¹ ≤ ((2 * n + 1 : ℕ) : ℝ) * (x / ε) := by
    have hsum_le : ∑ i : Fin n, ε * (t i)⁻¹ ≤ (n : ℝ) := by
      calc
        ∑ i : Fin n, ε * (t i)⁻¹ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_inv_le_iff₀ (htpos i), one_mul]
          exact htε i
        _ = (n : ℝ) := by simp
    have h2 : 2 * x * ∑ i : Fin n, (t i)⁻¹ = 2 * (x / ε) * ∑ i : Fin n, ε * (t i)⁻¹ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by field_simp [hε.ne']
    rw [h2]
    push_cast
    nlinarith
  have hden_ge1 : 1 ≤ 1 + 2 * x * ∑ i : Fin n, (t i)⁻¹ := by nlinarith
  rw [hrew]
  constructor
  · unfold scale
    rw [le_div_iff₀ hden_pos]
    calc
      (x / ε) * (∏ i, (t i / ε) ^ 2) * (1 + 2 * x * ∑ i, (t i)⁻¹)
          ≤ (x / ε) * (∏ i, (t i / ε) ^ 2) * (((2 * n + 1 : ℕ) : ℝ) * (x / ε)) := by
            gcongr
      _ = ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * ∏ i, (t i / ε) ^ 2 := by ring
  · unfold scale
    have hle1 :
        ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * (∏ i, (t i / ε) ^ 2) /
          (1 + 2 * x * ∑ i, (t i)⁻¹) ≤
        ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * (∏ i, (t i / ε) ^ 2) := by
      exact div_le_self (by positivity) hden_ge1
    calc
      ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * (∏ i, (t i / ε) ^ 2) /
          (1 + 2 * x * ∑ i, (t i)⁻¹)
          ≤ ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * (∏ i, (t i / ε) ^ 2) := hle1
      _ ≤ ((2 * n + 1 : ℕ) : ℝ) * (x / ε) ^ 2 * (∏ i, (t i / ε) ^ 2) ^ 2 := by
            have hpsq : ∏ i : Fin n, (t i / ε) ^ 2 ≤ (∏ i : Fin n, (t i / ε) ^ 2) ^ 2 := by
              nlinarith
            gcongr
      _ = ((2 * n + 1 : ℕ) : ℝ) * ((x / ε) * ∏ i, (t i / ε) ^ 2) ^ 2 := by ring

lemma part2 (n : ℕ) (ε x : ℕ → ℝ) (t : ℕ → Fin n → ℝ)
    (_hε0 : Tendsto ε atTop (𝓝 0))
    (hbnd : ∀ j, 0 < ε j ∧ ε j ≤ x j ∧ x j ≤ 1 ∧ ∀ i, ε j ≤ t j i ∧ t j i ≤ 1) :
    Tendsto (fun j => point (t j) (x j) / ε j) atTop atTop ↔
      Tendsto (fun j => scale (ε j) (x j) (t j)) atTop atTop := by
  have hb : ∀ j,
      scale (ε j) (x j) (t j) ≤ (point (t j) (x j) / ε j) ^ (2 * n + 2) ∧
        (point (t j) (x j) / ε j) ^ (2 * n + 2) ≤
          ((2 * n + 1 : ℕ) : ℝ) * (scale (ε j) (x j) (t j)) ^ 2 := fun j =>
    point_div_pow_bounds (hbnd j).1 (hbnd j).2.1 (fun i => ((hbnd j).2.2.2 i).1)
  have hpoint_pos : ∀ j, 0 ≤ point (t j) (x j) / ε j := by
    intro j
    have hε := (hbnd j).1
    have hx := lt_of_lt_of_le hε (hbnd j).2.1
    have ht : ∀ i, 0 < t j i := fun i => lt_of_lt_of_le hε ((hbnd j).2.2.2 i).1
    have hS : 0 ≤ ∑ i : Fin n, (t j i)⁻¹ := Finset.sum_nonneg fun i _ => inv_nonneg.mpr (ht i).le
    have hden : 0 < 1 + 2 * x j * ∑ i : Fin n, (t j i)⁻¹ := by nlinarith
    have hP : 0 < ∏ i : Fin n, (t j i) ^ 2 := Finset.prod_pos fun i _ => sq_pos_of_pos (ht i)
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) hε.le
  have hscale_nonneg : ∀ j, 0 ≤ scale (ε j) (x j) (t j) := by
    intro j
    have hε := (hbnd j).1
    have hx := lt_of_lt_of_le hε (hbnd j).2.1
    unfold scale
    exact mul_nonneg (div_nonneg hx.le hε.le) (Finset.prod_nonneg fun i _ => sq_nonneg _)
  constructor
  · intro hpt
    rw [tendsto_atTop_atTop] at hpt ⊢
    intro M
    let C : ℝ := ((2 * n + 1 : ℕ) : ℝ)
    have hCpos : 0 < C := by positivity
    let B : ℝ := max 1 (C * (max M 1) ^ 2)
    obtain ⟨N, hN⟩ := hpt B
    refine ⟨N, fun j hj => ?_⟩
    have h1 : B ≤ point (t j) (x j) / ε j := hN j hj
    have hB1 : 1 ≤ B := le_max_left _ _
    have hpow_ge : B ≤ (point (t j) (x j) / ε j) ^ (2 * n + 2) := by
      calc
        B ≤ B ^ (2 * n + 2) := le_self_pow₀ hB1 (by omega)
        _ ≤ (point (t j) (x j) / ε j) ^ (2 * n + 2) := by gcongr
    have h2 : C * (max M 1) ^ 2 ≤ C * (scale (ε j) (x j) (t j)) ^ 2 :=
      le_trans (le_max_right _ _) (le_trans hpow_ge (hb j).2)
    have h3 : (max M 1) ^ 2 ≤ (scale (ε j) (x j) (t j)) ^ 2 :=
      le_of_mul_le_mul_left h2 hCpos
    have h4 : max M 1 ≤ scale (ε j) (x j) (t j) := by
      nlinarith [hscale_nonneg j, le_max_right M 1]
    exact le_trans (le_max_left M 1) h4
  · intro hsc
    rw [tendsto_atTop_atTop] at hsc ⊢
    intro M
    let B : ℝ := (max M 1) ^ (2 * n + 2)
    obtain ⟨N, hN⟩ := hsc B
    refine ⟨N, fun j hj => ?_⟩
    have h1 : (max M 1) ^ (2 * n + 2) ≤ (point (t j) (x j) / ε j) ^ (2 * n + 2) :=
      le_trans (hN j hj) (hb j).1
    have h2 : max M 1 ≤ point (t j) (x j) / ε j := by
      by_contra hlt
      push Not at hlt
      have hpow_lt : (point (t j) (x j) / ε j) ^ (2 * n + 2) < (max M 1) ^ (2 * n + 2) :=
        pow_lt_pow_left₀ hlt (hpoint_pos j) (by omega)
      linarith
    exact le_trans (le_max_left M 1) h2

end OMA.Mo221284

theorem OMA.solution : type_of% @OMA.S_mo_221284.main :=
  ⟨OMA.Mo221284.part1, OMA.Mo221284.part2⟩
