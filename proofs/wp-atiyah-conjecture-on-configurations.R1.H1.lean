import OMAReductions.R_wp_atiyah_conjecture_on_configurations_R1
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Proof of `wp-atiyah-conjecture-on-configurations.R1.H1`

Proves Atiyah's collinear case (2001): for any `n` distinct collinear points
`p j = c + t j • u` (`u ≠ 0`) in `ℝ³`, `(configurationMatrix p).det ≠ 0`.

1. Positive scaling `s > 0` scales `directionFactor d` by a nonzero constant (`1` if `d` points
   to the north pole, `s` otherwise).
2. Hence the `i`-th column polynomial `P i = ∏ j ∈ univ.erase i, directionFactor (p j - p i)`
   equals `C (λ i) * F ^ (a i) * G ^ (n - 1 - a i)` where `F = directionFactor u`,
   `G = directionFactor (-u)`, `λ i ≠ 0`, and `a i = #{j | t i < t j}` is a bijection
   `Fin n → Fin n`.
3. Because `u ≠ 0`, either one of `F, G` is `1` and the other is `C (2 * r) * X`, or both have
   degree `1` with distinct roots `z₁ ≠ z₂`. In every case `{F ^ k * G ^ (n - 1 - k)}` is
   linearly independent over `ℂ`, and every `P i` has degree `< n`, so `configurationMatrix p`
   has trivial kernel and nonzero determinant.
-/

namespace WpAtiyahR1H1Proof

open OMA.S_wp_atiyah_conjecture_on_configurations Polynomial Finset

private lemma directionFactor_smul {s : ℝ} (hs : 0 < s) (d : Fin 3 → ℝ) :
    ∃ α : ℂ, α ≠ 0 ∧ directionFactor (s • d) = C α * directionFactor d := by
  unfold directionFactor
  have hnorm : Real.sqrt ((s * d 0) ^ 2 + (s * d 1) ^ 2 + (s * d 2) ^ 2) =
      s * Real.sqrt ((d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2) := by
    have h1 : (s * d 0) ^ 2 + (s * d 1) ^ 2 + (s * d 2) ^ 2 =
        s ^ 2 * ((d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2) := by ring
    rw [h1, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs_ne
  simp only [Pi.smul_apply, smul_eq_mul, hnorm]
  by_cases h : Real.sqrt ((d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2) = d 2
  · have h' : s * Real.sqrt ((d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2) = s * d 2 := by rw [h]
    rw [if_pos h', if_pos h]
    exact ⟨1, one_ne_zero, by simp⟩
  · have h' : s * Real.sqrt ((d 0) ^ 2 + (d 1) ^ 2 + (d 2) ^ 2) ≠ s * d 2 := fun heq =>
      h (mul_left_cancel₀ hs_ne heq)
    rw [if_neg h', if_neg h]
    refine ⟨(s : ℂ), hsC, ?_⟩
    push_cast
    simp only [map_sub, map_mul, map_add]
    ring

private lemma directionFactor_natDegree_le_one (d : Fin 3 → ℝ) :
    (directionFactor d).natDegree ≤ 1 := by
  unfold directionFactor
  dsimp only
  split_ifs
  · simp
  · refine (natDegree_sub_le _ _).trans (max_le ?_ (by rw [natDegree_C]; omega))
    exact (natDegree_C_mul_le _ _).trans (by simp)

private lemma natDegree_prod_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ 1) :
    (∏ i ∈ s, f i).natDegree ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    exact (natDegree_mul_le).trans (by omega)

private lemma linear_indep_pow_prod {n : ℕ} {F G : Polynomial ℂ}
    (hFG : (F = 1 ∧ ∃ a : ℂ, a ≠ 0 ∧ G = C a * X) ∨
      (G = 1 ∧ ∃ a : ℂ, a ≠ 0 ∧ F = C a * X) ∨
      (F ≠ 0 ∧ ∃ z : ℂ, F.eval z = 0 ∧ G.eval z ≠ 0))
    (c : Fin n → ℂ)
    (hsum : ∑ k : Fin n, C (c k) * (F ^ k.val * G ^ (n - 1 - k.val)) = 0) :
    ∀ k : Fin n, c k = 0 := by
  rcases hFG with ⟨rfl, a, ha, rfl⟩ | ⟨rfl, a, ha, rfl⟩ | ⟨hFne, z, hFz, hGz⟩
  · intro k
    have hcoeff := congrArg (fun P => P.coeff (n - 1 - k.val)) hsum
    rw [coeff_zero, finsetSum_coeff] at hcoeff
    have hterm : ∀ j : Fin n,
        (C (c j) * ((1 : Polynomial ℂ) ^ j.val * (C a * X) ^ (n - 1 - j.val))).coeff (n - 1 - k.val) =
        if j = k then c k * a ^ (n - 1 - k.val) else 0 := by
      intro j
      rw [one_pow, one_mul, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul, coeff_X_pow]
      by_cases hjk : j = k
      · subst hjk
        simp
      · have hne : n - 1 - k.val ≠ n - 1 - j.val := by
          intro heq
          apply hjk
          exact Fin.ext (by omega)
        simp [hjk, hne]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right (pow_ne_zero _ ha)
  · intro k
    have hcoeff := congrArg (fun P => P.coeff k.val) hsum
    rw [coeff_zero, finsetSum_coeff] at hcoeff
    have hterm : ∀ j : Fin n,
        (C (c j) * ((C a * X) ^ j.val * (1 : Polynomial ℂ) ^ (n - 1 - j.val))).coeff k.val =
        if j = k then c k * a ^ k.val else 0 := by
      intro j
      rw [one_pow, mul_one, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, coeff_C_mul, coeff_X_pow]
      by_cases hjk : j = k
      · subst hjk
        simp
      · have hne : k.val ≠ j.val := fun h => hjk (Fin.ext h.symm)
        simp [hjk, hne]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hcoeff
    exact (mul_eq_zero.mp hcoeff).resolve_right (pow_ne_zero _ ha)
  · suffices ∀ m : ℕ, ∀ k : Fin n, k.val < m → c k = 0 from fun k => this n k k.isLt
    intro m
    induction m with
    | zero => intro k hk; omega
    | succ m ih =>
      intro k hk
      by_cases hkm : k.val < m
      · exact ih k hkm
      · have hkeq : k.val = m := by omega
        have hsum' : ∑ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.val),
            C (c j) * (F ^ j.val * G ^ (n - 1 - j.val)) = 0 := by
          rw [← hsum]
          refine Finset.sum_subset (Finset.filter_subset _ _) fun j _ hj => ?_
          have hlt : j.val < m := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
            exact hj
          rw [ih j hlt, map_zero, zero_mul]
        have hfactor : ∑ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.val),
            C (c j) * (F ^ j.val * G ^ (n - 1 - j.val)) =
            F ^ m * ∑ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.val),
              C (c j) * (F ^ (j.val - m) * G ^ (n - 1 - j.val)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hmj : m ≤ j.val := (Finset.mem_filter.mp hj).2
          have hpow : F ^ j.val = F ^ m * F ^ (j.val - m) := by
            rw [← pow_add, Nat.add_sub_cancel' hmj]
          rw [hpow]
          ring
        rw [hfactor] at hsum'
        have hinner : ∑ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.val),
            C (c j) * (F ^ (j.val - m) * G ^ (n - 1 - j.val)) = 0 :=
          (mul_eq_zero.mp hsum').resolve_left (pow_ne_zero m hFne)
        have hev := congrArg (Polynomial.eval z) hinner
        rw [eval_zero, eval_finsetSum] at hev
        have hterm : ∀ j ∈ Finset.univ.filter (fun j : Fin n => m ≤ j.val),
            (C (c j) * (F ^ (j.val - m) * G ^ (n - 1 - j.val))).eval z =
            if j = k then c k * (G.eval z) ^ (n - 1 - k.val) else 0 := by
          intro j hj
          have hmj : m ≤ j.val := (Finset.mem_filter.mp hj).2
          simp only [eval_mul, eval_C, eval_pow]
          by_cases hjk : j = k
          · subst hjk
            simp [hkeq]
          · have hgt : 0 < j.val - m := by
              have hne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
              omega
            rw [hFz, zero_pow (Nat.ne_of_gt hgt), zero_mul, mul_zero, if_neg hjk]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq',
          if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ k, by omega⟩)] at hev
        exact (mul_eq_zero.mp hev).resolve_right (pow_ne_zero _ hGz)

private lemma fg_trichotomy {u : Fin 3 → ℝ} (hu : u ≠ 0) :
    (directionFactor u = 1 ∧ ∃ a : ℂ, a ≠ 0 ∧ directionFactor (-u) = C a * X) ∨
    (directionFactor (-u) = 1 ∧ ∃ a : ℂ, a ≠ 0 ∧ directionFactor u = C a * X) ∨
    (directionFactor u ≠ 0 ∧ ∃ z : ℂ, (directionFactor u).eval z = 0 ∧ (directionFactor (-u)).eval z ≠ 0) := by
  set r := Real.sqrt ((u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2)
  have hsq_pos : 0 < (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 := by
    have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 ∨ u 2 ≠ 0 := by
      by_contra h
      push Not at h
      apply hu
      ext i
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    rcases hne with h0 | h1 | h2
    · positivity
    · positivity
    · positivity
  have hr_pos : 0 < r := Real.sqrt_pos.mpr hsq_pos
  have hr_sq : r ^ 2 = (u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 := Real.sq_sqrt hsq_pos.le
  have hr_neg : Real.sqrt (((-u) 0) ^ 2 + ((-u) 1) ^ 2 + ((-u) 2) ^ 2) = r := by
    simp [r]
  by_cases hnorth : r = u 2
  · left
    have h01 : u 0 = 0 ∧ u 1 = 0 := by
      have hsum0 : (u 0) ^ 2 + (u 1) ^ 2 = 0 := by nlinarith [hr_sq, hnorth]
      constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
    refine ⟨by unfold directionFactor; rw [if_pos hnorth], ((2 * r : ℝ) : ℂ),
      Complex.ofReal_ne_zero.mpr (by linarith), ?_⟩
    unfold directionFactor
    rw [hr_neg]
    have hne : r ≠ (-u) 2 := by simp only [Pi.neg_apply]; linarith
    rw [if_neg hne]
    simp only [Pi.neg_apply, h01.1, h01.2, neg_zero, Complex.ofReal_zero, zero_mul, add_zero,
      map_zero, sub_zero]
    have hx : r - -u 2 = 2 * r := by linarith
    rw [hx]
  · by_cases hsouth : r = -u 2
    · right; left
      have h01 : u 0 = 0 ∧ u 1 = 0 := by
        have hsum0 : (u 0) ^ 2 + (u 1) ^ 2 = 0 := by nlinarith [hr_sq, hsouth]
        constructor <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
      refine ⟨by unfold directionFactor; rw [hr_neg]; dsimp only; rw [if_pos (show r = (-u) 2 from hsouth)], ((2 * r : ℝ) : ℂ),
        Complex.ofReal_ne_zero.mpr (by linarith), ?_⟩
      unfold directionFactor
      try dsimp only
      rw [if_neg hnorth]
      have hr_def : Real.sqrt ((u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2) = r := rfl
      have hb : ((u 0 : ℂ) + (u 1 : ℂ) * Complex.I) = 0 := by simp [h01.1, h01.2]
      rw [hb, map_zero, sub_zero]
      have hx : r - u 2 = 2 * r := by linarith
      rw [hr_def, hx]
    · right; right
      have ha1_pos : 0 < r - u 2 := by
        have hle : u 2 ≤ r := by nlinarith [hr_sq, sq_nonneg (u 0), sq_nonneg (u 1)]
        exact sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm hnorth))
      have ha2_pos : 0 < r + u 2 := by
        have hle : -u 2 ≤ r := by nlinarith [hr_sq, sq_nonneg (u 0), sq_nonneg (u 1)]
        have : -u 2 < r := lt_of_le_of_ne hle (Ne.symm hsouth)
        linarith
      have hb_ne : ((u 0 : ℂ) + (u 1 : ℂ) * Complex.I) ≠ 0 := by
        intro hz
        have hre := congrArg Complex.re hz
        have him := congrArg Complex.im hz
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero, Complex.zero_re] at hre
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.zero_im] at him
        have hsq2 : r ^ 2 = (u 2) ^ 2 := by rw [hr_sq, hre, him]; ring
        have hfac : (r - u 2) * (r + u 2) = 0 := by nlinarith
        rcases mul_eq_zero.mp hfac with h1 | h2 <;> linarith
      set a₁ : ℂ := ((r - u 2 : ℝ) : ℂ)
      set a₂ : ℂ := ((r + u 2 : ℝ) : ℂ)
      set b : ℂ := (u 0 : ℂ) + (u 1 : ℂ) * Complex.I
      have ha1_ne : a₁ ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha1_pos)
      have ha2_ne : a₂ ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha2_pos)
      have hF : directionFactor u = C a₁ * X - C b := by
        unfold directionFactor
        rw [if_neg hnorth]
      have hG : directionFactor (-u) = C a₂ * X + C b := by
        unfold directionFactor
        rw [hr_neg]
        have hne : r ≠ (-u) 2 := by simpa using hsouth
        rw [if_neg hne]
        simp only [Pi.neg_apply, Complex.ofReal_neg, a₂, b]
        have hrsub : ((r - -u 2 : ℝ) : ℂ) = ((r + u 2 : ℝ) : ℂ) := by congr 1; ring
        rw [hrsub, sub_eq_add_neg, ← map_neg]
        congr 2
        ring
      have hF_ne : directionFactor u ≠ 0 := by
        intro h0
        have hc := congrArg (fun P => P.coeff 1) (hF.symm.trans h0)
        simp only [coeff_sub, coeff_C_mul, coeff_X_one, mul_one, coeff_C, one_ne_zero, ↓reduceIte,
          sub_zero, coeff_zero] at hc
        exact ha1_ne hc
      refine ⟨hF_ne, b / a₁, ?_, ?_⟩
      · simp only [hF, eval_sub, eval_mul, eval_C, eval_X]
        rw [mul_div_cancel₀ _ ha1_ne, sub_self]
      · simp only [hG, eval_add, eval_mul, eval_C, eval_X]
        have hsum_ne : a₁ + a₂ ≠ 0 := by
          dsimp [a₁, a₂]
          rw [← Complex.ofReal_add]
          exact Complex.ofReal_ne_zero.mpr (by linarith)
        have hval : a₂ * (b / a₁) + b = b * (a₁ + a₂) / a₁ := by
          field_simp [ha1_ne]
          ring
        rw [hval]
        exact div_ne_zero (mul_ne_zero hb_ne hsum_ne) ha1_ne

end WpAtiyahR1H1Proof

theorem OMA.solution : OMA.R_wp_atiyah_conjecture_on_configurations_R1.H1 := by
  classical
  open OMA.S_wp_atiyah_conjecture_on_configurations Polynomial in
  intro n p hp ⟨c, u, t, hu, hcol⟩
  by_cases hn0 : n = 0
  · subst hn0
    simp
  have ht_inj : Function.Injective t := by
    intro i j hij
    apply hp
    rw [hcol i, hcol j, hij]
  let a : Fin n → Fin n := fun i =>
    ⟨(Finset.univ.filter (fun j : Fin n => t i < t j)).card, by
      have hsub : Finset.univ.filter (fun j : Fin n => t i < t j) ⊆ Finset.univ.erase i := by
        intro j hj
        rw [Finset.mem_filter] at hj
        exact Finset.mem_erase.mpr ⟨fun h => lt_irrefl _ (h ▸ hj.2), Finset.mem_univ j⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at hle
      omega⟩
  have ha_inj : Function.Injective a := by
    intro i j hij
    have hcard : (Finset.univ.filter (fun k : Fin n => t i < t k)).card =
        (Finset.univ.filter (fun k : Fin n => t j < t k)).card := congrArg Fin.val hij
    by_contra hne
    have htne : t i ≠ t j := fun h => hne (ht_inj h)
    rcases lt_or_gt_of_ne htne with hlt | hgt
    · have hss : Finset.univ.filter (fun k : Fin n => t j < t k) ⊂
          Finset.univ.filter (fun k : Fin n => t i < t k) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k,
            hlt.trans (Finset.mem_filter.mp hk).2⟩, fun heq => ?_⟩
        have hjmem : j ∈ Finset.univ.filter (fun k : Fin n => t i < t k) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hlt⟩
        rw [← heq, Finset.mem_filter] at hjmem
        exact lt_irrefl _ hjmem.2
      exact absurd hcard (ne_of_gt (Finset.card_lt_card hss))
    · have hss : Finset.univ.filter (fun k : Fin n => t i < t k) ⊂
          Finset.univ.filter (fun k : Fin n => t j < t k) := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ k,
            hgt.trans (Finset.mem_filter.mp hk).2⟩, fun heq => ?_⟩
        have himem : i ∈ Finset.univ.filter (fun k : Fin n => t j < t k) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hgt⟩
        rw [← heq, Finset.mem_filter] at himem
        exact lt_irrefl _ himem.2
      exact absurd hcard (ne_of_lt (Finset.card_lt_card hss))
  have ha_bij : Function.Bijective a := (Finite.injective_iff_bijective).mp ha_inj
  let aEquiv : Fin n ≃ Fin n := Equiv.ofBijective a ha_bij
  set F := directionFactor u
  set G := directionFactor (-u)
  have hP_form : ∀ i : Fin n, ∃ lam : ℂ, lam ≠ 0 ∧
      (∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i)) =
        C lam * (F ^ (a i).val * G ^ (n - 1 - (a i).val)) := by
    intro i
    set Spos := Finset.univ.filter (fun j : Fin n => t i < t j)
    set Sneg := Finset.univ.filter (fun j : Fin n => t j < t i)
    have hunion : Spos ∪ Sneg = Finset.univ.erase i := by
      ext j
      simp only [Spos, Sneg, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true]
      constructor
      · rintro (h | h) <;> rintro rfl <;> exact lt_irrefl _ h
      · intro hne
        exact lt_or_gt_of_ne (fun h => hne (ht_inj h.symm))
    have hdisj : Disjoint Spos Sneg := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hcard_neg : Sneg.card = n - 1 - (a i).val := by
      have htot := Finset.card_union_of_disjoint hdisj
      rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at htot
      have ha_eq : Spos.card = (a i).val := rfl
      omega
    have hpos_fac : ∀ j ∈ Spos, ∃ α : ℂ, α ≠ 0 ∧ directionFactor (p j - p i) = C α * F := by
      intro j hj
      have hlt : t i < t j := (Finset.mem_filter.mp hj).2
      have hdiff : p j - p i = (t j - t i) • u := by
        rw [hcol j, hcol i]; ext k; simp; ring
      rw [hdiff]
      exact WpAtiyahR1H1Proof.directionFactor_smul (sub_pos.mpr hlt) u
    have hneg_fac : ∀ j ∈ Sneg, ∃ α : ℂ, α ≠ 0 ∧ directionFactor (p j - p i) = C α * G := by
      intro j hj
      have hlt : t j < t i := (Finset.mem_filter.mp hj).2
      have hdiff : p j - p i = (t i - t j) • (-u) := by
        rw [hcol j, hcol i]; ext k; simp; ring
      rw [hdiff]
      exact WpAtiyahR1H1Proof.directionFactor_smul (sub_pos.mpr hlt) (-u)
    choose αp hαp_ne hαp_eq using hpos_fac
    choose αn hαn_ne hαn_eq using hneg_fac
    let lp : ℂ := ∏ j ∈ Spos.attach, αp j.1 j.2
    let ln : ℂ := ∏ j ∈ Sneg.attach, αn j.1 j.2
    have hlp_ne : lp ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hαp_ne j.1 j.2
    have hln_ne : ln ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hαn_ne j.1 j.2
    refine ⟨lp * ln, mul_ne_zero hlp_ne hln_ne, ?_⟩
    rw [← hunion, Finset.prod_union hdisj]
    have hprod_p : ∏ j ∈ Spos, directionFactor (p j - p i) = C lp * F ^ (a i).val := by
      rw [← Finset.prod_attach Spos]
      have hcongr : ∏ j ∈ Spos.attach, directionFactor (p j.1 - p i) =
          ∏ j ∈ Spos.attach, (C (αp j.1 j.2) * F) :=
        Finset.prod_congr rfl fun j _ => hαp_eq j.1 j.2
      rw [hcongr, Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Finset.card_attach]
    have hprod_n : ∏ j ∈ Sneg, directionFactor (p j - p i) = C ln * G ^ (n - 1 - (a i).val) := by
      rw [← Finset.prod_attach Sneg]
      have hcongr : ∏ j ∈ Sneg.attach, directionFactor (p j.1 - p i) =
          ∏ j ∈ Sneg.attach, (C (αn j.1 j.2) * G) :=
        Finset.prod_congr rfl fun j _ => hαn_eq j.1 j.2
      rw [hcongr, Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Finset.card_attach, hcard_neg]
    rw [hprod_p, hprod_n, map_mul]
    ring
  choose lam hlam_ne hP_eq using hP_form
  intro hdet
  obtain ⟨v, hv_ne, hv_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hpoly_zero : ∑ i : Fin n, C (v i) * ∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i) = 0 := by
    ext d
    rw [coeff_zero, finsetSum_coeff]
    by_cases hd : d < n
    · have hrow := congrFun hv_mul ⟨d, hd⟩
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, configurationMatrix] at hrow
      simpa only [coeff_C_mul, mul_comm] using hrow
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [coeff_C_mul]
      have hdeg : (∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i)).natDegree ≤ n - 1 := by
        have h1 := WpAtiyahR1H1Proof.natDegree_prod_le (Finset.univ.erase i)
          (fun j => directionFactor (p j - p i))
          (fun j _ => WpAtiyahR1H1Proof.directionFactor_natDegree_le_one _)
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin] at h1
        exact h1
      have hzero : (∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i)).coeff d = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hzero, mul_zero]
  have hreidx : ∑ k : Fin n, C (v (aEquiv.symm k)) *
        ∏ j ∈ Finset.univ.erase (aEquiv.symm k), directionFactor (p j - p (aEquiv.symm k)) =
      ∑ i : Fin n, C (v i) * ∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i) :=
    Equiv.sum_comp aEquiv.symm (fun i => C (v i) * ∏ j ∈ Finset.univ.erase i, directionFactor (p j - p i))
  have hsum_k : ∑ k : Fin n, C (v (aEquiv.symm k) * lam (aEquiv.symm k)) *
      (F ^ k.val * G ^ (n - 1 - k.val)) = 0 := by
    rw [← hpoly_zero, ← hreidx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hP_eq (aEquiv.symm k), map_mul, mul_assoc]
    have ha_symm : a (aEquiv.symm k) = k := aEquiv.apply_symm_apply k
    rw [ha_symm]
  have hall0 := WpAtiyahR1H1Proof.linear_indep_pow_prod (WpAtiyahR1H1Proof.fg_trichotomy hu) _ hsum_k
  apply hv_ne
  funext i
  have hmul0 := hall0 (aEquiv i)
  rw [Equiv.symm_apply_apply] at hmul0
  exact (mul_eq_zero.mp hmul0).resolve_right (hlam_ne i)
