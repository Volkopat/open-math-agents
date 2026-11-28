import OMAReductions.R_Green68_green_68_variants_voloch_R2
import Mathlib

/-!
Direct proof of Green68.green_68.variants.voloch.R2.H2:
the Stöhr-Voloch point bound for absolutely irreducible plane curves of degree 

over ZMod p via the quadratic Veronese Frobenius-Wronskian polynomial H and
generic projective projection resultant multiplicity bounds.
-/

namespace VolochH2Proof

open MvPolynomial Finset
open scoped Classical

section HomogHelpers

lemma weight_one_eq_degree {σ : Type*} (m : σ →₀ ℕ) :
    Finsupp.weight (1 : σ → ℕ) m = Finsupp.degree m := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma isHomogeneous_sum_eq {K : Type*} [CommSemiring K] {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) {m : σ →₀ ℕ} (hm : m ∈ P.support) :
    ∑ i : σ, m i = d := by
  have h := hP (MvPolynomial.mem_support_iff.mp hm)
  rw [weight_one_eq_degree, Finsupp.degree_apply] at h
  rw [← h]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)).symm

lemma isHomogeneous_eval_smul {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) (c : K) (v : σ → K) :
    eval (c • v) P = c ^ d * eval v P := by
  rw [P.as_sum, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [eval_monomial, eval_monomial]
  have hdeg : ∑ i : σ, m i = d := isHomogeneous_sum_eq hP hm
  have hprod : (m.prod fun i e => (c * v i) ^ e) = c ^ d * (m.prod fun i e => v i ^ e) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
    calc ∏ i : σ, (c * v i) ^ m i
        = ∏ i : σ, (c ^ m i * v i ^ m i) := by
            apply Finset.prod_congr rfl; intro i _; exact mul_pow _ _ _
      _ = (∏ i : σ, c ^ m i) * (∏ i : σ, v i ^ m i) := Finset.prod_mul_distrib
      _ = c ^ (∑ i : σ, m i) * (∏ i : σ, v i ^ m i) := by rw [Finset.prod_pow_eq_pow_sum]
      _ = c ^ d * (∏ i : σ, v i ^ m i) := by rw [hdeg]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hprod]; ring

lemma isHomogeneous_zero_eq_C {K : Type*} [CommRing K] {σ : Type*} {P : MvPolynomial σ K}
    (hP : P.IsHomogeneous 0) : P = C (P.coeff 0) := by
  ext m
  rw [MvPolynomial.coeff_C]
  split_ifs with hm
  · subst hm; rfl
  · by_contra hne
    have h := hP hne
    rw [weight_one_eq_degree] at h
    apply hm
    ext i
    have hle : m i ≤ Finsupp.degree m := by
      rw [Finsupp.degree_apply]
      by_cases hi : i ∈ m.support
      · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      · rw [Finsupp.notMem_support_iff.mp hi]; exact Nat.zero_le _
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega

lemma isHomogeneous_pderiv {K : Type*} [CommRing K] {σ : Type*} [Fintype σ]
    {P : MvPolynomial σ K} {d : ℕ} (hP : P.IsHomogeneous d) (i : σ) :
    (MvPolynomial.pderiv i P).IsHomogeneous (d - 1) := by
  intro m hm
  rw [MvPolynomial.coeff_pderiv] at hm
  have hc : P.coeff (m + Finsupp.single i 1) ≠ 0 := left_ne_zero_of_mul hm
  have hd := hP hc
  rw [weight_one_eq_degree] at hd ⊢
  rw [map_add, Finsupp.degree_single] at hd
  omega

lemma euler_homog_fin3 {K : Type*} [CommRing K] {F : MvPolynomial (Fin 3) K} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    X 0 * MvPolynomial.pderiv 0 F + X 1 * MvPolynomial.pderiv 1 F +
      X 2 * MvPolynomial.pderiv 2 F = (d : MvPolynomial (Fin 3) K) * F := by
  ext m
  have hterm : ∀ i : Fin 3, (X i * MvPolynomial.pderiv i F).coeff m = (m i : K) * F.coeff m := by
    intro i
    rw [mul_comm, MvPolynomial.coeff_mul_X']
    split_ifs with hi
    · have hpos : 0 < m i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
      rw [MvPolynomial.coeff_pderiv]
      have hsub : (m - (Finsupp.single i 1 : Fin 3 →₀ ℕ)) + (Finsupp.single i 1 : Fin 3 →₀ ℕ) = m := by
        ext j
        by_cases hj : j = i
        · subst hj; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        · simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_of_ne hj]
      rw [hsub]
      have hmi : (m - (Finsupp.single i 1 : Fin 3 →₀ ℕ)) i + 1 = m i := by
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
      have hcast : (((m - (Finsupp.single i 1 : Fin 3 →₀ ℕ)) i : K) + 1) = (m i : K) := by
        rw [show (1 : K) = ((1 : ℕ) : K) from Nat.cast_one.symm, ← Nat.cast_add, hmi]
      rw [hcast]; ring
    · have hm0 : m i = 0 := Finsupp.notMem_support_iff.mp hi
      simp [hm0]
  change ((X 0 * MvPolynomial.pderiv 0 F + X 1 * MvPolynomial.pderiv 1 F) +
      X 2 * MvPolynomial.pderiv 2 F).coeff m = ((d : MvPolynomial (Fin 3) K) * F).coeff m
  rw [show ∀ A B : MvPolynomial (Fin 3) K, (A + B).coeff m = A.coeff m + B.coeff m from
    fun A B => MvPolynomial.coeff_add m A B]
  rw [show ∀ A B : MvPolynomial (Fin 3) K, (A + B).coeff m = A.coeff m + B.coeff m from
    fun A B => MvPolynomial.coeff_add m A B]
  rw [hterm 0, hterm 1, hterm 2]
  have hC : ((d : MvPolynomial (Fin 3) K) * F).coeff m = (d : K) * F.coeff m := by
    rw [show (d : MvPolynomial (Fin 3) K) = C (d : K) from by simp, MvPolynomial.coeff_C_mul]
  rw [hC]
  by_cases hm : m ∈ F.support
  · have hdeg := isHomogeneous_sum_eq hF hm
    rw [Fin.sum_univ_three] at hdeg
    have hcast : ((m 0 : K) + (m 1 : K) + (m 2 : K)) = (d : K) := by
      rw [← Nat.cast_add, ← Nat.cast_add, hdeg]
    linear_combination F.coeff m * hcast
  · rw [MvPolynomial.notMem_support_iff.mp hm]; ring

lemma resultant_isHomogeneous_general {K : Type*} [Field K]
    {f₀ f₁ : Polynomial (MvPolynomial (Fin 2) K)} {m d : ℕ}
    (hf0_h : ∀ k, k ≤ m → (f₀.coeff k).IsHomogeneous (m - k))
    (hf1_h : ∀ k, k ≤ d → (f₁.coeff k).IsHomogeneous (d - k)) :
    (Polynomial.resultant f₀ f₁ m d).IsHomogeneous (m * d) := by
  unfold Polynomial.resultant
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ _
  have hsign : ∀ (s : ℤˣ) (P : MvPolynomial (Fin 2) K), P.IsHomogeneous (m * d) →
      (s • P).IsHomogeneous (m * d) := by
    intro s P hP
    rcases Int.units_eq_one_or s with rfl | rfl
    · simpa using hP
    · simpa using hP.neg
  apply hsign
  -- sylvester f₀ f₁ m d has size (m + d) x (m + d): left m cols are f₁ (deg d), right d cols are f₀ (deg m)
  let base : Fin (m + d) → ℕ := fun j => if j.val < m then j.val else j.val - m
  let degcol : Fin (m + d) → ℕ := fun j => if j.val < m then d else m
  have hsylv_left : ∀ (i : Fin (m + d)) (j₁ : Fin m),
      (f₀.sylvester f₁ m d) i (Fin.castAdd d j₁) =
        if i.val ∈ Set.Icc j₁.val (j₁.val + d) then f₁.coeff (i.val - j₁.val) else 0 := by
    intro i j₁; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_left]
  have hsylv_right : ∀ (i : Fin (m + d)) (j₁ : Fin d),
      (f₀.sylvester f₁ m d) i (Fin.natAdd m j₁) =
        if i.val ∈ Set.Icc j₁.val (j₁.val + m) then f₀.coeff (i.val - j₁.val) else 0 := by
    intro i j₁; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_right]
  by_cases hall : ∀ j : Fin (m + d), (σ j).val ∈ Set.Icc (base j) (base j + degcol j)
  · have hterm_h : ∀ j : Fin (m + d),
        ((f₀.sylvester f₁ m d) (σ j) j).IsHomogeneous (degcol j + base j - (σ j).val) := by
      intro j
      by_cases hj : j.val < m
      · let j₁ : Fin m := ⟨j.val, hj⟩
        have hj_eq : j = Fin.castAdd d j₁ := Fin.ext rfl
        have hbase : base j = j₁.val := by simp [base, hj, j₁]
        have hdc : degcol j = d := by simp [degcol, hj]
        have hin : (σ j).val ∈ Set.Icc j₁.val (j₁.val + d) := by
          have := hall j; rwa [hbase, hdc] at this
        rw [hj_eq, hsylv_left, ← hj_eq]
        simp only [hin, ite_true, hbase, hdc]
        have hle : (σ j).val - j₁.val ≤ d := by have h1 := hin.1; have h2 := hin.2; omega
        have heq : d - ((σ j).val - j₁.val) = d + j₁.val - (σ j).val := by
          have h1 := hin.1; have h2 := hin.2; omega
        rw [← heq]
        exact hf1_h _ hle
      · let j₁ : Fin d := ⟨j.val - m, by omega⟩
        have hj_eq : j = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hbase : base j = j₁.val := by simp [base, hj, j₁]
        have hdc : degcol j = m := by simp [degcol, hj]
        have hin : (σ j).val ∈ Set.Icc j₁.val (j₁.val + m) := by
          have := hall j; rwa [hbase, hdc] at this
        rw [hj_eq, hsylv_right, ← hj_eq]
        simp only [hin, ite_true, hbase, hdc]
        have hle : (σ j).val - j₁.val ≤ m := by have h1 := hin.1; have h2 := hin.2; omega
        have heq : m - ((σ j).val - j₁.val) = m + j₁.val - (σ j).val := by
          have h1 := hin.1; have h2 := hin.2; omega
        rw [← heq]
        exact hf0_h _ hle
    have hprod := IsHomogeneous.prod univ (fun j => (f₀.sylvester f₁ m d) (σ j) j)
      (fun j => degcol j + base j - (σ j).val) (fun j _ => hterm_h j)
    have hsum_deg : ∑ j : Fin (m + d), (degcol j + base j - (σ j).val) = m * d := by
      have hadd : ∑ j : Fin (m + d), (degcol j + base j - (σ j).val) +
          ∑ j : Fin (m + d), (σ j).val = ∑ j : Fin (m + d), (degcol j + base j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have h2 := (hall j).2
        omega
      have hperm : ∑ j : Fin (m + d), (σ j).val = ∑ i : Fin (m + d), i.val :=
        Equiv.sum_comp σ (fun i : Fin (m + d) => i.val)
      have hsum_i : ∑ i : Fin (m + d), i.val =
          (∑ j₁ : Fin m, j₁.val) + (∑ j₁ : Fin d, (m + j₁.val)) := by
        rw [Fin.sum_univ_add]
        simp only [Fin.val_castAdd, Fin.val_natAdd]
      have hsum_b : ∑ j : Fin (m + d), (degcol j + base j) =
          (∑ j₁ : Fin m, (d + j₁.val)) + (∑ j₁ : Fin d, (m + j₁.val)) := by
        rw [Fin.sum_univ_add]
        congr 1
        · apply Finset.sum_congr rfl; intro j₁ _; simp [base, degcol, j₁.isLt]
        · apply Finset.sum_congr rfl; intro j₁ _; simp [base, degcol]
      have hdiff : ∑ j₁ : Fin m, (d + j₁.val) = m * d + ∑ j₁ : Fin m, j₁.val := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      omega
    rwa [hsum_deg] at hprod
  · have hex : ∃ j : Fin (m + d), (σ j).val ∉ Set.Icc (base j) (base j + degcol j) := by
      by_contra h; apply hall; intro j; exact not_not.mp (fun hj => h ⟨j, hj⟩)
    obtain ⟨j₀, hj₀⟩ := hex
    have hzero : (f₀.sylvester f₁ m d) (σ j₀) j₀ = 0 := by
      by_cases hj : j₀.val < m
      · let j₁ : Fin m := ⟨j₀.val, hj⟩
        have hj_eq : j₀ = Fin.castAdd d j₁ := Fin.ext rfl
        have hbase : base j₀ = j₁.val := by simp [base, hj, j₁]
        have hdc : degcol j₀ = d := by simp [degcol, hj]
        have hnot : (σ j₀).val ∉ Set.Icc j₁.val (j₁.val + d) := by simpa [hbase, hdc] using hj₀
        rw [hj_eq, hsylv_left, ← hj_eq]; simp [hnot]
      · let j₁ : Fin d := ⟨j₀.val - m, by omega⟩
        have hj_eq : j₀ = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hbase : base j₀ = j₁.val := by simp [base, hj, j₁]
        have hdc : degcol j₀ = m := by simp [degcol, hj]
        have hnot : (σ j₀).val ∉ Set.Icc j₁.val (j₁.val + m) := by simpa [hbase, hdc] using hj₀
        rw [hj_eq, hsylv_right, ← hj_eq]; simp [hnot]
    have hprod0 : (∏ i : Fin (m + d), (f₀.sylvester f₁ m d) (σ i) i) = 0 :=
      Finset.prod_eq_zero (mem_univ j₀) hzero
    rw [hprod0]
    exact isHomogeneous_zero _ _ _

lemma exists_notMem_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] (S : Finset K) :
    ∃ x : K, x ∉ S := by
  by_cases hS : S.Nonempty
  · let P : Polynomial K := (∏ s ∈ S, (Polynomial.X - Polynomial.C s)) + 1
    have hmon_prod : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).Monic :=
      Polynomial.monic_prod_of_monic S _ (fun s _ => Polynomial.monic_X_sub_C s)
    have hnd_prod : (∏ s ∈ S, (Polynomial.X - Polynomial.C s)).natDegree = S.card := by
      rw [Polynomial.natDegree_prod_of_monic S _ (fun s _ => Polynomial.monic_X_sub_C s)]
      simp
    have hnd_P : P.natDegree = S.card := by
      dsimp only [P]
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      · exact hnd_prod
      · rw [Polynomial.natDegree_one, hnd_prod]; exact card_pos.mpr hS
    have hP0 : P ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at hnd_P; have := card_pos.mpr hS; omega
    have hdeg : P.degree ≠ 0 := by
      rw [Polynomial.degree_eq_natDegree hP0, hnd_P]
      have hpos : 0 < S.card := card_pos.mpr hS
      intro h0
      have : S.card = 0 := by exact_mod_cast h0
      omega
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hdeg
    refine ⟨r, ?_⟩
    intro hrS
    rw [Polynomial.IsRoot.def] at hr
    dsimp only [P] at hr
    rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_prod] at hr
    have hprod0 : (∏ s ∈ S, Polynomial.eval r (Polynomial.X - Polynomial.C s)) = 0 := by
      apply Finset.prod_eq_zero hrS
      simp
    rw [hprod0, zero_add] at hr
    exact one_ne_zero hr
  · exact ⟨0, by rw [not_nonempty_iff_eq_empty.mp hS]; exact notMem_empty 0⟩

lemma exists_eval_ne_zero_of_lt_card {K : Type*} [Field K] [Fintype K]
    : ∀ (k : ℕ) (P : MvPolynomial (Fin k) K), P ≠ 0 → P.totalDegree < Fintype.card K →
      ∃ v : Fin k → K, eval v P ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro P hP _
    refine ⟨Fin.elim0, ?_⟩
    intro h0
    apply hP
    ext m
    rw [MvPolynomial.coeff_zero]
    have hm : m = 0 := by ext i; exact Fin.elim0 i
    subst hm
    have hsum : eval Fin.elim0 P = P.coeff 0 := by
      conv_lhs => rw [P.as_sum]
      rw [map_sum]
      by_cases hmem : (0 : Fin 0 →₀ ℕ) ∈ P.support
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro s _ hs; exfalso; apply hs; ext i; exact Fin.elim0 i
        · intro h; exact absurd hmem h
      · rw [MvPolynomial.notMem_support_iff.mp hmem]
        apply Finset.sum_eq_zero
        intro s hs; exfalso; apply hmem
        have : s = 0 := by ext i; exact Fin.elim0 i
        exact this ▸ hs
    rw [← hsum]; exact h0
  | succ k ih =>
    intro P hP hdeg
    let g : Polynomial (MvPolynomial (Fin k) K) := MvPolynomial.finSuccEquiv K k P
    have hg0 : g ≠ 0 := fun h => hP ((MvPolynomial.finSuccEquiv K k).injective (h.trans (map_zero _).symm))
    have hlc0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    have hlc_deg : g.leadingCoeff.totalDegree ≤ P.totalDegree := by
      rw [MvPolynomial.totalDegree]
      apply Finset.sup_le
      intro s hs
      have hne : g.leadingCoeff.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
      rw [Polynomial.leadingCoeff, MvPolynomial.finSuccEquiv_coeff_coeff] at hne
      have hmem : Finsupp.cons g.natDegree s ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
      have hle : (Finsupp.cons g.natDegree s).sum (fun _ e => e) ≤ P.totalDegree :=
        Finset.le_sup (f := fun m : Fin (k + 1) →₀ ℕ => m.sum (fun _ e => e)) hmem
      have hsum_le : s.sum (fun _ e => e) ≤ (Finsupp.cons g.natDegree s).sum (fun _ e => e) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
          Fin.sum_univ_succ]
        have hsucc : ∀ i : Fin k, (Finsupp.cons g.natDegree s) (Fin.succ i) = s i :=
          fun i => Finsupp.cons_succ i g.natDegree s
        simp_rw [hsucc]
        omega
      omega
    obtain ⟨w, hw⟩ := ih g.leadingCoeff hlc0 (lt_of_le_of_lt hlc_deg hdeg)
    let gw : Polynomial K := g.map (eval w)
    have hgw_nd : gw.natDegree = g.natDegree := by
      apply le_antisymm Polynomial.natDegree_map_le
      apply Polynomial.le_natDegree_of_ne_zero
      rw [Polynomial.coeff_map]
      exact hw
    have hgw0 : gw ≠ 0 := by
      intro h0
      have hc := congrArg (fun q : Polynomial K => q.coeff g.natDegree) h0
      rw [Polynomial.coeff_zero, Polynomial.coeff_map] at hc
      exact hw hc
    have hgw_lt : gw.natDegree < Fintype.card K := by
      have hnd_le : g.natDegree ≤ P.totalDegree := by
        obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hlc0
        have hne : P.coeff (Finsupp.cons g.natDegree s) ≠ 0 := by
          rw [← MvPolynomial.finSuccEquiv_coeff_coeff]
          exact MvPolynomial.mem_support_iff.mp hs
        have hle : (Finsupp.cons g.natDegree s).sum (fun _ e => e) ≤ P.totalDegree :=
          Finset.le_sup (f := fun m : Fin (k + 1) →₀ ℕ => m.sum (fun _ e => e))
            (MvPolynomial.mem_support_iff.mpr hne)
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_succ, Finsupp.cons_zero] at hle
        omega
      omega
    have hcard_lt : gw.roots.toFinset.card < (univ : Finset K).card := by
      have h1 : gw.roots.toFinset.card ≤ gw.roots.card := Multiset.toFinset_card_le _
      have h2 : gw.roots.card ≤ gw.natDegree := Polynomial.card_roots' gw
      rw [Finset.card_univ]
      omega
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
    refine ⟨Fin.cons a w, ?_⟩
    rw [MvPolynomial.eval_eq_eval_mv_eval']
    intro h0
    apply ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hgw0, Polynomial.IsRoot.def]
    exact h0

lemma exists_basis_eval_ne_zero {p : ℕ} [Fact p.Prime] {n : ℕ}
    {F : MvPolynomial (Fin 3) (ZMod p)} (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) (hnp : n < p) :
    ∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), IsUnit M.det ∧
      eval (fun i => M i 0) F ≠ 0 ∧ eval (fun i => M i 1) F ≠ 0 ∧ eval (fun i => M i 2) F ≠ 0 := by
  by_cases hn0 : n = 0
  · subst hn0
    have hFc : F = C (F.coeff 0) := isHomogeneous_zero_eq_C hF
    have hc : F.coeff 0 ≠ 0 := fun h => hF0 (by rw [hFc, h, map_zero])
    refine ⟨1, by simp, ?_, ?_, ?_⟩ <;> (rw [hFc, eval_C]; exact hc)
  · have htd : F.totalDegree < Fintype.card (ZMod p) := by
      rw [ZMod.card p, hF.totalDegree hF0]; exact hnp
    obtain ⟨v₀, hv₀⟩ := exists_eval_ne_zero_of_lt_card 3 F hF0 htd
    have hv₀_nz : v₀ ≠ 0 := by
      intro h0; subst h0
      have := isHomogeneous_eval_smul hF (0 : ZMod p) (0 : Fin 3 → ZMod p)
      rw [zero_smul, zero_pow hn0, zero_mul] at this
      exact hv₀ this
    have hex_i : ∃ i₀ : Fin 3, v₀ i₀ ≠ 0 := by
      by_contra h; apply hv₀_nz; ext i; exact not_not.mp (fun hi => h ⟨i, hi⟩)
    obtain ⟨i₀, hi₀⟩ := hex_i
    let idx : Fin 3 → Fin 3 := fun k => match i₀, k with
      | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2
      | 1, 0 => 1 | 1, 1 => 0 | 1, 2 => 2
      | 2, 0 => 2 | 2, 1 => 0 | 2, 2 => 1
    let e : Fin 3 → (Fin 3 → ZMod p) := fun j i => if i = j then 1 else 0
    let w₁ := e (idx 1)
    let w₂ := e (idx 2)
    have hlin_deg : ∀ (a b : ZMod p),
        (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
      intro a b
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp [Polynomial.natDegree_X])
    have hex_t : ∀ w : Fin 3 → ZMod p, ∃ t : ZMod p, eval (w + t • v₀) F ≠ 0 := by
      intro w
      let φ : MvPolynomial (Fin 3) (ZMod p) →+* Polynomial (ZMod p) :=
        MvPolynomial.eval₂Hom Polynomial.C
          (fun i => Polynomial.C (w i) + Polynomial.C (v₀ i) * Polynomial.X)
      let Q : Polynomial (ZMod p) := φ F
      have hQ_eval : ∀ (P : MvPolynomial (Fin 3) (ZMod p)) (t : ZMod p),
          Polynomial.eval t (φ P) = eval (w + t • v₀) P := by
        intro P t
        induction P using MvPolynomial.induction_on with
        | C a => simp [φ]
        | add a b ha hb => simp [map_add, ha, hb]
        | mul_X a i ha =>
          rw [map_mul, map_mul, Polynomial.eval_mul, ha]
          have hX : Polynomial.eval t (φ (X i)) = (w + t • v₀) i := by
            simp only [φ, MvPolynomial.eval₂Hom_X', Polynomial.eval_add, Polynomial.eval_C,
              Polynomial.eval_mul, Polynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            ring
          rw [hX, eval_X]
      have hQ_coeff : Q.coeff n = eval v₀ F := by
        dsimp only [Q]
        conv_lhs => rw [F.as_sum]
        rw [map_sum, Polynomial.finsetSum_coeff]
        conv_rhs => rw [F.as_sum]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro s hs
        have hdeg := isHomogeneous_sum_eq hF hs
        dsimp only [φ]
        rw [MvPolynomial.eval₂Hom_monomial, eval_monomial, Polynomial.coeff_C_mul]
        congr 1
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
        have hprod_deg : ∀ i : Fin 3,
            ((Polynomial.C (w i) + Polynomial.C (v₀ i) * Polynomial.X) ^ s i).natDegree ≤ s i := by
          intro i
          calc ((Polynomial.C (w i) + Polynomial.C (v₀ i) * Polynomial.X) ^ s i).natDegree
              ≤ s i * (Polynomial.C (w i) + Polynomial.C (v₀ i) * Polynomial.X).natDegree :=
                Polynomial.natDegree_pow_le
            _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hlin_deg _ _)
            _ = s i := mul_one _
        have hcoeff_pow : ∀ (a b : ZMod p) (k : ℕ),
            ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k).coeff k = b ^ k := by
          intro a b k
          induction k with
          | zero => simp
          | succ k ihk =>
            rw [pow_succ, Polynomial.coeff_mul_add_eq_of_natDegree_le]
            · rw [ihk, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
                Polynomial.coeff_X, pow_succ]
              simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, mul_one]
            · calc ((Polynomial.C a + Polynomial.C b * Polynomial.X) ^ k).natDegree
                  ≤ k * (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree :=
                    Polynomial.natDegree_pow_le
                _ ≤ k * 1 := Nat.mul_le_mul_left _ (hlin_deg _ _)
                _ = k := mul_one _
            · exact hlin_deg _ _
        rw [Fin.prod_univ_three, Fin.prod_univ_three]
        rw [Fin.sum_univ_three] at hdeg
        rw [← hdeg]
        rw [Polynomial.coeff_mul_add_eq_of_natDegree_le]
        · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le]
          · rw [hcoeff_pow, hcoeff_pow, hcoeff_pow]
          · exact hprod_deg 0
          · exact hprod_deg 1
        · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hprod_deg 0) (hprod_deg 1))
        · exact hprod_deg 2
      have hQ_nd : Q.natDegree ≤ n := by
        dsimp only [Q]
        rw [F.as_sum, map_sum]
        refine (Polynomial.natDegree_sum_le _ _).trans ?_
        apply Finset.sup_le
        intro s hs
        have hdeg := isHomogeneous_sum_eq hF hs
        dsimp only [Function.comp_apply, φ]
        rw [MvPolynomial.eval₂Hom_monomial]
        refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
        refine (Polynomial.natDegree_prod_le _ _).trans ?_
        rw [← hdeg]
        apply Finset.sum_le_sum
        intro i _
        calc ((Polynomial.C (w i) + Polynomial.C (v₀ i) * Polynomial.X) ^ s i).natDegree
            ≤ s i * (Polynomial.C (w i) + Polynomial.C (v₀ i) * Polynomial.X).natDegree :=
              Polynomial.natDegree_pow_le
          _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hlin_deg _ _)
          _ = s i := mul_one _
      have hQ0 : Q ≠ 0 := by
        intro h0; rw [h0, Polynomial.coeff_zero] at hQ_coeff; exact hv₀ hQ_coeff.symm
      have hcard_lt : Q.roots.toFinset.card < (univ : Finset (ZMod p)).card := by
        have h1 : Q.roots.toFinset.card ≤ Q.roots.card := Multiset.toFinset_card_le _
        have h2 : Q.roots.card ≤ Q.natDegree := Polynomial.card_roots' Q
        rw [Finset.card_univ, ZMod.card p]
        omega
      obtain ⟨t, _, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_lt
      refine ⟨t, ?_⟩
      rw [← hQ_eval F t]
      intro h0
      apply ht
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ0, Polynomial.IsRoot.def]
      exact h0
    obtain ⟨t₁, ht₁⟩ := hex_t w₁
    obtain ⟨t₂, ht₂⟩ := hex_t w₂
    let M : Matrix (Fin 3) (Fin 3) (ZMod p) := fun i j => match j with
      | 0 => v₀ i
      | 1 => (w₁ + t₁ • v₀) i
      | 2 => (w₂ + t₂ • v₀) i
    refine ⟨M, ?_, hv₀, ht₁, ht₂⟩
    rw [isUnit_iff_ne_zero, Matrix.det_fin_three]
    fin_cases i₀ <;> (dsimp [M, w₁, w₂, e, idx]; ring_nf; simpa using hi₀)

end HomogHelpers

section DiffFieldWronskian

structure RingDeriv (R : Type*) [CommRing R] where
  toFun : R → R
  map_add' : ∀ a b, toFun (a + b) = toFun a + toFun b
  map_mul' : ∀ a b, toFun (a * b) = toFun a * b + a * toFun b

instance {R : Type*} [CommRing R] : CoeFun (RingDeriv R) (fun _ => R → R) := ⟨RingDeriv.toFun⟩

lemma RingDeriv.map_zero {R : Type*} [CommRing R] (D : RingDeriv R) : D 0 = 0 := by
  have h := D.map_add' 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

lemma RingDeriv.map_one {R : Type*} [CommRing R] (D : RingDeriv R) : D 1 = 0 := by
  have h := D.map_mul' 1 1
  simp only [mul_one, one_mul] at h
  linear_combination -h

lemma RingDeriv.map_neg {R : Type*} [CommRing R] (D : RingDeriv R) (a : R) : D (-a) = -D a := by
  have h := D.map_add' a (-a)
  rw [add_neg_cancel, D.map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma RingDeriv.map_sub {R : Type*} [CommRing R] (D : RingDeriv R) (a b : R) :
    D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, D.map_add', D.map_neg, ← sub_eq_add_neg]

lemma RingDeriv.map_natCast {R : Type*} [CommRing R] (D : RingDeriv R) (k : ℕ) : D (k : R) = 0 := by
  induction k with
  | zero => simp [D.map_zero]
  | succ k ih => rw [Nat.cast_succ, D.map_add', ih, D.map_one, add_zero]

lemma RingDeriv.map_ofNat {R : Type*} [CommRing R] (D : RingDeriv R) (k : ℕ) [k.AtLeastTwo] :
    D (OfNat.ofNat k : R) = 0 := by
  have h := D.map_natCast (OfNat.ofNat k)
  rwa [Nat.cast_ofNat] at h

lemma RingDeriv.map_pow {R : Type*} [CommRing R] (D : RingDeriv R) (a : R) (k : ℕ) :
    D (a ^ k) = (k : R) * a ^ (k - 1) * D a := by
  induction k with
  | zero => simp [D.map_one]
  | succ k ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [pow_succ, D.map_mul', ih]
      push_cast
      rw [pow_succ]
      ring

lemma RingDeriv.map_pow_char {R : Type*} [CommRing R] (p : ℕ) [CharP R p]
    (D : RingDeriv R) (a : R) : D (a ^ p) = 0 := by
  rw [D.map_pow, CharP.cast_eq_zero R p, zero_mul, zero_mul]

lemma RingDeriv.map_div {L : Type*} [Field L] (D : RingDeriv L) (a b : L) (hb : b ≠ 0) :
    D (a / b) = (D a * b - a * D b) / b ^ 2 := by
  have h := D.map_mul' (a / b) b
  rw [div_mul_cancel₀ a hb] at h
  have h1 : D (a / b) * b = D a - (a / b) * D b := eq_sub_of_add_eq h.symm
  field_simp [hb] at h1 ⊢
  linear_combination h1

def RingDeriv.smul {R : Type*} [CommRing R] (c : R) (D : RingDeriv R) : RingDeriv R where
  toFun a := c * D a
  map_add' a b := by rw [D.map_add', mul_add]
  map_mul' a b := by rw [D.map_mul']; ring

def RingDeriv.iter {R : Type*} [CommRing R] (D : RingDeriv R) : ℕ → R → R
  | 0, a => a
  | k + 1, a => D (D.iter k a)

-- Lift any RingDeriv on an integral domain A to FractionRing A
noncomputable def RingDeriv.toFractionRing {A : Type*} [CommRing A] [IsDomain A]
    (D : RingDeriv A) : RingDeriv (FractionRing A) where
  toFun x := Localization.liftOn x
    (fun (a : A) (b : nonZeroDivisors A) =>
      (Localization.mk (D a * b.val - a * D b.val) (b * b) : FractionRing A))
    (by
      intro a₁ a₂ b₁ b₂ h
      rw [Localization.r_iff_exists] at h
      obtain ⟨c, hc⟩ := h
      have hc0 : c.val ≠ 0 := nonZeroDivisors.ne_zero c.property
      have heq : b₂.val * a₁ = b₁.val * a₂ := mul_left_cancel₀ hc0 (by linear_combination hc)
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      have hD := congrArg D heq
      rw [D.map_mul', D.map_mul'] at hD
      simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
      linear_combination b₁.val * b₂.val * hD - (D b₁.val * b₂.val + b₁.val * D b₂.val) * heq)
  map_add' := by
    intro x y
    induction x using Localization.induction_on with
    | H p =>
      induction y using Localization.induction_on with
      | H q =>
        rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        dsimp only
        rw [Localization.add_mk, Localization.liftOn_mk, Localization.liftOn_mk,
          Localization.liftOn_mk, Localization.add_mk, Localization.mk_eq_mk_iff,
          Localization.r_iff_exists]
        refine ⟨1, ?_⟩
        simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul, D.map_add', D.map_mul']
        ring
  map_mul' := by
    intro x y
    induction x using Localization.induction_on with
    | H p =>
      induction y using Localization.induction_on with
      | H q =>
        rcases p with ⟨a, b⟩
        rcases q with ⟨c, d⟩
        dsimp only
        rw [Localization.mk_mul, Localization.liftOn_mk, Localization.liftOn_mk,
          Localization.liftOn_mk, Localization.mk_mul, Localization.mk_mul,
          Localization.add_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        refine ⟨1, ?_⟩
        simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul, D.map_mul']
        ring

lemma RingDeriv.toFractionRing_algebraMap {A : Type*} [CommRing A] [IsDomain A]
    (D : RingDeriv A) (a : A) :
    D.toFractionRing (algebraMap A (FractionRing A) a) = algebraMap A (FractionRing A) (D a) := by
  have hmk : algebraMap A (FractionRing A) a = Localization.mk a 1 := rfl
  have hmkD : algebraMap A (FractionRing A) (D a) = Localization.mk (D a) 1 := rfl
  rw [hmk, hmkD]
  dsimp only [RingDeriv.toFractionRing]
  rw [Localization.liftOn_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp [D.map_one]

def fwMatrix {R : Type*} [CommRing R] (p : ℕ) (D : RingDeriv R) (m : Fin 6 → R) :
    Matrix (Fin 6) (Fin 6) R :=
  fun i j => match i with
    | 0 => (m j) ^ p
    | 1 => m j
    | 2 => D (m j)
    | 3 => D.iter 2 (m j)
    | 4 => D.iter 3 (m j)
    | 5 => D.iter 4 (m j)

def w0Matrix {R : Type*} [CommRing R] (D : RingDeriv R) (m : Fin 6 → R) :
    Matrix (Fin 6) (Fin 6) R :=
  fun i j => D.iter i.val (m j)

lemma det_fwMatrix_mul {R : Type*} [CommRing R] (p : ℕ) (D : RingDeriv R)
    (g : R) (m : Fin 6 → R) :
    (fwMatrix p D (fun j => g * m j)).det = g ^ (p + 5) * (fwMatrix p D m).det := by
  let g1 := D g
  let g2 := D.iter 2 g
  let g3 := D.iter 3 g
  let g4 := D.iter 4 g
  let T : Matrix (Fin 6) (Fin 6) R := !![
    g ^ p, 0,      0,        0,        0,      0;
    0,     g,      0,        0,        0,      0;
    0,     g1,     g,        0,        0,      0;
    0,     g2,     2 * g1,   g,        0,      0;
    0,     g3,     3 * g2,   3 * g1,   g,      0;
    0,     g4,     4 * g3,   6 * g2,   4 * g1, g
  ]
  have hmul : fwMatrix p D (fun j => g * m j) = T * fwMatrix p D m := by
    ext i j
    have hD1 : D (g * m j) = g1 * m j + g * D (m j) := D.map_mul' g (m j)
    have hD2 : D.iter 2 (g * m j) = g2 * m j + 2 * g1 * D (m j) + g * D.iter 2 (m j) := by
      change D (D (g * m j)) = _
      rw [hD1, D.map_add', D.map_mul', D.map_mul']
      dsimp only [g1, g2, RingDeriv.iter]; ring
    have hD3 : D.iter 3 (g * m j) =
        g3 * m j + 3 * g2 * D (m j) + 3 * g1 * D.iter 2 (m j) + g * D.iter 3 (m j) := by
      change D (D.iter 2 (g * m j)) = _
      rw [hD2, D.map_add', D.map_add', D.map_mul', D.map_mul', D.map_mul', D.map_mul', D.map_ofNat]
      dsimp only [g1, g2, g3, RingDeriv.iter]; ring
    have hD4 : D.iter 4 (g * m j) =
        g4 * m j + 4 * g3 * D (m j) + 6 * g2 * D.iter 2 (m j) +
          4 * g1 * D.iter 3 (m j) + g * D.iter 4 (m j) := by
      change D (D.iter 3 (g * m j)) = _
      rw [hD3, D.map_add', D.map_add', D.map_add', D.map_mul', D.map_mul', D.map_mul', D.map_mul',
        D.map_mul', D.map_mul', D.map_ofNat]
      dsimp only [g1, g2, g3, g4, RingDeriv.iter]; ring
    match i with
    | 0 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, T, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_pow]; ring
    | 1 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, T, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    | 2 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, T, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hD1]; ring
    | 3 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, T, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hD2]; ring
    | 4 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, T, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hD3]; ring
    | 5 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, T, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hD4]; ring
  have hT_lt : T.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := hij
    fin_cases i <;> fin_cases j <;> (try exact absurd hlt (by decide)) <;> rfl
  rw [hmul, Matrix.det_mul, Matrix.det_of_isLowerTriangular T hT_lt]
  simp only [Fin.prod_univ_six, T, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

lemma det_fwMatrix_smul_deriv {R : Type*} [CommRing R] (p : ℕ) (D : RingDeriv R)
    (c : R) (m : Fin 6 → R) :
    (fwMatrix p (D.smul c) m).det = c ^ 10 * (fwMatrix p D m).det := by
  let c1 := D c
  let c2 := D.iter 2 c
  let c3 := D.iter 3 c
  let s32 := c * c1
  let s42 := c * (c1 * c1 + c * c2)
  let s43 := 3 * c ^ 2 * c1
  let s52 := c * (c1 ^ 3 + 4 * c * c1 * c2 + c ^ 2 * c3)
  let s53 := c ^ 2 * (7 * c1 ^ 2 + 4 * c * c2)
  let s54 := 6 * c ^ 3 * c1
  let S : Matrix (Fin 6) (Fin 6) R := !![
    1, 0, 0,   0,   0,   0;
    0, 1, 0,   0,   0,   0;
    0, 0, c,   0,   0,   0;
    0, 0, s32, c^2, 0,   0;
    0, 0, s42, s43, c^3, 0;
    0, 0, s52, s53, s54, c^4
  ]
  have hmul : fwMatrix p (D.smul c) m = S * fwMatrix p D m := by
    ext i j
    have h1 : (D.smul c) (m j) = c * D (m j) := rfl
    have h2 : (D.smul c).iter 2 (m j) = s32 * D (m j) + c ^ 2 * D.iter 2 (m j) := by
      change c * D (c * D (m j)) = _
      rw [D.map_mul']
      dsimp only [s32, c1, RingDeriv.iter]; ring
    have h3 : (D.smul c).iter 3 (m j) =
        s42 * D (m j) + s43 * D.iter 2 (m j) + c ^ 3 * D.iter 3 (m j) := by
      change c * D ((D.smul c).iter 2 (m j)) = _
      have hDc2 : D (c ^ 2) = 2 * c * c1 := by rw [D.map_pow]; dsimp only [c1]; push_cast; ring
      have h2' : D (s32 * D (m j) + c ^ 2 * D.iter 2 (m j)) =
          (D s32 * D (m j) + s32 * D.iter 2 (m j)) + (D (c ^ 2) * D.iter 2 (m j) + c ^ 2 * D.iter 3 (m j)) := by
        rw [D.map_add', D.map_mul' s32, D.map_mul' (c ^ 2)]; rfl
      have hDs32 : D s32 = c1 * c1 + c * c2 := by dsimp only [s32]; rw [D.map_mul']; rfl
      rw [h2, h2', hDs32, hDc2]
      dsimp only [s42, s43, s32, c1, c2, RingDeriv.iter]
      ring
    have h4 : (D.smul c).iter 4 (m j) =
        s52 * D (m j) + s53 * D.iter 2 (m j) + s54 * D.iter 3 (m j) + c ^ 4 * D.iter 4 (m j) := by
      change c * D ((D.smul c).iter 3 (m j)) = _
      have hDc3 : D (c ^ 3) = 3 * c ^ 2 * c1 := by rw [D.map_pow]; dsimp only [c1]; push_cast; ring
      have hDs42 : D s42 = c1 ^ 3 + 4 * c * c1 * c2 + c ^ 2 * c3 := by
        dsimp only [s42]
        rw [D.map_mul', D.map_add', D.map_mul', D.map_mul']
        dsimp only [c1, c2, c3, RingDeriv.iter]; ring
      have hDs43 : D s43 = 6 * c * c1 ^ 2 + 3 * c ^ 2 * c2 := by
        dsimp only [s43]
        rw [D.map_mul', D.map_mul', D.map_ofNat, D.map_pow]
        dsimp only [c1, c2, RingDeriv.iter]; push_cast; ring
      have h3' : D (s42 * D (m j) + s43 * D.iter 2 (m j) + c ^ 3 * D.iter 3 (m j)) =
          (D s42 * D (m j) + s42 * D.iter 2 (m j)) +
          (D s43 * D.iter 2 (m j) + s43 * D.iter 3 (m j)) +
          (D (c ^ 3) * D.iter 3 (m j) + c ^ 3 * D.iter 4 (m j)) := by
        rw [D.map_add', D.map_add', D.map_mul' s42, D.map_mul' s43, D.map_mul' (c ^ 3)]; rfl
      rw [h3, h3', hDs42, hDs43, hDc3]
      dsimp only [s52, s53, s54, s42, s43, c1, c2, c3, RingDeriv.iter]
      ring
    match i with
    | 0 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, S, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    | 1 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, S, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; ring
    | 2 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, S, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h1]; ring
    | 3 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, S, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h2]; ring
    | 4 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, S, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h3]; ring
    | 5 => rw [Matrix.mul_apply, Fin.sum_univ_six]; simp only [fwMatrix, S, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, h4]; ring
  have hS_lt : S.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hlt : i < j := hij
    fin_cases i <;> fin_cases j <;> (try exact absurd hlt (by decide)) <;> rfl
  rw [hmul, Matrix.det_mul, Matrix.det_of_isLowerTriangular S hS_lt]
  simp only [Fin.prod_univ_six, S, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  ring

lemma det_fwMatrix_perm {R : Type*} [CommRing R] (p : ℕ) (D : RingDeriv R)
    (m : Fin 6 → R) (σ : Equiv.Perm (Fin 6)) :
    (fwMatrix p D (m ∘ σ)).det = Equiv.Perm.sign σ • (fwMatrix p D m).det := by
  have hsub : fwMatrix p D (m ∘ σ) = (fwMatrix p D m).submatrix id σ := by
    ext i j; fin_cases i <;> rfl
  rw [hsub, Matrix.det_permute', Units.smul_def, zsmul_eq_mul]

lemma det_fin3_explicit {R : Type*} [CommRing R] (a00 a01 a02 a10 a11 a12 a20 a21 a22 : R) :
    (!![a00, a01, a02; a10, a11, a12; a20, a21, a22] : Matrix (Fin 3) (Fin 3) R).det =
      a00 * a11 * a22 + a01 * a12 * a20 + a02 * a10 * a21 -
        a00 * a12 * a21 - a01 * a10 * a22 - a02 * a11 * a20 := by
  rw [Matrix.det_fin_three]
  change a00 * a11 * a22 - a00 * a12 * a21 - a01 * a10 * a22 +
    a01 * a12 * a20 + a02 * a10 * a21 - a02 * a11 * a20 = _
  ring

lemma det_sparse_4x4 {R : Type*} [CommRing R] (dx dy y2 y3 y4 : R) :
    (!![
      dy, dx ^ 2, dx * dy,    dy ^ 2;
      y2, 2,      0,          0;
      y3, 0,      3 * y2,     0;
      y4, 0,      4 * y3,     6 * y2 ^ 2
    ] : Matrix (Fin 4) (Fin 4) R).det =
      2 * (18 * y2 ^ 3 * dy - 9 * y2 ^ 4 * dx ^ 2 - 6 * y2 ^ 2 * y3 * dx * dy +
        (4 * y3 ^ 2 - 3 * y2 * y4) * dy ^ 2) := by
  let B3 : Matrix (Fin 4) (Fin 4) R := !![
    dy, dx ^ 2, dx * dy,    dy ^ 2;
    y2, 2,      0,          0;
    y3, 0,      3 * y2,     0;
    y4, 0,      4 * y3,     6 * y2 ^ 2
  ]
  change B3.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  have h0 : B3.submatrix Fin.succ (Fin.succAbove 0) =
      !![2, 0, 0; 0, 3 * y2, 0; 0, 4 * y3, 6 * y2 ^ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h1 : B3.submatrix Fin.succ (Fin.succAbove 1) =
      !![y2, 0, 0; y3, 3 * y2, 0; y4, 4 * y3, 6 * y2 ^ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h2 : B3.submatrix Fin.succ (Fin.succAbove 2) =
      !![y2, 2, 0; y3, 0, 0; y4, 0, 6 * y2 ^ 2] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h3 : B3.submatrix Fin.succ (Fin.succAbove 3) =
      !![y2, 2, 0; y3, 0, 3 * y2; y4, 0, 4 * y3] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  change (-1) ^ (0 : ℕ) * dy * (B3.submatrix Fin.succ (Fin.succAbove 0)).det +
    (-1) ^ (1 : ℕ) * dx ^ 2 * (B3.submatrix Fin.succ (Fin.succAbove 1)).det +
    (-1) ^ (2 : ℕ) * (dx * dy) * (B3.submatrix Fin.succ (Fin.succAbove 2)).det +
    (-1) ^ (3 : ℕ) * dy ^ 2 * (B3.submatrix Fin.succ (Fin.succAbove 3)).det = _
  rw [h0, h1, h2, h3, det_fin3_explicit, det_fin3_explicit, det_fin3_explicit, det_fin3_explicit]
  ring

lemma det_succ_row_e0 {R : Type*} [CommRing R] {n : ℕ} (r : Fin (n + 1))
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hr0 : M r 0 = 1) (hrj : ∀ j : Fin (n + 1), j ≠ 0 → M r j = 0) :
    M.det = (-1 : R) ^ (r : ℕ) * (M.submatrix r.succAbove Fin.succ).det := by
  rw [Matrix.det_succ_row M r, Finset.sum_eq_single (0 : Fin (n + 1))]
  · rw [hr0, Fin.succAbove_zero]; simp
  · intro j _ hj; rw [hrj j hj, mul_zero, zero_mul]
  · intro h; exact absurd (mem_univ _) h

lemma det_sparse_6x6_to_5x5 {R : Type*} [CommRing R] (dx dy y2 y3 y4 : R) :
    (!![
      1, dx, dy, dx ^ 2, dx * dy,    dy ^ 2;
      1, 0,  0,  0,      0,          0;
      0, 1,  0,  0,      0,          0;
      0, 0,  y2, 2,      0,          0;
      0, 0,  y3, 0,      3 * y2,     0;
      0, 0,  y4, 0,      4 * y3,     6 * y2 ^ 2
    ] : Matrix (Fin 6) (Fin 6) R).det =
    -(!![
      dx, dy, dx ^ 2, dx * dy,    dy ^ 2;
      1,  0,  0,      0,          0;
      0,  y2, 2,      0,          0;
      0,  y3, 0,      3 * y2,     0;
      0,  y4, 0,      4 * y3,     6 * y2 ^ 2
    ] : Matrix (Fin 5) (Fin 5) R).det := by
  rw [det_succ_row_e0 1 _ rfl (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | rfl)]
  simp only [Fin.val_one, pow_one, neg_one_mul]
  congr 2; ext i j; fin_cases i <;> rfl

lemma det_sparse_5x5_to_4x4 {R : Type*} [CommRing R] (dx dy y2 y3 y4 : R) :
    (!![
      dx, dy, dx ^ 2, dx * dy,    dy ^ 2;
      1,  0,  0,      0,          0;
      0,  y2, 2,      0,          0;
      0,  y3, 0,      3 * y2,     0;
      0,  y4, 0,      4 * y3,     6 * y2 ^ 2
    ] : Matrix (Fin 5) (Fin 5) R).det =
    -(!![
      dy, dx ^ 2, dx * dy,    dy ^ 2;
      y2, 2,      0,          0;
      y3, 0,      3 * y2,     0;
      y4, 0,      4 * y3,     6 * y2 ^ 2
    ] : Matrix (Fin 4) (Fin 4) R).det := by
  rw [det_succ_row_e0 1 _ rfl (fun j hj => by fin_cases j <;> first | exact absurd rfl hj | rfl)]
  simp only [Fin.val_one, pow_one, neg_one_mul]
  congr 2; ext i j; fin_cases i <;> rfl

lemma det_sparse_6x6 {R : Type*} [CommRing R] (dx dy y2 y3 y4 : R) :
    (!![
      1, dx, dy, dx ^ 2, dx * dy,    dy ^ 2;
      1, 0,  0,  0,      0,          0;
      0, 1,  0,  0,      0,          0;
      0, 0,  y2, 2,      0,          0;
      0, 0,  y3, 0,      3 * y2,     0;
      0, 0,  y4, 0,      4 * y3,     6 * y2 ^ 2
    ] : Matrix (Fin 6) (Fin 6) R).det =
      2 * (18 * y2 ^ 3 * dy - 9 * y2 ^ 4 * dx ^ 2 - 6 * y2 ^ 2 * y3 * dx * dy +
        (4 * y3 ^ 2 - 3 * y2 * y4) * dy ^ 2) := by
  rw [det_sparse_6x6_to_5x5, det_sparse_5x5_to_4x4, neg_neg, det_sparse_4x4]

lemma det_fwMatrix_conic {R : Type*} [CommRing R] (p : ℕ) (D : RingDeriv R)
    (x y : R) (hx : D x = 1) :
    let y1 := D y
    let y2 := D y1
    let y3 := D y2
    let y4 := D y3
    let dx := x ^ p - x
    let dy := (y ^ p - y) - y1 * dx
    (fwMatrix p D ![1, x, y, x ^ 2, x * y, y ^ 2]).det =
      2 * (18 * y2 ^ 3 * dy - 9 * y2 ^ 4 * dx ^ 2 - 6 * y2 ^ 2 * y3 * dx * dy +
        (4 * y3 ^ 2 - 3 * y2 * y4) * dy ^ 2) := by
  intro y1 y2 y3 y4 dx dy
  let U : Matrix (Fin 6) (Fin 6) R := !![
    1, -x, x * y1 - y, x ^ 2, -x ^ 2 * y1 + x * y, x ^ 2 * y1 ^ 2 - 2 * x * y * y1 + y ^ 2;
    0, 1,  -y1,        -2 * x, 2 * x * y1 - y,     -2 * x * y1 ^ 2 + 2 * y * y1;
    0, 0,  1,          0,      -x,                 2 * x * y1 - 2 * y;
    0, 0,  0,          1,      -y1,                y1 ^ 2;
    0, 0,  0,          0,      1,                  -2 * y1;
    0, 0,  0,          0,      0,                  1
  ]
  have hU_ut : U.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [U]
  have hU_det : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_ut]
    simp [U, Fin.prod_univ_six]
  let B : Matrix (Fin 6) (Fin 6) R := !![
    1, dx, dy, dx ^ 2, dx * dy,    dy ^ 2;
    1, 0,  0,  0,      0,          0;
    0, 1,  0,  0,      0,          0;
    0, 0,  y2, 2,      0,          0;
    0, 0,  y3, 0,      3 * y2,     0;
    0, 0,  y4, 0,      4 * y3,     6 * y2 ^ 2
  ]
  have hD1 : D (1 : R) = 0 := D.map_one
  have hD2_1 : D.iter 2 (1 : R) = 0 := by change D (D 1) = 0; rw [hD1, D.map_zero]
  have hD3_1 : D.iter 3 (1 : R) = 0 := by change D (D.iter 2 1) = 0; rw [hD2_1, D.map_zero]
  have hD4_1 : D.iter 4 (1 : R) = 0 := by change D (D.iter 3 1) = 0; rw [hD3_1, D.map_zero]
  have hD2_x : D.iter 2 x = 0 := by change D (D x) = 0; rw [hx, hD1]
  have hD3_x : D.iter 3 x = 0 := by change D (D.iter 2 x) = 0; rw [hD2_x, D.map_zero]
  have hD4_x : D.iter 4 x = 0 := by change D (D.iter 3 x) = 0; rw [hD3_x, D.map_zero]
  have hD1_x2 : D (x ^ 2) = 2 * x := by rw [D.map_pow, hx]; push_cast; ring
  have hD2_x2 : D.iter 2 (x ^ 2) = 2 := by
    change D (D (x ^ 2)) = 2; rw [hD1_x2, D.map_mul', D.map_ofNat, hx]; ring
  have hD3_x2 : D.iter 3 (x ^ 2) = 0 := by
    change D (D.iter 2 (x ^ 2)) = 0; rw [hD2_x2]; exact D.map_ofNat 2
  have hD4_x2 : D.iter 4 (x ^ 2) = 0 := by
    change D (D.iter 3 (x ^ 2)) = 0; rw [hD3_x2, D.map_zero]
  have hD1_xy : D (x * y) = y + x * y1 := by rw [D.map_mul', hx]; dsimp only [y1]; ring
  have hD2_xy : D.iter 2 (x * y) = 2 * y1 + x * y2 := by
    change D (D (x * y)) = _; rw [hD1_xy, D.map_add', D.map_mul', hx]; dsimp only [y1, y2]; ring
  have hD3_xy : D.iter 3 (x * y) = 3 * y2 + x * y3 := by
    change D (D.iter 2 (x * y)) = _
    rw [hD2_xy, D.map_add', D.map_mul', D.map_ofNat, D.map_mul', hx]
    dsimp only [y1, y2, y3]; ring
  have hD4_xy : D.iter 4 (x * y) = 4 * y3 + x * y4 := by
    change D (D.iter 3 (x * y)) = _
    rw [hD3_xy, D.map_add', D.map_mul', D.map_ofNat, D.map_mul', hx]
    dsimp only [y2, y3, y4]; ring
  have hD1_y2 : D (y ^ 2) = 2 * y * y1 := by rw [D.map_pow]; dsimp only [y1]; push_cast; ring
  have hD2_y2 : D.iter 2 (y ^ 2) = 2 * y1 ^ 2 + 2 * y * y2 := by
    change D (D (y ^ 2)) = _
    rw [hD1_y2, D.map_mul', D.map_mul', D.map_ofNat]; dsimp only [y1, y2]; ring
  have hD3_y2 : D.iter 3 (y ^ 2) = 6 * y1 * y2 + 2 * y * y3 := by
    change D (D.iter 2 (y ^ 2)) = _
    rw [hD2_y2, D.map_add', D.map_mul', D.map_ofNat, D.map_pow, D.map_mul', D.map_mul',
      D.map_ofNat]
    dsimp only [y1, y2, y3]; push_cast; ring
  have hD4_y2 : D.iter 4 (y ^ 2) = 6 * y2 ^ 2 + 8 * y1 * y3 + 2 * y * y4 := by
    change D (D.iter 3 (y ^ 2)) = _
    rw [hD3_y2, D.map_add', D.map_mul', D.map_mul', D.map_ofNat, D.map_mul', D.map_mul',
      D.map_ofNat]
    dsimp only [y1, y2, y3, y4]; ring
  have hxp : x ^ p = x + dx := by dsimp only [dx]; ring
  have hyp : y ^ p = y + y1 * dx + dy := by dsimp only [dy]; ring
  have hx2p : (x ^ 2) ^ p = (x ^ p) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  have hy2p : (y ^ 2) ^ p = (y ^ p) ^ 2 := by rw [← pow_mul, ← pow_mul, mul_comm]
  -- Explicitly characterize each row of fwMatrix to avoid heartbeats in simp
  let A : Matrix (Fin 6) (Fin 6) R := !![
    1, x ^ p, y ^ p, (x ^ p) ^ 2, x ^ p * y ^ p, (y ^ p) ^ 2;
    1, x,     y,     x ^ 2,       x * y,         y ^ 2;
    0, 1,     y1,    2 * x,       y + x * y1,    2 * y * y1;
    0, 0,     y2,    2,           2 * y1 + x * y2, 2 * y1 ^ 2 + 2 * y * y2;
    0, 0,     y3,    0,           3 * y2 + x * y3, 6 * y1 * y2 + 2 * y * y3;
    0, 0,     y4,    0,           4 * y3 + x * y4, 6 * y2 ^ 2 + 8 * y1 * y3 + 2 * y * y4
  ]
  have hA_eq : fwMatrix p D ![1, x, y, x ^ 2, x * y, y ^ 2] = A := by
    ext i j
    fin_cases i
    · fin_cases j
      · change (1 : R) ^ p = 1; exact one_pow p
      · rfl
      · rfl
      · change (x ^ 2) ^ p = (x ^ p) ^ 2; exact hx2p
      · change (x * y) ^ p = x ^ p * y ^ p; exact mul_pow x y p
      · change (y ^ 2) ^ p = (y ^ p) ^ 2; exact hy2p
    · fin_cases j <;> rfl
    · fin_cases j
      · exact hD1
      · exact hx
      · rfl
      · exact hD1_x2
      · exact hD1_xy
      · exact hD1_y2
    · fin_cases j
      · exact hD2_1
      · exact hD2_x
      · rfl
      · exact hD2_x2
      · exact hD2_xy
      · exact hD2_y2
    · fin_cases j
      · exact hD3_1
      · exact hD3_x
      · rfl
      · exact hD3_x2
      · exact hD3_xy
      · exact hD3_y2
    · fin_cases j
      · exact hD4_1
      · exact hD4_x
      · rfl
      · exact hD4_x2
      · exact hD4_xy
      · exact hD4_y2
  have hAU : A * U = B := by
    ext i j
    match i, j with
    | 0, 0 | 0, 1 | 0, 2 | 0, 3 | 0, 4 | 0, 5 =>
      rw [Matrix.mul_apply, Fin.sum_univ_six]
      simp only [A, U, B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      rw [hxp, hyp]; ring
    | 1, 0 | 1, 1 | 1, 2 | 1, 3 | 1, 4 | 1, 5
    | 2, 0 | 2, 1 | 2, 2 | 2, 3 | 2, 4 | 2, 5
    | 3, 0 | 3, 1 | 3, 2 | 3, 3 | 3, 4 | 3, 5
    | 4, 0 | 4, 1 | 4, 2 | 4, 3 | 4, 4 | 4, 5
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 =>
      rw [Matrix.mul_apply, Fin.sum_univ_six]
      simp only [A, U, B, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val]
      ring
  calc (fwMatrix p D ![1, x, y, x ^ 2, x * y, y ^ 2]).det
      = A.det := by rw [hA_eq]
    _ = A.det * U.det := by rw [hU_det, mul_one]
    _ = (A * U).det := (Matrix.det_mul _ _).symm
    _ = B.det := by rw [hAU]
    _ = _ := det_sparse_6x6 dx dy y2 y3 y4

lemma det_fwMatrix_ne_zero_of_w0_ne_zero {L : Type*} [Field L] (p : ℕ) [CharP L p]
    (D : RingDeriv L) (m : Fin 6 → L) (hm0 : m 0 = 1)
    (hw0 : (w0Matrix D m).det ≠ 0) :
    (fwMatrix p D m).det ≠ 0 := by
  intro hwf0
  have hlin0 : LinearIndependent L (Matrix.row (w0Matrix D m)) :=
    Matrix.linearIndependent_rows_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hw0))
  have hdep : ¬ LinearIndependent L (Matrix.row (fwMatrix p D m)) := fun h =>
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp h))) hwf0
  rw [Fintype.linearIndependent_iff, not_forall] at hdep
  obtain ⟨c, hc⟩ := hdep
  rw [Classical.not_imp, not_forall] at hc
  obtain ⟨hsum, i₀, hi₀⟩ := hc
  have hc0_ne : c 0 ≠ 0 := by
    intro hc0
    have hsum' : ∑ i : Fin 6, (if h : i.val < 5 then c ⟨i.val + 1, by omega⟩ else 0) •
        Matrix.row (w0Matrix D m) i = 0 := by
      ext j
      have hj := congrFun hsum j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row_apply] at hj ⊢
      rw [Fin.sum_univ_six] at hj ⊢
      rw [hc0, zero_mul, zero_add] at hj
      simpa [fwMatrix, w0Matrix, RingDeriv.iter] using hj
    have hall0 := (Fintype.linearIndependent_iff.mp hlin0) _ hsum'
    apply hi₀
    fin_cases i₀
    · exact hc0
    · simpa using hall0 0
    · simpa using hall0 1
    · simpa using hall0 2
    · simpa using hall0 3
    · simpa using hall0 4
  let a : Fin 5 → L := fun k => - (c ⟨k.val + 1, by omega⟩ / c 0)
  have hw_eq : ∀ j : Fin 6, (m j) ^ p =
      a 0 * m j + a 1 * D (m j) + a 2 * D.iter 2 (m j) +
      a 3 * D.iter 3 (m j) + a 4 * D.iter 4 (m j) := by
    intro j
    have hj := congrFun hsum j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.sum_univ_six,
      Matrix.row_apply] at hj
    dsimp only [fwMatrix] at hj
    have ha0 : a 0 = -(c 1 / c 0) := rfl
    have ha1 : a 1 = -(c 2 / c 0) := rfl
    have ha2 : a 2 = -(c 3 / c 0) := rfl
    have ha3 : a 3 = -(c 4 / c 0) := rfl
    have ha4 : a 4 = -(c 5 / c 0) := rfl
    rw [ha0, ha1, ha2, ha3, ha4]
    field_simp [hc0_ne]
    linear_combination hj
  have hD_eq : ∀ j : Fin 6,
      D (a 0) * (w0Matrix D m 0 j) +
      (D (a 1) + a 0) * (w0Matrix D m 1 j) +
      (D (a 2) + a 1) * (w0Matrix D m 2 j) +
      (D (a 3) + a 2) * (w0Matrix D m 3 j) +
      (D (a 4) + a 3) * (w0Matrix D m 4 j) +
      a 4 * (w0Matrix D m 5 j) = 0 := by
    intro j
    have h0 := congrArg D (hw_eq j)
    rw [D.map_pow_char p] at h0
    simp only [D.map_add', D.map_mul'] at h0
    have e0 : w0Matrix D m 0 j = m j := rfl
    have e1 : w0Matrix D m 1 j = D (m j) := rfl
    have e2 : w0Matrix D m 2 j = D.iter 2 (m j) := rfl
    have e3 : w0Matrix D m 3 j = D.iter 3 (m j) := rfl
    have e4 : w0Matrix D m 4 j = D.iter 4 (m j) := rfl
    have e5 : w0Matrix D m 5 j = D.iter 5 (m j) := rfl
    have d1 : D (D (m j)) = D.iter 2 (m j) := rfl
    have d2 : D (D.iter 2 (m j)) = D.iter 3 (m j) := rfl
    have d3 : D (D.iter 3 (m j)) = D.iter 4 (m j) := rfl
    have d4 : D (D.iter 4 (m j)) = D.iter 5 (m j) := rfl
    rw [e0, e1, e2, e3, e4, e5]
    rw [d1, d2, d3, d4] at h0
    linear_combination h0.symm
  let b : Fin 6 → L := ![D (a 0), D (a 1) + a 0, D (a 2) + a 1,
    D (a 3) + a 2, D (a 4) + a 3, a 4]
  have hb_sum : ∑ i : Fin 6, b i • Matrix.row (w0Matrix D m) i = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.sum_univ_six,
      Matrix.row_apply, b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    exact hD_eq j
  have hb0 := (Fintype.linearIndependent_iff.mp hlin0) b hb_sum
  have ha4 : a 4 = 0 := by simpa [b] using hb0 5
  have ha3 : a 3 = 0 := by have := hb0 4; simp [b, ha4, D.map_zero] at this; exact this
  have ha2 : a 2 = 0 := by have := hb0 3; simp [b, ha3, D.map_zero] at this; exact this
  have ha1 : a 1 = 0 := by have := hb0 2; simp [b, ha2, D.map_zero] at this; exact this
  have ha0 : a 0 = 0 := by have := hb0 1; simp [b, ha1, D.map_zero] at this; exact this
  have h1 := hw_eq 0
  rw [hm0, one_pow, ha0, ha1, ha2, ha3, ha4] at h1
  simp at h1

end DiffFieldWronskian

section W10Polynomial

noncomputable def Dt2 {R : Type*} [CommRing R] (f g : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 2) R :=
  MvPolynomial.pderiv 1 f * MvPolynomial.pderiv 0 g -
    MvPolynomial.pderiv 0 f * MvPolynomial.pderiv 1 g

noncomputable def W10 {R : Type*} [CommRing R] (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 2) R :=
  let fx := MvPolynomial.pderiv 0 f
  let fy := MvPolynomial.pderiv 1 f
  let B := Dt2 f fy
  let E := Dt2 f fx
  let N2 := fx * B - fy * E
  let A := Dt2 f N2
  let K := B * Dt2 f E - E * Dt2 f B
  let Dx : MvPolynomial (Fin 2) R := X 0 ^ p - X 0
  let Dy : MvPolynomial (Fin 2) R := X 1 ^ p - X 1
  let Py := fy * Dy + fx * Dx
  let L := E * Dx + B * Dy
  18 * N2 ^ 3 * Py - 9 * N2 ^ 2 * L ^ 2 + 9 * N2 * K * Py ^ 2 +
    6 * A * N2 * L * Py + (4 * A ^ 2 - 3 * N2 * Dt2 f A) * Py ^ 2

lemma Dt2_add {R : Type*} [CommRing R] (f g h : MvPolynomial (Fin 2) R) :
    Dt2 f (g + h) = Dt2 f g + Dt2 f h := by
  unfold Dt2; simp only [map_add]; ring

lemma Dt2_sub {R : Type*} [CommRing R] (f g h : MvPolynomial (Fin 2) R) :
    Dt2 f (g - h) = Dt2 f g - Dt2 f h := by
  unfold Dt2; simp only [map_sub]; ring

lemma Dt2_mul {R : Type*} [CommRing R] (f g h : MvPolynomial (Fin 2) R) :
    Dt2 f (g * h) = Dt2 f g * h + g * Dt2 f h := by
  unfold Dt2; simp only [MvPolynomial.pderiv_mul]; ring

lemma Dt2_self {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) :
    Dt2 f f = 0 := by
  unfold Dt2; ring

lemma Dt2_ofNat {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) (k : ℕ) [k.AtLeastTwo] :
    Dt2 f (OfNat.ofNat k : MvPolynomial (Fin 2) R) = 0 := by
  unfold Dt2
  have hC : (OfNat.ofNat k : MvPolynomial (Fin 2) R) = C (OfNat.ofNat k : R) := by
    change (k : MvPolynomial (Fin 2) R) = C (k : R); simp
  rw [hC, MvPolynomial.pderiv_C, MvPolynomial.pderiv_C]; ring

lemma fy_sq_mul_W10 {R : Type*} [CommRing R] (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    let fx := MvPolynomial.pderiv 0 f
    let fy := MvPolynomial.pderiv 1 f
    let B := Dt2 f fy
    let E := Dt2 f fx
    let N2 := fx * B - fy * E
    let N3 := Dt2 f N2 * fy - 3 * N2 * B
    let N4 := Dt2 f N3 * fy - 5 * N3 * B
    let Dx : MvPolynomial (Fin 2) R := X 0 ^ p - X 0
    let Dy : MvPolynomial (Fin 2) R := X 1 ^ p - X 1
    let Py := fy * Dy + fx * Dx
    fy ^ 2 * W10 p f =
      18 * N2 ^ 3 * Py * fy ^ 2 - 9 * N2 ^ 4 * Dx ^ 2 - 6 * N2 ^ 2 * N3 * Dx * Py +
        (4 * N3 ^ 2 - 3 * N2 * N4) * Py ^ 2 := by
  intro fx fy B E N2 N3 N4 Dx Dy Py
  dsimp only [W10]
  have hDN2 : Dt2 f N2 = fx * Dt2 f B - fy * Dt2 f E := by
    dsimp only [N2]
    rw [Dt2_sub, Dt2_mul, Dt2_mul]
    dsimp only [B, E]
    ring
  have hDN3 : Dt2 f N3 = Dt2 f (Dt2 f N2) * fy - 2 * Dt2 f N2 * B - 3 * N2 * Dt2 f B := by
    dsimp only [N3]
    rw [Dt2_sub, Dt2_mul, Dt2_mul, Dt2_mul, Dt2_ofNat]
    dsimp only [B]
    ring
  dsimp only [N4]
  rw [hDN3]
  dsimp only [N3]
  have hK : N2 * Dt2 f B - Dt2 f N2 * B = fy * (B * Dt2 f E - E * Dt2 f B) := by
    rw [hDN2]; dsimp only [N2]; ring
  have hL : N2 * Dx - B * Py = -fy * (E * Dx + B * Dy) := by
    dsimp only [N2, Py]; ring
  linear_combination
    -9 * N2 ^ 2 * (N2 * Dx - B * Py - fy * (E * Dx + B * Dy)) * hL
    - 9 * N2 * Py ^ 2 * fy * hK

lemma totalDegree_pderiv_le_sub {R : Type*} [CommRing R] {σ : Type*}
    (i : σ) (g : MvPolynomial σ R) :
    (MvPolynomial.pderiv i g).totalDegree ≤ g.totalDegree - 1 := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  have hg : m + Finsupp.single i 1 ∈ g.support :=
    MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hc)
  have hle : (m + Finsupp.single i 1).sum (fun _ e => e) ≤ g.totalDegree :=
    Finset.le_sup (f := fun s : σ →₀ ℕ => s.sum (fun _ e => e)) hg
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  omega

lemma totalDegree_Dt2_le {R : Type*} [CommRing R] {f g : MvPolynomial (Fin 2) R} {n d : ℕ}
    (hf : f.totalDegree ≤ n) (hg : g.totalDegree ≤ d) (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (Dt2 f g).totalDegree ≤ n + d - 2 := by
  unfold Dt2
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 := totalDegree_pderiv_le_sub (1 : Fin 2) f
    have h2 := totalDegree_pderiv_le_sub (0 : Fin 2) g
    omega
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    have h1 := totalDegree_pderiv_le_sub (0 : Fin 2) f
    have h2 := totalDegree_pderiv_le_sub (1 : Fin 2) g
    omega

lemma totalDegree_natCast_mul_le {R : Type*} [CommRing R] {σ : Type*}
    (c : ℕ) (P : MvPolynomial σ R) :
    ((c : MvPolynomial σ R) * P).totalDegree ≤ P.totalDegree := by
  rw [show (c : MvPolynomial σ R) = C (c : R) from by simp]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]

lemma totalDegree_ofNat_mul_le {R : Type*} [CommRing R] {σ : Type*}
    (c : ℕ) [c.AtLeastTwo] (P : MvPolynomial σ R) :
    ((OfNat.ofNat c : MvPolynomial σ R) * P).totalDegree ≤ P.totalDegree := by
  have h := totalDegree_natCast_mul_le (OfNat.ofNat c) P
  rwa [Nat.cast_ofNat] at h

lemma totalDegree_W10_le {R : Type*} [CommRing R] {p n : ℕ} {f : MvPolynomial (Fin 2) R}
    (hf : f.totalDegree ≤ n) (hn : 3 ≤ n) (hp : 1 ≤ p) :
    (W10 p f).totalDegree ≤ 2 * p + 10 * n - 14 := by
  let fx := MvPolynomial.pderiv 0 f
  let fy := MvPolynomial.pderiv 1 f
  let B := Dt2 f fy
  let E := Dt2 f fx
  let N2 := fx * B - fy * E
  let A := Dt2 f N2
  let K := B * Dt2 f E - E * Dt2 f B
  let Dx : MvPolynomial (Fin 2) R := X 0 ^ p - X 0
  let Dy : MvPolynomial (Fin 2) R := X 1 ^ p - X 1
  let Py := fy * Dy + fx * Dx
  let L := E * Dx + B * Dy
  change (18 * N2 ^ 3 * Py - 9 * N2 ^ 2 * L ^ 2 + 9 * N2 * K * Py ^ 2 +
    6 * A * N2 * L * Py + (4 * A ^ 2 - 3 * N2 * Dt2 f A) * Py ^ 2).totalDegree ≤ 2 * p + 10 * n - 14
  have hfx : fx.totalDegree ≤ n - 1 :=
    (totalDegree_pderiv_le_sub 0 f).trans (Nat.sub_le_sub_right hf 1)
  have hfy : fy.totalDegree ≤ n - 1 :=
    (totalDegree_pderiv_le_sub 1 f).trans (Nat.sub_le_sub_right hf 1)
  have hB : B.totalDegree ≤ 2 * n - 3 := (totalDegree_Dt2_le hf hfy (by omega) (by omega)).trans (by omega)
  have hE : E.totalDegree ≤ 2 * n - 3 := (totalDegree_Dt2_le hf hfx (by omega) (by omega)).trans (by omega)
  have hN2 : N2.totalDegree ≤ 3 * n - 4 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have hA : A.totalDegree ≤ 4 * n - 6 := (totalDegree_Dt2_le hf hN2 (by omega) (by omega)).trans (by omega)
  have hDA : (Dt2 f A).totalDegree ≤ 5 * n - 8 := (totalDegree_Dt2_le hf hA (by omega) (by omega)).trans (by omega)
  have hDE : (Dt2 f E).totalDegree ≤ 3 * n - 5 := (totalDegree_Dt2_le hf hE (by omega) (by omega)).trans (by omega)
  have hDB : (Dt2 f B).totalDegree ≤ 3 * n - 5 := (totalDegree_Dt2_le hf hB (by omega) (by omega)).trans (by omega)
  have hK : K.totalDegree ≤ 5 * n - 8 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have hX0 : (X (0 : Fin 2) : MvPolynomial (Fin 2) R).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree]; apply Finset.sup_le; intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_X] at hc
    split_ifs at hc with h
    · rw [← h]; simp
    · exact absurd rfl hc
  have hX1 : (X (1 : Fin 2) : MvPolynomial (Fin 2) R).totalDegree ≤ 1 := by
    rw [MvPolynomial.totalDegree]; apply Finset.sup_le; intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_X] at hc
    split_ifs at hc with h
    · rw [← h]; simp
    · exact absurd rfl hc
  have hDx : Dx.totalDegree ≤ p := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left p hX0; omega)
    · omega
  have hDy : Dy.totalDegree ≤ p := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_pow _ _).trans (by have := Nat.mul_le_mul_left p hX1; omega)
    · omega
  have hPy : Py.totalDegree ≤ p + n - 1 := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have hL : L.totalDegree ≤ p + 2 * n - 3 := by
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have hN2_3 : (18 * N2 ^ 3).totalDegree ≤ 9 * n - 12 :=
    (totalDegree_ofNat_mul_le 18 _).trans ((MvPolynomial.totalDegree_pow _ _).trans (by omega))
  have hN2_2 : (9 * N2 ^ 2).totalDegree ≤ 6 * n - 8 :=
    (totalDegree_ofNat_mul_le 9 _).trans ((MvPolynomial.totalDegree_pow _ _).trans (by omega))
  have hL_2 : (L ^ 2).totalDegree ≤ 2 * p + 4 * n - 6 :=
    (MvPolynomial.totalDegree_pow _ _).trans (by omega)
  have hPy_2 : (Py ^ 2).totalDegree ≤ 2 * p + 2 * n - 2 :=
    (MvPolynomial.totalDegree_pow _ _).trans (by omega)
  have h9N2K : (9 * N2 * K).totalDegree ≤ 8 * n - 12 :=
    (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add ((totalDegree_ofNat_mul_le 9 _).trans hN2) hK) |>.trans (by omega)
  have h6AN2L : (6 * A * N2 * L).totalDegree ≤ p + 9 * n - 13 := by
    have h6A : (6 * A).totalDegree ≤ 4 * n - 6 := (totalDegree_ofNat_mul_le 6 _).trans hA
    have h6AN2 : (6 * A * N2).totalDegree ≤ 7 * n - 10 :=
      (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  have h5lhs : (4 * A ^ 2 - 3 * N2 * Dt2 f A).totalDegree ≤ 8 * n - 12 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (totalDegree_ofNat_mul_le 4 _).trans ((MvPolynomial.totalDegree_pow _ _).trans (by omega))
    · have h3N2 : (3 * N2).totalDegree ≤ 3 * n - 4 := (totalDegree_ofNat_mul_le 3 _).trans hN2
      exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
        · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)

def VanishesOrder {R : Type*} [CommRing R] (r : ℕ) (g : MvPolynomial (Fin 2) R) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < r → g.coeff m = 0

lemma vanishesOrder_add {R : Type*} [CommRing R] {r : ℕ} {g h : MvPolynomial (Fin 2) R}
    (hg : VanishesOrder r g) (hh : VanishesOrder r h) : VanishesOrder r (g + h) := by
  intro m hm
  have h1 : (g + h).coeff m = g.coeff m + h.coeff m := MvPolynomial.coeff_add m g h
  rw [h1, hg m hm, hh m hm, add_zero]

lemma vanishesOrder_sub {R : Type*} [CommRing R] {r : ℕ} {g h : MvPolynomial (Fin 2) R}
    (hg : VanishesOrder r g) (hh : VanishesOrder r h) : VanishesOrder r (g - h) := by
  intro m hm; rw [MvPolynomial.coeff_sub, hg m hm, hh m hm, sub_zero]

lemma vanishesOrder_mul {R : Type*} [CommRing R] {r s : ℕ} {g h : MvPolynomial (Fin 2) R}
    (hg : VanishesOrder r g) (hh : VanishesOrder s h) : VanishesOrder (r + s) (g * h) := by
  intro m hm
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  have hadd := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  have h0 : a 0 + b 0 = m 0 := congrFun (congrArg DFunLike.coe hadd) 0
  have h1 : a 1 + b 1 = m 1 := congrFun (congrArg DFunLike.coe hadd) 1
  by_cases ha : a 0 + a 1 < r
  · rw [hg a ha, zero_mul]
  · have hb : b 0 + b 1 < s := by omega
    rw [hh b hb, mul_zero]

lemma vanishesOrder_pow {R : Type*} [CommRing R] {r : ℕ} {g : MvPolynomial (Fin 2) R}
    (hg : VanishesOrder r g) (k : ℕ) : VanishesOrder (k * r) (g ^ k) := by
  induction k with
  | zero => intro m hm; omega
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact vanishesOrder_mul ih hg

lemma vanishesOrder_mono {R : Type*} [CommRing R] {r s : ℕ} {g : MvPolynomial (Fin 2) R}
    (hrs : r ≤ s) (hg : VanishesOrder s g) : VanishesOrder r g :=
  fun m hm => hg m (lt_of_lt_of_le hm hrs)

lemma vanishesOrder_ofNat_mul {R : Type*} [CommRing R] {r : ℕ} {g : MvPolynomial (Fin 2) R}
    (c : ℕ) [c.AtLeastTwo] (hg : VanishesOrder r g) :
    VanishesOrder r ((OfNat.ofNat c : MvPolynomial (Fin 2) R) * g) := by
  intro m hm
  have hC : (OfNat.ofNat c : MvPolynomial (Fin 2) R) = C (OfNat.ofNat c : R) := by
    change (c : MvPolynomial (Fin 2) R) = C (c : R); simp
  rw [hC, MvPolynomial.coeff_C_mul, hg m hm, mul_zero]

lemma vanishesOrder_pderiv {R : Type*} [CommRing R] {r : ℕ} {g : MvPolynomial (Fin 2) R}
    (i : Fin 2) (hg : VanishesOrder r g) : VanishesOrder (r - 1) (MvPolynomial.pderiv i g) := by
  intro m hm
  rw [MvPolynomial.coeff_pderiv]
  let m' : Fin 2 →₀ ℕ := m + (Finsupp.single i 1 : Fin 2 →₀ ℕ)
  have hlt : m' 0 + m' 1 < r := by
    dsimp only [m']
    fin_cases i <;> simp <;> omega
  rw [hg m' hlt, zero_mul]

lemma vanishesOrder_Dt2 {R : Type*} [CommRing R] {r s : ℕ} {f g : MvPolynomial (Fin 2) R}
    (hf : VanishesOrder r f) (hg : VanishesOrder s g) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    VanishesOrder (r + s - 2) (Dt2 f g) := by
  unfold Dt2
  have heq : (r - 1) + (s - 1) = r + s - 2 := by omega
  rw [← heq]
  exact vanishesOrder_sub
    (vanishesOrder_mul (vanishesOrder_pderiv 1 hf) (vanishesOrder_pderiv 0 hg))
    (vanishesOrder_mul (vanishesOrder_pderiv 0 hf) (vanishesOrder_pderiv 1 hg))

lemma vanishesOrder_W10_of_singular {R : Type*} [CommRing R] {p : ℕ} (hp : 1 ≤ p)
    {f : MvPolynomial (Fin 2) R} (hf : VanishesOrder 2 f) :
    VanishesOrder 8 (W10 p f) := by
  dsimp only [W10]
  have hfx : VanishesOrder 1 (MvPolynomial.pderiv 0 f) := vanishesOrder_pderiv 0 hf
  have hfy : VanishesOrder 1 (MvPolynomial.pderiv 1 f) := vanishesOrder_pderiv 1 hf
  have hB : VanishesOrder 1 (Dt2 f (MvPolynomial.pderiv 1 f)) :=
    vanishesOrder_Dt2 hf hfy (by omega) (by omega)
  have hE : VanishesOrder 1 (Dt2 f (MvPolynomial.pderiv 0 f)) :=
    vanishesOrder_Dt2 hf hfx (by omega) (by omega)
  have hN2 : VanishesOrder 2 (MvPolynomial.pderiv 0 f * Dt2 f (MvPolynomial.pderiv 1 f) -
      MvPolynomial.pderiv 1 f * Dt2 f (MvPolynomial.pderiv 0 f)) :=
    vanishesOrder_sub (vanishesOrder_mul hfx hB) (vanishesOrder_mul hfy hE)
  have hA : VanishesOrder 2 (Dt2 f (MvPolynomial.pderiv 0 f * Dt2 f (MvPolynomial.pderiv 1 f) -
      MvPolynomial.pderiv 1 f * Dt2 f (MvPolynomial.pderiv 0 f))) :=
    vanishesOrder_Dt2 hf hN2 (by omega) (by omega)
  have hDA : VanishesOrder 2 (Dt2 f (Dt2 f (MvPolynomial.pderiv 0 f * Dt2 f (MvPolynomial.pderiv 1 f) -
      MvPolynomial.pderiv 1 f * Dt2 f (MvPolynomial.pderiv 0 f)))) :=
    vanishesOrder_Dt2 hf hA (by omega) (by omega)
  have hDE : VanishesOrder 1 (Dt2 f (Dt2 f (MvPolynomial.pderiv 0 f))) :=
    vanishesOrder_Dt2 hf hE (by omega) (by omega)
  have hDB : VanishesOrder 1 (Dt2 f (Dt2 f (MvPolynomial.pderiv 1 f))) :=
    vanishesOrder_Dt2 hf hB (by omega) (by omega)
  have hK : VanishesOrder 2 (Dt2 f (MvPolynomial.pderiv 1 f) * Dt2 f (Dt2 f (MvPolynomial.pderiv 0 f)) -
      Dt2 f (MvPolynomial.pderiv 0 f) * Dt2 f (Dt2 f (MvPolynomial.pderiv 1 f))) :=
    vanishesOrder_sub (vanishesOrder_mul hB hDE) (vanishesOrder_mul hE hDB)
  have hX0 : VanishesOrder 1 (X (0 : Fin 2) : MvPolynomial (Fin 2) R) := by
    intro m hm; rw [MvPolynomial.coeff_X]; split_ifs with h
    · exfalso; rw [← h] at hm; simp at hm
    · rfl
  have hX1 : VanishesOrder 1 (X (1 : Fin 2) : MvPolynomial (Fin 2) R) := by
    intro m hm; rw [MvPolynomial.coeff_X]; split_ifs with h
    · exfalso; rw [← h] at hm; simp at hm
    · rfl
  have hDx : VanishesOrder 1 ((X (0 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 0) :=
    vanishesOrder_sub (vanishesOrder_mono (by omega) (vanishesOrder_pow hX0 p)) hX0
  have hDy : VanishesOrder 1 ((X (1 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 1) :=
    vanishesOrder_sub (vanishesOrder_mono (by omega) (vanishesOrder_pow hX1 p)) hX1
  have hPy : VanishesOrder 2 (MvPolynomial.pderiv 1 f * (X 1 ^ p - X 1) +
      MvPolynomial.pderiv 0 f * (X 0 ^ p - X 0)) :=
    vanishesOrder_add (vanishesOrder_mul hfy hDy) (vanishesOrder_mul hfx hDx)
  have hL : VanishesOrder 2 (Dt2 f (MvPolynomial.pderiv 0 f) * (X 0 ^ p - X 0) +
      Dt2 f (MvPolynomial.pderiv 1 f) * (X 1 ^ p - X 1)) :=
    vanishesOrder_add (vanishesOrder_mul hE hDx) (vanishesOrder_mul hB hDy)
  have ht1 : VanishesOrder 8 _ :=
    vanishesOrder_mul (vanishesOrder_ofNat_mul 18 (vanishesOrder_pow hN2 3)) hPy
  have ht2 : VanishesOrder 8 _ :=
    vanishesOrder_mul (vanishesOrder_ofNat_mul 9 (vanishesOrder_pow hN2 2)) (vanishesOrder_pow hL 2)
  have ht3 : VanishesOrder 8 _ :=
    vanishesOrder_mul (vanishesOrder_mul (vanishesOrder_ofNat_mul 9 hN2) hK) (vanishesOrder_pow hPy 2)
  have ht4 : VanishesOrder 8 _ :=
    vanishesOrder_mul (vanishesOrder_mul (vanishesOrder_mul (vanishesOrder_ofNat_mul 6 hA) hN2) hL) hPy
  have ht5 : VanishesOrder 8 _ :=
    vanishesOrder_mul
      (vanishesOrder_sub (vanishesOrder_ofNat_mul 4 (vanishesOrder_pow hA 2))
        (vanishesOrder_mul (vanishesOrder_ofNat_mul 3 hN2) hDA))
      (vanishesOrder_pow hPy 2)
  exact vanishesOrder_add (vanishesOrder_add (vanishesOrder_add (vanishesOrder_sub ht1 ht2) ht3) ht4) ht5

lemma W10_swap {R : Type*} [CommRing R] (p : ℕ) (f : MvPolynomial (Fin 2) R) :
    let sw : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) R :=
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom
    W10 p (sw f) = sw (W10 p f) := by
  intro sw
  have hpderiv_sw : ∀ (i : Fin 2) (g : MvPolynomial (Fin 2) R),
      MvPolynomial.pderiv i (sw g) = sw (MvPolynomial.pderiv (Equiv.swap (0 : Fin 2) 1 i) g) := by
    intro i g
    induction g using MvPolynomial.induction_on with
    | C a => simp [sw]
    | add a b ha hb => simp only [map_add, ha, hb]
    | mul_X a j ha =>
      rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, ha]
      congr 1; congr 1
      match i, j with
      | 0, 0 | 0, 1 | 1, 0 | 1, 1 =>
        simp [sw, MvPolynomial.rename_X, MvPolynomial.pderiv_X]
  have hDt_sw : ∀ g : MvPolynomial (Fin 2) R, Dt2 (sw f) (sw g) = - sw (Dt2 f g) := by
    intro g
    unfold Dt2
    rw [hpderiv_sw 1 f, hpderiv_sw 0 g, hpderiv_sw 0 f, hpderiv_sw 1 g]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, map_sub, map_mul]
    ring
  have hneg_Dt : ∀ g : MvPolynomial (Fin 2) R, Dt2 (sw f) (-g) = -Dt2 (sw f) g := by
    intro g; unfold Dt2; simp only [map_neg]; ring
  let fx := MvPolynomial.pderiv 0 f
  let fy := MvPolynomial.pderiv 1 f
  let B := Dt2 f fy
  let E := Dt2 f fx
  let N2 := fx * B - fy * E
  let A := Dt2 f N2
  let K := B * Dt2 f E - E * Dt2 f B
  let Dx : MvPolynomial (Fin 2) R := X 0 ^ p - X 0
  let Dy : MvPolynomial (Fin 2) R := X 1 ^ p - X 1
  let Py := fy * Dy + fx * Dx
  let L := E * Dx + B * Dy
  have hfx : MvPolynomial.pderiv 0 (sw f) = sw fy := by rw [hpderiv_sw 0 f]; rfl
  have hfy : MvPolynomial.pderiv 1 (sw f) = sw fx := by rw [hpderiv_sw 1 f]; rfl
  have hB : Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f)) = -sw E := by rw [hfy]; exact hDt_sw fx
  have hE : Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f)) = -sw B := by rw [hfx]; exact hDt_sw fy
  have hN2 : MvPolynomial.pderiv 0 (sw f) * Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f)) -
      MvPolynomial.pderiv 1 (sw f) * Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f)) = sw N2 := by
    rw [hB, hE, hfx, hfy]; dsimp only [N2]; simp only [map_sub, map_mul]; ring
  have hA : Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f) * Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f)) -
      MvPolynomial.pderiv 1 (sw f) * Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f))) = -sw A := by
    rw [hN2]; exact hDt_sw N2
  have hDA : Dt2 (sw f) (Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f) * Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f)) -
      MvPolynomial.pderiv 1 (sw f) * Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f)))) = sw (Dt2 f A) := by
    rw [hA, hneg_Dt, hDt_sw A, neg_neg]
  have hDE : Dt2 (sw f) (Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f))) = sw (Dt2 f B) := by
    rw [hE, hneg_Dt, hDt_sw B, neg_neg]
  have hDB : Dt2 (sw f) (Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f))) = sw (Dt2 f E) := by
    rw [hB, hneg_Dt, hDt_sw E, neg_neg]
  have hK : Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f)) * Dt2 (sw f) (Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f))) -
      Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f)) * Dt2 (sw f) (Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f))) = sw K := by
    rw [hDE, hDB, hB, hE]; dsimp only [K]; simp only [map_sub, map_mul]; ring
  have hDx : (X (0 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 0 = sw Dy := by
    dsimp only [Dy]; simp [sw, MvPolynomial.rename_X]
  have hDy : (X (1 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 1 = sw Dx := by
    dsimp only [Dx]; simp [sw, MvPolynomial.rename_X]
  have hPy : MvPolynomial.pderiv 1 (sw f) * ((X (1 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 1) +
      MvPolynomial.pderiv 0 (sw f) * ((X (0 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 0) = sw Py := by
    rw [hfx, hfy, hDx, hDy]; dsimp only [Py]; simp only [map_add, map_mul]; ring
  have hL : Dt2 (sw f) (MvPolynomial.pderiv 0 (sw f)) * ((X (0 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 0) +
      Dt2 (sw f) (MvPolynomial.pderiv 1 (sw f)) * ((X (1 : Fin 2) : MvPolynomial (Fin 2) R) ^ p - X 1) = -sw L := by
    rw [hE, hB, hDx, hDy]; dsimp only [L]; simp only [map_add, map_mul]; ring
  unfold W10
  dsimp only
  rw [hDA, hK, hA, hN2, hPy, hL]
  change 18 * sw N2 ^ 3 * sw Py - 9 * sw N2 ^ 2 * (-sw L) ^ 2 + 9 * sw N2 * sw K * sw Py ^ 2 +
    6 * (-sw A) * sw N2 * (-sw L) * sw Py + (4 * (-sw A) ^ 2 - 3 * sw N2 * sw (Dt2 f A)) * sw Py ^ 2 =
    sw (18 * N2 ^ 3 * Py - 9 * N2 ^ 2 * L ^ 2 + 9 * N2 * K * Py ^ 2 +
      6 * A * N2 * L * Py + (4 * A ^ 2 - 3 * N2 * Dt2 f A) * Py ^ 2)
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

lemma W10_translate {p : ℕ} [Fact p.Prime] (a b : ZMod p) (f : MvPolynomial (Fin 2) (ZMod p)) :
    let tr : MvPolynomial (Fin 2) (ZMod p) →+* MvPolynomial (Fin 2) (ZMod p) :=
      MvPolynomial.eval₂Hom C (fun i => match i with | 0 => X 0 + C a | 1 => X 1 + C b)
    W10 p (tr f) = tr (W10 p f) := by
  intro tr
  have hpderiv_tr : ∀ (i : Fin 2) (g : MvPolynomial (Fin 2) (ZMod p)),
      MvPolynomial.pderiv i (tr g) = tr (MvPolynomial.pderiv i g) := by
    intro i g
    induction g using MvPolynomial.induction_on with
    | C c => simp [tr]
    | add u v hu hv => simp only [map_add, hu, hv]
    | mul_X u j hu =>
      rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hu]
      congr 1; congr 1
      match i, j with
      | 0, 0 | 0, 1 | 1, 0 | 1, 1 =>
        simp [tr, MvPolynomial.pderiv_X]
  have hDt_tr : ∀ g : MvPolynomial (Fin 2) (ZMod p), Dt2 (tr f) (tr g) = tr (Dt2 f g) := by
    intro g; unfold Dt2
    rw [hpderiv_tr 1 f, hpderiv_tr 0 g, hpderiv_tr 0 f, hpderiv_tr 1 g]
    simp only [map_sub, map_mul]
  let fx := MvPolynomial.pderiv 0 f
  let fy := MvPolynomial.pderiv 1 f
  let B := Dt2 f fy
  let E := Dt2 f fx
  let N2 := fx * B - fy * E
  let A := Dt2 f N2
  let K := B * Dt2 f E - E * Dt2 f B
  let Dx : MvPolynomial (Fin 2) (ZMod p) := X 0 ^ p - X 0
  let Dy : MvPolynomial (Fin 2) (ZMod p) := X 1 ^ p - X 1
  let Py := fy * Dy + fx * Dx
  let L := E * Dx + B * Dy
  have hDx_tr : Dx = tr Dx := by
    dsimp only [Dx]; simp only [map_sub, map_pow, tr, MvPolynomial.eval₂Hom_X']
    rw [add_pow_char, ← map_pow, ZMod.pow_card]; ring
  have hDy_tr : Dy = tr Dy := by
    dsimp only [Dy]; simp only [map_sub, map_pow, tr, MvPolynomial.eval₂Hom_X']
    rw [add_pow_char, ← map_pow, ZMod.pow_card]; ring
  have hfx : MvPolynomial.pderiv 0 (tr f) = tr fx := hpderiv_tr 0 f
  have hfy : MvPolynomial.pderiv 1 (tr f) = tr fy := hpderiv_tr 1 f
  have hB : Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) = tr B := by rw [hfy]; exact hDt_tr fy
  have hE : Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) = tr E := by rw [hfx]; exact hDt_tr fx
  have hN2 : MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) = tr N2 := by
    rw [hB, hE, hfx, hfy]; dsimp only [N2]; simp only [map_sub, map_mul]
  have hA : Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) = tr A := by
    rw [hN2]; exact hDt_tr N2
  have hDA : Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)))) = tr (Dt2 f A) := by
    rw [hA]; exact hDt_tr A
  have hDE : Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) = tr (Dt2 f E) := by
    rw [hE]; exact hDt_tr E
  have hDB : Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f))) = tr (Dt2 f B) := by
    rw [hB]; exact hDt_tr B
  have hK : Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) * Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) -
      Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) * Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f))) = tr K := by
    rw [hDE, hDB, hB, hE]; dsimp only [K]; simp only [map_sub, map_mul]
  have hPy : MvPolynomial.pderiv 1 (tr f) * Dy + MvPolynomial.pderiv 0 (tr f) * Dx = tr Py := by
    rw [hfx, hfy, hDx_tr, hDy_tr]; dsimp only [Py]; simp only [map_add, map_mul]
  have hL : Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) * Dx +
      Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) * Dy = tr L := by
    rw [hE, hB, hDx_tr, hDy_tr]; dsimp only [L]; simp only [map_add, map_mul]
  unfold W10
  dsimp only
  change 18 * (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) ^ 3 *
      (MvPolynomial.pderiv 1 (tr f) * Dy + MvPolynomial.pderiv 0 (tr f) * Dx) -
    9 * (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) ^ 2 *
      (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) * Dx + Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) * Dy) ^ 2 +
    9 * (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) *
      (Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) * Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) -
      Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) * Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)))) *
      (MvPolynomial.pderiv 1 (tr f) * Dy + MvPolynomial.pderiv 0 (tr f) * Dx) ^ 2 +
    6 * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) *
      (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) *
      (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f)) * Dx + Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) * Dy) *
      (MvPolynomial.pderiv 1 (tr f) * Dy + MvPolynomial.pderiv 0 (tr f) * Dx) +
    (4 * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) ^ 2 -
      3 * (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))) *
      Dt2 (tr f) (Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 1 (tr f)) -
      MvPolynomial.pderiv 1 (tr f) * Dt2 (tr f) (MvPolynomial.pderiv 0 (tr f))))) *
      (MvPolynomial.pderiv 1 (tr f) * Dy + MvPolynomial.pderiv 0 (tr f) * Dx) ^ 2 =
    tr (18 * N2 ^ 3 * Py - 9 * N2 ^ 2 * L ^ 2 + 9 * N2 * K * Py ^ 2 +
      6 * A * N2 * L * Py + (4 * A ^ 2 - 3 * N2 * Dt2 f A) * Py ^ 2)
  rw [hDA, hK, hA, hN2, hPy, hL]
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat]

lemma W10_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ)
    (f : MvPolynomial (Fin 2) R) :
    W10 p (MvPolynomial.map φ f) = MvPolynomial.map φ (W10 p f) := by
  have hDt_map : ∀ g : MvPolynomial (Fin 2) R,
      Dt2 (MvPolynomial.map φ f) (MvPolynomial.map φ g) = MvPolynomial.map φ (Dt2 f g) := by
    intro g; unfold Dt2; simp only [MvPolynomial.pderiv_map, map_sub, map_mul]
  dsimp only [W10]
  simp only [MvPolynomial.pderiv_map, hDt_map, map_add, map_sub, map_mul, map_pow, map_ofNat,
    MvPolynomial.map_X]
  simp only [← map_mul, ← map_sub, ← map_pow, hDt_map]

end W10Polynomial

section ProjectiveH

-- Dehomogenization at X 2 = 1 and homogenization to degree d in X 2
noncomputable def dehomogZ {R : Type*} [CommRing R] :
    MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 2) R :=
  MvPolynomial.eval₂Hom C (fun i => match i with | 0 => X 0 | 1 => X 1 | 2 => 1)

noncomputable def homogZ {R : Type*} [CommRing R] (d : ℕ) (g : MvPolynomial (Fin 2) R) :
    MvPolynomial (Fin 3) R :=
  ∑ m ∈ g.support,
    monomial (Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) +
      Finsupp.single 2 (d - (m 0 + m 1))) (g.coeff m)

lemma homogZ_isHomogeneous {R : Type*} [CommRing R] {d : ℕ} {g : MvPolynomial (Fin 2) R}
    (hg : g.totalDegree ≤ d) : (homogZ d g).IsHomogeneous d := by
  unfold homogZ
  apply IsHomogeneous.sum
  intro m hm
  have hle : m 0 + m 1 ≤ d := by
    have h1 : m.sum (fun _ e => e) ≤ g.totalDegree :=
      Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum (fun _ e => e)) hm
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at h1
    omega
  apply isHomogeneous_monomial
  let t : Fin 3 →₀ ℕ := Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) +
    Finsupp.single 2 (d - (m 0 + m 1))
  change Finsupp.degree t = d
  rw [Finsupp.degree_apply, Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi),
    Fin.sum_univ_three]
  dsimp only [t]
  simp
  omega

lemma dehomogZ_homogZ {R : Type*} [CommRing R] {d : ℕ} (g : MvPolynomial (Fin 2) R) :
    dehomogZ (homogZ d g) = g := by
  unfold homogZ
  rw [map_sum]
  conv_rhs => rw [g.as_sum]
  apply Finset.sum_congr rfl
  intro m _
  dsimp only [dehomogZ]
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
    Fin.prod_univ_three]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 1),
    Finsupp.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 2),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 2),
    Finsupp.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
    Finsupp.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 1), add_zero, zero_add, one_pow, mul_one]
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]

lemma homogZ_dehomogZ_of_isHomogeneous {R : Type*} [CommRing R] {d : ℕ}
    {F : MvPolynomial (Fin 3) R} (hF : F.IsHomogeneous d) :
    homogZ d (dehomogZ F) = F := by
  have hcoeff : ∀ m : Fin 2 →₀ ℕ,
      (dehomogZ F).coeff m =
        if m 0 + m 1 ≤ d then
          F.coeff (Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) +
            Finsupp.single 2 (d - (m 0 + m 1)))
        else 0 := by
    intro m
    conv_lhs => rw [F.as_sum]
    rw [map_sum, MvPolynomial.coeff_sum]
    have hmon : ∀ s : Fin 3 →₀ ℕ,
        dehomogZ (monomial s (F.coeff s)) =
          monomial (Finsupp.single (0 : Fin 2) (s 0) + Finsupp.single 1 (s 1)) (F.coeff s) := by
      intro s
      dsimp only [dehomogZ]
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_three, one_pow, mul_one, MvPolynomial.monomial_eq,
        Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
      simp
    simp_rw [hmon, MvPolynomial.coeff_monomial]
    split_ifs with hle
    · let s₀ : Fin 3 →₀ ℕ :=
        Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1) + Finsupp.single 2 (d - (m 0 + m 1))
      by_cases hs₀ : s₀ ∈ F.support
      · rw [Finset.sum_eq_single s₀]
        · have heq : Finsupp.single (0 : Fin 2) (s₀ 0) + Finsupp.single 1 (s₀ 1) = m := by
            ext i; fin_cases i <;> simp [s₀]
          simp only [heq, ↓reduceIte]; rfl
        · intro s hs hne
          split_ifs with heq
          · exfalso; apply hne
            have hdeg := isHomogeneous_sum_eq hF hs
            rw [Fin.sum_univ_three] at hdeg
            have h0 : s 0 = m 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa using this
            have h1 : s 1 = m 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa using this
            ext i; fin_cases i <;> simp [s₀] <;> omega
          · rfl
        · intro h; exact absurd hs₀ h
      · rw [MvPolynomial.notMem_support_iff.mp hs₀]
        apply Finset.sum_eq_zero
        intro s hs
        split_ifs with heq
        · exfalso; apply hs₀
          have hdeg := isHomogeneous_sum_eq hF hs
          rw [Fin.sum_univ_three] at hdeg
          have h0 : s 0 = m 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa using this
          have h1 : s 1 = m 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa using this
          have : s = s₀ := by ext i; fin_cases i <;> simp [s₀] <;> omega
          exact this ▸ hs
        · rfl
    · apply Finset.sum_eq_zero
      intro s hs
      split_ifs with heq
      · exfalso
        have hdeg := isHomogeneous_sum_eq hF hs
        rw [Fin.sum_univ_three] at hdeg
        have h0 : s 0 = m 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa using this
        have h1 : s 1 = m 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa using this
        omega
      · rfl
  ext s
  unfold homogZ
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hs : s ∈ F.support
  · have hdeg := isHomogeneous_sum_eq hF hs
    rw [Fin.sum_univ_three] at hdeg
    let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1)
    have hm₀_sum : m₀ 0 + m₀ 1 = s 0 + s 1 := by simp [m₀]
    have hm₀_mem : m₀ ∈ (dehomogZ F).support := by
      have hle : m₀ 0 + m₀ 1 ≤ d := by omega
      rw [MvPolynomial.mem_support_iff, hcoeff]
      simp only [hle, ↓reduceIte]
      have hs_eq : Finsupp.single (0 : Fin 3) (m₀ 0) + Finsupp.single 1 (m₀ 1) +
          Finsupp.single 2 (d - (m₀ 0 + m₀ 1)) = s := by
        ext i; fin_cases i <;> (simp [m₀]; try omega)
      rw [hs_eq]
      exact MvPolynomial.mem_support_iff.mp hs
    rw [Finset.sum_eq_single m₀]
    · have hs_eq : Finsupp.single (0 : Fin 3) (m₀ 0) + Finsupp.single 1 (m₀ 1) +
          Finsupp.single 2 (d - (m₀ 0 + m₀ 1)) = s := by
        ext i; fin_cases i <;> (simp [m₀]; try omega)
      have hle : m₀ 0 + m₀ 1 ≤ d := by omega
      simp only [hs_eq, ↓reduceIte, hcoeff, hle]
    · intro m _ hne
      split_ifs with heq
      · exfalso; apply hne
        have h0 : m 0 = s 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa using this
        have h1 : m 1 = s 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa using this
        ext i; fin_cases i <;> simp [m₀, h0, h1]
      · rfl
    · intro h; exact absurd hm₀_mem h
  · rw [MvPolynomial.notMem_support_iff.mp hs]
    apply Finset.sum_eq_zero
    intro m hm
    split_ifs with heq
    · rw [hcoeff]
      split_ifs with hle
      · rw [heq]; exact MvPolynomial.notMem_support_iff.mp hs
      · rfl
    · rfl

lemma dehomogZ_pderiv_0 {R : Type*} [CommRing R] (F : MvPolynomial (Fin 3) R) :
    dehomogZ (MvPolynomial.pderiv 0 F) = MvPolynomial.pderiv 0 (dehomogZ F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [dehomogZ]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a i ha =>
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, map_mul, MvPolynomial.pderiv_mul, ha]
    congr 1; congr 1
    fin_cases i <;> simp [dehomogZ, MvPolynomial.pderiv_X]

lemma dehomogZ_pderiv_1 {R : Type*} [CommRing R] (F : MvPolynomial (Fin 3) R) :
    dehomogZ (MvPolynomial.pderiv 1 F) = MvPolynomial.pderiv 1 (dehomogZ F) := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [dehomogZ]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a i ha =>
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, map_mul, MvPolynomial.pderiv_mul, ha]
    congr 1; congr 1
    fin_cases i <;> simp [dehomogZ, MvPolynomial.pderiv_X]

lemma eval_dehomogZ {R : Type*} [CommRing R] (F : MvPolynomial (Fin 3) R) (a b : R) :
    eval ![a, b] (dehomogZ F) = eval ![a, b, 1] F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [dehomogZ]
  | add u v hu hv => simp only [map_add, hu, hv]
  | mul_X u i hu =>
    fin_cases i <;> (rw [map_mul, map_mul, map_mul, hu]; simp [dehomogZ])

lemma eq_of_dehomogZ_eq_of_isHomogeneous {R : Type*} [CommRing R] {d : ℕ}
    {P Q : MvPolynomial (Fin 3) R} (hP : P.IsHomogeneous d) (hQ : Q.IsHomogeneous d)
    (heq : dehomogZ P = dehomogZ Q) : P = Q := by
  rw [← homogZ_dehomogZ_of_isHomogeneous hP, ← homogZ_dehomogZ_of_isHomogeneous hQ, heq]

lemma dvd_of_dehomogZ_dvd {R : Type*} [CommRing R] {d n : ℕ}
    {F G : MvPolynomial (Fin 3) R} (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous d)
    (hdvd : dehomogZ F ∣ dehomogZ G) :
    ∃ k : ℕ, F ∣ X 2 ^ k * G := by
  rcases hdvd with ⟨q, hq⟩
  let m := q.totalDegree
  let Q := homogZ m q
  have hQh : Q.IsHomogeneous m := homogZ_isHomogeneous (le_refl m)
  have hde_FQ : dehomogZ (F * Q) = dehomogZ G := by
    rw [map_mul, dehomogZ_homogZ, hq]
  by_cases hle : d ≤ n + m
  · refine ⟨n + m - d, Q, ?_⟩
    have hLHS : (X (2 : Fin 3) ^ (n + m - d) * G).IsHomogeneous (n + m) := by
      have hx : (X (2 : Fin 3) ^ (n + m - d) : MvPolynomial (Fin 3) R).IsHomogeneous (n + m - d) := by
        simpa using (isHomogeneous_X R (2 : Fin 3)).pow (n + m - d)
      have h1 := hx.mul hG
      rwa [show n + m - d + d = n + m by omega] at h1
    have hRHS : (F * Q).IsHomogeneous (n + m) := hF.mul hQh
    apply eq_of_dehomogZ_eq_of_isHomogeneous hLHS hRHS
    rw [map_mul, map_pow, show dehomogZ (X (2 : Fin 3) : MvPolynomial (Fin 3) R) = 1 by simp [dehomogZ],
      one_pow, one_mul, hde_FQ]
  · refine ⟨0, X 2 ^ (d - (n + m)) * Q, ?_⟩
    rw [pow_zero, one_mul]
    have hRHS : (F * (X 2 ^ (d - (n + m)) * Q)).IsHomogeneous d := by
      have hx : (X (2 : Fin 3) ^ (d - (n + m)) : MvPolynomial (Fin 3) R).IsHomogeneous (d - (n + m)) := by
        simpa using (isHomogeneous_X R (2 : Fin 3)).pow (d - (n + m))
      have h1 := hF.mul (hx.mul hQh)
      rwa [show n + (d - (n + m) + m) = d by omega] at h1
    apply eq_of_dehomogZ_eq_of_isHomogeneous hG hRHS
    rw [map_mul, map_mul, map_pow,
      show dehomogZ (X (2 : Fin 3) : MvPolynomial (Fin 3) R) = 1 by simp [dehomogZ],
      one_pow, one_mul, ← map_mul, hde_FQ]

def cyc3 : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

noncomputable def rot3 {R : Type*} [CommRing R] :
    MvPolynomial (Fin 3) R ≃+* MvPolynomial (Fin 3) R :=
  (MvPolynomial.renameEquiv R cyc3).toRingEquiv

lemma rot3_isHomogeneous {R : Type*} [CommRing R] {d : ℕ} {F : MvPolynomial (Fin 3) R}
    (hF : F.IsHomogeneous d) : (rot3 F).IsHomogeneous d := by
  rw [F.as_sum, map_sum]
  apply IsHomogeneous.sum
  intro s hs
  change (MvPolynomial.rename cyc3 (monomial s (F.coeff s))).IsHomogeneous d
  rw [MvPolynomial.rename_monomial]
  apply isHomogeneous_monomial
  change (Finsupp.mapDomain cyc3 s).sum (fun _ e => e) = d
  rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact isHomogeneous_sum_eq hF hs

lemma rot3_X {R : Type*} [CommRing R] (i : Fin 3) :
    rot3 (X i : MvPolynomial (Fin 3) R) = X (cyc3 i) :=
  MvPolynomial.rename_X cyc3 i

lemma eval_rot3 {R : Type*} [CommRing R] (F : MvPolynomial (Fin 3) R) (v : Fin 3 → R) :
    eval v (rot3 F) = eval (v ∘ cyc3) F :=
  MvPolynomial.eval_rename cyc3 v F

noncomputable def W10Z {R : Type*} [CommRing R] (p n : ℕ) (F : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  homogZ (2 * p + 10 * n - 14) (W10 p (dehomogZ F))

noncomputable def W10X {R : Type*} [CommRing R] (p n : ℕ) (F : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  rot3 (W10Z p n (rot3.symm F))

noncomputable def W10Y {R : Type*} [CommRing R] (p n : ℕ) (F : MvPolynomial (Fin 3) R) :
    MvPolynomial (Fin 3) R :=
  rot3.symm (W10Z p n (rot3 F))

lemma eval_dehomogZ_rot3_symm {R : Type*} [CommRing R] (F : MvPolynomial (Fin 3) R) (a b : R) :
    eval ![a, b] (dehomogZ (rot3.symm F)) = eval ![1, a, b] F := by
  rw [eval_dehomogZ]
  change eval ![a, b, 1] (MvPolynomial.rename cyc3.symm F) = _
  rw [MvPolynomial.eval_rename]
  exact congrArg (fun v => eval v F) (by ext i; fin_cases i <;> rfl)

lemma prime_X_mv {K : Type*} [Field K] {σ : Type*} (i : σ) :
    Prime (X i : MvPolynomial σ K) := by
  have hne : (X i : MvPolynomial σ K) ≠ 0 := MvPolynomial.X_ne_zero i
  have hnotu : ¬ IsUnit (X i : MvPolynomial σ K) := by
    rintro ⟨u, hu⟩
    have h1 := congrArg (eval (0 : σ → K)) u.mul_inv
    rw [hu, map_mul, eval_X, map_one, Pi.zero_apply, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨hne, hnotu, ?_⟩
  let ev0 : MvPolynomial σ K →+* MvPolynomial σ K :=
    MvPolynomial.eval₂Hom C (fun j => if j = i then 0 else X j)
  have hev0_coeff : ∀ (P : MvPolynomial σ K) (s : σ →₀ ℕ),
      (ev0 P).coeff s = if s i = 0 then P.coeff s else 0 := by
    intro P s
    conv_lhs => rw [P.as_sum]
    rw [map_sum, MvPolynomial.coeff_sum]
    have hterm : ∀ t : σ →₀ ℕ,
        (ev0 (monomial t (P.coeff t))).coeff s =
          if t i = 0 ∧ t = s then P.coeff t else 0 := by
      intro t
      dsimp only [ev0]
      rw [MvPolynomial.eval₂Hom_monomial]
      by_cases hti : t i = 0
      · have hprod : (t.prod fun j e => (if j = i then (0 : MvPolynomial σ K) else X j) ^ e) =
            t.prod fun j e => X j ^ e := by
          unfold Finsupp.prod
          apply Finset.prod_congr rfl
          intro j hj
          have hji : j ≠ i := fun h => by subst h; exact Finsupp.mem_support_iff.mp hj hti
          simp [hji]
        rw [hprod, ← MvPolynomial.monomial_eq, MvPolynomial.coeff_monomial]
        simp [hti]
      · have hzero : (t.prod fun j e => (if j = i then (0 : MvPolynomial σ K) else X j) ^ e) = 0 := by
          unfold Finsupp.prod
          apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hti)
          simp [zero_pow hti]
        have hnt : ¬ (t i = 0 ∧ t = s) := by tauto
        rw [hzero, mul_zero]; simp only [hnt, ↓reduceIte]; rfl
    simp_rw [hterm]
    split_ifs with hsi
    · by_cases hs : s ∈ P.support
      · rw [Finset.sum_eq_single s]
        · simp only [hsi, true_and, ↓reduceIte]
        · intro t _ hne
          have hnt : ¬ (t i = 0 ∧ t = s) := by tauto
          simp only [hnt, ↓reduceIte]
        · intro h; exact absurd hs h
      · rw [MvPolynomial.notMem_support_iff.mp hs]
        apply Finset.sum_eq_zero; intro t ht; split_ifs with hcond
        · exact absurd (hcond.2 ▸ ht) hs
        · rfl
    · apply Finset.sum_eq_zero; intro t _; split_ifs with hcond
      · exact absurd (hcond.2 ▸ hcond.1) hsi
      · rfl
  have hdvd_iff : ∀ P : MvPolynomial σ K, X i ∣ P ↔ ev0 P = 0 := by
    intro P
    constructor
    · rintro ⟨Q, rfl⟩
      rw [map_mul, show ev0 (X i) = 0 by simp [ev0], zero_mul]
    · intro h0
      refine ⟨∑ s ∈ P.support, monomial (s - Finsupp.single i 1) (P.coeff s), ?_⟩
      conv_lhs => rw [P.as_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      have hsi : s i ≠ 0 := by
        intro hsi0
        have hc := congrArg (fun q : MvPolynomial σ K => q.coeff s) h0
        rw [hev0_coeff, MvPolynomial.coeff_zero] at hc; simp only [hsi0, ↓reduceIte] at hc
        exact MvPolynomial.mem_support_iff.mp hs hc
      rw [show (X i : MvPolynomial σ K) = monomial (Finsupp.single i 1) 1 from rfl,
        MvPolynomial.monomial_mul, one_mul]
      refine congrArg (fun d => monomial d (P.coeff s)) ?_
      ext j
      by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Finsupp.single_eq_of_ne hj]
  intro P Q hPQ
  simp_rw [hdvd_iff] at hPQ ⊢
  rw [map_mul, mul_eq_zero] at hPQ
  exact hPQ

lemma isUnit_mv_iff_eq_C {K : Type*} [Field K] {σ : Type*} {P : MvPolynomial σ K} :
    IsUnit P ↔ ∃ c : K, c ≠ 0 ∧ P = C c := by
  rw [MvPolynomial.isUnit_iff]
  constructor
  · rintro ⟨h0, hnil⟩
    refine ⟨P.coeff 0, isUnit_iff_ne_zero.mp h0, ?_⟩
    ext m
    rw [MvPolynomial.coeff_C]
    split_ifs with hm
    · subst hm; rfl
    · exact isNilpotent_iff_eq_zero.mp (hnil m (Ne.symm hm))
  · rintro ⟨c, hc0, rfl⟩
    refine ⟨by simpa [isUnit_iff_ne_zero] using hc0, fun m hm => ?_⟩
    rw [MvPolynomial.coeff_C]; simp only [Ne.symm hm, ↓reduceIte]
    exact IsNilpotent.zero

lemma irreducible_of_map_irreducible {p : ℕ} [Fact p.Prime] {F : MvPolynomial (Fin 3) (ZMod p)}
    (hF : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) F)) :
    Irreducible F := by
  let ι := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  have hinj : Function.Injective ι := ι.injective
  have hnotu : ¬ IsUnit F := fun hu => hF.not_isUnit (hu.map (MvPolynomial.map ι))
  refine ⟨hnotu, ?_⟩
  intro A B hAB
  have hmap : MvPolynomial.map ι F = MvPolynomial.map ι A * MvPolynomial.map ι B := by
    rw [hAB, map_mul]
  rcases hF.isUnit_or_isUnit hmap with hA | hB
  · left
    rw [isUnit_mv_iff_eq_C] at hA ⊢
    rcases hA with ⟨c, hc0, hc_eq⟩
    refine ⟨A.coeff 0, ?_, ?_⟩
    · intro h0
      have := congrArg (fun P : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p)) => P.coeff 0) hc_eq
      rw [MvPolynomial.coeff_C, MvPolynomial.coeff_map, h0, map_zero] at this; simp only [↓reduceIte] at this
      exact hc0 this.symm
    · ext m
      apply hinj
      rw [← MvPolynomial.coeff_map, hc_eq, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
      split_ifs with hm
      · subst hm
        have := congrArg (fun P : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p)) => P.coeff 0) hc_eq
        rw [MvPolynomial.coeff_C, MvPolynomial.coeff_map] at this; simp only [↓reduceIte] at this
        exact this.symm
      · simp
  · right
    rw [isUnit_mv_iff_eq_C] at hB ⊢
    rcases hB with ⟨c, hc0, hc_eq⟩
    refine ⟨B.coeff 0, ?_, ?_⟩
    · intro h0
      have := congrArg (fun P : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p)) => P.coeff 0) hc_eq
      rw [MvPolynomial.coeff_C, MvPolynomial.coeff_map, h0, map_zero] at this; simp only [↓reduceIte] at this
      exact hc0 this.symm
    · ext m
      apply hinj
      rw [← MvPolynomial.coeff_map, hc_eq, MvPolynomial.coeff_C, MvPolynomial.coeff_C]
      split_ifs with hm
      · subst hm
        have := congrArg (fun P : MvPolynomial (Fin 3) (AlgebraicClosure (ZMod p)) => P.coeff 0) hc_eq
        rw [MvPolynomial.coeff_C, MvPolynomial.coeff_map] at this; simp only [↓reduceIte] at this
        exact this.symm
      · simp

lemma irreducible_dehomogZ {K : Type*} [Field K] {n : ℕ} {F : MvPolynomial (Fin 3) K}
    (hF : F.IsHomogeneous n) (hFirr : Irreducible F) (hZ : ¬ (X (2 : Fin 3) ∣ F)) :
    Irreducible (dehomogZ F) := by
  have hf0 : dehomogZ F ≠ 0 := by
    intro h0
    apply hFirr.ne_zero
    rw [← homogZ_dehomogZ_of_isHomogeneous hF, h0]
    simp [homogZ]
  have hX2_ndvd_homog : ∀ (g : MvPolynomial (Fin 2) K), g ≠ 0 →
      ¬ (X (2 : Fin 3) ∣ homogZ g.totalDegree g) := by
    intro g hg0 ⟨Q, hQ⟩
    obtain ⟨m, hm, hdeg_eq⟩ : ∃ m ∈ g.support, m.sum (fun _ e => e) = g.totalDegree := by
      have hne : g.support.Nonempty := MvPolynomial.support_nonempty.mpr hg0
      obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image g.support (fun s : Fin 2 →₀ ℕ => s.sum (fun _ e => e)) hne
      refine ⟨m, hm, le_antisymm
        (Finset.le_sup (f := fun s : Fin 2 →₀ ℕ => s.sum (fun _ e => e)) hm)
        (Finset.sup_le (fun s hs => hmax s hs))⟩
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hdeg_eq
    let s₀ : Fin 3 →₀ ℕ := Finsupp.single 0 (m 0) + Finsupp.single 1 (m 1)
    have hc1 : (homogZ g.totalDegree g).coeff s₀ = g.coeff m := by
      unfold homogZ
      rw [MvPolynomial.coeff_sum]
      simp_rw [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single m]
      · have h0 : g.totalDegree - (m 0 + m 1) = 0 := by omega
        have hs₀ : Finsupp.single (0 : Fin 3) (m 0) + Finsupp.single 1 (m 1) + Finsupp.single 2 (g.totalDegree - (m 0 + m 1)) = s₀ := by simp [s₀, h0]
        simp only [hs₀, ↓reduceIte]
      · intro s _ hne
        split_ifs with heq
        · exfalso; apply hne
          have h0 : s 0 = m 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa [s₀] using this
          have h1 : s 1 = m 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa [s₀] using this
          ext i; fin_cases i <;> assumption
        · rfl
      · intro h; exact absurd hm h
    have hc2 : (X (2 : Fin 3) * Q).coeff s₀ = 0 := by
      rw [mul_comm, MvPolynomial.coeff_mul_X']
      split_ifs with hmem
      · exfalso; have : s₀ 2 ≠ 0 := Finsupp.mem_support_iff.mp hmem; simp [s₀] at this
      · rfl
    rw [hQ, hc2] at hc1
    exact MvPolynomial.mem_support_iff.mp hm hc1.symm
  have hnotu : ¬ IsUnit (dehomogZ F) := by
    intro hu
    rw [isUnit_mv_iff_eq_C] at hu
    rcases hu with ⟨c, hc0, hceq⟩
    have hCeq : homogZ n (C c) = C c * X (2 : Fin 3) ^ n := by
      unfold homogZ
      have hsupp : (C c : MvPolynomial (Fin 2) K).support = {0} := by
        ext m; simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C, hc0, eq_comm]
      rw [hsupp, Finset.sum_singleton]
      simp [MvPolynomial.monomial_eq, Finsupp.prod_single_index]
    have hFeq : F = C c * X (2 : Fin 3) ^ n := by
      rw [← homogZ_dehomogZ_of_isHomogeneous hF, hceq, hCeq]
    cases n with
    | zero =>
      rw [pow_zero, mul_one] at hFeq
      exact hFirr.not_isUnit (hFeq ▸ (isUnit_iff_ne_zero.mpr hc0).map C)
    | succ n =>
      apply hZ
      exact ⟨C c * X 2 ^ n, by rw [hFeq, pow_succ]; ring⟩
  refine ⟨hnotu, ?_⟩
  intro a b hab
  have ha0 : a ≠ 0 := fun h => hf0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hf0 (by rw [hab, h, mul_zero])
  let A := homogZ a.totalDegree a
  let B := homogZ b.totalDegree b
  have hAh : A.IsHomogeneous a.totalDegree := homogZ_isHomogeneous (le_refl _)
  have hBh : B.IsHomogeneous b.totalDegree := homogZ_isHomogeneous (le_refl _)
  have hAB_de : dehomogZ (A * B) = dehomogZ F := by
    rw [map_mul, dehomogZ_homogZ, dehomogZ_homogZ, hab]
  have hdeg_eq : a.totalDegree + b.totalDegree = n := by
    have hABh : (A * B).IsHomogeneous (a.totalDegree + b.totalDegree) := hAh.mul hBh
    have hX2_prime : Prime (X (2 : Fin 3) : MvPolynomial (Fin 3) K) := prime_X_mv 2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hFeq : F = X 2 ^ (n - (a.totalDegree + b.totalDegree)) * (A * B) := by
        apply eq_of_dehomogZ_eq_of_isHomogeneous hF
        · have hx : (X (2 : Fin 3) ^ (n - (a.totalDegree + b.totalDegree)) : MvPolynomial (Fin 3) K).IsHomogeneous
              (n - (a.totalDegree + b.totalDegree)) := by
            simpa using (isHomogeneous_X K (2 : Fin 3)).pow (n - (a.totalDegree + b.totalDegree))
          have h1 := hx.mul hABh
          rwa [show n - (a.totalDegree + b.totalDegree) + (a.totalDegree + b.totalDegree) = n by omega] at h1
        · rw [map_mul, map_pow,
            show dehomogZ (X (2 : Fin 3) : MvPolynomial (Fin 3) K) = 1 by simp [dehomogZ],
            one_pow, one_mul, hAB_de]
      apply hZ
      have hk : 1 ≤ n - (a.totalDegree + b.totalDegree) := by omega
      refine ⟨X 2 ^ (n - (a.totalDegree + b.totalDegree) - 1) * (A * B), ?_⟩
      calc F = X 2 ^ (n - (a.totalDegree + b.totalDegree)) * (A * B) := hFeq
        _ = X 2 ^ (n - (a.totalDegree + b.totalDegree) - 1 + 1) * (A * B) := by congr 2; omega
        _ = X 2 * (X 2 ^ (n - (a.totalDegree + b.totalDegree) - 1) * (A * B)) := by rw [pow_succ']; ring
    · have hABeq : A * B = X 2 ^ (a.totalDegree + b.totalDegree - n) * F := by
        apply eq_of_dehomogZ_eq_of_isHomogeneous hABh
        · have hx : (X (2 : Fin 3) ^ (a.totalDegree + b.totalDegree - n) : MvPolynomial (Fin 3) K).IsHomogeneous
              (a.totalDegree + b.totalDegree - n) := by
            simpa using (isHomogeneous_X K (2 : Fin 3)).pow (a.totalDegree + b.totalDegree - n)
          have h1 := hx.mul hF
          rwa [show a.totalDegree + b.totalDegree - n + n = a.totalDegree + b.totalDegree by omega] at h1
        · rw [hAB_de, map_mul, map_pow,
            show dehomogZ (X (2 : Fin 3) : MvPolynomial (Fin 3) K) = 1 by simp [dehomogZ],
            one_pow, one_mul]
      have hdvd : X (2 : Fin 3) ∣ A * B := by
        have hk : 1 ≤ a.totalDegree + b.totalDegree - n := by omega
        refine ⟨X 2 ^ (a.totalDegree + b.totalDegree - n - 1) * F, ?_⟩
        calc A * B = X 2 ^ (a.totalDegree + b.totalDegree - n) * F := hABeq
          _ = X 2 ^ (a.totalDegree + b.totalDegree - n - 1 + 1) * F := by congr 2; omega
          _ = X 2 * (X 2 ^ (a.totalDegree + b.totalDegree - n - 1) * F) := by rw [pow_succ']; ring
      rcases hX2_prime.dvd_or_dvd hdvd with hA_dvd | hB_dvd
      · exact hX2_ndvd_homog a ha0 hA_dvd
      · exact hX2_ndvd_homog b hb0 hB_dvd
  have hFeq : F = A * B := by
    apply eq_of_dehomogZ_eq_of_isHomogeneous hF
    · rw [← hdeg_eq]; exact hAh.mul hBh
    · exact hAB_de.symm
  rcases hFirr.isUnit_or_isUnit hFeq with hAu | hBu
  · left; rw [← dehomogZ_homogZ (d := a.totalDegree) a]; exact hAu.map dehomogZ
  · right; rw [← dehomogZ_homogZ (d := b.totalDegree) b]; exact hBu.map dehomogZ

lemma isHomogeneous_of_dvd_homog {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    {Φ P H : MvPolynomial σ K} {n : ℕ}
    (hΦ : Φ.IsHomogeneous n) (hΦ0 : Φ ≠ 0) (hmul : P * H = Φ) :
    P.IsHomogeneous P.totalDegree ∧ H.IsHomogeneous H.totalDegree ∧
      P.totalDegree + H.totalDegree = n := by
  have hP0 : P ≠ 0 := by intro h; rw [h, zero_mul] at hmul; exact hΦ0 hmul.symm
  have hH0 : H ≠ 0 := by intro h; rw [h, mul_zero] at hmul; exact hΦ0 hmul.symm
  let S_P := P.support.image Finsupp.degree
  let S_H := H.support.image Finsupp.degree
  have hSP_ne : S_P.Nonempty := (MvPolynomial.support_nonempty.mpr hP0).image _
  have hSH_ne : S_H.Nonempty := (MvPolynomial.support_nonempty.mpr hH0).image _
  let a_min := S_P.min' hSP_ne
  let a_max := S_P.max' hSP_ne
  let b_min := S_H.min' hSH_ne
  let b_max := S_H.max' hSH_ne
  have hc_ne : ∀ (Q : MvPolynomial σ K) (d : ℕ),
      d ∈ Q.support.image Finsupp.degree → homogeneousComponent d Q ≠ 0 := by
    intro Q d hd h0
    rcases mem_image.mp hd with ⟨m, hm, rfl⟩
    have hc := congrArg (fun f : MvPolynomial σ K => f.coeff m) h0
    rw [coeff_homogeneousComponent, MvPolynomial.coeff_zero] at hc; simp only [↓reduceIte] at hc
    exact MvPolynomial.mem_support_iff.mp hm hc
  have hΦ_comp_zero : ∀ k : ℕ, k ≠ n → homogeneousComponent k Φ = 0 := by
    intro k hkn
    ext m
    rw [coeff_homogeneousComponent, MvPolynomial.coeff_zero]
    split_ifs with hdeg
    · by_contra hne
      have h := hΦ hne
      rw [weight_one_eq_degree] at h
      exact hkn (hdeg.symm.trans h)
    · rfl
  have hmin_eq : a_min + b_min = n := by
    have hcomp : homogeneousComponent (a_min + b_min) (P * H) =
        homogeneousComponent a_min P * homogeneousComponent b_min H := by
      ext m
      rw [coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
      split_ifs with hdeg
      · apply Finset.sum_congr rfl
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = a_min + b_min := by
          rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hxy, hdeg]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        by_cases hx : P.coeff x = 0
        · simp [hx]
        · by_cases hy : H.coeff y = 0
          · simp [hy]
          · have hxa : a_min ≤ Finsupp.degree x :=
              Finset.min'_le S_P _ (mem_image.mpr ⟨x, MvPolynomial.mem_support_iff.mpr hx, rfl⟩)
            have hyb : b_min ≤ Finsupp.degree y :=
              Finset.min'_le S_H _ (mem_image.mpr ⟨y, MvPolynomial.mem_support_iff.mpr hy, rfl⟩)
            have hxe : Finsupp.degree x = a_min := by omega
            have hye : Finsupp.degree y = b_min := by omega
            simp [hxe, hye]
      · symm
        apply Finset.sum_eq_zero
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = Finsupp.degree m := by
          rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hxy]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        split_ifs with hx hy
        · exact absurd (by rw [← hsum, hx, hy]) hdeg
        · ring
        · ring
        · ring
    have hne : homogeneousComponent (a_min + b_min) Φ ≠ 0 := by
      rw [← hmul, hcomp]
      exact mul_ne_zero (hc_ne P a_min (Finset.min'_mem _ _)) (hc_ne H b_min (Finset.min'_mem _ _))
    by_contra hneq
    exact hne (hΦ_comp_zero _ hneq)
  have hmax_eq : a_max + b_max = n := by
    have hcomp : homogeneousComponent (a_max + b_max) (P * H) =
        homogeneousComponent a_max P * homogeneousComponent b_max H := by
      ext m
      rw [coeff_homogeneousComponent, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul]
      split_ifs with hdeg
      · apply Finset.sum_congr rfl
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = a_max + b_max := by
          rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hxy, hdeg]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        by_cases hx : P.coeff x = 0
        · simp [hx]
        · by_cases hy : H.coeff y = 0
          · simp [hy]
          · have hxa : Finsupp.degree x ≤ a_max :=
              Finset.le_max' S_P _ (mem_image.mpr ⟨x, MvPolynomial.mem_support_iff.mpr hx, rfl⟩)
            have hyb : Finsupp.degree y ≤ b_max :=
              Finset.le_max' S_H _ (mem_image.mpr ⟨y, MvPolynomial.mem_support_iff.mpr hy, rfl⟩)
            have hxe : Finsupp.degree x = a_max := by omega
            have hye : Finsupp.degree y = b_max := by omega
            simp [hxe, hye]
      · symm
        apply Finset.sum_eq_zero
        intro ⟨x, y⟩ hxy
        have hsum : Finsupp.degree x + Finsupp.degree y = Finsupp.degree m := by
          rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hxy]
        rw [coeff_homogeneousComponent, coeff_homogeneousComponent]
        split_ifs with hx hy
        · exact absurd (by rw [← hsum, hx, hy]) hdeg
        · ring
        · ring
        · ring
    have hne : homogeneousComponent (a_max + b_max) Φ ≠ 0 := by
      rw [← hmul, hcomp]
      exact mul_ne_zero (hc_ne P a_max (Finset.max'_mem _ _)) (hc_ne H b_max (Finset.max'_mem _ _))
    by_contra hneq
    exact hne (hΦ_comp_zero _ hneq)
  have ha_le : a_min ≤ a_max := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hb_le : b_min ≤ b_max := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have ha_eq : a_min = a_max := by omega
  have hb_eq : b_min = b_max := by omega
  have hPh : P.IsHomogeneous a_min := by
    intro m hm
    have hmem : Finsupp.degree m ∈ S_P := mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
    have h1 := Finset.min'_le S_P _ hmem
    have h2 := Finset.le_max' S_P _ hmem
    rw [weight_one_eq_degree]; omega
  have hHh : H.IsHomogeneous b_min := by
    intro m hm
    have hmem : Finsupp.degree m ∈ S_H := mem_image.mpr ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
    have h1 := Finset.min'_le S_H _ hmem
    have h2 := Finset.le_max' S_H _ hmem
    rw [weight_one_eq_degree]; omega
  exact ⟨(hPh.totalDegree hP0) ▸ hPh, (hHh.totalDegree hH0) ▸ hHh, by
    rw [hPh.totalDegree hP0, hHh.totalDegree hH0]; omega⟩

lemma not_dvd_of_isHomogeneous_lt {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    {F G : MvPolynomial σ K} {n d : ℕ}
    (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) (hG : G.IsHomogeneous d) (hG0 : G ≠ 0) (h : d < n) :
    ¬ (F ∣ G) := by
  rintro ⟨Q, hQ⟩
  obtain ⟨_, _, hsum⟩ := isHomogeneous_of_dvd_homog hG hG0 hQ.symm
  rw [hF.totalDegree hF0] at hsum
  omega

lemma not_dvd_dehomogZ_of_homog_lt {K : Type*} [Field K] {n d : ℕ}
    {F G : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous n) (hFirr : Irreducible F)
    (hG : G.IsHomogeneous d) (hG0 : G ≠ 0) (hd : d < n) (hn : 2 ≤ n) :
    ¬ (dehomogZ F ∣ dehomogZ G) := by
  intro hdvd
  obtain ⟨k, hk⟩ := dvd_of_dehomogZ_dvd hF hG hdvd
  have hFndvdX2 : ¬ (F ∣ X (2 : Fin 3)) :=
    not_dvd_of_isHomogeneous_lt hF hFirr.ne_zero (isHomogeneous_X K 2) (MvPolynomial.X_ne_zero 2) (by omega)
  have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
  have hFG : F ∣ G := by
    induction k with
    | zero => simpa using hk
    | succ k ih =>
      rw [pow_succ', mul_assoc] at hk
      rcases hFprime.dvd_or_dvd hk with hX | hrest
      · exact absurd hX hFndvdX2
      · exact ih hrest
  exact not_dvd_of_isHomogeneous_lt hF hFirr.ne_zero hG hG0 hd hFG

-- Abstract connection between fwMatrix and W10 along any differential hom φ : R[x,y] →+* L
lemma det_fwMatrix_eq_W10_of_deriv {R L : Type*} [CommRing R] [Field L]
    (p : ℕ) (φ : MvPolynomial (Fin 2) R →+* L) (D : RingDeriv L) (f : MvPolynomial (Fin 2) R)
    (hDx : D (φ (X 0)) = 1)
    (hDφ : ∀ g : MvPolynomial (Fin 2) R, D (φ g) = φ (Dt2 f g) / φ (MvPolynomial.pderiv 1 f))
    (hfy : φ (MvPolynomial.pderiv 1 f) ≠ 0) :
    (fwMatrix p D ![1, φ (X 0), φ (X 1), φ (X 0) ^ 2, φ (X 0) * φ (X 1), φ (X 1) ^ 2]).det =
      2 * φ (W10 p f) / φ (MvPolynomial.pderiv 1 f) ^ 10 := by
  let fx := MvPolynomial.pderiv 0 f
  let fy := MvPolynomial.pderiv 1 f
  let B := Dt2 f fy
  let E := Dt2 f fx
  let N2 := fx * B - fy * E
  let N3 := Dt2 f N2 * fy - 3 * N2 * B
  let N4 := Dt2 f N3 * fy - 5 * N3 * B
  let Dx_p : MvPolynomial (Fin 2) R := X 0 ^ p - X 0
  let Dy_p : MvPolynomial (Fin 2) R := X 1 ^ p - X 1
  let Py := fy * Dy_p + fx * Dx_p
  have hy1 : D (φ (X 1)) = -(φ fx / φ fy) := by
    rw [hDφ (X 1)]
    have hDt : Dt2 f (X 1) = -fx := by
      unfold Dt2; simp [fx, MvPolynomial.pderiv_X]
    rw [hDt, map_neg, neg_div]
  have hy2 : D (D (φ (X 1))) = φ N2 / φ fy ^ 3 := by
    rw [hy1, D.map_neg, D.map_div _ _ hfy, hDφ fx, hDφ fy]
    have h1 : φ N2 = φ fx * φ B - φ fy * φ E := by dsimp only [N2]; simp
    rw [h1]
    change -((φ E / φ fy * φ fy - φ fx * (φ B / φ fy)) / φ fy ^ 2) =
      (φ fx * φ B - φ fy * φ E) / φ fy ^ 3
    field_simp [hfy]
    ring
  have hy3 : D (D (D (φ (X 1)))) = φ N3 / φ fy ^ 5 := by
    rw [hy2, D.map_div _ _ (pow_ne_zero 3 hfy), hDφ N2, D.map_pow, hDφ fy]
    have h1 : φ N3 = φ (Dt2 f N2) * φ fy - 3 * φ N2 * φ B := by
      dsimp only [N3]; simp only [map_sub, map_mul, map_ofNat]
    rw [h1]
    change (φ (Dt2 f N2) / φ fy * φ fy ^ 3 - φ N2 * ((3 : L) * φ fy ^ 2 * (φ B / φ fy))) /
      (φ fy ^ 3) ^ 2 = (φ (Dt2 f N2) * φ fy - 3 * φ N2 * φ B) / φ fy ^ 5
    field_simp [hfy]
  have hy4 : D (D (D (D (φ (X 1))))) = φ N4 / φ fy ^ 7 := by
    rw [hy3, D.map_div _ _ (pow_ne_zero 5 hfy), hDφ N3, D.map_pow, hDφ fy]
    have h1 : φ N4 = φ (Dt2 f N3) * φ fy - 5 * φ N3 * φ B := by
      dsimp only [N4]; simp only [map_sub, map_mul, map_ofNat]
    rw [h1]
    change (φ (Dt2 f N3) / φ fy * φ fy ^ 5 - φ N3 * ((5 : L) * φ fy ^ 4 * (φ B / φ fy))) /
      (φ fy ^ 5) ^ 2 = (φ (Dt2 f N3) * φ fy - 5 * φ N3 * φ B) / φ fy ^ 7
    field_simp [hfy]
  have hdx : φ (X 0) ^ p - φ (X 0) = φ Dx_p := by simp [Dx_p]
  have hdy : (φ (X 1) ^ p - φ (X 1)) - D (φ (X 1)) * (φ (X 0) ^ p - φ (X 0)) = φ Py / φ fy := by
    rw [hy1, hdx]
    have h1 : φ Py = φ fy * (φ (X 1) ^ p - φ (X 1)) + φ fx * φ Dx_p := by
      dsimp only [Py, Dy_p]; simp only [map_add, map_sub, map_mul, map_pow]
    rw [h1, eq_div_iff hfy]
    have hmul : (-φ fx / φ fy) * φ fy = -φ fx := div_mul_cancel₀ _ hfy
    linear_combination -φ Dx_p * hmul
  rw [det_fwMatrix_conic p D (φ (X 0)) (φ (X 1)) hDx]
  rw [hy4, hy3, hy2, hdy, hdx]
  have hid := congrArg φ (fy_sq_mul_W10 p f)
  change φ (fy ^ 2 * W10 p f) =
    φ (18 * N2 ^ 3 * Py * fy ^ 2 - 9 * N2 ^ 4 * Dx_p ^ 2 - 6 * N2 ^ 2 * N3 * Dx_p * Py +
      (4 * N3 ^ 2 - 3 * N2 * N4) * Py ^ 2) at hid
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat] at hid
  rw [eq_div_iff (pow_ne_zero 10 hfy)]
  apply mul_right_cancel₀ (pow_ne_zero 2 hfy)
  have hdiv : ∀ (a : L) (k : ℕ), (a / φ fy ^ k) * φ fy ^ k = a :=
    fun a k => div_mul_cancel₀ a (pow_ne_zero k hfy)
  have ht1 : (φ N2 / φ fy ^ 3) ^ 3 * (φ Py / φ fy) * φ fy ^ 10 * φ fy ^ 2 =
      φ N2 ^ 3 * φ Py * φ fy ^ 2 := by
    rw [div_pow, ← pow_mul]
    have h1 := hdiv (φ N2 ^ 3) 9
    have h2 : (φ Py / φ fy) * φ fy = φ Py := div_mul_cancel₀ _ hfy
    calc (φ N2 ^ 3 / φ fy ^ (3 * 3)) * (φ Py / φ fy) * φ fy ^ 10 * φ fy ^ 2
        = ((φ N2 ^ 3 / φ fy ^ 9) * φ fy ^ 9) * ((φ Py / φ fy) * φ fy) * φ fy ^ 2 := by ring
      _ = φ N2 ^ 3 * φ Py * φ fy ^ 2 := by rw [h1, h2]
  have ht2 : (φ N2 / φ fy ^ 3) ^ 4 * φ Dx_p ^ 2 * φ fy ^ 10 * φ fy ^ 2 =
      φ N2 ^ 4 * φ Dx_p ^ 2 := by
    rw [div_pow, ← pow_mul]
    have h1 := hdiv (φ N2 ^ 4) 12
    calc (φ N2 ^ 4 / φ fy ^ (3 * 4)) * φ Dx_p ^ 2 * φ fy ^ 10 * φ fy ^ 2
        = ((φ N2 ^ 4 / φ fy ^ 12) * φ fy ^ 12) * φ Dx_p ^ 2 := by ring
      _ = φ N2 ^ 4 * φ Dx_p ^ 2 := by rw [h1]
  have ht3 : (φ N2 / φ fy ^ 3) ^ 2 * (φ N3 / φ fy ^ 5) * φ Dx_p * (φ Py / φ fy) * φ fy ^ 10 * φ fy ^ 2 =
      φ N2 ^ 2 * φ N3 * φ Dx_p * φ Py := by
    rw [div_pow, ← pow_mul]
    have h1 := hdiv (φ N2 ^ 2) 6
    have h2 := hdiv (φ N3) 5
    have h3 : (φ Py / φ fy) * φ fy = φ Py := div_mul_cancel₀ _ hfy
    calc (φ N2 ^ 2 / φ fy ^ (3 * 2)) * (φ N3 / φ fy ^ 5) * φ Dx_p * (φ Py / φ fy) * φ fy ^ 10 * φ fy ^ 2
        = ((φ N2 ^ 2 / φ fy ^ 6) * φ fy ^ 6) * ((φ N3 / φ fy ^ 5) * φ fy ^ 5) * φ Dx_p * ((φ Py / φ fy) * φ fy) := by ring
      _ = φ N2 ^ 2 * φ N3 * φ Dx_p * φ Py := by rw [h1, h2, h3]
  have ht4a : (φ N3 / φ fy ^ 5) ^ 2 * (φ Py / φ fy) ^ 2 * φ fy ^ 10 * φ fy ^ 2 =
      φ N3 ^ 2 * φ Py ^ 2 := by
    rw [div_pow, div_pow, ← pow_mul]
    have h1 := hdiv (φ N3 ^ 2) 10
    have h2 := hdiv (φ Py ^ 2) 2
    calc (φ N3 ^ 2 / φ fy ^ (5 * 2)) * (φ Py ^ 2 / φ fy ^ 2) * φ fy ^ 10 * φ fy ^ 2
        = ((φ N3 ^ 2 / φ fy ^ 10) * φ fy ^ 10) * ((φ Py ^ 2 / φ fy ^ 2) * φ fy ^ 2) := by ring
      _ = φ N3 ^ 2 * φ Py ^ 2 := by rw [h1, h2]
  have ht4b : (φ N2 / φ fy ^ 3) * (φ N4 / φ fy ^ 7) * (φ Py / φ fy) ^ 2 * φ fy ^ 10 * φ fy ^ 2 =
      φ N2 * φ N4 * φ Py ^ 2 := by
    rw [div_pow]
    have h1 := hdiv (φ N2) 3
    have h2 := hdiv (φ N4) 7
    have h3 := hdiv (φ Py ^ 2) 2
    calc (φ N2 / φ fy ^ 3) * (φ N4 / φ fy ^ 7) * (φ Py ^ 2 / φ fy ^ 2) * φ fy ^ 10 * φ fy ^ 2
        = ((φ N2 / φ fy ^ 3) * φ fy ^ 3) * ((φ N4 / φ fy ^ 7) * φ fy ^ 7) * ((φ Py ^ 2 / φ fy ^ 2) * φ fy ^ 2) := by ring
      _ = φ N2 * φ N4 * φ Py ^ 2 := by rw [h1, h2, h3]
  linear_combination 36 * ht1 - 18 * ht2 - 12 * ht3 + 8 * ht4a - 6 * ht4b - 2 * hid

lemma pderiv_rot3_symm {R : Type*} [CommRing R] (i : Fin 3) (P : MvPolynomial (Fin 3) R) :
    MvPolynomial.pderiv i (rot3.symm P) = rot3.symm (MvPolynomial.pderiv (cyc3 i) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : rot3.symm (C a) = C a := MvPolynomial.rename_C cyc3.symm a
    simp [h1]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul_X a j ha =>
    have hX : rot3.symm (X j : MvPolynomial (Fin 3) R) = X (cyc3.symm j) :=
      MvPolynomial.rename_X cyc3.symm j
    have hp : MvPolynomial.pderiv i (X (cyc3.symm j) : MvPolynomial (Fin 3) R) =
        rot3.symm (MvPolynomial.pderiv (cyc3 i) (X j)) := by
      rw [MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
      by_cases h : cyc3 i = j
      · subst h
        have h1 : cyc3.symm (cyc3 i) = i := cyc3.symm_apply_apply i
        rw [h1, Pi.single_eq_same, Pi.single_eq_same, map_one]
      · have h1 : cyc3.symm j ≠ i := fun he => h (by rw [← he, cyc3.apply_symm_apply])
        rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne (Ne.symm h), map_zero]
    rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul,
      ha, hX, hp]

lemma dehomogZ_totalDegree_le {R : Type*} [CommRing R] {d : ℕ}
    {P : MvPolynomial (Fin 3) R} (hP : P.IsHomogeneous d) :
    (dehomogZ P).totalDegree ≤ d := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro m hm
  have hc := MvPolynomial.mem_support_iff.mp hm
  have hsum_le : m 0 + m 1 ≤ d := by
    by_contra hgt
    apply hc
    conv_lhs => rw [P.as_sum]
    rw [map_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro s hs
    have hdeg := isHomogeneous_sum_eq hP hs
    rw [Fin.sum_univ_three] at hdeg
    have hmon : dehomogZ (monomial s (P.coeff s)) =
        monomial (Finsupp.single (0 : Fin 2) (s 0) + Finsupp.single 1 (s 1)) (P.coeff s) := by
      dsimp only [dehomogZ]
      rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
        Fin.prod_univ_three, one_pow, mul_one, MvPolynomial.monomial_eq,
        Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
      simp
    rw [hmon, MvPolynomial.coeff_monomial]
    split_ifs with heq
    · exfalso
      have h0 : s 0 = m 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa using this
      have h1 : s 1 = m 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa using this
      omega
    · rfl
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
  exact hsum_le

lemma W10Z_isHomogeneous {R : Type*} [CommRing R] {p n : ℕ}
    (hn3 : 3 ≤ n) (hp1 : 1 ≤ p) {F : MvPolynomial (Fin 3) R} (hFh : F.IsHomogeneous n) :
    (W10Z p n F).IsHomogeneous (2 * p + 10 * n - 14) :=
  homogZ_isHomogeneous (totalDegree_W10_le (dehomogZ_totalDegree_le hFh) hn3 hp1)

lemma rot3_symm_isHomogeneous {R : Type*} [CommRing R] {d : ℕ}
    {F : MvPolynomial (Fin 3) R} (hF : F.IsHomogeneous d) : (rot3.symm F).IsHomogeneous d := by
  have hfun : (cyc3.symm : Fin 3 → Fin 3) = cyc3 ∘ cyc3 := by
    ext i; fin_cases i <;> rfl
  have heq : rot3.symm F = rot3 (rot3 F) := by
    change MvPolynomial.rename cyc3.symm F = MvPolynomial.rename cyc3 (MvPolynomial.rename cyc3 F)
    rw [MvPolynomial.rename_rename, hfun]
  rw [heq]; exact rot3_isHomogeneous (rot3_isHomogeneous hF)

lemma W10X_isHomogeneous {R : Type*} [CommRing R] {p n : ℕ}
    (hn3 : 3 ≤ n) (hp1 : 1 ≤ p) {F : MvPolynomial (Fin 3) R} (hFh : F.IsHomogeneous n) :
    (W10X p n F).IsHomogeneous (2 * p + 10 * n - 14) :=
  rot3_isHomogeneous (W10Z_isHomogeneous hn3 hp1 (rot3_symm_isHomogeneous hFh))

-- Abstract field-level projective invariance of W10 (avoids unfolding FractionRing!)
lemma W10_ZX_in_field {p n : ℕ} [Fact p.Prime] {L : Type*} [Field L]
    (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p) (h2L : (2 : L) ≠ 0)
    {F : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (π : MvPolynomial (Fin 2) (ZMod p) →+* L)
    (hπ_f : π (dehomogZ F) = 0)
    (Dx : RingDeriv L)
    (hDx_π : ∀ g : MvPolynomial (Fin 2) (ZMod p),
      Dx (π g) = π (Dt2 (dehomogZ F) g) / π (MvPolynomial.pderiv 1 (dehomogZ F)))
    (hX0_ne : π (X 0) ≠ 0)
    (hfy_ne : π (MvPolynomial.pderiv 1 (dehomogZ F)) ≠ 0)
    (hfZ_ne : π (dehomogZ (MvPolynomial.pderiv 2 F)) ≠ 0) :
    π (dehomogZ (W10X p n F)) = π (X 0) ^ 6 * π (W10 p (dehomogZ F)) := by
  let f := dehomogZ F
  let xL : L := π (X 0)
  let yL : L := π (X 1)
  let fxL : L := π (MvPolynomial.pderiv 0 f)
  let fyL : L := π (MvPolynomial.pderiv 1 f)
  let fZL : L := π (dehomogZ (MvPolynomial.pderiv 2 F))
  have hDx_x : Dx xL = 1 := by
    dsimp only [xL]; rw [hDx_π]
    have hDt : Dt2 f (X 0) = MvPolynomial.pderiv 1 f := by unfold Dt2; simp [MvPolynomial.pderiv_X]
    rw [hDt]; exact div_self hfy_ne
  have hDx_y : Dx yL = -fxL / fyL := by
    dsimp only [yL, fxL]; rw [hDx_π]
    have hDt : Dt2 f (X 1) = -MvPolynomial.pderiv 0 f := by unfold Dt2; simp [MvPolynomial.pderiv_X]
    rw [hDt, map_neg, neg_div]
  have heuler_L : xL * fxL + yL * fyL + fZL = 0 := by
    have h1 := congrArg (π.comp dehomogZ) (euler_homog_fin3 hFh)
    simp only [RingHom.comp_apply, map_add, map_mul, map_natCast, dehomogZ_pderiv_0,
      dehomogZ_pderiv_1] at h1
    have hX0 : dehomogZ (X (0 : Fin 3) : MvPolynomial (Fin 3) (ZMod p)) = X 0 := by simp [dehomogZ]
    have hX1 : dehomogZ (X (1 : Fin 3) : MvPolynomial (Fin 3) (ZMod p)) = X 1 := by simp [dehomogZ]
    have hX2 : dehomogZ (X (2 : Fin 3) : MvPolynomial (Fin 3) (ZMod p)) = 1 := by simp [dehomogZ]
    rw [hX0, hX1, hX2, map_one, one_mul] at h1
    change xL * fxL + yL * fyL + fZL = (n : L) * π f at h1
    rw [hπ_f, mul_zero] at h1
    exact h1
  let u : L := yL / xL
  let v : L := 1 / xL
  let g : MvPolynomial (Fin 2) (ZMod p) := dehomogZ (rot3.symm F)
  let ev_uv : MvPolynomial (Fin 2) (ZMod p) →+* L := MvPolynomial.eval₂Hom (π.comp C) ![u, v]
  have hev_uv_X0 : ev_uv (X 0) = u := by simp [ev_uv]
  have hev_uv_X1 : ev_uv (X 1) = v := by simp [ev_uv]
  have hev_uv_homog : ∀ {d : ℕ} {P : MvPolynomial (Fin 3) (ZMod p)}, P.IsHomogeneous d →
      ev_uv (dehomogZ (rot3.symm P)) = xL⁻¹ ^ d * π (dehomogZ P) := by
    intro d P hPh
    rw [P.as_sum, map_sum, map_sum, map_sum, map_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hdeg := isHomogeneous_sum_eq hPh hs
    rw [Fin.sum_univ_three] at hdeg
    have hrot : rot3.symm (monomial s (P.coeff s)) =
        C (P.coeff s) * (X 2 ^ s 0 * X 0 ^ s 1 * X 1 ^ s 2) := by
      have hsym : ∀ k : Fin 3, rot3.symm (X k : MvPolynomial (Fin 3) (ZMod p)) = X (cyc3.symm k) :=
        fun k => MvPolynomial.rename_X cyc3.symm k
      have hC : rot3.symm (C (P.coeff s)) = C (P.coeff s) := MvPolynomial.rename_C cyc3.symm (P.coeff s)
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
      rw [map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hC, hsym 0, hsym 1, hsym 2]
      rfl
    rw [hrot]
    have hde1 : dehomogZ (C (P.coeff s) * (X 2 ^ s 0 * X 0 ^ s 1 * X 1 ^ s 2)) =
        C (P.coeff s) * (X 0 ^ s 1 * X 1 ^ s 2) := by simp [dehomogZ]
    have hde2 : dehomogZ (monomial s (P.coeff s)) =
        C (P.coeff s) * (X 0 ^ s 0 * X 1 ^ s 1) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
      simp [dehomogZ]
    rw [hde1, hde2]
    have hevC : ev_uv (C (P.coeff s)) = π (C (P.coeff s)) := MvPolynomial.eval₂Hom_C _ _ _
    rw [map_mul, map_mul, map_pow, map_pow, hevC, hev_uv_X0, hev_uv_X1,
      map_mul, map_mul, map_pow, map_pow]
    change π (C (P.coeff s)) * (u ^ s 1 * v ^ s 2) =
      xL⁻¹ ^ d * (π (C (P.coeff s)) * (xL ^ s 0 * yL ^ s 1))
    have h0 : (xL ^ s 0)⁻¹ * xL ^ s 0 = 1 := inv_mul_cancel₀ (pow_ne_zero _ hX0_ne)
    calc π (C (P.coeff s)) * (u ^ s 1 * v ^ s 2)
        = π (C (P.coeff s)) * ((yL ^ s 1 * (xL ^ s 1)⁻¹) * (xL ^ s 2)⁻¹) := by
            dsimp only [u, v]; rw [div_pow, div_pow, one_pow, div_eq_mul_inv, one_div]
      _ = ((xL ^ s 0)⁻¹ * xL ^ s 0) * (π (C (P.coeff s)) * ((yL ^ s 1 * (xL ^ s 1)⁻¹) * (xL ^ s 2)⁻¹)) := by
            rw [h0, one_mul]
      _ = ((xL ^ s 0)⁻¹ * (xL ^ s 1)⁻¹ * (xL ^ s 2)⁻¹) * (π (C (P.coeff s)) * (xL ^ s 0 * yL ^ s 1)) := by
            ac_rfl
      _ = xL⁻¹ ^ d * (π (C (P.coeff s)) * (xL ^ s 0 * yL ^ s 1)) := by
            rw [← hdeg, pow_add, pow_add, inv_pow, inv_pow, inv_pow]
  have hgu : ev_uv (MvPolynomial.pderiv 0 g) = xL⁻¹ ^ (n - 1) * fyL := by
    dsimp only [g]
    rw [← dehomogZ_pderiv_0, pderiv_rot3_symm 0 F]
    have hc0 : cyc3 0 = 1 := rfl
    rw [hc0, hev_uv_homog (isHomogeneous_pderiv hFh 1), dehomogZ_pderiv_1]
  have hgv : ev_uv (MvPolynomial.pderiv 1 g) = xL⁻¹ ^ (n - 1) * fZL := by
    dsimp only [g]
    rw [← dehomogZ_pderiv_1, pderiv_rot3_symm 1 F]
    have hc1 : cyc3 1 = 2 := rfl
    rw [hc1, hev_uv_homog (isHomogeneous_pderiv hFh 2)]
  have hgv_ne : ev_uv (MvPolynomial.pderiv 1 g) ≠ 0 := by
    rw [hgv]; exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hX0_ne)) hfZ_ne
  have hDx_u : Dx u = fZL / (xL ^ 2 * fyL) := by
    have h1 : Dx u = ((-fxL / fyL) * xL - yL * 1) / xL ^ 2 := by
      dsimp only [u]; rw [Dx.map_div yL xL hX0_ne, hDx_y, hDx_x]
    rw [h1, div_eq_div_iff (pow_ne_zero 2 hX0_ne) (mul_ne_zero (pow_ne_zero 2 hX0_ne) hfy_ne)]
    have hm : (-fxL / fyL) * fyL = -fxL := div_mul_cancel₀ _ hfy_ne
    linear_combination xL ^ 3 * hm - xL ^ 2 * heuler_L
  have hDx_u_ne : Dx u ≠ 0 := by
    rw [hDx_u]; exact div_ne_zero hfZ_ne (mul_ne_zero (pow_ne_zero 2 hX0_ne) hfy_ne)
  let Du : RingDeriv L := Dx.smul (Dx u)⁻¹
  have hDu_u : Du u = 1 := by dsimp only [Du, RingDeriv.smul]; exact inv_mul_cancel₀ hDx_u_ne
  have hDu_v : Du v = -ev_uv (MvPolynomial.pderiv 0 g) / ev_uv (MvPolynomial.pderiv 1 g) := by
    dsimp only [Du, RingDeriv.smul, v]
    rw [Dx.map_div 1 xL hX0_ne, Dx.map_one, hDx_x, hDx_u, hgu, hgv]
    have hx2 : xL ^ 2 ≠ 0 := pow_ne_zero 2 hX0_ne
    have hxn : xL⁻¹ ^ (n - 1) ≠ 0 := pow_ne_zero _ (inv_ne_zero hX0_ne)
    rw [inv_div, zero_mul, zero_sub, mul_one, div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero hfZ_ne hx2) (mul_ne_zero hxn hfZ_ne)]
    ring
  have hDu_ev : ∀ q : MvPolynomial (Fin 2) (ZMod p),
      Du (ev_uv q) = ev_uv (Dt2 g q) / ev_uv (MvPolynomial.pderiv 1 g) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
      have hC : ev_uv (C a) = π (C a) := by simp [ev_uv]
      have hDtC : Dt2 g (C a) = 0 := by unfold Dt2; simp
      rw [hDtC, map_zero, zero_div, hC]
      dsimp only [Du, RingDeriv.smul]
      rw [hDx_π]
      have hDtC2 : Dt2 f (C a) = 0 := by unfold Dt2; simp
      rw [hDtC2, map_zero, zero_div, mul_zero]
    | add a b ha hb => rw [map_add, Du.map_add', ha, hb, Dt2_add, map_add, add_div]
    | mul_X a i ha =>
      rw [map_mul, Du.map_mul', ha, Dt2_mul, map_add, map_mul, map_mul, add_div, mul_div_right_comm]
      congr 1
      match i with
      | 0 =>
        rw [hev_uv_X0, hDu_u, mul_one]
        have hDt0 : Dt2 g (X 0) = MvPolynomial.pderiv 1 g := by unfold Dt2; simp [MvPolynomial.pderiv_X]
        rw [hDt0, mul_div_cancel_right₀ _ hgv_ne]
      | 1 =>
        rw [hev_uv_X1, hDu_v]
        have hDt1 : Dt2 g (X 1) = -MvPolynomial.pderiv 0 g := by unfold Dt2; simp [MvPolynomial.pderiv_X]
        rw [hDt1, map_neg]; ring
  have hdetZ : (fwMatrix p Dx ![1, xL, yL, xL ^ 2, xL * yL, yL ^ 2]).det =
      2 * π (W10 p f) / fyL ^ 10 :=
    det_fwMatrix_eq_W10_of_deriv p π Dx f hDx_x hDx_π hfy_ne
  have hdetX : (fwMatrix p Du ![1, u, v, u ^ 2, u * v, v ^ 2]).det =
      2 * ev_uv (W10 p g) / ev_uv (MvPolynomial.pderiv 1 g) ^ 10 := by
    have := det_fwMatrix_eq_W10_of_deriv p ev_uv Du g (by rw [hev_uv_X0]; exact hDu_u) hDu_ev hgv_ne
    simpa [hev_uv_X0, hev_uv_X1] using this
  let σ : Equiv.Perm (Fin 6) := {
    toFun := ![3, 4, 1, 5, 2, 0]
    invFun := ![5, 2, 4, 0, 1, 3]
    left_inv := fun i => by fin_cases i <;> rfl
    right_inv := fun i => by fin_cases i <;> rfl
  }
  have hσ_sign : Equiv.Perm.sign σ = 1 := by decide
  let mZ : Fin 6 → L := ![1, xL, yL, xL ^ 2, xL * yL, yL ^ 2]
  let mX : Fin 6 → L := ![1, u, v, u ^ 2, u * v, v ^ 2]
  have hmX_eq : mX = fun j => xL⁻¹ ^ 2 * (mZ ∘ σ) j := by
    ext j
    match j with
    | 0 => dsimp only [mX, mZ, σ, u, v, Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; rw [← mul_pow, inv_mul_cancel₀ hX0_ne, one_pow]
    | 1 => dsimp only [mX, mZ, σ, u, v, Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; rw [sq, div_eq_mul_inv]; have h := inv_mul_cancel₀ hX0_ne; linear_combination -yL * xL⁻¹ * h
    | 2 => dsimp only [mX, mZ, σ, u, v, Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; rw [sq, one_div]; have h := inv_mul_cancel₀ hX0_ne; linear_combination -xL⁻¹ * h
    | 3 => dsimp only [mX, mZ, σ, u, v, Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; rw [div_pow, div_eq_mul_inv, inv_pow]; ring
    | 4 => dsimp only [mX, mZ, σ, u, v, Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; rw [div_eq_mul_inv, one_div, sq]; ring
    | 5 => dsimp only [mX, mZ, σ, u, v, Function.comp_apply, Equiv.coe_fn_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]; rw [one_div, mul_one]
  have hdet_rel : (fwMatrix p Du mX).det =
      (Dx u)⁻¹ ^ 10 * (xL⁻¹ ^ 2) ^ (p + 5) * (fwMatrix p Dx mZ).det := by
    dsimp only [Du]
    rw [det_fwMatrix_smul_deriv, hmX_eq, det_fwMatrix_mul, det_fwMatrix_perm, hσ_sign, one_smul]
    ring
  have hev_W10X : ev_uv (W10 p g) =
      xL⁻¹ ^ (2 * p + 10 * n - 14) * π (dehomogZ (W10X p n F)) := by
    have h1 := hev_uv_homog (W10X_isHomogeneous (p := p) hn3 (by omega) hFh)
    have h3 : dehomogZ (rot3.symm (W10X p n F)) = W10 p g := by
      unfold W10X W10Z
      rw [RingEquiv.symm_apply_apply, dehomogZ_homogZ]
    rwa [h3] at h1
  rw [hdetX, hdetZ, hev_W10X, hgv, hDx_u] at hdet_rel
  have hexp1 : (xL⁻¹ ^ 2) ^ (p + 5) = xL⁻¹ ^ (2 * p + 10) := by
    rw [← pow_mul, mul_add]
  have hexp2 : (xL⁻¹ ^ (n - 1) * fZL) ^ 10 = xL⁻¹ ^ (10 * n - 10) * fZL ^ 10 := by
    rw [mul_pow, ← pow_mul]; congr 2; omega
  have hexp3 : (fZL / (xL ^ 2 * fyL))⁻¹ ^ 10 = xL ^ 20 * fyL ^ 10 / fZL ^ 10 := by
    rw [inv_div, div_pow, mul_pow, ← pow_mul]
  rw [hexp1, hexp2, hexp3] at hdet_rel
  have hpow_xL : xL ^ (2 * p + 10 * n - 14) * xL⁻¹ ^ (2 * p + 10 * n - 14) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hX0_ne, one_pow]
  have hpow_rhs : xL ^ 20 * xL⁻¹ ^ (2 * p + 10) * xL ^ (2 * p + 10 * n - 14) * xL⁻¹ ^ (10 * n - 10) = xL ^ 6 := by
    have ha : xL ^ 20 * xL ^ (2 * p + 10 * n - 14) = xL ^ (2 * p + 10 * n + 6) := by
      rw [← pow_add]; congr 1; omega
    have hb : xL⁻¹ ^ (2 * p + 10) * xL⁻¹ ^ (10 * n - 10) = xL⁻¹ ^ (2 * p + 10 * n) := by
      rw [← pow_add]; congr 1; omega
    have hc : xL ^ (2 * p + 10 * n + 6) = xL ^ 6 * xL ^ (2 * p + 10 * n) := by
      rw [← pow_add]; congr 1; omega
    calc xL ^ 20 * xL⁻¹ ^ (2 * p + 10) * xL ^ (2 * p + 10 * n - 14) * xL⁻¹ ^ (10 * n - 10)
        = (xL ^ 20 * xL ^ (2 * p + 10 * n - 14)) * (xL⁻¹ ^ (2 * p + 10) * xL⁻¹ ^ (10 * n - 10)) := by ring
      _ = xL ^ (2 * p + 10 * n + 6) * xL⁻¹ ^ (2 * p + 10 * n) := by rw [ha, hb]
      _ = xL ^ 6 * (xL ^ (2 * p + 10 * n) * xL⁻¹ ^ (2 * p + 10 * n)) := by rw [hc]; ring
      _ = xL ^ 6 * 1 := by rw [← mul_pow, mul_inv_cancel₀ hX0_ne, one_pow]
      _ = xL ^ 6 := mul_one _
  have h2eq : 2 * π (dehomogZ (W10X p n F)) = 2 * (xL ^ 6 * π (W10 p f)) := by
    have hfz10 : fZL ^ 10 ≠ 0 := pow_ne_zero 10 hfZ_ne
    have hfy10 : fyL ^ 10 ≠ 0 := pow_ne_zero 10 hfy_ne
    have hxl_inv : xL⁻¹ ^ (10 * n - 10) ≠ 0 := pow_ne_zero _ (inv_ne_zero hX0_ne)
    have hdet_clear : 2 * (xL⁻¹ ^ (2 * p + 10 * n - 14) * π (dehomogZ (W10X p n F))) =
        xL ^ 20 * xL⁻¹ ^ (2 * p + 10) * (2 * π (W10 p f)) * xL⁻¹ ^ (10 * n - 10) := by
      have h1 := congrArg (· * (xL⁻¹ ^ (10 * n - 10) * fZL ^ 10)) hdet_rel
      rw [div_mul_cancel₀ _ (mul_ne_zero hxl_inv hfz10)] at h1
      rw [h1]
      have hcancel1 : (xL ^ 20 * fyL ^ 10 / fZL ^ 10) * fZL ^ 10 = xL ^ 20 * fyL ^ 10 :=
        div_mul_cancel₀ _ hfz10
      have hcancel2 : (2 * π (W10 p f) / fyL ^ 10) * fyL ^ 10 = 2 * π (W10 p f) :=
        div_mul_cancel₀ _ hfy10
      linear_combination
        xL⁻¹ ^ (2 * p + 10) * (2 * π (W10 p f) / fyL ^ 10) * xL⁻¹ ^ (10 * n - 10) * hcancel1 +
        xL ^ 20 * xL⁻¹ ^ (2 * p + 10) * xL⁻¹ ^ (10 * n - 10) * hcancel2
    calc 2 * π (dehomogZ (W10X p n F))
        = (2 * (xL⁻¹ ^ (2 * p + 10 * n - 14) * π (dehomogZ (W10X p n F)))) *
            xL ^ (2 * p + 10 * n - 14) := by
              linear_combination -2 * π (dehomogZ (W10X p n F)) * hpow_xL
      _ = (xL ^ 20 * xL⁻¹ ^ (2 * p + 10) * (2 * π (W10 p f)) * xL⁻¹ ^ (10 * n - 10)) *
            xL ^ (2 * p + 10 * n - 14) := by rw [hdet_clear]
      _ = 2 * ((xL ^ 20 * xL⁻¹ ^ (2 * p + 10) * xL ^ (2 * p + 10 * n - 14) * xL⁻¹ ^ (10 * n - 10)) *
            π (W10 p f)) := by ring
      _ = 2 * (xL ^ 6 * π (W10 p f)) := by rw [hpow_rhs]
  exact mul_left_cancel₀ h2L h2eq

-- Key projective congruence: F ∣ X 0 ^ 6 * W10Z - X 2 ^ 6 * W10X
lemma F_dvd_projective_W10_ZX {p n : ℕ} [Fact p.Prime] (_hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n) (hFirr : Irreducible F)
    (he0 : eval ![1, 0, 0] F ≠ 0) (he1 : eval ![0, 1, 0] F ≠ 0) (he2 : eval ![0, 0, 1] F ≠ 0) :
    F ∣ X 0 ^ 6 * W10Z p n F - X 2 ^ 6 * W10X p n F := by
  have hp_gt : n < p := by omega
  have hnp_ne : (n : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ n := (ZMod.natCast_eq_zero_iff n p).mp h0
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  have h2_ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have hle := Nat.le_of_dvd (by omega) hdvd
    have hp_ge := (Fact.out : p.Prime).two_le
    omega
  have hX2_ndvd : ¬ (X (2 : Fin 3) ∣ F) := by
    rintro ⟨Q, hQ⟩
    apply he0
    rw [hQ, map_mul, eval_X]
    simp
  let f : MvPolynomial (Fin 2) (ZMod p) := dehomogZ F
  have hf_irr : Irreducible f := irreducible_dehomogZ hFh hFirr hX2_ndvd
  have hf_prime : Prime f := UniqueFactorizationMonoid.irreducible_iff_prime.mp hf_irr
  let I : Ideal (MvPolynomial (Fin 2) (ZMod p)) := Ideal.span {f}
  have : I.IsPrime := (Ideal.span_singleton_prime hf_irr.ne_zero).mpr hf_prime
  let A := MvPolynomial (Fin 2) (ZMod p) ⧸ I
  let L := FractionRing A
  let π : MvPolynomial (Fin 2) (ZMod p) →+* L :=
    (algebraMap A L).comp (Ideal.Quotient.mk I)
  have hπ_zero_iff : ∀ g : MvPolynomial (Fin 2) (ZMod p), π g = 0 ↔ f ∣ g := by
    intro g
    dsimp only [π]
    rw [RingHom.comp_apply, map_eq_zero_iff (algebraMap A L) (IsFractionRing.injective A L),
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hπ_f : π f = 0 := (hπ_zero_iff f).mpr dvd_rfl
  let Dt_A : RingDeriv A := {
    toFun := Quotient.lift (fun g => Ideal.Quotient.mk I (Dt2 f g)) (by
      intro a b hab
      change Ideal.Quotient.mk I (Dt2 f a) = Ideal.Quotient.mk I (Dt2 f b)
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      have hsub : f ∣ a - b :=
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (Quotient.sound hab))
      rcases hsub with ⟨q, hq⟩
      have hDt_sub : Dt2 f a - Dt2 f b = Dt2 f (a - b) := (Dt2_sub f a b).symm
      rw [hDt_sub, hq, Dt2_mul, Dt2_self, zero_mul, zero_add]
      exact ⟨Dt2 f q, rfl⟩)
    map_add' := fun x y => Quotient.inductionOn₂ x y (fun a b => by
      change Ideal.Quotient.mk I (Dt2 f (a + b)) =
        Ideal.Quotient.mk I (Dt2 f a) + Ideal.Quotient.mk I (Dt2 f b)
      rw [Dt2_add, map_add])
    map_mul' := fun x y => Quotient.inductionOn₂ x y (fun a b => by
      change Ideal.Quotient.mk I (Dt2 f (a * b)) =
        Ideal.Quotient.mk I (Dt2 f a) * Ideal.Quotient.mk I b +
        Ideal.Quotient.mk I a * Ideal.Quotient.mk I (Dt2 f b)
      rw [Dt2_mul, map_add, map_mul, map_mul])
  }
  let Dt_L : RingDeriv L := Dt_A.toFractionRing
  have hDt_L : ∀ g : MvPolynomial (Fin 2) (ZMod p), Dt_L (π g) = π (Dt2 f g) := by
    intro g
    dsimp only [Dt_L, π]
    rw [RingHom.comp_apply, RingDeriv.toFractionRing_algebraMap]
    rfl
  have hX0_ne : π (X 0) ≠ 0 := by
    have hdeX0 : dehomogZ (X (0 : Fin 3) : MvPolynomial (Fin 3) (ZMod p)) = X 0 := by simp [dehomogZ]
    rw [← hdeX0, ne_eq, hπ_zero_iff]
    exact not_dvd_dehomogZ_of_homog_lt hFh hFirr (isHomogeneous_X _ 0) (MvPolynomial.X_ne_zero 0)
      (by omega) (by omega)
  have hFY_ne0 : MvPolynomial.pderiv 1 F ≠ 0 := by
    intro h0
    have heul := congrArg (eval ![0, 1, 0]) (euler_homog_fin3 hFh)
    rw [h0] at heul
    simp only [map_add, map_mul, eval_X, mul_zero, zero_mul, add_zero, map_natCast,
      Matrix.cons_val_zero, Matrix.cons_val] at heul
    exact mul_ne_zero hnp_ne he1 heul.symm
  have hFZ_ne0 : MvPolynomial.pderiv 2 F ≠ 0 := by
    intro h0
    have heul := congrArg (eval ![0, 0, 1]) (euler_homog_fin3 hFh)
    rw [h0] at heul
    simp only [map_add, map_mul, eval_X, mul_zero, zero_mul, add_zero, map_natCast,
      Matrix.cons_val_zero, Matrix.cons_val_one] at heul
    exact mul_ne_zero hnp_ne he2 heul.symm
  have hfy_ne : π (MvPolynomial.pderiv 1 f) ≠ 0 := by
    rw [← dehomogZ_pderiv_1, ne_eq, hπ_zero_iff]
    exact not_dvd_dehomogZ_of_homog_lt hFh hFirr (isHomogeneous_pderiv hFh 1) hFY_ne0
      (by omega) (by omega)
  have hfZ_ne : π (dehomogZ (MvPolynomial.pderiv 2 F)) ≠ 0 := by
    rw [ne_eq, hπ_zero_iff]
    exact not_dvd_dehomogZ_of_homog_lt hFh hFirr (isHomogeneous_pderiv hFh 2) hFZ_ne0
      (by omega) (by omega)
  have h2_L : (2 : L) ≠ 0 := by
    have h2eq : (2 : L) = π (C 2) := by rw [map_ofNat, map_ofNat]
    rw [h2eq, ne_eq, hπ_zero_iff]
    rintro ⟨q, hq⟩
    have hu : IsUnit (C (2 : ZMod p) : MvPolynomial (Fin 2) (ZMod p)) :=
      (isUnit_iff_ne_zero.mpr h2_ne).map C
    exact hf_irr.not_isUnit (isUnit_of_dvd_unit ⟨q, hq⟩ hu)
  let Dx : RingDeriv L := Dt_L.smul (π (MvPolynomial.pderiv 1 f))⁻¹
  have hDx_π : ∀ g : MvPolynomial (Fin 2) (ZMod p), Dx (π g) = π (Dt2 f g) / π (MvPolynomial.pderiv 1 f) := by
    intro g; dsimp only [Dx, RingDeriv.smul]; rw [hDt_L, div_eq_inv_mul]
  have hpi_eq : π (dehomogZ (W10X p n F)) = π (X 0) ^ 6 * π (W10 p f) :=
    W10_ZX_in_field hn3 h2np h2_L hFh π hπ_f Dx hDx_π hX0_ne hfy_ne hfZ_ne
  have hW10Z_hom : (W10Z p n F).IsHomogeneous (2 * p + 10 * n - 14) := W10Z_isHomogeneous hn3 (by omega) hFh
  have hW10X_hom : (W10X p n F).IsHomogeneous (2 * p + 10 * n - 14) := W10X_isHomogeneous hn3 (by omega) hFh
  have hdiff_hom : (X 0 ^ 6 * W10Z p n F - X 2 ^ 6 * W10X p n F).IsHomogeneous (6 + (2 * p + 10 * n - 14)) := by
    have hx0 : (X (0 : Fin 3) ^ 6 : MvPolynomial (Fin 3) (ZMod p)).IsHomogeneous 6 := by
      simpa using (isHomogeneous_X (ZMod p) (0 : Fin 3)).pow 6
    have hx2 : (X (2 : Fin 3) ^ 6 : MvPolynomial (Fin 3) (ZMod p)).IsHomogeneous 6 := by
      simpa using (isHomogeneous_X (ZMod p) (2 : Fin 3)).pow 6
    exact (hx0.mul hW10Z_hom).sub (hx2.mul hW10X_hom)
  have hf_dvd_diff : f ∣ dehomogZ (X 0 ^ 6 * W10Z p n F - X 2 ^ 6 * W10X p n F) := by
    rw [← hπ_zero_iff]
    simp only [map_sub, map_mul, map_pow]
    have hX0 : dehomogZ (X (0 : Fin 3) : MvPolynomial (Fin 3) (ZMod p)) = X 0 := by simp [dehomogZ]
    have hX2 : dehomogZ (X (2 : Fin 3) : MvPolynomial (Fin 3) (ZMod p)) = 1 := by simp [dehomogZ]
    have hWZ : dehomogZ (W10Z p n F) = W10 p f := dehomogZ_homogZ _
    rw [hX0, hX2, hWZ, map_one, one_pow, one_mul, hpi_eq]
    ring
  obtain ⟨k, hk⟩ := dvd_of_dehomogZ_dvd hFh hdiff_hom hf_dvd_diff
  have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
  have hFndvdX2 : ¬ (F ∣ X (2 : Fin 3)) :=
    not_dvd_of_isHomogeneous_lt hFh hFirr.ne_zero (isHomogeneous_X _ 2) (MvPolynomial.X_ne_zero 2) (by omega)
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    rw [pow_succ', mul_assoc] at hk
    rcases hFprime.dvd_or_dvd hk with hX | hrest
    · exact absurd hX hFndvdX2
    · exact ih hrest

-- 6-step extraction lemma: if F ∣ X 0 ^ 6 * W - X 2 ^ k * G and F(0, 1, 0) ≠ 0,
-- then ∃ H homogeneous of deg d - k with F ∣ W - X 2 ^ k * H!
lemma extract_X2_pow_mod_F {K : Type*} [Field K] {n : ℕ} {F : MvPolynomial (Fin 3) K}
    (hFh : F.IsHomogeneous n) (hFirr : Irreducible F) (hn : 2 ≤ n)
    (he1 : eval ![0, 1, 0] F ≠ 0) :
    ∀ (k d : ℕ) (W G : MvPolynomial (Fin 3) K),
      k ≤ d → W.IsHomogeneous d → F ∣ X 0 ^ 6 * W - X 2 ^ k * G →
      ∃ H : MvPolynomial (Fin 3) K, H.IsHomogeneous (d - k) ∧ F ∣ W - X 2 ^ k * H := by
  have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
  have hFndvdX2 : ¬ (F ∣ X (2 : Fin 3)) :=
    not_dvd_of_isHomogeneous_lt hFh hFirr.ne_zero (isHomogeneous_X _ 2) (MvPolynomial.X_ne_zero 2) (by omega)
  let setZ0 : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
    MvPolynomial.eval₂Hom C (fun i => match i with | 0 => X 0 | 1 => X 1 | 2 => 0)
  let lift23 : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 3) K :=
    MvPolynomial.eval₂Hom C (fun i => match i with | 0 => X 0 | 1 => X 1)
  have hsetZ0_lift : ∀ q : MvPolynomial (Fin 2) K, setZ0 (lift23 q) = q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [setZ0, lift23]
    | add a b ha hb => simp [map_add, ha, hb]
    | mul_X a i ha => fin_cases i <;> (rw [map_mul, map_mul, ha]; simp [setZ0, lift23])
  have hker_setZ0 : ∀ P : MvPolynomial (Fin 3) K, setZ0 P = 0 → X (2 : Fin 3) ∣ P := by
    intro P hP0
    have hcoeff0 : ∀ s : Fin 3 →₀ ℕ, s 2 = 0 → P.coeff s = 0 := by
      intro s hs2
      let m : Fin 2 →₀ ℕ := Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1)
      have hc := congrArg (fun q : MvPolynomial (Fin 2) K => q.coeff m) hP0
      rw [MvPolynomial.coeff_zero, P.as_sum, map_sum, MvPolynomial.coeff_sum] at hc
      have hterm : ∀ t : Fin 3 →₀ ℕ,
          (setZ0 (monomial t (P.coeff t))).coeff m =
            if t 2 = 0 ∧ t 0 = s 0 ∧ t 1 = s 1 then P.coeff t else 0 := by
        intro t
        dsimp only [setZ0]
        rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
          Fin.prod_univ_three]
        by_cases ht2 : t 2 = 0
        · rw [ht2, pow_zero, mul_one]
          have hmon : C (P.coeff t) * (X (0 : Fin 2) ^ t 0 * X 1 ^ t 1) =
              monomial (Finsupp.single 0 (t 0) + Finsupp.single 1 (t 1)) (P.coeff t) := by
            rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
            simp
          rw [hmon, MvPolynomial.coeff_monomial]
          by_cases heq : Finsupp.single (0 : Fin 2) (t 0) + Finsupp.single 1 (t 1) = m
          · have h0 : t 0 = s 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa [m] using this
            have h1 : t 1 = s 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa [m] using this
            simp only [heq, ↓reduceIte]
            simp only [h0, h1, and_self, ↓reduceIte]
          · have hnc : ¬ (t 2 = 0 ∧ t 0 = s 0 ∧ t 1 = s 1) := by
              rintro ⟨_, h0, h1⟩; apply heq; ext i; fin_cases i <;> simp [m, h0, h1]
            simp only [heq, ↓reduceIte]
            split_ifs with hcond
            · exfalso; exact hnc ⟨ht2, hcond.2⟩
            · rfl
        · have hnt : ¬ (t 2 = 0 ∧ t 0 = s 0 ∧ t 1 = s 1) := by tauto
          rw [zero_pow ht2, mul_zero, mul_zero]; simp only [hnt, ↓reduceIte]; rfl
      simp_rw [hterm] at hc
      by_cases hs : s ∈ P.support
      · rw [Finset.sum_eq_single s] at hc
        · simp only [hs2, and_self, ↓reduceIte] at hc; exact hc
        · intro t _ hne
          split_ifs with hcond
          · exfalso; rcases hcond with ⟨ht2, ht0, ht1⟩
            apply hne; ext i; fin_cases i
            · exact ht0
            · exact ht1
            · exact ht2.trans hs2.symm
          · rfl
        · intro h; exact absurd hs h
      · exact MvPolynomial.notMem_support_iff.mp hs
    refine ⟨∑ s ∈ P.support, monomial (s - Finsupp.single 2 1) (P.coeff s), ?_⟩
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hs2_ne : s 2 ≠ 0 := fun h0 => MvPolynomial.mem_support_iff.mp hs (hcoeff0 s h0)
    rw [show (X (2 : Fin 3) : MvPolynomial (Fin 3) K) = monomial (Finsupp.single 2 1) 1 from rfl,
      MvPolynomial.monomial_mul, one_mul]
    refine congrArg (fun d => monomial d (P.coeff s)) ?_
    ext i
    by_cases hi : i = 2
    · subst hi; simp; omega
    · simp [Finsupp.single_eq_of_ne hi]
  have hX0_prime : Prime (X (0 : Fin 2) : MvPolynomial (Fin 2) K) := prime_X_mv 0
  have hX0_ndvd_F0 : ¬ (X (0 : Fin 2) ∣ setZ0 F) := by
    rintro ⟨q, hq⟩
    apply he1
    have hev : ∀ P : MvPolynomial (Fin 3) K, eval ![0, 1] (setZ0 P) = eval ![0, 1, 0] P := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C a => simp [setZ0]
      | add a b ha hb => simp [map_add, ha, hb]
      | mul_X a i ha => fin_cases i <;> (rw [map_mul, map_mul, map_mul, ha]; simp [setZ0])
    rw [← hev F, hq, map_mul, eval_X]; simp
  have hlift_hom : ∀ {m : ℕ} {q : MvPolynomial (Fin 2) K}, q.IsHomogeneous m →
      (lift23 q).IsHomogeneous m := by
    intro m q hqh
    rw [q.as_sum, map_sum]
    apply IsHomogeneous.sum
    intro s hs
    dsimp only [lift23]
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
    have hdeg := isHomogeneous_sum_eq hqh hs
    rw [Fin.sum_univ_two] at hdeg
    have hx0 : (X (0 : Fin 3) ^ s 0 : MvPolynomial (Fin 3) K).IsHomogeneous (s 0) := by
      simpa using (isHomogeneous_X K (0 : Fin 3)).pow (s 0)
    have hx1 : (X (1 : Fin 3) ^ s 1 : MvPolynomial (Fin 3) K).IsHomogeneous (s 1) := by
      simpa using (isHomogeneous_X K (1 : Fin 3)).pow (s 1)
    have h1 := hx0.mul hx1
    rw [hdeg] at h1
    exact h1.C_mul _
  have hsetZ0_hom : ∀ {m : ℕ} {P : MvPolynomial (Fin 3) K}, P.IsHomogeneous m →
      (setZ0 P).IsHomogeneous m := by
    intro m P hPh
    rw [P.as_sum, map_sum]
    apply IsHomogeneous.sum
    intro s hs
    dsimp only [setZ0]
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
    by_cases hs2 : s 2 = 0
    · rw [hs2, pow_zero, mul_one]
      have hdeg := isHomogeneous_sum_eq hPh hs
      rw [Fin.sum_univ_three, hs2, add_zero] at hdeg
      have hx0 : (X (0 : Fin 2) ^ s 0 : MvPolynomial (Fin 2) K).IsHomogeneous (s 0) := by
        simpa using (isHomogeneous_X K (0 : Fin 2)).pow (s 0)
      have hx1 : (X (1 : Fin 2) ^ s 1 : MvPolynomial (Fin 2) K).IsHomogeneous (s 1) := by
        simpa using (isHomogeneous_X K (1 : Fin 2)).pow (s 1)
      have h1 := hx0.mul hx1
      rw [hdeg] at h1
      exact h1.C_mul _
    · rw [zero_pow hs2, mul_zero, mul_zero]; exact isHomogeneous_zero _ _ _
  intro k
  induction k with
  | zero =>
    intro d W _ _ hWh _
    exact ⟨W, by simpa using hWh, by simp⟩
  | succ k ih =>
    intro d W G hkd hWh hdvd
    -- Step 1: apply setZ0 to F ∣ X 0 ^ 6 * W - X 2 ^ (k+1) * G
    have hF0_dvd_mul : setZ0 F ∣ X (0 : Fin 2) ^ 6 * setZ0 W := by
      rcases hdvd with ⟨Q, hQ⟩
      have h1 := congrArg setZ0 hQ
      simp only [map_sub, map_mul, map_pow] at h1
      have hZ0 : setZ0 (X (2 : Fin 3) : MvPolynomial (Fin 3) K) = 0 := by simp [setZ0]
      have hX0 : setZ0 (X (0 : Fin 3) : MvPolynomial (Fin 3) K) = X 0 := by simp [setZ0]
      rw [hZ0, hX0, zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero] at h1
      exact ⟨setZ0 Q, h1⟩
    -- Cancel X 0 ^ 6 since X 0 is prime and X 0 ∤ setZ0 F!
    have hF0_dvd_W0 : setZ0 F ∣ setZ0 W := by
      have hcop : ∀ j : ℕ, setZ0 F ∣ X (0 : Fin 2) ^ j * setZ0 W → setZ0 F ∣ setZ0 W := by
        intro j
        induction j with
        | zero => intro h; simpa using h
        | succ j ihj =>
          intro hj
          rw [pow_succ', mul_assoc] at hj
          rcases hj with ⟨q, hq⟩
          have hX0_dvd : X (0 : Fin 2) ∣ setZ0 F * q := ⟨X 0 ^ j * setZ0 W, hq.symm⟩
          rcases hX0_prime.dvd_or_dvd hX0_dvd with hF0 | hq0
          · exact absurd hF0 hX0_ndvd_F0
          · rcases hq0 with ⟨q', hq'⟩
            apply ihj
            refine ⟨q', ?_⟩
            apply mul_left_cancel₀ (MvPolynomial.X_ne_zero (0 : Fin 2))
            calc X 0 * (X 0 ^ j * setZ0 W) = setZ0 F * (X 0 * q') := by rw [← hq', hq]
              _ = X 0 * (setZ0 F * q') := by ring
      exact hcop 6 hF0_dvd_mul
    rcases hF0_dvd_W0 with ⟨q₀, hq₀⟩
    have hex_Q : ∃ Q : MvPolynomial (Fin 3) K, (W - Q * F).IsHomogeneous d ∧ setZ0 (W - Q * F) = 0 := by
      by_cases hW0 : setZ0 W = 0
      · exact ⟨0, by simpa using hWh, by simpa using hW0⟩
      · have hF0_ne : setZ0 F ≠ 0 := fun h => hX0_ndvd_F0 (by rw [h]; exact dvd_zero _)
        obtain ⟨_, hq₀_h, hdeg_sum⟩ := isHomogeneous_of_dvd_homog (hsetZ0_hom hWh) hW0 hq₀.symm
        have hF0_td : (setZ0 F).totalDegree = n := (hsetZ0_hom hFh).totalDegree hF0_ne
        have hq₀_deg : q₀.IsHomogeneous (d - n) := by
          have : q₀.totalDegree = d - n := by omega
          rwa [this] at hq₀_h
        refine ⟨lift23 q₀, ?_, ?_⟩
        · have hQF : (lift23 q₀ * F).IsHomogeneous d := by
            have h1 := (hlift_hom hq₀_deg).mul hFh
            have hdn : d - n + n = d := by omega
            rwa [hdn] at h1
          exact hWh.sub hQF
        · rw [map_sub, map_mul, hsetZ0_lift, mul_comm, ← hq₀, sub_self]
    obtain ⟨Q, hWQ_h, hWQ_Z0⟩ := hex_Q
    obtain ⟨W₁, hW₁⟩ := hker_setZ0 (W - Q * F) hWQ_Z0
    have hW₁_hom : W₁.IsHomogeneous (d - 1) := by
      by_cases h0 : W - Q * F = 0
      · rw [h0] at hW₁
        have : W₁ = 0 := (mul_eq_zero.mp hW₁.symm).resolve_left (MvPolynomial.X_ne_zero 2)
        rw [this]; exact isHomogeneous_zero _ _ _
      · obtain ⟨_, hW₁h, hsum⟩ := isHomogeneous_of_dvd_homog hWQ_h h0 hW₁.symm
        have hX2_td : (X (2 : Fin 3) : MvPolynomial (Fin 3) K).totalDegree = 1 :=
          MvPolynomial.totalDegree_X 2
        have : W₁.totalDegree = d - 1 := by omega
        rwa [this] at hW₁h
    -- Now X 0 ^ 6 * (X 2 * W₁) - X 2 ^ (k+1) * G ≡ 0 (mod F), cancel X 2!
    have hF_dvd_W1 : F ∣ X 0 ^ 6 * W₁ - X 2 ^ k * G := by
      have hmul : F ∣ X (2 : Fin 3) * (X 0 ^ 6 * W₁ - X 2 ^ k * G) := by
        have hid : X (2 : Fin 3) * (X 0 ^ 6 * W₁ - X 2 ^ k * G) =
            (X 0 ^ 6 * W - X 2 ^ (k + 1) * G) - X 0 ^ 6 * Q * F := by
          have : X 2 * W₁ = W - Q * F := hW₁.symm
          calc X 2 * (X 0 ^ 6 * W₁ - X 2 ^ k * G)
              = X 0 ^ 6 * (X 2 * W₁) - X 2 ^ (k + 1) * G := by rw [pow_succ']; ring
            _ = X 0 ^ 6 * (W - Q * F) - X 2 ^ (k + 1) * G := by rw [this]
            _ = (X 0 ^ 6 * W - X 2 ^ (k + 1) * G) - X 0 ^ 6 * Q * F := by ring
        rw [hid]
        exact dvd_sub hdvd ⟨X 0 ^ 6 * Q, by ring⟩
      rcases hFprime.dvd_or_dvd hmul with hX | hrest
      · exact absurd hX hFndvdX2
      · exact hrest
    obtain ⟨H, hHh, hH_dvd⟩ := ih (d - 1) W₁ G (by omega) hW₁_hom hF_dvd_W1
    refine ⟨H, ?_, ?_⟩
    · have : d - 1 - k = d - (k + 1) := by omega
      rwa [this] at hHh
    · have hid : W - X 2 ^ (k + 1) * H = X 2 * (W₁ - X 2 ^ k * H) + Q * F := by
        have : X 2 * W₁ = W - Q * F := hW₁.symm
        calc W - X 2 ^ (k + 1) * H
            = (W - Q * F) - X 2 * (X 2 ^ k * H) + Q * F := by rw [pow_succ']; ring
          _ = X 2 * W₁ - X 2 * (X 2 ^ k * H) + Q * F := by rw [← this]
          _ = X 2 * (W₁ - X 2 ^ k * H) + Q * F := by ring
      rw [hid]
      exact dvd_add (dvd_mul_of_dvd_right hH_dvd _) ⟨Q, by ring⟩

-- Master Theorem of Section 4: Existence of the projective Frobenius-Wronskian H of degree 2p + 10n - 20
-- satisfying W10Z ≡ Z^6 H, W10X ≡ X^6 H, W10Y ≡ Y^6 H (mod F)!
theorem exists_projective_H {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n) (hFirr : Irreducible F)
    (he0 : eval ![1, 0, 0] F ≠ 0) (he1 : eval ![0, 1, 0] F ≠ 0) (he2 : eval ![0, 0, 1] F ≠ 0) :
    ∃ H : MvPolynomial (Fin 3) (ZMod p),
      H.IsHomogeneous (2 * p + 10 * n - 20) ∧
      (F ∣ W10Z p n F - X 2 ^ 6 * H) ∧
      (F ∣ W10X p n F - X 0 ^ 6 * H) ∧
      (F ∣ W10Y p n F - X 1 ^ 6 * H) := by
  have hFprime : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.mp hFirr
  have hFndvdX : ∀ i : Fin 3, ¬ (F ∣ X i) := fun i =>
    not_dvd_of_isHomogeneous_lt hFh hFirr.ne_zero (isHomogeneous_X _ i) (MvPolynomial.X_ne_zero i) (by omega)
  have hF_cancel_X6 : ∀ (i : Fin 3) (P : MvPolynomial (Fin 3) (ZMod p)), F ∣ X i ^ 6 * P → F ∣ P := by
    intro i P h
    have haux : ∀ k : ℕ, F ∣ X i ^ k * P → F ∣ P := by
      intro k; induction k with
      | zero => intro h0; simpa using h0
      | succ k ih =>
        intro hk; rw [pow_succ', mul_assoc] at hk
        rcases hFprime.dvd_or_dvd hk with hX | hrest
        · exact absurd hX (hFndvdX i)
        · exact ih hrest
    exact haux 6 h
  have hZX : F ∣ X 0 ^ 6 * W10Z p n F - X 2 ^ 6 * W10X p n F :=
    F_dvd_projective_W10_ZX hp2 hn3 h2np hFh hFirr he0 he1 he2
  -- Apply F_dvd_projective_W10_ZX to rot3 F to get Y^6 * W10Z ≡ Z^6 * W10Y (mod F)!
  -- Check: rot3 sends X 0 ↦ X 1, X 1 ↦ X 2, X 2 ↦ X 0.
  -- So F_dvd_projective_W10_ZX on (rot3.symm F):
  --   rot3.symm F ∣ X 0 ^ 6 * W10Z (rot3.symm F) - X 2 ^ 6 * W10X (rot3.symm F)
  -- Apply rot3 to both sides!
  --   rot3 (rot3.symm F) = F
  --   rot3 (X 0 ^ 6) = X 1 ^ 6
  --   rot3 (W10Z (rot3.symm F)) = W10X F
  --   rot3 (X 2 ^ 6) = X 0 ^ 6
  --   rot3 (W10X (rot3.symm F)) = rot3 (rot3 (W10Z (rot3.symm (rot3.symm F)))) = rot3.symm (W10Z (rot3 F)) = W10Y F!
  have hrot3_cubed : ∀ P : MvPolynomial (Fin 3) (ZMod p), rot3 (rot3 (rot3 P)) = P := by
    intro P
    change MvPolynomial.rename cyc3 (MvPolynomial.rename cyc3 (MvPolynomial.rename cyc3 P)) = P
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_rename]
    have hid : ((cyc3 : Fin 3 → Fin 3) ∘ cyc3) ∘ cyc3 = id := by ext i; fin_cases i <;> rfl
    rw [hid]; simp [MvPolynomial.rename_id]
  have hrot3_symm_eq : ∀ P : MvPolynomial (Fin 3) (ZMod p), rot3.symm P = rot3 (rot3 P) := by
    intro P; apply rot3.injective; rw [RingEquiv.apply_symm_apply, hrot3_cubed]
  have hF_rot_irr : Irreducible (rot3.symm F) := by
    have hnotu : ¬ IsUnit (rot3.symm F) := fun hu =>
      hFirr.not_isUnit (by have := hu.map rot3.toRingHom; simpa using this)
    refine ⟨hnotu, ?_⟩
    intro a b hab
    have hback : F = rot3 a * rot3 b := by
      have := congrArg rot3 hab; simpa [map_mul] using this
    rcases hFirr.isUnit_or_isUnit hback with ha | hb
    · left; have := ha.map rot3.symm.toRingHom; simpa using this
    · right; have := hb.map rot3.symm.toRingHom; simpa using this
  have hF_rot_h : (rot3.symm F).IsHomogeneous n := by
    rw [hrot3_symm_eq]; exact rot3_isHomogeneous (rot3_isHomogeneous hFh)
  have hev_rot : ∀ v : Fin 3 → ZMod p, eval v (rot3.symm F) = eval (v ∘ cyc3.symm) F :=
    fun v => MvPolynomial.eval_rename cyc3.symm v F
  have hXY_rot := F_dvd_projective_W10_ZX hp2 hn3 h2np hF_rot_h hF_rot_irr
    (by rw [hev_rot, show (![1, 0, 0] ∘ cyc3.symm : Fin 3 → ZMod p) = ![0, 1, 0] by ext i; fin_cases i <;> rfl]; exact he1)
    (by rw [hev_rot, show (![0, 1, 0] ∘ cyc3.symm : Fin 3 → ZMod p) = ![0, 0, 1] by ext i; fin_cases i <;> rfl]; exact he2)
    (by rw [hev_rot, show (![0, 0, 1] ∘ cyc3.symm : Fin 3 → ZMod p) = ![1, 0, 0] by ext i; fin_cases i <;> rfl]; exact he0)
  have hXY : F ∣ X 1 ^ 6 * W10X p n F - X 0 ^ 6 * W10Y p n F := by
    rcases hXY_rot with ⟨Q, hQ⟩
    refine ⟨rot3 Q, ?_⟩
    have h1 := congrArg rot3 hQ
    simp only [map_sub, map_mul, map_pow, RingEquiv.apply_symm_apply, rot3_X] at h1
    have hc0 : cyc3 0 = 1 := rfl
    have hc2 : cyc3 2 = 0 := rfl
    rw [hc0, hc2] at h1
    have hW1 : rot3 (W10Z p n (rot3.symm F)) = W10X p n F := rfl
    have hW2 : rot3 (W10X p n (rot3.symm F)) = W10Y p n F := by
      have hss : rot3.symm (rot3.symm F) = rot3 F := by
        rw [hrot3_symm_eq, hrot3_symm_eq, hrot3_cubed]
      change rot3 (rot3 (W10Z p n (rot3.symm (rot3.symm F)))) = rot3.symm (W10Z p n (rot3 F))
      rw [hss, ← hrot3_symm_eq]
    rw [hW1, hW2] at h1
    exact h1
  -- Extract H from hZX using extract_X2_pow_mod_F!
  have hW10Z_hom : (W10Z p n F).IsHomogeneous (2 * p + 10 * n - 14) := by
    unfold W10Z
    apply homogZ_isHomogeneous
    apply totalDegree_W10_le _ hn3 (by omega)
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    have hsum_le : m 0 + m 1 ≤ n := by
      by_contra hgt
      apply hc
      conv_lhs => rw [F.as_sum]
      rw [map_sum, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro s hs
      have hdeg := isHomogeneous_sum_eq hFh hs
      rw [Fin.sum_univ_three] at hdeg
      have hmon : dehomogZ (monomial s (F.coeff s)) =
          monomial (Finsupp.single (0 : Fin 2) (s 0) + Finsupp.single 1 (s 1)) (F.coeff s) := by
        dsimp only [dehomogZ]
        rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
          Fin.prod_univ_three, one_pow, mul_one, MvPolynomial.monomial_eq,
          Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        simp
      rw [hmon, MvPolynomial.coeff_monomial]
      split_ifs with heq
      · exfalso
        have h0 : s 0 = m 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa using this
        have h1 : s 1 = m 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa using this
        omega
      · rfl
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two]
    exact hsum_le
  obtain ⟨H, hHh, hHZ⟩ :=
    extract_X2_pow_mod_F hFh hFirr (by omega) he1 6 (2 * p + 10 * n - 14)
      (W10Z p n F) (W10X p n F) (by omega) hW10Z_hom hZX
  have hdeg_eq : 2 * p + 10 * n - 14 - 6 = 2 * p + 10 * n - 20 := by omega
  rw [hdeg_eq] at hHh
  have hHX : F ∣ W10X p n F - X 0 ^ 6 * H := by
    apply hF_cancel_X6 2
    have hid : X 2 ^ 6 * (W10X p n F - X 0 ^ 6 * H) =
        X 0 ^ 6 * (W10Z p n F - X 2 ^ 6 * H) - (X 0 ^ 6 * W10Z p n F - X 2 ^ 6 * W10X p n F) := by ring
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hHZ _) hZX
  have hHY : F ∣ W10Y p n F - X 1 ^ 6 * H := by
    apply hF_cancel_X6 0
    have hid : X 0 ^ 6 * (W10Y p n F - X 1 ^ 6 * H) =
        X 1 ^ 6 * (W10X p n F - X 0 ^ 6 * H) - (X 1 ^ 6 * W10X p n F - X 0 ^ 6 * W10Y p n F) := by ring
    rw [hid]
    exact dvd_sub (dvd_mul_of_dvd_right hHX _) hXY
  exact ⟨H, hHh, hHZ, hHX, hHY⟩

end ProjectiveH

-- ============================================================================
-- Section 5: Hensel Power Series & Non-Divisibility ¬ (F.map ι ∣ H.map ι)
-- ============================================================================

section NonDivisibility

-- Convert MvPolynomial (Fin 2) R ↔ Polynomial (Polynomial R) (variable Y = X 1 over R[X 0])
noncomputable def mv2ToPolyY (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) ![Polynomial.C Polynomial.X, Polynomial.X]

noncomputable def polyYToMv2 (R : Type*) [CommRing R] :
    Polynomial (Polynomial R) →+* MvPolynomial (Fin 2) R :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom C (X 0)) (X 1)

lemma polyYToMv2_mv2ToPolyY {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) :
    polyYToMv2 R (mv2ToPolyY R f) = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mv2ToPolyY, polyYToMv2]
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | mul_X a i ha =>
    rw [map_mul, map_mul, ha]
    match i with
    | 0 => simp [mv2ToPolyY, polyYToMv2]
    | 1 => simp [mv2ToPolyY, polyYToMv2]

lemma mv2ToPolyY_polyYToMv2 {R : Type*} [CommRing R] (g : Polynomial (Polynomial R)) :
    mv2ToPolyY R (polyYToMv2 R g) = g := by
  have heq : (mv2ToPolyY R).comp (polyYToMv2 R) = RingHom.id (Polynomial (Polynomial R)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext r; simp [mv2ToPolyY, polyYToMv2]
      · simp [mv2ToPolyY, polyYToMv2]
    · simp [mv2ToPolyY, polyYToMv2]
  exact RingHom.congr_fun heq g

noncomputable def mv2EquivPolyY (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R ≃+* Polynomial (Polynomial R) where
  toFun := mv2ToPolyY R
  invFun := polyYToMv2 R
  left_inv := polyYToMv2_mv2ToPolyY
  right_inv := mv2ToPolyY_polyYToMv2
  map_mul' := map_mul (mv2ToPolyY R)
  map_add' := map_add (mv2ToPolyY R)

lemma mv2ToPolyY_monomial {R : Type*} [CommRing R] (s : Fin 2 →₀ ℕ) (a : R) :
    mv2ToPolyY R (monomial s a) =
      Polynomial.monomial (s 1) (Polynomial.C a * Polynomial.X ^ s 0) := by
  dsimp only [mv2ToPolyY]
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
    Fin.prod_univ_two]
  simp only [RingHom.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← map_pow, ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]

lemma coeff_mv2ToPolyY_coeff {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) (j i : ℕ) :
    ((mv2ToPolyY R f).coeff j).coeff i = f.coeff (Finsupp.single 0 i + Finsupp.single 1 j) := by
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j
  have hm₀0 : m₀ 0 = i := by simp [m₀]
  have hm₀1 : m₀ 1 = j := by simp [m₀]
  have hterm : ∀ s : Fin 2 →₀ ℕ,
      ((mv2ToPolyY R (monomial s (f.coeff s))).coeff j).coeff i =
        if s = m₀ then f.coeff s else 0 := by
    intro s
    rw [mv2ToPolyY_monomial, Polynomial.coeff_monomial]
    by_cases h1 : s 1 = j
    · simp only [h1, ↓reduceIte, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h0 : i = s 0
      · have hs : s = m₀ := by
          ext k; match k with
          | 0 => exact h0.symm.trans hm₀0.symm
          | 1 => exact h1.trans hm₀1.symm
        simp [h0, hs]
      · have hs : s ≠ m₀ := fun h => h0 (by rw [h, hm₀0])
        simp [h0, hs]
    · simp only [h1, ↓reduceIte, Polynomial.coeff_zero]
      have hs : s ≠ m₀ := fun h => h1 (by rw [h, hm₀1])
      simp [hs]
  simp_rw [hterm]
  by_cases hm : m₀ ∈ f.support
  · rw [Finset.sum_eq_single m₀]
    · simp [m₀]
    · intro s _ hne; simp [hne]
    · intro h; exact absurd hm h
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    apply Finset.sum_eq_zero
    intro s hs
    have hne : s ≠ m₀ := fun h => hm (h ▸ hs)
    simp [hne]

lemma mv2ToPolyY_pderiv_1 {R : Type*} [CommRing R] (f : MvPolynomial (Fin 2) R) :
    mv2ToPolyY R (MvPolynomial.pderiv 1 f) = Polynomial.derivative (mv2ToPolyY R f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : mv2ToPolyY R (C a : MvPolynomial (Fin 2) R) = Polynomial.C (Polynomial.C a) := by
      simp [mv2ToPolyY]
    rw [MvPolynomial.pderiv_C, map_zero, h1, Polynomial.derivative_C]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | mul_X a i ha =>
    rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, ha, map_mul, Polynomial.derivative_mul]
    match i with
    | 0 =>
      have hX0 : mv2ToPolyY R (X 0 : MvPolynomial (Fin 2) R) = Polynomial.C Polynomial.X := by
        simp [mv2ToPolyY]
      have hp0 : MvPolynomial.pderiv (1 : Fin 2) (X 0 : MvPolynomial (Fin 2) R) = 0 := by
        simp [MvPolynomial.pderiv_X]
      rw [hp0, map_zero, mul_zero, add_zero, hX0, Polynomial.derivative_C, mul_zero, add_zero]
    | 1 =>
      have hX1 : mv2ToPolyY R (X 1 : MvPolynomial (Fin 2) R) = Polynomial.X := by
        simp [mv2ToPolyY]
      have hp1 : MvPolynomial.pderiv (1 : Fin 2) (X 1 : MvPolynomial (Fin 2) R) = 1 := by
        simp [MvPolynomial.pderiv_X]
      rw [hp1, map_one, mul_one, hX1, Polynomial.derivative_X, mul_one, add_comm]

lemma eval_map_mv2ToPolyY {R S : Type*} [CommRing R] [CommRing S]
    (ψ : Polynomial R →+* S) (y : S) (f : MvPolynomial (Fin 2) R) :
    Polynomial.eval y ((mv2ToPolyY R f).map ψ) =
      MvPolynomial.eval₂Hom (ψ.comp Polynomial.C) ![ψ Polynomial.X, y] f := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h1 : mv2ToPolyY R (C a : MvPolynomial (Fin 2) R) = Polynomial.C (Polynomial.C a) := by
      simp [mv2ToPolyY]
    rw [h1, Polynomial.map_C, Polynomial.eval_C, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  | add a b ha hb => rw [map_add, Polynomial.map_add, Polynomial.eval_add, map_add, ha, hb]
  | mul_X a i ha =>
    rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, map_mul, ha]
    match i with
    | 0 =>
      have hX0 : mv2ToPolyY R (X 0 : MvPolynomial (Fin 2) R) = Polynomial.C Polynomial.X := by
        simp [mv2ToPolyY]
      rw [hX0, Polynomial.map_C, Polynomial.eval_C, MvPolynomial.eval₂Hom_X']
      rfl
    | 1 =>
      have hX1 : mv2ToPolyY R (X 1 : MvPolynomial (Fin 2) R) = Polynomial.X := by
        simp [mv2ToPolyY]
      rw [hX1, Polynomial.map_X, Polynomial.eval_X, MvPolynomial.eval₂Hom_X']
      rfl

lemma mv2ToPolyY_degree_bounds {R : Type*} [CommRing R] {f : MvPolynomial (Fin 2) R} {d : ℕ}
    (hf : f.totalDegree ≤ d) :
    (mv2ToPolyY R f).natDegree ≤ d ∧ ∀ k ≤ d, ((mv2ToPolyY R f).coeff k).natDegree ≤ d - k := by
  have hzero : ∀ j i : ℕ, d < i + j → ((mv2ToPolyY R f).coeff j).coeff i = 0 := by
    intro j i hgt
    rw [coeff_mv2ToPolyY_coeff]
    by_contra hne
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    have hle := MvPolynomial.le_totalDegree hmem
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hle
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero, zero_add] at hle
    omega
  refine ⟨?_, ?_⟩
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    ext i
    rw [Polynomial.coeff_zero]
    exact hzero j i (by omega)
  · intro k hk
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    exact hzero k i (by omega)

lemma mv2ToPolyY_coeff_top_homog {R : Type*} [CommRing R] {n : ℕ}
    {F : MvPolynomial (Fin 3) R} (hFh : F.IsHomogeneous n) :
    (mv2ToPolyY R (dehomogZ F)).coeff n = Polynomial.C (eval ![0, 1, 0] F) := by
  ext i
  rw [coeff_mv2ToPolyY_coeff, Polynomial.coeff_C]
  have hde_coeff : ∀ j k : ℕ, (dehomogZ F).coeff (Finsupp.single 0 k + Finsupp.single 1 j) =
      if k + j ≤ n then F.coeff (Finsupp.single 0 k + Finsupp.single 1 j + Finsupp.single 2 (n - k - j)) else 0 := by
    intro j k
    conv_lhs => rw [F.as_sum]
    rw [map_sum, MvPolynomial.coeff_sum]
    let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 j
    have hterm : ∀ s ∈ F.support,
        (dehomogZ (monomial s (F.coeff s))).coeff m₀ =
          if s 0 = k ∧ s 1 = j then F.coeff s else 0 := by
      intro s _
      have hmon : dehomogZ (monomial s (F.coeff s)) =
          monomial (Finsupp.single (0 : Fin 2) (s 0) + Finsupp.single 1 (s 1)) (F.coeff s) := by
        dsimp only [dehomogZ]
        rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
          Fin.prod_univ_three, one_pow, mul_one, MvPolynomial.monomial_eq,
          Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        simp
      rw [hmon, MvPolynomial.coeff_monomial]
      have hiff : Finsupp.single (0 : Fin 2) (s 0) + Finsupp.single 1 (s 1) = m₀ ↔
          s 0 = k ∧ s 1 = j := by
        constructor
        · intro h
          exact ⟨by have := congrFun (congrArg DFunLike.coe h) 0; simpa [m₀] using this,
                 by have := congrFun (congrArg DFunLike.coe h) 1; simpa [m₀] using this⟩
        · rintro ⟨h0, h1⟩; rw [h0, h1]
      by_cases h : s 0 = k ∧ s 1 = j
      · simp [h.1, h.2, m₀]
      · simp [mt hiff.mp h, h]
    rw [Finset.sum_congr rfl hterm]
    split_ifs with hle
    · let s₀ : Fin 3 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 j + Finsupp.single 2 (n - k - j)
      have hs0 : ∀ s ∈ F.support, (s 0 = k ∧ s 1 = j) ↔ s = s₀ := by
        intro s hs
        have hdeg := isHomogeneous_sum_eq hFh hs
        rw [Fin.sum_univ_three] at hdeg
        constructor
        · rintro ⟨h0, h1⟩
          ext idx; match idx with
          | 0 => simp [s₀, h0]
          | 1 => simp [s₀, h1]
          | 2 => simp [s₀]; omega
        · intro h; subst h; simp [s₀]
      by_cases hm : s₀ ∈ F.support
      · rw [Finset.sum_eq_single s₀]
        · simp [s₀]
        · intro s hs hne; simp [mt (hs0 s hs).mp hne]
        · intro h; exact absurd hm h
      · rw [MvPolynomial.notMem_support_iff.mp hm]
        apply Finset.sum_eq_zero
        intro s hs
        have hne : s ≠ s₀ := fun h => hm (h ▸ hs)
        simp [mt (hs0 s hs).mp hne]
    · apply Finset.sum_eq_zero
      intro s hs
      have hdeg := isHomogeneous_sum_eq hFh hs
      rw [Fin.sum_univ_three] at hdeg
      have hnot : ¬ (s 0 = k ∧ s 1 = j) := by rintro ⟨h0, h1⟩; omega
      simp [hnot]
  rw [hde_coeff n i]
  by_cases hi : i = 0
  · subst hi
    simp only [zero_add, le_refl, ↓reduceIte, Nat.sub_zero, Nat.sub_self, Finsupp.single_zero,
      add_zero]
    conv_rhs => rw [F.as_sum]
    rw [map_sum]
    let s₁ : Fin 3 →₀ ℕ := Finsupp.single 1 n
    have hmon_ev : ∀ s ∈ F.support,
        eval (![0, 1, 0] : Fin 3 → R) (monomial s (F.coeff s)) =
          if s = s₁ then F.coeff s else 0 := by
      intro s hs
      have hdeg := isHomogeneous_sum_eq hFh hs
      rw [Fin.sum_univ_three] at hdeg
      rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_pow, mul_one]
      by_cases h0 : s 0 = 0
      · by_cases h2 : s 2 = 0
        · have heq : s = s₁ := by
            ext idx; match idx with
            | 0 => simp [s₁, h0]
            | 1 => simp [s₁]; omega
            | 2 => simp [s₁, h2]
          rw [h0, h2, pow_zero, mul_one, mul_one]; simp [heq]
        · have hne : s ≠ s₁ := fun h => h2 (by rw [h]; simp [s₁])
          simp [zero_pow h2, hne]
      · have hne : s ≠ s₁ := fun h => h0 (by rw [h]; simp [s₁])
        simp [zero_pow h0, hne]
    rw [Finset.sum_congr rfl hmon_ev]
    by_cases hm : s₁ ∈ F.support
    · rw [Finset.sum_eq_single s₁]
      · simp [s₁]
      · intro s _ hne; simp [hne]
      · intro h; exact absurd hm h
    · rw [MvPolynomial.notMem_support_iff.mp hm]
      symm
      apply Finset.sum_eq_zero
      intro s hs; simp [show s ≠ s₁ from fun h => hm (h ▸ hs)]
  · have hnot : ¬ (i + n ≤ n) := by omega
    simp [hnot, hi]

-- Degree bound for resultant of polynomials in (K[X])[Y] with total-degree bounds m, d
lemma natDegree_resultant_le {K : Type*} [Field K]
    {f g : Polynomial (Polynomial K)} {m d : ℕ}
    (hf : ∀ k ≤ m, (f.coeff k).natDegree ≤ m - k)
    (hg : ∀ k ≤ d, (g.coeff k).natDegree ≤ d - k) :
    (f.resultant g m d).natDegree ≤ m * d := by
  classical
  unfold Polynomial.resultant
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  apply Finset.sup_le
  intro σ _
  dsimp only [Function.comp_apply]
  have hsign : ∀ (s : ℤˣ) (P : Polynomial K), (s • P).natDegree ≤ P.natDegree := by
    intro s P
    rcases Int.units_eq_one_or s with rfl | rfl
    · simp
    · simp [Polynomial.natDegree_neg]
  refine (hsign _ _).trans ?_
  let base : Fin (m + d) → ℕ := fun j => if j.val < m then j.val else j.val - m
  let span : Fin (m + d) → ℕ := fun j => if j.val < m then d else m
  have hsylv_left : ∀ (i : Fin (m + d)) (j₁ : Fin m),
      (f.sylvester g m d) i (Fin.castAdd d j₁) =
        if i.val ∈ Set.Icc j₁.val (j₁.val + d) then g.coeff (i.val - j₁.val) else 0 := by
    intro i j₁; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_left]
  have hsylv_right : ∀ (i : Fin (m + d)) (j₁ : Fin d),
      (f.sylvester g m d) i (Fin.natAdd m j₁) =
        if i.val ∈ Set.Icc j₁.val (j₁.val + m) then f.coeff (i.val - j₁.val) else 0 := by
    intro i j₁; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_right]
  by_cases hall : ∀ j : Fin (m + d), (σ j).val ∈ Set.Icc (base j) (base j + span j)
  · refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have hterm : ∀ j : Fin (m + d),
        ((f.sylvester g m d) (σ j) j).natDegree ≤ span j + base j - (σ j).val := by
      intro j
      by_cases hj : j.val < m
      · let j₁ : Fin m := ⟨j.val, hj⟩
        have hj_eq : j = Fin.castAdd d j₁ := Fin.ext rfl
        have hbase : base j = j₁.val := by simp [base, hj, j₁]
        have hspan : span j = d := by simp [span, hj]
        have hin : (σ j).val ∈ Set.Icc j₁.val (j₁.val + d) := by
          have := hall j; rwa [hbase, hspan] at this
        rw [hj_eq, hsylv_left, ← hj_eq]
        simp only [hin, ite_true, hbase, hspan]
        have hle : (σ j).val - j₁.val ≤ d := by have h1 := hin.1; have h2 := hin.2; omega
        have heq : d - ((σ j).val - j₁.val) = d + j₁.val - (σ j).val := by
          have h1 := hin.1; have h2 := hin.2; omega
        rw [← heq]; exact hg _ hle
      · let j₁ : Fin d := ⟨j.val - m, by omega⟩
        have hj_eq : j = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hbase : base j = j₁.val := by simp [base, hj, j₁]
        have hspan : span j = m := by simp [span, hj]
        have hin : (σ j).val ∈ Set.Icc j₁.val (j₁.val + m) := by
          have := hall j; rwa [hbase, hspan] at this
        rw [hj_eq, hsylv_right, ← hj_eq]
        simp only [hin, ite_true, hbase, hspan]
        have hle : (σ j).val - j₁.val ≤ m := by have h1 := hin.1; have h2 := hin.2; omega
        have heq : m - ((σ j).val - j₁.val) = m + j₁.val - (σ j).val := by
          have h1 := hin.1; have h2 := hin.2; omega
        rw [← heq]; exact hf _ hle
    calc ∑ j : Fin (m + d), ((f.sylvester g m d) (σ j) j).natDegree
        ≤ ∑ j : Fin (m + d), (span j + base j - (σ j).val) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = m * d := by
          have hadd : ∑ j : Fin (m + d), (span j + base j - (σ j).val) +
              ∑ j : Fin (m + d), (σ j).val = ∑ j : Fin (m + d), (span j + base j) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j _
            have h2 := (hall j).2; omega
          have hperm : ∑ j : Fin (m + d), (σ j).val = ∑ i : Fin (m + d), i.val :=
            Equiv.sum_comp σ (fun i : Fin (m + d) => i.val)
          have hsum_i : ∑ i : Fin (m + d), i.val =
              (∑ j₁ : Fin m, j₁.val) + (∑ j₁ : Fin d, (m + j₁.val)) := by
            rw [Fin.sum_univ_add]; simp only [Fin.val_castAdd, Fin.val_natAdd]
          have hsum_sb : ∑ j : Fin (m + d), (span j + base j) =
              (∑ j₁ : Fin m, (d + j₁.val)) + (∑ j₁ : Fin d, (m + j₁.val)) := by
            rw [Fin.sum_univ_add]
            congr 1
            · apply Finset.sum_congr rfl; intro j₁ _; simp [base, span, j₁.isLt]
            · apply Finset.sum_congr rfl; intro j₁ _; simp [base, span]
          have hdiff : ∑ j₁ : Fin m, (d + j₁.val) = m * d + ∑ j₁ : Fin m, j₁.val := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul]
          omega
  · have hex : ∃ j : Fin (m + d), (σ j).val ∉ Set.Icc (base j) (base j + span j) := by
      by_contra h; apply hall; intro j; exact not_not.mp (fun hj => h ⟨j, hj⟩)
    obtain ⟨j₀, hj₀⟩ := hex
    have hzero : (f.sylvester g m d) (σ j₀) j₀ = 0 := by
      by_cases hj : j₀.val < m
      · let j₁ : Fin m := ⟨j₀.val, hj⟩
        have hj_eq : j₀ = Fin.castAdd d j₁ := Fin.ext rfl
        have hnot : (σ j₀).val ∉ Set.Icc j₁.val (j₁.val + d) := by
          have : base j₀ = j₁.val := by simp [base, hj, j₁]
          have : span j₀ = d := by simp [span, hj]
          rwa [‹base j₀ = _›, ‹span j₀ = _›] at hj₀
        rw [hj_eq, hsylv_left, ← hj_eq]; simp [hnot]
      · let j₁ : Fin d := ⟨j₀.val - m, by omega⟩
        have hj_eq : j₀ = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hnot : (σ j₀).val ∉ Set.Icc j₁.val (j₁.val + m) := by
          have : base j₀ = j₁.val := by simp [base, hj, j₁]
          have : span j₀ = m := by simp [span, hj]
          rwa [‹base j₀ = _›, ‹span j₀ = _›] at hj₀
        rw [hj_eq, hsylv_right, ← hj_eq]; simp [hnot]
    have hprod0 : (∏ i : Fin (m + d), (f.sylvester g m d) (σ i) i) = 0 :=
      Finset.prod_eq_zero (mem_univ j₀) hzero
    rw [hprod0, Polynomial.natDegree_zero]
    exact Nat.zero_le _

-- Nonvanishing of resultant when f is irreducible of Y-degree m with constant nonzero top coeff, and deg_Y(g) ≤ d < m
lemma resultant_ne_zero_of_irred_lt_deg {K : Type*} [Field K]
    {f g : MvPolynomial (Fin 2) K} {m d : ℕ}
    (hf_irr : Irreducible f)
    (hf_nd : (mv2ToPolyY K f).natDegree = m)
    {c : K} (hc : c ≠ 0) (hf_lc : (mv2ToPolyY K f).coeff m = Polynomial.C c)
    (hg0 : g ≠ 0) (hg_nd : (mv2ToPolyY K g).natDegree ≤ d) (hd_lt : d < m) :
    (mv2ToPolyY K f).resultant (mv2ToPolyY K g) m d ≠ 0 := by
  let pf := mv2ToPolyY K f
  let pg := mv2ToPolyY K g
  let FK := FractionRing (Polynomial K)
  let ιK := algebraMap (Polynomial K) FK
  have hι_inj : Function.Injective ιK := IsFractionRing.injective (Polynomial K) FK
  have hpf_irr : Irreducible pf := by
    let e := mv2EquivPolyY K
    have hnotu : ¬ IsUnit pf := fun hu => by
      have h1 : e.symm pf = f := polyYToMv2_mv2ToPolyY f
      exact hf_irr.not_isUnit (h1 ▸ hu.map e.symm.toRingHom)
    refine ⟨hnotu, ?_⟩
    intro a b hab
    have hback : f = e.symm a * e.symm b := by
      have h1 : e.symm pf = f := polyYToMv2_mv2ToPolyY f
      have h2 := congrArg e.symm hab
      rw [h1, map_mul] at h2; exact h2
    rcases hf_irr.isUnit_or_isUnit hback with ha | hb
    · left; have h1 : e (e.symm a) = a := mv2ToPolyY_polyYToMv2 a
      exact h1 ▸ ha.map e.toRingHom
    · right; have h1 : e (e.symm b) = b := mv2ToPolyY_polyYToMv2 b
      exact h1 ▸ hb.map e.toRingHom
  let u : Polynomial (Polynomial K) := Polynomial.C (Polynomial.C c⁻¹)
  have hu : IsUnit u := ((isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).map Polynomial.C).map Polynomial.C
  have hmon : (u * pf).Monic := by
    have hnd : (u * pf).natDegree = m := by
      rw [Polynomial.natDegree_C_mul (by simp [hc]), hf_nd]
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, Polynomial.coeff_C_mul, hf_lc,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  have hmon_irr : Irreducible (u * pf) :=
    (associated_unit_mul_left pf u hu).irreducible_iff.mpr hpf_irr
  have hmon_map_irr : Irreducible ((u * pf).map ιK) :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hmon.isPrimitive).mp hmon_irr
  have hpf_map_irr : Irreducible (pf.map ιK) := by
    have hu_map : IsUnit (u.map ιK) := hu.map (Polynomial.mapRingHom ιK)
    rw [Polynomial.map_mul] at hmon_map_irr
    exact (associated_unit_mul_left (pf.map ιK) (u.map ιK) hu_map).irreducible_iff.mp hmon_map_irr
  have hpf_map_nd : (pf.map ιK).natDegree = m := by
    rw [Polynomial.natDegree_map_eq_of_injective hι_inj, hf_nd]
  have hpg_map_ne : pg.map ιK ≠ 0 := by
    intro h0
    apply hg0
    have hpg0 : pg = 0 := Polynomial.map_injective ιK hι_inj (h0.trans (Polynomial.map_zero ιK).symm)
    exact (mv2EquivPolyY K).injective (hpg0.trans (map_zero (mv2EquivPolyY K)).symm)
  have hpg_map_nd : (pg.map ιK).natDegree ≤ d := by
    rw [Polynomial.natDegree_map_eq_of_injective hι_inj]; exact hg_nd
  have hndvd : ¬ (pf.map ιK ∣ pg.map ιK) := by
    rintro ⟨q, hq⟩
    have hq0 : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hpg_map_ne hq
    have hle := Polynomial.natDegree_le_of_dvd ⟨q, hq⟩ hpg_map_ne
    omega
  have hcop : IsCoprime (pf.map ιK) (pg.map ιK) := hpf_map_irr.coprime_iff_not_dvd.mpr hndvd
  have hres0 : (pf.map ιK).resultant (pg.map ιK) ≠ 0 := Polynomial.resultant_ne_zero _ _ hcop
  have hres_pad : (pf.map ιK).resultant (pg.map ιK) m d ≠ 0 := by
    have hadd := Polynomial.resultant_add_right_deg (pf.map ιK) (pg.map ιK) m (pg.map ιK).natDegree
      (d - (pg.map ιK).natDegree) le_rfl
    have hsum : (pg.map ιK).natDegree + (d - (pg.map ιK).natDegree) = d := by omega
    rw [hsum] at hadd
    rw [hadd]
    have hlc_ne : (pf.map ιK).coeff m ≠ 0 := by
      rw [Polynomial.coeff_map, hf_lc]
      intro h0
      have := hι_inj (h0.trans (map_zero ιK).symm)
      exact hc (Polynomial.C_eq_zero.mp this)
    refine mul_ne_zero (pow_ne_zero _ hlc_ne) ?_
    change (pf.map ιK).resultant (pg.map ιK) (pf.map ιK).natDegree (pg.map ιK).natDegree ≠ 0 at hres0
    rwa [hpf_map_nd] at hres0
  intro h0
  apply hres_pad
  rw [Polynomial.resultant_map_map, h0, map_zero]

lemma eval_map_eq_map_eval {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (v : Fin 3 → R) (F : MvPolynomial (Fin 3) R) :
    eval (φ ∘ v) (F.map φ) = φ (eval v F) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.hom_eval₂ F (RingHom.id R) φ v).symm

-- Existence of a smooth point (a, b) ∈ K² with f(a, b) = 0 and f_y(a, b) ≠ 0
lemma exists_smooth_point_over_K {p n : ℕ} [Fact p.Prime] (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (hFirrK : Irreducible (F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (he0 : eval ![1, 0, 0] F ≠ 0) (he1 : eval ![0, 1, 0] F ≠ 0) :
    let K := AlgebraicClosure (ZMod p)
    let fK := dehomogZ (F.map (algebraMap (ZMod p) K))
    ∃ a b : K, eval ![a, b] fK = 0 ∧ eval ![a, b] (MvPolynomial.pderiv 1 fK) ≠ 0 := by
  intro K fK
  let ι := algebraMap (ZMod p) K
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hFK_h : (F.map ι).IsHomogeneous n := hFh.map ι
  have he0K : eval ![1, 0, 0] (F.map ι) ≠ 0 := by
    have hv : (ι ∘ ![1, 0, 0] : Fin 3 → K) = ![1, 0, 0] := by
      ext i; match i with | 0 => simp | 1 => simp | 2 => simp
    rw [← hv, eval_map_eq_map_eval]
    exact fun h => he0 (hι_inj (h.trans (map_zero ι).symm))
  have he1K : eval ![0, 1, 0] (F.map ι) ≠ 0 := by
    have hv : (ι ∘ ![0, 1, 0] : Fin 3 → K) = ![0, 1, 0] := by
      ext i; match i with | 0 => simp | 1 => simp | 2 => simp
    rw [← hv, eval_map_eq_map_eval]
    exact fun h => he1 (hι_inj (h.trans (map_zero ι).symm))
  have hX2_ndvd : ¬ (X (2 : Fin 3) ∣ F.map ι) := by
    rintro ⟨Q, hQ⟩; apply he0K; rw [hQ, map_mul, eval_X]; simp
  have hfK_irr : Irreducible fK := irreducible_dehomogZ hFK_h hFirrK hX2_ndvd
  have hfK_td : fK.totalDegree ≤ n := dehomogZ_totalDegree_le hFK_h
  have hpf_lc : (mv2ToPolyY K fK).coeff n = Polynomial.C (eval ![0, 1, 0] (F.map ι)) :=
    mv2ToPolyY_coeff_top_homog hFK_h
  have hpf_nd : (mv2ToPolyY K fK).natDegree = n := by
    have hle := (mv2ToPolyY_degree_bounds hfK_td).1
    have hge : n ≤ (mv2ToPolyY K fK).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hpf_lc]; exact Polynomial.C_ne_zero.mpr he1K)
    omega
  let fyK := MvPolynomial.pderiv 1 fK
  have hpfy_eq : mv2ToPolyY K fyK = Polynomial.derivative (mv2ToPolyY K fK) :=
    mv2ToPolyY_pderiv_1 fK
  have hnK_ne : (n : K) ≠ 0 := by
    have hnp : (n : ZMod p) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff n p).mp h0
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
    have h1 : (n : K) = ι (n : ZMod p) := by simp
    rw [h1]; exact fun h => hnp (hι_inj (h.trans (map_zero ι).symm))
  have hpfy_top : (mv2ToPolyY K fyK).coeff (n - 1) =
      Polynomial.C ((n : K) * eval ![0, 1, 0] (F.map ι)) := by
    rw [hpfy_eq, Polynomial.coeff_derivative]
    have h1 : n - 1 + 1 = n := by omega
    rw [h1, hpf_lc]
    have hcast : ((n - 1 : ℕ) : Polynomial K) + 1 = Polynomial.C (n : K) := by
      rw [← map_natCast Polynomial.C, ← map_one Polynomial.C, ← map_add, ← Nat.cast_succ,
        Nat.succ_eq_add_one, show n - 1 + 1 = n by omega]
    rw [hcast, ← map_mul, mul_comm]
  have hfyK_ne : fyK ≠ 0 := by
    intro h0
    have := congrArg (fun q => (mv2ToPolyY K q).coeff (n - 1)) h0
    rw [map_zero, Polynomial.coeff_zero, hpfy_top] at this
    exact mul_ne_zero hnK_ne he1K (Polynomial.C_eq_zero.mp this)
  have hpfy_nd : (mv2ToPolyY K fyK).natDegree ≤ n - 1 := by
    rw [hpfy_eq]; exact (Polynomial.natDegree_derivative_le _).trans (by omega)
  let Ry : Polynomial K := (mv2ToPolyY K fK).resultant (mv2ToPolyY K fyK) n (n - 1)
  have hRy_ne : Ry ≠ 0 :=
    resultant_ne_zero_of_irred_lt_deg hfK_irr hpf_nd he1K hpf_lc hfyK_ne hpfy_nd (by omega)
  obtain ⟨a, ha⟩ := exists_notMem_of_isAlgClosed Ry.roots.toFinset
  have hRy_a : Polynomial.eval a Ry ≠ 0 := by
    intro h0; apply ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hRy_ne, Polynomial.IsRoot.def]; exact h0
  let fa : Polynomial K := (mv2ToPolyY K fK).map (Polynomial.evalRingHom a)
  have hfa_nd : fa.natDegree = n := by
    have hle : fa.natDegree ≤ n := Polynomial.natDegree_map_le.trans (by omega)
    have hge : n ≤ fa.natDegree := Polynomial.le_natDegree_of_ne_zero (by
      rw [Polynomial.coeff_map, hpf_lc]; simpa using he1K)
    omega
  have hfa_deg : fa.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (by intro h0; rw [h0, Polynomial.natDegree_zero] at hfa_nd; omega)]
    rw [hfa_nd]; exact_mod_cast (by omega : n ≠ 0)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_root fa hfa_deg
  have hev_a : ∀ q : MvPolynomial (Fin 2) K,
      Polynomial.eval b ((mv2ToPolyY K q).map (Polynomial.evalRingHom a)) = eval ![a, b] q := by
    intro q
    rw [eval_map_mv2ToPolyY]
    have h1 : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id K := by ext r; simp
    rw [h1]
    have h2 : ![(Polynomial.evalRingHom a) Polynomial.X, b] = ![a, b] := by
      ext i; match i with | 0 => simp | 1 => simp
    rw [h2]; rfl
  refine ⟨a, b, ?_, ?_⟩
  · rw [← hev_a]; exact Polynomial.IsRoot.def.mp hb
  · intro hby0
    apply hRy_a
    dsimp only [Ry]
    change (Polynomial.evalRingHom a) ((mv2ToPolyY K fK).resultant (mv2ToPolyY K fyK) n (n - 1)) = 0
    rw [← Polynomial.resultant_map_map]
    let fya := (mv2ToPolyY K fyK).map (Polynomial.evalRingHom a)
    have hfya_nd : fya.natDegree = n - 1 := by
      have hle : fya.natDegree ≤ n - 1 := Polynomial.natDegree_map_le.trans hpfy_nd
      have hge : n - 1 ≤ fya.natDegree := Polynomial.le_natDegree_of_ne_zero (by
        rw [Polynomial.coeff_map, hpfy_top]; simpa using mul_ne_zero hnK_ne he1K)
      omega
    change fa.resultant fya n (n - 1) = 0
    rw [← hfya_nd, ← hfa_nd]
    change fa.resultant fya = 0
    rw [Polynomial.resultant_eq_zero_iff]
    refine ⟨Or.inl (by intro h0; rw [h0, Polynomial.natDegree_zero] at hfa_nd; omega), ?_⟩
    rintro ⟨u, v, huv⟩
    have he := congrArg (Polynomial.eval b) huv
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.IsRoot.def.mp hb, hev_a fyK, hby0, mul_zero, mul_zero, add_zero,
      Polynomial.eval_one] at he
    exact zero_ne_one he

-- Hensel power series solver for g(X, y) = 0 with g(0, 0) = 0 and g_y(0, 0) ≠ 0
lemma eval₂Hom_X_dvd_sub_C {K : Type*} [Field K] {s : PowerSeries K}
    (hs : PowerSeries.X ∣ s) (h : MvPolynomial (Fin 2) K) :
    PowerSeries.X ∣ MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h -
      PowerSeries.C (eval ![0, 0] h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb =>
    simp only [map_add]
    have hid : (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] a +
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] b) -
        (PowerSeries.C (eval ![0, 0] a) + PowerSeries.C (eval ![0, 0] b)) =
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] a - PowerSeries.C (eval ![0, 0] a)) +
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] b - PowerSeries.C (eval ![0, 0] b)) := by ring
    rw [hid]; exact dvd_add ha hb
  | mul_X a i _ =>
    rw [map_mul, map_mul, map_mul]
    match i with
    | 0 =>
      simp only [MvPolynomial.eval₂Hom_X', eval_X, Matrix.cons_val_zero, map_zero, mul_zero, sub_zero]
      exact dvd_mul_left PowerSeries.X _
    | 1 =>
      simp only [MvPolynomial.eval₂Hom_X', eval_X, Matrix.cons_val_one, Matrix.cons_val, map_zero,
        mul_zero, sub_zero]
      exact dvd_mul_of_dvd_right hs _

lemma eval₂Hom_mod_X_pow {K : Type*} [Field K] {s₁ s₂ : PowerSeries K} {m : ℕ}
    (hdiff : PowerSeries.X ^ m ∣ s₁ - s₂) (h : MvPolynomial (Fin 2) K) :
    PowerSeries.X ^ m ∣
      MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] h -
      MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] h := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add a b ha hb =>
    simp only [map_add]
    have hid : (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] a +
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] b) -
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] a +
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] b) =
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] a -
          MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] a) +
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] b -
          MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] b) := by ring
    rw [hid]; exact dvd_add ha hb
  | mul_X a i ha =>
    rw [map_mul, map_mul]
    match i with
    | 0 =>
      simp only [MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, ← sub_mul]
      exact dvd_mul_of_dvd_left ha _
    | 1 =>
      simp only [MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val]
      have hid : MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] a * s₁ -
          MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] a * s₂ =
          (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₁] a -
            MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] a) * s₁ +
          MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s₂] a * (s₁ - s₂) := by ring
      rw [hid]; exact dvd_add (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hdiff _)

lemma eval₂Hom_add_monomial_mod {K : Type*} [Field K] {s : PowerSeries K}
    (hs : PowerSeries.X ∣ s) (k : ℕ) (a : K) (h : MvPolynomial (Fin 2) K) :
    let δ : PowerSeries K := PowerSeries.C a * PowerSeries.X ^ (k + 1)
    PowerSeries.X ^ (k + 2) ∣
      MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h -
      (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h +
        PowerSeries.C (eval ![0, 0] (MvPolynomial.pderiv 1 h)) * δ) := by
  intro δ
  have hδ_dvd : PowerSeries.X ^ (k + 1) ∣ δ := dvd_mul_left _ _
  have hδ_X : PowerSeries.X ∣ δ :=
    dvd_trans (dvd_pow_self (PowerSeries.X : PowerSeries K) (by omega)) hδ_dvd
  have hsδ_X : PowerSeries.X ∣ s + δ := dvd_add hs hδ_X
  induction h using MvPolynomial.induction_on with
  | C r => simp
  | add h₁ h₂ ih₁ ih₂ =>
    simp only [map_add]
    have hid : (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h₁ +
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h₂) -
        ((MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h₁ +
          MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h₂) +
          (PowerSeries.C (eval ![0, 0] (MvPolynomial.pderiv 1 h₁)) +
            PowerSeries.C (eval ![0, 0] (MvPolynomial.pderiv 1 h₂))) * δ) =
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h₁ -
          (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h₁ +
            PowerSeries.C (eval ![0, 0] (MvPolynomial.pderiv 1 h₁)) * δ)) +
        (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h₂ -
          (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h₂ +
            PowerSeries.C (eval ![0, 0] (MvPolynomial.pderiv 1 h₂)) * δ)) := by ring
    rw [hid]; exact dvd_add ih₁ ih₂
  | mul_X h i _ =>
    have hmod : PowerSeries.X ^ (k + 1) ∣
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h -
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h :=
      eval₂Hom_mod_X_pow (by rw [add_sub_cancel_left]; exact hδ_dvd) h
    match i with
    | 0 =>
      have hp0 : eval ![0, 0] (MvPolynomial.pderiv 1 (h * X 0)) = 0 := by
        rw [MvPolynomial.pderiv_mul]; simp [MvPolynomial.pderiv_X]
      rw [hp0, map_zero, zero_mul, add_zero, map_mul, map_mul]
      simp only [MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, ← sub_mul]
      have hpow : (PowerSeries.X : PowerSeries K) ^ (k + 2) =
          (PowerSeries.X : PowerSeries K) ^ (k + 1) * PowerSeries.X := pow_succ _ _
      rw [hpow]; exact mul_dvd_mul hmod dvd_rfl
    | 1 =>
      have hp1 : eval ![0, 0] (MvPolynomial.pderiv 1 (h * X 1)) = eval ![0, 0] h := by
        rw [MvPolynomial.pderiv_mul]; simp [MvPolynomial.pderiv_X]
      rw [hp1, map_mul, map_mul]
      simp only [MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val]
      have hid : MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h * (s + δ) -
          (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h * s +
            PowerSeries.C (eval ![0, 0] h) * δ) =
          (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h -
            MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] h) * s +
          (MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s + δ] h -
            PowerSeries.C (eval ![0, 0] h)) * δ := by ring
      rw [hid]
      have hpow1 : (PowerSeries.X : PowerSeries K) ^ (k + 2) =
          (PowerSeries.X : PowerSeries K) ^ (k + 1) * PowerSeries.X := pow_succ _ _
      have hpow2 : (PowerSeries.X : PowerSeries K) ^ (k + 2) =
          (PowerSeries.X : PowerSeries K) * PowerSeries.X ^ (k + 1) := by
        rw [pow_succ, mul_comm]
      exact dvd_add (hpow1 ▸ mul_dvd_mul hmod hs)
        (hpow2 ▸ mul_dvd_mul (eval₂Hom_X_dvd_sub_C hsδ_X h) hδ_dvd)

lemma exists_hensel_series {K : Type*} [Field K] (g : MvPolynomial (Fin 2) K)
    (hg0 : eval ![0, 0] g = 0) (hgy0 : eval ![0, 0] (MvPolynomial.pderiv 1 g) ≠ 0) :
    ∃ y : PowerSeries K,
      PowerSeries.constantCoeff y = 0 ∧
      MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, y] g = 0 := by
  let u : K := eval ![0, 0] (MvPolynomial.pderiv 1 g)
  let ev : PowerSeries K → PowerSeries K := fun s =>
    MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, s] g
  let y_trunc : ℕ → PowerSeries K := Nat.rec 0 (fun k yk =>
    yk + PowerSeries.C (-(PowerSeries.coeff (k + 1) (ev yk)) / u) * PowerSeries.X ^ (k + 1))
  have hy_const : ∀ k, PowerSeries.constantCoeff (y_trunc k) = 0 := by
    intro k
    induction k with
    | zero => simp [y_trunc]
    | succ k ih =>
      change PowerSeries.constantCoeff
        (y_trunc k + PowerSeries.C (-(PowerSeries.coeff (k + 1) (ev (y_trunc k))) / u) *
          PowerSeries.X ^ (k + 1)) = 0
      rw [map_add, ih, zero_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
        zero_pow (by omega), mul_zero]
  have hy_step : ∀ k j, j ≤ k → PowerSeries.coeff j (y_trunc (k + 1)) = PowerSeries.coeff j (y_trunc k) := by
    intro k j hjk
    change PowerSeries.coeff j
      (y_trunc k + PowerSeries.C (-(PowerSeries.coeff (k + 1) (ev (y_trunc k))) / u) *
        PowerSeries.X ^ (k + 1)) = PowerSeries.coeff j (y_trunc k)
    rw [map_add, PowerSeries.coeff_C_mul_X_pow]
    have hne : j ≠ k + 1 := by omega
    simp only [hne, ↓reduceIte, add_zero]
  have hy_stable : ∀ k m j, j ≤ k → k ≤ m → PowerSeries.coeff j (y_trunc m) = PowerSeries.coeff j (y_trunc k) := by
    intro k m j hjk hkm
    induction m with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    | succ m ih =>
      by_cases h : k = m + 1
      · subst h; rfl
      · rw [hy_step m j (by omega), ih (by omega)]
  have hy_dvd : ∀ k, PowerSeries.X ^ (k + 1) ∣ ev (y_trunc k) := by
    intro k
    induction k with
    | zero =>
      rw [pow_one]
      have h0 : ev (y_trunc 0) = ev 0 - PowerSeries.C (eval ![0, 0] g) := by
        rw [hg0, map_zero, sub_zero]; rfl
      rw [h0]
      exact eval₂Hom_X_dvd_sub_C (dvd_zero PowerSeries.X) g
    | succ k ih =>
      let a := -(PowerSeries.coeff (k + 1) (ev (y_trunc k))) / u
      let δ := PowerSeries.C a * PowerSeries.X ^ (k + 1)
      have hX_yk : PowerSeries.X ∣ y_trunc k := PowerSeries.X_dvd_iff.mpr (hy_const k)
      have hmod := eval₂Hom_add_monomial_mod hX_yk k a g
      have hlin_dvd : PowerSeries.X ^ (k + 2) ∣ ev (y_trunc k) + PowerSeries.C u * δ := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro m hm
        rw [map_add]
        have hδc : PowerSeries.C u * δ = PowerSeries.C (u * a) * PowerSeries.X ^ (k + 1) := by
          dsimp only [δ]; rw [← mul_assoc, ← map_mul]
        rw [hδc, PowerSeries.coeff_C_mul_X_pow]
        by_cases hmk : m = k + 1
        · subst hmk
          simp only [↓reduceIte]
          dsimp only [a]
          rw [mul_div_cancel₀ _ hgy0, add_neg_cancel]
        · have hmlt : m < k + 1 := by omega
          have hc0 := (PowerSeries.X_pow_dvd_iff.mp ih) m hmlt
          simp [hmk, hc0]
      have hstep : ev (y_trunc (k + 1)) =
          (ev (y_trunc k + δ) - (ev (y_trunc k) + PowerSeries.C u * δ)) +
          (ev (y_trunc k) + PowerSeries.C u * δ) := by
        change ev (y_trunc k + δ) = _; ring
      rw [hstep]; exact dvd_add hmod hlin_dvd
  let y : PowerSeries K := PowerSeries.mk (fun k => PowerSeries.coeff k (y_trunc k))
  refine ⟨y, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hy_const 0
  · ext k
    rw [map_zero]
    have hdiff : PowerSeries.X ^ (k + 1) ∣ y - y_trunc k := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, PowerSeries.coeff_mk, hy_stable m k m le_rfl (by omega), sub_self]
    have hev_diff : PowerSeries.X ^ (k + 1) ∣ ev y - ev (y_trunc k) :=
      eval₂Hom_mod_X_pow hdiff g
    have hev_y : PowerSeries.X ^ (k + 1) ∣ ev y := by
      have hid : ev y = (ev y - ev (y_trunc k)) + ev (y_trunc k) := by ring
      rw [hid]; exact dvd_add hev_diff (hy_dvd k)
    exact (PowerSeries.X_pow_dvd_iff.mp hev_y) k (by omega)

-- PowerSeries RingDeriv & chain rule
noncomputable def powerSeriesDeriv (R : Type*) [CommRing R] : RingDeriv (PowerSeries R) where
  toFun := PowerSeries.derivative R
  map_add' := map_add (PowerSeries.derivative R)
  map_mul' a b := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_comm b, add_comm]

lemma powerSeries_chain_rule {R : Type*} [CommRing R] (s₁ s₂ : PowerSeries R)
    (h : MvPolynomial (Fin 2) R) :
    let φ := MvPolynomial.eval₂Hom PowerSeries.C ![s₁, s₂]
    PowerSeries.derivative R (φ h) =
      φ (MvPolynomial.pderiv 0 h) * PowerSeries.derivative R s₁ +
      φ (MvPolynomial.pderiv 1 h) * PowerSeries.derivative R s₂ := by
  intro φ
  induction h using MvPolynomial.induction_on with
  | C a => simp [φ, PowerSeries.derivative_C]
  | add a b ha hb =>
    simp only [map_add, ha, hb]
    ring
  | mul_X a i ha =>
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ha,
      MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul]
    match i with
    | 0 =>
      simp only [φ, MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, MvPolynomial.pderiv_X,
        Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), map_add, map_mul,
        mul_one, mul_zero, add_zero]
      ring
    | 1 =>
      simp only [φ, MvPolynomial.eval₂Hom_X', Matrix.cons_val_one, Matrix.cons_val,
        MvPolynomial.pderiv_X, Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        map_add, map_mul, mul_one, mul_zero, add_zero]
      ring

-- Wronskian minimal-order constant linear relation when det(w0Matrix D m) = 0
def wronskianSub {L : Type*} [CommRing L] (D : RingDeriv L) (m : Fin 6 → L) (k : ℕ) (hk : k ≤ 5) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) L :=
  fun i j => D.iter i.val (m ⟨j.val, by omega⟩)

lemma RingDeriv.map_sum {R : Type*} [CommRing R] (D : RingDeriv R) {ι : Type*}
    (s : Finset ι) (f : ι → R) : D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D.map_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, D.map_add', ih, Finset.sum_insert ha]

lemma det_wronskianSub_congr {L : Type*} [CommRing L] (D : RingDeriv L) (m : Fin 6 → L)
    {k₁ k₂ : ℕ} (heq : k₁ = k₂) (h1 : k₁ ≤ 5) (h2 : k₂ ≤ 5) :
    (wronskianSub D m k₁ h1).det = (wronskianSub D m k₂ h2).det := by
  subst heq; rfl

lemma exists_const_rel_of_w0_det_eq_zero {L : Type*} [Field L] (D : RingDeriv L) (m : Fin 6 → L)
    (hm0 : m 0 = 1) (hw0 : (w0Matrix D m).det = 0) :
    ∃ (r : ℕ) (hr : r ≤ 4) (c : Fin (r + 2) → L),
      c (Fin.last (r + 1)) = -1 ∧
      (∀ j, D (c j) = 0) ∧
      ∑ j : Fin (r + 2), c j * m ⟨j.val, by omega⟩ = 0 := by
  classical
  have hex : ∃ k : ℕ, ∃ hk : k ≤ 5, (wronskianSub D m k hk).det = 0 := by
    refine ⟨5, le_rfl, ?_⟩
    have heq : wronskianSub D m 5 le_rfl = w0Matrix D m := by
      ext i j; rfl
    rw [heq]; exact hw0
  let k := Nat.find hex
  obtain ⟨hk5, hk_det⟩ := Nat.find_spec hex
  have hk_ne0 : k ≠ 0 := by
    intro h0
    have hdet0 : (wronskianSub D m 0 (by omega)).det = 1 := by
      rw [Matrix.det_fin_one]
      exact hm0
    have hk0 : (wronskianSub D m 0 (by omega)).det = 0 :=
      (det_wronskianSub_congr D m h0.symm (by omega) hk5).trans hk_det
    exact one_ne_zero (hdet0.symm.trans hk0)
  let r := k - 1
  have hr_eq : r + 1 = k := by omega
  have hr4 : r ≤ 4 := by omega
  let Mr := wronskianSub D m r (by omega)
  have hMr_det : Mr.det ≠ 0 := by
    intro h0
    exact Nat.find_min hex (by omega : r < k) ⟨by omega, h0⟩
  let Mr1 := wronskianSub D m (r + 1) (by omega)
  have hMr1_det : Mr1.det = 0 :=
    (det_wronskianSub_congr D m hr_eq (by omega) hk5).trans hk_det
  have hMr_unit : IsUnit Mr.det := isUnit_iff_ne_zero.mpr hMr_det
  let v : Fin (r + 1) → L := fun i => D.iter i.val (m ⟨r + 1, by omega⟩)
  let a : Fin (r + 1) → L := Mr⁻¹.mulVec v
  have hMa : Mr.mulVec a = v := by
    dsimp only [a]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Mr hMr_unit, Matrix.one_mulVec]
  -- Upper-triangular unipotent U clearing the top r + 1 entries of the last column of Mr1
  let U : Matrix (Fin (r + 2)) (Fin (r + 2)) L := fun i j =>
    if j = Fin.last (r + 1) then
      if h : i.val < r + 1 then -a ⟨i.val, h⟩ else 1
    else if i = j then 1 else 0
  have hU_ut : U.BlockTriangular id := by
    intro i j hij
    have hlt : j.val < i.val := hij
    have hj_ne : j ≠ Fin.last (r + 1) := by
      intro heq; rw [heq, Fin.val_last] at hlt; omega
    have hij_ne : i ≠ j := by intro heq; rw [heq] at hlt; omega
    simp [U, hj_ne, hij_ne]
  have hU_det : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_ut]
    apply Finset.prod_eq_one
    intro i _
    by_cases h : i = Fin.last (r + 1)
    · subst h; simp [U]
    · simp [U, h]
  let P := Mr1 * U
  have hP_det : P.det = 0 := by
    rw [Matrix.det_mul, hMr1_det, hU_det, mul_one]
  have hP_col_cast : ∀ (i : Fin (r + 2)) (j : Fin (r + 1)), P i j.castSucc = Mr1 i j.castSucc := by
    intro i j
    dsimp only [P]; rw [Matrix.mul_apply]
    have hj_ne : j.castSucc ≠ Fin.last (r + 1) := Fin.castSucc_ne_last j
    rw [Finset.sum_eq_single j.castSucc]
    · simp [U, hj_ne]
    · intro l _ hne; simp [U, hj_ne, hne]
    · intro h; exact absurd (mem_univ _) h
  have hP_last_col : ∀ i : Fin (r + 2),
      P i (Fin.last (r + 1)) =
        D.iter i.val (m ⟨r + 1, by omega⟩) - ∑ j : Fin (r + 1), D.iter i.val (m ⟨j.val, by omega⟩) * a j := by
    intro i
    dsimp only [P]; rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
    have hlast : Mr1 i (Fin.last (r + 1)) * U (Fin.last (r + 1)) (Fin.last (r + 1)) =
        D.iter i.val (m ⟨r + 1, by omega⟩) := by
      simp [U, Mr1, wronskianSub, Fin.val_last]
    rw [hlast]
    have hsum : ∑ j : Fin (r + 1), Mr1 i j.castSucc * U j.castSucc (Fin.last (r + 1)) =
        -∑ j : Fin (r + 1), D.iter i.val (m ⟨j.val, by omega⟩) * a j := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      have hjlt : (j.castSucc : Fin (r + 2)).val < r + 1 := j.isLt
      simp only [U, ↓reduceIte, ↓reduceDIte, Mr1, wronskianSub, Fin.val_castSucc, j.isLt, Fin.eta, mul_neg]
    rw [hsum]; ring
  have hP_last_top : ∀ i : Fin (r + 1), P i.castSucc (Fin.last (r + 1)) = 0 := by
    intro i
    rw [hP_last_col]
    have hi := congrFun hMa i
    simp only [Matrix.mulVec, dotProduct, Mr, wronskianSub, v] at hi
    simp only [Fin.val_castSucc, hi, sub_self]
  let Δ : L := P (Fin.last (r + 1)) (Fin.last (r + 1))
  have hΔ_eq0 : Δ = 0 := by
    have hdet_exp : P.det = Δ * Mr.det := by
      rw [← Matrix.det_transpose, Matrix.det_succ_row (i := Fin.last (r + 1))]
      rw [Finset.sum_eq_single (Fin.last (r + 1))]
      · have hsign : (-1 : L) ^ ((Fin.last (r + 1) : Fin (r + 2)).val + (Fin.last (r + 1) : Fin (r + 2)).val) = 1 := by
          rw [Fin.val_last, ← two_mul, pow_mul]; norm_num
        have hsub : P.transpose.submatrix (Fin.last (r + 1)).succAbove (Fin.last (r + 1)).succAbove = Mr.transpose := by
          ext i j
          simp only [Matrix.submatrix_apply, Matrix.transpose_apply, Fin.succAbove_last]
          rw [hP_col_cast]
          rfl
        rw [hsign, one_mul, hsub, Matrix.det_transpose]
        rfl
      · intro j _ hne
        have hjlt : j.val < r + 1 := by
          have := j.isLt
          have : j.val ≠ r + 1 := fun h => hne (Fin.ext (by rw [Fin.val_last]; exact h))
          omega
        let j' : Fin (r + 1) := ⟨j.val, hjlt⟩
        have hj_eq : j = j'.castSucc := Fin.ext rfl
        rw [hj_eq, Matrix.transpose_apply, hP_last_top j', mul_zero, zero_mul]
      · intro h; exact absurd (mem_univ _) h
    rw [hP_det] at hdet_exp
    exact (mul_eq_zero.mp hdet_exp.symm).resolve_right hMr_det
  -- All rows i ∈ Fin (r + 2) satisfy the linear relation
  have hrel_all : ∀ i : Fin (r + 2),
      ∑ j : Fin (r + 1), D.iter i.val (m ⟨j.val, by omega⟩) * a j = D.iter i.val (m ⟨r + 1, by omega⟩) := by
    intro i
    by_cases h : i = Fin.last (r + 1)
    · subst h
      have h1 := hP_last_col (Fin.last (r + 1))
      change Δ = _ at h1
      rw [hΔ_eq0] at h1
      exact (sub_eq_zero.mp h1.symm).symm
    · have hilt : i.val < r + 1 := by
        have := i.isLt
        have : i.val ≠ r + 1 := fun he => h (Fin.ext (by rw [Fin.val_last]; exact he))
        omega
      have hi := congrFun hMa ⟨i.val, hilt⟩
      simpa [Matrix.mulVec, dotProduct, Mr, wronskianSub, v] using hi
  -- Differentiate row i and subtract row i + 1 to show D (a j) = 0 for all j
  have hDa_zero : ∀ j : Fin (r + 1), D (a j) = 0 := by
    have hmv : Mr.mulVec (fun j => D (a j)) = 0 := by
      ext i
      simp only [Matrix.mulVec, dotProduct, Mr, wronskianSub, Pi.zero_apply]
      have hi0 := congrArg D (hrel_all i.castSucc)
      have hi1 := hrel_all i.succ
      rw [D.map_sum] at hi0
      have hsumD : ∑ j : Fin (r + 1), D (D.iter i.val (m ⟨j.val, by omega⟩) * a j) =
          (∑ j : Fin (r + 1), D.iter (i.val + 1) (m ⟨j.val, by omega⟩) * a j) +
          (∑ j : Fin (r + 1), D.iter i.val (m ⟨j.val, by omega⟩) * D (a j)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [D.map_mul']; rfl
      simp only [Fin.val_castSucc] at hi0
      simp only [Fin.val_succ] at hi1
      change ∑ j : Fin (r + 1), D (D.iter i.val (m ⟨j.val, by omega⟩) * a j) =
        D.iter (i.val + 1) (m ⟨r + 1, by omega⟩) at hi0
      rw [hsumD, hi1] at hi0
      linear_combination hi0
    have hinv := congrArg (Mr⁻¹.mulVec) hmv
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Mr hMr_unit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hinv
    exact fun j => congrFun hinv j
  let c : Fin (r + 2) → L := fun j =>
    if h : j.val < r + 1 then a ⟨j.val, h⟩ else -1
  refine ⟨r, hr4, c, ?_, ?_, ?_⟩
  · simp [c]
  · intro j
    by_cases h : j.val < r + 1
    · simp only [c, h, ↓reduceDIte]; exact hDa_zero ⟨j.val, h⟩
    · simp only [c, h, ↓reduceDIte, D.map_neg, D.map_one, neg_zero]
  · rw [Fin.sum_univ_castSucc]
    have h0 := hrel_all 0
    simp only [Fin.val_zero, RingDeriv.iter] at h0
    have hsum : ∑ j : Fin (r + 1), c j.castSucc * m ⟨j.castSucc.val, by omega⟩ =
        ∑ j : Fin (r + 1), m ⟨j.val, by omega⟩ * a j := by
      apply Finset.sum_congr rfl
      intro j _
      have hjlt : j.castSucc.val < r + 1 := j.isLt
      simp only [c, ↓reduceDIte, Fin.val_castSucc, j.isLt, Fin.eta]
      rw [mul_comm]
    rw [hsum, h0]
    have hlast : c (Fin.last (r + 1)) = -1 := by simp [c, Fin.val_last]
    rw [hlast]
    change m ⟨r + 1, by omega⟩ + -1 * m ⟨r + 1, by omega⟩ = 0
    ring

-- PowerSeries helpers in char p: clearing denominators by X^(p*N) and stripping X^m₀
lemma exists_X_pow_mul_unit_of_ne_zero {K : Type*} [Field K] {s : PowerSeries K} (hs : s ≠ 0) :
    ∃ (r : ℕ) (u : PowerSeries K), IsUnit u ∧ s = PowerSeries.X ^ r * u := by
  classical
  have hex : ∃ k : ℕ, PowerSeries.coeff k s ≠ 0 := by
    by_contra h
    apply hs; ext k; rw [map_zero]; exact not_not.mp (fun hk => h ⟨k, hk⟩)
  let r := Nat.find hex
  have hr_spec : PowerSeries.coeff r s ≠ 0 := Nat.find_spec hex
  have hr_dvd : PowerSeries.X ^ r ∣ s := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm; exact not_not.mp (Nat.find_min hex hm)
  rcases hr_dvd with ⟨u, hu⟩
  refine ⟨r, u, ?_, hu⟩
  rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hc : PowerSeries.coeff r s = PowerSeries.coeff 0 u := by
    have h0 := PowerSeries.coeff_X_pow_mul u r 0
    rw [zero_add] at h0
    rw [hu, h0]
  rwa [← hc]

lemma exists_X_pow_p_mul_mem_powerSeries {K : Type*} [Field K] (p : ℕ) (hp : 1 ≤ p)
    (c : FractionRing (PowerSeries K)) :
    ∃ (N : ℕ) (d : PowerSeries K),
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.X ^ (p * N)) * c =
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) d := by
  let ιS := algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.mk'_surjective (nonZeroDivisors (PowerSeries K)) c
  have hb0 : b.val ≠ 0 := nonZeroDivisors.ne_zero b.property
  obtain ⟨r, u, hu, hb_eq⟩ := exists_X_pow_mul_unit_of_ne_zero hb0
  rcases hu with ⟨u_unit, rfl⟩
  let uinv : PowerSeries K := ((u_unit⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)
  refine ⟨r, PowerSeries.X ^ (p * r - r) * a * uinv, ?_⟩
  have hcb : ιS b.val * c = ιS a := by
    rw [← hc, IsLocalization.mk'_spec']
  have hb_ne : ιS b.val ≠ 0 := by
    intro h0; exact hb0 (IsFractionRing.injective (PowerSeries K) _ (h0.trans (map_zero ιS).symm))
  apply mul_left_cancel₀ hb_ne
  calc ιS b.val * (ιS (PowerSeries.X ^ (p * r)) * c)
      = ιS (PowerSeries.X ^ (p * r)) * (ιS b.val * c) := by ring
    _ = ιS (PowerSeries.X ^ (p * r) * a) := by rw [hcb, map_mul]
    _ = ιS (b.val * (PowerSeries.X ^ (p * r - r) * a * uinv)) := by
        congr 1
        rw [hb_eq]
        have hpow : PowerSeries.X ^ r * PowerSeries.X ^ (p * r - r) =
            (PowerSeries.X : PowerSeries K) ^ (p * r) := by
          rw [← pow_add]; congr 1
          have : r ≤ p * r := Nat.le_mul_of_pos_left r (by omega)
          omega
        have hu_mul : (u_unit : PowerSeries K) * uinv = 1 := Units.mul_inv u_unit
        calc PowerSeries.X ^ (p * r) * a
            = (PowerSeries.X ^ r * PowerSeries.X ^ (p * r - r)) * a * ((u_unit : PowerSeries K) * uinv) := by
                rw [hpow, hu_mul, mul_one]
          _ = PowerSeries.X ^ r * (u_unit : PowerSeries K) * (PowerSeries.X ^ (p * r - r) * a * uinv) := by
                ring
    _ = ιS b.val * ιS (PowerSeries.X ^ (p * r - r) * a * uinv) := map_mul _ _ _

lemma powerSeries_deriv_X_pow_mul_p {K : Type*} [Field K] (p : ℕ) [CharP K p] (k : ℕ) :
    PowerSeries.derivative K ((PowerSeries.X : PowerSeries K) ^ (p * k)) = 0 := by
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one]
  have h0 : ((p * k : ℕ) : PowerSeries K) = 0 := by
    rw [← map_natCast PowerSeries.C (p * k), Nat.cast_mul, CharP.cast_eq_zero K p, zero_mul, map_zero]
  rw [h0, zero_mul]

lemma powerSeries_X_pow_p_dvd_sub_C_of_deriv_zero {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] {e : PowerSeries K} (he : PowerSeries.derivative K e = 0) :
    PowerSeries.X ^ p ∣ e - PowerSeries.C (PowerSeries.constantCoeff e) := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, PowerSeries.coeff_C]
  by_cases hm0 : m = 0
  · subst hm0; simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp only [hm0, ↓reduceIte, sub_zero]
    have hd := congrArg (PowerSeries.coeff (m - 1)) he
    rw [PowerSeries.coeff_derivative, map_zero] at hd
    have h1 : m - 1 + 1 = m := by omega
    rw [h1] at hd
    have hcast : ((m - 1 : ℕ) : K) + 1 = (m : K) := by
      rw [← Nat.cast_succ, Nat.succ_eq_add_one, show m - 1 + 1 = m by omega]
    rw [hcast] at hd
    have hm_ne : (m : K) ≠ 0 := by
      intro h0
      have hdvd := (CharP.cast_eq_zero_iff K p m).mp h0
      have hle := Nat.le_of_dvd (by omega) hdvd
      omega
    exact (mul_eq_zero.mp hd).resolve_right hm_ne

-- Main theorem of Section 5: ¬ (F.map ι ∣ H.map ι)
lemma not_F_dvd_H {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F H : MvPolynomial (Fin 3) (ZMod p)}
    (hFh : F.IsHomogeneous n)
    (hFirrK : Irreducible (F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))))
    (he0 : eval ![1, 0, 0] F ≠ 0) (he1 : eval ![0, 1, 0] F ≠ 0)
    (hHZ : F ∣ W10Z p n F - X 2 ^ 6 * H) :
    ¬ (F.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) ∣
        H.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) := by
  classical
  let K := AlgebraicClosure (ZMod p)
  let ι := algebraMap (ZMod p) K
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hCharK : CharP K p := charP_of_injective_ringHom hι_inj p
  have h2np_lt : 2 * n < p := by
    by_contra hge
    have heq : 2 * n = p := by omega
    have h2dvd : 2 ∣ p := ⟨n, heq.symm⟩
    have hprime := (Fact.out : p.Prime)
    rcases hprime.eq_one_or_self_of_dvd 2 h2dvd with h | h
    · omega
    · exact hp2 h.symm
  have h2K : (2 : K) ≠ 0 := by
    have h2p : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hdvd := (ZMod.natCast_eq_zero_iff 2 p).mp h0
      have hle := Nat.le_of_dvd (by omega) hdvd
      have hpge := (Fact.out : p.Prime).two_le
      omega
    have h1 : (2 : K) = ι (2 : ZMod p) := (map_ofNat ι 2).symm
    rw [h1]; exact fun h => h2p (hι_inj (h.trans (map_zero ι).symm))
  let FK := F.map ι
  let fK := dehomogZ FK
  have hFK_h : FK.IsHomogeneous n := hFh.map ι
  have he0K : eval ![1, 0, 0] FK ≠ 0 := by
    have hv : (ι ∘ ![1, 0, 0] : Fin 3 → K) = ![1, 0, 0] := by
      ext i; match i with | 0 => simp | 1 => simp | 2 => simp
    rw [← hv, eval_map_eq_map_eval]
    exact fun h => he0 (hι_inj (h.trans (map_zero ι).symm))
  have he1K : eval ![0, 1, 0] FK ≠ 0 := by
    have hv : (ι ∘ ![0, 1, 0] : Fin 3 → K) = ![0, 1, 0] := by
      ext i; match i with | 0 => simp | 1 => simp | 2 => simp
    rw [← hv, eval_map_eq_map_eval]
    exact fun h => he1 (hι_inj (h.trans (map_zero ι).symm))
  have hX2_ndvd : ¬ (X (2 : Fin 3) ∣ FK) := by
    rintro ⟨Q, hQ⟩; apply he0K; rw [hQ, map_mul, eval_X]; simp
  have hfK_irr : Irreducible fK := irreducible_dehomogZ hFK_h hFirrK hX2_ndvd
  have hfK_td : fK.totalDegree ≤ n := dehomogZ_totalDegree_le hFK_h
  have hpf_lc : (mv2ToPolyY K fK).coeff n = Polynomial.C (eval ![0, 1, 0] FK) :=
    mv2ToPolyY_coeff_top_homog hFK_h
  have hpf_nd : (mv2ToPolyY K fK).natDegree = n := by
    have hle := (mv2ToPolyY_degree_bounds hfK_td).1
    have hge : n ≤ (mv2ToPolyY K fK).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (by rw [hpf_lc]; exact Polynomial.C_ne_zero.mpr he1K)
    omega
  -- Step 1: Smooth point (a, b) ∈ K² and Hensel series y_ser ∈ PowerSeries K
  obtain ⟨a, b, hab0, hab_y⟩ := exists_smooth_point_over_K hn3 h2np hFh hFirrK he0 he1
  let tr : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
    MvPolynomial.eval₂Hom C ![C a + X 0, C b + X 1]
  have htr_eval : ∀ q : MvPolynomial (Fin 2) K, eval ![0, 0] (tr q) = eval ![a, b] q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [tr]
    | add u v hu hv => simp [map_add, hu, hv]
    | mul_X u i hu =>
      rw [map_mul, map_mul, map_mul, hu]
      match i with | 0 => simp [tr] | 1 => simp [tr]
  have htr_pderiv1 : ∀ q : MvPolynomial (Fin 2) K, MvPolynomial.pderiv 1 (tr q) = tr (MvPolynomial.pderiv 1 q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [tr]
    | add u v hu hv => simp [map_add, hu, hv]
    | mul_X u i hu =>
      rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, hu]
      match i with
      | 0 => simp [tr, MvPolynomial.pderiv_X]
      | 1 => simp [tr, MvPolynomial.pderiv_X]
  obtain ⟨y_ser, hy_const, hy_root⟩ := exists_hensel_series (tr fK)
    (by rw [htr_eval]; exact hab0)
    (by rw [htr_pderiv1, htr_eval]; exact hab_y)
  let φS : MvPolynomial (Fin 2) K →+* PowerSeries K :=
    MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.C a + PowerSeries.X, PowerSeries.C b + y_ser]
  have hφS_tr : ∀ q : MvPolynomial (Fin 2) K,
      MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, y_ser] (tr q) = φS q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [tr, φS]
    | add u v hu hv => simp [map_add, hu, hv]
    | mul_X u i hu =>
      rw [map_mul, map_mul, map_mul, hu]
      match i with | 0 => simp [tr, φS] | 1 => simp [tr, φS]
  have hφS_fK : φS fK = 0 := by rw [← hφS_tr]; exact hy_root
  have hφS_const : ∀ q : MvPolynomial (Fin 2) K, PowerSeries.constantCoeff (φS q) = eval ![a, b] q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r => simp [φS]
    | add u v hu hv => simp [map_add, hu, hv]
    | mul_X u i hu =>
      rw [map_mul, map_mul, map_mul, hu]
      match i with
      | 0 => simp [φS]
      | 1 => simp [φS, hy_const]
  have hφS_fy_ne : φS (MvPolynomial.pderiv 1 fK) ≠ 0 := by
    intro h0
    have := congrArg PowerSeries.constantCoeff h0
    rw [hφS_const, map_zero] at this
    exact hab_y this
  -- Step 2: Work in LS := FractionRing (PowerSeries K) with D_LS
  let S := PowerSeries K
  let LS := FractionRing S
  let ιS := algebraMap S LS
  have hιS_inj : Function.Injective ιS := IsFractionRing.injective S LS
  have hCharS : CharP S p := charP_of_injective_ringHom PowerSeries.C_injective p
  have hCharLS : CharP LS p := charP_of_injective_ringHom hιS_inj p
  let DS : RingDeriv S := powerSeriesDeriv K
  let DLS : RingDeriv LS := DS.toFractionRing
  let φLS : MvPolynomial (Fin 2) K →+* LS := ιS.comp φS
  have hφLS_fy_ne : φLS (MvPolynomial.pderiv 1 fK) ≠ 0 := by
    intro h0; exact hφS_fy_ne (hιS_inj (h0.trans (map_zero ιS).symm))
  have hDx_s1 : PowerSeries.derivative K (PowerSeries.C a + PowerSeries.X) = 1 := by
    rw [map_add, PowerSeries.derivative_C, PowerSeries.derivative_X, zero_add]
  have hφS0 : φS (X 0) = PowerSeries.C a + PowerSeries.X := by simp [φS]
  have hφS1 : φS (X 1) = PowerSeries.C b + y_ser := by simp [φS]
  have hDLS_X0 : DLS (φLS (X 0)) = 1 := by
    dsimp only [φLS, RingHom.comp_apply, DLS]
    rw [RingDeriv.toFractionRing_algebraMap, hφS0]
    change ιS (PowerSeries.derivative K (PowerSeries.C a + PowerSeries.X)) = 1
    rw [hDx_s1, map_one]
  have hDLS_X1 : DLS (φLS (X 1)) = -φLS (MvPolynomial.pderiv 0 fK) / φLS (MvPolynomial.pderiv 1 fK) := by
    have hch := congrArg ιS (powerSeries_chain_rule (PowerSeries.C a + PowerSeries.X) (PowerSeries.C b + y_ser) fK)
    change ιS (PowerSeries.derivative K (φS fK)) = _ at hch
    rw [hφS_fK, map_zero, map_zero, map_add, map_mul, map_mul, hDx_s1, map_one, mul_one] at hch
    have hdy_eq : ιS (PowerSeries.derivative K (PowerSeries.C b + y_ser)) = DLS (φLS (X 1)) := by
      dsimp only [φLS, RingHom.comp_apply, DLS]
      rw [RingDeriv.toFractionRing_algebraMap, hφS1]; rfl
    rw [hdy_eq] at hch
    rw [eq_div_iff hφLS_fy_ne]
    linear_combination hch.symm
  have hDLS_φ : ∀ g : MvPolynomial (Fin 2) K,
      DLS (φLS g) = φLS (Dt2 fK g) / φLS (MvPolynomial.pderiv 1 fK) := by
    intro g
    have hch := congrArg ιS (powerSeries_chain_rule (PowerSeries.C a + PowerSeries.X) (PowerSeries.C b + y_ser) g)
    have hlhs : DLS (φLS g) = ιS (PowerSeries.derivative K (φS g)) := by
      dsimp only [φLS, RingHom.comp_apply, DLS]
      rw [RingDeriv.toFractionRing_algebraMap]; rfl
    rw [hlhs, hch, map_add, map_mul, map_mul, hDx_s1, map_one, mul_one]
    have hdy_eq : ιS (PowerSeries.derivative K (PowerSeries.C b + y_ser)) = DLS (φLS (X 1)) := by
      dsimp only [φLS, RingHom.comp_apply, DLS]
      rw [RingDeriv.toFractionRing_algebraMap, hφS1]; rfl
    rw [hdy_eq, hDLS_X1]
    change φLS (MvPolynomial.pderiv 0 g) + φLS (MvPolynomial.pderiv 1 g) *
        (-φLS (MvPolynomial.pderiv 0 fK) / φLS (MvPolynomial.pderiv 1 fK)) =
      φLS (Dt2 fK g) / φLS (MvPolynomial.pderiv 1 fK)
    have hDt : φLS (Dt2 fK g) =
        φLS (MvPolynomial.pderiv 1 fK) * φLS (MvPolynomial.pderiv 0 g) -
        φLS (MvPolynomial.pderiv 0 fK) * φLS (MvPolynomial.pderiv 1 g) := by
      unfold Dt2; simp only [map_sub, map_mul]
    rw [hDt, eq_div_iff hφLS_fy_ne]
    have hm : (-φLS (MvPolynomial.pderiv 0 fK) / φLS (MvPolynomial.pderiv 1 fK)) *
        φLS (MvPolynomial.pderiv 1 fK) = -φLS (MvPolynomial.pderiv 0 fK) :=
      div_mul_cancel₀ _ hφLS_fy_ne
    linear_combination φLS (MvPolynomial.pderiv 1 g) * hm
  -- Step 3: Prove det(w0Matrix DLS mLS) ≠ 0
  let monom2 : Fin 6 → MvPolynomial (Fin 2) K := ![1, X 0, X 1, X 0 ^ 2, X 0 * X 1, X 1 ^ 2]
  let mS : Fin 6 → S := fun j => φS (monom2 j)
  let mLS : Fin 6 → LS := fun j => ιS (mS j)
  have hmLS_eq : mLS = ![1, φLS (X 0), φLS (X 1), φLS (X 0) ^ 2, φLS (X 0) * φLS (X 1), φLS (X 1) ^ 2] := by
    ext j; match j with
    | 0 => simp [mLS, mS, monom2]
    | 1 => simp [mLS, mS, monom2, φLS]
    | 2 => simp [mLS, mS, monom2, φLS]
    | 3 => simp [mLS, mS, monom2, φLS]
    | 4 => simp [mLS, mS, monom2, φLS]
    | 5 => simp [mLS, mS, monom2, φLS]
  have hw0_ne : (w0Matrix DLS mLS).det ≠ 0 := by
    intro hw0
    obtain ⟨r, hr4, c, hc_last, hDc, hsum_c⟩ :=
      exists_const_rel_of_w0_det_eq_zero DLS mLS (by rw [hmLS_eq]; rfl) hw0
    -- Clear denominators of c j using X^(p*N)
    have hclear : ∀ j : Fin (r + 2), ∃ (N : ℕ) (d : S), ιS (PowerSeries.X ^ (p * N)) * c j = ιS d :=
      fun j => exists_X_pow_p_mul_mem_powerSeries p (by omega) (c j)
    choose N_fn d_fn hd_fn using hclear
    let Nmax := Finset.univ.sup N_fn
    let e : Fin (r + 2) → S := fun j => PowerSeries.X ^ (p * (Nmax - N_fn j)) * d_fn j
    have he_eq : ∀ j : Fin (r + 2), ιS (e j) = ιS (PowerSeries.X ^ (p * Nmax)) * c j := by
      intro j
      have hle : N_fn j ≤ Nmax := Finset.le_sup (f := N_fn) (mem_univ j)
      have hpow : p * (Nmax - N_fn j) + p * N_fn j = p * Nmax := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hle]
      dsimp only [e]
      rw [map_mul, ← hd_fn j, ← mul_assoc, ← map_mul, ← pow_add, hpow]
    have he_last_ne : e (Fin.last (r + 1)) ≠ 0 := by
      intro h0
      have h1 := he_eq (Fin.last (r + 1))
      rw [h0, map_zero, hc_last, mul_neg, mul_one, eq_comm, neg_eq_zero] at h1
      have hX0 : (PowerSeries.X : S) ^ (p * Nmax) = 0 :=
        hιS_inj (h1.trans (map_zero ιS).symm)
      have hX1 : PowerSeries.coeff (p * Nmax) ((PowerSeries.X : S) ^ (p * Nmax)) = 1 :=
        PowerSeries.coeff_X_pow_self (p * Nmax)
      rw [hX0, map_zero] at hX1; exact zero_ne_one hX1
    have hDe : ∀ j : Fin (r + 2), PowerSeries.derivative K (e j) = 0 := by
      intro j
      apply hιS_inj
      rw [map_zero]
      change ιS (DS (e j)) = 0
      rw [← RingDeriv.toFractionRing_algebraMap DS (e j)]
      change DLS (ιS (e j)) = 0
      rw [he_eq j, DLS.map_mul', hDc j, mul_zero, add_zero]
      have hDX : DLS (ιS (PowerSeries.X ^ (p * Nmax))) = 0 := by
        dsimp only [DLS]; rw [RingDeriv.toFractionRing_algebraMap]
        change ιS (PowerSeries.derivative K (PowerSeries.X ^ (p * Nmax))) = 0
        rw [powerSeries_deriv_X_pow_mul_p p Nmax, map_zero]
      rw [hDX, zero_mul]
    have hsum_e : ∑ j : Fin (r + 2), e j * mS ⟨j.val, by omega⟩ = 0 := by
      apply hιS_inj
      rw [map_zero, map_sum]
      have h1 : ∑ j : Fin (r + 2), ιS (e j * mS ⟨j.val, by omega⟩) =
          ιS (PowerSeries.X ^ (p * Nmax)) * ∑ j : Fin (r + 2), c j * mLS ⟨j.val, by omega⟩ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul, he_eq j]; dsimp only [mLS]; ring
      rw [h1, hsum_c, mul_zero]
    -- Strip common X^m₀ factor where m₀ is minimum exponent across all e j
    have hex_m : ∃ m : ℕ, ∃ j : Fin (r + 2), PowerSeries.coeff m (e j) ≠ 0 := by
      by_contra h
      apply he_last_ne; ext m; rw [map_zero]
      exact not_not.mp (fun hm => h ⟨m, Fin.last (r + 1), hm⟩)
    let m₀ := Nat.find hex_m
    obtain ⟨j₀, hj₀⟩ := Nat.find_spec hex_m
    have hp_dvd_m0 : p ∣ m₀ := by
      by_cases hm0 : m₀ = 0
      · rw [hm0]; exact dvd_zero p
      · have hd := congrArg (PowerSeries.coeff (m₀ - 1)) (hDe j₀)
        rw [PowerSeries.coeff_derivative, map_zero] at hd
        have h1 : m₀ - 1 + 1 = m₀ := by omega
        rw [h1] at hd
        have hcast : ((m₀ - 1 : ℕ) : K) + 1 = (m₀ : K) := by
          rw [← Nat.cast_succ, Nat.succ_eq_add_one, show m₀ - 1 + 1 = m₀ by omega]
        rw [hcast] at hd
        exact (CharP.cast_eq_zero_iff K p m₀).mp ((mul_eq_zero.mp hd).resolve_left hj₀)
    have he_dvd : ∀ j : Fin (r + 2), PowerSeries.X ^ m₀ ∣ e j := by
      intro j
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      by_contra hne
      exact Nat.find_min hex_m hm ⟨j, hne⟩
    choose e' he' using he_dvd
    have he'_const_ne : PowerSeries.constantCoeff (e' j₀) ≠ 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      have hc : PowerSeries.coeff m₀ (e j₀) = PowerSeries.coeff 0 (e' j₀) := by
        have h0 := PowerSeries.coeff_X_pow_mul (e' j₀) m₀ 0
        rw [zero_add] at h0
        rw [he' j₀, h0]
      rwa [← hc]
    have hDe' : ∀ j : Fin (r + 2), PowerSeries.derivative K (e' j) = 0 := by
      intro j
      rcases hp_dvd_m0 with ⟨q, hq⟩
      have h1 := hDe j
      rw [he' j, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hq,
        powerSeries_deriv_X_pow_mul_p p q, mul_zero, add_zero] at h1
      have h2 : PowerSeries.X ^ (p * q) * PowerSeries.derivative K (e' j) =
          PowerSeries.X ^ (p * q) * 0 := by rw [mul_zero]; exact h1
      exact PowerSeries.X_pow_mul_cancel h2
    have hsum_e' : ∑ j : Fin (r + 2), e' j * mS ⟨j.val, by omega⟩ = 0 := by
      have h1 : PowerSeries.X ^ m₀ * ∑ j : Fin (r + 2), e' j * mS ⟨j.val, by omega⟩ =
          PowerSeries.X ^ m₀ * 0 := by
        rw [mul_zero, Finset.mul_sum]
        calc ∑ j : Fin (r + 2), PowerSeries.X ^ m₀ * (e' j * mS ⟨j.val, by omega⟩)
            = ∑ j : Fin (r + 2), e j * mS ⟨j.val, by omega⟩ := by
                apply Finset.sum_congr rfl; intro j _; rw [he' j, mul_assoc]
          _ = 0 := hsum_e
      exact PowerSeries.X_pow_mul_cancel h1
    -- Extract nonzero conic Q of totalDegree ≤ 2 with X^p ∣ φS Q
    let Q : MvPolynomial (Fin 2) K :=
      ∑ j : Fin (r + 2), C (PowerSeries.constantCoeff (e' j)) * monom2 ⟨j.val, by omega⟩
    have hQ_ne : Q ≠ 0 := by
      let exp6 : Fin 6 → (Fin 2 →₀ ℕ) :=
        ![0, Finsupp.single 0 1, Finsupp.single 1 1, Finsupp.single 0 2,
          Finsupp.single 0 1 + Finsupp.single 1 1, Finsupp.single 1 2]
      have hmon_eq : ∀ idx : Fin 6, monom2 idx = monomial (exp6 idx) (1 : K) := by
        intro idx
        match idx with
        | 0 => simp [monom2, exp6]
        | 1 => simp [monom2, exp6, MvPolynomial.X]
        | 2 => simp [monom2, exp6, MvPolynomial.X]
        | 3 => simp [monom2, exp6, MvPolynomial.X, MvPolynomial.monomial_pow]
        | 4 => simp [monom2, exp6, MvPolynomial.X, MvPolynomial.monomial_mul]
        | 5 => simp [monom2, exp6, MvPolynomial.X, MvPolynomial.monomial_pow]
      have hexp_inj : Function.Injective exp6 := by
        intro i j hij
        have h0 : exp6 i 0 = exp6 j 0 := congrFun (congrArg DFunLike.coe hij) 0
        have h1 : exp6 i 1 = exp6 j 1 := congrFun (congrArg DFunLike.coe hij) 1
        fin_cases i <;> fin_cases j <;> simp [exp6] at h0 h1 ⊢
      intro hQ0
      have hc := congrArg (fun P => P.coeff (exp6 ⟨j₀.val, by omega⟩)) hQ0
      rw [MvPolynomial.coeff_zero] at hc
      dsimp only [Q] at hc
      rw [MvPolynomial.coeff_sum] at hc
      rw [Finset.sum_eq_single j₀] at hc
      · rw [hmon_eq, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial] at hc
        simp only [↓reduceIte] at hc
        exact he'_const_ne hc
      · intro j _ hne
        rw [hmon_eq, MvPolynomial.C_mul_monomial, mul_one, MvPolynomial.coeff_monomial]
        have hne_exp : exp6 ⟨j.val, by omega⟩ ≠ exp6 ⟨j₀.val, by omega⟩ := fun h => by
          have hfin : (⟨j.val, by omega⟩ : Fin 6) = ⟨j₀.val, by omega⟩ := hexp_inj h
          exact hne (Fin.ext (congrArg (fun x : Fin 6 => x.val) hfin))
        simp [hne_exp]
      · intro h; exact absurd (mem_univ j₀) h
    have hQ_td : Q.totalDegree ≤ 2 := by
      refine (MvPolynomial.totalDegree_finsetSum _ _).trans ?_
      apply Finset.sup_le
      intro j _
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      have htd6 : ∀ idx : Fin 6, (monom2 idx).totalDegree ≤ 2 := by
        intro idx; match idx with
        | 0 => simp [monom2]
        | 1 => simp [monom2]
        | 2 => simp [monom2]
        | 3 =>
          calc (X (0 : Fin 2) ^ 2 : MvPolynomial (Fin 2) K).totalDegree
              ≤ 2 * (X (0 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree := MvPolynomial.totalDegree_pow _ _
            _ ≤ 2 := by simp
        | 4 =>
          calc (X (0 : Fin 2) * X 1 : MvPolynomial (Fin 2) K).totalDegree
              ≤ (X (0 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree +
                (X (1 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree := MvPolynomial.totalDegree_mul _ _
            _ ≤ 2 := by simp
        | 5 =>
          calc (X (1 : Fin 2) ^ 2 : MvPolynomial (Fin 2) K).totalDegree
              ≤ 2 * (X (1 : Fin 2) : MvPolynomial (Fin 2) K).totalDegree := MvPolynomial.totalDegree_pow _ _
            _ ≤ 2 := by simp
      exact htd6 ⟨j.val, by omega⟩
    have hXp_dvd_φQ : PowerSeries.X ^ p ∣ φS Q := by
      have hφQ : φS Q = ∑ j : Fin (r + 2),
          (PowerSeries.C (PowerSeries.constantCoeff (e' j)) - e' j) * mS ⟨j.val, by omega⟩ := by
        have h1 : φS Q = ∑ j : Fin (r + 2),
            PowerSeries.C (PowerSeries.constantCoeff (e' j)) * mS ⟨j.val, by omega⟩ := by
          dsimp only [Q, mS]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _; rw [map_mul, MvPolynomial.eval₂Hom_C]
        rw [h1, ← sub_zero (∑ j : Fin (r + 2), _), ← hsum_e', ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _; ring
      rw [hφQ]
      apply Finset.dvd_sum
      intro j _
      have hsub := powerSeries_X_pow_p_dvd_sub_C_of_deriv_zero p (hDe' j)
      have hneg : PowerSeries.X ^ p ∣ PowerSeries.C (PowerSeries.constantCoeff (e' j)) - e' j := by
        rw [← neg_sub]; exact dvd_neg.mpr hsub
      exact dvd_mul_of_dvd_left hneg _
    -- Resultant R_Q = Res_Y(fK, Q) has 0 < R_Q, natDegree ≤ 2n, yet X^p ∣ R_Q(a + X)!
    let RQ : Polynomial K := (mv2ToPolyY K fK).resultant (mv2ToPolyY K Q) n 2
    have hRQ_ne : RQ ≠ 0 :=
      resultant_ne_zero_of_irred_lt_deg hfK_irr hpf_nd he1K hpf_lc hQ_ne
        (mv2ToPolyY_degree_bounds hQ_td).1 (by omega)
    have hRQ_deg : RQ.natDegree ≤ 2 * n := by
      dsimp only [RQ]
      rw [mul_comm]
      exact natDegree_resultant_le (mv2ToPolyY_degree_bounds hfK_td).2
        (mv2ToPolyY_degree_bounds hQ_td).2
    let ψ : Polynomial K →+* S := Polynomial.eval₂RingHom PowerSeries.C (PowerSeries.C a + PowerSeries.X)
    have hψ_RQ : PowerSeries.X ^ p ∣ ψ RQ := by
      have hmap : ψ RQ = ((mv2ToPolyY K fK).map ψ).resultant ((mv2ToPolyY K Q).map ψ) n 2 :=
        (Polynomial.resultant_map_map _ _ _ _ ψ).symm
      rw [hmap]
      have hev_ψ : ∀ h : MvPolynomial (Fin 2) K,
          Polynomial.eval (PowerSeries.C b + y_ser) ((mv2ToPolyY K h).map ψ) = φS h := by
        intro h
        rw [eval_map_mv2ToPolyY]
        have h1 : ψ.comp Polynomial.C = PowerSeries.C := by ext r; simp [ψ]
        have h2 : ![ψ Polynomial.X, PowerSeries.C b + y_ser] =
            ![PowerSeries.C a + PowerSeries.X, PowerSeries.C b + y_ser] := by
          ext i; match i with | 0 => simp [ψ] | 1 => rfl
        rw [h1, h2]
      have hroot : Polynomial.IsRoot ((mv2ToPolyY K fK).map ψ) (PowerSeries.C b + y_ser) := by
        rw [Polynomial.IsRoot.def, hev_ψ]; exact hφS_fK
      obtain ⟨g', hg'⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
      have hmf_nd : ((mv2ToPolyY K fK).map ψ).natDegree = n := by
        have hle : ((mv2ToPolyY K fK).map ψ).natDegree ≤ n :=
          Polynomial.natDegree_map_le.trans (by omega)
        have hge : n ≤ ((mv2ToPolyY K fK).map ψ).natDegree := Polynomial.le_natDegree_of_ne_zero (by
          rw [Polynomial.coeff_map, hpf_lc]
          have h1 : ψ (Polynomial.C (eval ![0, 1, 0] FK)) = PowerSeries.C (eval ![0, 1, 0] FK) := by
            simp [ψ]
          rw [h1]; exact fun h0 => he1K (PowerSeries.C_injective (h0.trans (map_zero PowerSeries.C).symm)))
        omega
      have hmf_ne : (mv2ToPolyY K fK).map ψ ≠ 0 := by
        intro h0; rw [h0, Polynomial.natDegree_zero] at hmf_nd; omega
      have hg'_ne : g' ≠ 0 := by rintro rfl; rw [mul_zero] at hg'; exact hmf_ne hg'
      have hlin_mon : (Polynomial.X - Polynomial.C (PowerSeries.C b + y_ser)).Monic :=
        Polynomial.monic_X_sub_C _
      have hg'_nd : g'.natDegree = n - 1 := by
        have h1 := congrArg Polynomial.natDegree hg'
        rw [hmf_nd, hlin_mon.natDegree_mul' hg'_ne, Polynomial.natDegree_X_sub_C] at h1
        omega
      have hn_sum : (Polynomial.X - Polynomial.C (PowerSeries.C b + y_ser)).natDegree + g'.natDegree = n := by
        rw [Polynomial.natDegree_X_sub_C, hg'_nd]; omega
      have hQ_nd : ((mv2ToPolyY K Q).map ψ).natDegree ≤ 2 :=
        Polynomial.natDegree_map_le.trans (mv2ToPolyY_degree_bounds hQ_td).1
      rw [hg', ← hn_sum, Polynomial.resultant_mul_left _ _ _ 2 hQ_nd,
        Polynomial.natDegree_X_sub_C, Polynomial.resultant_X_sub_C_left _ 2 _ hQ_nd, hev_ψ Q]
      exact dvd_mul_of_dvd_left hXp_dvd_φQ _
    -- Translate R_Q to R_Q(X + a) ∈ K[X] to deduce p ≤ R_Q.natDegree ≤ 2n
    let Rshift : Polynomial K := RQ.comp (Polynomial.X + Polynomial.C a)
    have hψ_eq_coe : ψ RQ = (Rshift : PowerSeries K) := by
      have h1 : ∀ P : Polynomial K, ψ P = ((P.comp (Polynomial.X + Polynomial.C a) : Polynomial K) : PowerSeries K) := by
        intro P
        induction P using Polynomial.induction_on' with
        | add u v hu hv => rw [map_add, Polynomial.add_comp, Polynomial.coe_add, hu, hv]
        | monomial k r =>
          rw [Polynomial.monomial_comp, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow,
            Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C]
          simp [ψ, add_comm]
      exact h1 RQ
    rw [hψ_eq_coe, PowerSeries.X_pow_dvd_iff] at hψ_RQ
    have hXp_poly : Polynomial.X ^ p ∣ Rshift := by
      rw [Polynomial.X_pow_dvd_iff]
      intro m hm
      have h1 := hψ_RQ m hm
      rwa [Polynomial.coeff_coe] at h1
    have hRshift_ne : Rshift ≠ 0 := by
      intro h0
      have hback := congrArg (fun P : Polynomial K => P.comp (Polynomial.X - Polynomial.C a)) h0
      rw [Polynomial.zero_comp, Polynomial.comp_assoc] at hback
      have hid : (Polynomial.X + Polynomial.C a).comp (Polynomial.X - Polynomial.C a) = Polynomial.X := by
        simp [Polynomial.add_comp]
      rw [hid, Polynomial.comp_X] at hback
      exact hRQ_ne hback
    have hRshift_deg : Rshift.natDegree = RQ.natDegree := by
      dsimp only [Rshift]
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    have hp_le := Polynomial.natDegree_le_of_dvd hXp_poly hRshift_ne
    rw [Polynomial.natDegree_X_pow, hRshift_deg] at hp_le
    omega
  -- Step 4: w0Matrix ≠ 0 ⟹ fwMatrix ≠ 0 ⟹ φLS (W10 p fK) ≠ 0 ⟹ ¬ (FK ∣ H.map ι)
  have hfw_ne : (fwMatrix p DLS mLS).det ≠ 0 :=
    det_fwMatrix_ne_zero_of_w0_ne_zero p DLS mLS (by rw [hmLS_eq]; rfl) hw0_ne
  rw [hmLS_eq, det_fwMatrix_eq_W10_of_deriv p φLS DLS fK hDLS_X0 hDLS_φ hφLS_fy_ne] at hfw_ne
  have hφ_W10_ne : φLS (W10 p fK) ≠ 0 := by
    intro h0; rw [h0, mul_zero, zero_div] at hfw_ne; exact hfw_ne rfl
  intro hFH_dvd
  have hW10Z_dvd : FK ∣ (W10Z p n F).map ι := by
    have hHZK : FK ∣ (W10Z p n F).map ι - X 2 ^ 6 * H.map ι := by
      rcases hHZ with ⟨Q, hQ⟩
      refine ⟨Q.map ι, ?_⟩
      have h1 := congrArg (MvPolynomial.map ι) hQ
      simpa [FK, map_sub, map_mul, map_pow] using h1
    have hX2H : FK ∣ X 2 ^ 6 * H.map ι := dvd_mul_of_dvd_right hFH_dvd _
    have hid : (W10Z p n F).map ι = ((W10Z p n F).map ι - X 2 ^ 6 * H.map ι) + X 2 ^ 6 * H.map ι := by ring
    rw [hid]; exact dvd_add hHZK hX2H
  have hfK_dvd_W10 : fK ∣ W10 p fK := by
    rcases hW10Z_dvd with ⟨Q, hQ⟩
    refine ⟨dehomogZ Q, ?_⟩
    have h1 := congrArg dehomogZ hQ
    rw [map_mul] at h1
    have h2 : dehomogZ ((W10Z p n F).map ι) = W10 p fK := by
      have hcomm : ∀ P : MvPolynomial (Fin 3) (ZMod p),
          dehomogZ (P.map ι) = (dehomogZ P).map ι := by
        intro P
        induction P using MvPolynomial.induction_on with
        | C r => simp [dehomogZ]
        | add u v hu hv => simp [map_add, hu, hv]
        | mul_X u i hu =>
          rw [map_mul, map_mul, map_mul, map_mul, hu]
          match i with | 0 => simp [dehomogZ] | 1 => simp [dehomogZ] | 2 => simp [dehomogZ]
      rw [hcomm, W10Z, dehomogZ_homogZ, ← W10_map, ← hcomm]
    rwa [h2] at h1
  rcases hfK_dvd_W10 with ⟨Q, hQ⟩
  apply hφ_W10_ne
  have h1 := congrArg φLS hQ
  rw [map_mul] at h1
  have hφLS_fK : φLS fK = 0 := by dsimp only [φLS]; rw [RingHom.comp_apply, hφS_fK, map_zero]
  rw [hφLS_fK, zero_mul] at h1
  exact h1

end NonDivisibility

-- ============================================================================
-- Section 6: Local Multiplicity ≥ 5, Sylvester Bezout Bound & Final Assembly
-- ============================================================================

section LocalMultAndBezout

-- 6.1 Basic projective linear algebra & 2-variable nonvanishing over IsAlgClosed K
def cross3 {K : Type*} [CommRing K] (u v : Fin 3 → K) : Fin 3 → K :=
  fun i => match i with
    | 0 => u 1 * v 2 - u 2 * v 1
    | 1 => u 2 * v 0 - u 0 * v 2
    | 2 => u 0 * v 1 - u 1 * v 0

def det3 {K : Type*} [CommRing K] (u v w : Fin 3 → K) : K :=
  cross3 u v 0 * w 0 + cross3 u v 1 * w 1 + cross3 u v 2 * w 2

abbrev IsNorm {K : Type*} [Zero K] [One K] (v : Fin 3 → K) : Prop :=
  v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨ (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)

lemma isNorm_ne_zero {K : Type*} [Field K] {v : Fin 3 → K} (hv : IsNorm v) : v ≠ 0 := by
  intro h
  rcases hv with h0 | ⟨_, h1⟩ | ⟨_, _, h2⟩
  · exact one_ne_zero (h0.symm.trans (congrFun h 0))
  · exact one_ne_zero (h1.symm.trans (congrFun h 1))
  · exact one_ne_zero (h2.symm.trans (congrFun h 2))

lemma isNorm_eq_of_smul {K : Type*} [Field K] {u v : Fin 3 → K}
    (hu : IsNorm u) (hv : IsNorm v) {c : K} (h : u = c • v) : u = v := by
  have hc : c = 1 := by
    have h0 : u 0 = c * v 0 := congrFun h 0
    have h1 : u 1 = c * v 1 := congrFun h 1
    have h2 : u 2 = c * v 2 := congrFun h 2
    rcases hu with hu0 | ⟨hu0, hu1⟩ | ⟨hu0, hu1, hu2⟩ <;>
    rcases hv with hv0 | ⟨hv0, hv1⟩ | ⟨hv0, hv1, hv2⟩
    · rw [hu0, hv0, mul_one] at h0; exact h0.symm
    · rw [hu0, hv0, mul_zero] at h0; exact absurd h0 one_ne_zero
    · rw [hu0, hv0, mul_zero] at h0; exact absurd h0 one_ne_zero
    · rw [hu0, hv0, mul_one] at h0; rw [← h0, zero_mul] at h1; rw [hu1] at h1; exact absurd h1 one_ne_zero
    · rw [hu1, hv1, mul_one] at h1; exact h1.symm
    · rw [hu1, hv1, mul_zero] at h1; exact absurd h1 one_ne_zero
    · rw [hu0, hv0, mul_one] at h0; rw [← h0, zero_mul] at h2; rw [hu2] at h2; exact absurd h2 one_ne_zero
    · rw [hu1, hv1, mul_one] at h1; rw [← h1, zero_mul] at h2; rw [hu2] at h2; exact absurd h2 one_ne_zero
    · rw [hu2, hv2, mul_one] at h2; exact h2.symm
  rw [h, hc, one_smul]

lemma cross3_ne_zero_of_isNorm_ne {K : Type*} [Field K] {u v : Fin 3 → K}
    (hu : IsNorm u) (hv : IsNorm v) (hne : u ≠ v) : cross3 u v ≠ 0 := by
  intro hc
  have h0 : u 1 * v 2 - u 2 * v 1 = 0 := congrFun hc 0
  have h1 : u 2 * v 0 - u 0 * v 2 = 0 := congrFun hc 1
  have h2 : u 0 * v 1 - u 1 * v 0 = 0 := congrFun hc 2
  have hex : ∃ c : K, v = c • u := by
    by_cases hu0 : u 0 ≠ 0
    · refine ⟨v 0 / u 0, ?_⟩
      ext i; match i with
      | 0 => change v 0 = v 0 / u 0 * u 0; rw [div_mul_cancel₀ _ hu0]
      | 1 => change v 1 = v 0 / u 0 * u 1; apply mul_left_cancel₀ hu0
             calc u 0 * v 1 = u 1 * v 0 := sub_eq_zero.mp h2
               _ = u 0 * (v 0 / u 0 * u 1) := by rw [← mul_assoc, mul_div_cancel₀ _ hu0]; ring
      | 2 => change v 2 = v 0 / u 0 * u 2; apply mul_left_cancel₀ hu0
             calc u 0 * v 2 = u 2 * v 0 := (sub_eq_zero.mp h1).symm
               _ = u 0 * (v 0 / u 0 * u 2) := by rw [← mul_assoc, mul_div_cancel₀ _ hu0]; ring
    · have hu0' : u 0 = 0 := not_not.mp hu0
      by_cases hu1 : u 1 ≠ 0
      · refine ⟨v 1 / u 1, ?_⟩
        ext i; match i with
        | 0 => change v 0 = v 1 / u 1 * u 0; rw [hu0', mul_zero]
               have : u 1 * v 0 = 0 := by rw [hu0', zero_mul, zero_sub, neg_eq_zero] at h2; exact h2
               exact (mul_eq_zero.mp this).resolve_left hu1
        | 1 => change v 1 = v 1 / u 1 * u 1; rw [div_mul_cancel₀ _ hu1]
        | 2 => change v 2 = v 1 / u 1 * u 2; apply mul_left_cancel₀ hu1
               calc u 1 * v 2 = u 2 * v 1 := sub_eq_zero.mp h0
                 _ = u 1 * (v 1 / u 1 * u 2) := by rw [← mul_assoc, mul_div_cancel₀ _ hu1]; ring
      · have hu1' : u 1 = 0 := not_not.mp hu1
        have hu2 : u 2 ≠ 0 := by
          intro hu2; exact isNorm_ne_zero hu (by ext i; match i with | 0 => exact hu0' | 1 => exact hu1' | 2 => exact hu2)
        refine ⟨v 2 / u 2, ?_⟩
        ext i; match i with
        | 0 => change v 0 = v 2 / u 2 * u 0; rw [hu0', mul_zero]
               have : u 2 * v 0 = 0 := by rw [hu0', zero_mul, sub_zero] at h1; exact h1
               exact (mul_eq_zero.mp this).resolve_left hu2
        | 1 => change v 1 = v 2 / u 2 * u 1; rw [hu1', mul_zero]
               have : u 2 * v 1 = 0 := by rw [hu1', zero_mul, zero_sub, neg_eq_zero] at h0; exact h0
               exact (mul_eq_zero.mp this).resolve_left hu2
        | 2 => change v 2 = v 2 / u 2 * u 2; rw [div_mul_cancel₀ _ hu2]
  obtain ⟨c, hvu⟩ := hex
  exact hne (isNorm_eq_of_smul hv hu hvu).symm

noncomputable def norm3 {K : Type*} [Field K] (v : Fin 3 → K) : Fin 3 → K := by
  classical
  exact if v 0 ≠ 0 then (v 0)⁻¹ • v
    else if v 1 ≠ 0 then (v 1)⁻¹ • v
    else (v 2)⁻¹ • v

lemma norm3_isNorm {K : Type*} [Field K] {v : Fin 3 → K} (hv : v ≠ 0) : IsNorm (norm3 v) := by
  classical
  unfold norm3 IsNorm
  split_ifs with h0 h1
  · left; simp [h0]
  · right; left; have h0' : v 0 = 0 := not_not.mp h0; simp [h0', h1]
  · right; right
    have h0' : v 0 = 0 := not_not.mp h0
    have h1' : v 1 = 0 := not_not.mp h1
    have h2 : v 2 ≠ 0 := by
      intro h2; exact hv (by ext i; match i with | 0 => exact h0' | 1 => exact h1' | 2 => exact h2)
    simp [h0', h1', h2]

lemma norm3_exists_smul {K : Type*} [Field K] {v : Fin 3 → K} (hv : v ≠ 0) :
    ∃ c : K, c ≠ 0 ∧ norm3 v = c • v := by
  classical
  unfold norm3
  split_ifs with h0 h1
  · exact ⟨(v 0)⁻¹, inv_ne_zero h0, rfl⟩
  · exact ⟨(v 1)⁻¹, inv_ne_zero h1, rfl⟩
  · have h0' : v 0 = 0 := not_not.mp h0
    have h1' : v 1 = 0 := not_not.mp h1
    have h2 : v 2 ≠ 0 := by
      intro h2; exact hv (by ext i; match i with | 0 => exact h0' | 1 => exact h1' | 2 => exact h2)
    exact ⟨(v 2)⁻¹, inv_ne_zero h2, rfl⟩

noncomputable def dehomog1 {K : Type*} [CommRing K] : MvPolynomial (Fin 2) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]

lemma dehomog1_monomial {K : Type*} [CommRing K] (m : Fin 2 →₀ ℕ) (a : K) :
    dehomog1 (monomial m a) = Polynomial.C a * Polynomial.X ^ (m 0) := by
  unfold dehomog1
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
  simp

lemma coeff_dehomog1_of_isHomogeneous {K : Type*} [CommRing K] {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) (k : ℕ) :
    (dehomog1 P).coeff k =
      if k ≤ d then P.coeff (Finsupp.single 0 k + Finsupp.single 1 (d - k)) else 0 := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  have hdeg : ∀ m ∈ P.support, m 0 + m 1 = d := by
    intro m hm; have h := isHomogeneous_sum_eq hP hm; rwa [Fin.sum_univ_two] at h
  split_ifs with hkd
  · let m₀ : Fin 2 →₀ ℕ := Finsupp.single 0 k + Finsupp.single 1 (d - k)
    have hm₀0 : m₀ 0 = k := by simp [m₀]
    have hm₀1 : m₀ 1 = d - k := by simp [m₀]
    by_cases hmem : m₀ ∈ P.support
    · rw [Finset.sum_eq_single m₀]
      · rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hm₀0]; simp [m₀]
      · intro m hm hne
        rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        split_ifs with h0
        · exfalso; apply hne
          ext i; match i with
          | 0 => exact h0.symm.trans hm₀0.symm
          | 1 => have hd := hdeg m hm; rw [hm₀1]; omega
        · rw [mul_zero]
      · intro h; exact absurd hmem h
    · rw [MvPolynomial.notMem_support_iff.mp hmem]
      apply Finset.sum_eq_zero
      intro m hm
      rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs with h0
      · exfalso; apply hmem
        have : m = m₀ := by
          ext i; match i with
          | 0 => exact h0.symm.trans hm₀0.symm
          | 1 => have hd := hdeg m hm; rw [hm₀1]; omega
        exact this ▸ hm
      · rw [mul_zero]
  · apply Finset.sum_eq_zero
    intro m hm
    rw [dehomog1_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have hd := hdeg m hm
    have hne : k ≠ m 0 := by omega
    simp [hne]

lemma dehomog1_ne_zero_of_isHomogeneous {K : Type*} [CommRing K] {P : MvPolynomial (Fin 2) K}
    {d : ℕ} (hP : P.IsHomogeneous d) (hP0 : P ≠ 0) : dehomog1 P ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr hP0
  have hd := isHomogeneous_sum_eq hP hm
  rw [Fin.sum_univ_two] at hd
  have hc := congrArg (fun q : Polynomial K => q.coeff (m 0)) h0
  rw [Polynomial.coeff_zero, coeff_dehomog1_of_isHomogeneous hP] at hc
  have hle : m 0 ≤ d := by omega
  simp only [hle, ↓reduceIte] at hc
  have hm_eq : Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single 1 (d - m 0) = m := by
    ext i; match i with
    | 0 => simp
    | 1 => simp; omega
  rw [hm_eq] at hc
  exact MvPolynomial.mem_support_iff.mp hm hc

lemma natDegree_dehomog1_le {K : Type*} [CommRing K] {P : MvPolynomial (Fin 2) K} {d : ℕ}
    (hP : P.IsHomogeneous d) : (dehomog1 P).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_dehomog1_of_isHomogeneous hP]
  have hnot : ¬ (k ≤ d) := by omega
  simp [hnot]

lemma exists_eval_ne_zero_mv2 {K : Type*} [Field K] [IsAlgClosed K]
    {G : MvPolynomial (Fin 2) K} (hG : G ≠ 0) :
    ∃ v : Fin 2 → K, eval v G ≠ 0 := by
  classical
  let g := mv2ToPolyY K G
  have hg0 : g ≠ 0 := fun h => hG ((mv2EquivPolyY K).injective (h.trans (map_zero _).symm))
  have hlc0 : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
  obtain ⟨a, ha⟩ := exists_notMem_of_isAlgClosed g.leadingCoeff.roots.toFinset
  have ha_ne : Polynomial.eval a g.leadingCoeff ≠ 0 := by
    intro h0; apply ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hlc0, Polynomial.IsRoot.def]; exact h0
  let ga : Polynomial K := g.map (Polynomial.evalRingHom a)
  have hga0 : ga ≠ 0 := by
    intro h0
    have hc := congrArg (fun q : Polynomial K => q.coeff g.natDegree) h0
    rw [Polynomial.coeff_zero, Polynomial.coeff_map] at hc
    exact ha_ne hc
  obtain ⟨b, hb⟩ := exists_notMem_of_isAlgClosed ga.roots.toFinset
  have hb_ne : Polynomial.eval b ga ≠ 0 := by
    intro h0; apply hb
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hga0, Polynomial.IsRoot.def]; exact h0
  refine ⟨![a, b], ?_⟩
  have hev : Polynomial.eval b ga = eval ![a, b] G := by
    dsimp only [ga, g]
    rw [eval_map_mv2ToPolyY]
    have h1 : (Polynomial.evalRingHom a).comp Polynomial.C = RingHom.id K := by ext r; simp
    have h2 : ![(Polynomial.evalRingHom a) Polynomial.X, b] = ![a, b] := by
      ext i; match i with | 0 => simp | 1 => simp
    rw [h1, h2]; rfl
  rwa [← hev]

-- 6.2 Sylvester Matrix Scaling Lemma: X^(r * s) ∣ Res(f, g) when ord(f) ≥ r, ord(g) ≥ s
lemma two_mul_sum_range_sub (N : ℕ) :
    2 * ∑ k ∈ Finset.range N, (N - k) = N * (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∑ k ∈ Finset.range N, (N + 1 - (k + 1)) = ∑ k ∈ Finset.range N, (N - k) := by
      apply Finset.sum_congr rfl; intro k _; omega
    rw [h1, Nat.sub_zero, mul_add, ih]
    ring

lemma X_pow_mul_dvd_resultant_of_vanishesOrder {K : Type*} [Field K]
    {f g : Polynomial (Polynomial K)} {m d r s : ℕ}
    (hr : r ≤ m) (hs : s ≤ d)
    (hf_ord : ∀ k < r, Polynomial.X ^ (r - k) ∣ f.coeff k)
    (hg_ord : ∀ k < s, Polynomial.X ^ (s - k) ∣ g.coeff k) :
    Polynomial.X ^ (r * s) ∣ f.resultant g m d := by
  classical
  unfold Polynomial.resultant
  rw [Matrix.det_apply]
  apply Finset.dvd_sum
  intro σ _
  have hsign : ∀ (u : ℤˣ) (P : Polynomial K), Polynomial.X ^ (r * s) ∣ P →
      Polynomial.X ^ (r * s) ∣ u • P := by
    intro u P hP
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa using hP
    · simpa using dvd_neg.mpr hP
  apply hsign
  let a : Fin (m + d) → ℕ := fun i => (r + s) - i.val
  let b : Fin (m + d) → ℕ := fun j => if j.val < m then r - j.val else s - (j.val - m)
  have hentry : ∀ (i j : Fin (m + d)),
      Polynomial.X ^ (a i - b j) ∣ (f.sylvester g m d) i j := by
    intro i j
    by_cases he : a i - b j = 0
    · rw [he, pow_zero]; exact one_dvd _
    · by_cases hj : j.val < m
      · let j₁ : Fin m := ⟨j.val, hj⟩
        have hj_eq : j = Fin.castAdd d j₁ := Fin.ext rfl
        have hsylv : (f.sylvester g m d) i j =
            if i.val ∈ Set.Icc j₁.val (j₁.val + d) then g.coeff (i.val - j₁.val) else 0 := by
          rw [hj_eq]; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_left]
        rw [hsylv]
        split_ifs with hin
        · have hb : b j = r - j₁.val := by simp [b, hj, j₁]
          have h1 := hin.1
          have hlt : i.val - j₁.val < s := by dsimp only [a] at he; rw [hb] at he; omega
          have hle : a i - b j ≤ s - (i.val - j₁.val) := by dsimp only [a]; rw [hb]; omega
          exact dvd_trans (pow_dvd_pow Polynomial.X hle) (hg_ord _ hlt)
        · exact dvd_zero _
      · let j₁ : Fin d := ⟨j.val - m, by omega⟩
        have hj_eq : j = Fin.natAdd m j₁ := Fin.ext (by dsimp [Fin.natAdd, j₁]; omega)
        have hsylv : (f.sylvester g m d) i j =
            if i.val ∈ Set.Icc j₁.val (j₁.val + m) then f.coeff (i.val - j₁.val) else 0 := by
          rw [hj_eq]; unfold Polynomial.sylvester; simp only [Matrix.of_apply, Fin.addCases_right]
        rw [hsylv]
        split_ifs with hin
        · have hb : b j = s - j₁.val := by simp [b, hj, j₁]
          have h1 := hin.1
          have hlt : i.val - j₁.val < r := by dsimp only [a] at he; rw [hb] at he; omega
          have hle : a i - b j ≤ r - (i.val - j₁.val) := by dsimp only [a]; rw [hb]; omega
          exact dvd_trans (pow_dvd_pow Polynomial.X hle) (hf_ord _ hlt)
        · exact dvd_zero _
  have hprod_dvd : Polynomial.X ^ (∑ j : Fin (m + d), (a (σ j) - b j)) ∣
      ∏ j : Fin (m + d), (f.sylvester g m d) (σ j) j := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_dvd_prod_of_dvd _ _ (fun j _ => hentry (σ j) j)
  have hsum_ge : r * s ≤ ∑ j : Fin (m + d), (a (σ j) - b j) := by
    have hle_sum : ∑ j : Fin (m + d), a (σ j) ≤
        (∑ j : Fin (m + d), (a (σ j) - b j)) + ∑ j : Fin (m + d), b j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun j _ => by omega)
    have hsum_fin : ∀ (M N : ℕ), N ≤ M →
        ∑ i : Fin M, (N - i.val) = ∑ k ∈ Finset.range N, (N - k) := by
      intro M N hNM
      rw [Fin.sum_univ_eq_sum_range (fun k => N - k) M]
      symm
      apply Finset.sum_subset (Finset.range_mono hNM)
      intro k _ hnot
      rw [Finset.mem_range] at hnot; omega
    have hsum_a : ∑ j : Fin (m + d), a (σ j) = ∑ k ∈ Finset.range (r + s), (r + s - k) := by
      rw [Equiv.sum_comp σ a]; exact hsum_fin (m + d) (r + s) (by omega)
    have hsum_b : ∑ j : Fin (m + d), b j =
        (∑ k ∈ Finset.range r, (r - k)) + ∑ k ∈ Finset.range s, (s - k) := by
      rw [Fin.sum_univ_add]
      congr 1
      · have h1 : ∑ j₁ : Fin m, b (Fin.castAdd d j₁) = ∑ j₁ : Fin m, (r - j₁.val) := by
          apply Finset.sum_congr rfl; intro j₁ _; simp [b, j₁.isLt]
        rw [h1]; exact hsum_fin m r hr
      · have h2 : ∑ j₁ : Fin d, b (Fin.natAdd m j₁) = ∑ j₁ : Fin d, (s - j₁.val) := by
          apply Finset.sum_congr rfl; intro j₁ _; simp [b]
        rw [h2]; exact hsum_fin d s hs
    have hta := two_mul_sum_range_sub (r + s)
    have htr := two_mul_sum_range_sub r
    have hts := two_mul_sum_range_sub s
    have hdiff : 2 * (∑ k ∈ Finset.range (r + s), (r + s - k)) =
        2 * (∑ k ∈ Finset.range r, (r - k)) + 2 * (∑ k ∈ Finset.range s, (s - k)) + 2 * (r * s) := by
      rw [hta, htr, hts]; ring
    omega
  exact dvd_trans (pow_dvd_pow Polynomial.X hsum_ge) hprod_dvd

lemma X_pow_dvd_mv2ToPolyY_coeff_of_vanishesOrder {K : Type*} [Field K]
    {h : MvPolynomial (Fin 2) K} {r : ℕ} (hh : VanishesOrder r h) :
    ∀ k < r, Polynomial.X ^ (r - k) ∣ (mv2ToPolyY K h).coeff k := by
  intro k hk
  rw [Polynomial.X_pow_dvd_iff]
  intro i hi
  rw [coeff_mv2ToPolyY_coeff]
  exact hh (Finsupp.single 0 i + Finsupp.single 1 k) (by
    simp only [Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero, zero_add]
    omega)

-- 6.3 Resultant translation invariance & mod-f factorization
lemma roots_multiset_prod_X_sub_C {E : Type*} [Field E] (s : Multiset E) :
    (s.map fun r => Polynomial.X - Polynomial.C r).prod.roots = s := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.roots_mul, Polynomial.roots_X_sub_C, ih]
    · simp
    · refine mul_ne_zero (Polynomial.X_sub_C_ne_zero a) ?_
      apply Multiset.prod_ne_zero
      intro hmem
      rcases Multiset.mem_map.mp hmem with ⟨r, _, hr⟩
      exact Polynomial.X_sub_C_ne_zero r hr

lemma resultant_comp_X_add_C {R : Type*} [CommRing R] [IsDomain R]
    {f g : Polynomial R} {m d : ℕ} (hf_mon : f.Monic) (hf_nd : f.natDegree = m)
    (hg_nd : g.natDegree ≤ d) (c : R) :
    (f.comp (Polynomial.X + Polynomial.C c)).resultant
      (g.comp (Polynomial.X + Polynomial.C c)) m d = f.resultant g m d := by
  let E := AlgebraicClosure (FractionRing R)
  let ι : R →+* E := (algebraMap (FractionRing R) E).comp (algebraMap R (FractionRing R))
  have hι_inj : Function.Injective ι :=
    (RingHom.injective (algebraMap (FractionRing R) E)).comp (IsFractionRing.injective R _)
  apply hι_inj
  rw [← Polynomial.resultant_map_map, ← Polynomial.resultant_map_map,
    Polynomial.map_comp, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  let fE := f.map ι
  let gE := g.map ι
  have hfE_mon : fE.Monic := hf_mon.map ι
  have hfE_nd : fE.natDegree = m := by rw [hf_mon.natDegree_map, hf_nd]
  have hgE_nd : gE.natDegree ≤ d := Polynomial.natDegree_map_le.trans hg_nd
  let fEs := fE.comp (Polynomial.X + Polynomial.C (ι c))
  let gEs := gE.comp (Polynomial.X + Polynomial.C (ι c))
  have hfEs_mon : fEs.Monic := hfE_mon.comp (Polynomial.monic_X_add_C _) (by simp)
  have hfEs_nd : fEs.natDegree = m := by
    dsimp only [fEs]; rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one, hfE_nd]
  have hgEs_nd : gEs.natDegree ≤ d := by
    dsimp only [gEs]; rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]; exact hgE_nd
  have hfE_prod : fE = (fE.roots.map fun r => Polynomial.X - Polynomial.C r).prod :=
    (IsAlgClosed.splits fE).eq_prod_roots_of_monic hfE_mon
  have hcomp_prod : ∀ s : Multiset E,
      (s.map fun r => Polynomial.X - Polynomial.C r).prod.comp (Polynomial.X + Polynomial.C (ι c)) =
        ((s.map fun r => r - ι c).map fun r => Polynomial.X - Polynomial.C r).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_comp, ih,
        Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons]
      congr 1
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, map_sub]
      ring
  have hfEs_roots : fEs.roots = fE.roots.map (fun r => r - ι c) := by
    have h1 : fEs = ((fE.roots.map fun r => r - ι c).map fun r => Polynomial.X - Polynomial.C r).prod := by
      dsimp only [fEs]; conv_lhs => rw [hfE_prod]
      exact hcomp_prod fE.roots
    rw [h1, roots_multiset_prod_X_sub_C]
  have h1 := Polynomial.resultant_eq_prod_eval fEs gEs d hgEs_nd (IsAlgClosed.splits fEs)
  have h2 := Polynomial.resultant_eq_prod_eval fE gE d hgE_nd (IsAlgClosed.splits fE)
  rw [hfEs_nd, hfEs_mon.leadingCoeff, one_pow, one_mul, hfEs_roots, Multiset.map_map] at h1
  rw [hfE_nd, hfE_mon.leadingCoeff, one_pow, one_mul] at h2
  rw [h1, h2]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  dsimp only [Function.comp_apply, gEs]
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, sub_add_cancel]

lemma resultant_pad_mod_and_mul {R : Type*} [CommRing R] [IsDomain R]
    {f w l h q : Polynomial R} {n D : ℕ}
    (hf_mon : f.Monic) (hf_nd : f.natDegree = n)
    (hnD : n ≤ D + 6)
    (hw_eq : w = l ^ 6 * h + f * q)
    (hw_nd : w.natDegree ≤ D + 6) (hl_nd : l.natDegree ≤ 1) (hh_nd : h.natDegree ≤ D)
    (hl0 : l ≠ 0) (hh0 : h ≠ 0) :
    f.resultant w n (D + 6) = (f.resultant l n 1) ^ 6 * f.resultant h n D := by
  have hfn : f.coeff n = 1 := by rw [← hf_nd]; exact hf_mon.leadingCoeff
  have hl6_nd : (l ^ 6).natDegree = 6 * l.natDegree := Polynomial.natDegree_pow l 6
  have hl6_ne : l ^ 6 ≠ 0 := pow_ne_zero 6 hl0
  have hl6h_nd : (l ^ 6 * h).natDegree = 6 * l.natDegree + h.natDegree := by
    rw [Polynomial.natDegree_mul hl6_ne hh0, hl6_nd]
  have hl6h_le : (l ^ 6 * h).natDegree ≤ D + 6 := by omega
  have hq_le : q.natDegree + n ≤ D + 6 := by
    by_cases hq0 : q = 0
    · rw [hq0, Polynomial.natDegree_zero, zero_add]; exact hnD
    · have hfq_eq : f * q = w - l ^ 6 * h := by rw [hw_eq]; ring
      have hfq_nd : (f * q).natDegree = n + q.natDegree := by
        rw [hf_mon.natDegree_mul' hq0, hf_nd]
      have hsub_le : (w - l ^ 6 * h).natDegree ≤ D + 6 :=
        (Polynomial.natDegree_sub_le _ _).trans (max_le hw_nd hl6h_le)
      rw [← hfq_eq, hfq_nd] at hsub_le; omega
  have hpad : ∀ (p : Polynomial R) (d : ℕ), p.natDegree ≤ d →
      f.resultant p n d = f.resultant p n p.natDegree := by
    intro p d hpd
    have h1 := Polynomial.resultant_add_right_deg f p n p.natDegree (d - p.natDegree) le_rfl
    rw [Nat.add_sub_cancel' hpd, hfn, one_pow, one_mul] at h1
    exact h1
  rw [hw_eq, Polynomial.resultant_add_mul_right f (l ^ 6 * h) q n (D + 6) hq_le (le_of_eq hf_nd),
    hpad (l ^ 6 * h) (D + 6) hl6h_le, Polynomial.natDegree_mul hl6_ne hh0,
    Polynomial.resultant_mul_right f (l ^ 6) h n (le_of_eq hf_nd),
    Polynomial.resultant_pow_right f l n 6 (le_of_eq hf_nd)
      (pow_ne_zero 6 (Polynomial.leadingCoeff_ne_zero.mpr hl0)),
    ← hpad l 1 hl_nd, ← hpad h D hh_nd]

-- 6.4 VanishesOrder invariance under projective linear change of coordinates
lemma vanishesOrder_of_homog_chart {K : Type*} [Field K] {d r : ℕ}
    {P : MvPolynomial (Fin 3) K} (hPh : P.IsHomogeneous d)
    {a b : K}
    (hord : VanishesOrder r (MvPolynomial.eval₂Hom C ![X 0 + C a, X 1 + C b] (dehomogZ P)))
    (L0 L1 L2 : MvPolynomial (Fin 2) K)
    (hL0 : eval ![0, 0] (L0 - C a * L2) = 0)
    (hL1 : eval ![0, 0] (L1 - C b * L2) = 0) :
    VanishesOrder r (MvPolynomial.eval₂Hom C ![L0, L1, L2] P) := by
  let sh : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
    MvPolynomial.eval₂Hom C ![X 0 + C a * X 2, X 1 + C b * X 2, X 2]
  have hsh_hom : (sh P).IsHomogeneous d := by
    rw [P.as_sum, map_sum]
    apply IsHomogeneous.sum
    intro s hs
    dsimp only [sh]
    rw [MvPolynomial.eval₂Hom_monomial]
    apply IsHomogeneous.C_mul
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    have h1 : ∀ i : Fin 3, ((![X 0 + C a * X 2, X 1 + C b * X 2, X 2] i : MvPolynomial (Fin 3) K) ^ s i).IsHomogeneous (s i) := by
      intro i; match i with
      | 0 => simpa using ((isHomogeneous_X K 0).add ((isHomogeneous_X K 2).C_mul a)).pow (s 0)
      | 1 => simpa using ((isHomogeneous_X K 1).add ((isHomogeneous_X K 2).C_mul b)).pow (s 1)
      | 2 => simpa using (isHomogeneous_X K 2).pow (s 2)
    have hpr := IsHomogeneous.prod univ _ (fun i => s i) (fun i _ => h1 i)
    rwa [isHomogeneous_sum_eq hPh hs] at hpr
  have hde_sh : dehomogZ (sh P) = MvPolynomial.eval₂Hom C ![X 0 + C a, X 1 + C b] (dehomogZ P) := by
    have h1 : ∀ Q : MvPolynomial (Fin 3) K,
        dehomogZ (sh Q) = MvPolynomial.eval₂Hom C ![X 0 + C a, X 1 + C b] (dehomogZ Q) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => simp [dehomogZ, sh]
      | add u v hu hv => simp [map_add, hu, hv]
      | mul_X u i hu =>
        rw [map_mul, map_mul, map_mul, map_mul, hu]
        match i with
        | 0 => simp [dehomogZ, sh]
        | 1 => simp [dehomogZ, sh]
        | 2 => simp [dehomogZ, sh]
    exact h1 P
  have hsh_supp : ∀ s ∈ (sh P).support, r ≤ s 0 + s 1 := by
    intro s hs
    let m : Fin 2 →₀ ℕ := Finsupp.single 0 (s 0) + Finsupp.single 1 (s 1)
    have hm_coeff : (dehomogZ (sh P)).coeff m = (sh P).coeff s := by
      conv_lhs => rw [(sh P).as_sum]
      rw [map_sum, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single s]
      · have hmon : dehomogZ (monomial s ((sh P).coeff s)) = monomial m ((sh P).coeff s) := by
          dsimp only [dehomogZ]
          rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
            Fin.prod_univ_three, one_pow, mul_one, MvPolynomial.monomial_eq,
            Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
          simp [m]
        rw [hmon, MvPolynomial.coeff_monomial]; simp
      · intro t ht hne
        have hmon : dehomogZ (monomial t ((sh P).coeff t)) =
            monomial (Finsupp.single (0 : Fin 2) (t 0) + Finsupp.single 1 (t 1)) ((sh P).coeff t) := by
          dsimp only [dehomogZ]
          rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
            Fin.prod_univ_three, one_pow, mul_one, MvPolynomial.monomial_eq,
            Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
          simp
        rw [hmon, MvPolynomial.coeff_monomial]
        have hne_m : Finsupp.single (0 : Fin 2) (t 0) + Finsupp.single 1 (t 1) ≠ m := by
          intro heq; apply hne
          have h0 : t 0 = s 0 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa [m] using this
          have h1 : t 1 = s 1 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa [m] using this
          have hdt := isHomogeneous_sum_eq hsh_hom ht
          have hds := isHomogeneous_sum_eq hsh_hom hs
          rw [Fin.sum_univ_three] at hdt hds
          ext idx; match idx with | 0 => exact h0 | 1 => exact h1 | 2 => omega
        simp [hne_m]
      · intro h; exact absurd hs h
    by_contra hlt
    have hm0 : (dehomogZ (sh P)).coeff m = 0 := by
      rw [hde_sh]
      exact hord m (by simp only [m, Finsupp.add_apply, Finsupp.single_eq_same,
        Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero, zero_add]; omega)
    rw [hm_coeff] at hm0
    exact MvPolynomial.mem_support_iff.mp hs hm0
  have hev_eq : MvPolynomial.eval₂Hom C ![L0, L1, L2] P =
      MvPolynomial.eval₂Hom C ![L0 - C a * L2, L1 - C b * L2, L2] (sh P) := by
    have h1 : ∀ Q : MvPolynomial (Fin 3) K,
        MvPolynomial.eval₂Hom C ![L0, L1, L2] Q =
          MvPolynomial.eval₂Hom C ![L0 - C a * L2, L1 - C b * L2, L2] (sh Q) := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => simp [sh]
      | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
      | mul_X u i hu =>
        rw [map_mul, map_mul, map_mul, hu]
        match i with
        | 0 => simp [sh]
        | 1 => simp [sh]
        | 2 => simp [sh]
    exact h1 P
  have hvo1 : ∀ g : MvPolynomial (Fin 2) K, eval ![0, 0] g = 0 → VanishesOrder 1 g := by
    intro g hg m hm
    have hm0 : m = 0 := by ext i; match i with | 0 => simp; omega | 1 => simp; omega
    have hev0 : eval ![0, 0] g = g.coeff 0 := by
      conv_lhs => rw [g.as_sum]
      rw [map_sum]
      by_cases h0 : (0 : Fin 2 →₀ ℕ) ∈ g.support
      · rw [Finset.sum_eq_single 0]
        · rw [eval_monomial]; simp
        · intro t _ hne
          rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
          by_cases ht0 : t 0 = 0
          · have ht1 : t 1 ≠ 0 := fun h1 => hne (by ext i; match i with | 0 => exact ht0 | 1 => exact h1)
            simp [zero_pow ht1]
          · simp [zero_pow ht0]
        · intro h; exact absurd h0 h
      · rw [MvPolynomial.notMem_support_iff.mp h0]
        apply Finset.sum_eq_zero
        intro t ht
        have hne : t ≠ 0 := fun h => h0 (h ▸ ht)
        rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        by_cases ht0 : t 0 = 0
        · have ht1 : t 1 ≠ 0 := fun h1 => hne (by ext i; match i with | 0 => exact ht0 | 1 => exact h1)
          simp [zero_pow ht1]
        · simp [zero_pow ht0]
    rw [hm0, ← hev0]; exact hg
  have hvo_L0 : VanishesOrder 1 (L0 - C a * L2) := hvo1 _ hL0
  have hvo_L1 : VanishesOrder 1 (L1 - C b * L2) := hvo1 _ hL1
  have hvo_zero : ∀ g : MvPolynomial (Fin 2) K, VanishesOrder 0 g :=
    fun _ _ hm => absurd hm (by omega)
  have hvo_sum : ∀ (s : Finset (Fin 3 →₀ ℕ)) (f : (Fin 3 →₀ ℕ) → MvPolynomial (Fin 2) K),
      (∀ i ∈ s, VanishesOrder r (f i)) → VanishesOrder r (∑ i ∈ s, f i) := by
    intro s f hf
    classical
    induction s using Finset.induction_on with
    | empty => intro m _; simp
    | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact vanishesOrder_add (hf x (mem_insert_self x s))
        (ih (fun i hi => hf i (mem_insert_of_mem hi)))
  rw [hev_eq, (sh P).as_sum, map_sum]
  apply hvo_sum
  intro s hs
  rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hC0 : VanishesOrder 0 (C ((sh P).coeff s)) := hvo_zero _
  have hp0 : VanishesOrder (s 0) ((L0 - C a * L2) ^ s 0) := by
    have := vanishesOrder_pow hvo_L0 (s 0); rwa [mul_one] at this
  have hp1 : VanishesOrder (s 1) ((L1 - C b * L2) ^ s 1) := by
    have := vanishesOrder_pow hvo_L1 (s 1); rwa [mul_one] at this
  have hp2 : VanishesOrder 0 (L2 ^ s 2) := hvo_zero _
  have hall := vanishesOrder_mul hC0 (vanishesOrder_mul (vanishesOrder_mul hp0 hp1) hp2)
  rw [zero_add, add_zero] at hall
  exact vanishesOrder_mono (hsh_supp s hs) hall

-- 6.5 Smooth-point X^5 divisibility via telescoping Taylor derivative & Fermat's little theorem
lemma X5_dvd_fwMatrix_of_rational_const {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    {K : Type*} [Field K] [CharP K p]
    {α β : PowerSeries K}
    (hα_unit : IsUnit (PowerSeries.derivative K α))
    (hα_p : (PowerSeries.constantCoeff α) ^ p = PowerSeries.constantCoeff α)
    (hβ_p : (PowerSeries.constantCoeff β) ^ p = PowerSeries.constantCoeff β) :
    let uinv : PowerSeries K := ((hα_unit.unit⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)
    let Dα : RingDeriv (PowerSeries K) := (powerSeriesDeriv K).smul uinv
    PowerSeries.X ^ 5 ∣ (fwMatrix p Dα ![1, α, β, α ^ 2, α * β, β ^ 2]).det := by
  intro uinv Dα
  have hCharS : CharP (PowerSeries K) p := charP_of_injective_ringHom PowerSeries.C_injective p
  have hmul_inv : uinv * PowerSeries.derivative K α = 1 := Units.inv_mul hα_unit.unit
  have hmul_inv' : PowerSeries.derivative K α * uinv = 1 := Units.mul_inv hα_unit.unit
  have hDα_C : ∀ c : K, Dα (PowerSeries.C c) = 0 := by
    intro c; change uinv * PowerSeries.derivative K (PowerSeries.C c) = 0
    rw [PowerSeries.derivative_C, mul_zero]
  have hDα_pow_p : ∀ s : PowerSeries K, Dα (s ^ p) = 0 := by
    intro s; rw [Dα.map_pow, CharP.cast_eq_zero (PowerSeries K) p, zero_mul, zero_mul]
  let u : PowerSeries K := α - PowerSeries.C (PowerSeries.constantCoeff α)
  have hX_dvd_u : PowerSeries.X ∣ u := by
    rw [PowerSeries.X_dvd_iff]; simp [u]
  have hDα_u : Dα u = 1 := by
    dsimp only [u]; rw [Dα.map_sub, hDα_C, sub_zero]; exact hmul_inv
  have hDα_neg_u : Dα (-u) = -1 := by rw [Dα.map_neg, hDα_u]
  have hcast_ne : ∀ k : ℕ, 0 < k → k < 7 → (k : K) ≠ 0 := by
    intro k hk0 hk7 h0
    have hdvd := (CharP.cast_eq_zero_iff K p k).mp h0
    have hle := Nat.le_of_dvd hk0 hdvd
    omega
  have h2K : (2 : K) ≠ 0 := by exact_mod_cast hcast_ne 2 (by omega) (by omega)
  have h3K : (3 : K) ≠ 0 := by exact_mod_cast hcast_ne 3 (by omega) (by omega)
  have h4K : (4 : K) ≠ 0 := by exact_mod_cast hcast_ne 4 (by omega) (by omega)
  have h6K : (6 : K) ≠ 0 := by exact_mod_cast hcast_ne 6 (by omega) (by omega)
  have h24K : (24 : K) ≠ 0 := by
    have : (24 : K) = 4 * 6 := by norm_num
    rw [this]; exact mul_ne_zero h4K h6K
  let c2 : PowerSeries K := PowerSeries.C (2 : K)⁻¹
  let c6 : PowerSeries K := PowerSeries.C (6 : K)⁻¹
  let c24 : PowerSeries K := PowerSeries.C (24 : K)⁻¹
  have hc2 : (2 : PowerSeries K) * c2 = 1 := by
    dsimp only [c2]; rw [← map_ofNat PowerSeries.C 2, ← map_mul, mul_inv_cancel₀ h2K, map_one]
  have hc6 : (3 : PowerSeries K) * c6 = c2 := by
    dsimp only [c6, c2]; rw [← map_ofNat PowerSeries.C 3, ← map_mul]
    congr 1; field_simp [h2K, h6K]; norm_num
  have hc24 : (4 : PowerSeries K) * c24 = c6 := by
    dsimp only [c24, c6]; rw [← map_ofNat PowerSeries.C 4, ← map_mul]
    congr 1; field_simp [h6K, h24K]; norm_num
  let R : PowerSeries K → PowerSeries K := fun s =>
    s ^ p - s - (-u) * Dα s - c2 * (-u) ^ 2 * Dα.iter 2 s -
      c6 * (-u) ^ 3 * Dα.iter 3 s - c24 * (-u) ^ 4 * Dα.iter 4 s
  have hR_X5 : ∀ s : PowerSeries K, (PowerSeries.constantCoeff s) ^ p = PowerSeries.constantCoeff s →
      PowerSeries.X ^ 5 ∣ R s := by
    intro s hs_p
    have hDR : Dα (R s) = -(c24 * (-u) ^ 4 * Dα.iter 5 s) := by
      dsimp only [R]
      have h1 : Dα ((-u) * Dα s) = -Dα s + (-u) * Dα.iter 2 s := by
        rw [Dα.map_mul', hDα_neg_u]; change -1 * Dα s + (-u) * Dα.iter 2 s = _; ring
      have h2 : Dα (c2 * (-u) ^ 2 * Dα.iter 2 s) =
          -((-u) * Dα.iter 2 s) + c2 * (-u) ^ 2 * Dα.iter 3 s := by
        rw [Dα.map_mul', Dα.map_mul', hDα_C, zero_mul, zero_add, Dα.map_pow, hDα_neg_u]
        change c2 * (2 * (-u) ^ 1 * -1) * Dα.iter 2 s + c2 * (-u) ^ 2 * Dα.iter 3 s = _
        linear_combination -(-u) * Dα.iter 2 s * hc2
      have h3 : Dα (c6 * (-u) ^ 3 * Dα.iter 3 s) =
          -(c2 * (-u) ^ 2 * Dα.iter 3 s) + c6 * (-u) ^ 3 * Dα.iter 4 s := by
        rw [Dα.map_mul', Dα.map_mul', hDα_C, zero_mul, zero_add, Dα.map_pow, hDα_neg_u]
        change c6 * (3 * (-u) ^ 2 * -1) * Dα.iter 3 s + c6 * (-u) ^ 3 * Dα.iter 4 s = _
        linear_combination -(-u) ^ 2 * Dα.iter 3 s * hc6
      have h4 : Dα (c24 * (-u) ^ 4 * Dα.iter 4 s) =
          -(c6 * (-u) ^ 3 * Dα.iter 4 s) + c24 * (-u) ^ 4 * Dα.iter 5 s := by
        rw [Dα.map_mul', Dα.map_mul', hDα_C, zero_mul, zero_add, Dα.map_pow, hDα_neg_u]
        change c24 * (4 * (-u) ^ 3 * -1) * Dα.iter 4 s + c24 * (-u) ^ 4 * Dα.iter 5 s = _
        linear_combination -(-u) ^ 3 * Dα.iter 4 s * hc24
      rw [Dα.map_sub, Dα.map_sub, Dα.map_sub, Dα.map_sub, Dα.map_sub,
        hDα_pow_p s, h1, h2, h3, h4]
      ring
    have hderiv_R : PowerSeries.derivative K (R s) = PowerSeries.derivative K α * Dα (R s) := by
      change PowerSeries.derivative K (R s) = PowerSeries.derivative K α * (uinv * PowerSeries.derivative K (R s))
      rw [← mul_assoc, hmul_inv', one_mul]
    have hX4_deriv : PowerSeries.X ^ 4 ∣ PowerSeries.derivative K (R s) := by
      rw [hderiv_R, hDR]
      have hu4 : PowerSeries.X ^ 4 ∣ (-u) ^ 4 := pow_dvd_pow_of_dvd (dvd_neg.mpr hX_dvd_u) 4
      have h1 : PowerSeries.X ^ 4 ∣ c24 * (-u) ^ 4 * Dα.iter 5 s :=
        dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hu4 _) _
      exact dvd_mul_of_dvd_right (dvd_neg.mpr h1) _
    have hconst_R : PowerSeries.constantCoeff (R s) = 0 := by
      dsimp only [R]
      have hu0 : PowerSeries.constantCoeff (-u) = 0 := by simp [u]
      simp only [map_sub, map_mul, map_pow, hu0, zero_pow (by omega : 2 ≠ 0),
        zero_pow (by omega : 3 ≠ 0), zero_pow (by omega : 4 ≠ 0), zero_mul, mul_zero, sub_zero]
      rw [hs_p, sub_self]
    rw [PowerSeries.X_pow_dvd_iff]
    intro k hk
    by_cases hk0 : k = 0
    · subst hk0; rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hconst_R
    · have hc0 := (PowerSeries.X_pow_dvd_iff.mp hX4_deriv) (k - 1) (by omega)
      rw [PowerSeries.coeff_derivative] at hc0
      have hk1 : k - 1 + 1 = k := by omega
      rw [hk1] at hc0
      have hcast : ((k - 1 : ℕ) : K) + 1 = (k : K) := by
        rw [← Nat.cast_succ, Nat.succ_eq_add_one, hk1]
      rw [hcast] at hc0
      exact (mul_eq_zero.mp hc0).resolve_right (hcast_ne k (by omega) (by omega))
  let m : Fin 6 → PowerSeries K := ![1, α, β, α ^ 2, α * β, β ^ 2]
  have hm_p : ∀ j : Fin 6, (PowerSeries.constantCoeff (m j)) ^ p = PowerSeries.constantCoeff (m j) := by
    intro j; match j with
    | 0 => simp [m]
    | 1 => exact hα_p
    | 2 => exact hβ_p
    | 3 =>
      change (PowerSeries.constantCoeff (α ^ 2)) ^ p = PowerSeries.constantCoeff (α ^ 2)
      rw [map_pow, ← pow_mul, mul_comm 2 p, pow_mul, hα_p]
    | 4 =>
      change (PowerSeries.constantCoeff (α * β)) ^ p = PowerSeries.constantCoeff (α * β)
      rw [map_mul, mul_pow, hα_p, hβ_p]
    | 5 =>
      change (PowerSeries.constantCoeff (β ^ 2)) ^ p = PowerSeries.constantCoeff (β ^ 2)
      rw [map_pow, ← pow_mul, mul_comm 2 p, pow_mul, hβ_p]
  let Lmat : Matrix (Fin 6) (Fin 6) (PowerSeries K) := !![
    1, -1, -(-u), -(c2 * (-u) ^ 2), -(c6 * (-u) ^ 3), -(c24 * (-u) ^ 4);
    0, 1,  0,     0,                0,                0;
    0, 0,  1,     0,                0,                0;
    0, 0,  0,     1,                0,                0;
    0, 0,  0,     0,                1,                0;
    0, 0,  0,     0,                0,                1
  ]
  have hL_ut : Lmat.BlockTriangular id := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | rfl
  have hL_det : Lmat.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hL_ut]; simp [Lmat, Fin.prod_univ_six]
  have hdet_eq : (fwMatrix p Dα m).det = (Lmat * fwMatrix p Dα m).det := by
    rw [Matrix.det_mul, hL_det, one_mul]
  rw [hdet_eq, Matrix.det_succ_row_zero]
  apply Finset.dvd_sum
  intro j _
  have hrow0 : (Lmat * fwMatrix p Dα m) 0 j = R (m j) := by
    rw [Matrix.mul_apply, Fin.sum_univ_six]
    simp only [Lmat, fwMatrix, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    dsimp only [R]; ring
  rw [hrow0]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (hR_X5 (m j) (hm_p j)) _) _

lemma smooth_chart_X5_dvd {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    {q : Fin 3 → ZMod p} (hq2 : q 2 ≠ 0)
    (Xvec : Fin 3 → PowerSeries K)
    (hXF : MvPolynomial.eval₂Hom PowerSeries.C Xvec (F.map ι) = 0)
    (hX_const : ∃ c : K, c ≠ 0 ∧ ∀ j : Fin 3, PowerSeries.constantCoeff (Xvec j) = c * ι (q j))
    (hsmooth : ∃ j : Fin 3, eval (ι ∘ q) (MvPolynomial.pderiv j (F.map ι)) ≠ 0)
    (hlin : ¬ ∃ lam : K, ∀ j : Fin 3,
      PowerSeries.constantCoeff (PowerSeries.derivative K (Xvec j)) =
        lam * PowerSeries.constantCoeff (Xvec j)) :
    PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C Xvec ((W10Z p n F).map ι) := by
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hCharK : CharP K p := charP_of_injective_ringHom hι_inj p
  have hp7 : 7 ≤ p := by
    by_contra hlt
    have heq : 2 * n = p := by omega
    have h2dvd : 2 ∣ p := ⟨n, heq.symm⟩
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd 2 h2dvd with h | h
    · omega
    · exact hp2 h.symm
  have h2K : (2 : K) ≠ 0 := by
    intro h0
    have hdvd := (CharP.cast_eq_zero_iff K p 2).mp h0
    have hle := Nat.le_of_dvd (by omega) hdvd; omega
  obtain ⟨c, hc0, hXc⟩ := hX_const
  have hq2K : ι (q 2) ≠ 0 := fun h => hq2 (hι_inj (h.trans (map_zero ι).symm))
  have hX2_unit : IsUnit (Xvec 2) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, hXc 2]
    exact mul_ne_zero hc0 hq2K
  let X2inv : PowerSeries K := ((hX2_unit.unit⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)
  have hX2_mul : Xvec 2 * X2inv = 1 := Units.mul_inv hX2_unit.unit
  have hX2_mul' : X2inv * Xvec 2 = 1 := Units.inv_mul hX2_unit.unit
  let α : PowerSeries K := Xvec 0 * X2inv
  let β : PowerSeries K := Xvec 1 * X2inv
  have hinv_c : PowerSeries.constantCoeff X2inv = (c * ι (q 2))⁻¹ := by
    have h1 := congrArg PowerSeries.constantCoeff hX2_mul
    rw [map_mul, map_one, hXc 2] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hα0 : PowerSeries.constantCoeff α = ι (q 0 / q 2) := by
    dsimp only [α]; rw [map_mul, hXc 0, hinv_c, map_div₀, div_eq_mul_inv, mul_inv]
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    linear_combination ι (q 0) * (ι (q 2))⁻¹ * hcc
  have hβ0 : PowerSeries.constantCoeff β = ι (q 1 / q 2) := by
    dsimp only [β]; rw [map_mul, hXc 1, hinv_c, map_div₀, div_eq_mul_inv, mul_inv]
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    linear_combination ι (q 1) * (ι (q 2))⁻¹ * hcc
  have hα_p : (PowerSeries.constantCoeff α) ^ p = PowerSeries.constantCoeff α := by
    rw [hα0, ← map_pow, ZMod.pow_card]
  have hβ_p : (PowerSeries.constantCoeff β) ^ p = PowerSeries.constantCoeff β := by
    rw [hβ0, ← map_pow, ZMod.pow_card]
  -- Homogeneous evaluation scaling: eval₂Hom C Xvec P = Xvec 2 ^ d * eval₂Hom C ![α, β] (dehomogZ P)
  have hev_hom : ∀ {d : ℕ} {P : MvPolynomial (Fin 3) K}, P.IsHomogeneous d →
      MvPolynomial.eval₂Hom PowerSeries.C Xvec P =
        Xvec 2 ^ d * MvPolynomial.eval₂Hom PowerSeries.C ![α, β] (dehomogZ P) := by
    intro d P hPh
    rw [P.as_sum, map_sum, map_sum, map_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hdeg := isHomogeneous_sum_eq hPh hs
    rw [Fin.sum_univ_three] at hdeg
    have hde : dehomogZ (monomial s (P.coeff s)) =
        C (P.coeff s) * (X 0 ^ s 0 * X 1 ^ s 1) := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
      simp [dehomogZ]
    rw [hde, MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
      Fin.prod_univ_three]
    simp only [map_mul, map_pow, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
      Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [α, β]
    rw [mul_pow, mul_pow, ← hdeg, pow_add, pow_add]
    have h0 : Xvec 2 ^ s 0 * X2inv ^ s 0 = 1 := by rw [← mul_pow, hX2_mul, one_pow]
    have h1 : Xvec 2 ^ s 1 * X2inv ^ s 1 = 1 := by rw [← mul_pow, hX2_mul, one_pow]
    calc PowerSeries.C (P.coeff s) * (Xvec 0 ^ s 0 * Xvec 1 ^ s 1 * Xvec 2 ^ s 2)
        = (Xvec 2 ^ s 0 * X2inv ^ s 0) * (Xvec 2 ^ s 1 * X2inv ^ s 1) *
            (PowerSeries.C (P.coeff s) * (Xvec 0 ^ s 0 * Xvec 1 ^ s 1 * Xvec 2 ^ s 2)) := by
              rw [h0, h1, one_mul, one_mul]
      _ = Xvec 2 ^ s 0 * Xvec 2 ^ s 1 * Xvec 2 ^ s 2 *
            (PowerSeries.C (P.coeff s) * (Xvec 0 ^ s 0 * X2inv ^ s 0 * (Xvec 1 ^ s 1 * X2inv ^ s 1))) := by
              ring
  let FK := F.map ι
  let fK := dehomogZ FK
  have hFK_h : FK.IsHomogeneous n := hFh.map ι
  have hφ_fK : MvPolynomial.eval₂Hom PowerSeries.C ![α, β] fK = 0 := by
    have h1 := hev_hom hFK_h
    rw [hXF] at h1
    have h2 : X2inv ^ n * (Xvec 2 ^ n * MvPolynomial.eval₂Hom PowerSeries.C ![α, β] fK) = 0 := by
      rw [← h1, mul_zero]
    rw [← mul_assoc, ← mul_pow, hX2_mul', one_pow, one_mul] at h2
    exact h2
  -- Show (α'(0), β'(0)) ≠ (0, 0) using hlin
  have hderiv_nz : PowerSeries.constantCoeff (PowerSeries.derivative K α) ≠ 0 ∨
      PowerSeries.constantCoeff (PowerSeries.derivative K β) ≠ 0 := by
    by_contra hboth
    rw [not_or, not_not, not_not] at hboth
    rcases hboth with ⟨hαd0, hβd0⟩
    apply hlin
    have hX2_0 : PowerSeries.constantCoeff (Xvec 2) ≠ 0 := by rw [hXc 2]; exact mul_ne_zero hc0 hq2K
    refine ⟨PowerSeries.constantCoeff (PowerSeries.derivative K (Xvec 2)) / PowerSeries.constantCoeff (Xvec 2), ?_⟩
    have hα_rel : PowerSeries.derivative K (Xvec 0) =
        PowerSeries.derivative K α * Xvec 2 + α * PowerSeries.derivative K (Xvec 2) := by
      have hX0 : Xvec 0 = α * Xvec 2 := by dsimp only [α]; rw [mul_assoc, hX2_mul', mul_one]
      conv_lhs => rw [hX0]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    have hβ_rel : PowerSeries.derivative K (Xvec 1) =
        PowerSeries.derivative K β * Xvec 2 + β * PowerSeries.derivative K (Xvec 2) := by
      have hX1 : Xvec 1 = β * Xvec 2 := by dsimp only [β]; rw [mul_assoc, hX2_mul', mul_one]
      conv_lhs => rw [hX1]
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    intro j; match j with
    | 0 =>
      have h1 := congrArg PowerSeries.constantCoeff hα_rel
      rw [map_add PowerSeries.constantCoeff, map_mul PowerSeries.constantCoeff,
        map_mul PowerSeries.constantCoeff, hαd0, zero_mul, zero_add] at h1
      have h2 : PowerSeries.constantCoeff (Xvec 0) = PowerSeries.constantCoeff α * PowerSeries.constantCoeff (Xvec 2) := by
        have hX0 : Xvec 0 = α * Xvec 2 := by dsimp only [α]; rw [mul_assoc, hX2_mul', mul_one]
        rw [hX0, map_mul]
      rw [h1, h2]; field_simp [hX2_0]
    | 1 =>
      have h1 := congrArg PowerSeries.constantCoeff hβ_rel
      rw [map_add PowerSeries.constantCoeff, map_mul PowerSeries.constantCoeff,
        map_mul PowerSeries.constantCoeff, hβd0, zero_mul, zero_add] at h1
      have h2 : PowerSeries.constantCoeff (Xvec 1) = PowerSeries.constantCoeff β * PowerSeries.constantCoeff (Xvec 2) := by
        have hX1 : Xvec 1 = β * Xvec 2 := by dsimp only [β]; rw [mul_assoc, hX2_mul', mul_one]
        rw [hX1, map_mul]
      rw [h1, h2]; field_simp [hX2_0]
    | 2 => rw [div_mul_cancel₀ _ hX2_0]
  -- Show (fK_x(α₀, β₀), fK_y(α₀, β₀)) ≠ (0, 0) using hsmooth + Euler
  let α0 := PowerSeries.constantCoeff α
  let β0 := PowerSeries.constantCoeff β
  have hconst_ev : ∀ g : MvPolynomial (Fin 2) K,
      PowerSeries.constantCoeff (MvPolynomial.eval₂Hom PowerSeries.C ![α, β] g) = eval ![α0, β0] g := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C r => simp
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
    | mul_X a i ha =>
      rw [map_mul, map_mul, map_mul, ha]
      match i with | 0 => simp [α0] | 1 => simp [β0]
  have hgrad_nz : eval ![α0, β0] (MvPolynomial.pderiv 0 fK) ≠ 0 ∨
      eval ![α0, β0] (MvPolynomial.pderiv 1 fK) ≠ 0 := by
    by_contra hboth
    rw [not_or, not_not, not_not] at hboth
    rcases hboth with ⟨hfx0, hfy0⟩
    have hpt_eq : ![α0, β0, 1] = (ι (q 2))⁻¹ • (ι ∘ q) := by
      ext i; match i with
      | 0 => change α0 = (ι (q 2))⁻¹ * ι (q 0); dsimp only [α0]; rw [hα0, map_div₀, div_eq_inv_mul]
      | 1 => change β0 = (ι (q 2))⁻¹ * ι (q 1); dsimp only [β0]; rw [hβ0, map_div₀, div_eq_inv_mul]
      | 2 => change 1 = (ι (q 2))⁻¹ * ι (q 2); rw [inv_mul_cancel₀ hq2K]
    have hde_ev : ∀ P : MvPolynomial (Fin 3) K, eval ![α0, β0] (dehomogZ P) = eval ![α0, β0, 1] P := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C r => simp [dehomogZ]
      | add a b ha hb => simp [map_add, ha, hb]
      | mul_X a i ha =>
        rw [map_mul, map_mul, map_mul, ha]
        match i with | 0 => simp [dehomogZ] | 1 => simp [dehomogZ] | 2 => simp [dehomogZ]
    have hFX0 : eval (ι ∘ q) (MvPolynomial.pderiv 0 FK) = 0 := by
      rw [← dehomogZ_pderiv_0, hde_ev, hpt_eq, isHomogeneous_eval_smul (isHomogeneous_pderiv hFK_h 0)] at hfx0
      exact (mul_eq_zero.mp hfx0).resolve_left (pow_ne_zero _ (inv_ne_zero hq2K))
    have hFY0 : eval (ι ∘ q) (MvPolynomial.pderiv 1 FK) = 0 := by
      rw [← dehomogZ_pderiv_1, hde_ev, hpt_eq, isHomogeneous_eval_smul (isHomogeneous_pderiv hFK_h 1)] at hfy0
      exact (mul_eq_zero.mp hfy0).resolve_left (pow_ne_zero _ (inv_ne_zero hq2K))
    have hFK_q0 : eval (ι ∘ q) FK = 0 := by
      have h1 := congrArg PowerSeries.constantCoeff hφ_fK
      rw [map_zero, hconst_ev, hde_ev, hpt_eq, isHomogeneous_eval_smul hFK_h] at h1
      exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (inv_ne_zero hq2K))
    have hFZ0 : eval (ι ∘ q) (MvPolynomial.pderiv 2 FK) = 0 := by
      have heul := congrArg (eval (ι ∘ q)) (euler_homog_fin3 hFK_h)
      simp only [map_add, map_mul, eval_X, map_natCast, hFX0, hFY0, hFK_q0, mul_zero, zero_add] at heul
      exact (mul_eq_zero.mp heul).resolve_left hq2K
    obtain ⟨j, hj⟩ := hsmooth
    match j with
    | 0 => exact hj hFX0
    | 1 => exact hj hFY0
    | 2 => exact hj hFZ0
  -- Chain rule at constantCoeff: fK_x(α₀, β₀) * α'(0) + fK_y(α₀, β₀) * β'(0) = 0
  have hch0 : eval ![α0, β0] (MvPolynomial.pderiv 0 fK) * PowerSeries.constantCoeff (PowerSeries.derivative K α) +
      eval ![α0, β0] (MvPolynomial.pderiv 1 fK) * PowerSeries.constantCoeff (PowerSeries.derivative K β) = 0 := by
    have h1 := congrArg PowerSeries.constantCoeff (powerSeries_chain_rule α β fK)
    rw [hφ_fK, map_zero, map_zero, map_add PowerSeries.constantCoeff,
      map_mul PowerSeries.constantCoeff, map_mul PowerSeries.constantCoeff, hconst_ev, hconst_ev] at h1
    exact h1.symm
  -- Helper: when f_y(u₀, v₀) ≠ 0 and u'(0) ≠ 0, X^5 ∣ (W10 p g)(u, v)
  have hmain_case : ∀ (g : MvPolynomial (Fin 2) K) (u v : PowerSeries K),
      MvPolynomial.eval₂Hom PowerSeries.C ![u, v] g = 0 →
      (PowerSeries.constantCoeff u) ^ p = PowerSeries.constantCoeff u →
      (PowerSeries.constantCoeff v) ^ p = PowerSeries.constantCoeff v →
      PowerSeries.constantCoeff (PowerSeries.derivative K u) ≠ 0 →
      PowerSeries.constantCoeff (MvPolynomial.eval₂Hom PowerSeries.C ![u, v] (MvPolynomial.pderiv 1 g)) ≠ 0 →
      PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C ![u, v] (W10 p g) := by
    intro g u v hg0 hu_p hv_p hud_ne hgy_ne
    have hu_unit : IsUnit (PowerSeries.derivative K u) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]; exact hud_ne
    have hgy_unit : IsUnit (MvPolynomial.eval₂Hom PowerSeries.C ![u, v] (MvPolynomial.pderiv 1 g)) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero]; exact hgy_ne
    let uinv : PowerSeries K := ((hu_unit.unit⁻¹ : (PowerSeries K)ˣ) : PowerSeries K)
    let Du : RingDeriv (PowerSeries K) := (powerSeriesDeriv K).smul uinv
    have hX5_fw : PowerSeries.X ^ 5 ∣ (fwMatrix p Du ![1, u, v, u ^ 2, u * v, v ^ 2]).det :=
      X5_dvd_fwMatrix_of_rational_const hp7 hu_unit hu_p hv_p
    -- Relate (fwMatrix p Du m).det to 2 * (W10 p g)(u, v) / g_y(u, v)^10 in FractionRing (PowerSeries K)
    let S := PowerSeries K
    let LS := FractionRing S
    let ιS := algebraMap S LS
    have hιS_inj : Function.Injective ιS := IsFractionRing.injective S LS
    let φS := MvPolynomial.eval₂Hom PowerSeries.C ![u, v]
    let φLS := ιS.comp φS
    let DLS : RingDeriv LS := Du.toFractionRing
    have hDu_u : Du u = 1 := Units.inv_mul hu_unit.unit
    have hDLS_X0 : DLS (φLS (X 0)) = 1 := by
      dsimp only [φLS, RingHom.comp_apply, DLS]
      rw [RingDeriv.toFractionRing_algebraMap]
      have hX0 : φS (X 0) = u := by simp [φS]
      rw [hX0, hDu_u, map_one]
    have hφLS_gy_ne : φLS (MvPolynomial.pderiv 1 g) ≠ 0 := by
      intro h0
      have h1 : φS (MvPolynomial.pderiv 1 g) = 0 := hιS_inj (h0.trans (map_zero ιS).symm)
      exact hgy_ne (by rw [h1, map_zero])
    have hDu_ch : ∀ q : MvPolynomial (Fin 2) K,
        Du (φS q) = φS (MvPolynomial.pderiv 0 q) * Du u + φS (MvPolynomial.pderiv 1 q) * Du v := by
      intro q
      change uinv * PowerSeries.derivative K (φS q) = _
      rw [powerSeries_chain_rule u v q]
      change uinv * (φS (MvPolynomial.pderiv 0 q) * PowerSeries.derivative K u +
        φS (MvPolynomial.pderiv 1 q) * PowerSeries.derivative K v) =
        φS (MvPolynomial.pderiv 0 q) * (uinv * PowerSeries.derivative K u) +
        φS (MvPolynomial.pderiv 1 q) * (uinv * PowerSeries.derivative K v)
      ring
    have hDLS_X1 : DLS (φLS (X 1)) = -φLS (MvPolynomial.pderiv 0 g) / φLS (MvPolynomial.pderiv 1 g) := by
      have h1 := congrArg ιS (hDu_ch g)
      rw [hg0, Du.map_zero, hDu_u, mul_one, map_zero, map_add, map_mul] at h1
      have hv_eq : ιS (Du v) = DLS (φLS (X 1)) := by
        dsimp only [φLS, RingHom.comp_apply, DLS]
        rw [RingDeriv.toFractionRing_algebraMap]
        have hX1 : φS (X 1) = v := by simp [φS]
        rw [hX1]
      rw [hv_eq] at h1
      rw [eq_div_iff hφLS_gy_ne]
      linear_combination h1.symm
    have hDLS_φ : ∀ q : MvPolynomial (Fin 2) K,
        DLS (φLS q) = φLS (Dt2 g q) / φLS (MvPolynomial.pderiv 1 g) := by
      intro q
      have h1 := congrArg ιS (hDu_ch q)
      rw [hDu_u, mul_one, map_add, map_mul] at h1
      have hq_eq : ιS (Du (φS q)) = DLS (φLS q) := by
        dsimp only [φLS, RingHom.comp_apply, DLS]; rw [RingDeriv.toFractionRing_algebraMap]
      have hv_eq : ιS (Du v) = DLS (φLS (X 1)) := by
        dsimp only [φLS, RingHom.comp_apply, DLS]
        rw [RingDeriv.toFractionRing_algebraMap]
        have hX1 : φS (X 1) = v := by simp [φS]
        rw [hX1]
      rw [hq_eq, hv_eq, hDLS_X1] at h1
      rw [h1]
      have hDt : φLS (Dt2 g q) =
          φLS (MvPolynomial.pderiv 1 g) * φLS (MvPolynomial.pderiv 0 q) -
          φLS (MvPolynomial.pderiv 0 g) * φLS (MvPolynomial.pderiv 1 q) := by
        unfold Dt2; simp only [map_sub, map_mul]
      rw [hDt, eq_div_iff hφLS_gy_ne]
      have hm : (-φLS (MvPolynomial.pderiv 0 g) / φLS (MvPolynomial.pderiv 1 g)) *
          φLS (MvPolynomial.pderiv 1 g) = -φLS (MvPolynomial.pderiv 0 g) :=
        div_mul_cancel₀ _ hφLS_gy_ne
      linear_combination φLS (MvPolynomial.pderiv 1 q) * hm
    have hdet_LS : ιS ((fwMatrix p Du ![1, u, v, u ^ 2, u * v, v ^ 2]).det) =
        2 * φLS (W10 p g) / φLS (MvPolynomial.pderiv 1 g) ^ 10 := by
      have hmap_fw : ιS ((fwMatrix p Du ![1, u, v, u ^ 2, u * v, v ^ 2]).det) =
          (fwMatrix p DLS ![1, φLS (X 0), φLS (X 1), φLS (X 0) ^ 2, φLS (X 0) * φLS (X 1), φLS (X 1) ^ 2]).det := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        have hiter : ∀ k (x : S), ιS (Du.iter k x) = DLS.iter k (ιS x) := by
          intro k x
          induction k with
          | zero => rfl
          | succ k ih =>
            change ιS (Du (Du.iter k x)) = DLS (DLS.iter k (ιS x))
            rw [← ih, ← RingDeriv.toFractionRing_algebraMap]
        have hm_j : ∀ j : Fin 6,
            ιS ((![1, u, v, u ^ 2, u * v, v ^ 2] : Fin 6 → S) j) =
              (![1, φLS (X 0), φLS (X 1), φLS (X 0) ^ 2, φLS (X 0) * φLS (X 1), φLS (X 1) ^ 2] : Fin 6 → LS) j := by
          intro j
          have hX0 : φLS (X 0) = ιS u := by dsimp only [φLS]; simp [φS]
          have hX1 : φLS (X 1) = ιS v := by dsimp only [φLS]; simp [φS]
          match j with
          | 0 => simp
          | 1 => simp [hX0]
          | 2 => simp [hX1]
          | 3 => simp [hX0]
          | 4 => simp [hX0, hX1]
          | 5 => simp [hX1]
        match i with
        | 0 => simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fwMatrix, map_pow, hm_j]
        | 1 => simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fwMatrix, hm_j]
        | 2 =>
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fwMatrix]
          have := hiter 1 (![1, u, v, u ^ 2, u * v, v ^ 2] j)
          rw [hm_j] at this; exact this
        | 3 =>
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fwMatrix]
          have := hiter 2 (![1, u, v, u ^ 2, u * v, v ^ 2] j)
          rw [hm_j] at this; exact this
        | 4 =>
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fwMatrix]
          have := hiter 3 (![1, u, v, u ^ 2, u * v, v ^ 2] j)
          rw [hm_j] at this; exact this
        | 5 =>
          simp only [RingHom.mapMatrix_apply, Matrix.map_apply, fwMatrix]
          have := hiter 4 (![1, u, v, u ^ 2, u * v, v ^ 2] j)
          rw [hm_j] at this; exact this
      rw [hmap_fw]
      exact det_fwMatrix_eq_W10_of_deriv p φLS DLS g hDLS_X0 hDLS_φ hφLS_gy_ne
    have hS_eq : (fwMatrix p Du ![1, u, v, u ^ 2, u * v, v ^ 2]).det *
        φS (MvPolynomial.pderiv 1 g) ^ 10 = PowerSeries.C (2 : K) * φS (W10 p g) := by
      apply hιS_inj
      rw [map_mul, map_pow, hdet_LS, map_mul, map_ofNat, map_ofNat]
      exact div_mul_cancel₀ _ (pow_ne_zero 10 hφLS_gy_ne)
    have hX5_2W : PowerSeries.X ^ 5 ∣ PowerSeries.C (2 : K) * φS (W10 p g) := by
      rw [← hS_eq]; exact dvd_mul_of_dvd_left hX5_fw _
    have h2inv : PowerSeries.C (2 : K)⁻¹ * (PowerSeries.C (2 : K) * φS (W10 p g)) = φS (W10 p g) := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ h2K, map_one, one_mul]
    rw [← h2inv]; exact dvd_mul_of_dvd_right hX5_2W _
  -- Split on fK_y(α₀, β₀) ≠ 0 vs fK_x(α₀, β₀) ≠ 0 (using W10_swap!)
  have hX5_W10 : PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C ![α, β] (W10 p fK) := by
    by_cases hfy_ne : eval ![α0, β0] (MvPolynomial.pderiv 1 fK) ≠ 0
    · have hαd_ne : PowerSeries.constantCoeff (PowerSeries.derivative K α) ≠ 0 := by
        intro h0
        rw [h0, mul_zero, zero_add] at hch0
        have hβd0 := (mul_eq_zero.mp hch0).resolve_left hfy_ne
        rcases hderiv_nz with h | h
        · exact h h0
        · exact h hβd0
      exact hmain_case fK α β hφ_fK hα_p hβ_p hαd_ne (by rw [hconst_ev]; exact hfy_ne)
    · have hfy0 : eval ![α0, β0] (MvPolynomial.pderiv 1 fK) = 0 := not_not.mp hfy_ne
      have hfx_ne : eval ![α0, β0] (MvPolynomial.pderiv 0 fK) ≠ 0 :=
        hgrad_nz.resolve_right hfy_ne
      have hβd_ne : PowerSeries.constantCoeff (PowerSeries.derivative K β) ≠ 0 := by
        intro h0
        rw [h0, mul_zero, add_zero] at hch0
        have hαd0 := (mul_eq_zero.mp hch0).resolve_left hfx_ne
        rcases hderiv_nz with h | h
        · exact h hαd0
        · exact h h0
      let sw : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
        (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)).toRingHom
      have hev_sw : ∀ q : MvPolynomial (Fin 2) K,
          MvPolynomial.eval₂Hom PowerSeries.C ![β, α] (sw q) =
            MvPolynomial.eval₂Hom PowerSeries.C ![α, β] q := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C r => simp [sw]
        | add a b ha hb => simp [map_add, ha, hb]
        | mul_X a i ha =>
          rw [map_mul, map_mul, map_mul, ha]
          match i with
          | 0 => simp [sw, MvPolynomial.rename_X]
          | 1 => simp [sw, MvPolynomial.rename_X]
      have hpderiv_sw : MvPolynomial.pderiv 1 (sw fK) = sw (MvPolynomial.pderiv 0 fK) := by
        have h1 : ∀ q : MvPolynomial (Fin 2) K,
            MvPolynomial.pderiv 1 (sw q) = sw (MvPolynomial.pderiv 0 q) := by
          intro q
          induction q using MvPolynomial.induction_on with
          | C r => simp [sw]
          | add a b ha hb => simp [map_add, ha, hb]
          | mul_X a i ha =>
            rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, ha]
            match i with
            | 0 => simp [sw, MvPolynomial.rename_X, MvPolynomial.pderiv_X]
            | 1 => simp [sw, MvPolynomial.rename_X, MvPolynomial.pderiv_X]
        exact h1 fK
      have hres := hmain_case (sw fK) β α (by rw [hev_sw]; exact hφ_fK) hβ_p hα_p hβd_ne
        (by rw [hpderiv_sw, hev_sw, hconst_ev]; exact hfx_ne)
      rw [W10_swap p fK, hev_sw] at hres
      exact hres
  have hW10Z_hom : ((W10Z p n F).map ι).IsHomogeneous (2 * p + 10 * n - 14) :=
    (W10Z_isHomogeneous (p := p) hn3 (by omega) hFh).map ι
  rw [hev_hom hW10Z_hom]
  have hdeW : dehomogZ ((W10Z p n F).map ι) = W10 p fK := by
    have hcomm : ∀ P : MvPolynomial (Fin 3) (ZMod p),
        dehomogZ (P.map ι) = (dehomogZ P).map ι := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C r => simp [dehomogZ]
      | add a b ha hb => simp [map_add, ha, hb]
      | mul_X a i ha =>
        rw [map_mul, map_mul, map_mul, map_mul, ha]
        match i with | 0 => simp [dehomogZ] | 1 => simp [dehomogZ] | 2 => simp [dehomogZ]
    rw [hcomm, W10Z, dehomogZ_homogZ, ← W10_map, ← hcomm]
  rw [hdeW]
  exact dvd_mul_of_dvd_right hX5_W10 _

-- Helper for summing root multiplicities over a finite set of distinct roots
lemma sum_count_le_card {K : Type*} [DecidableEq K] (S : Finset K) (m : Multiset K) :
    ∑ x ∈ S, m.count x ≤ m.card := by
  classical
  have hle : (S.val.bind fun x => Multiset.replicate (m.count x) x) ≤ m := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_bind]
    by_cases ha : a ∈ S
    · have hsum : (S.val.map fun x => Multiset.count a (Multiset.replicate (m.count x) x)).sum =
          ∑ x ∈ S, Multiset.count a (Multiset.replicate (m.count x) x) := rfl
      rw [hsum, Finset.sum_eq_single a]
      · simp
      · intro x _ hne; simp [Multiset.count_replicate, hne]
      · intro h; exact absurd ha h
    · have hsum : (S.val.map fun x => Multiset.count a (Multiset.replicate (m.count x) x)).sum =
          ∑ x ∈ S, Multiset.count a (Multiset.replicate (m.count x) x) := rfl
      rw [hsum, Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro x hx
        have hne : x ≠ a := fun h => ha (h ▸ hx)
        simp [Multiset.count_replicate, hne]
  have hcard := Multiset.card_le_card hle
  rw [Multiset.card_bind] at hcard
  have heq : (S.val.map (Multiset.card ∘ fun x => Multiset.replicate (m.count x) x)).sum =
      ∑ x ∈ S, m.count x := by
    change ∑ x ∈ S, (Multiset.replicate (m.count x) x).card = ∑ x ∈ S, m.count x
    apply Finset.sum_congr rfl; intro x _; simp
  rwa [heq] at hcard

-- 6.6 Modular projective shear & generic projection helpers
noncomputable def shear3 {K : Type*} [CommRing K] (α β γ : K) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  MvPolynomial.eval₂Hom C ![X 0, X 1 + C α * X 0, X 2 - C γ * X 1 + C β * X 0]

noncomputable def shear3Inv {K : Type*} [CommRing K] (α β γ : K) :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 3) K :=
  MvPolynomial.eval₂Hom C ![X 0, X 1 - C α * X 0, X 2 + C γ * X 1 - C (β + γ * α) * X 0]

def shear3Vec {K : Type*} [CommRing K] (α β γ : K) (v : Fin 3 → K) : Fin 3 → K :=
  ![v 0, v 1 + α * v 0, v 2 - γ * v 1 + β * v 0]

noncomputable def aff1 {K : Type*} [CommRing K] :
    MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom C ![X 1, X 0, 1]

lemma shear3Inv_shear3 {K : Type*} [CommRing K] (α β γ : K) (P : MvPolynomial (Fin 3) K) :
    shear3Inv α β γ (shear3 α β γ P) = P := by
  have heq : (shear3Inv α β γ).comp (shear3 α β γ) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · ext r; simp [shear3, shear3Inv]
    · intro i; match i with
      | 0 => simp [shear3, shear3Inv]
      | 1 => simp only [RingHom.comp_apply, RingHom.id_apply, shear3, shear3Inv,
          MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_mul,
          MvPolynomial.eval₂Hom_C]; ring
      | 2 => simp only [RingHom.comp_apply, RingHom.id_apply, shear3, shear3Inv,
          MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          map_add, map_sub, map_mul, MvPolynomial.eval₂Hom_C]; ring
  exact RingHom.congr_fun heq P

lemma shear3_shear3Inv {K : Type*} [CommRing K] (α β γ : K) (P : MvPolynomial (Fin 3) K) :
    shear3 α β γ (shear3Inv α β γ P) = P := by
  have heq : (shear3 α β γ).comp (shear3Inv α β γ) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · ext r; simp [shear3, shear3Inv]
    · intro i; match i with
      | 0 => simp [shear3, shear3Inv]
      | 1 => simp only [RingHom.comp_apply, RingHom.id_apply, shear3, shear3Inv,
          MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_mul,
          MvPolynomial.eval₂Hom_C]; ring
      | 2 => simp only [RingHom.comp_apply, RingHom.id_apply, shear3, shear3Inv,
          MvPolynomial.eval₂Hom_X', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
          map_add, map_sub, map_mul, MvPolynomial.eval₂Hom_C]; ring
  exact RingHom.congr_fun heq P

lemma shear3_eval {K : Type*} [CommRing K] (α β γ : K)
    (P : MvPolynomial (Fin 3) K) (v : Fin 3 → K) :
    eval v (shear3 α β γ P) = eval (shear3Vec α β γ v) P := by
  have heq : (eval v).comp (shear3 α β γ) = eval (shear3Vec α β γ v) := by
    apply MvPolynomial.ringHom_ext'
    · ext r; simp [shear3]
    · intro i; match i with
      | 0 => simp [shear3, shear3Vec]
      | 1 => simp [shear3, shear3Vec]
      | 2 => simp [shear3, shear3Vec]
  exact RingHom.congr_fun heq P

lemma shear3_isHomogeneous {K : Type*} [CommRing K] (α β γ : K) {d : ℕ}
    {P : MvPolynomial (Fin 3) K} (hPh : P.IsHomogeneous d) :
    (shear3 α β γ P).IsHomogeneous d := by
  rw [P.as_sum, map_sum]
  apply IsHomogeneous.sum; intro s hs
  dsimp only [shear3]; rw [MvPolynomial.eval₂Hom_monomial]
  apply IsHomogeneous.C_mul
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ i : Fin 3, ((![X 0, X 1 + C α * X 0, X 2 - C γ * X 1 + C β * X 0] i :
      MvPolynomial (Fin 3) K) ^ s i).IsHomogeneous (s i) := by
    intro i; match i with
    | 0 => simpa using (isHomogeneous_X K (0 : Fin 3)).pow (s 0)
    | 1 => simpa using ((isHomogeneous_X K (1 : Fin 3)).add ((isHomogeneous_X K 0).C_mul α)).pow (s 1)
    | 2 =>
      have hlin : (X (2 : Fin 3) - C γ * X 1 + C β * X 0 : MvPolynomial (Fin 3) K).IsHomogeneous 1 :=
        ((isHomogeneous_X K 2).sub ((isHomogeneous_X K 1).C_mul γ)).add ((isHomogeneous_X K 0).C_mul β)
      simpa using hlin.pow (s 2)
  have hpr := IsHomogeneous.prod univ _ (fun i => s i) (fun i _ => h1 i)
  rwa [isHomogeneous_sum_eq hPh hs] at hpr

lemma shear3_pderiv_0 {K : Type*} [CommRing K] (α β γ : K) (P : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 0 (shear3 α β γ P) =
      shear3 α β γ (MvPolynomial.pderiv 0 P) +
      C α * shear3 α β γ (MvPolynomial.pderiv 1 P) +
      C β * shear3 α β γ (MvPolynomial.pderiv 2 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [shear3]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb, map_add, map_add, map_add, map_add, map_add, map_add]
    ring
  | mul_X a i ha =>
    rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_mul, ha]
    match i with
    | 0 => simp [shear3, MvPolynomial.pderiv_X]; ring
    | 1 => simp [shear3, MvPolynomial.pderiv_X]; ring
    | 2 => simp [shear3, MvPolynomial.pderiv_X]; ring

lemma aff1_pderiv_1 {K : Type*} [CommRing K] (P : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 1 (aff1 P) = aff1 (MvPolynomial.pderiv 0 P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [aff1]
  | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
  | mul_X a i ha =>
    rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, ha]
    match i with
    | 0 => simp [aff1, MvPolynomial.pderiv_X]
    | 1 => simp [aff1, MvPolynomial.pderiv_X]
    | 2 => simp [aff1, MvPolynomial.pderiv_X]

lemma map_dehomog1_finSuccEquiv {K : Type*} [CommRing K] (P : MvPolynomial (Fin 3) K) :
    (MvPolynomial.finSuccEquiv K 2 P).map dehomog1 = mv2ToPolyY K (aff1 P) := by
  have heq : (Polynomial.mapRingHom (dehomog1 (K := K))).comp
      (MvPolynomial.finSuccEquiv K 2).toRingHom =
      (mv2ToPolyY K).comp aff1 := by
    apply MvPolynomial.ringHom_ext'
    · apply RingHom.ext; intro c
      change Polynomial.map dehomog1 (MvPolynomial.finSuccEquiv K 2 (C c)) = mv2ToPolyY K (aff1 (C c))
      have hC : MvPolynomial.finSuccEquiv K 2 (C c) = Polynomial.C (C c) := by
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, Polynomial.algebraMap_apply,
          MvPolynomial.algebraMap_eq]
      rw [hC, Polynomial.map_C]
      simp [aff1, dehomog1, mv2ToPolyY]
    · intro i; match i with
      | 0 =>
        change Polynomial.map dehomog1 (MvPolynomial.finSuccEquiv K 2 (X 0)) = mv2ToPolyY K (aff1 (X 0))
        rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X]
        simp [aff1, mv2ToPolyY]
      | 1 =>
        change Polynomial.map dehomog1 (MvPolynomial.finSuccEquiv K 2 (X (Fin.succ 0))) = _
        rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
        simp [aff1, dehomog1, mv2ToPolyY]
      | 2 =>
        change Polynomial.map dehomog1 (MvPolynomial.finSuccEquiv K 2 (X (Fin.succ 1))) = _
        rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
        simp [aff1, dehomog1, mv2ToPolyY]
  exact RingHom.congr_fun heq P

lemma finSuccEquiv_coeff_hom {K : Type*} [CommRing K] {m : ℕ}
    {P : MvPolynomial (Fin 3) K} (hPh : P.IsHomogeneous m) :
    (∀ k ≤ m, ((MvPolynomial.finSuccEquiv K 2 P).coeff k).IsHomogeneous (m - k)) ∧
    (∀ k, m < k → (MvPolynomial.finSuccEquiv K 2 P).coeff k = 0) := by
  refine ⟨?_, ?_⟩
  · intro k hk s hs
    rw [MvPolynomial.finSuccEquiv_coeff_coeff] at hs
    have hdeg := hPh hs
    rw [weight_one_eq_degree, Finsupp.degree_apply] at hdeg
    have hsum : ∑ i ∈ (Finsupp.cons k s).support, (Finsupp.cons k s) i =
        ∑ i : Fin 3, (Finsupp.cons k s) i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
    rw [hsum, Fin.sum_univ_three] at hdeg
    have h0 : (Finsupp.cons k s) 0 = k := Finsupp.cons_zero k s
    have h1 : (Finsupp.cons k s) 1 = s 0 := Finsupp.cons_succ (0 : Fin 2) k s
    have h2 : (Finsupp.cons k s) 2 = s 1 := Finsupp.cons_succ (1 : Fin 2) k s
    rw [h0, h1, h2] at hdeg
    rw [weight_one_eq_degree, Finsupp.degree_apply]
    have hsum2 : ∑ i ∈ s.support, s i = ∑ i : Fin 2, s i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
    rw [hsum2, Fin.sum_univ_two]; omega
  · intro k hk
    ext s
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_zero]
    by_contra hne
    have hdeg := hPh hne
    rw [weight_one_eq_degree, Finsupp.degree_apply] at hdeg
    have hsum : ∑ i ∈ (Finsupp.cons k s).support, (Finsupp.cons k s) i =
        ∑ i : Fin 3, (Finsupp.cons k s) i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => Finsupp.notMem_support_iff.mp hi)
    rw [hsum, Fin.sum_univ_three] at hdeg
    have h0 : (Finsupp.cons k s) 0 = k := Finsupp.cons_zero k s
    rw [h0] at hdeg; omega

lemma finSuccEquiv_coeff_top {K : Type*} [CommRing K] {m : ℕ}
    {P : MvPolynomial (Fin 3) K} (hPh : P.IsHomogeneous m) :
    (MvPolynomial.finSuccEquiv K 2 P).coeff m = C (eval ![1, 0, 0] P) := by
  have hhom0 : ((MvPolynomial.finSuccEquiv K 2 P).coeff m).IsHomogeneous 0 := by
    have := (finSuccEquiv_coeff_hom hPh).1 m le_rfl; rwa [Nat.sub_self] at this
  have hC_eq := isHomogeneous_zero_eq_C hhom0
  rw [hC_eq]
  congr 1
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  have hcons : Finsupp.cons m (0 : Fin 2 →₀ ℕ) = Finsupp.single (0 : Fin 3) m := by
    ext i; match i with
    | 0 => simp [Finsupp.cons_zero]
    | 1 => change (Finsupp.cons m (0 : Fin 2 →₀ ℕ)) (Fin.succ 0) = _; rw [Finsupp.cons_succ]; simp
    | 2 => change (Finsupp.cons m (0 : Fin 2 →₀ ℕ)) (Fin.succ 1) = _; rw [Finsupp.cons_succ]; simp
  rw [hcons]
  conv_rhs => rw [P.as_sum]
  rw [map_sum]
  by_cases hmem : Finsupp.single (0 : Fin 3) m ∈ P.support
  · rw [Finset.sum_eq_single (Finsupp.single 0 m)]
    · rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]; simp
    · intro s hs hne
      rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
      have hdeg := isHomogeneous_sum_eq hPh hs; rw [Fin.sum_univ_three] at hdeg
      by_cases hs1 : s 1 = 0
      · have hs2 : s 2 ≠ 0 := fun h2 => hne (by ext i; match i with | 0 => simp; omega | 1 => simp [hs1] | 2 => simp [h2])
        simp [zero_pow hs2]
      · simp [zero_pow hs1]
    · intro h; exact absurd hmem h
  · rw [MvPolynomial.notMem_support_iff.mp hmem]
    symm; apply Finset.sum_eq_zero
    intro s hs
    rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_three]
    have hdeg := isHomogeneous_sum_eq hPh hs; rw [Fin.sum_univ_three] at hdeg
    by_cases hs1 : s 1 = 0
    · have hs2 : s 2 ≠ 0 := fun h2 => hmem (by
        have : s = Finsupp.single (0 : Fin 3) m := by ext i; match i with | 0 => simp; omega | 1 => simp [hs1] | 2 => simp [h2]
        exact this ▸ hs)
      simp [zero_pow hs2]
    · simp [zero_pow hs1]

-- Helpers for generic projection center
lemma eval_aff0_eq {K : Type*} [CommRing K] (P : MvPolynomial (Fin 3) K) (w : Fin 2 → K) :
    eval w (MvPolynomial.eval₂Hom C ![1, X 0, X 1] P) = eval ![1, w 0, w 1] P := by
  have heq : (eval w).comp (MvPolynomial.eval₂Hom C ![1, X 0, X 1]) = eval ![1, w 0, w 1] := by
    apply MvPolynomial.ringHom_ext'
    · ext r; simp
    · intro i; match i with | 0 => simp | 1 => simp | 2 => simp
  exact RingHom.congr_fun heq P

lemma aff0_ne_zero_of_isHomogeneous {K : Type*} [CommRing K] {d : ℕ}
    {P : MvPolynomial (Fin 3) K} (hPh : P.IsHomogeneous d) (hP0 : P ≠ 0) :
    MvPolynomial.eval₂Hom C (![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) P ≠ 0 := by
  intro h0
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hP0
  let s' : Fin 2 →₀ ℕ := Finsupp.single 0 (s 1) + Finsupp.single 1 (s 2)
  have hc := congrArg (fun q : MvPolynomial (Fin 2) K => q.coeff s') h0
  rw [MvPolynomial.coeff_zero, P.as_sum, map_sum, MvPolynomial.coeff_sum] at hc
  have hmon : ∀ t : Fin 3 →₀ ℕ,
      MvPolynomial.eval₂Hom C (![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K)
        (monomial t (P.coeff t)) =
      monomial (Finsupp.single (0 : Fin 2) (t 1) + Finsupp.single 1 (t 2)) (P.coeff t) := by
    intro t
    rw [MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
      Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_pow, one_mul]
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
    simp
  rw [Finset.sum_eq_single s] at hc
  · rw [hmon, MvPolynomial.coeff_monomial] at hc
    simp only [s', ↓reduceIte] at hc
    exact MvPolynomial.mem_support_iff.mp hs hc
  · intro t ht hne
    rw [hmon, MvPolynomial.coeff_monomial]
    have hne' : Finsupp.single (0 : Fin 2) (t 1) + Finsupp.single 1 (t 2) ≠ s' := by
      intro heq; apply hne
      have h1 : t 1 = s 1 := by have := congrFun (congrArg DFunLike.coe heq) 0; simpa [s'] using this
      have h2 : t 2 = s 2 := by have := congrFun (congrArg DFunLike.coe heq) 1; simpa [s'] using this
      have hdt := isHomogeneous_sum_eq hPh ht
      have hds := isHomogeneous_sum_eq hPh hs
      rw [Fin.sum_univ_three] at hdt hds
      ext i; match i with | 0 => omega | 1 => exact h1 | 2 => exact h2
    simp [hne']
  · intro h; exact absurd hs h

lemma eval_axis_poly {K : Type*} [CommRing K] (u : Fin 3 → K) (i : Fin 3) (w : Fin 2 → K)
    (Q : MvPolynomial (Fin 3) K) :
    eval w (MvPolynomial.eval₂Hom C (fun j =>
      C (u i) * ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) j) -
      ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) i) * C (u j)) Q) =
    eval (fun j => u i * (![1, w 0, w 1] j) - (![1, w 0, w 1] i) * u j) Q := by
  have h012 : ∀ idx : Fin 3,
      eval w ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) idx) = ![1, w 0, w 1] idx :=
    fun idx => by match idx with | 0 => simp | 1 => simp | 2 => simp
  have heq : (eval w).comp (MvPolynomial.eval₂Hom C (fun j =>
        C (u i) * ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) j) -
        ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) i) * C (u j))) =
      eval (fun j => u i * (![1, w 0, w 1] j) - (![1, w 0, w 1] i) * u j) := by
    apply MvPolynomial.ringHom_ext'
    · ext r; simp
    · intro k
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', map_sub, map_mul, eval_C, eval_X,
        h012 k, h012 i]
  exact RingHom.congr_fun heq Q

lemma axis_poly_ne_zero {K : Type*} [Field K] {n : ℕ} {FK : MvPolynomial (Fin 3) K}
    (hFK_h : FK.IsHomogeneous n) (he0K : eval ![1, 0, 0] FK ≠ 0) (he2K : eval ![0, 0, 1] FK ≠ 0)
    (u : Fin 3 → K) (i : Fin 3) (hui : u i ≠ 0) :
    MvPolynomial.eval₂Hom C (fun j =>
      C (u i) * ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) j) -
      ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) i) * C (u j)) FK ≠ 0 := by
  intro h0
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl
  · have h1 := congrArg (eval ![u 1 / u 0, (1 + u 2) / u 0]) h0
    rw [map_zero, eval_axis_poly] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have hvec : (fun j : Fin 3 => u 0 * (![1, u 1 / u 0, (1 + u 2) / u 0] j) - 1 * u j) = ![0, 0, 1] := by
      ext j; match j with
      | 0 => simp
      | 1 => simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul]
             rw [mul_div_cancel₀ _ hui, sub_self]
      | 2 => simp only [Matrix.cons_val, one_mul]
             rw [mul_div_cancel₀ _ hui]; ring
    rw [hvec] at h1; exact he2K h1
  · have h1 := congrArg (eval ![0, 0]) h0
    rw [map_zero, eval_axis_poly] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have hvec : (fun j : Fin 3 => u 1 * (![1, 0, 0] j) - 0 * u j) =
        u 1 • ![1, 0, 0] := by ext j; match j with | 0 => simp | 1 => simp | 2 => simp
    rw [hvec, isHomogeneous_eval_smul hFK_h] at h1
    exact mul_ne_zero (pow_ne_zero n hui) he0K h1
  · have h1 := congrArg (eval ![0, 0]) h0
    rw [map_zero, eval_axis_poly] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have hvec : (fun j : Fin 3 => u 2 * (![1, 0, 0] j) - (![1, 0, 0] 2) * u j) =
        u 2 • ![1, 0, 0] := by ext j; match j with | 0 => simp | 1 => simp | 2 => simp
    rw [hvec, isHomogeneous_eval_smul hFK_h] at h1
    exact mul_ne_zero (pow_ne_zero n hui) he0K h1

-- Generic projection center (α, β) and line-at-infinity slope γ
lemma exists_generic_projection {K : Type*} [Field K] [IsAlgClosed K]
    {n D : ℕ} {FK HK : MvPolynomial (Fin 3) K}
    (hFK_h : FK.IsHomogeneous n) (hHK_h : HK.IsHomogeneous D)
    (hFK_ne : FK ≠ 0) (hHK_ne : HK ≠ 0)
    (he0K : eval ![1, 0, 0] FK ≠ 0) (he2K : eval ![0, 0, 1] FK ≠ 0)
    (ZK : Finset (Fin 3 → K))
    (hZK_norm : ∀ u ∈ ZK, IsNorm u)
    (hZK_F0 : ∀ u ∈ ZK, eval u FK = 0) :
    ∃ α β γ : K,
      eval ![1, α, β] FK ≠ 0 ∧
      eval ![1, α, β] HK ≠ 0 ∧
      (∀ u ∈ ZK, ∀ v ∈ ZK, u ≠ v →
        (u 1 - α * u 0) * (v 2 - β * v 0) - (u 2 - β * u 0) * (v 1 - α * v 0) ≠ 0) ∧
      (∀ u ∈ ZK, (eval u (MvPolynomial.pderiv 0 FK) ≠ 0 ∨ eval u (MvPolynomial.pderiv 1 FK) ≠ 0 ∨
          eval u (MvPolynomial.pderiv 2 FK) ≠ 0) →
        eval u (MvPolynomial.pderiv 0 FK) + α * eval u (MvPolynomial.pderiv 1 FK) +
          β * eval u (MvPolynomial.pderiv 2 FK) ≠ 0) ∧
      (∀ u ∈ ZK, ∀ i : Fin 3, u i ≠ 0 →
        eval (fun j => u i * (![1, α, β] j) - (![1, α, β] i) * u j) FK ≠ 0) ∧
      (∀ u ∈ ZK, (u 2 - β * u 0) + γ * (u 1 - α * u 0) ≠ 0) := by
  classical
  let aff0 : MvPolynomial (Fin 3) K →+* MvPolynomial (Fin 2) K :=
    MvPolynomial.eval₂Hom C ![1, X 0, X 1]
  let P_sec : (Fin 3 → K) → (Fin 3 → K) → MvPolynomial (Fin 2) K := fun u v =>
    C (cross3 u v 0) + C (cross3 u v 1) * X 0 + C (cross3 u v 2) * X 1
  let P_tan : (Fin 3 → K) → MvPolynomial (Fin 2) K := fun u =>
    if eval u (MvPolynomial.pderiv 0 FK) ≠ 0 ∨ eval u (MvPolynomial.pderiv 1 FK) ≠ 0 ∨
        eval u (MvPolynomial.pderiv 2 FK) ≠ 0 then
      C (eval u (MvPolynomial.pderiv 0 FK)) +
      C (eval u (MvPolynomial.pderiv 1 FK)) * X 0 +
      C (eval u (MvPolynomial.pderiv 2 FK)) * X 1
    else 1
  let P_axis : (Fin 3 → K) → Fin 3 → MvPolynomial (Fin 2) K := fun u i =>
    if u i ≠ 0 then
      MvPolynomial.eval₂Hom C (fun j =>
        C (u i) * ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) j) -
        ((![1, X 0, X 1] : Fin 3 → MvPolynomial (Fin 2) K) i) * C (u j)) FK
    else 1
  have hlin_ne : ∀ (a b c : K), (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
      (C a + C b * X (0 : Fin 2) + C c * X 1 : MvPolynomial (Fin 2) K) ≠ 0 := by
    intro a b c hne h0
    have e0 := congrArg (eval ![0, 0]) h0
    have e1 := congrArg (eval ![1, 0]) h0
    have e2 := congrArg (eval ![0, 1]) h0
    simp only [map_add, map_mul, eval_C, eval_X, map_zero, Matrix.cons_val_zero,
      Matrix.cons_val_one, mul_zero, mul_one, add_zero] at e0 e1 e2
    rcases hne with h | h | h
    · exact h e0
    · exact h (by linear_combination e1 - e0)
    · exact h (by linear_combination e2 - e0)
  have hPsec_ne : ∀ u ∈ ZK, ∀ v ∈ ZK.erase u, P_sec u v ≠ 0 := by
    intro u hu v hv
    have hcr := cross3_ne_zero_of_isNorm_ne (hZK_norm u hu)
      (hZK_norm v (Finset.mem_erase.mp hv).2) (Finset.mem_erase.mp hv).1.symm
    apply hlin_ne
    by_contra hall
    rw [not_or, not_or, not_not, not_not, not_not] at hall
    rcases hall with ⟨h0, h1, h2⟩
    apply hcr; ext i; match i with | 0 => exact h0 | 1 => exact h1 | 2 => exact h2
  have hPtan_ne : ∀ u ∈ ZK, P_tan u ≠ 0 := by
    intro u _; dsimp only [P_tan]
    split_ifs with hsm
    · exact hlin_ne _ _ _ hsm
    · exact one_ne_zero
  have hPaxis_ne : ∀ u ∈ ZK, ∀ i : Fin 3, P_axis u i ≠ 0 := by
    intro u _ i; dsimp only [P_axis]
    split_ifs with hui
    · exact axis_poly_ne_zero hFK_h he0K he2K u i hui
    · exact one_ne_zero
  let G : MvPolynomial (Fin 2) K :=
    aff0 FK * aff0 HK *
      (∏ u ∈ ZK, ∏ v ∈ ZK.erase u, P_sec u v) *
      (∏ u ∈ ZK, P_tan u) *
      (∏ u ∈ ZK, ∏ i : Fin 3, P_axis u i)
  have hG_ne : G ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (aff0_ne_zero_of_isHomogeneous hFK_h hFK_ne) (aff0_ne_zero_of_isHomogeneous hHK_h hHK_ne))
      (Finset.prod_ne_zero_iff.mpr fun u hu => Finset.prod_ne_zero_iff.mpr (hPsec_ne u hu)))
      (Finset.prod_ne_zero_iff.mpr hPtan_ne))
      (Finset.prod_ne_zero_iff.mpr fun u hu => Finset.prod_ne_zero_iff.mpr fun i _ => hPaxis_ne u hu i)
  obtain ⟨w, hw⟩ := exists_eval_ne_zero_mv2 hG_ne
  set α := w 0
  set β := w 1
  dsimp only [G] at hw
  simp only [map_mul, map_prod] at hw
  have hFK_O : eval ![1, α, β] FK ≠ 0 := by
    have := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hw)))
    rwa [eval_aff0_eq] at this
  have hHK_O : eval ![1, α, β] HK ≠ 0 := by
    have := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hw)))
    rwa [eval_aff0_eq] at this
  let Pγ : Polynomial K := ∏ u ∈ ZK,
    (Polynomial.C (u 2 - β * u 0) + Polynomial.C (u 1 - α * u 0) * Polynomial.X)
  have hPγ_ne : Pγ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu h0
    have hc0 : u 2 - β * u 0 = 0 := by
      have := congrArg (fun p : Polynomial K => p.coeff 0) h0; simpa using this
    have hc1 : u 1 - α * u 0 = 0 := by
      have := congrArg (fun p : Polynomial K => p.coeff 1) h0; simpa using this
    have hu0_ne : u 0 ≠ 0 := by
      intro hu0
      have hu1 : u 1 = 0 := by rw [hu0, mul_zero, sub_zero] at hc1; exact hc1
      have hu2 : u 2 = 0 := by rw [hu0, mul_zero, sub_zero] at hc0; exact hc0
      apply isNorm_ne_zero (hZK_norm u hu)
      ext i; match i with | 0 => exact hu0 | 1 => exact hu1 | 2 => exact hu2
    have hu_eq : u = u 0 • ![1, α, β] := by
      ext i; match i with
      | 0 => change u 0 = u 0 * 1; ring
      | 1 => change u 1 = u 0 * α; linear_combination hc1
      | 2 => change u 2 = u 0 * β; linear_combination hc0
    have hF0 := hZK_F0 u hu
    rw [hu_eq, isHomogeneous_eval_smul hFK_h] at hF0
    exact mul_ne_zero (pow_ne_zero n hu0_ne) hFK_O hF0
  have : Infinite K := IsAlgClosed.instInfinite
  obtain ⟨γ, hγ⟩ := exists_notMem_of_isAlgClosed (Pγ.roots.toFinset)
  have hPγ_eval : Polynomial.eval γ Pγ ≠ 0 := fun h0 =>
    hγ (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPγ_ne).mpr h0))
  refine ⟨α, β, γ, hFK_O, hHK_O, ?_, ?_, ?_, ?_⟩
  · intro u hu v hv hne
    have hprod := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hw))
    have h1 := Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hprod u hu) v
      (Finset.mem_erase.mpr ⟨hne.symm, hv⟩)
    dsimp only [P_sec] at h1
    simp only [map_add, map_mul, eval_C, eval_X] at h1
    have hdet_eq : (u 1 - α * u 0) * (v 2 - β * v 0) - (u 2 - β * u 0) * (v 1 - α * v 0) =
        cross3 u v 0 + cross3 u v 1 * α + cross3 u v 2 * β := by
      dsimp only [cross3]; ring
    rw [hdet_eq]; exact h1
  · intro u hu hsm
    have hprod := right_ne_zero_of_mul (left_ne_zero_of_mul hw)
    have h1 := Finset.prod_ne_zero_iff.mp hprod u hu
    dsimp only [P_tan] at h1
    simp only [hsm, ↓reduceIte] at h1
    simp only [map_add, map_mul, eval_C, eval_X] at h1
    have : eval u (MvPolynomial.pderiv 0 FK) + α * eval u (MvPolynomial.pderiv 1 FK) +
        β * eval u (MvPolynomial.pderiv 2 FK) =
        eval u (MvPolynomial.pderiv 0 FK) + eval u (MvPolynomial.pderiv 1 FK) * α +
        eval u (MvPolynomial.pderiv 2 FK) * β := by ring
    rw [this]; exact h1
  · intro u hu i hui
    have hprod := right_ne_zero_of_mul hw
    have h1 := Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hprod u hu) i (mem_univ i)
    dsimp only [P_axis] at h1
    split_ifs at h1
    rwa [eval_axis_poly] at h1
  · intro u hu h0
    apply hPγ_eval
    dsimp only [Pγ]; rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero hu
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    linear_combination h0

-- Shared rotation / shear-shift algebra helpers
lemma eval_rot3_eq {R : Type*} [CommRing R] (v : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    eval v (rot3 P) = eval (v ∘ cyc3) P := by
  have heq : (eval v).comp rot3.toRingHom = eval (v ∘ cyc3) := by
    apply MvPolynomial.ringHom_ext'
    · ext c; simp [rot3]
    · intro i; simp [rot3_X]
  exact RingHom.congr_fun heq P

lemma eval_rot3_symm_eq {R : Type*} [CommRing R] (v : Fin 3 → R) (P : MvPolynomial (Fin 3) R) :
    eval v (rot3.symm P) = eval (v ∘ cyc3.symm) P := by
  have heq : (eval v).comp rot3.symm.toRingHom = eval (v ∘ cyc3.symm) := by
    apply MvPolynomial.ringHom_ext'
    · ext c; simp [rot3]
    · intro i
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      have hX : rot3.symm (X i : MvPolynomial (Fin 3) R) = X (cyc3.symm i) :=
        MvPolynomial.rename_X cyc3.symm i
      rw [hX, eval_X, eval_X]; rfl
  exact RingHom.congr_fun heq P

lemma shear3_MT_u {K : Type*} [Field K] (α β γ : K) (u : Fin 3 → K)
    (hLu : (u 2 - β * u 0) + γ * (u 1 - α * u 0) ≠ 0) :
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    shear3Vec α β γ ![u 0 / Lu, (u 1 - α * u 0) / Lu, 1] = Lu⁻¹ • u := by
  intro Lu
  have hinv : Lu * Lu⁻¹ = 1 := mul_inv_cancel₀ hLu
  have h1 : Lu * ((u 1 - α * u 0) / Lu) = u 1 - α * u 0 := mul_div_cancel₀ _ hLu
  have h2 : Lu * (u 0 / Lu) = u 0 := mul_div_cancel₀ _ hLu
  ext i; match i with
  | 0 => change u 0 / Lu = Lu⁻¹ * u 0; rw [div_eq_inv_mul]
  | 1 =>
    change (u 1 - α * u 0) / Lu + α * (u 0 / Lu) = Lu⁻¹ * u 1
    apply mul_left_cancel₀ hLu
    linear_combination h1 + α * h2 - u 1 * hinv
  | 2 =>
    change 1 - γ * ((u 1 - α * u 0) / Lu) + β * (u 0 / Lu) = Lu⁻¹ * u 2
    apply mul_left_cancel₀ hLu
    have hLdef : Lu = (u 2 - β * u 0) + γ * (u 1 - α * u 0) := rfl
    linear_combination hLdef - γ * h1 + β * h2 - u 2 * hinv

lemma shear3_tr_ev0 {K : Type*} [Field K] (α β γ : K) (u : Fin 3 → K)
    (hLu : (u 2 - β * u 0) + γ * (u 1 - α * u 0) ≠ 0) (P : MvPolynomial (Fin 3) K) :
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C ((u 1 - α * u 0) / Lu) + X 0, C (u 0 / Lu) + X 1]
    eval ![0, 0] (tr_u (aff1 (shear3 α β γ P))) = eval (Lu⁻¹ • u) P := by
  intro Lu tr_u
  have heq : ((eval ![0, 0]).comp tr_u).comp aff1 = eval ![u 0 / Lu, (u 1 - α * u 0) / Lu, 1] := by
    apply MvPolynomial.ringHom_ext'
    · ext r; simp [tr_u, aff1]
    · intro i; match i with | 0 => simp [tr_u, aff1] | 1 => simp [tr_u, aff1] | 2 => simp [tr_u, aff1]
  have h1 := RingHom.congr_fun heq (shear3 α β γ P)
  simp only [RingHom.comp_apply] at h1
  rw [h1, shear3_eval, shear3_MT_u α β γ u hLu]

lemma shear3_tr_poly {K : Type*} [CommRing K] (xu yu : K) (g : MvPolynomial (Fin 2) K) :
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let τx : Polynomial K →+* Polynomial K :=
      Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C xu)
    mv2ToPolyY K (tr_u g) =
      ((mv2ToPolyY K g).map τx).comp (Polynomial.X + Polynomial.C (Polynomial.C yu)) := by
  intro tr_u τx
  induction g using MvPolynomial.induction_on with
  | C c => simp [tr_u, mv2ToPolyY, τx]
  | add a b ha hb => rw [map_add, map_add, map_add, Polynomial.map_add, Polynomial.add_comp, ha, hb]
  | mul_X a i ha =>
    rw [map_mul, map_mul, map_mul, Polynomial.map_mul, Polynomial.mul_comp, ha]; congr 1
    match i with | 0 => simp [tr_u, mv2ToPolyY, τx, add_comm] | 1 => simp [tr_u, mv2ToPolyY, τx, add_comm]

lemma shear3_shift_deg_props {K : Type*} [Field K] {n D : ℕ}
    {FK HK : MvPolynomial (Fin 3) K} (hFK_h : FK.IsHomogeneous n) (hHK_h : HK.IsHomogeneous D)
    (α β γ xu yu : K) (hFK_O : eval ![1, α, β] FK ≠ 0) :
    let cF := eval ![1, α, β] FK
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let f_u := tr_u (aff1 (C cF⁻¹ * shear3 α β γ FK))
    let h_u := tr_u (aff1 (shear3 α β γ HK))
    (mv2ToPolyY K f_u).Monic ∧ (mv2ToPolyY K f_u).natDegree = n ∧ (mv2ToPolyY K h_u).natDegree ≤ D := by
  intro cF tr_u f_u h_u
  have hF'_h : (C cF⁻¹ * shear3 α β γ FK).IsHomogeneous n := (shear3_isHomogeneous α β γ hFK_h).C_mul _
  have hF'_e0 : eval ![1, 0, 0] (C cF⁻¹ * shear3 α β γ FK) = 1 := by
    rw [map_mul, eval_C, shear3_eval]
    have hM : shear3Vec α β γ ![1, 0, 0] = ![1, α, β] := by
      ext i; match i with | 0 => simp [shear3Vec] | 1 => simp [shear3Vec] | 2 => simp [shear3Vec]
    rw [hM]; exact inv_mul_cancel₀ hFK_O
  have hf0_c : (MvPolynomial.finSuccEquiv K 2 (C cF⁻¹ * shear3 α β γ FK)).coeff n = 1 := by
    rw [finSuccEquiv_coeff_top hF'_h, hF'_e0, map_one]
  have hf0_nd : (MvPolynomial.finSuccEquiv K 2 (C cF⁻¹ * shear3 α β γ FK)).natDegree = n :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (finSuccEquiv_coeff_hom hF'_h).2)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hf0_c]; exact one_ne_zero))
  have hf0_m : (MvPolynomial.finSuccEquiv K 2 (C cF⁻¹ * shear3 α β γ FK)).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hf0_nd]; exact hf0_c
  have haff_m : (mv2ToPolyY K (aff1 (C cF⁻¹ * shear3 α β γ FK))).Monic := by
    rw [← map_dehomog1_finSuccEquiv]; exact hf0_m.map dehomog1
  have haff_nd : (mv2ToPolyY K (aff1 (C cF⁻¹ * shear3 α β γ FK))).natDegree = n := by
    rw [← map_dehomog1_finSuccEquiv, hf0_m.natDegree_map, hf0_nd]
  let τx : Polynomial K →+* Polynomial K := Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C xu)
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [f_u]; rw [shear3_tr_poly]
    exact (haff_m.map τx).comp (Polynomial.monic_X_add_C _) (by simp)
  · dsimp only [f_u]
    rw [shear3_tr_poly, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one,
      haff_m.natDegree_map, haff_nd]
  · dsimp only [h_u]
    rw [shear3_tr_poly, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    refine Polynomial.natDegree_map_le.trans ?_
    rw [← map_dehomog1_finSuccEquiv]
    exact Polynomial.natDegree_map_le.trans
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (finSuccEquiv_coeff_hom (shear3_isHomogeneous α β γ hHK_h)).2)

-- Smooth chart dispatch helper: X^5 ∣ H(Xvec)
lemma smooth_point_X5_HK {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F H : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (hHZ : F ∣ W10Z p n F - X 2 ^ 6 * H)
    (hHX : F ∣ W10X p n F - X 0 ^ 6 * H)
    (hHY : F ∣ W10Y p n F - X 1 ^ 6 * H)
    {q : Fin 3 → ZMod p} (hq_norm : IsNorm q)
    (Xvec : Fin 3 → PowerSeries K)
    (hXvec_F : MvPolynomial.eval₂Hom PowerSeries.C Xvec (F.map ι) = 0)
    (c : K) (hc : c ≠ 0)
    (hXvec_const : ∀ j : Fin 3, PowerSeries.constantCoeff (Xvec j) = c * ι (q j))
    (hsm_ex : ∃ j : Fin 3, eval (ι ∘ q) (MvPolynomial.pderiv j (F.map ι)) ≠ 0)
    (hXvec_lin : ¬ ∃ lam : K, ∀ j : Fin 3,
      PowerSeries.constantCoeff (PowerSeries.derivative K (Xvec j)) =
        lam * PowerSeries.constantCoeff (Xvec j)) :
    PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C Xvec (H.map ι) := by
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hX5_from_chart : ∀ (i₀ : Fin 3) (W : MvPolynomial (Fin 3) (ZMod p)),
      q i₀ ≠ 0 → F ∣ W - X i₀ ^ 6 * H →
      PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C Xvec (W.map ι) →
      PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C Xvec (H.map ι) := by
    intro i₀ W hqi hFW hX5W
    rcases hFW with ⟨Q, hQ⟩
    have h1 := congrArg (MvPolynomial.eval₂Hom PowerSeries.C Xvec ∘ MvPolynomial.map ι) hQ
    simp only [Function.comp_apply, map_sub, map_mul, map_pow, MvPolynomial.map_X,
      MvPolynomial.eval₂Hom_X'] at h1
    rw [hXvec_F, zero_mul, sub_eq_zero] at h1
    have hXi_unit : IsUnit (Xvec i₀) := by
      rw [PowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, hXvec_const i₀]
      exact mul_ne_zero hc (fun h => hqi (hι_inj (h.trans (map_zero ι).symm)))
    rcases hXi_unit.pow 6 with ⟨u6, hu6⟩
    have hback : MvPolynomial.eval₂Hom PowerSeries.C Xvec (H.map ι) =
        ((u6⁻¹ : (PowerSeries K)ˣ) : PowerSeries K) *
          MvPolynomial.eval₂Hom PowerSeries.C Xvec (W.map ι) := by
      rw [h1, ← hu6, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hback]; exact dvd_mul_of_dvd_right hX5W _
  by_cases hq2 : q 2 ≠ 0
  · exact hX5_from_chart 2 (W10Z p n F) hq2 hHZ
      (smooth_chart_X5_dvd ι hp2 hn3 h2np hFh hq2 Xvec hXvec_F ⟨c, hc, hXvec_const⟩ hsm_ex hXvec_lin)
  · by_cases hq0 : q 0 ≠ 0
    · let F₁ := rot3.symm F
      let q₁ : Fin 3 → ZMod p := q ∘ cyc3
      let Xvec₁ : Fin 3 → PowerSeries K := Xvec ∘ cyc3
      have hrot_ev : ∀ (P : MvPolynomial (Fin 3) (ZMod p)),
          MvPolynomial.eval₂Hom PowerSeries.C Xvec₁ ((rot3.symm P).map ι) =
            MvPolynomial.eval₂Hom PowerSeries.C Xvec (P.map ι) := by
        intro P
        have heq : ((MvPolynomial.eval₂Hom PowerSeries.C Xvec₁).comp (MvPolynomial.map ι)).comp
            rot3.symm.toRingHom = (MvPolynomial.eval₂Hom PowerSeries.C Xvec).comp (MvPolynomial.map ι) := by
          apply MvPolynomial.ringHom_ext'
          · ext r; simp [rot3]
          · intro i
            simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
            have hX : rot3.symm (X i : MvPolynomial (Fin 3) (ZMod p)) = X (cyc3.symm i) :=
              MvPolynomial.rename_X cyc3.symm i
            rw [hX, MvPolynomial.map_X, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X',
              MvPolynomial.eval₂Hom_X']; simp [Xvec₁]
        exact RingHom.congr_fun heq P
      have hX1_sm : ∃ j : Fin 3, eval (ι ∘ q₁) (MvPolynomial.pderiv j (F₁.map ι)) ≠ 0 := by
        obtain ⟨j, hj⟩ := hsm_ex; refine ⟨cyc3.symm j, ?_⟩
        have hcomm : F₁.map ι = rot3.symm (F.map ι) := by dsimp only [F₁, rot3]; simp [MvPolynomial.map_rename]
        rw [hcomm, pderiv_rot3_symm, Equiv.apply_symm_apply, eval_rot3_symm_eq]
        have hqeq : (ι ∘ q₁) ∘ cyc3.symm = ι ∘ q := by ext i; simp [q₁]
        rwa [hqeq]
      have hX1_lin : ¬ ∃ lam : K, ∀ j : Fin 3,
          PowerSeries.constantCoeff (PowerSeries.derivative K (Xvec₁ j)) =
            lam * PowerSeries.constantCoeff (Xvec₁ j) := by
        rintro ⟨lam, hlam⟩; apply hXvec_lin; refine ⟨lam, fun j => ?_⟩
        have := hlam (cyc3.symm j); simpa [Xvec₁] using this
      have hX5_W1 := smooth_chart_X5_dvd ι hp2 hn3 h2np (rot3_symm_isHomogeneous hFh) hq0 Xvec₁
        (by rw [hrot_ev]; exact hXvec_F) ⟨c, hc, fun j => hXvec_const (cyc3 j)⟩ hX1_sm hX1_lin
      have hW1_eq : W10Z p n F₁ = rot3.symm (W10X p n F) := by unfold W10X; rw [RingEquiv.symm_apply_apply]
      rw [hW1_eq, hrot_ev] at hX5_W1
      exact hX5_from_chart 0 (W10X p n F) hq0 hHX hX5_W1
    · have hq1 : q 1 ≠ 0 := by
        rcases hq_norm with h0 | ⟨_, h1⟩ | ⟨_, _, h2⟩
        · exact absurd (by rw [h0]; exact one_ne_zero) hq0
        · rw [h1]; exact one_ne_zero
        · exact absurd (by rw [h2]; exact one_ne_zero) hq2
      let F₂ := rot3 F
      let q₂ : Fin 3 → ZMod p := q ∘ cyc3.symm
      let Xvec₂ : Fin 3 → PowerSeries K := Xvec ∘ cyc3.symm
      have hrot_ev : ∀ (P : MvPolynomial (Fin 3) (ZMod p)),
          MvPolynomial.eval₂Hom PowerSeries.C Xvec₂ ((rot3 P).map ι) =
            MvPolynomial.eval₂Hom PowerSeries.C Xvec (P.map ι) := by
        intro P
        have heq : ((MvPolynomial.eval₂Hom PowerSeries.C Xvec₂).comp (MvPolynomial.map ι)).comp
            rot3.toRingHom = (MvPolynomial.eval₂Hom PowerSeries.C Xvec).comp (MvPolynomial.map ι) := by
          apply MvPolynomial.ringHom_ext'
          · ext r; simp [rot3]
          · intro i
            simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
              rot3_X, MvPolynomial.map_X, MvPolynomial.eval₂Hom_X', Xvec₂, Function.comp_apply,
              Equiv.symm_apply_apply]
        exact RingHom.congr_fun heq P
      have hX2_sm : ∃ j : Fin 3, eval (ι ∘ q₂) (MvPolynomial.pderiv j (F₂.map ι)) ≠ 0 := by
        obtain ⟨j, hj⟩ := hsm_ex; refine ⟨cyc3 j, ?_⟩
        have hcomm : F₂.map ι = rot3 (F.map ι) := by dsimp only [F₂, rot3]; simp [MvPolynomial.map_rename]
        have hrot_pd : MvPolynomial.pderiv (cyc3 j) (rot3 (F.map ι)) = rot3 (MvPolynomial.pderiv j (F.map ι)) := by
          have h1 := congrArg rot3 (pderiv_rot3_symm j (rot3 (F.map ι)))
          rw [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h1; exact h1.symm
        rw [hcomm, hrot_pd, eval_rot3_eq]
        have hqeq : (ι ∘ q₂) ∘ cyc3 = ι ∘ q := by ext i; simp [q₂]
        rwa [hqeq]
      have hX2_lin : ¬ ∃ lam : K, ∀ j : Fin 3,
          PowerSeries.constantCoeff (PowerSeries.derivative K (Xvec₂ j)) =
            lam * PowerSeries.constantCoeff (Xvec₂ j) := by
        rintro ⟨lam, hlam⟩; apply hXvec_lin; refine ⟨lam, fun j => ?_⟩
        have := hlam (cyc3 j); simpa [Xvec₂] using this
      have hX5_W2 := smooth_chart_X5_dvd ι hp2 hn3 h2np (rot3_isHomogeneous hFh) hq1 Xvec₂
        (by rw [hrot_ev]; exact hXvec_F) ⟨c, hc, fun j => hXvec_const (cyc3.symm j)⟩ hX2_sm hX2_lin
      have hW2_eq : W10Z p n F₂ = rot3 (W10Y p n F) := by unfold W10Y; rw [RingEquiv.apply_symm_apply]
      rw [hW2_eq, hrot_ev] at hX5_W2
      exact hX5_from_chart 1 (W10Y p n F) hq1 hHY hX5_W2

-- Case A (smooth point): X^5 ∣ Res_Y(f_u, h_u, n, D)
lemma smooth_point_X5_dvd_shift {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F H : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (hHh : H.IsHomogeneous (2 * p + 10 * n - 20))
    (hHZ : F ∣ W10Z p n F - X 2 ^ 6 * H)
    (hHX : F ∣ W10X p n F - X 0 ^ 6 * H)
    (hHY : F ∣ W10Y p n F - X 1 ^ 6 * H)
    (α β γ : K)
    (hFK_O : eval ![1, α, β] (F.map ι) ≠ 0)
    {q : Fin 3 → ZMod p} (hq_norm : IsNorm q) (hqF : eval q F = 0)
    (hLu : (ι (q 2) - β * ι (q 0)) + γ * (ι (q 1) - α * ι (q 0)) ≠ 0)
    (hsm : eval (ι ∘ q) (MvPolynomial.pderiv 0 (F.map ι)) ≠ 0 ∨
      eval (ι ∘ q) (MvPolynomial.pderiv 1 (F.map ι)) ≠ 0 ∨
      eval (ι ∘ q) (MvPolynomial.pderiv 2 (F.map ι)) ≠ 0)
    (htan : eval (ι ∘ q) (MvPolynomial.pderiv 0 (F.map ι)) +
      α * eval (ι ∘ q) (MvPolynomial.pderiv 1 (F.map ι)) +
      β * eval (ι ∘ q) (MvPolynomial.pderiv 2 (F.map ι)) ≠ 0) :
    let u := ι ∘ q
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    let xu := (u 1 - α * u 0) / Lu
    let yu := u 0 / Lu
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let cF := eval ![1, α, β] (F.map ι)
    let f_u := tr_u (aff1 (C cF⁻¹ * shear3 α β γ (F.map ι)))
    let h_u := tr_u (aff1 (shear3 α β γ (H.map ι)))
    Polynomial.X ^ 5 ∣ (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n (2 * p + 10 * n - 20) := by
  intro u Lu xu yu tr_u cF f_u h_u
  let D := 2 * p + 10 * n - 20
  let FK := F.map ι
  let HK := H.map ι
  have hFK_h : FK.IsHomogeneous n := hFh.map ι
  have hHK_h : HK.IsHomogeneous D := hHh.map ι
  have hFK_u : eval u FK = 0 := by dsimp only [u, FK]; rw [eval_map_eq_map_eval, hqF, map_zero]
  have hMT_u : shear3Vec α β γ ![yu, xu, 1] = Lu⁻¹ • u := shear3_MT_u α β γ u hLu
  have htr_ev0 : ∀ P : MvPolynomial (Fin 3) K,
      eval ![0, 0] (tr_u (aff1 (shear3 α β γ P))) = eval (Lu⁻¹ • u) P := shear3_tr_ev0 α β γ u hLu
  have htrC : ∀ r : K, tr_u (aff1 (C r)) = C r := fun r => by simp [tr_u, aff1]
  have hfu_0 : eval ![0, 0] f_u = 0 := by
    dsimp only [f_u]
    rw [map_mul, map_mul, htrC, map_mul, eval_C, htr_ev0, isHomogeneous_eval_smul hFK_h, hFK_u,
      mul_zero, mul_zero]
  have hfu_y : eval ![0, 0] (MvPolynomial.pderiv 1 f_u) ≠ 0 := by
    have hpd_tr : ∀ g : MvPolynomial (Fin 2) K, MvPolynomial.pderiv 1 (tr_u g) = tr_u (MvPolynomial.pderiv 1 g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C c => simp [tr_u]
      | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
      | mul_X a i ha =>
        rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, ha]
        match i with | 0 => simp [tr_u, MvPolynomial.pderiv_X] | 1 => simp [tr_u, MvPolynomial.pderiv_X]
    dsimp only [f_u]
    rw [hpd_tr, aff1_pderiv_1, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
      shear3_pderiv_0]
    simp only [map_mul, map_add, htrC, eval_C, htr_ev0]
    rw [isHomogeneous_eval_smul (isHomogeneous_pderiv hFK_h 0),
      isHomogeneous_eval_smul (isHomogeneous_pderiv hFK_h 1),
      isHomogeneous_eval_smul (isHomogeneous_pderiv hFK_h 2)]
    have hfac : cF⁻¹ * ((Lu⁻¹) ^ (n - 1) * eval u (MvPolynomial.pderiv 0 FK) +
        α * ((Lu⁻¹) ^ (n - 1) * eval u (MvPolynomial.pderiv 1 FK)) +
        β * ((Lu⁻¹) ^ (n - 1) * eval u (MvPolynomial.pderiv 2 FK))) =
        cF⁻¹ * (Lu⁻¹) ^ (n - 1) * (eval u (MvPolynomial.pderiv 0 FK) +
          α * eval u (MvPolynomial.pderiv 1 FK) + β * eval u (MvPolynomial.pderiv 2 FK)) := by ring
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (inv_ne_zero hFK_O) (pow_ne_zero _ (inv_ne_zero hLu))) htan
  obtain ⟨y_ser, hy_const, hy_root⟩ := exists_hensel_series f_u hfu_0 hfu_y
  obtain ⟨hf_u_mon, hf_u_nd, hh_u_nd⟩ := shear3_shift_deg_props hFK_h hHK_h α β γ xu yu hFK_O
  let coeS : Polynomial K →+* PowerSeries K := Polynomial.coeToPowerSeries.ringHom
  have hhu_dvd_r : MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, y_ser] h_u ∣
      coeS ((mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n D) := by
    rw [← Polynomial.resultant_map_map]
    have hev_coe : ∀ g : MvPolynomial (Fin 2) K,
        Polynomial.eval y_ser ((mv2ToPolyY K g).map coeS) =
          MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, y_ser] g := by
      intro g; rw [eval_map_mv2ToPolyY]
      have h1 : coeS.comp Polynomial.C = PowerSeries.C := by ext c; simp [coeS]
      have h2 : ![coeS Polynomial.X, y_ser] = ![PowerSeries.X, y_ser] := by
        ext i; match i with | 0 => simp [coeS] | 1 => rfl
      rw [h1, h2]
    have hrt : Polynomial.IsRoot ((mv2ToPolyY K f_u).map coeS) y_ser := by
      rw [Polynomial.IsRoot.def, hev_coe]; exact hy_root
    obtain ⟨g', hg'⟩ := Polynomial.dvd_iff_isRoot.mpr hrt
    have hmf_mon : ((mv2ToPolyY K f_u).map coeS).Monic := hf_u_mon.map coeS
    have hmf_nd : ((mv2ToPolyY K f_u).map coeS).natDegree = n := by rw [hf_u_mon.natDegree_map, hf_u_nd]
    have hg'_ne : g' ≠ 0 := by rintro rfl; rw [mul_zero] at hg'; exact hmf_mon.ne_zero hg'
    have hg'_nd : g'.natDegree = n - 1 := by
      have h1 := congrArg Polynomial.natDegree hg'
      rw [hmf_nd, (Polynomial.monic_X_sub_C y_ser).natDegree_mul' hg'_ne, Polynomial.natDegree_X_sub_C] at h1
      omega
    have hn_sum : (Polynomial.X - Polynomial.C y_ser).natDegree + g'.natDegree = n := by
      rw [Polynomial.natDegree_X_sub_C, hg'_nd]; omega
    have hmh_nd : ((mv2ToPolyY K h_u).map coeS).natDegree ≤ D := Polynomial.natDegree_map_le.trans hh_u_nd
    rw [hg', ← hn_sum, Polynomial.resultant_mul_left _ _ _ D hmh_nd,
      Polynomial.natDegree_X_sub_C, Polynomial.resultant_X_sub_C_left _ D _ hmh_nd, hev_coe]
    exact dvd_mul_right _ _
  let x_ser : PowerSeries K := PowerSeries.C xu + PowerSeries.X
  let y_t : PowerSeries K := PowerSeries.C yu + y_ser
  let Xvec : Fin 3 → PowerSeries K :=
    ![y_t, x_ser + PowerSeries.C α * y_t, 1 - PowerSeries.C γ * x_ser + PowerSeries.C β * y_t]
  have hev_Xvec : ∀ P : MvPolynomial (Fin 3) K,
      MvPolynomial.eval₂Hom PowerSeries.C Xvec P =
        MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, y_ser] (tr_u (aff1 (shear3 α β γ P))) := by
    intro P
    have heq : MvPolynomial.eval₂Hom PowerSeries.C Xvec =
        (((MvPolynomial.eval₂Hom PowerSeries.C ![PowerSeries.X, y_ser]).comp tr_u).comp aff1).comp
          (shear3 α β γ) := by
      apply MvPolynomial.ringHom_ext'
      · ext c; simp [shear3, aff1, tr_u]
      · intro i; match i with
        | 0 => simp [Xvec, y_t, shear3, aff1, tr_u]
        | 1 => simp [Xvec, x_ser, y_t, shear3, aff1, tr_u]
        | 2 => simp [Xvec, x_ser, y_t, shear3, aff1, tr_u]
    exact RingHom.congr_fun heq P
  have hXvec_F : MvPolynomial.eval₂Hom PowerSeries.C Xvec FK = 0 := by
    rw [hev_Xvec]
    have h1 : tr_u (aff1 (shear3 α β γ FK)) = C cF * f_u := by
      dsimp only [f_u]; rw [map_mul, map_mul, htrC, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hFK_O,
        map_one, one_mul]
    rw [h1, map_mul, MvPolynomial.eval₂Hom_C, hy_root, mul_zero]
  have hXvec_const : ∀ j : Fin 3, PowerSeries.constantCoeff (Xvec j) = Lu⁻¹ * u j := by
    intro j
    have hx0 : PowerSeries.constantCoeff x_ser = xu := by simp [x_ser]
    have hy0 : PowerSeries.constantCoeff y_t = yu := by simp [y_t, hy_const]
    have h1 : PowerSeries.constantCoeff (Xvec j) = shear3Vec α β γ ![yu, xu, 1] j := by
      match j with
      | 0 => simp [Xvec, shear3Vec, hy0]
      | 1 => simp [Xvec, shear3Vec, hx0, hy0]
      | 2 => simp [Xvec, shear3Vec, hx0, hy0]
    rw [h1, hMT_u]; rfl
  have hXvec_lin : ¬ ∃ lam : K, ∀ j : Fin 3,
      PowerSeries.constantCoeff (PowerSeries.derivative K (Xvec j)) =
        lam * PowerSeries.constantCoeff (Xvec j) := by
    rintro ⟨lam, hlam⟩
    have hdx : PowerSeries.constantCoeff (PowerSeries.derivative K x_ser) = 1 := by
      dsimp only [x_ser]; rw [map_add, PowerSeries.derivative_C, PowerSeries.derivative_X, zero_add, map_one]
    have h0 := hlam 0; have h1 := hlam 1; have h2 := hlam 2
    have hcx0 : PowerSeries.constantCoeff x_ser = xu := by simp [x_ser]
    have hcy0 : PowerSeries.constantCoeff y_t = yu := by simp [y_t, hy_const]
    dsimp only [Xvec] at h0 h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add, map_sub,
      Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_C, PowerSeries.derivative_one,
      mul_zero, add_zero, zero_sub, map_neg, map_mul, hdx, hcx0, hcy0,
      PowerSeries.constantCoeff_C, map_one, mul_one] at h0 h1 h2
    have hsub1 : (1 : K) = lam * xu := by linear_combination h1 - α * h0
    have hsub2 : -γ = lam * (1 - γ * xu) := by linear_combination h2 - β * h0
    have hlam0 : lam = 0 := by linear_combination -(hsub2 + γ * hsub1)
    rw [hlam0, zero_mul] at hsub1
    exact one_ne_zero hsub1
  have hsm_ex : ∃ j : Fin 3, eval u (MvPolynomial.pderiv j FK) ≠ 0 := by
    rcases hsm with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  have hX5_HK : PowerSeries.X ^ 5 ∣ MvPolynomial.eval₂Hom PowerSeries.C Xvec HK :=
    smooth_point_X5_HK ι hp2 hn3 h2np hFh hHZ hHX hHY hq_norm Xvec hXvec_F Lu⁻¹ (inv_ne_zero hLu)
      hXvec_const hsm_ex hXvec_lin
  rw [hev_Xvec HK] at hX5_HK
  have hX5_coe : PowerSeries.X ^ 5 ∣ coeS ((mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n D) :=
    dvd_trans hX5_HK hhu_dvd_r
  rw [PowerSeries.X_pow_dvd_iff] at hX5_coe
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  have h1 := hX5_coe m hm
  change PowerSeries.coeff m (((mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n D : Polynomial K) : PowerSeries K) = 0 at h1
  rwa [Polynomial.coeff_coe] at h1

-- Singular-point helper 1a: X ∤ Res_Y(f_u, l_u, n, 1)
lemma singular_res_l_not_dvd_X {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K)
    {F : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (α β γ : K) (hFK_O : eval ![1, α, β] (F.map ι) ≠ 0)
    {q : Fin 3 → ZMod p}
    (hLu : (ι (q 2) - β * ι (q 0)) + γ * (ι (q 1) - α * ι (q 0)) ≠ 0)
    (haxis : ∀ i : Fin 3, ι (q i) ≠ 0 →
      eval (fun j => ι (q i) * (![1, α, β] j) - (![1, α, β] i) * ι (q j)) (F.map ι) ≠ 0)
    (i₀ : Fin 3) (hqi : q i₀ ≠ 0) :
    let u := ι ∘ q
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    let xu := (u 1 - α * u 0) / Lu
    let yu := u 0 / Lu
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let cF := eval ![1, α, β] (F.map ι)
    let f_u := tr_u (aff1 (C cF⁻¹ * shear3 α β γ (F.map ι)))
    let l_u := tr_u (aff1 (shear3 α β γ (X i₀ : MvPolynomial (Fin 3) K)))
    (mv2ToPolyY K f_u).Monic → (mv2ToPolyY K f_u).natDegree = n → (mv2ToPolyY K l_u).natDegree ≤ 1 →
    ¬ (Polynomial.X ∣ (mv2ToPolyY K f_u).resultant (mv2ToPolyY K l_u) n 1) := by
  intro u Lu xu yu tr_u cF f_u l_u hf_u_mon hf_u_nd hl_nd
  let FK := F.map ι
  let O : Fin 3 → K := ![1, α, β]
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hFK_h : FK.IsHomogeneous n := hFh.map ι
  have hui_ne : u i₀ ≠ 0 := fun h => hqi (hι_inj (h.trans (map_zero ι).symm))
  have hMT_u : shear3Vec α β γ ![yu, xu, 1] = Lu⁻¹ • u := shear3_MT_u α β γ u hLu
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
  change (Polynomial.evalRingHom 0) ((mv2ToPolyY K f_u).resultant (mv2ToPolyY K l_u) n 1) ≠ 0
  rw [← Polynomial.resultant_map_map]
  let f0 := (mv2ToPolyY K f_u).map (Polynomial.evalRingHom 0)
  let l0 := (mv2ToPolyY K l_u).map (Polynomial.evalRingHom 0)
  have hf0_m : f0.Monic := hf_u_mon.map _
  have hf0_d : f0.natDegree = n := by rw [hf_u_mon.natDegree_map, hf_u_nd]
  have hev_0 : ∀ (P : MvPolynomial (Fin 3) K) (t : K),
      Polynomial.eval t ((mv2ToPolyY K (tr_u (aff1 (shear3 α β γ P)))).map (Polynomial.evalRingHom 0)) =
        eval (fun j => Lu⁻¹ * u j + t * O j) P := by
    intro P t; rw [eval_map_mv2ToPolyY]
    have h1 : (Polynomial.evalRingHom 0).comp Polynomial.C = RingHom.id K := by ext r; simp
    have h2 : ![(Polynomial.evalRingHom 0) Polynomial.X, t] = ![0, t] := by
      ext k; match k with | 0 => simp | 1 => rfl
    rw [h1, h2]
    change eval ![0, t] (tr_u (aff1 (shear3 α β γ P))) = _
    have heq : ((eval ![0, t]).comp tr_u).comp aff1 = eval ![yu + t, xu, 1] := by
      apply MvPolynomial.ringHom_ext'
      · ext r; simp [tr_u, aff1]
      · intro k; match k with | 0 => simp [tr_u, aff1] | 1 => simp [tr_u, aff1] | 2 => simp [tr_u, aff1]
    have h3 := RingHom.congr_fun heq (shear3 α β γ P)
    simp only [RingHom.comp_apply] at h3
    rw [h3, shear3_eval]
    apply congrArg (fun v => eval v P)
    ext k
    have hM := congrFun hMT_u k
    match k with
    | 0 => change yu + t = Lu⁻¹ * u 0 + t * O 0; change yu = Lu⁻¹ * u 0 at hM; simp [O, hM]
    | 1 => change xu + α * (yu + t) = Lu⁻¹ * u 1 + t * O 1
           change xu + α * yu = Lu⁻¹ * u 1 at hM; simp [O]; linear_combination hM
    | 2 => change 1 - γ * xu + β * (yu + t) = Lu⁻¹ * u 2 + t * O 2
           change 1 - γ * xu + β * yu = Lu⁻¹ * u 2 at hM; simp [O]; linear_combination hM
  have hl0_eq : l0 = Polynomial.C (Lu⁻¹ * u i₀) + Polynomial.C (O i₀) * Polynomial.X := by
    have hdeg1 : l0.natDegree ≤ 1 := Polynomial.natDegree_map_le.trans hl_nd
    have h0 : Polynomial.eval 0 l0 = Lu⁻¹ * u i₀ := by
      have := hev_0 (X i₀) 0; simp only [eval_X, zero_mul, add_zero] at this; exact this
    have h1 : Polynomial.eval 1 l0 = Lu⁻¹ * u i₀ + O i₀ := by
      have := hev_0 (X i₀) 1; simp only [eval_X, one_mul] at this; exact this
    have hlin : l0 = Polynomial.C (l0.coeff 0) + Polynomial.C (l0.coeff 1) * Polynomial.X := by
      ext k; match k with
      | 0 => simp
      | 1 => simp
      | k + 2 =>
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    rw [hlin] at h0 h1
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      mul_zero, add_zero, mul_one] at h0 h1
    rw [hlin, h0, show l0.coeff 1 = O i₀ by linear_combination h1 - h0]
  change f0.resultant l0 n 1 ≠ 0
  by_cases hOi : O i₀ = 0
  · rw [hl0_eq, hOi, map_zero, zero_mul, add_zero, Polynomial.resultant_C_right]
    have hfn : f0.coeff n = 1 := by rw [← hf0_d]; exact hf0_m.leadingCoeff
    rw [hfn, one_pow, one_mul]
    exact pow_ne_zero n (mul_ne_zero (inv_ne_zero hLu) hui_ne)
  · let tstar : K := -(Lu⁻¹ * u i₀) / O i₀
    have hl0_fac : l0 = Polynomial.C (O i₀) * (Polynomial.X - Polynomial.C tstar) := by
      rw [hl0_eq]; dsimp only [tstar]
      rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hOi, map_neg, sub_neg_eq_add, add_comm]
    rw [hl0_fac, Polynomial.resultant_C_mul_right,
      ← pow_one (Polynomial.X - Polynomial.C tstar),
      Polynomial.resultant_X_sub_C_pow_right f0 tstar n 1 (le_of_eq hf0_d), mul_one, pow_one]
    have hf0_tstar : Polynomial.eval tstar f0 ≠ 0 := by
      have hevF : Polynomial.eval tstar f0 = cF⁻¹ * eval (fun j => Lu⁻¹ * u j + tstar * O j) FK := by
        dsimp only [f0, f_u]
        have hsplit : tr_u (aff1 (C cF⁻¹ * shear3 α β γ FK)) = C cF⁻¹ * tr_u (aff1 (shear3 α β γ FK)) := by
          rw [map_mul, map_mul]; congr 1; simp [tr_u, aff1]
        rw [hsplit, map_mul, Polynomial.map_mul, Polynomial.eval_mul, hev_0 FK tstar]
        have hC : Polynomial.eval tstar ((mv2ToPolyY K (C cF⁻¹)).map (Polynomial.evalRingHom 0)) = cF⁻¹ := by
          simp [mv2ToPolyY]
        rw [hC]
      rw [hevF]; refine mul_ne_zero (inv_ne_zero hFK_O) ?_
      have hscale : (fun j : Fin 3 => Lu⁻¹ * u j + tstar * O j) =
          (-(Lu⁻¹ / O i₀)) • (fun j => u i₀ * O j - O i₀ * u j) := by
        ext j; dsimp only [Pi.smul_apply, smul_eq_mul, tstar]; field_simp [hOi, hLu]; ring
      rw [hscale, isHomogeneous_eval_smul hFK_h]
      exact mul_ne_zero (pow_ne_zero n (neg_ne_zero.mpr (div_ne_zero (inv_ne_zero hLu) hOi)))
        (haxis i₀ hui_ne)
    exact mul_ne_zero (pow_ne_zero n hOi)
      (mul_ne_zero (pow_ne_zero n (by norm_num : (-1 : K) ≠ 0)) hf0_tstar)

lemma shear3_tr_aff1_natDegree_le {K : Type*} [Field K] {d : ℕ}
    {P : MvPolynomial (Fin 3) K} (hPh : P.IsHomogeneous d) (α β γ xu yu : K) :
    (mv2ToPolyY K ((MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1] :
      MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K) (aff1 (shear3 α β γ P)))).natDegree ≤ d := by
  rw [shear3_tr_poly, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
  refine Polynomial.natDegree_map_le.trans ?_
  rw [← map_dehomog1_finSuccEquiv]
  exact Polynomial.natDegree_map_le.trans
    (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
      (finSuccEquiv_coeff_hom (shear3_isHomogeneous α β γ hPh)).2)

lemma X_pow_dvd_right_of_mul_not_dvd {K : Type*} [Field K] {A B : Polynomial K} {k : ℕ}
    (hA : ¬ Polynomial.X ∣ A) (hAB : Polynomial.X ^ k ∣ A * B) : Polynomial.X ^ k ∣ B := by
  have hX_prime : Prime (Polynomial.X : Polynomial K) := Polynomial.prime_X
  induction k generalizing B with
  | zero => simp
  | succ k ih =>
    rw [pow_succ'] at hAB ⊢
    rcases hX_prime.dvd_or_dvd (dvd_trans (dvd_mul_right _ _) hAB) with hL | ⟨R', hR'⟩
    · exact absurd hL hA
    · rw [hR'] at hAB ⊢
      have hk' : Polynomial.X ^ k ∣ A * R' := by
        rcases hAB with ⟨S', hS'⟩; refine ⟨S', ?_⟩
        exact mul_left_cancel₀ Polynomial.X_ne_zero (by linear_combination hS')
      exact mul_dvd_mul_left Polynomial.X (ih hk')

lemma X5_dvd_res_from_chart_poly {K : Type*} [Field K] {n D : ℕ}
    {pf ph pw pl pq : Polynomial (Polynomial K)}
    (hpf_mon : pf.Monic) (hpf_nd : pf.natDegree = n) (hn : 3 ≤ n) (hnD : n ≤ D + 6) (hD : 8 ≤ D + 6)
    (hw_eq : pw = pl ^ 6 * ph + pf * pq)
    (hw_nd : pw.natDegree ≤ D + 6) (hl_nd : pl.natDegree ≤ 1) (hh_nd : ph.natDegree ≤ D)
    (hl_ne : pl ≠ 0) (hh_ne : ph ≠ 0)
    (hf_ord : ∀ k < 2, Polynomial.X ^ (2 - k) ∣ pf.coeff k)
    (hw_ord : ∀ k < 8, Polynomial.X ^ (8 - k) ∣ pw.coeff k)
    (hX_ndvd : ¬ Polynomial.X ∣ pf.resultant pl n 1) :
    Polynomial.X ^ 5 ∣ pf.resultant ph n D := by
  have hres_fac : pf.resultant pw n (D + 6) = (pf.resultant pl n 1) ^ 6 * pf.resultant ph n D :=
    resultant_pad_mod_and_mul hpf_mon hpf_nd hnD hw_eq hw_nd hl_nd hh_nd hl_ne hh_ne
  have hX16 : Polynomial.X ^ (2 * 8) ∣ pf.resultant pw n (D + 6) :=
    X_pow_mul_dvd_resultant_of_vanishesOrder (r := 2) (s := 8) (by omega) hD hf_ord hw_ord
  rw [hres_fac] at hX16
  have hndvd6 : ¬ Polynomial.X ∣ (pf.resultant pl n 1) ^ 6 :=
    fun h => hX_ndvd (Polynomial.prime_X.dvd_of_dvd_pow h)
  exact dvd_trans (pow_dvd_pow Polynomial.X (by omega : 5 ≤ 2 * 8))
    (X_pow_dvd_right_of_mul_not_dvd hndvd6 hX16)

-- Singular-point helper 1b: X^5 ∣ Res_Y(f_u, h_u) from chart divisibility + VanishesOrder 2 & 8
lemma singular_from_chart_X5_dvd {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F H : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (hHh : H.IsHomogeneous (2 * p + 10 * n - 20))
    (α β γ : K) (hFK_O : eval ![1, α, β] (F.map ι) ≠ 0)
    {q : Fin 3 → ZMod p}
    (hLu : (ι (q 2) - β * ι (q 0)) + γ * (ι (q 1) - α * ι (q 0)) ≠ 0)
    (haxis : ∀ i : Fin 3, ι (q i) ≠ 0 →
      eval (fun j => ι (q i) * (![1, α, β] j) - (![1, α, β] i) * ι (q j)) (F.map ι) ≠ 0)
    (i₀ : Fin 3) (W : MvPolynomial (Fin 3) (ZMod p))
    (hqi : q i₀ ≠ 0) (hWh : W.IsHomogeneous (2 * p + 10 * n - 20 + 6))
    (hFW : F ∣ W - X i₀ ^ 6 * H) :
    let u := ι ∘ q
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    let xu := (u 1 - α * u 0) / Lu
    let yu := u 0 / Lu
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let cF := eval ![1, α, β] (F.map ι)
    let f_u := tr_u (aff1 (C cF⁻¹ * shear3 α β γ (F.map ι)))
    let h_u := tr_u (aff1 (shear3 α β γ (H.map ι)))
    (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n (2 * p + 10 * n - 20) ≠ 0 →
    VanishesOrder 8 (tr_u (aff1 (shear3 α β γ (W.map ι)))) →
    VanishesOrder 2 f_u →
    Polynomial.X ^ 5 ∣ (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n (2 * p + 10 * n - 20) := by
  intro u Lu xu yu tr_u cF f_u h_u hres_ne hW_vo hf_vo
  let D := 2 * p + 10 * n - 20
  let FK := F.map ι
  let HK := H.map ι
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have hFK_h : FK.IsHomogeneous n := hFh.map ι
  have hHK_h : HK.IsHomogeneous D := hHh.map ι
  have htr_ev0 : ∀ P : MvPolynomial (Fin 3) K,
      eval ![0, 0] (tr_u (aff1 (shear3 α β γ P))) = eval (Lu⁻¹ • u) P := shear3_tr_ev0 α β γ u hLu
  obtain ⟨hf_u_mon, hf_u_nd, hh_u_nd⟩ := shear3_shift_deg_props hFK_h hHK_h α β γ xu yu hFK_O
  change (mv2ToPolyY K f_u).Monic at hf_u_mon
  change (mv2ToPolyY K f_u).natDegree = n at hf_u_nd
  change (mv2ToPolyY K h_u).natDegree ≤ D at hh_u_nd
  rcases hFW with ⟨Q, hQ⟩
  let w_u := tr_u (aff1 (shear3 α β γ (W.map ι)))
  let l_u := tr_u (aff1 (shear3 α β γ (X i₀ : MvPolynomial (Fin 3) K)))
  let q_u := C cF * tr_u (aff1 (shear3 α β γ (Q.map ι)))
  have hw_eq : w_u = l_u ^ 6 * h_u + f_u * q_u := by
    have h1 := congrArg (tr_u ∘ aff1 ∘ shear3 α β γ ∘ MvPolynomial.map ι) hQ
    simp only [Function.comp_apply, map_sub, map_mul, map_pow, MvPolynomial.map_X] at h1
    have hF_eq : tr_u (aff1 (shear3 α β γ FK)) = C cF * f_u := by
      dsimp only [f_u]; rw [map_mul, map_mul]
      have hC : tr_u (aff1 (C cF⁻¹)) = C cF⁻¹ := by simp [tr_u, aff1]
      rw [hC, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hFK_O, map_one, one_mul]
    change w_u - l_u ^ 6 * h_u = tr_u (aff1 (shear3 α β γ FK)) * tr_u (aff1 (shear3 α β γ (Q.map ι))) at h1
    rw [hF_eq, sub_eq_iff_eq_add] at h1
    rw [h1, add_comm]; congr 1; dsimp only [q_u]; ring
  have hw_poly : mv2ToPolyY K w_u = (mv2ToPolyY K l_u) ^ 6 * mv2ToPolyY K h_u +
      mv2ToPolyY K f_u * mv2ToPolyY K q_u := by rw [hw_eq, map_add, map_mul, map_mul, map_pow]
  have hw_nd : (mv2ToPolyY K w_u).natDegree ≤ D + 6 :=
    shear3_tr_aff1_natDegree_le (hWh.map ι) α β γ xu yu
  have hl_nd : (mv2ToPolyY K l_u).natDegree ≤ 1 :=
    shear3_tr_aff1_natDegree_le (isHomogeneous_X K i₀) α β γ xu yu
  have hui_ne : u i₀ ≠ 0 := fun h => hqi (hι_inj (h.trans (map_zero ι).symm))
  have hl_ne : mv2ToPolyY K l_u ≠ 0 := by
    intro h0
    have hl0 : l_u = 0 := (mv2EquivPolyY K).injective (h0.trans (map_zero _).symm)
    have hev := congrArg (eval ![0, 0]) hl0
    rw [map_zero] at hev; dsimp only [l_u] at hev; rw [htr_ev0, eval_X] at hev
    exact mul_ne_zero (inv_ne_zero hLu) hui_ne hev
  have hh_ne : mv2ToPolyY K h_u ≠ 0 := by
    intro h0; apply hres_ne
    rw [h0, Polynomial.resultant_zero_right, zero_pow (by omega), zero_mul]
  have hX_ndvd_resl : ¬ (Polynomial.X ∣ (mv2ToPolyY K f_u).resultant (mv2ToPolyY K l_u) n 1) :=
    singular_res_l_not_dvd_X ι hFh α β γ hFK_O hLu haxis i₀ hqi hf_u_mon hf_u_nd hl_nd
  exact X5_dvd_res_from_chart_poly hf_u_mon hf_u_nd hn3 (by omega) (by omega) hw_poly hw_nd hl_nd hh_u_nd
    hl_ne hh_ne (X_pow_dvd_mv2ToPolyY_coeff_of_vanishesOrder hf_vo)
    (X_pow_dvd_mv2ToPolyY_coeff_of_vanishesOrder hW_vo) hX_ndvd_resl

-- Singular-point helper 2: VanishesOrder 2 & 8 on a chart
lemma singular_vo_chart {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    (Fr : MvPolynomial (Fin 3) (ZMod p)) (qr : Fin 3 → ZMod p)
    (L0 L1 L2 : MvPolynomial (Fin 2) K)
    (hFr_h : Fr.IsHomogeneous n) (hqr2 : qr 2 ≠ 0) (hqr0 : eval qr Fr = 0)
    (hqr_x : eval qr (MvPolynomial.pderiv 0 Fr) = 0)
    (hqr_y : eval qr (MvPolynomial.pderiv 1 Fr) = 0)
    (hL0 : eval ![0, 0] (L0 - C (ι (qr 0 / qr 2)) * L2) = 0)
    (hL1 : eval ![0, 0] (L1 - C (ι (qr 1 / qr 2)) * L2) = 0) :
    VanishesOrder 2 (MvPolynomial.eval₂Hom C ![L0, L1, L2] (Fr.map ι)) ∧
    VanishesOrder 8 (MvPolynomial.eval₂Hom C ![L0, L1, L2] ((W10Z p n Fr).map ι)) := by
  let ap : ZMod p := qr 0 / qr 2
  let bp : ZMod p := qr 1 / qr 2
  let trp : MvPolynomial (Fin 2) (ZMod p) →+* MvPolynomial (Fin 2) (ZMod p) :=
    MvPolynomial.eval₂Hom C ![X 0 + C ap, X 1 + C bp]
  have htrp_ev : ∀ g : MvPolynomial (Fin 2) (ZMod p), eval ![0, 0] (trp g) = eval ![ap, bp] g := by
    intro g
    have heq : (eval ![0, 0]).comp trp = eval ![ap, bp] := by
      apply MvPolynomial.ringHom_ext'; · ext c; simp [trp]
      · intro i; match i with | 0 => simp [trp] | 1 => simp [trp]
    exact RingHom.congr_fun heq g
  have hde_evp : ∀ P : MvPolynomial (Fin 3) (ZMod p), eval ![ap, bp] (dehomogZ P) = eval ![ap, bp, 1] P := by
    intro P
    have heq : (eval ![ap, bp]).comp dehomogZ = eval ![ap, bp, 1] := by
      apply MvPolynomial.ringHom_ext'; · ext c; simp [dehomogZ]
      · intro i; match i with | 0 => simp [dehomogZ] | 1 => simp [dehomogZ] | 2 => simp [dehomogZ]
    exact RingHom.congr_fun heq P
  have hptp : ![ap, bp, 1] = (qr 2)⁻¹ • qr := by
    ext i; match i with
    | 0 => change qr 0 / qr 2 = (qr 2)⁻¹ * qr 0; rw [div_eq_inv_mul]
    | 1 => change qr 1 / qr 2 = (qr 2)⁻¹ * qr 1; rw [div_eq_inv_mul]
    | 2 => change 1 = (qr 2)⁻¹ * qr 2; rw [inv_mul_cancel₀ hqr2]
  have htrp_pd : ∀ (i : Fin 2) (g : MvPolynomial (Fin 2) (ZMod p)),
      MvPolynomial.pderiv i (trp g) = trp (MvPolynomial.pderiv i g) := by
    intro i g
    induction g using MvPolynomial.induction_on with
    | C c => simp [trp]
    | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    | mul_X a j ha =>
      rw [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_mul, map_add, map_mul, map_mul, ha]
      match i, j with | 0, 0 | 0, 1 | 1, 0 | 1, 1 => simp [trp, MvPolynomial.pderiv_X]
  have hf0_p : eval ![0, 0] (trp (dehomogZ Fr)) = 0 := by
    rw [htrp_ev, hde_evp, hptp, isHomogeneous_eval_smul hFr_h, hqr0, mul_zero]
  have hfx_p : eval ![0, 0] (MvPolynomial.pderiv 0 (trp (dehomogZ Fr))) = 0 := by
    rw [htrp_pd, htrp_ev, ← dehomogZ_pderiv_0, hde_evp, hptp,
      isHomogeneous_eval_smul (isHomogeneous_pderiv hFr_h 0), hqr_x, mul_zero]
  have hfy_p : eval ![0, 0] (MvPolynomial.pderiv 1 (trp (dehomogZ Fr))) = 0 := by
    rw [htrp_pd, htrp_ev, ← dehomogZ_pderiv_1, hde_evp, hptp,
      isHomogeneous_eval_smul (isHomogeneous_pderiv hFr_h 1), hqr_y, mul_zero]
  have hvo2_p : VanishesOrder 2 (trp (dehomogZ Fr)) := by
    intro m hm
    have hcoeff0 : ∀ g : MvPolynomial (Fin 2) (ZMod p), eval ![0, 0] g = g.coeff 0 := by
      intro g; conv_lhs => rw [g.as_sum]; rw [map_sum]
      by_cases h0 : (0 : Fin 2 →₀ ℕ) ∈ g.support
      · rw [Finset.sum_eq_single 0]
        · rw [eval_monomial]; simp
        · intro t _ hne; rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
          by_cases ht0 : t 0 = 0
          · have ht1 : t 1 ≠ 0 := fun h1 => hne (by ext i; match i with | 0 => exact ht0 | 1 => exact h1)
            simp [zero_pow ht1]
          · simp [zero_pow ht0]
        · intro h; exact absurd h0 h
      · rw [MvPolynomial.notMem_support_iff.mp h0]
        apply Finset.sum_eq_zero; intro t ht
        have hne : t ≠ 0 := fun h => h0 (h ▸ ht)
        rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp), Fin.prod_univ_two]
        by_cases ht0 : t 0 = 0
        · have ht1 : t 1 ≠ 0 := fun h1 => hne (by ext i; match i with | 0 => exact ht0 | 1 => exact h1)
          simp [zero_pow ht1]
        · simp [zero_pow ht0]
    have hcase : m = 0 ∨ m = Finsupp.single 0 1 ∨ m = Finsupp.single 1 1 := by
      by_cases h0 : m 0 = 0
      · by_cases h1 : m 1 = 0
        · left; ext i; match i with | 0 => exact h0 | 1 => exact h1
        · right; right; ext i; match i with | 0 => simp [h0] | 1 => simp; omega
      · right; left; ext i; match i with | 0 => simp; omega | 1 => simp; omega
    rcases hcase with rfl | rfl | rfl
    · rw [← hcoeff0]; exact hf0_p
    · rw [hcoeff0, MvPolynomial.coeff_pderiv] at hfx_p
      simpa [Finsupp.single_add] using hfx_p
    · rw [hcoeff0, MvPolynomial.coeff_pderiv] at hfy_p
      simpa [Finsupp.single_add] using hfy_p
  have hvo8_p : VanishesOrder 8 (trp (W10 p (dehomogZ Fr))) := by
    have htr_eq : trp (W10 p (dehomogZ Fr)) = W10 p (trp (dehomogZ Fr)) := by
      have h1 := (W10_translate ap bp (dehomogZ Fr)).symm
      have h2 : MvPolynomial.eval₂Hom C (fun i : Fin 2 =>
          match i with
          | 0 => (X 0 : MvPolynomial (Fin 2) (ZMod p)) + C ap
          | 1 => X 1 + C bp) = trp := by
        apply MvPolynomial.ringHom_ext'
        · ext c; simp [trp]
        · intro i; match i with | 0 => simp [trp] | 1 => simp [trp]
      rwa [h2] at h1
    rw [htr_eq]; exact vanishesOrder_W10_of_singular (by omega) hvo2_p
  have hmap_vo : ∀ {r' : ℕ} {g : MvPolynomial (Fin 2) (ZMod p)}, VanishesOrder r' g → VanishesOrder r' (g.map ι) :=
    fun hg m hm => by rw [MvPolynomial.coeff_map, hg m hm, map_zero]
  have hcomm_tr : ∀ g : MvPolynomial (Fin 2) (ZMod p),
      MvPolynomial.eval₂Hom C ![X 0 + C (ι ap), X 1 + C (ι bp)] (g.map ι) = (trp g).map ι := by
    intro g
    have heq : (MvPolynomial.eval₂Hom C ![X 0 + C (ι ap), X 1 + C (ι bp)]).comp (MvPolynomial.map ι) =
        (MvPolynomial.map ι).comp trp := by
      apply MvPolynomial.ringHom_ext'; · ext c; simp [trp]
      · intro i; match i with | 0 => simp [trp] | 1 => simp [trp]
    exact RingHom.congr_fun heq g
  have hcomm_de : ∀ P : MvPolynomial (Fin 3) (ZMod p), dehomogZ (P.map ι) = (dehomogZ P).map ι := by
    intro P
    have heq : dehomogZ.comp (MvPolynomial.map ι) = (MvPolynomial.map ι).comp dehomogZ := by
      apply MvPolynomial.ringHom_ext'; · ext c; simp [dehomogZ]
      · intro i; match i with | 0 => simp [dehomogZ] | 1 => simp [dehomogZ] | 2 => simp [dehomogZ]
    exact RingHom.congr_fun heq P
  refine ⟨vanishesOrder_of_homog_chart (hFr_h.map ι) ?_ L0 L1 L2 hL0 hL1,
    vanishesOrder_of_homog_chart ((W10Z_isHomogeneous (p := p) hn3 (by omega) hFr_h).map ι) ?_ L0 L1 L2 hL0 hL1⟩
  · rw [hcomm_de, hcomm_tr]; exact hmap_vo hvo2_p
  · rw [hcomm_de, W10Z, dehomogZ_homogZ, hcomm_tr]; exact hmap_vo hvo8_p

-- Case B (singular point): X^5 ∣ Res_Y(f_u, h_u, n, D)
lemma singular_point_X5_dvd_shift {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K]
    (ι : ZMod p →+* K) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F H : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (hHh : H.IsHomogeneous (2 * p + 10 * n - 20))
    (hHZ : F ∣ W10Z p n F - X 2 ^ 6 * H)
    (hHX : F ∣ W10X p n F - X 0 ^ 6 * H)
    (hHY : F ∣ W10Y p n F - X 1 ^ 6 * H)
    (α β γ : K)
    (hFK_O : eval ![1, α, β] (F.map ι) ≠ 0)
    {q : Fin 3 → ZMod p} (hq_norm : IsNorm q) (hqF : eval q F = 0)
    (hLu : (ι (q 2) - β * ι (q 0)) + γ * (ι (q 1) - α * ι (q 0)) ≠ 0)
    (hFX0 : eval (ι ∘ q) (MvPolynomial.pderiv 0 (F.map ι)) = 0)
    (hFY0 : eval (ι ∘ q) (MvPolynomial.pderiv 1 (F.map ι)) = 0)
    (hFZ0 : eval (ι ∘ q) (MvPolynomial.pderiv 2 (F.map ι)) = 0)
    (haxis : ∀ i : Fin 3, ι (q i) ≠ 0 →
      eval (fun j => ι (q i) * (![1, α, β] j) - (![1, α, β] i) * ι (q j)) (F.map ι) ≠ 0)
    (hres_ne : let u := ι ∘ q
      let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
      let xu := (u 1 - α * u 0) / Lu
      let yu := u 0 / Lu
      let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
        MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
      let cF := eval ![1, α, β] (F.map ι)
      let f_u := tr_u (aff1 (C cF⁻¹ * shear3 α β γ (F.map ι)))
      let h_u := tr_u (aff1 (shear3 α β γ (H.map ι)))
      (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n (2 * p + 10 * n - 20) ≠ 0) :
    let u := ι ∘ q
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    let xu := (u 1 - α * u 0) / Lu
    let yu := u 0 / Lu
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let cF := eval ![1, α, β] (F.map ι)
    let f_u := tr_u (aff1 (C cF⁻¹ * shear3 α β γ (F.map ι)))
    let h_u := tr_u (aff1 (shear3 α β γ (H.map ι)))
    Polynomial.X ^ 5 ∣ (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n (2 * p + 10 * n - 20) := by
  intro u Lu xu yu tr_u cF f_u h_u
  let D := 2 * p + 10 * n - 20
  let FK := F.map ι
  have hι_inj : Function.Injective ι := RingHom.injective ι
  have htr_ev0 : ∀ P : MvPolynomial (Fin 3) K,
      eval ![0, 0] (tr_u (aff1 (shear3 α β γ P))) = eval (Lu⁻¹ • u) P := shear3_tr_ev0 α β γ u hLu
  let L0 : MvPolynomial (Fin 2) K := tr_u (aff1 (shear3 α β γ (X 0)))
  let L1 : MvPolynomial (Fin 2) K := tr_u (aff1 (shear3 α β γ (X 1)))
  let L2 : MvPolynomial (Fin 2) K := tr_u (aff1 (shear3 α β γ (X 2)))
  have hev_L : ∀ P : MvPolynomial (Fin 3) K, tr_u (aff1 (shear3 α β γ P)) = MvPolynomial.eval₂Hom C ![L0, L1, L2] P := by
    intro P
    have heq : (tr_u.comp aff1).comp (shear3 α β γ) = MvPolynomial.eval₂Hom C ![L0, L1, L2] := by
      apply MvPolynomial.ringHom_ext'; · ext c; simp [shear3, aff1, tr_u]
      · intro i; match i with | 0 => simp [L0] | 1 => simp [L1] | 2 => simp [L2]
    exact RingHom.congr_fun heq P
  have hL0_ev : eval ![0, 0] L0 = Lu⁻¹ * u 0 := by simpa [L0] using htr_ev0 (X 0)
  have hL1_ev : eval ![0, 0] L1 = Lu⁻¹ * u 1 := by simpa [L1] using htr_ev0 (X 1)
  have hL2_ev : eval ![0, 0] L2 = Lu⁻¹ * u 2 := by simpa [L2] using htr_ev0 (X 2)
  have hqFx : eval q (MvPolynomial.pderiv 0 F) = 0 := by
    apply hι_inj; rw [map_zero, ← eval_map_eq_map_eval]
    have hpd : (MvPolynomial.pderiv 0 F).map ι = MvPolynomial.pderiv 0 FK := MvPolynomial.pderiv_map.symm
    rw [hpd]; exact hFX0
  have hqFy : eval q (MvPolynomial.pderiv 1 F) = 0 := by
    apply hι_inj; rw [map_zero, ← eval_map_eq_map_eval]
    have hpd : (MvPolynomial.pderiv 1 F).map ι = MvPolynomial.pderiv 1 FK := MvPolynomial.pderiv_map.symm
    rw [hpd]; exact hFY0
  have hqFz : eval q (MvPolynomial.pderiv 2 F) = 0 := by
    apply hι_inj; rw [map_zero, ← eval_map_eq_map_eval]
    have hpd : (MvPolynomial.pderiv 2 F).map ι = MvPolynomial.pderiv 2 FK := MvPolynomial.pderiv_map.symm
    rw [hpd]; exact hFZ0
  have hvo2_fu : VanishesOrder 2 (tr_u (aff1 (shear3 α β γ FK))) → VanishesOrder 2 f_u := by
    intro hvo
    have hf_eq : f_u = C cF⁻¹ * tr_u (aff1 (shear3 α β γ FK)) := by
      dsimp only [f_u, FK]; rw [map_mul, map_mul]; congr 1; simp [tr_u, aff1]
    rw [hf_eq]
    have hC0 : VanishesOrder 0 (C cF⁻¹ : MvPolynomial (Fin 2) K) := fun _ hm => absurd hm (by omega)
    have := vanishesOrder_mul hC0 hvo; rwa [zero_add] at this
  have hD6 : 2 * p + 10 * n - 14 = D + 6 := by omega
  by_cases hq2 : q 2 ≠ 0
  · have hq2K : u 2 ≠ 0 := fun h => hq2 (hι_inj (h.trans (map_zero ι).symm))
    obtain ⟨hvoF, hvoW⟩ := singular_vo_chart ι hn3 h2np F q L0 L1 L2 hFh hq2 hqF hqFx hqFy
      (by rw [map_sub, map_mul, eval_C, hL0_ev, hL2_ev, map_div₀]; change Lu⁻¹ * u 0 - u 0 / u 2 * (Lu⁻¹ * u 2) = 0; field_simp [hq2K]; ring)
      (by rw [map_sub, map_mul, eval_C, hL1_ev, hL2_ev, map_div₀]; change Lu⁻¹ * u 1 - u 1 / u 2 * (Lu⁻¹ * u 2) = 0; field_simp [hq2K]; ring)
    rw [← hev_L] at hvoF hvoW
    exact singular_from_chart_X5_dvd ι hn3 h2np hFh hHh α β γ hFK_O hLu haxis 2 (W10Z p n F) hq2
      (hD6 ▸ W10Z_isHomogeneous (p := p) hn3 (by omega) hFh) hHZ hres_ne hvoW (hvo2_fu hvoF)
  · by_cases hq0 : q 0 ≠ 0
    · have hq0K : u 0 ≠ 0 := fun h => hq0 (hι_inj (h.trans (map_zero ι).symm))
      let F₁ := rot3.symm F; let q₁ : Fin 3 → ZMod p := q ∘ cyc3
      have hev_L1 : ∀ P : MvPolynomial (Fin 3) (ZMod p),
          MvPolynomial.eval₂Hom C ![L1, L2, L0] ((rot3.symm P).map ι) = tr_u (aff1 (shear3 α β γ (P.map ι))) := by
        intro P; rw [hev_L]
        have heq : ((MvPolynomial.eval₂Hom C ![L1, L2, L0]).comp (MvPolynomial.map ι)).comp rot3.symm.toRingHom =
            (MvPolynomial.eval₂Hom C ![L0, L1, L2]).comp (MvPolynomial.map ι) := by
          apply MvPolynomial.ringHom_ext'; · ext c; simp [rot3]
          · intro i
            simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
            have hX : rot3.symm (X i : MvPolynomial (Fin 3) (ZMod p)) = X (cyc3.symm i) := MvPolynomial.rename_X cyc3.symm i
            rw [hX, MvPolynomial.map_X, MvPolynomial.map_X]
            match i with | 0 => simp [cyc3] | 1 => simp [cyc3] | 2 => simp [cyc3]
        exact RingHom.congr_fun heq P
      have hq1_comp : q₁ ∘ cyc3.symm = q := by ext i; simp [q₁]
      have hq1_0 : eval q₁ F₁ = 0 := by dsimp only [F₁]; rw [eval_rot3_symm_eq, hq1_comp]; exact hqF
      have hq1_x : eval q₁ (MvPolynomial.pderiv 0 F₁) = 0 := by
        dsimp only [F₁]; rw [pderiv_rot3_symm 0 F, eval_rot3_symm_eq, hq1_comp]; exact hqFy
      have hq1_y : eval q₁ (MvPolynomial.pderiv 1 F₁) = 0 := by
        dsimp only [F₁]; rw [pderiv_rot3_symm 1 F, eval_rot3_symm_eq, hq1_comp]; exact hqFz
      obtain ⟨hvoF, hvoW⟩ := singular_vo_chart ι hn3 h2np F₁ q₁ L1 L2 L0 (rot3_symm_isHomogeneous hFh) hq0 hq1_0 hq1_x hq1_y
        (by rw [map_sub, map_mul, eval_C, hL1_ev, hL0_ev, map_div₀]; change Lu⁻¹ * u 1 - u 1 / u 0 * (Lu⁻¹ * u 0) = 0; field_simp [hq0K]; ring)
        (by rw [map_sub, map_mul, eval_C, hL2_ev, hL0_ev, map_div₀]; change Lu⁻¹ * u 2 - u 2 / u 0 * (Lu⁻¹ * u 0) = 0; field_simp [hq0K]; ring)
      rw [hev_L1 F] at hvoF
      have hW1_eq : W10Z p n F₁ = rot3.symm (W10X p n F) := by unfold W10X; rw [RingEquiv.symm_apply_apply]
      rw [hW1_eq, hev_L1 (W10X p n F)] at hvoW
      exact singular_from_chart_X5_dvd ι hn3 h2np hFh hHh α β γ hFK_O hLu haxis 0 (W10X p n F) hq0
        (hD6 ▸ W10X_isHomogeneous (p := p) hn3 (by omega) hFh) hHX hres_ne hvoW (hvo2_fu hvoF)
    · have hq1 : q 1 ≠ 0 := by
        rcases hq_norm with h0 | ⟨_, h1⟩ | ⟨_, _, h2⟩
        · exact absurd (by rw [h0]; exact one_ne_zero) hq0
        · rw [h1]; exact one_ne_zero
        · exact absurd (by rw [h2]; exact one_ne_zero) hq2
      have hq1K : u 1 ≠ 0 := fun h => hq1 (hι_inj (h.trans (map_zero ι).symm))
      let F₂ := rot3 F; let q₂ : Fin 3 → ZMod p := q ∘ cyc3.symm
      have hev_L2 : ∀ P : MvPolynomial (Fin 3) (ZMod p),
          MvPolynomial.eval₂Hom C ![L2, L0, L1] ((rot3 P).map ι) = tr_u (aff1 (shear3 α β γ (P.map ι))) := by
        intro P; rw [hev_L]
        have heq : ((MvPolynomial.eval₂Hom C ![L2, L0, L1]).comp (MvPolynomial.map ι)).comp rot3.toRingHom =
            (MvPolynomial.eval₂Hom C ![L0, L1, L2]).comp (MvPolynomial.map ι) := by
          apply MvPolynomial.ringHom_ext'; · ext c; simp [rot3]
          · intro i
            simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
              rot3_X, MvPolynomial.map_X]
            match i with | 0 => simp [cyc3] | 1 => simp [cyc3] | 2 => simp [cyc3]
        exact RingHom.congr_fun heq P
      have hq2_comp : q₂ ∘ cyc3 = q := by ext i; simp [q₂]
      have hq2_0 : eval q₂ F₂ = 0 := by dsimp only [F₂]; rw [eval_rot3_eq, hq2_comp]; exact hqF
      have hrot_pd : ∀ k : Fin 3, MvPolynomial.pderiv (cyc3 k) (rot3 F) = rot3 (MvPolynomial.pderiv k F) := by
        intro k
        have h1 := congrArg rot3 (pderiv_rot3_symm k (rot3 F))
        rw [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at h1; exact h1.symm
      have hq2_x : eval q₂ (MvPolynomial.pderiv 0 F₂) = 0 := by
        have hc : (0 : Fin 3) = cyc3 2 := rfl
        dsimp only [F₂]; rw [hc, hrot_pd 2, eval_rot3_eq, hq2_comp]; exact hqFz
      have hq2_y : eval q₂ (MvPolynomial.pderiv 1 F₂) = 0 := by
        have hc : (1 : Fin 3) = cyc3 0 := rfl
        dsimp only [F₂]; rw [hc, hrot_pd 0, eval_rot3_eq, hq2_comp]; exact hqFx
      obtain ⟨hvoF, hvoW⟩ := singular_vo_chart ι hn3 h2np F₂ q₂ L2 L0 L1 (rot3_isHomogeneous hFh) hq1 hq2_0 hq2_x hq2_y
        (by rw [map_sub, map_mul, eval_C, hL2_ev, hL1_ev, map_div₀]; change Lu⁻¹ * u 2 - u 2 / u 1 * (Lu⁻¹ * u 1) = 0; field_simp [hq1K]; ring)
        (by rw [map_sub, map_mul, eval_C, hL0_ev, hL1_ev, map_div₀]; change Lu⁻¹ * u 0 - u 0 / u 1 * (Lu⁻¹ * u 1) = 0; field_simp [hq1K]; ring)
      rw [hev_L2 F] at hvoF
      have hW2_eq : W10Z p n F₂ = rot3 (W10Y p n F) := by unfold W10Y; rw [RingEquiv.apply_symm_apply]
      rw [hW2_eq, hev_L2 (W10Y p n F)] at hvoW
      have hWY_hom : (W10Y p n F).IsHomogeneous (D + 6) := by
        unfold W10Y
        exact hD6 ▸ rot3_symm_isHomogeneous (W10Z_isHomogeneous (p := p) hn3 (by omega) (rot3_isHomogeneous hFh))
      exact singular_from_chart_X5_dvd ι hn3 h2np hFh hHh α β γ hFK_O hLu haxis 1 (W10Y p n F) hq1
        hWY_hom hHY hres_ne hvoW (hvo2_fu hvoF)

-- Helper: non-vanishing of resultant of irreducible monic f₀ and non-multiple f₁
lemma resultant_finSuccEquiv_ne_zero {K : Type*} [Field K] {n D : ℕ} (hn : 1 ≤ n)
    {F' H' : MvPolynomial (Fin 3) K}
    (hF'_irr : Irreducible F') (hF'_ndvd_H' : ¬ (F' ∣ H'))
    (hf0_nd : (MvPolynomial.finSuccEquiv K 2 F').natDegree = n)
    (hf0_mon : (MvPolynomial.finSuccEquiv K 2 F').Monic)
    (hf1_nd : (MvPolynomial.finSuccEquiv K 2 H').natDegree = D) :
    (MvPolynomial.finSuccEquiv K 2 F').resultant (MvPolynomial.finSuccEquiv K 2 H') n D ≠ 0 := by
  let f₀ := MvPolynomial.finSuccEquiv K 2 F'
  let f₁ := MvPolynomial.finSuccEquiv K 2 H'
  let : GCDMonoid (MvPolynomial (Fin 2) K) := UniqueFactorizationMonoid.toGCDMonoid _
  let FracR := FractionRing (MvPolynomial (Fin 2) K)
  let ιF := algebraMap (MvPolynomial (Fin 2) K) FracR
  have hιF_inj : Function.Injective ιF := IsFractionRing.injective _ _
  have hf0_irr : Irreducible f₀ := by
    let e := (MvPolynomial.finSuccEquiv K 2).toRingEquiv
    have hnotu : ¬ IsUnit (e F') := fun hu => hF'_irr.not_isUnit (by have := hu.map e.symm.toRingHom; simpa using this)
    refine ⟨hnotu, ?_⟩
    intro a b hab
    have hback : F' = e.symm a * e.symm b := by have := congrArg e.symm hab; simpa [e, f₀, map_mul] using this
    rcases hF'_irr.isUnit_or_isUnit hback with ha | hb
    · left; have := ha.map e.toRingHom; simpa using this
    · right; have := hb.map e.toRingHom; simpa using this
  have hf0_map_irr : Irreducible (f₀.map ιF) :=
    (Polynomial.IsPrimitive.irreducible_iff_irreducible_map_fraction_map hf0_mon.isPrimitive).mp hf0_irr
  have hndvd_map : ¬ (f₀.map ιF ∣ f₁.map ιF) := by
    rintro ⟨q, hq⟩
    have hdiv : f₁ = f₀ * (f₁ /ₘ f₀) + f₁ %ₘ f₀ := (Polynomial.modByMonic_add_div f₁ f₀).symm.trans (add_comm _ _)
    have hrem0 : (f₁ %ₘ f₀).map ιF = 0 := by
      have h1 := congrArg (Polynomial.map ιF) hdiv
      rw [Polynomial.map_add, Polynomial.map_mul, hq] at h1
      have hdvd_rem : f₀.map ιF ∣ (f₁ %ₘ f₀).map ιF := ⟨q - (f₁ /ₘ f₀).map ιF, by linear_combination -h1⟩
      by_contra hne
      have hle := Polynomial.natDegree_le_of_dvd hdvd_rem hne
      have hlt : (f₁ %ₘ f₀).natDegree < f₀.natDegree :=
        Polynomial.natDegree_modByMonic_lt f₁ hf0_mon (by
          intro h1; have := congrArg Polynomial.natDegree h1; rw [hf0_nd, Polynomial.natDegree_one] at this; omega)
      rw [Polynomial.natDegree_map_eq_of_injective hιF_inj, Polynomial.natDegree_map_eq_of_injective hιF_inj] at hle
      omega
    have hrem : f₁ %ₘ f₀ = 0 := Polynomial.map_injective ιF hιF_inj (hrem0.trans (Polynomial.map_zero ιF).symm)
    rw [hrem, add_zero] at hdiv
    apply hF'_ndvd_H'
    refine ⟨(MvPolynomial.finSuccEquiv K 2).symm (f₁ /ₘ f₀), ?_⟩
    have hback := congrArg (MvPolynomial.finSuccEquiv K 2).symm hdiv
    simpa [f₀, f₁, map_mul] using hback
  have hcop := hf0_map_irr.coprime_iff_not_dvd.mpr hndvd_map
  intro h0
  have hmap0 : (f₀.map ιF).resultant (f₁.map ιF) n D = 0 := by
    rw [Polynomial.resultant_map_map]; change ιF (f₀.resultant f₁ n D) = 0; rw [h0, map_zero]
  have hnd0 : (f₀.map ιF).natDegree = n := by rw [hf0_mon.natDegree_map, hf0_nd]
  have hnd1 : (f₁.map ιF).natDegree = D := by rw [Polynomial.natDegree_map_eq_of_injective hιF_inj, hf1_nd]
  have hmap0' : (f₀.map ιF).resultant (f₁.map ιF) = 0 := by
    change (f₀.map ιF).resultant (f₁.map ιF) (f₀.map ιF).natDegree (f₁.map ιF).natDegree = 0
    rw [hnd0, hnd1]; exact hmap0
  exact (Polynomial.resultant_eq_zero_iff.mp hmap0').2 hcop

-- Main Voloch H2 bound under normalized coordinate axes F(e₀), F(e₁), F(e₂) ≠ 0 (abstract K!)
lemma voloch_H2_normalized_field {p n : ℕ} [Fact p.Prime] {K : Type*} [Field K] [IsAlgClosed K]
    (ι : ZMod p →+* K) (hp2 : p ≠ 2) (hn3 : 3 ≤ n) (h2np : 2 * n ≤ p)
    {F H : MvPolynomial (Fin 3) (ZMod p)} (hFh : F.IsHomogeneous n)
    (hHh : H.IsHomogeneous (2 * p + 10 * n - 20))
    (hFirrK : Irreducible (F.map ι))
    (hFH_ndvd : ¬ (F.map ι ∣ H.map ι))
    (he0 : eval ![1, 0, 0] F ≠ 0) (he2 : eval ![0, 0, 1] F ≠ 0)
    (hHZ : F ∣ W10Z p n F - X 2 ^ 6 * H)
    (hHX : F ∣ W10X p n F - X 0 ^ 6 * H)
    (hHY : F ∣ W10Y p n F - X 1 ^ 6 * H) :
    let Z := (univ : Finset (Fin 3 → ZMod p)).filter fun v => IsNorm v ∧ eval v F = 0
    5 * Z.card ≤ 10 * n * (n - 3) + 2 * n * (p + 5) := by
  classical
  intro Z
  have hι_inj : Function.Injective ι := RingHom.injective ι
  let D : ℕ := 2 * p + 10 * n - 20
  let FK := F.map ι
  let HK := H.map ι
  have hFK_h : FK.IsHomogeneous n := hFh.map ι
  have hHK_h : HK.IsHomogeneous D := hHh.map ι
  have hHK_ne : HK ≠ 0 := fun h0 => hFH_ndvd (by change FK ∣ HK; rw [h0]; exact dvd_zero FK)
  have he0K : eval ![1, 0, 0] FK ≠ 0 := by
    have hv : (ι ∘ ![1, 0, 0] : Fin 3 → K) = ![1, 0, 0] := by ext i; match i with | 0 => simp | 1 => simp | 2 => simp
    rw [← hv, eval_map_eq_map_eval]; exact fun h => he0 (hι_inj (h.trans (map_zero ι).symm))
  have he2K : eval ![0, 0, 1] FK ≠ 0 := by
    have hv : (ι ∘ ![0, 0, 1] : Fin 3 → K) = ![0, 0, 1] := by ext i; match i with | 0 => simp | 1 => simp | 2 => simp
    rw [← hv, eval_map_eq_map_eval]; exact fun h => he2 (hι_inj (h.trans (map_zero ι).symm))
  let embZ : (Fin 3 → ZMod p) → (Fin 3 → K) := fun q => ι ∘ q
  have hembZ_inj : Function.Injective embZ := fun q₁ q₂ h => funext fun i => hι_inj (congrFun h i)
  let ZK : Finset (Fin 3 → K) := Z.image embZ
  have hZK_card : ZK.card = Z.card := Finset.card_image_of_injective Z hembZ_inj
  have hZK_norm : ∀ u ∈ ZK, IsNorm u := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
    rcases (Finset.mem_filter.mp hq).2.1 with h0 | ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · left; simp [embZ, h0]
    · right; left; simp [embZ, h0, h1]
    · right; right; simp [embZ, h0, h1, h2]
  have hZK_F0 : ∀ u ∈ ZK, eval u FK = 0 := by
    intro u hu; rcases Finset.mem_image.mp hu with ⟨q, hq, rfl⟩
    dsimp only [embZ, FK]; rw [eval_map_eq_map_eval, (Finset.mem_filter.mp hq).2.2, map_zero]
  obtain ⟨α, β, γ, hFK_O, hHK_O, hZ_det, hZ_tan, hZ_axis, hLinf_ne⟩ :=
    exists_generic_projection hFK_h hHK_h hFirrK.ne_zero hHK_ne he0K he2K ZK hZK_norm hZK_F0
  let cF := eval ![1, α, β] FK
  let F' : MvPolynomial (Fin 3) K := C cF⁻¹ * shear3 α β γ FK
  let H' : MvPolynomial (Fin 3) K := shear3 α β γ HK
  have hF'_h : F'.IsHomogeneous n := (shear3_isHomogeneous α β γ hFK_h).C_mul _
  have hH'_h : H'.IsHomogeneous D := shear3_isHomogeneous α β γ hHK_h
  have hF'_e0 : eval ![1, 0, 0] F' = 1 := by
    dsimp only [F']; rw [map_mul, eval_C, shear3_eval]
    have hM : shear3Vec α β γ ![1, 0, 0] = ![1, α, β] := by
      ext i; match i with | 0 => simp [shear3Vec] | 1 => simp [shear3Vec] | 2 => simp [shear3Vec]
    rw [hM]; exact inv_mul_cancel₀ hFK_O
  have hH'_e0 : eval ![1, 0, 0] H' = eval ![1, α, β] HK := by
    dsimp only [H']; rw [shear3_eval]
    have hM : shear3Vec α β γ ![1, 0, 0] = ![1, α, β] := by
      ext i; match i with | 0 => simp [shear3Vec] | 1 => simp [shear3Vec] | 2 => simp [shear3Vec]
    rw [hM]
  have hF'_irr : Irreducible F' := by
    have hTF_irr : Irreducible (shear3 α β γ FK) := by
      have hnotu : ¬ IsUnit (shear3 α β γ FK) := fun hu =>
        hFirrK.not_isUnit (by have := hu.map (shear3Inv α β γ); rwa [shear3Inv_shear3] at this)
      refine ⟨hnotu, ?_⟩
      intro a b hab
      have hback : FK = shear3Inv α β γ a * shear3Inv α β γ b := by
        have := congrArg (shear3Inv α β γ) hab; rwa [shear3Inv_shear3, map_mul] at this
      rcases hFirrK.isUnit_or_isUnit hback with ha | hb
      · left; have := ha.map (shear3 α β γ); rwa [shear3_shear3Inv] at this
      · right; have := hb.map (shear3 α β γ); rwa [shear3_shear3Inv] at this
    have hu : IsUnit (C cF⁻¹ : MvPolynomial (Fin 3) K) := (isUnit_iff_ne_zero.mpr (inv_ne_zero hFK_O)).map C
    exact (associated_unit_mul_left (shear3 α β γ FK) (C cF⁻¹) hu).irreducible_iff.mpr hTF_irr
  have hF'_ndvd_H' : ¬ (F' ∣ H') := by
    rintro ⟨Q, hQ⟩; apply hFH_ndvd; refine ⟨C cF⁻¹ * shear3Inv α β γ Q, ?_⟩
    have h1 := congrArg (shear3Inv α β γ) hQ
    dsimp only [F', H', FK, HK] at h1
    rw [map_mul, map_mul, shear3Inv_shear3, shear3Inv_shear3] at h1
    have hC : shear3Inv α β γ (C cF⁻¹) = C cF⁻¹ := by simp [shear3Inv]
    rw [hC] at h1; rw [h1]; ring
  let f₀ := MvPolynomial.finSuccEquiv K 2 F'
  let f₁ := MvPolynomial.finSuccEquiv K 2 H'
  have hf0_c : f₀.coeff n = 1 := by dsimp only [f₀]; rw [finSuccEquiv_coeff_top hF'_h, hF'_e0, map_one]
  have hf0_nd : f₀.natDegree = n :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (finSuccEquiv_coeff_hom hF'_h).2)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hf0_c]; exact one_ne_zero))
  have hf0_mon : f₀.Monic := by rw [Polynomial.Monic, Polynomial.leadingCoeff, hf0_nd]; exact hf0_c
  have hf1_c : f₁.coeff D = C (eval ![1, α, β] HK) := by dsimp only [f₁]; rw [finSuccEquiv_coeff_top hH'_h, hH'_e0]
  have hf1_nd : f₁.natDegree = D :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (finSuccEquiv_coeff_hom hH'_h).2)
      (Polynomial.le_natDegree_of_ne_zero (by rw [hf1_c]; exact MvPolynomial.C_ne_zero.mpr hHK_O))
  let Res : MvPolynomial (Fin 2) K := f₀.resultant f₁ n D
  have hRes_hom : Res.IsHomogeneous (n * D) :=
    resultant_isHomogeneous_general (finSuccEquiv_coeff_hom hF'_h).1 (finSuccEquiv_coeff_hom hH'_h).1
  have hRes_ne : Res ≠ 0 :=
    resultant_finSuccEquiv_ne_zero (by omega) hF'_irr hF'_ndvd_H' hf0_nd hf0_mon hf1_nd
  let r : Polynomial K := dehomog1 Res
  have hr_ne : r ≠ 0 := dehomog1_ne_zero_of_isHomogeneous hRes_hom hRes_ne
  have hr_deg : r.natDegree ≤ n * D := natDegree_dehomog1_le hRes_hom
  have hr_eq_res : r = (mv2ToPolyY K (aff1 F')).resultant (mv2ToPolyY K (aff1 H')) n D := by
    dsimp only [r, Res, f₀, f₁]; rw [← Polynomial.resultant_map_map, map_dehomog1_finSuccEquiv, map_dehomog1_finSuccEquiv]
  have hpf_aff_mon : (mv2ToPolyY K (aff1 F')).Monic := by
    rw [← map_dehomog1_finSuccEquiv]; exact hf0_mon.map dehomog1
  have hpf_aff_nd : (mv2ToPolyY K (aff1 F')).natDegree = n := by
    rw [← map_dehomog1_finSuccEquiv, hf0_mon.natDegree_map, hf0_nd]
  have hph_aff_nd : (mv2ToPolyY K (aff1 H')).natDegree ≤ D := by
    rw [← map_dehomog1_finSuccEquiv]; exact Polynomial.natDegree_map_le.trans (le_of_eq hf1_nd)
  let x_proj : (Fin 3 → K) → K := fun u => (u 1 - α * u 0) / ((u 2 - β * u 0) + γ * (u 1 - α * u 0))
  have hx_inj : Set.InjOn x_proj ZK := by
    intro u hu v hv heq; by_contra hne
    dsimp only [x_proj] at heq; rw [div_eq_div_iff (hLinf_ne u hu) (hLinf_ne v hv)] at heq
    apply hZ_det u hu v hv hne; linear_combination heq
  have hmult5 : ∀ u ∈ ZK, (Polynomial.X - Polynomial.C (x_proj u)) ^ 5 ∣ r := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨q, hqZ, rfl⟩
    let u := embZ q
    have hq_norm : IsNorm q := (Finset.mem_filter.mp hqZ).2.1
    have hqF : eval q F = 0 := (Finset.mem_filter.mp hqZ).2.2
    let Lu := (u 2 - β * u 0) + γ * (u 1 - α * u 0)
    let xu := (u 1 - α * u 0) / Lu
    let yu := u 0 / Lu
    let tr_u : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
      MvPolynomial.eval₂Hom C ![C xu + X 0, C yu + X 1]
    let f_u := tr_u (aff1 F')
    let h_u := tr_u (aff1 H')
    let τx : Polynomial K →+* Polynomial K := Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C xu)
    have hr_shift_eq : r.comp (Polynomial.X + Polynomial.C xu) =
        (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n D := by
      have hτ : τx r = r.comp (Polynomial.X + Polynomial.C xu) := rfl
      rw [← hτ, hr_eq_res, ← Polynomial.resultant_map_map]
      have hph_map_nd : ((mv2ToPolyY K (aff1 H')).map τx).natDegree ≤ D :=
        Polynomial.natDegree_map_le.trans hph_aff_nd
      have h1 := resultant_comp_X_add_C (hpf_aff_mon.map τx)
        (by rw [hpf_aff_mon.natDegree_map, hpf_aff_nd])
        hph_map_nd (Polynomial.C yu)
      rw [← h1]
      dsimp only [f_u, h_u]
      rw [shear3_tr_poly xu yu (aff1 F'), shear3_tr_poly xu yu (aff1 H')]
    have hshift_ne : (mv2ToPolyY K f_u).resultant (mv2ToPolyY K h_u) n D ≠ 0 := by
      rw [← hr_shift_eq]; intro h0
      have hback := congrArg (fun P : Polynomial K => P.comp (Polynomial.X - Polynomial.C xu)) h0
      rw [Polynomial.comp_assoc, Polynomial.zero_comp] at hback
      have hid : (Polynomial.X + Polynomial.C xu).comp (Polynomial.X - Polynomial.C xu) = Polynomial.X := by
        simp [Polynomial.add_comp]
      rw [hid, Polynomial.comp_X] at hback; exact hr_ne hback
    have hX5_shift : Polynomial.X ^ 5 ∣ r.comp (Polynomial.X + Polynomial.C xu) := by
      rw [hr_shift_eq]
      by_cases hsm : eval u (MvPolynomial.pderiv 0 FK) ≠ 0 ∨ eval u (MvPolynomial.pderiv 1 FK) ≠ 0 ∨
          eval u (MvPolynomial.pderiv 2 FK) ≠ 0
      · exact smooth_point_X5_dvd_shift ι hp2 hn3 h2np hFh hHh hHZ hHX hHY α β γ hFK_O hq_norm hqF
          (hLinf_ne u hu) hsm (hZ_tan u hu hsm)
      · rw [not_or, not_or, not_not, not_not, not_not] at hsm
        rcases hsm with ⟨h0, h1, h2⟩
        exact singular_point_X5_dvd_shift ι hn3 h2np hFh hHh hHZ hHX hHY α β γ hFK_O hq_norm hqF
          (hLinf_ne u hu) h0 h1 h2 (hZ_axis u hu) hshift_ne
    rcases hX5_shift with ⟨Q, hQ⟩
    refine ⟨Q.comp (Polynomial.X - Polynomial.C xu), ?_⟩
    have h1 := congrArg (fun P : Polynomial K => P.comp (Polynomial.X - Polynomial.C xu)) hQ
    rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp] at h1
    have hid : (Polynomial.X + Polynomial.C xu).comp (Polynomial.X - Polynomial.C xu) = Polynomial.X := by
      simp [Polynomial.add_comp]
    rw [hid, Polynomial.comp_X] at h1; exact h1
  let S : Finset K := ZK.image x_proj
  have hS_card : S.card = Z.card := by rw [Finset.card_image_of_injOn hx_inj, hZK_card]
  have hsum_le : 5 * S.card ≤ ∑ x ∈ S, r.roots.count x := by
    calc 5 * S.card = ∑ _ ∈ S, 5 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ S, r.roots.count x := by
          apply Finset.sum_le_sum; intro x hx
          rcases Finset.mem_image.mp hx with ⟨u, hu, rfl⟩
          rw [Polynomial.count_roots, Polynomial.le_rootMultiplicity_iff hr_ne]
          exact hmult5 u hu
  have hbound : 5 * Z.card ≤ n * D := by
    calc 5 * Z.card = 5 * S.card := by rw [hS_card]
      _ ≤ ∑ x ∈ S, r.roots.count x := hsum_le
      _ ≤ r.roots.card := sum_count_le_card S r.roots
      _ ≤ r.natDegree := Polynomial.card_roots' r
      _ ≤ n * D := hr_deg
  have halg : n * D = 10 * n * (n - 3) + 2 * n * (p + 5) := by
    dsimp only [D]
    have h1 : 10 * n * (n - 3) + 30 * n = 10 * n * n := by
      have : n - 3 + 3 = n := by omega
      calc 10 * n * (n - 3) + 30 * n = 10 * n * ((n - 3) + 3) := by ring
        _ = 10 * n * n := by rw [this]
    have h2 : n * (2 * p + 10 * n - 20) + 20 * n = n * (2 * p + 10 * n) := by
      have : 2 * p + 10 * n - 20 + 20 = 2 * p + 10 * n := by omega
      calc n * (2 * p + 10 * n - 20) + 20 * n = n * ((2 * p + 10 * n - 20) + 20) := by ring
        _ = n * (2 * p + 10 * n) := by rw [this]
    have h3 : n * (2 * p + 10 * n) + 10 * n = 10 * n * n + 2 * n * (p + 5) := by ring
    omega
  omega

-- 6.7 Top-level linear change of variables & Final Assembly
noncomputable def linMap3 {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    MvPolynomial (Fin 3) R →+* MvPolynomial (Fin 3) R :=
  MvPolynomial.eval₂Hom C (fun i => ∑ j : Fin 3, C (A i j) * X j)

lemma linMap3_eval {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R)
    (P : MvPolynomial (Fin 3) R) (v : Fin 3 → R) :
    eval v (linMap3 A P) = eval (A.mulVec v) P := by
  have heq : (eval v).comp (linMap3 A) = eval (A.mulVec v) := by
    apply MvPolynomial.ringHom_ext'
    · ext c; simp [linMap3]
    · intro i
      simp only [RingHom.comp_apply, linMap3, MvPolynomial.eval₂Hom_X', map_sum, map_mul,
        eval_C, eval_X, Matrix.mulVec, dotProduct]
  exact RingHom.congr_fun heq P

lemma linMap3_comp {R : Type*} [CommRing R] (A B : Matrix (Fin 3) (Fin 3) R)
    (P : MvPolynomial (Fin 3) R) :
    linMap3 B (linMap3 A P) = linMap3 (A * B) P := by
  have heq : (linMap3 B).comp (linMap3 A) = linMap3 (A * B) := by
    apply MvPolynomial.ringHom_ext'
    · ext c; simp [linMap3]
    · intro i
      simp only [RingHom.comp_apply, linMap3, MvPolynomial.eval₂Hom_X', map_sum, map_mul,
        MvPolynomial.eval₂Hom_C, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro j _
      ring
  exact RingHom.congr_fun heq P

lemma linMap3_one {R : Type*} [CommRing R] (P : MvPolynomial (Fin 3) R) :
    linMap3 1 P = P := by
  have heq : linMap3 (1 : Matrix (Fin 3) (Fin 3) R) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · ext c; simp [linMap3]
    · intro i
      simp only [linMap3, MvPolynomial.eval₂Hom_X', RingHom.id_apply, Matrix.one_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (mem_univ i) h
  exact RingHom.congr_fun heq P

lemma linMap3_isHomogeneous {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) {d : ℕ}
    {P : MvPolynomial (Fin 3) R} (hPh : P.IsHomogeneous d) :
    (linMap3 A P).IsHomogeneous d := by
  rw [P.as_sum, map_sum]
  apply IsHomogeneous.sum; intro s hs
  dsimp only [linMap3]; rw [MvPolynomial.eval₂Hom_monomial]
  apply IsHomogeneous.C_mul
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ i : Fin 3, ((∑ j : Fin 3, C (A i j) * X j : MvPolynomial (Fin 3) R) ^ s i).IsHomogeneous (s i) := by
    intro i
    have hlin1 : (∑ j : Fin 3, C (A i j) * X j : MvPolynomial (Fin 3) R).IsHomogeneous 1 :=
      IsHomogeneous.sum univ _ _ (fun j _ => (isHomogeneous_X R j).C_mul (A i j))
    simpa using hlin1.pow (s i)
  have hpr := IsHomogeneous.prod univ _ (fun i => s i) (fun i _ => h1 i)
  rwa [isHomogeneous_sum_eq hPh hs] at hpr

lemma linMap3_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (A : Matrix (Fin 3) (Fin 3) R) (P : MvPolynomial (Fin 3) R) :
    (linMap3 A P).map φ = linMap3 (A.map φ) (P.map φ) := by
  have heq : (MvPolynomial.map φ).comp (linMap3 A) = (linMap3 (A.map φ)).comp (MvPolynomial.map φ) := by
    apply MvPolynomial.ringHom_ext'
    · ext c; simp [linMap3]
    · intro i; simp [linMap3]
  exact RingHom.congr_fun heq P

theorem voloch_H2_main :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (n : ℕ)
      (F : MvPolynomial (Fin 3) (ZMod p)),
      3 ≤ n → 2 * n ≤ p → F.IsHomogeneous n →
      Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) F) →
      let Z := (univ : Finset (Fin 3 → ZMod p)).filter fun v =>
        (v 0 = 1 ∨ (v 0 = 0 ∧ v 1 = 1) ∨
          (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 1)) ∧ eval v F = 0
      5 * Z.card ≤ 10 * n * (n - 3) + 2 * n * (p + 5) := by
  classical
  intro p _ hp2 n F hn3 h2np hFh hFirrK Z
  let K := AlgebraicClosure (ZMod p)
  let ι := algebraMap (ZMod p) K
  have hFirr : Irreducible F := irreducible_of_map_irreducible hFirrK
  obtain ⟨M, hM_unit, hMe0, hMe1, hMe2⟩ := exists_basis_eval_ne_zero hFh hFirr.ne_zero (by omega)
  let F' := linMap3 M F
  have hF'_h : F'.IsHomogeneous n := linMap3_isHomogeneous M hFh
  have hF'_irrK : Irreducible (F'.map ι) := by
    have hMMi : M.map ι * M⁻¹.map ι = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M hM_unit, Matrix.map_one ι (map_zero ι) (map_one ι)]
    have hMiM : M⁻¹.map ι * M.map ι = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul M hM_unit, Matrix.map_one ι (map_zero ι) (map_one ι)]
    dsimp only [F']; rw [linMap3_map]
    have hnotu : ¬ IsUnit (linMap3 (M.map ι) (F.map ι)) := fun hu =>
      hFirrK.not_isUnit (by have := hu.map (linMap3 (M⁻¹.map ι)); rwa [linMap3_comp, hMMi, linMap3_one] at this)
    refine ⟨hnotu, ?_⟩
    intro a b hab
    have hback : F.map ι = linMap3 (M⁻¹.map ι) a * linMap3 (M⁻¹.map ι) b := by
      have := congrArg (linMap3 (M⁻¹.map ι)) hab
      rwa [linMap3_comp, hMMi, linMap3_one, map_mul] at this
    rcases hFirrK.isUnit_or_isUnit hback with ha | hb
    · left; have := ha.map (linMap3 (M.map ι)); rwa [linMap3_comp, hMiM, linMap3_one] at this
    · right; have := hb.map (linMap3 (M.map ι)); rwa [linMap3_comp, hMiM, linMap3_one] at this
  have hF'_e0 : eval ![1, 0, 0] F' ≠ 0 := by
    dsimp only [F']; rw [linMap3_eval]
    have h1 : M.mulVec ![1, 0, 0] = fun i => M i 0 := by ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [h1]; exact hMe0
  have hF'_e1 : eval ![0, 1, 0] F' ≠ 0 := by
    dsimp only [F']; rw [linMap3_eval]
    have h1 : M.mulVec ![0, 1, 0] = fun i => M i 1 := by ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [h1]; exact hMe1
  have hF'_e2 : eval ![0, 0, 1] F' ≠ 0 := by
    dsimp only [F']; rw [linMap3_eval]
    have h1 : M.mulVec ![0, 0, 1] = fun i => M i 2 := by ext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rw [h1]; exact hMe2
  have hF'_irr : Irreducible F' := irreducible_of_map_irreducible hF'_irrK
  obtain ⟨H', hH'h, hH'Z, hH'X, hH'Y⟩ :=
    exists_projective_H hp2 hn3 h2np hF'_h hF'_irr hF'_e0 hF'_e1 hF'_e2
  have hF'_ndvd_H' : ¬ (F'.map ι ∣ H'.map ι) :=
    not_F_dvd_H hp2 hn3 h2np hF'_h hF'_irrK hF'_e0 hF'_e1 hH'Z
  let Z' := (univ : Finset (Fin 3 → ZMod p)).filter fun v => IsNorm v ∧ eval v F' = 0
  have hZ_le : Z.card ≤ Z'.card := by
    let φ : (Fin 3 → ZMod p) → (Fin 3 → ZMod p) := fun v => norm3 (M⁻¹.mulVec v)
    have hMiv_ne : ∀ v ∈ Z, M⁻¹.mulVec v ≠ 0 := by
      intro v hv h0
      have h1 := congrArg M.mulVec h0
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM_unit, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      exact isNorm_ne_zero (Finset.mem_filter.mp hv).2.1 h1
    have hφ_maps : ∀ v ∈ Z, φ v ∈ Z' := by
      intro v hv
      obtain ⟨c, _, hc⟩ := norm3_exists_smul (hMiv_ne v hv)
      rw [Finset.mem_filter]
      refine ⟨mem_univ _, norm3_isNorm (hMiv_ne v hv), ?_⟩
      dsimp only [φ, F']
      rw [hc, isHomogeneous_eval_smul hF'_h, linMap3_eval, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv M hM_unit, Matrix.one_mulVec, (Finset.mem_filter.mp hv).2.2, mul_zero]
    have hφ_inj : Set.InjOn φ Z := by
      intro v₁ hv₁ v₂ hv₂ heq
      obtain ⟨c₁, hc₁, hsm₁⟩ := norm3_exists_smul (hMiv_ne v₁ hv₁)
      obtain ⟨c₂, hc₂, hsm₂⟩ := norm3_exists_smul (hMiv_ne v₂ hv₂)
      have hsm : c₁ • M⁻¹.mulVec v₁ = c₂ • M⁻¹.mulVec v₂ := by rw [← hsm₁, ← hsm₂]; exact heq
      have hback := congrArg M.mulVec hsm
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv M hM_unit, Matrix.one_mulVec, Matrix.one_mulVec] at hback
      have hv1_eq : v₁ = (c₁⁻¹ * c₂) • v₂ := by
        calc v₁ = c₁⁻¹ • (c₁ • v₁) := by rw [inv_smul_smul₀ hc₁]
          _ = c₁⁻¹ • (c₂ • v₂) := by rw [hback]
          _ = (c₁⁻¹ * c₂) • v₂ := by rw [smul_smul]
      exact isNorm_eq_of_smul (Finset.mem_filter.mp hv₁).2.1 (Finset.mem_filter.mp hv₂).2.1 hv1_eq
    calc Z.card = (Z.image φ).card := (Finset.card_image_of_injOn hφ_inj).symm
      _ ≤ Z'.card := Finset.card_le_card (Finset.image_subset_iff.mpr hφ_maps)
  have hbound : 5 * Z'.card ≤ 10 * n * (n - 3) + 2 * n * (p + 5) :=
    voloch_H2_normalized_field ι hp2 hn3 h2np hF'_h hH'h hF'_irrK hF'_ndvd_H' hF'_e0 hF'_e2 hH'Z hH'X hH'Y
  omega

end LocalMultAndBezout

end VolochH2Proof

theorem OMA.solution : OMA.R_Green68_green_68_variants_voloch_R2.H2 :=
  VolochH2Proof.voloch_H2_main
