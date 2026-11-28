import FormalConjectures.ErdosProblems.«1046»
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.LinearCombination

/-! Polynomial power sums of scaled root differences give the diameter bound by
the maximum modulus principle. The long-chord argument is adapted from
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1421. -/

open Polynomial Finset Metric

namespace OMA

private lemma enumRoots (p : ℂ[X]) {n : ℕ} (h : p.natDegree = n) :
    ∃ a : Fin n → ℂ, Finset.univ.val.map a = p.roots := by
  classical
  have hc : Fintype.card p.roots = n := by
    simpa using (splits_iff_card_roots.mp (IsAlgClosed.splits p)).trans h
  let e : Fin n ≃ p.roots := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨fun i => (e i : ℂ), ?_⟩
  change Finset.univ.val.map ((fun x : p.roots => (x : ℂ)) ∘ e) = p.roots
  rw [← Multiset.map_map, Multiset.map_univ_val_equiv, Multiset.map_univ_coe]

private lemma symmetricEval (n k : ℕ) :
    ∃ p : MvPolynomial (Fin n) ℂ,
      MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p =
        MvPolynomial.psum (Fin n) ℂ k := by
  classical
  let q : MvPolynomial.symmetricSubalgebra (Fin n) ℂ :=
    ⟨_, MvPolynomial.psum_isSymmetric (Fin n) ℂ k⟩
  have h := MvPolynomial.esymmAlgHom_surjective (σ := Fin n) (R := ℂ)
    (show Fintype.card (Fin n) ≤ n by simp)
  obtain ⟨p, hp⟩ := h q
  exact ⟨p, by
    rw [← MvPolynomial.esymmAlgHom_apply, hp]⟩

private lemma signedCoeff {p : ℂ[X]} (hp : p.Monic) {i : ℕ} (hi : i ≤ p.natDegree) :
    (-1 : ℂ)^i * p.coeff (p.natDegree - i) = p.roots.esymm i := by
  have hsub : p.natDegree - (p.natDegree - i) = i := by omega
  rw [coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p) (Nat.sub_le ..), hp.leadingCoeff,
    hsub, one_mul, ← mul_assoc, ← mul_pow]
  norm_num

private lemma powerSumPoly (H : (ℂ[X])[X]) (hH : H.Monic) (k : ℕ) :
    ∃ q : ℂ[X], ∀ v : ℂ,
      q.eval v = (((H.map (evalRingHom v)).roots).map (· ^ k)).sum := by
  classical
  let n := H.natDegree
  obtain ⟨p, hp⟩ := symmetricEval n k
  let coeffs : Fin n → ℂ[X] := fun i => (-1)^(i.val+1) * H.coeff (n - (i.val+1))
  refine ⟨MvPolynomial.aeval coeffs p, fun v => ?_⟩
  let G := H.map (evalRingHom v)
  have hG : G.Monic := hH.map _
  have hdeg : G.natDegree = n := hH.natDegree_map _
  obtain ⟨a, ha⟩ := enumRoots G hdeg
  have hcoeff (i : Fin n) :
      (coeffs i).eval v = MvPolynomial.aeval a (MvPolynomial.esymm (Fin n) ℂ (i+1)) := by
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, ha]
    have hi : i.val+1 ≤ G.natDegree := by rw [hdeg]; exact i.isLt
    simpa [coeffs, hdeg, G, coeff_map] using signedCoeff hG hi
  change (Polynomial.aeval v) (MvPolynomial.aeval coeffs p) = (G.roots.map (· ^ k)).sum
  rw [MvPolynomial.comp_aeval_apply]
  simp only [Polynomial.coe_aeval_eq_eval, hcoeff]
  rw [← MvPolynomial.comp_aeval_apply, hp, MvPolynomial.psum]
  simp only [map_sum, map_pow, MvPolynomial.aeval_X]
  rw [← ha, Finset.sum_eq_multiset_sum, Multiset.map_map]
  rfl

private lemma pairSumPoly {n : ℕ} (P Q : (ℂ[X])[X]) (hP : P.Monic) (hQ : Q.Monic)
    (m : ℕ) :
    ∃ b : ℂ[X], ∀ (v : ℂ) (x y : Fin n → ℂ),
      Finset.univ.val.map x = (P.map (evalRingHom v)).roots →
      Finset.univ.val.map y = (Q.map (evalRingHom v)).roots →
      b.eval v = ∑ i, ∑ j, (x i - y j)^m := by
  classical
  choose p hp using fun k => powerSumPoly P hP k
  choose q hq using fun k => powerSumPoly Q hQ k
  refine ⟨∑ k ∈ range (m+1), p k * q (m-k) * C ((-1)^(m-k) * (m.choose k : ℂ)), ?_⟩
  intro v x y hx hy
  have hp' (k : ℕ) : (p k).eval v = ∑ i, x i ^ k := by
    rw [hp, ← hx, sum_eq_multiset_sum, Multiset.map_map]
    rfl
  have hq' (k : ℕ) : (q k).eval v = ∑ j, y j ^ k := by
    rw [hq, ← hy, sum_eq_multiset_sum, Multiset.map_map]
    rfl
  rw [← coe_evalRingHom, map_sum]
  simp only [coe_evalRingHom, eval_mul, eval_C, hp', hq']
  calc
    _ = ∑ k ∈ range (m+1), ∑ i, ∑ j, x i ^ k * (- y j) ^ (m-k) * (m.choose k : ℂ) := by
      refine sum_congr rfl fun k _ => ?_
      simp only [sum_mul, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [neg_pow]
      ring
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sub_eq_add_neg, add_pow]

private noncomputable def scaledFamily {n : ℕ} (w : Fin n → ℂ) (a : ℂ) : (ℂ[X])[X] :=
  (∏ i, (X - C (C (w i) * X))) - C (C a)

private lemma scaledFamily_monic_degrees {n : ℕ} (hn : 0 < n) (w : Fin n → ℂ) (a : ℂ) :
    (scaledFamily w a).Monic ∧ (scaledFamily w a).natDegree = n := by
  have hmono := monic_prod_X_sub_C (fun i => C (w i) * X) Finset.univ
  have hdeg : (∏ i, (X - C (C (w i) * X))).natDegree = n := by
    rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
    simp only [natDegree_X_sub_C, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Nat.cast_id]
  have hlt : (C (C a) : (ℂ[X])[X]).natDegree < (∏ i, (X - C (C (w i) * X))).natDegree := by
    simpa only [natDegree_C, hdeg] using hn
  exact ⟨hmono.sub_of_left (degree_lt_degree hlt),
    (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hdeg⟩

private lemma scaledFamily_map {n : ℕ} (w : Fin n → ℂ) (a v : ℂ) :
    (scaledFamily w a).map (evalRingHom v) =
      (∏ i, (X - C (w i * v))) - C a := by
  simp [scaledFamily, Polynomial.map_sub, Polynomial.map_prod]

private lemma scaledFamily_zero {n : ℕ} (w : Fin n → ℂ) (a : ℂ) :
    (scaledFamily w a).map (evalRingHom 0) = X ^ n - C a := by
  rw [scaledFamily_map]
  simp

private lemma root_scaledFamily {n : ℕ} (hn : 0 < n) (w : Fin n → ℂ) {a v x : ℂ}
    (hv : v ≠ 0) (hx : x ∈ ((scaledFamily w a).map (evalRingHom v)).roots) :
    v^n * (∏ i, (x/v - w i)) = a := by
  have hmonic := (scaledFamily_monic_degrees hn w a).1.map (evalRingHom v)
  have hz := (mem_roots hmonic.ne_zero).mp hx
  rw [scaledFamily_map, IsRoot.def, eval_sub, eval_prod, eval_C, sub_eq_zero] at hz
  simp only [eval_sub, eval_X, eval_C] at hz
  calc
    v^n * (∏ i, (x/v - w i)) = ∏ i, v*(x/v - w i) := by rw [prod_mul_distrib]; simp
    _ = ∏ i, (x - w i * v) := by
      refine prod_congr rfl fun i _ => ?_
      rw [mul_sub, mul_div_cancel₀ _ hv, mul_comm v]
    _ = a := hz

private lemma normalized_nonnegative {n j : ℕ} {x y : ℂ}
    (hn : 0 < n) (hx : x^n = 1) (hy : y^n = (-1)^n) :
    0 ≤ ((x-y)^(2*n*j)).re := by
  have hu : (-y)^n = 1 := by rw [neg_pow, hy, ← mul_pow]; norm_num
  have hconj (z : ℂ) (hz : z^n = 1) : z * starRingEnd ℂ z = 1 := by
    have hnz := congrArg norm hz
    rw [norm_pow, norm_one] at hnz
    have hz' := (pow_left_inj₀ (norm_nonneg z) zero_le_one hn.ne').mp (by simpa using hnz)
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz']
  let u : ℂ := -y
  have hsq : (x + u)^2 = (x*u) * (Complex.normSq (x+u) : ℂ) := by
    rw [← Complex.mul_conj, map_add]
    linear_combination -(x+u)*u*hconj x hx - (x+u)*x*hconj u hu
  have hp : ((x+u)^2)^n = ((Complex.normSq (x+u) : ℂ)^n) := by
    rw [hsq, mul_pow, mul_pow, hx, show u^n = 1 from hu, one_mul, one_mul]
  rw [sub_eq_add_neg, show -y = u by rfl, pow_mul _ (2*n) j, pow_mul _ 2 n, hp,
    ← pow_mul, ← Complex.ofReal_pow, Complex.ofReal_re]
  exact pow_nonneg (Complex.normSq_nonneg _) _

private lemma longChord {n : ℕ} (hn : 0 < n) (w : Fin n → ℂ) {f : ℂ[X]}
    (hf : ∀ z, f.eval z = ∏ i, (z - w i)) {D : ℝ} (hD : 0 ≤ D) (hD' : D < 2) :
    ∃ z z' : ℂ, ‖f.eval z‖ = 1 ∧ ‖f.eval z'‖ = 1 ∧ D < dist z z' := by
  classical
  by_contra! h
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one
    (by positivity : (0 : ℝ) < 1 / (n : ℝ)^2) (by linarith : D/2 < 1)
  let m := 2*n*(j+1)
  have hjm : j ≤ m := by dsimp [m]; nlinarith
  have hm : (n : ℝ)^2 * D^m < (2 : ℝ)^m := by
    have hsmall := (pow_le_pow_of_le_one (by positivity : 0 ≤ D/2)
      (by linarith : D/2 ≤ 1) hjm).trans_lt hj
    rw [div_pow, lt_div_iff₀ (by positivity : 0 < (n : ℝ)^2)] at hsmall
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < (2 : ℝ)^m), one_mul] at hsmall
    simpa [mul_comm] using hsmall
  let P := scaledFamily w 1
  let Q := scaledFamily w ((-1)^n)
  have hP := scaledFamily_monic_degrees hn w 1
  have hQ := scaledFamily_monic_degrees hn w ((-1)^n)
  obtain ⟨b, hb⟩ := pairSumPoly (n := n) P Q hP.1 hQ.1 m
  have en (v : ℂ) : ∃ x y : Fin n → ℂ,
      Finset.univ.val.map x = (P.map (evalRingHom v)).roots ∧
      Finset.univ.val.map y = (Q.map (evalRingHom v)).roots := by
    obtain ⟨x, hx⟩ := enumRoots (P.map (evalRingHom v)) ((hP.1.natDegree_map _).trans hP.2)
    obtain ⟨y, hy⟩ := enumRoots (Q.map (evalRingHom v)) ((hQ.1.natDegree_map _).trans hQ.2)
    exact ⟨x, y, hx, hy⟩
  have onCircle (v : ℂ) (hv : ‖v‖ = 1) : ‖b.eval v‖ ≤ (n : ℝ)^2 * D^m := by
    obtain ⟨x, y, hx, hy⟩ := en v
    have vne : v ≠ 0 := by intro hv0; simp [hv0] at hv
    have enval {a : ℂ} (ha : ‖a‖ = 1) {z : Fin n → ℂ}
        (hz : Finset.univ.val.map z = ((scaledFamily w a).map (evalRingHom v)).roots)
        (i : Fin n) : ‖f.eval (z i / v)‖ = 1 := by
      have hu : z i ∈ ((scaledFamily w a).map (evalRingHom v)).roots := by
        rw [← hz]
        exact Multiset.mem_map.2 ⟨i, by simp, rfl⟩
      simpa [hf, norm_mul, hv, ha] using congrArg norm (root_scaledFamily hn w vne hu)
    have hdist (i j : Fin n) : ‖x i - y j‖ ≤ D := by
      simpa [dist_eq_norm, ← sub_div, norm_div, hv] using
        h _ _ (enval (a := 1) (by simp) hx i) (enval (a := (-1)^n) (by simp) hy j)
    rw [hb v x y hx hy]
    calc
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, D^m := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdist i j) _
      _ = _ := by simp [pow_two, mul_assoc]
  have horigin : ‖b.eval 0‖ ≤ (n : ℝ)^2 * D^m := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le
      (Metric.isBounded_ball (x := (0 : ℂ)) (r := 1))
      (b.differentiable.diffContOnCl) (fun v hv => ?_) ?_
    · have hvs := Metric.frontier_ball_subset_sphere hv
      exact onCircle v (by simpa [mem_sphere, dist_zero_right] using hvs)
    · exact subset_closure (by simp : (0 : ℂ) ∈ ball 0 1)
  obtain ⟨x, y, hx, hy⟩ := en 0
  have hor {a : ℂ} {z : Fin n → ℂ}
      (hz : Finset.univ.val.map z = ((scaledFamily w a).map (evalRingHom 0)).roots) (u : ℂ) :
      u^n = a ↔ ∃ i, z i = u := by
    rw [scaledFamily_zero] at hz
    have hu : u ∈ (X^n - C a).roots ↔ u^n = a := by
      rw [mem_roots (X_pow_sub_C_ne_zero hn a)]
      simp [IsRoot.def, sub_eq_zero]
    rw [← hu, ← hz, Multiset.mem_map]
    simp
  obtain ⟨ix, hix⟩ := (hor hx 1).1 (by simp)
  obtain ⟨iy, hiy⟩ := (hor hy (-1)).1 rfl
  have hlow : (2 : ℝ)^m ≤ (b.eval 0).re := by
    rw [hb 0 x y hx hy]
    simp only [Complex.re_sum]
    have hnon i j : 0 ≤ ((x i - y j)^m).re :=
      normalized_nonnegative hn ((hor hx _).2 ⟨i, rfl⟩) ((hor hy _).2 ⟨j, rfl⟩)
    calc
      (2 : ℝ)^m = ((x ix - y iy)^m).re := by
        rw [hix, hiy]
        have htwo : 1 - (-1 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
        rw [htwo, ← Complex.ofReal_pow, Complex.ofReal_re]
      _ ≤ ∑ j, ((x ix - y j)^m).re :=
        single_le_sum (fun j _ => hnon ix j) (mem_univ iy)
      _ ≤ ∑ i, ∑ j, ((x i - y j)^m).re :=
        single_le_sum (fun i _ => sum_nonneg fun j _ => hnon i j) (mem_univ ix)
  exact (not_lt_of_ge (hlow.trans ((Complex.re_le_norm _).trans horigin))) hm
end OMA

theorem OMA.solution : type_of% @Erdos1046.erdos_1046.variants.diameter := by
  intro f hmonic _
  by_cases hdeg : f.natDegree = 0
  · have hf := eq_one_of_monic_natDegree_zero hmonic hdeg
    subst f
    have hz : (0 : ℂ) ∈ Erdos1046.closedLemniscate 1 := by
      simp [Erdos1046.closedLemniscate]
    have hz' : (2 : ℂ) ∈ Erdos1046.closedLemniscate 1 := by
      simp [Erdos1046.closedLemniscate]
    calc
      2 = edist (0 : ℂ) 2 := by
        rw [edist_dist, dist_zero_left]
        norm_num [show ‖(2 : ℂ)‖ = 2 by norm_num]
      _ ≤ _ := edist_le_ediam_of_mem hz hz'
  · by_contra! hdiam
    let D := (ediam (Erdos1046.closedLemniscate f)).toReal
    have hfinite : ediam (Erdos1046.closedLemniscate f) ≠ ⊤ :=
      ne_top_of_lt (hdiam.trans_le le_top)
    have hDlt : D < 2 := by
      simpa [D] using (ENNReal.toReal_lt_toReal hfinite (by norm_num : (2 : ENNReal) ≠ ⊤)).2 hdiam
    have hsplit := IsAlgClosed.splits f
    obtain ⟨w, hw⟩ := OMA.enumRoots f rfl
    have hf (z : ℂ) : f.eval z = ∏ i, (z - w i) := by
      rw [hsplit.eval_eq_prod_roots_of_monic hmonic, ← hw,
        Finset.prod_eq_multiset_prod, Multiset.map_map]
      rfl
    obtain ⟨z, z', hz, hz', hzz'⟩ :=
      OMA.longChord (Nat.pos_of_ne_zero hdeg) w hf ENNReal.toReal_nonneg hDlt
    have he : edist z z' ≤ ediam (Erdos1046.closedLemniscate f) :=
      edist_le_ediam_of_mem hz.le hz'.le
    exact hzz'.not_ge (by simpa [D, edist_dist] using ENNReal.toReal_mono hfinite he)
