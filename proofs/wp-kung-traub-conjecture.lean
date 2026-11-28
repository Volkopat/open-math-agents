import OMAStatements.S_wp_kung_traub_conjecture
import Mathlib
noncomputable section
open scoped BigOperators Polynomial
open Polynomial Finset
namespace KungTraubProof
private def wr {m : ℕ} (b : Fin m → ℂ[X]) : ℂ[X] :=
  (Matrix.of fun k i : Fin m => (derivative^[k.val]) (b i)).det

private theorem coeff_prod_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) (d : ι → ℕ)
    (h : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, (f j).natDegree ≤ d j := fun j hj => h j (mem_insert_of_mem hj)
    rw [prod_insert hi, sum_insert hi, prod_insert hi, coeff_mul_add_eq_of_natDegree_le,
      ih hs]
    · exact h i (mem_insert_self _ _)
    · exact (natDegree_prod_le s f).trans (sum_le_sum hs)

private theorem det_top {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ[X]) (d : Fin m → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ (∑ j, d j) ∧
      A.det.coeff (∑ j, d j) = (Matrix.of fun i j => (A i j).coeff (d j)).det := by
  classical
  constructor
  · rw [Matrix.det_apply']
    apply natDegree_sum_le_of_forall_le
    intro σ _
    refine natDegree_mul_le.trans ?_
    have h0 : (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ[X]).natDegree = 0 := by
      rw [← C_eq_intCast]
      exact natDegree_C _
    rw [h0, zero_add]
    exact (natDegree_prod_le _ _).trans (sum_le_sum fun j _ => h (σ j) j)
  · rw [Matrix.det_apply', Matrix.det_apply', finsetSum_coeff]
    apply sum_congr rfl
    intro σ _
    simp only [← C_eq_intCast, coeff_C_mul, Matrix.of_apply]
    rw [coeff_prod_sum _ _ _ (fun j _ => h (σ j) j)]

private theorem wr_degree_distinct {m : ℕ} (b : Fin m → ℂ[X])
    (hb : ∀ i, b i ≠ 0) (hd : Function.Injective (fun i => (b i).natDegree)) :
    wr b ≠ 0 ∧ (wr b).natDegree + (∑ k : Fin m, k.val) = ∑ i, (b i).natDegree := by
  let d := fun i => (b i).natDegree
  let A := Matrix.of fun k i : Fin m => X ^ k.val * (derivative^[k.val]) (b i)
  have hA (k i : Fin m) : (A k i).natDegree ≤ d i := by
    change ((X : ℂ[X]) ^ k.val * (derivative^[k.val]) (b i)).natDegree ≤ (b i).natDegree
    by_cases hki : k.val ≤ (b i).natDegree
    · exact (natDegree_mul_le).trans (by
        rw [natDegree_X_pow]
        have h' := natDegree_iterate_derivative (b i) k.val
        omega)
    · have hd0 : (derivative^[k.val]) (b i) = 0 := by
        ext v
        rw [coeff_iterate_derivative, coeff_eq_zero_of_natDegree_lt (by omega), smul_zero, coeff_zero]
      simp [hd0]
  have hcoeff (k i : Fin m) :
      (A k i).coeff (d i) = (b i).leadingCoeff * (((d i).descFactorial k.val : ℕ) : ℂ) := by
    change ((X : ℂ[X]) ^ k.val * (derivative^[k.val]) (b i)).coeff (b i).natDegree = _
    by_cases hki : k.val ≤ (b i).natDegree
    · conv_lhs => rw [show (b i).natDegree = ((b i).natDegree - k.val) + k.val by omega]
      rw [coeff_X_pow_mul, coeff_iterate_derivative, Nat.sub_add_cancel hki, coeff_natDegree]
      simp [d, nsmul_eq_mul, mul_comm]
    · rw [show d i = (b i).natDegree by rfl, Nat.descFactorial_eq_zero_iff_lt.mpr
        (Nat.lt_of_not_ge hki), Nat.cast_zero, mul_zero]
      simp [coeff_X_pow_mul', hki]
  have hV : (Matrix.of fun k i : Fin m => ((((d i).descFactorial k.val : ℕ) : ℂ))).det ≠ 0 := by
    rw [← Matrix.det_transpose]
    change (Matrix.of fun i j : Fin m => (((d i).descFactorial j.val : ℕ) : ℂ)).det ≠ 0
    simp_rw [← descPochhammer_eval_eq_descFactorial ℂ]
    rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun i => (d i : ℂ)) (fun j => descPochhammer ℂ j.val)
      (fun j => descPochhammer_natDegree ℂ j.val) (fun j => monic_descPochhammer ℂ j.val),
      Matrix.det_vandermonde_ne_zero_iff]
    exact Nat.cast_injective.comp hd
  obtain ⟨hAd, hc⟩ := det_top A d hA
  have hnz : A.det.coeff (∑ j, d j) ≠ 0 := by
    rw [hc]
    simp_rw [hcoeff]
    have ht := Matrix.det_mul_row (fun i => (b i).leadingCoeff)
      (Matrix.of fun k i : Fin m => (((d i).descFactorial k.val : ℕ) : ℂ))
    simp only [Matrix.of_apply] at ht
    rw [ht]
    exact mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => leadingCoeff_ne_zero.mpr (hb i)) hV
  have heq : A.det = (X : ℂ[X]) ^ (∑ k : Fin m, k.val) * wr b := by
    change (Matrix.of fun k i : Fin m => X ^ k.val * (derivative^[k.val]) (b i)).det = _
    calc
      _ = (∏ k : Fin m, (X : ℂ[X]) ^ k.val) * wr b := by
        simpa only [Matrix.of_apply, wr] using
          Matrix.det_mul_column (fun k : Fin m => (X : ℂ[X]) ^ k.val)
            (Matrix.of fun k i => (derivative^[k.val]) (b i))
      _ = _ := by rw [← prod_pow_eq_pow_sum]
  have hw : wr b ≠ 0 := by
    intro h
    simp [heq, h] at hnz
  refine ⟨hw, ?_⟩
  rw [← natDegree_eq_of_le_of_coeff_ne_zero hAd hnz, heq,
    natDegree_mul (pow_ne_zero _ X_ne_zero) hw, natDegree_X_pow, add_comm]

private theorem degree_bound {d : ℕ} {p : ℂ[X]} :
    p ∈ degreeLT ℂ (d + 1) ↔ p.natDegree ≤ d := by
  rw [degreeLT_succ_eq_degreeLE, mem_degreeLE, natDegree_le_iff_degree_le]

private theorem degree_mem_of_coeff_zero {d : ℕ} {p : ℂ[X]}
    (hp : p.natDegree ≤ d) (hc : p.coeff d = 0) : p ∈ degreeLT ℂ d := by
  rw [mem_degreeLT]
  by_cases h0 : p = 0
  · simp [h0]
  rw [← natDegree_lt_iff_degree_lt h0]
  by_contra! hn
  have he : p.natDegree = d := le_antisymm hp hn
  exact leadingCoeff_ne_zero.mpr h0 (by rwa [leadingCoeff, he])

private theorem degree_basis (d : ℕ) (V : Submodule ℂ ℂ[X]) (hV : V ≤ degreeLT ℂ d) :
    ∃ (m : ℕ) (b : Fin m → ℂ[X]), m = Module.finrank ℂ V ∧
      (∀ i, b i ≠ 0) ∧ StrictMono (fun i => (b i).natDegree) ∧
      Submodule.span ℂ (Set.range b) = V := by
  classical
  induction d generalizing V with
  | zero =>
    have hbot : V = ⊥ := by
      refine le_antisymm (fun p hp => ?_) bot_le
      rcases eq_or_ne p 0 with rfl | hn
      · exact Submodule.zero_mem _
      · exact False.elim (Nat.not_lt_zero _ ((natDegree_lt_iff_degree_lt hn).mpr
          (mem_degreeLT.mp (hV hp))))
    subst V
    refine ⟨0, Fin.elim0, by simp, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simp
  | succ d ih =>
    by_cases he : ∀ p ∈ V, (p : ℂ[X]).coeff d = 0
    · exact ih V fun p hp => degree_mem_of_coeff_zero (degree_bound.mp (hV hp)) (he p hp)
    · push Not at he
      obtain ⟨p, hpV, hp⟩ := he
      let W := V ⊓ degreeLT ℂ d
      let f : V →ₗ[ℂ] ℂ := (lcoeff ℂ d).comp V.subtype
      let pV : V := ⟨p, hpV⟩
      have hnz : f pV ≠ 0 := hp
      have hf : f.range = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro a
        exact ⟨(a / f pV) • pV, by
          rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hnz]⟩
      have hk : f.ker.map V.subtype = W := by
        ext q
        constructor
        · rintro ⟨r, hr, rfl⟩
          exact ⟨r.property, degree_mem_of_coeff_zero (degree_bound.mp (hV r.property)) hr⟩
        · intro hq
          refine ⟨⟨q, hq.1⟩, ?_, rfl⟩
          change q.coeff d = 0
          by_cases hq0 : q = 0
          · simp [hq0]
          exact coeff_eq_zero_of_natDegree_lt ((natDegree_lt_iff_degree_lt hq0).mpr
            (mem_degreeLT.mp hq.2))
      let : Module.Finite ℂ V := Module.Finite.of_injective
        (Submodule.inclusion hV) (Submodule.inclusion_injective hV)
      have hr := LinearMap.finrank_range_add_finrank_ker f
      rw [hf, finrank_top, Module.finrank_self, ← Submodule.finrank_map_subtype_eq V, hk] at hr
      obtain ⟨m, b, hdim, hbnz, hbinc, hspan⟩ := ih W inf_le_right
      have hbmem (i : Fin m) : b i ∈ W := by
        rw [← hspan]
        exact Submodule.subset_span (Set.mem_range_self i)
      have hpdeg : p.natDegree = d := natDegree_eq_of_le_of_coeff_ne_zero
        (degree_bound.mp (hV hpV)) hp
      have hp0 : p ≠ 0 := fun h => hp (by simp [h])
      let c : Fin (m + 1) → ℂ[X] := Fin.snoc b p
      have hcold (i : Fin m) : c i.castSucc = b i := by simp [c]
      have hclast : c (Fin.last m) = p := by simp [c]
      refine ⟨m + 1, c, by omega, Fin.lastCases (by simpa [hclast] using hp0) (fun i => by
        simpa [hcold] using hbnz i), ?_, ?_⟩
      · intro i j hij
        revert hij
        refine Fin.lastCases (fun hij => ?_) (fun j' hij => ?_) j
        · have hi : i.val < m := hij
          let i' : Fin m := ⟨i.val, hi⟩
          have hcast : i'.castSucc = i := Fin.ext rfl
          change (c i).natDegree < (c (Fin.last m)).natDegree
          rw [← hcast, hcold, hclast, hpdeg]
          exact (natDegree_lt_iff_degree_lt (hbnz i')).mpr (mem_degreeLT.mp (hbmem i').2)
        · have hi : i.val < m := Nat.lt_of_lt_of_le hij (Nat.le_of_lt j'.isLt)
          let i' : Fin m := ⟨i.val, hi⟩
          have hcast : i'.castSucc = i := Fin.ext rfl
          change (c i).natDegree < (c j'.castSucc).natDegree
          rw [← hcast, hcold, hcold]
          exact hbinc (show i' < j' from hij)
      · apply le_antisymm
        · rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact Fin.lastCases (by simpa [hclast] using hpV)
            (fun j => by simpa [hcold] using (hbmem j).1) i
        · intro q hq
          let T := Submodule.span ℂ (Set.range c)
          have hWT : W ≤ T := by
            rw [← hspan, Submodule.span_le]
            rintro _ ⟨i, rfl⟩
            exact Submodule.subset_span ⟨i.castSucc, hcold i⟩
          have hpT : p ∈ T := Submodule.subset_span ⟨Fin.last m, hclast⟩
          have hs (a : ℂ) : (a • p).coeff d = a * p.coeff d := by simp [coeff_smul]
          let a := q.coeff d / p.coeff d
          have hsub : q - a • p ∈ V := V.sub_mem hq (V.smul_mem _ hpV)
          have hm : q - a • p ∈ W := ⟨hsub, degree_mem_of_coeff_zero
            (degree_bound.mp (hV hsub)) (by
              rw [coeff_sub, hs, div_mul_cancel₀ _ hp, sub_self])⟩
          exact (sub_add_cancel q (a • p)) ▸ T.add_mem (hWT hm) (T.smul_mem a hpT)

private theorem wr_combination {m : ℕ} (b : Fin m → ℂ[X])
    (D : Matrix (Fin m) (Fin m) ℂ) :
    wr (fun i => ∑ j, D j i • b j) = wr b * C D.det := by
  classical
  change (Matrix.of (fun k i : Fin m =>
    (derivative^[k.val]) (∑ j, D j i • b j))).det = _
  have hm : (Matrix.of fun k i : Fin m =>
      (derivative^[k.val]) (∑ j, D j i • b j)) =
      (Matrix.of fun k j : Fin m => (derivative^[k.val]) (b j)) * D.map C := by
    apply Matrix.ext
    intro k i
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply,
      ← Module.End.pow_apply, map_sum, map_smul]
    simp only [smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [hm, Matrix.det_mul]
  change wr b * (C.mapMatrix D).det = _
  rw [← RingHom.map_det]

private theorem strictMono_fin_nat_le {m : ℕ} {f : Fin m → ℕ}
    (h : StrictMono f) (i : Fin m) : i.val ≤ f i := by
  suffices ∀ (k : ℕ) (hk : k < m), k ≤ f ⟨k, hk⟩ by
    exact this i.val i.isLt
  intro k
  induction k with
  | zero => exact fun _ => Nat.zero_le _
  | succ k ih =>
    intro hk
    have hk' : k < m := by omega
    have hlt : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := h (by exact Nat.lt_succ_self k)
    exact Nat.succ_le_of_lt ((ih hk').trans_lt hlt)

private theorem wr_spec {m d : ℕ} (b : Fin m → ℂ[X])
    (hb : LinearIndependent ℂ b) (hdeg : ∀ i, (b i).natDegree ≤ d) :
    wr b ≠ 0 ∧ (wr b).natDegree ≤ m * d ∧
      ((wr b).natDegree = 0 → Submodule.span ℂ (Set.range b) ≤ degreeLT ℂ m) := by
  classical
  let V := Submodule.span ℂ (Set.range b)
  have hV : V ≤ degreeLT ℂ (d + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact degree_bound.mpr (hdeg i)
  obtain ⟨l, c, hdim, hc, hdc, hspan⟩ := degree_basis (d + 1) V hV
  have heq : l = m := hdim.trans (by simpa [V] using finrank_span_eq_card hb)
  clear hdim
  subst l
  have hcV (i : Fin m) : c i ∈ V := by
    rw [← hspan]
    exact Submodule.subset_span (Set.mem_range_self i)
  choose e he using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hcV i)
  let D := Matrix.of fun j i => e i j
  have hwc : wr c = wr b * C D.det := by
    convert wr_combination b D using 2
    funext i
    exact (he i).symm
  obtain ⟨hwnz, hformula⟩ := wr_degree_distinct c hc hdc.injective
  have hb0 : wr b ≠ 0 := fun hn => hwnz (by simp [hwc, hn])
  have hdet : C D.det ≠ 0 := fun hn => hwnz (by simp [hwc, hn])
  have hwd : (wr c).natDegree = (wr b).natDegree := by
    rw [hwc, natDegree_mul hb0 hdet, natDegree_C, add_zero]
  have hdc' (i : Fin m) : (c i).natDegree ≤ d := degree_bound.mp (hV (hcV i))
  have hsum : (∑ i, (c i).natDegree) ≤ m * d := by
    calc
      _ ≤ ∑ _ : Fin m, d := sum_le_sum fun i _ => hdc' i
      _ = _ := by simp
  refine ⟨hb0, ?_, ?_⟩
  · omega
  · intro h0
    have h_eq (i : Fin m) : (c i).natDegree = i.val := by
      apply le_antisymm _ (strictMono_fin_nat_le hdc i)
      by_contra! hh
      have hlt := sum_lt_sum
        (s := (univ : Finset (Fin m))) (fun j _ => strictMono_fin_nat_le hdc j)
        ⟨i, mem_univ _, hh⟩
      omega
    change V ≤ _
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change c i ∈ degreeLT ℂ m
    rw [mem_degreeLT, ← natDegree_lt_iff_degree_lt (hc i), h_eq]
    exact i.isLt
end KungTraubProof

namespace KungTraubProof
open Filter
open scoped Topology

private abbrev CoeffSpace (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) :=
  EuclideanSpace 𝕜 (Fin (d + 1))

private def coeffEquiv (𝕜 : Type*) [RCLike 𝕜] (d : ℕ) :
    degreeLT 𝕜 (d + 1) ≃ₗ[𝕜] CoeffSpace 𝕜 d :=
  (degreeLTEquiv 𝕜 (d + 1)).trans (WithLp.linearEquiv 2 𝕜 _).symm

private def poly {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} :
    CoeffSpace 𝕜 d →ₗ[𝕜] Polynomial 𝕜 :=
  (degreeLT 𝕜 (d + 1)).subtype.comp (coeffEquiv 𝕜 d).symm.toLinearMap

private theorem poly_injective {𝕜 : Type*} [RCLike 𝕜] {d : ℕ} :
    Function.Injective (poly : CoeffSpace 𝕜 d → Polynomial 𝕜) :=
  Subtype.val_injective.comp (coeffEquiv 𝕜 d).symm.injective

private theorem poly_deg {d : ℕ} (v : CoeffSpace ℂ d) : (poly v).natDegree ≤ d :=
  degree_bound.mp ((coeffEquiv ℂ d).symm v).property

private theorem poly_coeff {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (v : CoeffSpace 𝕜 d) (i : Fin (d + 1)) : (poly v).coeff i = v i := by
  exact congrArg (fun u : CoeffSpace 𝕜 d => u i)
    ((coeffEquiv 𝕜 d).apply_symm_apply v)

private theorem poly_eval {𝕜 : Type*} [RCLike 𝕜] {d : ℕ}
    (v : CoeffSpace 𝕜 d) (z : 𝕜) : (poly v).eval z = ∑ i : Fin (d + 1), v i * z ^ i.val := by
  have h := eval_eq_sum_degreeLTEquiv ((coeffEquiv 𝕜 d).symm v).property z
  change (poly v).eval z = ∑ i : Fin (d + 1), (poly v).coeff i * z ^ i.val at h
  simpa only [poly_coeff] using h

private def CoeffLimit (p : ℕ → ℂ[X]) (q : ℂ[X]) : Prop :=
  ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k))

private theorem CoeffLimit.comp {p : ℕ → ℂ[X]} {q : ℂ[X]} (h : CoeffLimit p q)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) : CoeffLimit (p ∘ φ) q :=
  fun k => (h k).comp hφ.tendsto_atTop

private theorem CoeffLimit.poly {d : ℕ} {v : ℕ → CoeffSpace ℂ d} {u : CoeffSpace ℂ d}
    (h : Tendsto v atTop (𝓝 u)) : CoeffLimit (fun j => poly (v j)) (poly u) := by
  intro k
  by_cases hk : k < d + 1
  · let i : Fin (d + 1) := ⟨k, hk⟩
    change Tendsto (fun j => (KungTraubProof.poly (v j)).coeff i) atTop
      (𝓝 ((KungTraubProof.poly u).coeff i))
    simpa only [poly_coeff, Function.comp_def] using
      ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℂ) i).tendsto u).comp h
  · simp only [coeff_eq_zero_of_natDegree_lt ((poly_deg _).trans_lt (by omega : d < k))]
    exact tendsto_const_nhds

private theorem CoeffLimit.eval {d : ℕ} {p : ℕ → ℂ[X]} {q : ℂ[X]}
    (h : CoeffLimit p q) (hp : ∀ j, (p j).natDegree ≤ d) (hq : q.natDegree ≤ d)
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a)) :
    Tendsto (fun j => (p j).eval (z j)) atTop (𝓝 (q.eval a)) := by
  simp only [eval_eq_sum_range' (by omega : q.natDegree < d + 1),
    eval_eq_sum_range' (Nat.lt_succ_of_le (hp _))]
  exact tendsto_finsetSum _ fun k _ => (h k).mul (hz.pow k)

private theorem CoeffLimit.mul {p q : ℕ → ℂ[X]} {a b : ℂ[X]}
    (hp : CoeffLimit p a) (hq : CoeffLimit q b) :
    CoeffLimit (fun j => p j * q j) (a * b) := by
  intro k
  simp only [coeff_mul]
  exact tendsto_finsetSum _ fun i _ => (hp i.1).mul (hq i.2)

private theorem CoeffLimit.prod {ι : Type*} (s : Finset ι) {p : ι → ℕ → ℂ[X]}
    {q : ι → ℂ[X]} (h : ∀ i ∈ s, CoeffLimit (p i) (q i)) :
    CoeffLimit (fun j => ∏ i ∈ s, p i j) (∏ i ∈ s, q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty]; exact fun _ => tendsto_const_nhds
  | @insert i s hi ih =>
    simp only [prod_insert hi]
    exact (h i (mem_insert_self _ _)).mul (ih fun k hk => h k (mem_insert_of_mem hk))

private theorem CoeffLimit.wr {m : ℕ} {b : ℕ → Fin m → ℂ[X]} {c : Fin m → ℂ[X]}
    (h : ∀ i, CoeffLimit (fun j => b j i) (c i)) :
    CoeffLimit (fun j => wr (b j)) (wr c) := by
  intro k
  simp only [KungTraubProof.wr, Matrix.det_apply', Matrix.of_apply, finsetSum_coeff, ← C_eq_intCast,
    coeff_C_mul]
  refine tendsto_finsetSum _ fun σ _ => Tendsto.const_mul _ ?_
  refine CoeffLimit.prod univ (fun i _ => ?_) k
  intro l
  simp only [coeff_iterate_derivative, nsmul_eq_mul]
  exact Tendsto.const_mul _ (h i _)

private theorem CoeffLimit.divLinear {d : ℕ} {p : ℕ → ℂ[X]} {q : ℂ[X]}
    (h : CoeffLimit p q) (hp : ∀ j, (p j).natDegree ≤ d) (hq : q.natDegree ≤ d)
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a)) :
    CoeffLimit (fun j => p j /ₘ (X - C (z j))) (q /ₘ (X - C a)) := by
  have formula (r : ℂ[X]) (hr : r.natDegree ≤ d) (b : ℂ) (k : ℕ) :
      (r /ₘ (X - C b)).coeff k = ∑ i ∈ Icc (k + 1) d, b ^ (i - (k + 1)) * r.coeff i := by
    rw [coeff_divByMonic_X_sub_C]
    apply sum_subset
    · intro i hi
      exact mem_Icc.mpr ⟨(mem_Icc.mp hi).1, (mem_Icc.mp hi).2.trans hr⟩
    · intro i hi hn
      rw [coeff_eq_zero_of_natDegree_lt (by
        have hi' := (mem_Icc.mp hi).1
        by_contra! hle
        exact hn (mem_Icc.mpr ⟨hi', hle⟩)), mul_zero]
  intro k
  simp only [formula q hq, formula (p _) (hp _)]
  exact tendsto_finsetSum _ fun i _ => (hz.pow _).mul (h i)

private theorem limit_degree_of_small_roots {d m : ℕ} {p : ℕ → ℂ[X]} {q : ℂ[X]}
    (h : CoeffLimit p q) (hp : ∀ j, (p j).natDegree ≤ d) (hq : q.natDegree ≤ d)
    (hq0 : q ≠ 0) (hr : ∀ j, m ≤ ((p j).roots.filter fun z => ‖z‖ ≤ 1).card) :
    m ≤ q.natDegree := by
  induction m generalizing p q with
  | zero => exact Nat.zero_le _
  | succ m ih =>
    have hex (j : ℕ) : ∃ z, z ∈ (p j).roots.filter (fun z => ‖z‖ ≤ 1) :=
      Multiset.card_pos_iff_exists_mem.mp (by have := hr j; omega)
    choose z hz using hex
    have hzB (j : ℕ) : z j ∈ Metric.closedBall (0 : ℂ) 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using (Multiset.mem_filter.mp (hz j)).2
    obtain ⟨a, _, φ, hφ, ha⟩ := (isCompact_closedBall 0 1).tendsto_subseq hzB
    have hp0 (j : ℕ) : p j ≠ 0 := by
      intro e
      simpa [e] using (Multiset.mem_filter.mp (hz j)).1
    have hroot (j : ℕ) : (p j).IsRoot (z j) :=
      (mem_roots (hp0 j)).mp (Multiset.mem_filter.mp (hz j)).1
    have hqa : q.IsRoot a := by
      have e (j : ℕ) : (p (φ j)).eval (z (φ j)) = 0 := hroot (φ j)
      apply tendsto_nhds_unique ((h.comp hφ).eval (fun j => hp (φ j)) hq ha)
      simpa only [Function.comp_apply, e] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
    let p' (j : ℕ) := p (φ j) /ₘ (X - C (z (φ j)))
    let q' := q /ₘ (X - C a)
    have ep (j : ℕ) : (X - C (z (φ j))) * p' j = p (φ j) :=
      mul_divByMonic_eq_iff_isRoot.mpr (hroot (φ j))
    have eq : (X - C a) * q' = q := mul_divByMonic_eq_iff_isRoot.mpr hqa
    have hp'0 (j : ℕ) : p' j ≠ 0 := by
      intro e
      exact hp0 (φ j) (by simpa [e] using (ep j).symm)
    have hq'0 : q' ≠ 0 := fun e => hq0 (by simpa [e] using eq.symm)
    have hdp (j : ℕ) : 1 + (p' j).natDegree = (p (φ j)).natDegree := by
      rw [← ep j, natDegree_mul (X_sub_C_ne_zero _) (hp'0 j), natDegree_X_sub_C]
    have hdq : 1 + q'.natDegree = q.natDegree := by
      rw [← eq, natDegree_mul (X_sub_C_ne_zero _) hq'0, natDegree_X_sub_C]
    have h' : CoeffLimit p' q' := (h.comp hφ).divLinear (fun j => hp (φ j)) hq ha
    have hh := ih h' (fun j => by have := hp (φ j); have := hdp j; omega) (by omega) hq'0
    suffices m ≤ q'.natDegree by omega
    apply hh
    intro j
    have hb := hr (φ j)
    have hs : ‖z (φ j)‖ ≤ 1 := (Multiset.mem_filter.mp (hz (φ j))).2
    rw [← ep j, roots_mul (by rw [ep j]; exact hp0 _), roots_X_sub_C,
      Multiset.filter_add, Multiset.filter_singleton, if_pos hs, Multiset.card_add,
      Multiset.card_singleton] at hb
    omega

end KungTraubProof

namespace KungTraubProof
open Filter
open scoped Topology

private theorem coeff_dilate (p : ℂ[X]) (s : ℂ) (k : ℕ) :
    (p.comp (C s * X)).coeff k = p.coeff k * s ^ k := by
  classical
  rw [comp_eq_sum_left, Polynomial.sum, finsetSum_coeff]
  simp_rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul, C_mul_X_pow_eq_monomial,
    coeff_monomial]
  by_cases hk : k ∈ p.support
  · rw [sum_eq_single_of_mem k hk]
    · simp
    · intro i _ hi
      simp [hi]
  · rw [notMem_support_iff.mp hk, zero_mul]
    apply sum_eq_zero
    intro i hi
    have he : i ≠ k := fun e => hk (e ▸ hi)
    simp [he]

private theorem mahler_eq_eval_zero {p : ℂ[X]}
    (hr : ∀ z ∈ p.roots, 1 ≤ ‖z‖) : p.mahlerMeasure = ‖p.eval 0‖ := by
  have he : p.eval 0 = p.leadingCoeff * (p.roots.map fun z => -z).prod := by
    have hf := congrArg (eval (0 : ℂ)) (IsAlgClosed.splits p).eq_prod_roots
    simpa only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_sub, eval_X, zero_sub] using hf
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, he, norm_mul]
  congr 1
  change _ = ((normHom : ℂ →*₀ ℝ).toMonoidHom) (Multiset.prod _)
  rw [← Multiset.prod_hom, Multiset.map_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro z hz
  simp [max_eq_right (hr z hz)]

private theorem coeff_le_of_roots_far {d k : ℕ} {p : ℂ[X]} (hd : p.natDegree ≤ d)
    {s : ℝ} (hs : 1 ≤ s) (hk : 0 < k)
    (hr : ∀ z, p.IsRoot z → s ≤ ‖z‖) :
    ‖p.coeff k‖ ≤ (d.choose k : ℝ) * ‖p.coeff 0‖ / s := by
  let P := p.comp (C (s : ℂ) * X)
  have hs0 : 0 < s := by linarith
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hP0 : P ≠ 0 := by
    intro h
    have h' : p.IsRoot 0 := by
      have := congrArg (eval (0 : ℂ)) h
      simpa [P, eval_comp, IsRoot] using this
    exact hs0.not_ge (by simpa using hr 0 h')
  have hP (z : ℂ) (hz : z ∈ P.roots) : 1 ≤ ‖z‖ := by
    have hroot : p.IsRoot ((s : ℂ) * z) := by
      simpa [P, IsRoot, eval_comp] using (mem_roots hP0).mp hz
    have hz' := hr _ hroot
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le] at hz'
    exact (le_mul_iff_one_le_right hs0).mp hz'
  have he : P.eval 0 = p.coeff 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [P, eval_comp]
  have hd' : P.natDegree ≤ d := by
    simpa [P, natDegree_comp, natDegree_C_mul_X _ hsC] using hd
  have h := norm_coeff_le_choose_mul_mahlerMeasure k P
  rw [mahler_eq_eval_zero hP, he] at h
  change ‖(p.comp (C (s : ℂ) * X)).coeff k‖ ≤ _ at h
  rw [coeff_dilate, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hs0.le] at h
  apply (le_div_iff₀ hs0).mpr
  calc
    ‖p.coeff k‖ * s ≤ ‖p.coeff k‖ * s ^ k := by
      gcongr
      simpa using pow_le_pow_right₀ hs (show 1 ≤ k by omega)
    _ ≤ _ := h
    _ ≤ _ := by gcongr

private theorem limit_constant_of_roots_far {d : ℕ} {p : ℕ → ℂ[X]} {q : ℂ[X]}
    (h : CoeffLimit p q) (hd : ∀ j, (p j).natDegree ≤ d)
    (hr : ∀ j z, (p j).IsRoot z → (j : ℝ) + 1 ≤ ‖z‖) :
    q.natDegree = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  obtain ⟨A, hA⟩ := (h 0).norm.bddAbove_range
  have hb (j : ℕ) : ‖(p j).coeff 0‖ ≤ A := hA (Set.mem_range_self j)
  have hlim : Tendsto (fun j : ℕ => (d.choose k : ℝ) * A / ((j : ℝ) + 1)) atTop (𝓝 0) := by
    have h' := (tendsto_const_div_atTop_nhds_zero_nat ((d.choose k : ℝ) * A)).comp
      ((show StrictMono Nat.succ from fun _ _ h => Nat.succ_lt_succ h).tendsto_atTop)
    change Tendsto (fun j : ℕ => (d.choose k : ℝ) * A / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) at h'
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  have hq := le_of_tendsto_of_tendsto (h k).norm hlim
    (Eventually.of_forall fun j => (coeff_le_of_roots_far (hd j) (by linarith [Nat.cast_nonneg (α := ℝ) j] : 1 ≤ (j : ℝ) + 1) hk (hr j)).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb j) (by positivity)) (by positivity)))
  exact norm_eq_zero.mp (le_antisymm hq (norm_nonneg _))

end KungTraubProof

namespace KungTraubProof
open Filter InnerProductSpace
open scoped Topology

private theorem wr_root_of_span_le {l m : ℕ} {b : Fin l → ℂ[X]} {c : Fin m → ℂ[X]}
    (h : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range c))
    (e : l = m) {z : ℂ} (hz : (wr c).IsRoot z) : (wr b).IsRoot z := by
  subst l
  classical
  choose a ha using fun i => (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    (h (Submodule.subset_span (Set.mem_range_self i)))
  have hb : b = fun i => ∑ j, a i j • c j := funext fun i => (ha i).symm
  rw [hb]
  have he := wr_combination c (Matrix.of fun j i => a i j)
  simp only [Matrix.of_apply] at he
  rw [he]
  simp [IsRoot, show (wr c).eval z = 0 from hz]

private theorem orthonormal_poly_frame {d m : ℕ} {b : Fin m → ℂ[X]}
    (hb : LinearIndependent ℂ b) (hd : ∀ i, (b i).natDegree ≤ d) :
    ∃ c : Fin m → CoeffSpace ℂ d, Orthonormal ℂ c ∧
      Submodule.span ℂ (Set.range (poly ∘ c)) = Submodule.span ℂ (Set.range b) := by
  let v (i : Fin m) := coeffEquiv ℂ d ⟨b i, degree_bound.mpr (hd i)⟩
  have hv (i : Fin m) : poly (v i) = b i := by simp [poly, v]
  have hvb : poly ∘ v = b := funext hv
  have h' : LinearIndependent ℂ (poly ∘ v) := hvb.symm ▸ hb
  have hli : LinearIndependent ℂ v := LinearIndependent.of_comp poly h'
  refine ⟨gramSchmidtNormed ℂ v, gramSchmidtNormed_orthonormal hli, ?_⟩
  rw [Set.range_comp, ← LinearMap.map_span, span_gramSchmidtNormed_range, span_gramSchmidt,
    LinearMap.map_span, ← Set.range_comp, hvb]

private theorem frame_expansion {d m : ℕ} {b : Fin m → CoeffSpace ℂ d}
    (hb : Orthonormal ℂ b) {v : CoeffSpace ℂ d}
    (hv : v ∈ Submodule.span ℂ (Set.range b)) :
    (∑ i, inner ℂ (b i) v • b i) = v := by
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  conv_lhs => enter [2, i, 1, 3]; rw [← hl]
  simpa only [hb.inner_right_fintype] using hl

private theorem wronskian_unit_frame (d m : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (b : Fin m → CoeffSpace ℂ d) (v : CoeffSpace ℂ d),
      Orthonormal ℂ b → ‖v‖ = 1 → v ∈ Submodule.span ℂ (Set.range b) →
      m ≤ ((poly v).roots.filter fun z => ‖z‖ ≤ 1).card →
      ∃ z, (wr (poly ∘ b)).IsRoot z ∧ ‖z‖ ≤ A := by
  classical
  by_contra! hn
  have hex (j : ℕ) := hn ((j : ℝ) + 1) (by positivity)
  choose b v hb hv hspan hsmall hfar using hex
  let S : Set (Fin m → CoeffSpace ℂ d) := {b | ∀ i, b i ∈ Metric.closedBall 0 1}
  have hS : IsCompact S := isCompact_pi_infinite fun _ => isCompact_closedBall _ _
  have hin (j : ℕ) : (b j, v j) ∈ S ×ˢ Metric.closedBall 0 1 := by
    constructor
    · intro i
      simp [Metric.mem_closedBall, (hb j).norm_eq_one i]
    · simp [Metric.mem_closedBall, hv j]
  obtain ⟨⟨c, u⟩, _, φ, hφ, ht⟩ :=
    (hS.prod (isCompact_closedBall 0 1)).tendsto_subseq hin
  change Tendsto (fun j => (b (φ j), v (φ j))) atTop (𝓝 (c, u)) at ht
  have hbt : Tendsto (fun j => b (φ j)) atTop (𝓝 c) :=
    (continuous_fst.tendsto (c, u)).comp ht
  have hb' (i : Fin m) : Tendsto (fun j => b (φ j) i) atTop (𝓝 (c i)) :=
    (continuous_apply i).tendsto c |>.comp hbt
  have hv' : Tendsto (fun j => v (φ j)) atTop (𝓝 u) :=
    (continuous_snd.tendsto (c, u)).comp ht
  have hc : Orthonormal ℂ c := by
    rw [orthonormal_iff_ite]
    intro i k
    apply tendsto_nhds_unique ((hb' i).inner (hb' k))
    have he (j : ℕ) := orthonormal_iff_ite.mp (hb (φ j)) i k
    simpa only [he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => if i = k then (1 : ℂ) else 0)
        atTop (𝓝 (if i = k then 1 else 0)))
  have hu : ‖u‖ = 1 := by
    apply tendsto_nhds_unique hv'.norm
    simpa only [Function.comp_apply, hv] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hcu : (∑ i, inner ℂ (c i) u • c i) = u := by
    apply tendsto_nhds_unique
      (tendsto_finsetSum univ fun i _ => ((hb' i).inner hv').smul (hb' i))
    simpa only [Function.comp_apply, frame_expansion (hb _) (hspan _)] using hv'
  have hcLI : LinearIndependent ℂ (poly ∘ c) :=
    hc.linearIndependent.map' poly (LinearMap.ker_eq_bot.mpr poly_injective)
  obtain ⟨_, _, hwr⟩ := wr_spec (poly ∘ c) hcLI (fun i => poly_deg (c i))
  have hlim : CoeffLimit (fun j => wr (poly ∘ b (φ j))) (wr (poly ∘ c)) :=
    CoeffLimit.wr fun i => CoeffLimit.poly (hb' i)
  have hW0 : (wr (poly ∘ c)).natDegree = 0 := by
    apply limit_constant_of_roots_far hlim
      (fun j => (wr_spec (poly ∘ b (φ j)) ((hb (φ j)).linearIndependent.map' poly
        (LinearMap.ker_eq_bot.mpr poly_injective)) (fun i => poly_deg (b (φ j) i))).2.1)
    intro j z hz
    have hle : (j : ℝ) ≤ (φ j : ℝ) := by exact_mod_cast hφ.id_le j
    exact (add_le_add_left hle 1).trans (le_of_lt (hfar (φ j) z hz))
  have hpu0 : poly u ≠ 0 := by
    intro e
    have e' : u = 0 := poly_injective (e.trans (map_zero poly).symm)
    simp [e'] at hu
  have hpu : poly u ∈ Submodule.span ℂ (Set.range (poly ∘ c)) := by
    rw [← hcu, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have hlt : (poly u).natDegree < m :=
    (natDegree_lt_iff_degree_lt hpu0).mpr (mem_degreeLT.mp (hwr hW0 hpu))
  exact hlt.not_ge (limit_degree_of_small_roots (CoeffLimit.poly hv')
    (fun j => poly_deg (v (φ j))) (poly_deg u) hpu0 (fun j => hsmall (φ j)))

private theorem wronskian_unit (d m : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (b : Fin m → ℂ[X]) (p : ℂ[X]),
      LinearIndependent ℂ b → (∀ i, (b i).natDegree ≤ d) →
      p ∈ Submodule.span ℂ (Set.range b) → p ≠ 0 →
      m ≤ (p.roots.filter fun z => ‖z‖ ≤ 1).card →
      ∃ z, (wr b).IsRoot z ∧ ‖z‖ ≤ A := by
  obtain ⟨A, hA, H⟩ := wronskian_unit_frame d m
  refine ⟨A, hA, ?_⟩
  intro b p hb hd hp hp0 hr
  obtain ⟨c, hc, hcb⟩ := orthonormal_poly_frame hb hd
  rw [← hcb, Set.range_comp, ← LinearMap.map_span] at hp
  obtain ⟨v, hv, rfl⟩ := hp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr fun e => hp0 (by simp [e])
  let s : ℂ := (‖v‖⁻¹ : ℝ)
  have hs : s ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hn.ne')
  have hv' : ‖s • v‖ = 1 := by simp [s, norm_smul, hn.ne']
  obtain ⟨z, hz, hzA⟩ := H c (s • v) hc hv' (Submodule.smul_mem _ _ hv)
    (by rwa [map_smul, roots_smul_nonzero _ hs])
  exact ⟨z, wr_root_of_span_le hcb.ge rfl hz, hzA⟩

private theorem iterate_derivative_affine (p : ℂ[X]) (a s : ℂ) (k : ℕ) :
    derivative^[k] (p.comp (C s * X + C a)) =
      C (s ^ k) * (derivative^[k] p).comp (C s * X + C a) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_comp]
    have ha : derivative (C s * X + C a : ℂ[X]) = C s := by simp
    rw [ha, ← smul_eq_C_mul, ← Module.End.pow_apply, map_smul,
      Module.End.pow_apply, smul_eq_C_mul, ih, pow_succ', map_mul, mul_assoc]

private theorem wr_affine_eval {m : ℕ} (b : Fin m → ℂ[X]) (a s z : ℂ) :
    (wr (fun i => (b i).comp (C s * X + C a))).eval z =
      (∏ i : Fin m, s ^ i.val) * (wr b).eval (s * z + a) := by
  let L := Matrix.of fun k i : Fin m => derivative^[k.val] ((b i).comp (C s * X + C a))
  let N := Matrix.of fun k i : Fin m => derivative^[k.val] (b i)
  change evalRingHom z L.det = _ * evalRingHom (s * z + a) N.det
  rw [RingHom.map_det, RingHom.map_det]
  have e : (evalRingHom z).mapMatrix L =
      Matrix.of (fun k i => s ^ k.val * ((evalRingHom (s * z + a)).mapMatrix N) k i) := by
    ext k i
    change (derivative^[k.val] ((b i).comp (C s * X + C a))).eval z =
      s ^ k.val * (derivative^[k.val] (b i)).eval (s * z + a)
    simp [iterate_derivative_affine, eval_comp]
  rw [e]
  exact Matrix.det_mul_column _ _

theorem wronskian_localization (d m : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (b : Fin m → ℂ[X]) (p : ℂ[X]) (a : ℂ) (r : ℝ),
      LinearIndependent ℂ b → (∀ i, (b i).natDegree ≤ d) →
      p ∈ Submodule.span ℂ (Set.range b) → p ≠ 0 → 0 ≤ r →
      m ≤ (p.roots.filter fun z => ‖z - a‖ ≤ r).card →
      ∃ z, (wr b).IsRoot z ∧ ‖z - a‖ ≤ A * r := by
  obtain ⟨A, hA, H⟩ := wronskian_unit d m
  refine ⟨A, hA, ?_⟩
  intro b p a r hb hd hp hp0 hr hrs
  have main (r : ℝ) (hr : 0 < r) (hrs : m ≤ (p.roots.filter fun z => ‖z - a‖ ≤ r).card) :
      ∃ z, (wr b).IsRoot z ∧ ‖z - a‖ ≤ A * r := by
    let s : ℂ := r
    have hs : s ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    let G : ℂ[X] →ₗ[ℂ] ℂ[X] :=
      { toFun := fun q => q.comp (C s * X + C a)
        map_add' := fun q q' => map_add (compRingHom _) q q'
        map_smul' := fun c q => by simp [smul_eq_C_mul, mul_comp] }
    have hG : Function.Injective G := by
      intro q q' e
      apply Polynomial.funext
      intro z
      have hz : s * ((z - a) / s) + a = z := by field_simp; ring
      have ee := congrArg (eval ((z - a) / s)) e
      change (q.comp (C s * X + C a)).eval _ = (q'.comp (C s * X + C a)).eval _ at ee
      simpa [eval_comp, hz] using ee
    have hdeg (i : Fin m) : (G (b i)).natDegree ≤ d := by
      change ((b i).comp (C s * X + C a)).natDegree ≤ d
      simpa only [natDegree_comp, natDegree_linear hs, mul_one] using hd i
    have hmem : G p ∈ Submodule.span ℂ (Set.range (G ∘ b)) := by
      rw [Set.range_comp, ← LinearMap.map_span]
      exact ⟨p, hp, rfl⟩
    have hroots : m ≤ ((G p).roots.filter fun z => ‖z‖ ≤ 1).card := by
      change m ≤ ((p.comp (C s * X + C a)).roots.filter fun z => ‖z‖ ≤ 1).card
      rw [roots_comp_C_mul_X_add_C p s a (isUnit_iff_ne_zero.mpr hs),
        Multiset.filter_map, Multiset.card_map]
      convert hrs using 3
      rename_i z
      simp only [Function.comp_apply, Ring.inverse_eq_inv, norm_mul, norm_inv, s,
        Complex.norm_real, Real.norm_of_nonneg hr.le]
      rw [← div_eq_inv_mul, div_le_iff₀ hr, one_mul]
    obtain ⟨z, hz, hzd⟩ := H (G ∘ b) (G p) (hb.map' G (LinearMap.ker_eq_bot.mpr hG))
      hdeg hmem (fun e => hp0 (hG (e.trans (map_zero G).symm))) hroots
    refine ⟨s * z + a, ?_, ?_⟩
    · change (wr (fun i => (b i).comp (C s * X + C a))).eval z = 0 at hz
      rw [wr_affine_eval] at hz
      exact (mul_eq_zero.mp hz).resolve_left (prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hs)
    · simpa [norm_mul, s, Complex.norm_real, Real.norm_of_nonneg hr.le, mul_comm r] using
        mul_le_mul_of_nonneg_left hzd hr.le
  rcases hr.eq_or_lt with rfl | hr'
  · by_cases h : (wr b).IsRoot a
    · exact ⟨a, h, by simp⟩
    · have hopen : IsOpen {z : ℂ | (wr b).eval z ≠ 0} :=
        isOpen_ne_fun (wr b).continuous continuous_const
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen a h
      let ρ := δ / (2 * A)
      have hρ : 0 < ρ := by positivity
      obtain ⟨z, hz, hzδ⟩ := main ρ hρ (hrs.trans (Multiset.card_le_card
        (Multiset.monotone_filter_right p.roots
          (fun _ (hy : ‖_ - a‖ ≤ 0) => hy.trans hρ.le))))
      have hlt : A * ρ < δ := by
        dsimp [ρ]
        rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
        nlinarith
      exact False.elim ((hsub (by simpa [Metric.mem_ball, dist_eq_norm] using hzδ.trans_lt hlt)) hz)
  · exact main r hr' hrs

end KungTraubProof

namespace KungTraubProof
open scoped ENNReal

private theorem coeff_norm_le_sum {n : ℕ} (v : CoeffSpace ℂ n) :
    ‖v‖ ≤ ∑ i : Fin (n + 1), ‖v i‖ := by
  classical
  have h : (∑ i, EuclideanSpace.single i (v i)) = v := by
    ext i
    simp
  calc
    ‖v‖ = ‖∑ i, EuclideanSpace.single i (v i)‖ := by rw [h]
    _ ≤ ∑ i, ‖EuclideanSpace.single i (v i)‖ := norm_sum_le _ _
    _ = _ := by simp

private theorem one_le_mahler_of_unit {n : ℕ} (v : CoeffSpace ℂ n) (hv : ‖v‖ = 1) :
    1 ≤ (2 : ℝ) ^ (poly v).natDegree * (poly v).mahlerMeasure := by
  let p := poly v
  have h := coeff_norm_le_sum v
  rw [hv] at h
  simp_rw [← poly_coeff v] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => ‖p.coeff i‖)] at h
  refine h.trans ?_
  calc
    (∑ i ∈ range (n + 1), ‖p.coeff i‖) =
        ∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖ := by
      symm
      apply sum_subset (range_mono (Nat.succ_le_succ (poly_deg v)))
      intro i _ hi
      rw [coeff_eq_zero_of_natDegree_lt (by simpa [mem_range] using hi), norm_zero]
    _ ≤ ∑ i ∈ range (p.natDegree + 1), (p.natDegree.choose i : ℝ) * p.mahlerMeasure :=
      sum_le_sum fun i _ => norm_coeff_le_choose_mul_mahlerMeasure i p
    _ = _ := by rw [← sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose p.natDegree

private theorem root_factor_bound {a z : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) * min 1 ‖a - z‖ * max 1 ‖z‖ ≤ ‖a - z‖ := by
  rcases le_total ‖z‖ 1 with hz | hz
  · rw [max_eq_left hz, mul_one]
    have := min_le_right (1 : ℝ) ‖a - z‖
    linarith [norm_nonneg (a - z)]
  · rw [max_eq_right hz]
    have ht := norm_sub_le z a
    have hh : ‖z‖ ≤ ‖a - z‖ + ‖a‖ := by
      simpa only [sub_add_cancel, norm_sub_rev z a] using norm_add_le (z - a) a
    calc
      (1 / 2 : ℝ) * min 1 ‖a - z‖ * ‖z‖ ≤ (1 / 2 : ℝ) * 1 * ‖z‖ := by
        gcongr; exact min_le_left _ _
      _ ≤ ‖a - z‖ := by linarith

private theorem prod_root_factor_bound (s : Multiset ℂ) {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (1 / 2 : ℝ) ^ s.card * (s.map fun z => min 1 ‖a - z‖).prod *
      (s.map fun z => max 1 ‖z‖).prod ≤ (s.map fun z => ‖a - z‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    simp only [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons]
    calc
      _ = ((1 / 2 : ℝ) * min 1 ‖a - z‖ * max 1 ‖z‖) *
          ((1 / 2 : ℝ) ^ s.card * (s.map fun z => min 1 ‖a - z‖).prod *
            (s.map fun z => max 1 ‖z‖).prod) := by ring
      _ ≤ _ := mul_le_mul (root_factor_bound ha) ih
        (mul_nonneg (mul_nonneg (by positivity) (Multiset.prod_nonneg fun y hy => by
          obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hy
          exact le_min zero_le_one (norm_nonneg (a - z))))
          (Multiset.prod_nonneg fun y hy => by
            obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hy
            exact le_trans zero_le_one (le_max_left 1 ‖z‖))) (norm_nonneg (a - z))

theorem product_estimate {n : ℕ} (v : CoeffSpace ℂ n) (hv : ‖v‖ = 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (4 : ℝ)⁻¹ ^ (poly v).natDegree *
      ((poly v).roots.map fun z => min 1 ‖a - z‖).prod ≤ ‖(poly v).eval a‖ := by
  let p := poly v
  have h : (1 / 2 : ℝ) ^ p.natDegree ≤ p.mahlerMeasure := by
    have hM := one_le_mahler_of_unit v hv
    change 1 ≤ (2 : ℝ) ^ p.natDegree * p.mahlerMeasure at hM
    rw [div_pow, one_pow, div_le_iff₀ (by positivity)]
    simpa only [mul_comm] using hM
  have hev : ‖p.eval a‖ = ‖p.leadingCoeff‖ * (p.roots.map fun z => ‖a - z‖).prod := by
    have h' := congrArg (eval a) (IsAlgClosed.splits p).eq_prod_roots
    simp only [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_sub, eval_X] at h'
    rw [h', norm_mul]
    congr 1
    change ((normHom : ℂ →*₀ ℝ).toMonoidHom) ((p.roots.map fun z => a - z).prod) = _
    rw [← Multiset.prod_hom, Multiset.map_map]
    rfl
  have hb := prod_root_factor_bound p.roots ha
  rw [← (IsAlgClosed.splits p).natDegree_eq_card_roots] at hb
  let D := (p.roots.map fun z => min 1 ‖a - z‖).prod
  change (4 : ℝ)⁻¹ ^ p.natDegree * D ≤ ‖p.eval a‖
  have hD : 0 ≤ D := Multiset.prod_nonneg fun z hz => by
    obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hz
    exact le_min zero_le_one (norm_nonneg _)
  calc
    _ = (1 / 2 : ℝ) ^ p.natDegree * D * (1 / 2 : ℝ) ^ p.natDegree := by
      rw [mul_right_comm, ← mul_pow]
      norm_num
    _ ≤ (1 / 2 : ℝ) ^ p.natDegree * D * p.mahlerMeasure := by gcongr
    _ = ‖p.leadingCoeff‖ * ((1 / 2 : ℝ) ^ p.natDegree * D *
        (p.roots.map fun z => max 1 ‖z‖).prod) := by
      rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
      ring
    _ ≤ ‖p.eval a‖ := by rw [hev]; gcongr

private def invScale {n : ℕ} (ε : ℝ) (v : CoeffSpace ℂ n) : CoeffSpace ℂ n :=
  WithLp.toLp 2 (Fin.cons (v 0 / (ε : ℂ)) (fun i : Fin n => v i.succ))

private theorem norm_coeff_tail {n : ℕ} (v : CoeffSpace ℂ n) :
    ‖(WithLp.toLp 2 (Fin.cons 0 (fun i : Fin n => v i.succ)) : CoeffSpace ℂ n)‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, Fin.cons_succ]
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem invScale_le {n : ℕ} (v : CoeffSpace ℂ n) {ε : ℝ} (hε : 0 < ε) :
    ‖invScale ε v‖ ≤ ‖v 0‖ / ε + ‖v‖ := by
  let T : CoeffSpace ℂ n := WithLp.toLp 2 (Fin.cons 0 (fun i : Fin n => v i.succ))
  have h : invScale ε v = EuclideanSpace.single 0 (v 0 / (ε : ℂ)) + T := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [invScale, T]
    · simp [invScale, T]
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [PiLp.norm_single, norm_div, Complex.norm_real, Real.norm_of_nonneg hε.le]
  exact add_le_add_right (norm_coeff_tail v) _

private theorem norm_eval_sub_const {n : ℕ} (v : CoeffSpace ℂ n) (hv : ‖v‖ = 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) : ‖(poly v).eval a - v 0‖ ≤ 2 * ‖a‖ := by
  rw [poly_eval, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, add_sub_cancel_left, Fin.val_succ]
  have hsum : (∑ i ∈ range n, (1 / 2 : ℝ) ^ i) ≤ 2 := by
    have h := geom_sum_mul (1 / 2 : ℝ) n
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
  calc
    _ ≤ ∑ i : Fin n, ‖v i.succ * a ^ (i.val + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin n, ‖a‖ * (1 / 2 : ℝ) ^ i.val := by
      apply sum_le_sum
      intro i _
      have hi := PiLp.norm_apply_le v i.succ
      rw [hv] at hi
      rw [norm_mul, norm_pow, pow_succ, ← mul_assoc, mul_comm _ ‖a‖]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_left (pow_nonneg (norm_nonneg a) _) hi |>.trans
          (pow_le_pow_left₀ (norm_nonneg a) ha _)) (norm_nonneg a)
    _ ≤ 2 * ‖a‖ := by
      rw [← mul_sum, Fin.sum_univ_eq_sum_range, mul_comm 2]
      exact mul_le_mul_of_nonneg_left hsum (norm_nonneg _)

theorem scaled_norm_estimate {n : ℕ} (v : CoeffSpace ℂ n) (hv : ‖v‖ = 1)
    {a : ℂ} {R ε : ℝ} (hε : 0 < ε) (ha : ‖a‖ ≤ R * ε) (hR : R * ε ≤ 1 / 2) :
    min ε ‖(poly v).eval a‖ / (2 * R + 2) ≤ ‖(poly v).eval a‖ / ‖invScale ε v‖ := by
  have hR0 : 0 ≤ R := nonneg_of_mul_nonneg_left ((norm_nonneg a).trans ha) hε
  have hpos : 0 < ‖invScale ε v‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hz : v = 0 := by
      ext i
      have he := congrArg (fun u : CoeffSpace ℂ n => u i) h
      revert he
      refine Fin.cases ?_ (fun j => ?_) i
      · intro he
        simpa [invScale, Complex.ofReal_ne_zero.mpr hε.ne'] using he
      · intro he
        simpa [invScale] using he
    simp [hz] at hv
  let t := ‖(poly v).eval a‖
  have hb : ‖v 0‖ ≤ t + 2 * (R * ε) := by
    calc
      ‖v 0‖ = ‖(poly v).eval a + (v 0 - (poly v).eval a)‖ := by rw [add_sub_cancel]
      _ ≤ t + ‖(poly v).eval a - v 0‖ := by rw [norm_sub_rev]; exact norm_add_le _ _
      _ ≤ _ := by linarith [norm_eval_sub_const v hv (ha.trans hR), ha]
  have hS : ‖invScale ε v‖ ≤ t / ε + 2 * R + 1 := by
    refine (invScale_le v hε).trans ?_
    rw [hv]
    have hh := div_le_div_of_nonneg_right hb hε.le
    have he : (t + 2 * (R * ε)) / ε = t / ε + 2 * R := by field_simp
    rw [he] at hh
    linarith
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ min ε t / (2 * R + 2) * (t / ε + 2 * R + 1) := by
      apply mul_le_mul_of_nonneg_left hS
      positivity
    _ ≤ t := by
      have h : 0 < 2 * R + 2 := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ h]
      have he : min ε t * (t / ε) ≤ t := by
        calc
          _ ≤ ε * (t / ε) := mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
          _ = _ := by field_simp
      have ht : min ε t * (2 * R + 1) ≤ t * (2 * R + 1) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      linarith only [he, ht, mul_add (min ε t) (t / ε) (2 * R + 1)]

end KungTraubProof

namespace KungTraubProof

def B : ℕ → ℕ
  | 0 => 1
  | j + 1 => 2 ^ j

private theorem B_pos (j : ℕ) : 0 < B j := by
  cases j <;> simp [B]

private theorem B_sum (j : ℕ) (hj : 0 < j) : ∑ i ∈ range j, B i = B j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [sum_range_succ]
    cases j with
    | zero => simp [B]
    | succ j =>
      rw [ih (by omega)]
      simp [B, pow_succ, Nat.mul_two]

private def obsSpace (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d : ℕ) : ℕ → Submodule ℂ ℂ[X]
  | 0 => degreeLT ℂ (d + 1)
  | j + 1 => obsSpace L d j ⊓ (L j).ker

private theorem obs_mem {L : ℕ → ℂ[X] →ₗ[ℂ] ℂ} {d j : ℕ} {p : ℂ[X]} :
    p ∈ obsSpace L d j ↔ p.natDegree ≤ d ∧ ∀ i < j, L i p = 0 := by
  induction j with
  | zero => simp [obsSpace, degree_bound]
  | succ j ih =>
    change (p ∈ obsSpace L d j ∧ L j p = 0) ↔ _
    constructor
    · rintro ⟨hj, hl⟩
      obtain ⟨hd, hp⟩ := ih.mp hj
      refine ⟨hd, fun i hi => ?_⟩
      rcases (Nat.lt_succ_iff.mp hi).lt_or_eq with hi | rfl
      · exact hp i hi
      · exact hl
    · rintro ⟨hd, hp⟩
      exact ⟨ih.mpr ⟨hd, fun i hi => hp i (by omega)⟩, hp j (by omega)⟩

private theorem obs_le (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    obsSpace L d j ≤ degreeLT ℂ (d + 1) :=
  fun _ h => degree_bound.mpr (obs_mem.mp h).1

private instance obs_finite (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    Module.Finite ℂ (obsSpace L d j) :=
  Module.Finite.of_injective (Submodule.inclusion (obs_le L d j))
    (Submodule.inclusion_injective _)

private abbrev dim (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :=
  Module.finrank ℂ (obsSpace L d j)

private theorem degreeLT_dim (d : ℕ) : Module.finrank ℂ (degreeLT ℂ d) = d :=
  (degreeLTEquiv ℂ d).finrank_eq.trans (Module.finrank_fin_fun ℂ)

private theorem dim_zero (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d : ℕ) : dim L d 0 = d + 1 :=
  degreeLT_dim (d + 1)

private theorem dim_le (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) : dim L d j ≤ d + 1 :=
  (Submodule.finrank_mono (obs_le L d j)).trans_eq (degreeLT_dim _)

private theorem dim_drop (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    dim L d j ≤ dim L d (j + 1) + 1 := by
  let V := obsSpace L d j
  let f := (L j).domRestrict V
  have hf := LinearMap.finrank_range_add_finrank_ker f
  have hx : Module.finrank ℂ f.ker = dim L d (j + 1) := by
    rw [← Submodule.finrank_map_subtype_eq V, LinearMap.ker_domRestrict,
      Submodule.map_comap_subtype]
    rfl
  rw [hx] at hf
  have hr : Module.finrank ℂ f.range ≤ 1 :=
    (Submodule.finrank_le f.range).trans_eq (Module.finrank_self ℂ)
  change _ + _ = dim L d j at hf
  omega

private theorem dim_lower (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    d + 1 ≤ dim L d j + j := by
  induction j with
  | zero => simp [dim_zero]
  | succ j ih =>
    have h := dim_drop L d j
    omega

private def obsBasis (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    Fin (dim L d j) → ℂ[X] :=
  (obsSpace L d j).subtype ∘ Module.finBasis ℂ (obsSpace L d j)

private theorem obsBasis_independent (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    LinearIndependent ℂ (obsBasis L d j) :=
  (Module.finBasis ℂ (obsSpace L d j)).linearIndependent.map' _
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)

private theorem obsBasis_span (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) :
    Submodule.span ℂ (Set.range (obsBasis L d j)) = obsSpace L d j := by
  rw [obsBasis, Set.range_comp, ← LinearMap.map_span, Module.Basis.span_eq,
    Submodule.map_subtype_top]

private theorem obsBasis_deg (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (d j : ℕ) (i : Fin (dim L d j)) :
    (obsBasis L d j i).natDegree ≤ d :=
  (obs_mem.mp ((Module.finBasis ℂ (obsSpace L d j)) i).property).1

private theorem obs_exists_min_degree (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) {n j : ℕ} (hj : j ≤ n) :
    ∃ p : ℂ[X], p ∈ obsSpace L n j ∧ p ≠ 0 ∧
      ∀ q ∈ obsSpace L n j, q ≠ 0 → p.natDegree ≤ q.natDegree := by
  classical
  have hpos : 0 < dim L n j := by have := dim_lower L n j; omega
  let b := obsBasis L n j
  have ex : ∃ d : ℕ, ∃ p ∈ obsSpace L n j, p ≠ 0 ∧ p.natDegree = d := by
    let i : Fin (dim L n j) := ⟨0, hpos⟩
    refine ⟨(b i).natDegree, b i, ((Module.finBasis ℂ (obsSpace L n j)) i).property,
      (obsBasis_independent L n j).ne_zero i, rfl⟩
  obtain ⟨p, hp, hp0, hpd⟩ := Nat.find_spec ex
  refine ⟨p, hp, hp0, fun q hq hq0 => ?_⟩
  rw [hpd]
  exact Nat.find_min' ex ⟨q, hq, hq0, rfl⟩

private theorem dim_min_degree (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) {d n j : ℕ} (hdn : d ≤ n)
    (hmin : ∀ q ∈ obsSpace L n j, q ≠ 0 → d ≤ q.natDegree) :
    dim L d j ≤ 1 := by
  let f := (lcoeff ℂ d).domRestrict (obsSpace L d j)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro q hq
    have hc : (q : ℂ[X]).coeff d = 0 := hq
    have hd := (obs_mem.mp q.property).1
    have hmem := obs_mem.mpr ⟨hd.trans hdn, (obs_mem.mp q.property).2⟩
    apply Subtype.ext
    change (q : ℂ[X]) = 0
    by_contra hne
    have he : (q : ℂ[X]).natDegree = d := le_antisymm hd (hmin _ hmem hne)
    exact leadingCoeff_ne_zero.mpr hne (by simpa only [leadingCoeff, he] using hc)
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans_eq (Module.finrank_self ℂ)

private theorem stages_of_dimensions {D : ℕ → ℕ} {d j : ℕ}
    (h0 : D 0 = d + 1) (hj : D j ≤ 1)
    (hstep : ∀ i, D i ≤ D (i + 1) + 1) :
    ∃ f : Fin d ↪ Fin j, ∀ k, D ((f k).val + 1) = k.val + 1 := by
  classical
  have hex (k : Fin d) : ∃ i, D i ≤ k.val + 1 := ⟨j, hj.trans (by omega)⟩
  let a (k : Fin d) := Nat.find (hex k)
  have haj (k : Fin d) : a k ≤ j := Nat.find_min' (hex k) (hj.trans (by omega))
  have ha0 (k : Fin d) : a k ≠ 0 := by
    have := Nat.find_spec (hex k)
    change D (a k) ≤ k.val + 1 at this
    intro h
    rw [h, h0] at this
    omega
  have he (k : Fin d) : D (a k) = k.val + 1 := by
    have hval := Nat.find_spec (hex k)
    change D (a k) ≤ k.val + 1 at hval
    have hprev : ¬D (a k - 1) ≤ k.val + 1 :=
      Nat.find_min (hex k) (by change a k - 1 < a k; have := ha0 k; omega)
    have h := hstep (a k - 1)
    have h' : a k - 1 + 1 = a k := by have := ha0 k; omega
    rw [h'] at h
    omega
  let f (k : Fin d) : Fin j := ⟨a k - 1, by have := haj k; have := ha0 k; omega⟩
  have hf (k : Fin d) : D ((f k).val + 1) = k.val + 1 := by
    have : (f k).val + 1 = a k := by dsimp [f]; have := ha0 k; omega
    rw [this]
    exact he k
  refine ⟨⟨f, ?_⟩, hf⟩
  intro k l hk
  apply Fin.ext
  have e := hf k
  rw [hk, hf l] at e
  omega

private theorem sorted_distances (p : ℂ[X]) (a : ℂ) :
    ∃ ρ : Fin p.roots.card → ℝ,
      (∀ k, 0 ≤ ρ k ∧ k.val + 1 ≤ (p.roots.filter fun z => ‖z - a‖ ≤ ρ k).card) ∧
      (∏ k, min 1 (ρ k)) = (p.roots.map fun z => min 1 ‖a - z‖).prod := by
  let s := p.roots.map (fun z => ‖z - a‖)
  let l := s.sort (· ≤ ·)
  have hl : (l : Multiset ℝ) = s := Multiset.sort_eq _ _
  have hlen : l.length = p.roots.card := by
    simpa [s] using congrArg Multiset.card hl
  let ρ (k : Fin p.roots.card) := l.get (k.cast hlen.symm)
  refine ⟨ρ, ?_, ?_⟩
  · intro k
    have hk : ρ k ∈ s := by
      rw [← hl]
      exact List.get_mem l _
    obtain ⟨z, _, hz⟩ := Multiset.mem_map.mp hk
    refine ⟨hz ▸ norm_nonneg (z - a), ?_⟩
    let t := l.take (k.val + 1)
    have ht : (t : Multiset ℝ) ≤ s := by
      rw [← hl, Multiset.coe_le]
      exact (List.take_sublist _ _).subperm
    have htf : (t : Multiset ℝ) ≤ s.filter (· ≤ ρ k) := by
      refine Multiset.le_filter.mpr ⟨ht, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp (show x ∈ t from hx)
      have hi' : i < l.length := (lt_min_iff.mp hi).2
      have hik : i ≤ k.val := by have := (lt_min_iff.mp hi).1; omega
      rcases hik.lt_or_eq with hlt | he
      · exact (List.pairwise_iff_get.mp (Multiset.pairwise_sort s (· ≤ ·)))
          ⟨i, hi'⟩ (k.cast hlen.symm) hlt
      · subst i
        exact le_rfl
    have hc := Multiset.card_le_card htf
    have htc : t.length = k.val + 1 := by simp [t, List.length_take, hlen, k.isLt]
    change t.length ≤ (s.filter (· ≤ ρ k)).card at hc
    rw [htc] at hc
    dsimp only [s] at hc
    rw [Multiset.filter_map, Multiset.card_map] at hc
    exact hc
  · have he : (∏ k, min 1 (ρ k)) = ∏ i : Fin l.length, min 1 (l.get i) :=
      Fintype.prod_equiv (finCongr hlen.symm) _ _ (fun _ => rfl)
    rw [he]
    rw [← List.prod_ofFn]
    have hlist : List.ofFn (fun i : Fin l.length => min 1 (l.get i)) = l.map (min 1) := by
      change List.ofFn (min 1 ∘ l.get) = _
      rw [← List.map_ofFn]
      exact congrArg (List.map (min 1)) (List.ofFn_get l)
    rw [hlist]
    change ((l : Multiset ℝ).map (min 1)).prod = _
    rw [hl, Multiset.map_map]
    simp [norm_sub_rev]

end KungTraubProof

namespace KungTraubProof

private def Localizes (n : ℕ) (A : ℝ) : Prop :=
  ∀ {m : ℕ}, m ≤ n + 1 → ∀ (b : Fin m → ℂ[X]) (p : ℂ[X]) (a : ℂ) (r : ℝ),
    LinearIndependent ℂ b → (∀ i, (b i).natDegree ≤ n) →
    p ∈ Submodule.span ℂ (Set.range b) → p ≠ 0 → 0 ≤ r →
    m ≤ (p.roots.filter fun z => ‖z - a‖ ≤ r).card →
    ∃ z, (wr b).IsRoot z ∧ ‖z - a‖ ≤ A * r

private theorem uniform_localizer (n : ℕ) : ∃ A : ℝ, 1 ≤ A ∧ Localizes n A := by
  classical
  choose C hC hloc using fun i : Fin (n + 2) => wronskian_localization n i.val
  let A := 1 + ∑ i, C i
  have hsum : 0 ≤ ∑ i, C i := sum_nonneg fun i _ => (hC i).le
  refine ⟨A, by dsimp [A]; linarith, ?_⟩
  intro m hm b p a r hb hd hpb hp hr hs
  let i : Fin (n + 2) := ⟨m, by omega⟩
  have hi := single_le_sum (s := univ) (fun k _ => (hC k).le) (mem_univ i)
  obtain ⟨z, hz, he⟩ := hloc i b p a r hb hd hpb hp hr hs
  exact ⟨z, hz, he.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) hr)⟩

private noncomputable def badRoots (n : ℕ) (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (x : ℝ) (j : ℕ) :
    Finset ℝ := by
  classical
  exact (range (n + 1)).biUnion fun d =>
    (wr (obsBasis L d j)).roots.toFinset.image fun z => x + z.re

private theorem badRoots_card (n : ℕ) (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ) (x : ℝ) (j : ℕ) :
    (badRoots n L x j).card ≤ (n + 1) * ((n + 1) * n) := by
  classical
  unfold badRoots
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _ ∈ range (n + 1), (n + 1) * n := by
      apply sum_le_sum
      intro d hd
      have hdn : d ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hd
      exact card_image_le.trans ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans
        ((wr_spec _ (obsBasis_independent L d j) (obsBasis_deg L d j)).2.1.trans
          (Nat.mul_le_mul ((dim_le L d j).trans (by omega)) hdn))))
    _ = _ := by simp

private theorem mem_badRoots {n d j : ℕ} {L : ℕ → ℂ[X] →ₗ[ℂ] ℂ} {x : ℝ} {z : ℂ}
    (hd : d ≤ n) (hz : (wr (obsBasis L d j)).IsRoot z) :
    x + z.re ∈ badRoots n L x j := by
  classical
  apply mem_biUnion.mpr
  refine ⟨d, mem_range.mpr (by omega), mem_image.mpr ⟨z, ?_, rfl⟩⟩
  rw [Multiset.mem_toFinset]
  exact (mem_roots (wr_spec _ (obsBasis_independent L d j) (obsBasis_deg L d j)).1).mpr hz

private def coefficientBound (n j : ℕ) (A : ℝ) (γ : ℕ → ℝ) :=
  (4 : ℝ)⁻¹ ^ n * ∏ i ∈ range j, min 1 (γ i / A)

private theorem coefficientBound_pos {n j : ℕ} {A : ℝ} (hA : 0 < A)
    {γ : ℕ → ℝ} (hγ : ∀ i < j, 0 < γ i) :
    0 < coefficientBound n j A γ :=
  mul_pos (by positivity) (prod_pos fun i hi => lt_min zero_lt_one (div_pos (hγ i (mem_range.mp hi)) hA))

private theorem coefficientBound_le_one {n j : ℕ} {A : ℝ} (hA : 0 < A)
    {γ : ℕ → ℝ} (hγ : ∀ i < j, 0 < γ i) :
    coefficientBound n j A γ ≤ 1 := by
  unfold coefficientBound
  apply mul_le_one₀ (pow_le_one₀ (by norm_num) (by norm_num))
  · exact prod_nonneg fun i hi => le_min zero_le_one (div_nonneg (hγ i (mem_range.mp hi)).le hA.le)
  · exact prod_le_one (fun i hi => le_min zero_le_one (div_nonneg (hγ i (mem_range.mp hi)).le hA.le))
      (fun _ _ => min_le_left _ _)

private theorem polynomial_direction {n j : ℕ} (hj : j ≤ n) (L : ℕ → ℂ[X] →ₗ[ℂ] ℂ)
    {A ε x t : ℝ} (hA : 0 < A) (hLoc : Localizes n A) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (ha : ‖((t - x : ℝ) : ℂ)‖ ≤ 1 / 2)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    (haway : ∀ i < j, ∀ z ∈ badRoots n L x (i + 1), γ i * ε ^ B i ≤ |t - z|) :
    ∃ v : CoeffSpace ℂ n, ‖v‖ = 1 ∧ poly v ∈ obsSpace L n j ∧
      coefficientBound n j A γ * ε ^ B j ≤ ‖(poly v).eval ((t - x : ℝ) : ℂ)‖ := by
  classical
  obtain ⟨p, hp, hp0, hmin⟩ := obs_exists_min_degree L hj
  let b := coeffEquiv ℂ n ⟨p, obs_le L n j hp⟩
  have hb : poly b = p := by simp [poly, b]
  have hb0 : 0 < ‖b‖ := norm_pos_iff.mpr fun e => hp0 (by simpa [e] using hb.symm)
  let c : ℂ := (‖b‖⁻¹ : ℝ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero hb0.ne')
  let v := c • b
  have hv : ‖v‖ = 1 := by simp [v, c, norm_smul, hb0.ne']
  let q := poly v
  have hq : q = c • p := by simp [q, v, hb]
  have hq0 : q ≠ 0 := by rw [hq]; exact smul_ne_zero hc hp0
  have hqmem : q ∈ obsSpace L n j := hq ▸ (obsSpace L n j).smul_mem c hp
  let d := q.natDegree
  have hd : d = p.natDegree := by
    dsimp [d]
    rw [hq, smul_eq_C_mul, natDegree_C_mul hc]
  have hdn : d ≤ n := (obs_mem.mp hqmem).1
  have hdim := dim_min_degree L hdn (fun z hz hz0 => hd.trans_le (hmin z hz hz0))
  obtain ⟨f, hf⟩ := stages_of_dimensions (dim_zero L d) hdim (dim_drop L d)
  let a : ℂ := ((t - x : ℝ) : ℂ)
  have hcard : q.roots.card = d := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  obtain ⟨ρ, hρ, hprod⟩ := sorted_distances q a
  let g : Fin q.roots.card ↪ Fin j := (finCongr hcard).toEmbedding.trans f
  let F (i : ℕ) : ℝ := min 1 (γ i / A) * ε ^ B i
  have F_nonneg (i : ℕ) (hi : i < j) : 0 ≤ F i := by
    apply mul_nonneg (le_min zero_le_one (div_nonneg (hγ i hi).le hA.le)) (by positivity)
  have F_le (i : ℕ) : F i ≤ 1 := by
    exact mul_le_one₀ (min_le_left _ _) (by positivity) (pow_le_one₀ hε.le hε₁)
  have hfac (k : Fin q.roots.card) : F (g k).val ≤ min 1 (ρ k) := by
    let i := (g k).val
    have hi : i < j := (g k).isLt
    have hdim' : dim L d (i + 1) = k.val + 1 := hf ((finCongr hcard) k)
    have hmem : q ∈ obsSpace L d (i + 1) :=
      obs_mem.mpr ⟨le_rfl, fun l hl => (obs_mem.mp hqmem).2 l (by omega)⟩
    have hdeg (l : Fin (dim L d (i + 1))) : (obsBasis L d (i + 1) l).natDegree ≤ n :=
      (obsBasis_deg L d (i + 1) l).trans hdn
    obtain ⟨z, hz, hzr⟩ := hLoc ((dim_le L d (i + 1)).trans (by omega))
      (obsBasis L d (i + 1)) q a (ρ k) (obsBasis_independent L d (i + 1)) hdeg
      (by rwa [obsBasis_span]) hq0 (hρ k).1 (by rw [hdim']; exact (hρ k).2)
    have hnorm : |t - (x + z.re)| ≤ ‖z - a‖ := by
      have e := Complex.abs_re_le_norm (z - a)
      change |(z - a).re| ≤ _ at e
      rw [Complex.sub_re] at e
      change |z.re - (t - x)| ≤ _ at e
      rw [abs_sub_comm]
      convert e using 2
      ring
    have hl := (haway i hi _ (mem_badRoots hdn hz)).trans (hnorm.trans hzr)
    refine le_min (F_le i) ?_
    calc
      F i ≤ (γ i / A) * ε ^ B i :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ ≤ ρ k := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hA, mul_comm (ρ k)]
        exact hl
  let I : Finset ℕ := univ.image fun k : Fin q.roots.card => (g k).val
  have hI : I ⊆ range j := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := mem_image.mp hi
    exact mem_range.mpr (g k).isLt
  have hsub := prod_le_prod_of_subset_of_le_one hI
    (fun i hi => F_nonneg i (mem_range.mp hi)) (fun i _ _ => F_le i)
  have hF : (∏ i ∈ I, F i) = ∏ k, F (g k).val :=
    prod_image (fun _ _ _ _ e => g.injective (Fin.ext e))
  rw [hF] at hsub
  have ht : (∏ i ∈ range j, F i) ≤ (q.roots.map fun z => min 1 ‖a - z‖).prod :=
    hsub.trans (hprod ▸ prod_le_prod (fun k _ => F_nonneg _ (g k).isLt) (fun k _ => hfac k))
  have hB : ∑ i ∈ range j, B i ≤ B j := by
    by_cases hj0 : j = 0
    · simp [hj0, B]
    · exact (B_sum j (by omega)).le
  have hεB : ε ^ B j ≤ ε ^ (∑ i ∈ range j, B i) :=
    pow_le_pow_of_le_one hε.le hε₁ hB
  have hs : 0 ≤ ∏ i ∈ range j, min 1 (γ i / A) :=
    prod_nonneg fun i hi => le_min zero_le_one (div_nonneg (hγ i (mem_range.mp hi)).le hA.le)
  have hcn : (4 : ℝ)⁻¹ ^ n ≤ (4 : ℝ)⁻¹ ^ d :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hdn
  refine ⟨v, hv, hqmem, ?_⟩
  calc
    coefficientBound n j A γ * ε ^ B j ≤ (4 : ℝ)⁻¹ ^ d * ∏ i ∈ range j, F i := by
      simp only [coefficientBound, F, prod_mul_distrib, prod_pow_eq_pow_sum]
      rw [← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcn hs) hεB (by positivity)
        (mul_nonneg (by positivity) hs)
    _ ≤ (4 : ℝ)⁻¹ ^ d * _ := mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ _ := product_estimate v hv ha

end KungTraubProof

namespace KungTraubProof
open OMA.S_wp_kung_traub_conjecture (Method answer)
open scoped Topology

noncomputable def vVec {n : ℕ} (w : ℝ → ℝ) (x ε : ℝ)
    (k : Fin (n + 1)) (t : ℝ) : ℝ :=
  Fin.cases (w t * ε) (fun i : Fin n => w t * (t - x) ^ (i.val + 1)) k

noncomputable def perturb {n : ℕ} (w : ℝ → ℝ) (x ε : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) : ℝ :=
  w t * (ε * u 0 + ∑ i : Fin n, u i.succ * (t - x) ^ (i.val + 1))

noncomputable def familyFn {n : ℕ} (f₀ w : ℝ → ℝ) (x ε : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) : ℝ :=
  f₀ t + perturb w x ε u t

structure FamilyHyp {n : ℕ} (f₀ w : ℝ → ℝ) (x ε m M R wstar : ℝ)
    (α : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) : Prop where
  root : ∀ u : CoeffSpace ℝ n, ‖u‖ ≤ 1 → familyFn f₀ w x ε u (α u) = 0
  derivBounds : ∀ u : CoeffSpace ℝ n, ‖u‖ ≤ 1 → ∀ t, DifferentiableAt ℝ (familyFn f₀ w x ε u) t ∧
    m ≤ deriv (familyFn f₀ w x ε u) t ∧ deriv (familyFn f₀ w x ε u) t ≤ M
  rootNear : ∀ u : CoeffSpace ℝ n, ‖u‖ ≤ 1 → |α u - x| ≤ R * ε
  weight : ∀ u : CoeffSpace ℝ n, ‖u‖ ≤ 1 → wstar ≤ |w (α u)|
  linear : ∀ u : CoeffSpace ℝ n, ‖u‖ ≤ 1 → ∀ (ν : ℕ) (t : ℝ),
    iteratedDeriv ν (familyFn f₀ w x ε u) t =
      iteratedDeriv ν f₀ t + ∑ i : Fin (n + 1), u i * iteratedDeriv ν (vVec w x ε i) t

private def row {n : ℕ} (l : Fin (n + 1) → ℝ) : CoeffSpace ℝ n →ₗ[ℝ] ℝ where
  toFun u := ∑ i, u i * l i
  map_add' u v := by simp [add_mul, sum_add_distrib]
  map_smul' c u := by simp [mul_assoc, mul_sum]

private theorem row_apply {n : ℕ} (c : Fin (n + 1) → ℝ) (u : CoeffSpace ℝ n) :
    row c u = ∑ i, u i * c i := rfl

private abbrev evalRow {n : ℕ} (w : ℝ → ℝ) (x ε t : ℝ) :=
  row (fun i : Fin (n + 1) => vVec w x ε i t)

private theorem evalRow_apply {n : ℕ} (w : ℝ → ℝ) (x ε t : ℝ) (u : CoeffSpace ℝ n) :
    evalRow w x ε t u = perturb w x ε u t := by
  rw [row_apply, Fin.sum_univ_succ, perturb]
  simp only [vVec, Fin.cases_zero, Fin.cases_succ, mul_add, mul_sum]
  congr 1
  · ring
  · apply sum_congr rfl
    intro i _
    ring

private theorem secant {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α)
    {u : CoeffSpace ℝ n} (hu : ‖u‖ ≤ 1) {a b : ℝ} (hab : a ≤ b) :
    m * (b - a) ≤ familyFn f₀ w x ε u b - familyFn f₀ w x ε u a ∧
    familyFn f₀ w x ε u b - familyFn f₀ w x ε u a ≤ M * (b - a) := by
  have hd : Differentiable ℝ (familyFn f₀ w x ε u) := fun t => (H.derivBounds u hu t).1
  exact ⟨(convex_univ : Convex ℝ Set.univ).mul_sub_le_image_sub_of_le_deriv
      hd.continuous.continuousOn hd.differentiableOn (fun t _ => (H.derivBounds u hu t).2.1)
      a trivial b trivial hab,
    (convex_univ : Convex ℝ Set.univ).image_sub_le_mul_sub_of_deriv_le
      hd.continuous.continuousOn hd.differentiableOn (fun t _ => (H.derivBounds u hu t).2.2)
      a trivial b trivial hab⟩

private theorem root_eval_bounds {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α) (hm : 0 < m)
    {u : CoeffSpace ℝ n} (hu : ‖u‖ ≤ 1) (t : ℝ) :
    m * |t - α u| ≤ |familyFn f₀ w x ε u t| ∧
    |familyFn f₀ w x ε u t| ≤ M * |t - α u| := by
  rcases le_total (α u) t with ht | ht
  · obtain ⟨h1, h2⟩ := secant H hu ht
    rw [H.root u hu, sub_zero] at h1 h2
    rw [abs_of_nonneg (sub_nonneg.mpr ht),
      abs_of_nonneg ((mul_nonneg hm.le (sub_nonneg.mpr ht)).trans h1)]
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := secant H hu ht
    rw [H.root u hu, zero_sub] at h1 h2
    rw [abs_of_nonpos (sub_nonpos.mpr ht),
      abs_of_nonpos (neg_nonneg.mp ((mul_nonneg hm.le (sub_nonneg.mpr ht)).trans h1)),
      neg_sub]
    exact ⟨h1, h2⟩

private theorem family_sub {n : ℕ} (f₀ w : ℝ → ℝ) (x ε t : ℝ) (u v : CoeffSpace ℝ n) :
    familyFn f₀ w x ε v t - familyFn f₀ w x ε u t = evalRow w x ε t (v - u) := by
  simp only [map_sub, evalRow_apply, familyFn]
  ring

private theorem α_continuousOn {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α) (hm : 0 < m) :
    ContinuousOn α {u | ‖u‖ ≤ 1} := by
  intro u hu
  rw [Metric.continuousWithinAt_iff]
  intro e he
  let L := (evalRow w x ε (α u) : CoeffSpace ℝ n →ₗ[ℝ] ℝ).toContinuousLinearMap
  refine ⟨m * e / (‖L‖ + 1), by positivity, ?_⟩
  intro v hv hdist
  have hs := (root_eval_bounds H hm hv (α u)).1
  have hef : familyFn f₀ w x ε v (α u) = L (v - u) := by
    change familyFn f₀ w x ε v (α u) = evalRow w x ε (α u) (v - u)
    simpa only [H.root u hu, sub_zero] using family_sub f₀ w x ε (α u) u v
  rw [hef, abs_sub_comm (α u), ← Real.norm_eq_abs (L _)] at hs
  rw [dist_eq_norm] at hdist
  change |α v - α u| < e
  have hbound := L.le_opNorm (v - u)
  have hlt : (‖L‖ + 1) * ‖v - u‖ < m * e := by
    have h := (lt_div_iff₀ (by positivity : 0 < ‖L‖ + 1)).mp hdist
    rwa [mul_comm] at h
  nlinarith [norm_nonneg (v - u)]

private def parameterBall {n : ℕ} (E : Submodule ℝ (CoeffSpace ℝ n))
    (u : CoeffSpace ℝ n) (r : ℝ) : Set (CoeffSpace ℝ n) :=
  {v | v - u ∈ E ∧ ‖v - u‖ ≤ r}

private theorem parameterBall_compact {n : ℕ} (E : Submodule ℝ (CoeffSpace ℝ n))
    (u : CoeffSpace ℝ n) (r : ℝ) : IsCompact (parameterBall E u r) := by
  have h : parameterBall E u r = Metric.closedBall u r ∩ (fun v => v - u) ⁻¹' (E : Set _) := by
    ext v
    simp [parameterBall, Metric.mem_closedBall, dist_eq_norm, and_comm]
  rw [h]
  exact (isCompact_closedBall _ _).inter_right
    (E.closed_of_finiteDimensional.preimage (continuous_id.sub continuous_const))

private theorem parameterBall_convex {n : ℕ} (E : Submodule ℝ (CoeffSpace ℝ n))
    (u : CoeffSpace ℝ n) (r : ℝ) : Convex ℝ (parameterBall E u r) := by
  intro v hv z hz a b ha hb hab
  change (a • v + b • z - u) ∈ E ∧ ‖a • v + b • z - u‖ ≤ r
  have h : a • v + b • z - u = a • (v - u) + b • (z - u) := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  rw [h]
  refine ⟨E.add_mem (E.smul_mem _ hv.1) (E.smul_mem _ hz.1), (norm_add_le _ _).trans ?_⟩
  rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  calc
    _ ≤ a * r + b * r := add_le_add (mul_le_mul_of_nonneg_left hv.2 ha)
      (mul_le_mul_of_nonneg_left hz.2 hb)
    _ = r := by rw [← add_mul, hab, one_mul]

private theorem mem_parameterBall_add {n : ℕ} {E : Submodule ℝ (CoeffSpace ℝ n)}
    (u : CoeffSpace ℝ n) {h : CoeffSpace ℝ n} {r : ℝ} (hh : h ∈ E) (hr : ‖h‖ ≤ r) :
    u + h ∈ parameterBall E u r := by simpa [parameterBall] using And.intro hh hr

end KungTraubProof

namespace KungTraubProof

private theorem grid_avoid (S : Finset ℝ) {N : ℕ} (hS : S.card ≤ N) {l u : ℝ} (h : l < u) :
    ∃ y ∈ Set.Icc l u, ∀ z ∈ S, (u - l) / (2 * (N + 1)) ≤ |y - z| := by
  classical
  let s : ℝ := (u - l) / (N + 1)
  have hs : 0 < s := by dsimp [s]; positivity
  let g (i : Fin (N + 1)) : ℝ := l + (i.val + 1 / 2) * s
  let Near (z : ℝ) := (univ : Finset (Fin (N + 1))).filter fun i => |g i - z| < s / 2
  have hc (z : ℝ) : (Near z).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    have hab := abs_sub_le (g i) z (g j)
    rw [abs_sub_comm z] at hab
    have hlt : |g i - g j| < s := by linarith
    apply Fin.ext
    by_contra hn
    have hg : g i - g j = ((i.val : ℝ) - j.val) * s := by dsimp [g]; ring
    rw [hg, abs_mul, abs_of_pos hs, mul_lt_iff_lt_one_left hs] at hlt
    rcases lt_or_gt_of_ne hn with hh | hh
    · have hh' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (show i.val + 1 ≤ j.val by omega)
      have := (abs_lt.mp hlt).1
      linarith
    · have hh' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast (show j.val + 1 ≤ i.val by omega)
      have := (abs_lt.mp hlt).2
      linarith
  have hcard : (S.biUnion Near).card ≤ N := (card_biUnion_le.trans
    ((sum_le_sum fun z _ => hc z).trans_eq (by simp))).trans hS
  obtain ⟨i, _, hi⟩ := exists_mem_notMem_of_card_lt_card (s := S.biUnion Near)
    (t := (univ : Finset (Fin (N + 1)))) (by simpa using Nat.lt_succ_of_le hcard)
  refine ⟨g i, ⟨?_, ?_⟩, ?_⟩
  · dsimp [g]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) hs.le)
  · have hi' : (i.val : ℝ) + 1 / 2 ≤ N + 1 := by
      have hh : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.lt_succ_iff.mp i.isLt)
      linarith
    have hh := mul_le_mul_of_nonneg_right hi' hs.le
    have he : (N + 1 : ℝ) * s = u - l := by dsimp [s]; field_simp
    dsimp [g]
    linarith
  · intro z hz
    have hnear : i ∉ Near z := fun h => hi (mem_biUnion.mpr ⟨z, hz, h⟩)
    have h' : s / 2 ≤ |g i - z| := le_of_not_gt fun h => hnear (mem_filter.mpr ⟨mem_univ _, h⟩)
    exact (show (u - l) / (2 * (N + 1)) ≤ s / 2 by dsimp [s]; rw [div_div, mul_comm]).trans h'

private theorem root_interval {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α) (hm : 0 < m)
    (E : Submodule ℝ (CoeffSpace ℝ n)) (c : CoeffSpace ℝ n) {r : ℝ} (hr : 0 ≤ r)
    (hfit : ∀ u ∈ parameterBall E c r, ‖u‖ ≤ 1) :
    ∃ l u, α '' parameterBall E c r = Set.Icc l u := by
  let S := parameterBall E c r
  have hc : c ∈ S := by simp [S, parameterBall, hr]
  have hC := parameterBall_compact E c r
  have hCont : ContinuousOn α S := (α_continuousOn H hm).mono hfit
  obtain ⟨l, hl, hmin⟩ := hC.exists_isMinOn ⟨c, hc⟩ hCont
  obtain ⟨u, hu, hmax⟩ := hC.exists_isMaxOn ⟨c, hc⟩ hCont
  refine ⟨α l, α u, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨hmin hv, hmax hv⟩
  · have hpre := (parameterBall_convex E c r).isPreconnected.image α hCont
    exact (isPreconnected_iff_ordConnected.mp hpre).out ⟨l, hl, rfl⟩ ⟨u, hu, rfl⟩

private theorem root_range_length {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α) (hm : 0 < m)
    (hM : 0 < M) {E : Submodule ℝ (CoeffSpace ℝ n)} {c h : CoeffSpace ℝ n} {r l u A : ℝ}
    (hr : 0 ≤ r) (hh : h ∈ E) (hn : ‖h‖ ≤ 1) (ha : A ≤ |evalRow w x ε (α c) h|)
    (hfit : ∀ v ∈ parameterBall E c (r / 2), ‖v‖ ≤ 1)
    (hI : α '' parameterBall E c (r / 2) = Set.Icc l u) :
    r * A / (2 * M) ≤ u - l := by
  let v := c + (r / 2) • h
  have hvs : v ∈ parameterBall E c (r / 2) := by
    apply mem_parameterBall_add _ (E.smul_mem _ hh)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) hn
  have hcs : c ∈ parameterBall E c (r / 2) := by simp [parameterBall]; positivity
  have hv : α v ∈ Set.Icc l u := hI ▸ ⟨v, hvs, rfl⟩
  have hc : α c ∈ Set.Icc l u := hI ▸ ⟨c, hcs, rfl⟩
  have he : familyFn f₀ w x ε v (α c) = (r / 2) * evalRow w x ε (α c) h := by
    have h := family_sub f₀ w x ε (α c) c v
    rw [H.root c (hfit c hcs), sub_zero] at h
    simpa only [v, add_sub_cancel_left, map_smul, smul_eq_mul] using h
  have hb := (root_eval_bounds H hm (hfit v hvs) (α c)).2
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r / 2)] at hb
  have hd : |α c - α v| ≤ u - l := abs_le.mpr ⟨by linarith [hc.1, hv.2], by linarith [hc.2, hv.1]⟩
  apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
  nlinarith [mul_le_mul_of_nonneg_left ha (show 0 ≤ r / 2 by positivity),
    mul_le_mul_of_nonneg_left hd hM.le]

private theorem root_range_motion {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α) (hm : 0 < m)
    (hM : 0 < M) {E : Submodule ℝ (CoeffSpace ℝ n)} {c u v : CoeffSpace ℝ n} {r l U : ℝ}
    (hr : 0 < r) (hu : u ∈ parameterBall E c (r / 2)) (hv : ‖v‖ ≤ 1) (hdir : v - u ∈ E)
    (hfit : ∀ p ∈ parameterBall E c (r / 2), ‖p‖ ≤ 1)
    (hI : α '' parameterBall E c (r / 2) = Set.Icc l U) :
    |α v - α u| ≤ 4 * M * (U - l) / (m * r) * ‖v - u‖ := by
  by_cases e : v = u
  · simp [e]
  have hdpos : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr e)
  let a := r / (2 * ‖v - u‖)
  have ha : 0 < a := by dsimp [a]; positivity
  let p := c + a • (v - u)
  have hpS : p ∈ parameterBall E c (r / 2) := by
    apply mem_parameterBall_add _ (E.smul_mem _ hdir)
    rw [norm_smul, Real.norm_of_nonneg ha.le]
    dsimp [a]
    field_simp
    exact le_rfl
  have hcS : c ∈ parameterBall E c (r / 2) := by simp [parameterBall]; positivity
  let t := α u
  have ht : t ∈ Set.Icc l U := hI ▸ ⟨u, hu, rfl⟩
  have hf : ∀ z ∈ parameterBall E c (r / 2), |familyFn f₀ w x ε z t| ≤ M * (U - l) := by
    intro z hz
    have hzI : α z ∈ Set.Icc l U := hI ▸ ⟨z, hz, rfl⟩
    apply (root_eval_bounds H hm (hfit z hz) t).2.trans
    apply mul_le_mul_of_nonneg_left _ hM.le
    exact abs_le.mpr ⟨by linarith [ht.1, hzI.2], by linarith [ht.2, hzI.1]⟩
  have he : familyFn f₀ w x ε p t - familyFn f₀ w x ε c t =
      a * evalRow w x ε t (v - u) := by
    simpa only [p, add_sub_cancel_left, map_smul, smul_eq_mul] using family_sub f₀ w x ε t c p
  have hf' := abs_sub (familyFn f₀ w x ε p t) (familyFn f₀ w x ε c t)
  rw [he, abs_mul, abs_of_pos ha] at hf'
  have hmove := (root_eval_bounds H hm hv t).1
  have hmove' : familyFn f₀ w x ε v t = evalRow w x ε t (v - u) := by
    simpa only [t, H.root u (hfit u hu), sub_zero] using family_sub f₀ w x ε t u v
  rw [hmove', abs_sub_comm] at hmove
  have hbound : a * (m * |α v - α u|) ≤ 2 * M * (U - l) :=
    (mul_le_mul_of_nonneg_left hmove ha.le).trans
      (hf'.trans (by linarith [hf p hpS, hf c hcS]))
  change (r / (2 * ‖v - u‖)) * (m * |α v - α u|) ≤ _ at hbound
  rw [div_mul_eq_mul_div] at hbound
  have h' : r * (m * |α v - α u|) ≤ 2 * M * (U - l) * (2 * ‖v - u‖) :=
    (div_le_iff₀ (by positivity : 0 < 2 * ‖v - u‖)).mp hbound
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hm hr)]
  nlinarith only [h']

end KungTraubProof

namespace KungTraubProof
open OMA.S_wp_kung_traub_conjecture (Method answer)

private abbrev Query := Option (ℝ × ℕ)

private def observationValues {n : ℕ} (w : ℝ → ℝ) (x ε : ℝ) (q : Query) :
    Fin (n + 1) → ℝ :=
  fun i => answer q (vVec w x ε i)

private def realKernel {n : ℕ} (w : ℝ → ℝ) (x ε : ℝ) (Q : ℕ → Query) (j : ℕ) :
    Submodule ℝ (CoeffSpace ℝ n) :=
  ⨅ i : Fin j, (row (observationValues w x ε (Q i.val))).ker

private theorem realKernel_mem {n j : ℕ} {w : ℝ → ℝ} {x ε : ℝ} {Q : ℕ → Query}
    {v : CoeffSpace ℝ n} :
    v ∈ realKernel w x ε Q j ↔ ∀ i < j, row (observationValues w x ε (Q i)) v = 0 := by
  rw [realKernel, Submodule.mem_iInf]
  constructor
  · exact fun h i hi => h ⟨i, hi⟩
  · exact fun h i => h i.val i.isLt

private def queries {n : ℕ} (method : Method n) (f : ℝ → ℝ) (x : ℝ) (i : ℕ) :
    Query :=
  if hi : i < n then method.query ⟨i, hi⟩ x (method.answers f x i hi.le) else none

private theorem answer_sub {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α)
    {u v : CoeffSpace ℝ n} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (q : Query) :
    answer q (familyFn f₀ w x ε v) - answer q (familyFn f₀ w x ε u) =
      row (observationValues w x ε q) (v - u) := by
  cases q with
  | none => simp [answer, row_apply, observationValues]
  | some q =>
    obtain ⟨z, ν⟩ := q
    simp only [answer, H.linear v hv, H.linear u hu, add_sub_add_left_eq_sub,
      row_apply, observationValues, PiLp.sub_apply, sub_mul, sum_sub_distrib]

private theorem answers_eq {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α)
    {u v : CoeffSpace ℝ n} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (method : Method n)
    (j : ℕ) (hj : j ≤ n)
    (hd : v - u ∈ realKernel w x ε (queries method (familyFn f₀ w x ε u) x) j) :
    method.answers (familyFn f₀ w x ε u) x j hj =
      method.answers (familyFn f₀ w x ε v) x j hj := by
  induction j with
  | zero => exact Subsingleton.elim _ _
  | succ j ih =>
    have hj' : j < n := hj
    have hprev := ih hj'.le (realKernel_mem.mpr
      fun i hi => realKernel_mem.mp hd i (by omega))
    simp only [Method.answers]
    rw [← hprev]
    congr 1
    symm
    apply sub_eq_zero.mp
    rw [answer_sub H hu hv]
    have hzero := realKernel_mem.mp hd j (by omega)
    simpa only [queries, dif_pos hj'] using hzero

private theorem queries_eq {n : ℕ} {f₀ w : ℝ → ℝ} {x ε m M R wstar : ℝ}
    {α : CoeffSpace ℝ n → ℝ} (H : FamilyHyp f₀ w x ε m M R wstar α)
    {u v : CoeffSpace ℝ n} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (method : Method n)
    (j : ℕ) (_hj : j ≤ n)
    (hd : v - u ∈ realKernel w x ε (queries method (familyFn f₀ w x ε u) x) j)
    (i : ℕ) (hi : i ≤ j) :
    queries method (familyFn f₀ w x ε u) x i =
      queries method (familyFn f₀ w x ε v) x i := by
  by_cases h : i < n
  · simp only [queries, dif_pos h]
    rw [answers_eq H hu hv method i h.le
      (realKernel_mem.mpr fun k hk => realKernel_mem.mp hd k (hk.trans_le hi))]
  · simp [queries, h]

private def coefficientRow {n : ℕ} (ε : ℝ) (l : Fin (n + 1) → ℝ) : ℂ[X] →ₗ[ℂ] ℂ :=
  ((l 0 : ℂ) / (ε : ℂ)) • lcoeff ℂ 0 +
    ∑ i : Fin n, (l i.succ : ℂ) • lcoeff ℂ (i.val + 1)

private abbrev polynomialRows {n : ℕ} (w : ℝ → ℝ) (x ε : ℝ) (Q : ℕ → Query)
    (j : ℕ) : ℂ[X] →ₗ[ℂ] ℂ :=
  coefficientRow ε (observationValues (n := n) w x ε (Q j))

private def rowC {n : ℕ} (l : Fin (n + 1) → ℝ) (v : CoeffSpace ℂ n) : ℂ :=
  ∑ i, v i * (l i : ℂ)

private theorem coefficientRow_eq {n : ℕ} (ε : ℝ) (l : Fin (n + 1) → ℝ)
    (b : CoeffSpace ℂ n) : coefficientRow ε l (poly b) = rowC l (invScale ε b) := by
  simp only [coefficientRow, rowC, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, lcoeff_apply, Fin.sum_univ_succ, invScale,
    Fin.cons_zero, Fin.cons_succ]
  rw [show (poly b).coeff 0 = b 0 from poly_coeff b 0]
  congr 1
  · ring
  · apply sum_congr rfl
    intro i _
    rw [show (poly b).coeff (i.val + 1) = b i.succ from poly_coeff b i.succ]
    ring

private theorem eval_rowC {n : ℕ} (w : ℝ → ℝ) (x ε t : ℝ) (hε : 0 < ε)
    (v : CoeffSpace ℂ n) :
    rowC (fun i => vVec w x ε i t) (invScale ε v) =
      (w t : ℂ) * (poly v).eval ((t - x : ℝ) : ℂ) := by
  rw [poly_eval]
  simp only [rowC, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, mul_one,
    mul_add, mul_sum, invScale, Fin.cons_zero, Fin.cons_succ, vVec, Fin.cases_zero,
    Fin.cases_succ, Complex.ofReal_mul, Complex.ofReal_pow]
  congr 1
  · field_simp [Complex.ofReal_ne_zero.mpr hε.ne']
  · apply sum_congr rfl
    intro i _
    ring

private def partVector {n : ℕ} (p : ℂ → ℝ) (u : CoeffSpace ℂ n) : CoeffSpace ℝ n :=
  WithLp.toLp 2 (fun i => p (u i))

private theorem norm_partVector_le {n : ℕ} (p : ℂ → ℝ) (u : CoeffSpace ℂ n)
    (hp : ∀ z, |p z| ≤ ‖z‖) : ‖partVector p u‖ ≤ ‖u‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply sum_le_sum
  intro i _
  exact pow_le_pow_left₀ (norm_nonneg _) (hp _) _

private theorem row_partVector_re {n : ℕ} (l : Fin (n + 1) → ℝ) (u : CoeffSpace ℂ n) :
    row l (partVector Complex.re u) = (rowC l u).re := by
  change _ = Complex.reCLM (∑ i, u i * (l i : ℂ))
  rw [map_sum]
  simp [row_apply, partVector, Complex.mul_re]

private theorem row_partVector_im {n : ℕ} (l : Fin (n + 1) → ℝ) (u : CoeffSpace ℂ n) :
    row l (partVector Complex.im u) = (rowC l u).im := by
  change _ = Complex.imCLM (∑ i, u i * (l i : ℂ))
  rw [map_sum]
  simp [row_apply, partVector, Complex.mul_im]

private theorem rowC_smul {n : ℕ} (l : Fin (n + 1) → ℝ) (z : ℂ) (v : CoeffSpace ℂ n) :
    rowC l (z • v) = z * rowC l v := by simp [rowC, mul_sum, mul_assoc]

private theorem real_direction {n j : ℕ} (hj : j ≤ n) (w : ℝ → ℝ) (Q : ℕ → Query)
    {A ε x t R wstar : ℝ} (hA : 0 < A) (hLoc : Localizes n A) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hw : 0 < wstar) (hw' : wstar ≤ |w t|) (hNear : |t - x| ≤ R * ε) (hR : R * ε ≤ 1 / 2)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    (haway : ∀ i < j, ∀ z ∈ badRoots n (polynomialRows (n := n) w x ε Q) x (i + 1),
      γ i * ε ^ B i ≤ |t - z|) :
    ∃ h : CoeffSpace ℝ n, h ∈ realKernel w x ε Q j ∧ ‖h‖ ≤ 1 ∧
      wstar / (2 * (2 * R + 2)) * coefficientBound n j A γ * ε ^ B j ≤
        |evalRow w x ε t h| := by
  let a : ℂ := ((t - x : ℝ) : ℂ)
  have ha : ‖a‖ ≤ R * ε := by simpa only [a, Complex.norm_real, Real.norm_eq_abs] using hNear
  obtain ⟨v, hv, hmem, hval⟩ :=
    polynomial_direction hj (polynomialRows w x ε Q) hA hLoc hε hε₁ (ha.trans hR) γ hγ haway
  let d := ‖invScale ε v‖
  have hd : 0 < d := by
    apply norm_pos_iff.mpr
    intro he
    have heval := eval_rowC w x ε t hε v
    rw [he] at heval
    have hz : 0 = (w t : ℂ) * (poly v).eval a := by simpa [rowC, a] using heval
    have hw0 : (w t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
      intro e
      simp [e] at hw'
      linarith)
    have hq : (poly v).eval a = 0 := (mul_eq_zero.mp hz.symm).resolve_left hw0
    rw [hq, norm_zero] at hval
    exact (mul_pos (coefficientBound_pos hA hγ) (by positivity)).not_ge hval
  let z : CoeffSpace ℂ n := ((d⁻¹ : ℝ) : ℂ) • invScale ε v
  have hz : ‖z‖ = 1 := by simp [z, norm_smul, ← show d = ‖invScale ε v‖ from rfl, abs_of_pos hd, hd.ne']
  have hzK (i : ℕ) (hi : i < j) : rowC (observationValues w x ε (Q i)) z = 0 := by
    have hzero := (obs_mem.mp hmem).2 i hi
    change coefficientRow ε (observationValues w x ε (Q i)) (poly v) = 0 at hzero
    rw [coefficientRow_eq] at hzero
    rw [show rowC _ z = ((d⁻¹ : ℝ) : ℂ) * rowC _ (invScale ε v) from rowC_smul _ _ _,
      hzero, mul_zero]
  let L : Fin (n + 1) → ℝ := fun i => vVec w x ε i t
  have hzeval : ‖rowC L z‖ = |w t| * (‖(poly v).eval a‖ / d) := by
    rw [show rowC L z = ((d⁻¹ : ℝ) : ℂ) * rowC L (invScale ε v) from rowC_smul _ _ _]
    rw [show rowC L (invScale ε v) = (w t : ℂ) * (poly v).eval a from eval_rowC _ _ _ _ hε _]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hd, div_eq_mul_inv]
    ring
  have hR0 : 0 ≤ R := nonneg_of_mul_nonneg_left ((norm_nonneg a).trans ha) hε
  have hmin : coefficientBound n j A γ * ε ^ B j ≤ min ε ‖(poly v).eval a‖ := by
    apply le_min _ hval
    refine (mul_le_of_le_one_left (by positivity) (coefficientBound_le_one hA hγ)).trans ?_
    simpa using pow_le_pow_of_le_one hε.le hε₁ (show 1 ≤ B j from B_pos j)
  have he := (div_le_div_of_nonneg_right hmin (by positivity : 0 ≤ 2 * R + 2)).trans
    (scaled_norm_estimate v hv hε ha hR)
  have hbound : wstar * (coefficientBound n j A γ * ε ^ B j / (2 * R + 2)) ≤
      ‖rowC L z‖ := by
    rw [hzeval]
    exact mul_le_mul hw' he (div_nonneg
      (mul_nonneg (coefficientBound_pos hA hγ).le (by positivity)) (by positivity))
      (le_trans hw.le hw')
  let g := wstar / (2 * (2 * R + 2)) * coefficientBound n j A γ * ε ^ B j
  have hg : 2 * g ≤ ‖rowC L z‖ := by
    convert hbound using 1
    dsimp [g]
    field_simp [show 2 * R + 2 ≠ 0 by positivity]
  have hsum := Complex.norm_le_abs_re_add_abs_im (rowC L z)
  by_cases hgre : g ≤ |(rowC L z).re|
  · refine ⟨partVector Complex.re z, realKernel_mem.mpr (fun i hi => ?_),
      (norm_partVector_le _ _ Complex.abs_re_le_norm).trans_eq hz, ?_⟩
    · rw [row_partVector_re, hzK i hi, Complex.zero_re]
    · change g ≤ |row L (partVector Complex.re z)|
      rwa [row_partVector_re]
  · have hgim : g ≤ |(rowC L z).im| := by linarith
    refine ⟨partVector Complex.im z, realKernel_mem.mpr (fun i hi => ?_),
      (norm_partVector_le _ _ Complex.abs_im_le_norm).trans_eq hz, ?_⟩
    · rw [row_partVector_im, hzK i hi, Complex.zero_im]
    · change g ≤ |row L (partVector Complex.im z)|
      rwa [row_partVector_im]

end KungTraubProof

namespace KungTraubProof
open OMA.S_wp_kung_traub_conjecture (Method)

private theorem obsSpace_congr {L L' : ℕ → ℂ[X] →ₗ[ℂ] ℂ} {d j : ℕ}
    (h : ∀ i < j, L i = L' i) : obsSpace L d j = obsSpace L' d j := by
  ext p
  simp only [obs_mem]
  constructor <;> rintro ⟨hd, hz⟩ <;> refine ⟨hd, fun i hi => ?_⟩
  · rw [← h i hi]
    exact hz i hi
  · rw [h i hi]
    exact hz i hi

private theorem badRoots_congr {n j : ℕ} {L L' : ℕ → ℂ[X] →ₗ[ℂ] ℂ} (x : ℝ)
    (h : ∀ i < j, L i = L' i) : badRoots n L x j = badRoots n L' x j := by
  classical
  have H (d : ℕ) : (wr (obsBasis L d j)).roots.toFinset =
      (wr (obsBasis L' d j)).roots.toFinset := by
    have he : obsSpace L d j = obsSpace L' d j := obsSpace_congr h
    have hd : dim L d j = dim L' d j :=
      congrArg (fun V : Submodule ℂ ℂ[X] => Module.finrank ℂ V) he
    have hs : Submodule.span ℂ (Set.range (obsBasis L d j)) =
        Submodule.span ℂ (Set.range (obsBasis L' d j)) := by
      rw [obsBasis_span, obsBasis_span, he]
    ext z
    rw [Multiset.mem_toFinset, Multiset.mem_toFinset,
      mem_roots (wr_spec _ (obsBasis_independent L d j) (obsBasis_deg L d j)).1,
      mem_roots (wr_spec _ (obsBasis_independent L' d j) (obsBasis_deg L' d j)).1]
    exact ⟨wr_root_of_span_le hs.ge hd.symm, wr_root_of_span_le hs.le hd⟩
  simp only [badRoots, H]

private def avoidedCount (n : ℕ) : ℕ := (n + 1) * ((n + 1) * n) + 1

private def avoidedPoints (n : ℕ) (w : ℝ → ℝ) (x ε : ℝ) (Q : ℕ → Query) (i : ℕ) :
    Finset ℝ :=
  let S := badRoots n (polynomialRows (n := n) w x ε Q) x (i + 1)
  match Q i with
  | none => S
  | some (z, _) => insert z S

private theorem avoidedPoints_card (n : ℕ) (w : ℝ → ℝ) (x ε : ℝ) (Q : ℕ → Query) (i : ℕ) :
    (avoidedPoints n w x ε Q i).card ≤ avoidedCount n := by
  have h := badRoots_card n (polynomialRows (n := n) w x ε Q) x (i + 1)
  unfold avoidedPoints avoidedCount
  cases Q i with
  | none => exact h.trans (Nat.le_succ _)
  | some q => exact (card_insert_le _ _).trans (Nat.succ_le_succ h)

private theorem badRoots_subset_avoided (n : ℕ) (w : ℝ → ℝ) (x ε : ℝ) (Q : ℕ → Query) (i : ℕ) :
    badRoots n (polynomialRows (n := n) w x ε Q) x (i + 1) ⊆ avoidedPoints n w x ε Q i := by
  unfold avoidedPoints
  cases Q i with
  | none => exact Subset.rfl
  | some q => exact subset_insert _ _

private theorem query_mem_avoided {n i ν : ℕ} {w : ℝ → ℝ} {x ε z : ℝ} {Q : ℕ → Query}
    (h : Q i = some (z, ν)) : z ∈ avoidedPoints n w x ε Q i := by
  simp [avoidedPoints, h]

private theorem avoidedPoints_congr {n i : ℕ} (w : ℝ → ℝ) (x ε : ℝ) {Q Q' : ℕ → Query}
    (h : ∀ k ≤ i, Q k = Q' k) :
    avoidedPoints n w x ε Q i = avoidedPoints n w x ε Q' i := by
  have he := badRoots_congr (n := n) (j := i + 1)
    (L := polynomialRows (n := n) w x ε Q) (L' := polynomialRows (n := n) w x ε Q') x
      (fun k hk => by simp only [polynomialRows, h k (by omega)])
  simp only [avoidedPoints, he, h i le_rfl]

private def weightProduct (A : ℝ) (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => weightProduct A a j * min 1 (a j * weightProduct A a j / A)

private theorem weightProduct_pos {A : ℝ} (hA : 0 < A) {a : ℕ → ℝ} (ha : ∀ i, 0 < a i) :
    ∀ j, 0 < weightProduct A a j := by
  intro j
  induction j with
  | zero => simp [weightProduct]
  | succ j ih =>
    exact mul_pos ih (lt_min zero_lt_one (div_pos (mul_pos (ha j) ih) hA))

private theorem weightProduct_eq (A : ℝ) (a : ℕ → ℝ) (j : ℕ) :
    weightProduct A a j = ∏ i ∈ range j, min 1 (a i * weightProduct A a i / A) := by
  induction j with
  | zero => simp [weightProduct]
  | succ j ih =>
    rw [prod_range_succ]
    conv_lhs => rw [weightProduct]
    rw [← ih]

/-- Uniform bounds for all families at the specified scales and all methods with n queries.
The derivative bounds give the secant estimates used to control root motion. -/
theorem fixed_scale_lower_bound {n : ℕ} (_hn : 1 ≤ n)
    {m M R wstar ε_init : ℝ} (hm : 0 < m) (hmM : m ≤ M)
    (hR : 0 < R) (hw : 0 < wstar) (hinit : 0 < ε_init) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f₀ w : ℝ → ℝ) (α₀ : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
      (∀ ε ∈ Set.Ioo 0 ε_init, FamilyHyp f₀ w (α₀ + ε) ε m M R wstar (α ε)) →
      ∀ (method : Method n) (ε : ℝ), ε ∈ Set.Ioo 0 ε₀ →
      ∃ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 ∧
        c * ε ^ B n ≤ |method.step (familyFn f₀ w (α₀ + ε) ε u) (α₀ + ε) - α ε u| ∧
        ∀ (j : Fin n) (z : ℝ) (ν : ℕ),
          method.query j (α₀ + ε)
            (method.answers (familyFn f₀ w (α₀ + ε) ε u) (α₀ + ε) j.val j.isLt.le) =
            some (z, ν) → z ≠ α ε u := by
  classical
  obtain ⟨A, hA, hLoc⟩ := uniform_localizer n
  have hA0 : 0 < A := by linarith
  have hM : 0 < M := hm.trans_le hmM
  let N := avoidedCount n
  let θ := min (1 / 2 : ℝ) (m / (16 * M * (N + 1)))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  let r (j : ℕ) := θ ^ j / 2
  have hr (j : ℕ) : 0 < r j := by dsimp [r]; positivity
  have hrstep (j : ℕ) : r (j + 1) = θ * r j := by dsimp [r]; rw [pow_succ']; ring
  have hrhalf (j : ℕ) : r (j + 1) ≤ r j / 2 := by
    rw [hrstep]
    calc
      _ ≤ (1 / 2 : ℝ) * r j := mul_le_mul_of_nonneg_right (by
        dsimp [θ]
        exact min_le_left _ _) (hr j).le
      _ = _ := by ring
  let G := wstar / (2 * (2 * R + 2)) * (4 : ℝ)⁻¹ ^ n
  have hG : 0 < G := by dsimp [G]; positivity
  let a (j : ℕ) := r j * G / (8 * M * (N + 1))
  have ha (j : ℕ) : 0 < a j := by dsimp [a]; positivity
  let P := weightProduct A a
  have hP := weightProduct_pos hA0 ha
  let γ (j : ℕ) := a j * P j
  have hγ (j : ℕ) : 0 < γ j := mul_pos (ha j) (hP j)
  let C (j : ℕ) := G * P j
  have hC (j : ℕ) : 0 < C j := mul_pos hG (hP j)
  have hcoef (j : ℕ) :
      wstar / (2 * (2 * R + 2)) * coefficientBound n j A γ = C j := by
    change wstar / (2 * (2 * R + 2)) * coefficientBound n j A γ =
      G * weightProduct A a j
    rw [weightProduct_eq]
    simp only [coefficientBound, G, γ, P, mul_assoc]
  let c := r n * C n / (4 * M)
  let ε₀ := min ε_init (min 1 (1 / (2 * R)))
  have hc : 0 < c := div_pos (mul_pos (hr n) (hC n)) (by positivity)
  have he₀ : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨c, hc, ε₀, he₀, ?_⟩
  intro f₀ w α₀ α H method ε hε
  have hεInit : ε < ε_init := hε.2.trans_le (min_le_left _ _)
  have hε₁ : ε ≤ 1 := hε.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεR : R * ε ≤ 1 / 2 := by
    calc
      _ ≤ R * (1 / (2 * R)) := mul_le_mul_of_nonneg_left
        (hε.2.le.trans ((min_le_right _ _).trans (min_le_right _ _))) hR.le
      _ = _ := by field_simp [hR.ne']
  let x := α₀ + ε
  let F := familyFn f₀ w x ε (n := n)
  let root := α ε
  have HS : FamilyHyp f₀ w x ε m M R wstar root := H ε ⟨hε.1, hεInit⟩
  let Q (u : CoeffSpace ℝ n) := queries method (F u) x
  let E (u : CoeffSpace ℝ n) (j : ℕ) : Submodule ℝ (CoeffSpace ℝ n) :=
    realKernel w x ε (Q u) j
  let S (u : CoeffSpace ℝ n) (i : ℕ) := avoidedPoints n w x ε (Q u) i
  let Good (j : ℕ) (u : CoeffSpace ℝ n) : Prop :=
    ∀ v ∈ parameterBall (E u j) u (r j), ‖v‖ ≤ 1 ∧
      ∀ i < j, ∀ z ∈ S u i, γ i * ε ^ B i ≤ |root v - z|
  have center {j : ℕ} (u : CoeffSpace ℝ n) : u ∈ parameterBall (E u j) u (r j) := by
    simp [parameterBall, (hr j).le]
  have half {j : ℕ} {u v : CoeffSpace ℝ n}
      (hv : v ∈ parameterBall (E u j) u (r j / 2)) :
      v ∈ parameterBall (E u j) u (r j) :=
    ⟨hv.1, hv.2.trans (by linarith [hr j])⟩
  have direction {j : ℕ} (hj : j ≤ n) {u : CoeffSpace ℝ n} (hu : Good j u) :
      ∃ h ∈ E u j, ‖h‖ ≤ 1 ∧ C j * ε ^ B j ≤ |evalRow w x ε (root u) h| := by
    obtain ⟨hu₁, hu₂⟩ := hu u (center u)
    rw [← hcoef j]
    exact real_direction hj w (Q u) hA0 hLoc hε.1 hε₁ hw (HS.weight u hu₁)
      (HS.rootNear u hu₁) hεR γ (fun i _ => hγ i)
      (fun i hi z hz => hu₂ i hi z (badRoots_subset_avoided _ _ _ _ _ _ hz))
  have move (j : ℕ) (hj : j < n) (u : CoeffSpace ℝ n) (hu : Good j u) :
      ∃ u', Good (j + 1) u' := by
    have hu₁ := (hu u (center u)).1
    have hfit (v : CoeffSpace ℝ n) (hv : v ∈ parameterBall (E u j) u (r j / 2)) :
        ‖v‖ ≤ 1 := (hu v (half hv)).1
    obtain ⟨l, U, hI⟩ := root_interval HS hm (E u j) u (div_nonneg (hr j).le (by norm_num)) hfit
    obtain ⟨h, hh, hn, hval⟩ := direction hj.le hu
    have hlen := root_range_length HS hm hM (hr j).le hh hn hval hfit hI
    have hpos : 0 < r j * (C j * ε ^ B j) / (2 * M) :=
      div_pos (mul_pos (hr j) (mul_pos (hC j) (pow_pos hε.1 _))) (by positivity)
    have hlu : l < U := sub_pos.mp (hpos.trans_le hlen)
    obtain ⟨y, hy, haway⟩ := grid_avoid (S u j) (avoidedPoints_card _ _ _ _ _ _) hlu
    rw [← hI] at hy
    obtain ⟨u', hu', rfl⟩ := hy
    have hu'₁ := hfit u' hu'
    have hQ (i : ℕ) (hi : i ≤ j) : Q u i = Q u' i :=
      queries_eq HS hu₁ hu'₁ method j hj.le hu'.1 i hi
    refine ⟨u', ?_⟩
    intro v hv
    have hdir : v - u' ∈ E u j := by
      apply realKernel_mem.mpr
      intro i hi
      rw [hQ i hi.le]
      exact realKernel_mem.mp hv.1 i (by omega)
    have hsub : v - u = (v - u') + (u' - u) := by abel
    have hmem : v ∈ parameterBall (E u j) u (r j) := ⟨by
      rw [hsub]
      exact (E u j).add_mem hdir hu'.1, by
      rw [hsub]
      exact (norm_add_le _ _).trans (by linarith [hv.2, hu'.2, hrhalf j])⟩
    obtain ⟨hv₁, hprev⟩ := hu v hmem
    refine ⟨hv₁, ?_⟩
    intro i hi z hz
    have hS : S u i = S u' i := avoidedPoints_congr w x ε (fun k hk => hQ k (by omega))
    rw [← hS] at hz
    rcases (Nat.lt_succ_iff.mp hi).lt_or_eq with hi | he
    · exact hprev i hi z hz
    subst i
    have hdist := haway z hz
    change (U - l) / (2 * (N + 1 : ℝ)) ≤ |root u' - z| at hdist
    have hmoved := root_range_motion HS hm hM (hr j) hu' hv₁ hdir hfit hI
    have hnpos : 0 < (N + 1 : ℝ) := by positivity
    have hθq : θ ≤ m / (16 * M * (N + 1)) := min_le_right _ _
    have hmov : |root v - root u'| ≤ (U - l) / (4 * (N + 1)) := by
      have hL : 0 ≤ 4 * M * (U - l) / (m * r j) := by positivity
      calc
        _ ≤ (4 * M * (U - l) / (m * r j)) * r (j + 1) :=
          hmoved.trans (mul_le_mul_of_nonneg_left hv.2 hL)
        _ ≤ (4 * M * (U - l) / (m * r j)) * (m / (16 * M * (N + 1)) * r j) := by
          rw [hrstep]
          gcongr
        _ = _ := by field_simp [hm.ne', hM.ne', (hr j).ne', hnpos.ne']; ring
    have htri := abs_sub_le (root u') (root v) z
    rw [abs_sub_comm (root u') (root v)] at htri
    have hsep : (U - l) / (4 * (N + 1)) ≤ |root v - z| := by
      have he : (U - l) / (2 * (N + 1)) = 2 * ((U - l) / (4 * (N + 1))) := by
        field_simp [hnpos.ne']
        norm_num
      linarith
    apply le_trans _ hsep
    have hl := div_le_div_of_nonneg_right hlen (by positivity : (0 : ℝ) ≤ 4 * (N + 1))
    have he : r j * (C j * ε ^ B j) / (2 * M) / (4 * (N + 1)) = γ j * ε ^ B j := by
      dsimp [γ, a, C]
      field_simp [hM.ne', hnpos.ne']
      ring
    rwa [he] at hl
  have hgood : ∀ j ≤ n, ∃ u : CoeffSpace ℝ n, Good j u := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨0, fun v hv => ⟨?_, fun i hi => (Nat.not_lt_zero i hi).elim⟩⟩
      have h := hv.2
      change ‖v - 0‖ ≤ r 0 at h
      simp [r] at h
      linarith
    | succ j ih =>
      intro hj
      obtain ⟨u, hu⟩ := ih (by omega)
      exact move j (by omega) u hu
  obtain ⟨u, hu⟩ := hgood n le_rfl
  have hu₁ := (hu u (center u)).1
  have hfit (v : CoeffSpace ℝ n) (hv : v ∈ parameterBall (E u n) u (r n / 2)) :
      ‖v‖ ≤ 1 := (hu v (half hv)).1
  obtain ⟨l, U, hI⟩ := root_interval HS hm (E u n) u (div_nonneg (hr n).le (by norm_num)) hfit
  obtain ⟨h, hh, hn, hval⟩ := direction le_rfl hu
  have hlen := root_range_length HS hm hM (hr n).le hh hn hval hfit hI
  have hpos : 0 < r n * (C n * ε ^ B n) / (2 * M) :=
    div_pos (mul_pos (hr n) (mul_pos (hC n) (pow_pos hε.1 _))) (by positivity)
  have hlu : l ≤ U := sub_nonneg.mp (hpos.le.trans hlen)
  have hl : l ∈ root '' parameterBall (E u n) u (r n / 2) := hI.symm ▸ ⟨le_rfl, hlu⟩
  have hU : U ∈ root '' parameterBall (E u n) u (r n / 2) := hI.symm ▸ ⟨hlu, le_rfl⟩
  obtain ⟨v₁, hv₁, hroot₁⟩ := hl
  obtain ⟨v₂, hv₂, hroot₂⟩ := hU
  let y := method.step (F u) x
  have hend (v : CoeffSpace ℝ n) (hv : v ∈ parameterBall (E u n) u (r n / 2))
      (hval : c * ε ^ B n ≤ |y - root v|) :
      ‖v‖ ≤ 1 ∧ c * ε ^ B n ≤ |method.step (F v) x - root v| ∧
      ∀ (j : Fin n) (z : ℝ) (ν : ℕ), Q v j.val = some (z, ν) → z ≠ root v := by
    obtain ⟨hv₁, hv₂⟩ := hu v (half hv)
    have heq : method.step (F v) x = y :=
      congrArg (method.output x) (answers_eq HS hu₁ hv₁ method n le_rfl hv.1).symm
    refine ⟨hv₁, heq ▸ hval, ?_⟩
    intro j z ν hz hzero
    have hz' : Q u j.val = some (z, ν) :=
      (queries_eq HS hu₁ hv₁ method n le_rfl hv.1 _ j.isLt.le).trans hz
    have hdist := hv₂ j.val j.isLt z (query_mem_avoided hz')
    rw [hzero, sub_self, abs_zero] at hdist
    exact (mul_pos (hγ j.val) (pow_pos hε.1 _)).not_ge hdist
  have herrors : 2 * (c * ε ^ B n) ≤ |y - root v₁| + |y - root v₂| := by
    rw [hroot₁, hroot₂]
    have htri := abs_sub_le U y l
    rw [abs_of_nonneg (sub_nonneg.mpr hlu), abs_sub_comm U y] at htri
    have he : 2 * (c * ε ^ B n) = r n * (C n * ε ^ B n) / (2 * M) := by
      dsimp [c]
      ring
    linarith
  have hchoose : c * ε ^ B n ≤ |y - root v₁| ∨ c * ε ^ B n ≤ |y - root v₂| := by
    by_contra! hn
    linarith [hn.1, hn.2]
  obtain ⟨v, hvs, hv⟩ : ∃ v ∈ parameterBall (E u n) u (r n / 2),
      c * ε ^ B n ≤ |y - root v| :=
    hchoose.elim (fun h => ⟨v₁, hv₁, h⟩) (fun h => ⟨v₂, hv₂, h⟩)
  refine ⟨v, ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := hend v hvs hv
  exact ⟨h₁, h₂, fun j z ν he =>
    h₃ j z ν (by simpa only [Q, queries, dif_pos j.isLt] using he)⟩

end KungTraubProof

noncomputable section
open Filter Set Finset Polynomial
open scoped Topology
namespace KungTraubProof



private theorem root_exists {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ t, (1 / 2 : ℝ) ≤ deriv f t) : ∃ a, f a = 0 := by
  let R := 2 * |f 0| + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hl := mul_sub_le_image_sub_of_le_deriv hf h (neg_nonpos.mpr hR)
  have hr := mul_sub_le_image_sub_of_le_deriv hf h hR
  have ha : f (-R) ≤ 0 := by dsimp [R] at hl; linarith [le_abs_self (f 0)]
  have hb : 0 ≤ f R := by dsimp [R] at hr ⊢; linarith [neg_abs_le (f 0)]
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc (f := f)
    (show -R ≤ R by linarith) hf.continuous.continuousOn ⟨ha, hb⟩
  exact ⟨a, ha⟩

private theorem secant_abs_lower {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (h : ∀ t, (1 / 2 : ℝ) ≤ deriv f t) (a b : ℝ) :
    |a - b| / 2 ≤ |f a - f b| := by
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm a b, abs_sub_comm (f a) (f b), abs_of_nonneg (sub_nonneg.mpr hab)]
    have hs := mul_sub_le_image_sub_of_le_deriv hf h hab
    linarith [le_abs_self (f b - f a)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hs := mul_sub_le_image_sub_of_le_deriv hf h hba
    linarith [le_abs_self (f a - f b)]

private theorem scale_for_error {k : ℕ} {p c bound D : ℝ}
    (hp : (k : ℝ) < p) (hc : 0 < c) (hb : 0 < bound) (_hD : 0 ≤ D) :
    ∃ ε ∈ Ioo 0 bound, D * (2 * ε) ^ p ≤ c * ε ^ k := by
  have hpow : Tendsto (fun x : ℝ => x ^ (p - k)) (𝓝[>] 0) (𝓝 0) := by
    have hh := (Real.continuousAt_rpow_const 0 (p - k) (Or.inr (sub_nonneg.mpr hp.le))).tendsto
    rw [Real.zero_rpow (sub_pos.mpr hp).ne'] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have hh : Tendsto (fun x : ℝ => (D * (2 : ℝ) ^ p) * x ^ (p - k)) (𝓝[>] 0)
      (𝓝 0) := by simpa only [mul_zero] using tendsto_const_nhds.mul hpow
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 bound ∧
      (D * (2 : ℝ) ^ p) * ε ^ (p - k) < c := by
    filter_upwards [self_mem_nhdsWithin, (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
      (gt_mem_nhds hb), hh.eventually (gt_mem_nhds hc)] with x hx₀ hx₁ hx₂
    exact ⟨⟨hx₀, hx₁⟩, hx₂⟩
  obtain ⟨ε, hε, hsmall⟩ := hev.exists
  refine ⟨ε, hε, ?_⟩
  calc
    D * (2 * ε) ^ p = ((D * (2 : ℝ) ^ p) * ε ^ (p - k)) * ε ^ k := by
      rw [Real.mul_rpow (by norm_num) hε.1.le, ← Real.rpow_natCast,
        mul_assoc, mul_assoc, ← Real.rpow_add hε.1]
      congr 3
      ring
    _ ≤ c * ε ^ k := mul_le_mul_of_nonneg_right hsmall.le (pow_nonneg hε.1.le _)






private theorem restrict_deriv (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    deriv (fun t : ℝ => (F t).re) = fun t : ℝ => (deriv F t).re := by
  funext t
  have h := (Complex.reCLM.hasFDerivAt (x := F t)).comp t
    (((hF t).hasDerivAt.hasFDerivAt.restrictScalars ℝ).comp t
      (Complex.ofRealCLM.hasFDerivAt (x := t)))
  simpa [Function.comp_def] using h.hasDerivAt.deriv

private theorem restrict_iteratedDeriv (F : ℂ → ℂ) (hF : Differentiable ℂ F) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => (F t).re) = fun t : ℝ => (iteratedDeriv k F t).re := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact restrict_deriv _ ((hF.contDiff : ContDiff ℂ ⊤ F).differentiable_iteratedDeriv k (by simp))

private theorem tendsto_iteratedDeriv_on {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (h : TendstoLocallyUniformlyOn F G atTop U)
    (hF : ∀ s, Differentiable ℂ (F s)) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun s => iteratedDeriv k (F s)) (iteratedDeriv k G) atTop U := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    apply ih.deriv _ hU
    exact Eventually.of_forall fun s =>
      (((hF s).contDiff : ContDiff ℂ ⊤ (F s)).differentiable_iteratedDeriv k (by simp)).differentiableOn

private theorem all_derivatives_converge {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn F G atTop Set.univ)
    (hF : ∀ s, Differentiable ℂ (F s)) (k : ℕ) (t : ℝ) :
    Tendsto (fun s => iteratedDeriv k (fun a : ℝ => (F s a).re) t) atTop
      (𝓝 (iteratedDeriv k (fun a : ℝ => (G a).re) t)) := by
  have hG : Differentiable ℂ G := differentiableOn_univ.mp
    (h.differentiableOn (Eventually.of_forall fun s => (hF s).differentiableOn) isOpen_univ)
  simp only [restrict_iteratedDeriv _ (hF _) _, restrict_iteratedDeriv _ hG]
  exact (Complex.continuous_re.tendsto _).comp
    ((tendsto_iteratedDeriv_on isOpen_univ h hF k).tendsto_at (mem_univ (t : ℂ)))


private theorem geometric_budget {b : ℕ → ℝ} (_hb : ∀ j, 0 ≤ b j)
    (hstep : ∀ j, b (j + 1) ≤ b j / 2) (i j : ℕ) :
    b (i + j) ≤ b i * (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc]
    exact (hstep (i + j)).trans (by linarith)

set_option maxHeartbeats 800000 in
private theorem geometric_distance {α : Type*} [PseudoMetricSpace α] {f : ℕ → α}
    {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (hstep : ∀ j, b (j + 1) ≤ b j / 2)
    {i : ℕ} (h : ∀ j ≥ i, dist (f j) (f (j + 1)) ≤ b j) {g : α}
    (hg : Tendsto f atTop (𝓝 g)) : dist (f i) g ≤ 2 * b i := by
  have hshift : Tendsto (fun j => f (i + j)) atTop (𝓝 g) :=
    by simpa only [Nat.add_comm i] using (tendsto_add_atTop_iff_nat i).2 hg
  have hdist (j : ℕ) : dist (f (i + j)) (f (i + (j + 1))) ≤ b i * (1 / 2 : ℝ) ^ j :=
    (h (i + j) (Nat.le_add_right i j)).trans (geometric_budget hb hstep i j)
  have hh := dist_le_of_le_geometric_of_tendsto₀ (1 / 2 : ℝ) (b i) (by norm_num) hdist hshift
  rw [Nat.add_zero, show b i / (1 - 1 / 2) = 2 * b i by ring] at hh
  exact hh

private theorem entire_limit {F : ℕ → ℂ → ℂ} {b : ℕ → ℝ}
    (hb : ∀ j, 0 ≤ b j) (hstep : ∀ j, b (j + 1) ≤ b j / 2)
    (hF : ∀ j, Differentiable ℂ (F j))
    (hdisk : ∀ (j : ℕ) (z : ℂ), ‖z‖ ≤ (j : ℝ) + 2 → dist (F j z) (F (j + 1) z) ≤ b j) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ TendstoLocallyUniformlyOn F G atTop univ := by
  classical
  have hx (z : ℂ) : ∃ w, Tendsto (fun j => F j z) atTop (𝓝 w) := by
    obtain ⟨i, hi⟩ := exists_nat_ge ‖z‖
    have hdist (j : ℕ) : dist (F (i + j) z) (F (i + (j + 1)) z) ≤
        b i * (1 / 2 : ℝ) ^ j := by
      apply le_trans (hdisk (i + j) z _) (geometric_budget hb hstep i j)
      push_cast
      linarith [show (0 : ℝ) ≤ (j : ℝ) by positivity]
    have hc := cauchySeq_of_le_geometric (1 / 2 : ℝ) (b i) (by norm_num) hdist
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨w, (tendsto_add_atTop_iff_nat i).mp (by simpa only [Nat.add_comm i] using hw)⟩
  choose G hG using hx
  have hlim : TendstoLocallyUniformlyOn F G atTop univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨i, hi⟩ := exists_nat_ge R
    have hb0 : Tendsto b atTop (𝓝 0) := by
      have hp : Tendsto (fun j : ℕ => b 0 * (1 / 2 : ℝ) ^ j) atTop (𝓝 (b 0 * 0)) :=
        tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      rw [mul_zero] at hp
      exact squeeze_zero hb (fun j => by simpa using geometric_budget hb hstep 0 j) hp
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hsmall := (tendsto_const_nhds.mul hb0 : Tendsto (fun j => 2 * b j) atTop (𝓝 (2 * 0))).eventually
      (gt_mem_nhds (by simpa using hε))
    filter_upwards [eventually_ge_atTop i, hsmall] with j hj hs z hz
    rw [dist_comm]
    apply lt_of_le_of_lt (geometric_distance hb hstep (i := j) (f := fun k => F k z) _ (hG z)) hs
    intro k hk
    apply hdisk
    have hki : (i : ℝ) ≤ k := by exact_mod_cast hj.trans hk
    linarith [hR z hz]
  exact ⟨G, differentiableOn_univ.mp (hlim.differentiableOn
    (Eventually.of_forall fun j => (hF j).differentiableOn) isOpen_univ), hlim⟩





private def realGaussian (P : ℝ[X]) (t : ℝ) : ℝ := Real.exp (-t ^ 2) * P.eval t

private def complexGaussian (P : ℝ[X]) (z : ℂ) : ℂ :=
  Complex.exp (-z ^ 2) * P.eval₂ Complex.ofRealHom z

private theorem analytic_complexGaussian (P : ℝ[X]) (z : ℂ) :
    AnalyticAt ℂ (complexGaussian P) z := by
  unfold complexGaussian
  have hp : AnalyticAt ℂ (fun z : ℂ => (P.map Complex.ofRealHom).eval z) z :=
    (show Differentiable ℂ (fun z : ℂ => (P.map Complex.ofRealHom).eval z) from
      fun z => ((P.map Complex.ofRealHom).hasDerivAt z).differentiableAt).analyticAt z
  simp only [eval_map] at hp
  exact (show AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z ^ 2)) z by fun_prop).mul hp

private theorem complexGaussian_ofReal (P : ℝ[X]) (t : ℝ) :
    complexGaussian P t = (realGaussian P t : ℂ) := by
  have hp := P.eval₂_at_apply Complex.ofRealHom t
  simpa [realGaussian, complexGaussian] using hp

private theorem realGaussian_hasDerivAt (P : ℝ[X]) (t : ℝ) :
    HasDerivAt (realGaussian P) (realGaussian (P.derivative - C 2 * X * P) t) t := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-t ^ 2)) (Real.exp (-t ^ 2) * (-(2 * t))) t := by
    convert (((hasDerivAt_id t).pow 2).neg.exp) using 1 <;> simp
  have hEq : realGaussian (P.derivative - C 2 * X * P) t =
      Real.exp (-t ^ 2) * (-(2 * t)) * P.eval t + Real.exp (-t ^ 2) * P.derivative.eval t := by
    simp [realGaussian]
    ring
  rw [hEq]
  exact he.mul (P.hasDerivAt t)

private theorem gaussian_monomial_bound (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, Real.exp (-t ^ 2) * |t| ^ k ≤ A := by
  have ht : Tendsto (fun t : ℝ => Real.exp (-t ^ 2) * |t| ^ k) (cocompact ℝ) (𝓝 0) := by
    simpa [Real.rpow_natCast, mul_comm] using
      (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact one_pos (k : ℝ))
  obtain ⟨K, hK, hsub⟩ := mem_cocompact.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  have hc : Continuous (fun t : ℝ => Real.exp (-t ^ 2) * |t| ^ k) := by fun_prop
  obtain ⟨B, hB⟩ := (hK.image hc).isBounded.exists_norm_le
  refine ⟨max 1 B, le_max_left _ _ |>.trans' zero_le_one, ?_⟩
  intro t
  by_cases h : t ∈ K
  · exact (le_abs_self _).trans ((hB _ ⟨t, h, rfl⟩).trans (le_max_right _ _))
  · exact (hsub h).le.trans (le_max_left _ _)

private theorem gaussian_weighted_bound (P : ℝ[X]) (k : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, |realGaussian P t| * (max 1 |t|) ^ k ≤ A := by
  classical
  choose A hA hbound using gaussian_monomial_bound
  refine ⟨∑ j ∈ P.support, |P.coeff j| * (A j + A (j + k)),
    sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (add_nonneg (hA _) (hA _))), ?_⟩
  intro t
  rw [realGaussian, abs_mul, abs_of_pos (Real.exp_pos _), eval_eq_sum, Polynomial.sum]
  calc
    _ ≤ Real.exp (-t ^ 2) * (∑ j ∈ P.support, |P.coeff j * t ^ j|) * max 1 |t| ^ k :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _)
        (Real.exp_nonneg _)) (by positivity)
    _ ≤ _ := by
      simp only [mul_sum, sum_mul, abs_mul, abs_pow]
      apply sum_le_sum
      intro j hj
      have hb : Real.exp (-t ^ 2) * |t| ^ j * max 1 |t| ^ k ≤ A j + A (j + k) := by
        rcases le_total |t| 1 with ht | ht
        · rw [max_eq_left ht, one_pow, mul_one]
          linarith [hbound j t, hA (j + k)]
        · rw [max_eq_right ht, mul_assoc, ← pow_add]
          linarith [hbound (j + k) t, hA j]
      calc
        _ = |P.coeff j| * (Real.exp (-t ^ 2) * |t| ^ j * max 1 |t| ^ k) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)






private def shape {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}
    (u : Fin (n + 1) → 𝕜) (x ε t : 𝕜) : 𝕜 :=
  ε * u 0 + ∑ i : Fin n, u i.succ * (t - x) ^ (i.val + 1)

private def shapeSlope {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}
    (u : Fin (n + 1) → 𝕜) (x t : 𝕜) : 𝕜 :=
  ∑ i : Fin n, u i.succ * ((i.val + 1 : ℕ) : 𝕜) * (t - x) ^ i.val

private theorem shape_hasDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}
    (u : Fin (n + 1) → 𝕜) (x ε t : 𝕜) :
    HasDerivAt (shape u x ε) (shapeSlope u x t) t := by
  unfold shapeSlope
  apply HasDerivAt.const_add
  apply HasDerivAt.fun_sum
  intro i _
  simpa [mul_assoc] using ((((hasDerivAt_id t).sub_const x).pow (i.val + 1)).const_mul (u i.succ))

private theorem shape_shift_pow {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x t : 𝕜}
    {X : ℝ} (hX : 0 ≤ X) (hx : ‖x‖ ≤ X) {j n : ℕ} (hj : j ≤ n) :
    ‖t - x‖ ^ j ≤ (1 + X) ^ n * (max 1 ‖t‖) ^ n := by
  let U := max 1 ‖t‖
  have hU : 1 ≤ U := le_max_left _ _
  have hnorm : ‖t - x‖ ≤ (1 + X) * U := by
    have hXU := mul_le_mul_of_nonneg_left hU hX
    have htU : ‖t‖ ≤ U := le_max_right _ _
    linarith [norm_sub_le t x]
  have hbase : 1 ≤ (1 + X) * U := by nlinarith
  rw [← mul_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm _).trans (pow_le_pow_right₀ hbase hj)

private theorem shape_bound {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}
    {u : Fin (n + 1) → 𝕜} (hu : ∀ i, ‖u i‖ ≤ 1)
    {x ε t : 𝕜} {X : ℝ} (hX : 0 ≤ X) (hx : ‖x‖ ≤ X) (he : ‖ε‖ ≤ 1) :
    ‖shape u x ε t‖ ≤ (n + 1 : ℝ) * (1 + X) ^ n * (max 1 ‖t‖) ^ n := by
  let B := (1 + X) ^ n * (max 1 ‖t‖) ^ n
  have hB : 1 ≤ B := by simpa [B] using shape_shift_pow hX hx (t := t) (Nat.zero_le n)
  have hterm (i : Fin n) : ‖u i.succ * (t - x) ^ (i.val + 1)‖ ≤ B := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (hu i.succ) (by positivity)).trans
      (by simpa using shape_shift_pow hX hx (t := t) i.isLt)
  have h0 : ‖ε * u 0‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ he (norm_nonneg _) (hu 0)
  calc
    _ ≤ ‖ε * u 0‖ + ∑ i : Fin n, ‖u i.succ * (t - x) ^ (i.val + 1)‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ B + ∑ _ : Fin n, B := add_le_add (h0.trans hB) (sum_le_sum fun i _ => hterm i)
    _ = _ := by simp [B]; ring

private theorem shapeSlope_bound {n : ℕ} {u : Fin (n + 1) → ℝ}
    (hu : ∀ i, |u i| ≤ 1) {x t X : ℝ} (hX : 0 ≤ X) (hx : |x| ≤ X) :
    |shapeSlope u x t| ≤ (n + 1 : ℝ) ^ 2 * (1 + X) ^ n * (max 1 |t|) ^ n := by
  let B := (1 + X) ^ n * (max 1 |t|) ^ n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (i : Fin n) : |u i.succ * ((i.val + 1 : ℕ) : ℝ) * (t - x) ^ i.val| ≤ n * B := by
    simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (i.val + 1)), abs_pow]
    have hj : ((i.val + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast i.isLt
    have hp : |t - x| ^ i.val ≤ B :=
      shape_shift_pow hX hx (t := t) (Nat.le_of_lt i.isLt)
    apply mul_le_mul _ hp (by positivity) (by positivity)
    simpa using mul_le_mul (hu i.succ) hj (by positivity) zero_le_one
  calc
    _ ≤ ∑ i : Fin n, |u i.succ * ((i.val + 1 : ℕ) : ℝ) * (t - x) ^ i.val| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n, (n : ℝ) * B := sum_le_sum fun i _ => hterm i
    _ = (n : ℝ) ^ 2 * B := by simp; ring
    _ ≤ _ := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) 2) hB




open OMA.S_wp_kung_traub_conjecture (Method answer HasOrderAtLeast)

/-- A scaled Gaussian multiplier gives uniform bounds on the real axis and the designated disk. -/
private theorem small_gaussian_multiplier (n : ℕ) (P : ℝ[X]) {T R b : ℝ}
    (hX : 0 ≤ T) (hb : 0 < b) : ∃ lam : ℝ, 0 < lam ∧
    (∀ t : ℝ, |lam * realGaussian P t| ≤ b) ∧
    ∀ (x ε : ℝ) (u : CoeffSpace ℝ n), |x| ≤ T → |ε| ≤ 1 → ‖u‖ ≤ 1 →
      (∀ t : ℝ, |perturb (fun z => lam * realGaussian P z) x ε u t| ≤ b ∧
        |deriv (perturb (fun z => lam * realGaussian P z) x ε u) t| ≤ b) ∧
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖((lam : ℂ) * complexGaussian P z) *
          shape (fun i => (u i : ℂ)) x ε z‖ ≤ b := by
  obtain ⟨A, hA, ha⟩ := gaussian_weighted_bound P n
  obtain ⟨D, hD, hd⟩ := gaussian_weighted_bound (P.derivative - C 2 * Polynomial.X * P) n
  have hc : Continuous (complexGaussian P) :=
    continuous_iff_continuousAt.mpr fun z => (analytic_complexGaussian P z).continuousAt
  obtain ⟨C₀, hC₀⟩ := ((isCompact_closedBall (0 : ℂ) R).image hc).isBounded.exists_norm_le
  let C' := max C₀ 0
  have hC (z : ℂ) (hz : ‖z‖ ≤ R) : ‖complexGaussian P z‖ ≤ C' :=
    (hC₀ _ ⟨z, by simpa [Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩).trans (le_max_left _ _)
  let L := ((n : ℝ) + 1) ^ 2 * (1 + T) ^ n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn)
    (one_le_pow₀ (by linarith))
  have hL' : ((n : ℝ) + 1) * (1 + T) ^ n ≤ L := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ (n : ℝ) + 1 by positivity)]
  let V := max 1 R ^ n
  let K := 1 + (A + D) * L + C' * (L * V)
  have hK : 0 < K := by dsimp [K, C', V]; positivity
  let lam := b / K
  have hlam : 0 < lam := div_pos hb hK
  have hscale {q : ℝ} (hq : q ≤ K) : lam * q ≤ b := by
    calc
      lam * q ≤ lam * K := mul_le_mul_of_nonneg_left hq hlam.le
      _ = b := div_mul_cancel₀ b hK.ne'
  have hC' : 0 ≤ C' := le_max_right _ _
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hADK : (A + D) * L ≤ K := by dsimp [K]; nlinarith [mul_nonneg hC' (mul_nonneg (by linarith : 0 ≤ L) hV)]
  have hAK : A ≤ K := by
    have hAL : A ≤ A * L := by nlinarith
    exact hAL.trans ((mul_le_mul_of_nonneg_right (by linarith) (by linarith : 0 ≤ L)).trans hADK)
  refine ⟨lam, hlam, fun t => ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hlam]
    apply hscale
    have hh := one_le_pow₀ (n := n) (le_max_left (1 : ℝ) |t|)
    exact (le_trans (by nlinarith [abs_nonneg (realGaussian P t)]) (ha t)).trans hAK
  intro x ε u hx he hu
  have hui (i : Fin (n + 1)) : |u i| ≤ 1 := (PiLp.norm_apply_le u i).trans hu
  have hmul (t a S : ℝ) (ht : |a| * max 1 |t| ^ n ≤ S) {v : ℝ}
      (hv : |v| ≤ L * max 1 |t| ^ n) : |a| * |v| ≤ S * L := by
    calc
      _ ≤ |a| * (L * max 1 |t| ^ n) := mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = (|a| * max 1 |t| ^ n) * L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ht (by linarith)
  refine ⟨fun t => ?_, fun z hz => ?_⟩
  · have hs : |shape u x ε t| ≤ L * max 1 |t| ^ n :=
      (by simpa only [Real.norm_eq_abs] using
        (shape_bound (u := u) (t := t) hui hX hx he) :
          |shape u x ε t| ≤ ((n : ℝ) + 1) * (1 + T) ^ n * max 1 |t| ^ n).trans
        (mul_le_mul_of_nonneg_right hL' (by positivity))
    have hSlope : |shapeSlope u x t| ≤ L * max 1 |t| ^ n := shapeSlope_bound hui hX hx
    have hDeriv : deriv (fun t => lam * (realGaussian P t * shape u x ε t)) t =
        lam * (realGaussian (P.derivative - C 2 * Polynomial.X * P) t * shape u x ε t +
          realGaussian P t * shapeSlope u x t) :=
      (((realGaussian_hasDerivAt P t).mul (shape_hasDerivAt u x ε t)).const_mul lam).deriv
    have hfun : perturb (fun z => lam * realGaussian P z) x ε u =
        fun t => lam * (realGaussian P t * shape u x ε t) := by
      funext t
      exact mul_assoc _ _ _
    rw [hfun, hDeriv]
    constructor
    · rw [abs_mul, abs_of_pos hlam, abs_mul]
      exact hscale ((hmul _ _ _ (ha t) hs).trans ((mul_le_mul_of_nonneg_right (by linarith)
        (by linarith : 0 ≤ L)).trans hADK))
    · rw [abs_mul, abs_of_pos hlam]
      apply hscale
      refine (abs_add_le _ _).trans ?_
      simp only [abs_mul]
      linarith [hmul _ _ _ (hd t) hs, hmul _ _ _ (ha t) hSlope]
  · have hshape : ‖shape (fun i => (u i : ℂ)) x ε z‖ ≤ L * V := by
      have hh := shape_bound (t := z) (X := T) (u := fun i => (u i : ℂ))
        (fun i => by simpa [Complex.norm_real] using hui i) hX
        (by simpa [Complex.norm_real] using hx : ‖(x : ℂ)‖ ≤ T)
        (by simpa [Complex.norm_real] using he : ‖(ε : ℂ)‖ ≤ 1)
      exact hh.trans (mul_le_mul hL' (pow_le_pow_left₀ (by positivity) (max_le_max_left 1 hz) _)
        (by positivity) (by linarith))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam, mul_assoc]
    refine hscale ((mul_le_mul (hC z hz) hshape (norm_nonneg _) hC').trans ?_)
    dsimp [K]
    linarith [mul_nonneg (add_nonneg hA hD) (show 0 ≤ L by linarith)]


private def onReal (F : ℂ → ℂ) (t : ℝ) : ℝ := (F t).re

private theorem onReal_analytic {F : ℂ → ℂ} (hF : Differentiable ℂ F) (t : ℝ) :
    AnalyticAt ℝ (onReal F) t :=
  (hF.analyticAt _).re_ofReal

private theorem analytic_realGaussian (P : ℝ[X]) (t : ℝ) :
    AnalyticAt ℝ (realGaussian P) t := by
  have h : onReal (complexGaussian P) = realGaussian P := by
    funext s
    rw [onReal, complexGaussian_ofReal, Complex.ofReal_re]
  rw [← h]
  exact (analytic_complexGaussian P t).re_ofReal

private theorem smooth_of_analytic {f : ℝ → ℝ} (hf : ∀ t, AnalyticAt ℝ f t) :
    ContDiff ℝ ⊤ f :=
  contDiff_iff_contDiffAt.mpr fun t => (hf t).contDiffAt

private theorem perturb_analytic {n : ℕ} {w : ℝ → ℝ} (hw : ∀ t, AnalyticAt ℝ w t)
    (x ε : ℝ) (u : CoeffSpace ℝ n) (t : ℝ) :
    AnalyticAt ℝ (perturb w x ε u) t := by
  have hshape : AnalyticAt ℝ (shape u x ε) t := by unfold shape; fun_prop
  exact (hw t).mul hshape

private theorem real_correction {n : ℕ} {F : ℂ → ℂ} (P : ℝ[X])
    (lam x ε : ℝ) (u : CoeffSpace ℝ n) :
    onReal (fun z => F z + ((lam : ℂ) * complexGaussian P z) *
      shape (fun i => (u i : ℂ)) x ε z) =
      familyFn (onReal F) (fun t => lam * realGaussian P t) x ε u := by
  funext t
  have hs : shape (fun i => (u i : ℂ)) (x : ℂ) (ε : ℂ) (t : ℂ) = ((shape u x ε t : ℝ) : ℂ) := by
    simp [shape]
  rw [onReal, complexGaussian_ofReal, hs]
  simp only [Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

private theorem family_iteratedDeriv {n : ℕ} {f w : ℝ → ℝ}
    (hf : ∀ t, AnalyticAt ℝ f t) (hw : ∀ t, AnalyticAt ℝ w t)
    (x ε : ℝ) (u : CoeffSpace ℝ n) (ν : ℕ) (t : ℝ) :
    iteratedDeriv ν (familyFn f w x ε u) t =
      iteratedDeriv ν f t + ∑ i : Fin (n + 1), u i * iteratedDeriv ν (vVec w x ε i) t := by
  have hv (i : Fin (n + 1)) : ∀ t, AnalyticAt ℝ (vVec w x ε i) t := by
    intro t
    refine Fin.cases ?_ (fun j => ?_) i
    · have hh : vVec (n := n) w x ε 0 = fun s => w s * ε := by funext s; simp [vVec]
      rw [hh]
      exact (hw t).mul analyticAt_const
    · have hh : vVec w x ε j.succ = fun s => w s * (s - x) ^ (j.val + 1) := by
        funext s
        simp [vVec]
      rw [hh]
      exact (hw t).mul (show AnalyticAt ℝ (fun t => (t - x) ^ (j.val + 1)) t by fun_prop)
  have heq : perturb w x ε u = fun t => ∑ i : Fin (n + 1), u i * vVec w x ε i t := by
    funext t
    rw [Fin.sum_univ_succ, perturb]
    simp only [vVec, Fin.cases_zero, Fin.cases_succ, mul_add, mul_sum]
    congr 1
    · ring
    · apply sum_congr rfl
      intro i _
      ring
  have hterm (i : Fin (n + 1)) : ContDiffAt ℝ ν (fun s => u i * vVec w x ε i s) t :=
    (analyticAt_const.mul (hv i t)).contDiffAt
  change iteratedDeriv ν (f + perturb w x ε u) t = _
  rw [iteratedDeriv_add ((smooth_of_analytic hf).contDiffAt.of_le (by simp))
    ((smooth_of_analytic (perturb_analytic hw x ε u)).contDiffAt.of_le (by simp)), heq,
    iteratedDeriv_fun_sum (fun i _ => hterm i)]
  congr 1
  apply sum_congr rfl
  intro i _
  exact iteratedDeriv_const_mul (u i) ((hv i t).contDiffAt)
 
private theorem root_motion_at_scale {n : ℕ} {f w : ℝ → ℝ} {a ε b : ℝ}
    (ha : f a = 0) (he : 0 < ε) (he₁ : ε ≤ 1)
    (hw : |w a| ≤ b) (hb : b ≤ 1 / (16 * ((n : ℝ) + 1))) (u : CoeffSpace ℝ n)
    (hu : ‖u‖ ≤ 1) {r : ℝ} (hr : familyFn f w (a + ε) ε u r = 0)
    (hd : Differentiable ℝ (familyFn f w (a + ε) ε u))
    (hm : ∀ t, 1 / 2 ≤ deriv (familyFn f w (a + ε) ε u) t) :
    |r - a| ≤ ε / 8 := by
  have hcoef (i : Fin (n + 1)) : |u i| ≤ 1 := (PiLp.norm_apply_le u i).trans hu
  have hpow (i : Fin n) : ε ^ (i.val + 1) ≤ ε := by
    rw [pow_succ']
    exact mul_le_of_le_one_right he.le (pow_le_one₀ he.le he₁)
  have hsum : |ε * u 0 + ∑ i : Fin n, u i.succ * (a - (a + ε)) ^ (i.val + 1)| ≤
      ((n : ℝ) + 1) * ε := by
    have hterm (i : Fin n) : |u i.succ * (a - (a + ε)) ^ (i.val + 1)| ≤ ε := by
      rw [abs_mul, abs_pow, show a - (a + ε) = -ε by ring, abs_neg, abs_of_pos he]
      exact (mul_le_of_le_one_left (by positivity) (hcoef _)).trans (hpow i)
    calc
      _ ≤ |ε * u 0| + (∑ i : Fin n, |u i.succ * (a - (a + ε)) ^ (i.val + 1)|) :=
        (abs_add_le _ _).trans (add_le_add_right (abs_sum_le_sum_abs _ _) _)
      _ ≤ ε + ∑ _ : Fin n, ε := add_le_add
        (by rw [abs_mul, abs_of_pos he]; exact mul_le_of_le_one_right he.le (hcoef _))
        (sum_le_sum fun i _ => hterm i)
      _ = _ := by simp; ring
  have h := secant_abs_lower hd hm r a
  rw [hr, zero_sub, abs_neg, familyFn, ha, zero_add, perturb, abs_mul] at h
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hw
  have h₁ := mul_le_mul hw hsum (abs_nonneg _) hb0
  have h₂ : b * ((n : ℝ) + 1) ≤ 1 / 16 := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hg := mul_le_mul_of_nonneg_right hb hn.le
    calc
      _ ≤ (1 / (16 * ((n : ℝ) + 1))) * ((n : ℝ) + 1) := hg
      _ = _ := by field_simp
  have h₃ := mul_le_mul_of_nonneg_right h₂ he.le
  nlinarith


private def jetPolynomial (J : Finset (ℝ × ℕ)) : ℝ[X] :=
  ∏ q ∈ J, (Polynomial.X - C q.1) ^ (q.2 + 1)

private theorem jetPolynomial_ne_zero_at {J : Finset (ℝ × ℕ)} {a : ℝ}
    (ha : ∀ q ∈ J, q.1 ≠ a) : (jetPolynomial J).eval a ≠ 0 := by
  simp only [jetPolynomial, eval_prod, eval_pow, eval_sub, eval_X, eval_C]
  exact Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (sub_ne_zero.mpr (ha q hq).symm)

private theorem correction_jet_zero {n : ℕ} {J : Finset (ℝ × ℕ)} {a : ℝ} {ν : ℕ}
    (hj : (a, ν) ∈ J) (lam x ε : ℝ) (u : CoeffSpace ℝ n) :
    iteratedDeriv ν (perturb (fun t => lam * realGaussian (jetPolynomial J) t) x ε u) a = 0 := by
  classical
  let g := perturb (fun t => lam * realGaussian (jetPolynomial (J.erase (a, ν))) t) x ε u
  have hg (t : ℝ) : AnalyticAt ℝ g t :=
    perturb_analytic (fun z => analyticAt_const.mul (analytic_realGaussian _ z)) _ _ _ _
  have heq (t : ℝ) : perturb (fun s => lam * realGaussian (jetPolynomial J) s) x ε u t =
      (t - a) ^ (ν + 1) * g t := by
    have hp : jetPolynomial J = (Polynomial.X - C a) ^ (ν + 1) *
        jetPolynomial (J.erase (a, ν)) := by
      unfold jetPolynomial
      exact (mul_prod_erase _ _ hj).symm
    simp only [perturb, realGaussian, hp, eval_mul, eval_pow, eval_sub, eval_X, eval_C, g]
    ring
  obtain ⟨H, _, hH⟩ := iteratedDeriv_mul_pow_sub_of_analytic (t := 1) hg heq
  rw [hH]
  simp

private def observedJets {n : ℕ} (M : Method n) (f : ℝ → ℝ) (x : ℝ) : Finset (ℝ × ℕ) :=
  Finset.univ.biUnion fun i : Fin n => (M.query i x (M.answers f x i.val i.isLt.le)).toFinset

private theorem mem_observedJets {n : ℕ} {M : Method n} {f : ℝ → ℝ} {x : ℝ} {q : ℝ × ℕ} :
    q ∈ observedJets M f x ↔
      ∃ i : Fin n, M.query i x (M.answers f x i.val i.isLt.le) = some q := by
  classical
  simp [observedJets, Option.mem_def, eq_comm]

private theorem same_output {n : ℕ} (M : Method n) {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ q ∈ observedJets M f x, iteratedDeriv q.2 f q.1 = iteratedDeriv q.2 g q.1) :
    M.step f x = M.step g x := by
  have ha (j : ℕ) (hj : j ≤ n) : M.answers f x j hj = M.answers g x j hj := by
    induction j with
    | zero => exact Subsingleton.elim _ _
    | succ j ih =>
      have hj' : j < n := hj
      have hprev := ih hj'.le
      simp only [Method.answers]
      rw [← hprev]
      congr 1
      generalize hq : M.query ⟨j, hj'⟩ x (M.answers f x j hj'.le) = q
      cases q with
      | none => rfl
      | some p =>
        exact h p (mem_observedJets.mpr ⟨⟨j, hj'⟩, hq⟩)
  exact congrArg (M.output x) (ha n le_rfl)


private structure CounterexampleStage (n : ℕ) where
  F : ℂ → ℂ
  root : ℝ
  budget : ℝ
  jets : Finset (ℝ × ℕ)
  entire : Differentiable ℂ F
  atRoot : onReal F root = 0
  budget_pos : 0 < budget
  budget_small : budget ≤ 1 / (16 * ((n : ℝ) + 1))
  slope : ∀ t, 1 / 2 + 2 * budget ≤ deriv (onReal F) t ∧
    deriv (onReal F) t ≤ 3 / 2 - 2 * budget
  avoids : ∀ q ∈ jets, q.1 ≠ root

private def initialStage (n : ℕ) : CounterexampleStage n where
  F := id
  root := 0
  budget := min (1 / 8) (1 / (16 * ((n : ℝ) + 1)))
  jets := ∅
  entire := differentiable_id
  atRoot := by simp [onReal]
  budget_pos := by positivity
  budget_small := min_le_right _ _
  slope := by
    intro t
    have h := min_le_left (1 / 8 : ℝ) (1 / (16 * ((n : ℝ) + 1)))
    have h' : deriv (onReal id) t = 1 := by
      change deriv (fun a : ℝ => a) t = 1
      simp
    rw [h']
    constructor <;> linarith
  avoids := by simp

private structure StageLink {n : ℕ} (M : Method n) (p : ℝ) (s : ℕ)
    (old new : CounterexampleStage n) (x ε : ℝ) : Prop where
  budget_half : new.budget ≤ old.budget / 2
  real_bound : ∀ t, |onReal old.F t - onReal new.F t| ≤ old.budget
  disk_bound : ∀ z : ℂ, ‖z‖ ≤ (s : ℝ) + 2 → dist (old.F z) (new.F z) ≤ old.budget
  jets_subset : old.jets ⊆ new.jets
  keeps_jets : ∀ q ∈ old.jets, iteratedDeriv q.2 (onReal old.F) q.1 =
    iteratedDeriv q.2 (onReal new.F) q.1
  observed : observedJets M (onReal new.F) x ⊆ new.jets
  scale : 0 < ε ∧ ε < 1 / ((s : ℝ) + 1)
  offsets : 7 * ε / 8 ≤ x - new.root ∧ x - new.root ≤ 9 * ε / 8
  error : 2 * ((s : ℝ) + 1) * (2 * ε) ^ p ≤ |M.step (onReal new.F) x - new.root|
  budget_error : new.budget ≤ |M.step (onReal new.F) x - new.root| / 16
  budget_scale : new.budget ≤ ε / 16

set_option maxHeartbeats 1200000 in
private theorem next_stage {n : ℕ} (hn : 1 ≤ n) (M : Method n) {p : ℝ}
    (hp : (B n : ℝ) < p) (s : ℕ) (old : CounterexampleStage n) :
    ∃ new x ε, StageLink M p s old new x ε := by
  classical
  let a := old.root
  let f := onReal old.F
  let P := jetPolynomial old.jets
  let T := |a| + 1
  obtain ⟨lam, hlam, hwle, hsmall⟩ := small_gaussian_multiplier n P
    (R := (s : ℝ) + 2) (by dsimp [T]; positivity : 0 ≤ T) old.budget_pos
  let w (t : ℝ) := lam * realGaussian P t
  have hw (t : ℝ) : AnalyticAt ℝ w t := analyticAt_const.mul (analytic_realGaussian P t)
  have hf (t : ℝ) : AnalyticAt ℝ f t := onReal_analytic old.entire t
  have hwa : w a ≠ 0 :=
    mul_ne_zero hlam.ne' (mul_ne_zero (Real.exp_pos _).ne' (jetPolynomial_ne_zero_at old.avoids))
  let wstar := |w a| / 2
  have hstar : 0 < wstar := by dsimp [wstar]; positivity
  have hnbr : ∀ᶠ t in 𝓝 a, wstar < |w t| :=
    ((hw a).continuousAt.abs.tendsto).eventually
      (lt_mem_nhds (show wstar < |w a| by dsimp [wstar]; linarith [abs_pos.mpr hwa]))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hnbr
  let init := min 1 r
  have hinit : 0 < init := lt_min zero_lt_one hr
  have hloc {ε : ℝ} (he : ε ∈ Ioo 0 init) : |a + ε| ≤ T ∧ |ε| ≤ 1 := by
    have he1 : ε ≤ 1 := he.2.le.trans (min_le_left _ _)
    rw [abs_of_pos he.1]
    exact ⟨(abs_add_le _ _).trans (by rw [abs_of_pos he.1]; dsimp [T]; linarith), he1⟩
  have hg {ε : ℝ} (he : ε ∈ Ioo 0 init) (u : CoeffSpace ℝ n) (hu : ‖u‖ ≤ 1) (t : ℝ) :
      deriv (familyFn f w (a + ε) ε u) t =
        deriv f t + deriv (perturb w (a + ε) ε u) t ∧
      |deriv (perturb w (a + ε) ε u) t| ≤ old.budget := by
    refine ⟨deriv_add (hf t).differentiableAt (perturb_analytic hw _ _ u t).differentiableAt, ?_⟩
    exact ((hsmall _ _ u (hloc he).1 (hloc he).2 hu).1 t).2
  have hdiff (ε : ℝ) (u : CoeffSpace ℝ n) : Differentiable ℝ (familyFn f w (a + ε) ε u) :=
    fun t => ((hf t).add (perturb_analytic hw _ _ u t)).differentiableAt
  have hderiv {ε : ℝ} (he : ε ∈ Ioo 0 init) (u : CoeffSpace ℝ n) (hu : ‖u‖ ≤ 1) (t : ℝ) :
      1 / 2 + old.budget ≤ deriv (familyFn f w (a + ε) ε u) t ∧
      deriv (familyFn f w (a + ε) ε u) t ≤ 3 / 2 - old.budget := by
    obtain ⟨h, hb⟩ := hg he u hu t
    have h₀ := old.slope t
    change 1 / 2 + 2 * old.budget ≤ deriv f t ∧ deriv f t ≤ 3 / 2 - 2 * old.budget at h₀
    obtain ⟨lo, hi⟩ := abs_le.mp hb
    constructor <;> linarith [h₀.1, h₀.2]
  have hroot (ε : ℝ) (u : CoeffSpace ℝ n) : ∃ t, ε ∈ Ioo 0 init → ‖u‖ ≤ 1 →
      familyFn f w (a + ε) ε u t = 0 := by
    by_cases H : ε ∈ Ioo 0 init ∧ ‖u‖ ≤ 1
    · obtain ⟨t, ht⟩ := root_exists (hdiff ε u) (fun t =>
        le_trans (by linarith [old.budget_pos]) (hderiv H.1 u H.2 t).1)
      exact ⟨t, fun _ _ => ht⟩
    · exact ⟨0, fun h₁ h₂ => (H ⟨h₁, h₂⟩).elim⟩
  choose root hroot using hroot
  have hmove {ε : ℝ} (he : ε ∈ Ioo 0 init) (u : CoeffSpace ℝ n) (hu : ‖u‖ ≤ 1) :
      |root ε u - a| ≤ ε / 8 :=
    root_motion_at_scale old.atRoot he.1 (he.2.le.trans (min_le_left _ _)) (hwle a)
      old.budget_small u hu (hroot ε u he hu) (hdiff ε u)
      (fun t => le_trans (by linarith [old.budget_pos]) (hderiv he u hu t).1)
  have hfamily (ε : ℝ) (he : ε ∈ Ioo 0 init) :
      FamilyHyp f w (a + ε) ε (1 / 2) (3 / 2) 2 wstar (root ε) := by
    refine ⟨fun u hu => hroot ε u he hu, ?_, ?_, ?_,
      fun u _ ν t => family_iteratedDeriv hf hw _ _ u ν t⟩
    · intro u hu t
      have hh := hderiv he u hu t
      exact ⟨hdiff ε u t, by linarith [hh.1, old.budget_pos], by linarith [hh.2, old.budget_pos]⟩
    · intro u hu
      have h := abs_sub_le (root ε u) a (a + ε)
      rw [show a - (a + ε) = -ε by ring, abs_neg, abs_of_pos he.1] at h
      linarith [hmove he u hu, he.1]
    · intro u hu
      apply (hball _ ?_).le
      rw [Metric.mem_ball, Real.dist_eq]
      have hεr := he.2.trans_le (min_le_right _ _)
      linarith [hmove he u hu, he.1]
  obtain ⟨c, hc, e₀, he₀, hfixed⟩ := fixed_scale_lower_bound hn (m := 1 / 2)
    (M := 3 / 2) (R := 2) (by norm_num) (by norm_num) (by norm_num) hstar hinit
  let D := 2 * ((s : ℝ) + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨ε, he, hratio⟩ := scale_for_error hp hc
    (lt_min he₀ (lt_min hinit (by positivity : 0 < 1 / ((s : ℝ) + 1)))) hD.le
  have he₀' : ε ∈ Ioo 0 e₀ := ⟨he.1, he.2.trans_le (min_le_left _ _)⟩
  have he' : ε ∈ Ioo 0 init := ⟨he.1, he.2.trans_le ((min_le_right _ _).trans (min_le_left _ _))⟩
  have heScale : ε < 1 / ((s : ℝ) + 1) :=
    he.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨u, hu, hval, hav⟩ := hfixed f w a root hfamily M ε he₀'
  let x := a + ε
  let F (z : ℂ) := old.F z + ((lam : ℂ) * complexGaussian P z) *
    shape (fun i => (u i : ℂ)) (x : ℂ) (ε : ℂ) z
  have hF : Differentiable ℂ F := by
    intro z
    exact (old.entire z).add ((analyticAt_const.mul (analytic_complexGaussian P z)).differentiableAt.mul
      (shape_hasDerivAt _ _ _ z).differentiableAt)
  have hReal : onReal F = familyFn f w x ε u := real_correction P lam x ε u
  let α := root ε u
  let E := |M.step (onReal F) x - α|
  have hval' : c * ε ^ B n ≤ E := by simpa only [E, hReal] using hval
  have hE : 0 < E := (mul_pos hc (pow_pos he.1 _)).trans_le hval'
  let b := min (old.budget / 2) (min (E / 16) (ε / 16))
  have hb : 0 < b := lt_min (by linarith [old.budget_pos])
    (lt_min (by linarith) (by linarith [he.1]))
  have hhalf : b ≤ old.budget / 2 := min_le_left _ _
  let J := observedJets M (onReal F) x
  have hkeep (q : ℝ × ℕ) (hq : q ∈ old.jets) :
      iteratedDeriv q.2 f q.1 = iteratedDeriv q.2 (onReal F) q.1 := by
    rw [hReal]
    change _ = iteratedDeriv q.2 (f + perturb w x ε u) q.1
    rw [iteratedDeriv_add ((smooth_of_analytic hf).contDiffAt.of_le (by simp))
      ((smooth_of_analytic (perturb_analytic hw x ε u)).contDiffAt.of_le (by simp)),
      correction_jet_zero hq lam x ε u, add_zero]
  have hzero : onReal F α = 0 := by rw [hReal]; exact hroot ε u he' hu
  have hold (q : ℝ × ℕ) (hq : q ∈ old.jets) : q.1 ≠ α := by
    intro hqα
    obtain ⟨z, ν⟩ := q
    have hz : perturb w x ε u z = 0 := by
      unfold perturb w realGaussian P jetPolynomial
      have hp : (∏ q ∈ old.jets, (Polynomial.X - C q.1) ^ (q.2 + 1)).eval z = 0 := by
        rw [eval_prod]
        apply Finset.prod_eq_zero hq
        simp
      rw [hp]
      ring
    have hfz : f z = 0 := by
      have h := hzero
      change z = α at hqα
      rw [← hqα, hReal, familyFn, hz, add_zero] at h
      exact h
    exact old.avoids (z, ν) hq
      ((strictMono_of_deriv_pos (fun t => by linarith [(old.slope t).1, old.budget_pos])).injective
        (hfz.trans old.atRoot.symm))
  let new : CounterexampleStage n := {
    F := F, root := α, budget := b, jets := old.jets ∪ J, entire := hF, atRoot := hzero,
    budget_pos := hb,
    budget_small := le_trans (hhalf.trans (by linarith [old.budget_pos])) old.budget_small,
    slope := fun t => by
      rw [hReal]
      have ht := hderiv he' u hu t
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩,
    avoids := fun q hq => by
      rcases Finset.mem_union.mp hq with holdq | hnewq
      · exact hold q holdq
      · obtain ⟨i, hi⟩ := mem_observedJets.mp hnewq
        exact hav i q.1 q.2 (by simpa only [hReal, Prod.eta] using hi) }
  refine ⟨new, x, ε, hhalf, ?_, ?_, Finset.subset_union_left, hkeep, Finset.subset_union_right,
    ⟨he.1, heScale⟩, ?_, hratio.trans hval', (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _)⟩
  · intro t
    change |f t - onReal F t| ≤ old.budget
    rw [hReal, familyFn, show f t - (f t + perturb w x ε u t) = -perturb w x ε u t by ring, abs_neg]
    exact ((hsmall x ε u (hloc he').1 (hloc he').2 hu).1 t).1
  · intro z hz
    rw [dist_comm, dist_eq_norm]
    change ‖old.F z + _ - old.F z‖ ≤ _
    rw [add_sub_cancel_left]
    exact (hsmall x ε u (hloc he').1 (hloc he').2 hu).2 z hz
  · obtain ⟨h₁, h₂⟩ := abs_le.mp (hmove he' u hu)
    change _ ≤ a + ε - root ε u ∧ a + ε - root ε u ≤ _
    constructor <;> linarith


set_option maxHeartbeats 1200000 in
/-- The limit of the successive corrections retains each finite transcript. -/
private theorem no_larger_order {n : ℕ} (hn : 1 ≤ n) (M : Method n) (p : ℝ)
    (hp : (B n : ℝ) < p) : ¬ HasOrderAtLeast M p := by
  classical
  choose next x ε step using next_stage hn M hp
  let S : ℕ → CounterexampleStage n := fun j => Nat.rec (initialStage n) next j
  let start (j : ℕ) := x j (S j)
  let scale (j : ℕ) := ε j (S j)
  have link (j : ℕ) : StageLink M p j (S j) (S (j + 1)) (start j) (scale j) :=
    step j (S j)
  obtain ⟨G, hG, hlim⟩ := entire_limit (b := fun j => (S j).budget)
    (fun j => (S j).budget_pos.le) (fun j => (link j).budget_half)
    (fun j => (S j).entire) (fun j => (link j).disk_bound)
  let f := onReal G
  have hf (t : ℝ) : AnalyticAt ℝ f t := onReal_analytic hG t
  have hconv (k : ℕ) (t : ℝ) : Tendsto (fun j => iteratedDeriv k (onReal (S j).F) t)
      atTop (𝓝 (iteratedDeriv k f t)) :=
    all_derivatives_converge hlim (fun j => (S j).entire) k t
  have hderiv (t : ℝ) : 1 / 2 ≤ deriv f t := by
    have hc : Tendsto (fun j => deriv (onReal (S j).F) t) atTop (𝓝 (deriv f t)) := by
      simpa only [iteratedDeriv_one] using hconv 1 t
    exact ge_of_tendsto hc (Eventually.of_forall fun j =>
      (show 1 / 2 ≤ 1 / 2 + 2 * (S j).budget by linarith [(S j).budget_pos]).trans ((S j).slope t).1)
  have hdiff : Differentiable ℝ f := fun t => (hf t).differentiableAt
  obtain ⟨α, hα⟩ := root_exists hdiff hderiv
  have hroot (i : ℕ) : |(S i).root - α| ≤ 4 * (S i).budget := by
    have ht : Tendsto (fun j => onReal (S j).F (S i).root) atTop (𝓝 (f (S i).root)) := by
      simpa using hconv 0 (S i).root
    have hg := geometric_distance (b := fun j => (S j).budget)
      (fun j => (S j).budget_pos.le) (fun j => (link j).budget_half) (i := i)
      (fun j _ => by rw [Real.dist_eq]; exact (link j).real_bound (S i).root) ht
    have hs := secant_abs_lower hdiff hderiv (S i).root α
    rw [Real.dist_eq, (S i).atRoot, zero_sub, abs_neg] at hg
    rw [hα, sub_zero] at hs
    linarith
  have hobserve (i : ℕ) (q : ℝ × ℕ) (hq : q ∈ observedJets M (onReal (S (i + 1)).F) (start i)) :
      iteratedDeriv q.2 (onReal (S (i + 1)).F) q.1 = iteratedDeriv q.2 f q.1 := by
    have ht (j : ℕ) (hj : i + 1 ≤ j) : q ∈ (S j).jets ∧
        iteratedDeriv q.2 (onReal (S (i + 1)).F) q.1 = iteratedDeriv q.2 (onReal (S j).F) q.1 := by
      induction j, hj using Nat.le_induction with
      | base => exact ⟨(link i).observed hq, rfl⟩
      | succ j hj ih =>
        exact ⟨(link j).jets_subset ih.1, ih.2.trans ((link j).keeps_jets q ih.1)⟩
    apply tendsto_nhds_unique _ (hconv q.2 q.1)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (i + 1)] with j hj
    exact (ht j hj).2
  have hout (i : ℕ) : M.step f (start i) = M.step (onReal (S (i + 1)).F) (start i) :=
    (same_output M (hobserve i)).symm
  intro horder
  obtain ⟨C, δ, hC, hδ, order⟩ := horder f hf α hα (by linarith [hderiv α])
  obtain ⟨i, hi⟩ := exists_nat_gt (max C (2 / δ))
  have hiC : C < (i : ℝ) + 1 := by linarith [(le_max_left C (2 / δ)).trans_lt hi]
  have hiδ : 2 / δ < (i : ℝ) + 1 := by linarith [(le_max_right C (2 / δ)).trans_lt hi]
  have hd := hroot (i + 1)
  have L := link i
  have hmove : |(S (i + 1)).root - α| ≤ scale i / 4 := by linarith [L.budget_scale]
  have hdist : 0 < |start i - α| ∧ |start i - α| ≤ 2 * scale i := by
    have hm := abs_le.mp hmove
    have hpos : 0 < start i - α := by linarith [L.offsets.1, L.scale.1, hm.1]
    rw [abs_of_pos hpos]
    exact ⟨hpos, by linarith [L.offsets.2, hm.2, L.scale.1]⟩
  have hnear : |start i - α| < δ := by
    have hι : 0 < (i : ℝ) + 1 := by positivity
    have hs := (lt_div_iff₀ hι).mp L.scale.2
    have hprod := (div_lt_iff₀ hδ).mp hiδ
    have hh : 2 * scale i < δ := (mul_lt_mul_iff_right₀ hι).mp (by nlinarith)
    exact hdist.2.trans_lt hh
  have herror : ((i : ℝ) + 1) * (2 * scale i) ^ p ≤ |M.step f (start i) - α| := by
    rw [hout]
    let y := M.step (onReal (S (i + 1)).F) (start i)
    have htri := abs_sub_le y α (S (i + 1)).root
    rw [abs_sub_comm α (S (i + 1)).root] at htri
    have hE := L.error
    have hb := L.budget_error
    change 2 * ((i : ℝ) + 1) * (2 * scale i) ^ p ≤ |y - (S (i + 1)).root| at hE
    change (S (i + 1)).budget ≤ |y - (S (i + 1)).root| / 16 at hb
    change ((i : ℝ) + 1) * (2 * scale i) ^ p ≤ |y - α|
    linarith only [hd, htri, hE, hb, abs_nonneg (y - (S (i + 1)).root)]
  have hpow := Real.rpow_le_rpow hdist.1.le hdist.2 ((Nat.cast_nonneg (B n) : (0 : ℝ) ≤ B n).trans hp.le)
  have hpos : 0 < (2 * scale i) ^ p := Real.rpow_pos_of_pos (by linarith [L.scale.1]) _
  exact (not_lt_of_ge herror)
    ((order (start i) hdist.1 hnear).trans_lt
      ((mul_le_mul_of_nonneg_left hpow hC.le).trans_lt (mul_lt_mul_of_pos_right hiC hpos)))

end KungTraubProof

theorem OMA.solution : type_of% @OMA.S_wp_kung_traub_conjecture.main := by
  intro n hn M p hp
  apply KungTraubProof.no_larger_order hn M p
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa [KungTraubProof.B, Nat.cast_pow] using hp
