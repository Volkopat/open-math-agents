import OMAReductions.R_Erdos651_erdos_651_variants_subexponential_R1
import Mathlib

/-!
# Valtr's Projection Inequality for Higher-Dimensional Erdős–Szekeres Numbers

We prove `OMA.R_Erdos651_erdos_651_variants_subexponential_R1.H2`:
`∀ k n : ℕ, 3 ≤ k → Erdos651.f (k + 1) n ≤ Erdos651.f k n`.

Following Valtr (1996) and Erdős–Szekeres (1935):
1. For any `k ≥ 2` and `N ∈ cardSet k n`, every finite general-position set `X ⊆ ℝ^(k+1)`
   of cardinality `≥ N` projects linearly along a generic moment-curve direction
   `v(t) = (1, t, t^2, ..., t^k)` avoiding the finitely many proper difference subspaces
   `vectorSpan ℝ Y` (`Y ⊆ X`, `2 ≤ Y.card ≤ k + 1`) to a general-position set in `ℝ^k` of the
   same cardinality. Lifting a convex-independent `n`-subset yields `N ∈ cardSet (k + 1) n`.
2. To ensure `cardSet k n` is nonempty (so `Nat.sInf` is antitone), we prove the planar
   Erdős–Szekeres cap–cup theorem (`(cardSet 2 n).Nonempty`) and propagate nonemptiness
   to all `k ≥ 2` by induction using the projection step.
-/

namespace Erdos651H2

open Finset Erdos651
open scoped EuclideanGeometry

private abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/- ### Part 1: Generic moment-curve direction avoiding finitely many proper subspaces -/

private lemma exists_functional_vanishing_on {k : ℕ} (W : Submodule ℝ (E (k + 1)))
    (hW : W ≠ ⊤) : ∃ φ : E (k + 1) →ₗ[ℝ] ℝ, φ ≠ 0 ∧ W ≤ LinearMap.ker φ := by
  have hlt : W < ⊤ := lt_top_iff_ne_top.mpr hW
  obtain ⟨v, _, hv⟩ : ∃ v ∈ (⊤ : Submodule ℝ (E (k + 1))), v ∉ W :=
    SetLike.exists_of_lt hlt
  obtain ⟨φ, hφv, hφW⟩ := Submodule.exists_le_ker_of_notMem hv
  refine ⟨φ, ?_, hφW⟩
  intro h0
  rw [h0] at hφv
  exact hφv rfl

private noncomputable def momentVec (k : ℕ) (t : ℝ) : E (k + 1) :=
  (EuclideanSpace.equiv (Fin (k + 1)) ℝ).symm (fun i => t ^ (i : ℕ))

private lemma momentVec_apply (k : ℕ) (t : ℝ) (i : Fin (k + 1)) :
    momentVec k t i = t ^ (i : ℕ) := rfl

private lemma eval_momentVec_eq_poly {k : ℕ} (φ : E (k + 1) →ₗ[ℝ] ℝ) :
    ∃ P : Polynomial ℝ, (φ ≠ 0 → P ≠ 0) ∧ ∀ t : ℝ, φ (momentVec k t) = P.eval t := by
  let b := EuclideanSpace.basisFun (Fin (k + 1)) ℝ
  let P : Polynomial ℝ := ∑ i : Fin (k + 1), Polynomial.C (φ (b i)) * Polynomial.X ^ (i : ℕ)
  refine ⟨P, ?_, ?_⟩
  · intro hφ hP0
    apply hφ
    apply b.toBasis.ext
    intro i
    have hcoeff : P.coeff (i : ℕ) = 0 := by rw [hP0, Polynomial.coeff_zero]
    dsimp only [P] at hcoeff
    rw [Polynomial.finsetSum_coeff] at hcoeff
    have hsum : (∑ j : Fin (k + 1), (Polynomial.C (φ (b j)) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ)) =
        φ (b i) := by
      rw [Finset.sum_eq_single i]
      · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      · intro j _ hji
        have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hji (Fin.ext h.symm)
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    rw [hsum] at hcoeff
    simpa using hcoeff
  · intro t
    have hmv : momentVec k t = ∑ i : Fin (k + 1), (t ^ (i : ℕ)) • b i := by
      ext j
      change t ^ (j : ℕ) = (∑ i : Fin (k + 1), (t ^ (i : ℕ)) • b i).ofLp j
      rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single j]
      · simp [b, EuclideanSpace.basisFun_apply]
      · intro i _ hij
        simp [b, EuclideanSpace.basisFun_apply, hij.symm]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [hmv, map_sum]
    simp only [P, map_smul, smul_eq_mul, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma exists_momentVec_notMem_family {k : ℕ} {ι : Type*}
    (I : Finset ι) (W : ι → Submodule ℝ (E (k + 1))) (hW : ∀ i ∈ I, W i ≠ ⊤) :
    ∃ t : ℝ, ∀ i ∈ I, momentVec k t ∉ W i := by
  classical
  choose φ hφne hφker using fun (i : I) => exists_functional_vanishing_on (W i.1) (hW i.1 i.2)
  choose P hPne hPeval using fun (i : I) => eval_momentVec_eq_poly (φ i)
  let Q : Polynomial ℝ := ∏ i : I, P i
  have hQne : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hPne i (hφne i)
  have hfin : {t : ℝ | Q.eval t = 0}.Finite := by
    refine (Q.roots.toFinset.finite_toSet).subset ?_
    intro t ht
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hQne]
    exact ht
  obtain ⟨t, ht⟩ := (Set.infinite_univ.sdiff hfin).nonempty
  refine ⟨t, fun i hi hmem => ?_⟩
  have hQt : Q.eval t ≠ 0 := by simpa using ht.2
  have hPW : (P ⟨i, hi⟩).eval t = 0 := by
    rw [← hPeval ⟨i, hi⟩]
    exact hφker ⟨i, hi⟩ hmem
  apply hQt
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ ⟨i, hi⟩) hPW

/- ### Part 2: Explicit linear projection with kernel `ℝ ∙ momentVec k t` -/

private noncomputable def projLin (k : ℕ) (t : ℝ) : E (k + 1) →ₗ[ℝ] E k where
  toFun x := (EuclideanSpace.equiv (Fin k) ℝ).symm fun j =>
    x j.succ - x 0 * t ^ ((j : ℕ) + 1)
  map_add' x y := by ext j; simp; ring
  map_smul' c x := by ext j; simp; ring

private lemma projLin_ker_iff {k : ℕ} {t : ℝ} {x : E (k + 1)} :
    projLin k t x = 0 ↔ x = (x 0) • momentVec k t := by
  constructor
  · intro hx
    ext i
    refine Fin.cases ?_ ?_ i
    · simp [momentVec_apply]
    · intro j
      have hj := congrFun (congrArg WithLp.ofLp hx) j
      simp only [projLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_zero, Pi.zero_apply] at hj
      change x j.succ - x 0 * t ^ ((j : ℕ) + 1) = 0 at hj
      simp only [PiLp.smul_apply, smul_eq_mul, momentVec_apply, Fin.val_succ]
      linarith
  · intro hx
    ext j
    simp only [projLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_zero, Pi.zero_apply]
    change x j.succ - x 0 * t ^ ((j : ℕ) + 1) = 0
    have h1 := congrFun (congrArg WithLp.ofLp hx) j.succ
    have h0 := congrFun (congrArg WithLp.ofLp hx) 0
    simp only [PiLp.smul_apply, smul_eq_mul, momentVec_apply, Fin.val_succ, Fin.val_zero, pow_zero,
      mul_one] at h1 h0
    linarith

private lemma finrank_vectorSpan_lt {k : ℕ} {Y : Finset (E (k + 1))} (hY : Y.card ≤ k + 1) :
    vectorSpan ℝ (Y : Set (E (k + 1))) ≠ ⊤ := by
  classical
  intro htop
  have h2 : Module.finrank ℝ (vectorSpan ℝ (Y : Set (E (k + 1)))) = k + 1 := by
    rw [htop, finrank_top, finrank_euclideanSpace_fin]
  rcases Y.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · rw [Finset.coe_empty, vectorSpan_empty, finrank_bot] at h2; omega
  · have h1 : Module.finrank ℝ (vectorSpan ℝ (Y : Set (E (k + 1)))) ≤ Y.card - 1 := by
      have hcard : Y.card = (Y.card - 1) + 1 := by
        have := Finset.card_pos.mpr ⟨y₀, hy₀⟩; omega
      have hle := finrank_vectorSpan_image_finset_le ℝ (id : E (k + 1) → E (k + 1)) Y hcard
      rw [Finset.image_id] at hle
      exact hle
    omega

private lemma cardSet_subset_succ {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : cardSet k n ⊆ cardSet (k + 1) n := by
  classical
  intro N hN X hX hcard
  let subY : Finset (Finset (E (k + 1))) := X.powerset.filter (fun Y => Y.card ≤ k + 1)
  have hbad : ∀ Y ∈ subY, vectorSpan ℝ (Y : Set (E (k + 1))) ≠ ⊤ := fun Y hY =>
    finrank_vectorSpan_lt (Finset.mem_filter.mp hY).2
  obtain ⟨t, ht⟩ := exists_momentVec_notMem_family subY (fun Y => vectorSpan ℝ (Y : Set (E (k + 1)))) hbad
  have hnotmem : ∀ Y ⊆ X, Y.card ≤ k + 1 → momentVec k t ∉ vectorSpan ℝ (Y : Set (E (k + 1))) := by
    intro Y hYX hYc
    exact ht Y (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hYX, hYc⟩)
  let L := projLin k t
  have hinj : Set.InjOn L (X : Set (E (k + 1))) := by
    intro x hx y hy hxy
    by_contra hne
    have h0 : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hsm := projLin_ker_iff.mp h0
    have hcoeff_ne : (x - y) 0 ≠ 0 := by
      intro h0'
      rw [h0', zero_smul] at hsm
      exact hne (sub_eq_zero.mp hsm)
    have hmem_vs : x - y ∈ vectorSpan ℝ (({x, y} : Finset (E (k + 1))) : Set (E (k + 1))) := by
      have hx' : x ∈ (({x, y} : Finset (E (k + 1))) : Set (E (k + 1))) := by simp
      have hy' : y ∈ (({x, y} : Finset (E (k + 1))) : Set (E (k + 1))) := by simp
      simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ hx' hy'
    have hmv_mem : momentVec k t ∈ vectorSpan ℝ (({x, y} : Finset (E (k + 1))) : Set (E (k + 1))) := by
      have : momentVec k t = ((x - y) 0)⁻¹ • (x - y) := by
        calc momentVec k t = (1 : ℝ) • momentVec k t := (one_smul _ _).symm
          _ = (((x - y) 0)⁻¹ * (x - y) 0) • momentVec k t := by rw [inv_mul_cancel₀ hcoeff_ne]
          _ = ((x - y) 0)⁻¹ • ((x - y) 0 • momentVec k t) := mul_smul _ _ _
          _ = ((x - y) 0)⁻¹ • (x - y) := by rw [← hsm]
      rw [this]
      exact Submodule.smul_mem _ _ hmem_vs
    have hsub2 : ({x, y} : Finset (E (k + 1))) ⊆ X := by
      intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    have hcard2 : ({x, y} : Finset (E (k + 1))).card ≤ k + 1 := by
      have := Finset.card_pair hne; omega
    exact hnotmem {x, y} hsub2 hcard2 hmv_mem
  have hgp : IsInGeneralPosition (X.image L) := by
    intro Z hZ hZc
    let Y := X.filter (fun p => L p ∈ Z)
    have hYX : Y ⊆ X := Finset.filter_subset _ _
    have hYZ : Y.image L = Z := by
      ext q
      simp only [Finset.mem_image, Finset.mem_filter, Y]
      constructor
      · rintro ⟨p, ⟨_, hpZ⟩, rfl⟩; exact hpZ
      · intro hqZ
        obtain ⟨p, hpX, rfl⟩ := Finset.mem_image.mp (hZ hqZ)
        exact ⟨p, ⟨hpX, hqZ⟩, rfl⟩
    have hYcard : Y.card = Z.card := by
      rw [← hYZ, Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hYX))]
    rw [affineIndependent_iff]
    intro s w hw hsum i hi
    -- Pull back s ⊆ Z to sY ⊆ Y via inverse of L on Y
    have hz_im : ∀ z : ↥(Z : Set (E k)), z.1 ∈ Y.image L := fun z => by
      rw [hYZ]; exact z.2
    let f : ↥(Z : Set (E k)) → E (k + 1) := fun z =>
      (Finset.mem_image.mp (hz_im z)).choose
    have hf_mem : ∀ z : ↥(Z : Set (E k)), f z ∈ Y := fun z =>
      (Finset.mem_image.mp (hz_im z)).choose_spec.1
    have hf_L : ∀ z : ↥(Z : Set (E k)), L (f z) = z.1 := fun z =>
      (Finset.mem_image.mp (hz_im z)).choose_spec.2
    let v : E (k + 1) := ∑ z ∈ s, w z • f z
    have hLsum : L v = 0 := by
      dsimp only [v]
      rw [map_sum]
      have hcongr : (∑ z ∈ s, L (w z • f z)) = ∑ z ∈ s, w z • z.1 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [map_smul, hf_L z]
      rw [hcongr]
      exact hsum
    have hker := projLin_ker_iff.mp hLsum
    have hvs : v ∈ vectorSpan ℝ (Y : Set (E (k + 1))) := by
      rcases s.eq_empty_or_nonempty with rfl | ⟨z₀, hz₀⟩
      · simp [v]
      · have hv_eq : v = ∑ z ∈ s, w z • (f z - f z₀) := by
          dsimp only [v]
          simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw, zero_smul, sub_zero]
        rw [hv_eq]
        refine Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ ?_
        simpa [vsub_eq_sub] using vsub_mem_vectorSpan ℝ (hf_mem z) (hf_mem z₀)
    have hc0 : v 0 = 0 := by
      by_contra hne
      have hmv : momentVec k t ∈ vectorSpan ℝ (Y : Set (E (k + 1))) := by
        have : momentVec k t = (v 0)⁻¹ • v := by
          calc momentVec k t = (1 : ℝ) • momentVec k t := (one_smul _ _).symm
            _ = ((v 0)⁻¹ * v 0) • momentVec k t := by rw [inv_mul_cancel₀ hne]
            _ = (v 0)⁻¹ • (v 0 • momentVec k t) := mul_smul _ _ _
            _ = (v 0)⁻¹ • v := by rw [← hker]
        rw [this]
        exact Submodule.smul_mem _ _ hvs
      exact hnotmem Y hYX (hYcard.trans_le hZc) hmv
    have hzero : ∑ z ∈ s, w z • f z = 0 := by
      change v = 0
      rw [hker, hc0, zero_smul]
    have hYgp : AffineIndependent ℝ ((↑) : ↥(Y : Set (E (k + 1))) → E (k + 1)) :=
      hX Y hYX (by omega)
    let e : ↥(Z : Set (E k)) → ↥(Y : Set (E (k + 1))) := fun z => ⟨f z, hf_mem z⟩
    have he_inj : Function.Injective e := by
      intro z1 z2 heq
      apply Subtype.ext
      have h1 : f z1 = f z2 := congrArg Subtype.val heq
      rw [← hf_L z1, ← hf_L z2, h1]
    have hcomp : AffineIndependent ℝ (fun z : ↥(Z : Set (E k)) => f z) :=
      hYgp.comp_embedding ⟨e, he_inj⟩
    exact affineIndependent_iff.mp hcomp s w hw hzero i hi
  have hcard' : N ≤ (X.image L).card := by
    rw [Finset.card_image_of_injOn hinj]
    exact hcard
  obtain ⟨Z, hZsub, hZcard, hZconv⟩ := hN (X.image L) hgp hcard'
  let Y := X.filter (fun p => L p ∈ Z)
  have hYX : Y ⊆ X := Finset.filter_subset _ _
  have hYZ : Y.image L = Z := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Y]
    constructor
    · rintro ⟨p, ⟨_, hpZ⟩, rfl⟩; exact hpZ
    · intro hqZ
      obtain ⟨p, hpX, rfl⟩ := Finset.mem_image.mp (hZsub hqZ)
      exact ⟨p, ⟨hpX, hqZ⟩, rfl⟩
  have hYcard : Y.card = n := by
    rw [← hZcard, ← hYZ, Finset.card_image_of_injOn (hinj.mono (by exact_mod_cast hYX))]
  refine ⟨Y, hYX, hYcard, ?_⟩
  intro s y hy
  have hyZ : L y.1 ∈ Z := (Finset.mem_filter.mp y.2).2
  let sZ : Set ↥(Z : Set (E k)) :=
    (fun p : ↥(Y : Set (E (k + 1))) => (⟨L p.1, (Finset.mem_filter.mp p.2).2⟩ : ↥(Z : Set (E k)))) '' s
  have hLmem : L y.1 ∈ convexHull ℝ ((↑) '' sZ) := by
    have h1 := Set.mem_image_of_mem L.toAffineMap hy
    rw [AffineMap.image_convexHull] at h1
    refine convexHull_mono ?_ h1
    rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨⟨L p.1, (Finset.mem_filter.mp p.2).2⟩, ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨p, hp, hpEq⟩ := hZconv sZ ⟨L y.1, hyZ⟩ hLmem
  have hpy : p = y := Subtype.ext (hinj (hYX p.2) (hYX y.2) (congrArg Subtype.val hpEq))
  exact hpy ▸ hp

/- ### Part 3: Planar Erdős–Szekeres theorem (`(cardSet 2 n).Nonempty`) -/

private lemma planar_distinct_x (X : Finset (E 2)) :
    ∃ u : E 2, u ≠ 0 ∧ Set.InjOn (fun p : E 2 => inner ℝ p u) (X : Set (E 2)) := by
  classical
  have horth : ∀ pq ∈ X.offDiag, LinearMap.ker (innerSL ℝ (pq.1 - pq.2)).toLinearMap ≠ ⊤ := by
    intro pq hpq htop
    have hne : pq.1 - pq.2 ≠ 0 := sub_ne_zero.mpr (Finset.mem_offDiag.mp hpq).2.2
    have hmem : pq.1 - pq.2 ∈ LinearMap.ker (innerSL ℝ (pq.1 - pq.2)).toLinearMap := by
      rw [htop]; trivial
    have h0 : inner ℝ (pq.1 - pq.2) (pq.1 - pq.2) = 0 := hmem
    exact hne (inner_self_eq_zero.mp h0)
  obtain ⟨t, ht⟩ := exists_momentVec_notMem_family X.offDiag
    (fun pq => LinearMap.ker (innerSL ℝ (pq.1 - pq.2)).toLinearMap) horth
  refine ⟨momentVec 1 t, ?_, ?_⟩
  · intro h0
    have := congrFun (congrArg WithLp.ofLp h0) 0
    simp [momentVec_apply] at this
  · intro x hx y hy hxy
    dsimp only at hxy
    by_contra hne
    have hmem : momentVec 1 t ∈ LinearMap.ker (innerSL ℝ (x - y)).toLinearMap := by
      change inner ℝ (x - y) (momentVec 1 t) = 0
      rw [inner_sub_left, hxy, sub_self]
    exact ht (x, y) (Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩) hmem

private def IsCup (pts : List (ℝ × ℝ)) : Prop :=
  pts.Pairwise (fun a b => a.1 < b.1) ∧
  ∀ i : ℕ, (h : i + 2 < pts.length) →
    (pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1) <
    (pts[i + 2].2 - pts[i + 1].2) / (pts[i + 2].1 - pts[i + 1].1)

private def IsCap (pts : List (ℝ × ℝ)) : Prop :=
  pts.Pairwise (fun a b => a.1 < b.1) ∧
  ∀ i : ℕ, (h : i + 2 < pts.length) →
    (pts[i + 2].2 - pts[i + 1].2) / (pts[i + 2].1 - pts[i + 1].1) <
    (pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1)

private lemma slope_strictMono_of_isCup {pts : List (ℝ × ℝ)} (hcup : IsCup pts)
    {i j : ℕ} (hi : i < j) (hj : j + 1 < pts.length) :
    (pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1) <
    (pts[j + 1].2 - pts[j].2) / (pts[j + 1].1 - pts[j].1) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hij : i = j
    · subst hij; exact hcup.2 i hj
    · exact (ih (by omega) (by omega)).trans (hcup.2 j hj)

private lemma x_lt_of_pairwise {pts : List (ℝ × ℝ)} (hp : pts.Pairwise (fun a b => a.1 < b.1))
    {i j : ℕ} (hij : i < j) (hj : j < pts.length) :
    pts[i].1 < pts[j].1 :=
  List.pairwise_iff_getElem.mp hp i j (by omega) hj hij

private lemma isCup_strict_above_line {pts : List (ℝ × ℝ)} (hcup : IsCup pts)
    {i : ℕ} (hi : i < pts.length) :
    ∃ m : ℝ, ∀ j : ℕ, (hj : j < pts.length) → j ≠ i →
      pts[i].2 + m * (pts[j].1 - pts[i].1) < pts[j].2 := by
  have hstep_pos : ∀ r : ℕ, (hr : r + 1 < pts.length) → 0 < pts[r + 1].1 - pts[r].1 := fun r hr =>
    sub_pos.mpr (x_lt_of_pairwise hcup.1 (Nat.lt_succ_self r) hr)
  -- Pick m strictly between left slope (if i > 0) and right slope (if i + 1 < pts.length)
  obtain ⟨m, hmL, hmR⟩ : ∃ m : ℝ,
      (∀ h0 : 0 < i, (pts[i].2 - pts[i - 1].2) / (pts[i].1 - pts[i - 1].1) < m) ∧
      (∀ h1 : i + 1 < pts.length, m < (pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1)) := by
    by_cases h0 : 0 < i
    · by_cases h1 : i + 1 < pts.length
      · have hlt : (pts[i].2 - pts[i - 1].2) / (pts[i].1 - pts[i - 1].1) <
            (pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1) := by
          have := hcup.2 (i - 1) (by omega)
          simpa [Nat.sub_add_cancel h0, show i - 1 + 2 = i + 1 by omega] using this
        refine ⟨((pts[i].2 - pts[i - 1].2) / (pts[i].1 - pts[i - 1].1) +
                 (pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1)) / 2,
          fun _ => by linarith, fun _ => by linarith⟩
      · refine ⟨(pts[i].2 - pts[i - 1].2) / (pts[i].1 - pts[i - 1].1) + 1,
          fun _ => by linarith, fun h => absurd h h1⟩
    · by_cases h1 : i + 1 < pts.length
      · refine ⟨(pts[i + 1].2 - pts[i].2) / (pts[i + 1].1 - pts[i].1) - 1,
          fun h => absurd h h0, fun _ => by linarith⟩
      · exact ⟨0, fun h => absurd h h0, fun h => absurd h h1⟩
  refine ⟨m, fun j hj hne => ?_⟩
  rcases lt_or_gt_of_ne hne with hji | hij
  · -- j < i: telescope from j to i
    suffices ∀ d : ℕ, (hd : j + d ≤ i) → 0 < d →
        pts[j + d].2 + m * (pts[j].1 - pts[j + d].1) < pts[j].2 by
      have := this (i - j) (by omega) (by omega)
      simpa [Nat.add_sub_cancel' hji.le] using this
    intro d hd hdpos
    induction d with
    | zero => omega
    | succ d ih =>
      have hstep : m * (pts[j + d].1 - pts[j + d + 1].1) + pts[j + d + 1].2 < pts[j + d].2 := by
        have hpos := hstep_pos (j + d) (by omega)
        have hslope_lt : (pts[j + d + 1].2 - pts[j + d].2) / (pts[j + d + 1].1 - pts[j + d].1) < m := by
          have hi0 : 0 < i := by omega
          by_cases heq : j + d = i - 1
          · have hsub : i - 1 + 1 = i := by omega
            simp only [heq, hsub]
            exact hmL hi0
          · have hlt := slope_strictMono_of_isCup hcup (i := j + d) (j := i - 1) (by omega) (by omega)
            have h1 : i - 1 + 1 = i := by omega
            have h2 := hmL hi0
            simp only [h1] at hlt
            exact hlt.trans h2
        have hmul := (div_lt_iff₀ hpos).mp hslope_lt
        linarith
      by_cases hd0 : d = 0
      · subst hd0; simp only [add_zero, ← add_assoc] at hstep ⊢; linarith
      · have hprev := ih (by omega) (by omega)
        simp only [← add_assoc] at hstep hprev ⊢; linarith
  · -- i < j: telescope from i to j
    suffices ∀ d : ℕ, (hd : i + d < pts.length) → 0 < d →
        pts[i].2 + m * (pts[i + d].1 - pts[i].1) < pts[i + d].2 by
      have := this (j - i) (by omega) (by omega)
      simpa [Nat.add_sub_cancel' hij.le] using this
    intro d hd hdpos
    induction d with
    | zero => omega
    | succ d ih =>
      have hstep : pts[i + d].2 + m * (pts[i + d + 1].1 - pts[i + d].1) < pts[i + d + 1].2 := by
        have hpos := hstep_pos (i + d) hd
        have hslope_gt : m < (pts[i + d + 1].2 - pts[i + d].2) / (pts[i + d + 1].1 - pts[i + d].1) := by
          have hi1 : i + 1 < pts.length := by omega
          by_cases heq : d = 0
          · subst heq; simpa using hmR hi1
          · exact (hmR hi1).trans (slope_strictMono_of_isCup hcup (i := i) (j := i + d) (by omega) hd)
        have hmul := (lt_div_iff₀ hpos).mp hslope_gt
        linarith
      by_cases hd0 : d = 0
      · subst hd0; simp only [add_zero, ← add_assoc] at hstep ⊢; linarith
      · have hprev := ih (by omega) (by omega)
        simp only [← add_assoc] at hstep hprev ⊢; linarith

private lemma isCap_strict_below_line {pts : List (ℝ × ℝ)} (hcap : IsCap pts)
    {i : ℕ} (hi : i < pts.length) :
    ∃ m : ℝ, ∀ j : ℕ, (hj : j < pts.length) → j ≠ i →
      pts[j].2 < pts[i].2 + m * (pts[j].1 - pts[i].1) := by
  let pts' := pts.map (fun p => (p.1, -p.2))
  have hcup : IsCup pts' := by
    refine ⟨?_, ?_⟩
    · exact List.pairwise_map.mpr (hcap.1.imp fun h => h)
    · intro r hr
      simp only [pts', List.length_map] at hr ⊢
      have h := hcap.2 r hr
      simp only [List.getElem_map]
      have h1 : (-pts[r + 1].2 - -pts[r].2) / (pts[r + 1].1 - pts[r].1) =
          -((pts[r + 1].2 - pts[r].2) / (pts[r + 1].1 - pts[r].1)) := by ring
      have h2 : (-pts[r + 2].2 - -pts[r + 1].2) / (pts[r + 2].1 - pts[r + 1].1) =
          -((pts[r + 2].2 - pts[r + 1].2) / (pts[r + 2].1 - pts[r + 1].1)) := by ring
      rw [h1, h2]; linarith
  obtain ⟨m, hm⟩ := isCup_strict_above_line hcup (i := i) (by simp [pts', hi])
  refine ⟨-m, fun j hj hne => ?_⟩
  have h := hm j (by simp [pts', hj]) hne
  simp only [pts', List.getElem_map] at h
  linarith

private lemma sublist_of_pairwise_subset : ∀ (pts a : List (ℝ × ℝ)),
    pts.Pairwise (fun x y => x.1 < y.1) →
    a.Pairwise (fun x y => x.1 < y.1) →
    (∀ x ∈ a, x ∈ pts) → a.Sublist pts := by
  intro pts
  induction pts with
  | nil =>
    intro a _ _ ha_mem
    cases a with
    | nil => exact List.Sublist.slnil
    | cons x xs => exact absurd (ha_mem x (by simp)) (by simp)
  | cons z zs ih =>
    intro a hpair ha_pair ha_mem
    cases a with
    | nil => exact List.nil_sublist _
    | cons x xs =>
      have hx_mem := ha_mem x (by simp)
      rcases List.mem_cons.mp hx_mem with rfl | hx_zs
      · apply List.Sublist.cons_cons
        apply ih xs (List.pairwise_cons.mp hpair).2 (List.pairwise_cons.mp ha_pair).2
        intro y hy
        have hy_mem := ha_mem y (by simp [hy])
        rcases List.mem_cons.mp hy_mem with rfl | hy_zs
        · exfalso; exact lt_irrefl _ ((List.pairwise_cons.mp ha_pair).1 y hy)
        · exact hy_zs
      · apply List.Sublist.cons
        apply ih (x :: xs) (List.pairwise_cons.mp hpair).2 ha_pair
        intro y hy
        have hy_mem := ha_mem y hy
        rcases List.mem_cons.mp hy_mem with hyz | hy_zs
        · exfalso
          have hz_lt_x : z.1 < x.1 := (List.pairwise_cons.mp hpair).1 x hx_zs
          rw [hyz] at hy
          rcases List.mem_cons.mp hy with hzx | hz_xs
          · rw [hzx] at hz_lt_x; exact lt_irrefl _ hz_lt_x
          · have hx_lt_z : x.1 < z.1 := (List.pairwise_cons.mp ha_pair).1 z hz_xs
            linarith
        · exact hy_zs

private lemma cap_cup_exists : ∀ (s : ℕ) (k l : ℕ), 2 ≤ k → 2 ≤ l → k + l = s →
    ∀ (pts : List (ℝ × ℝ)),
      pts.Pairwise (fun a b => a.1 < b.1) →
      (∀ i j r : ℕ, (hi : i < j) → (hj : j < r) → (hr : r < pts.length) →
        (pts[j].2 - pts[i].2) / (pts[j].1 - pts[i].1) ≠
        (pts[r].2 - pts[j].2) / (pts[r].1 - pts[j].1)) →
      Nat.choose (k + l - 4) (k - 2) < pts.length →
      (∃ sub : List (ℝ × ℝ), sub.Sublist pts ∧ sub.length = k ∧ IsCup sub) ∨
      (∃ sub : List (ℝ × ℝ), sub.Sublist pts ∧ sub.length = l ∧ IsCap sub) := by
  intro s
  induction s using Nat.strongRecOn with
  | ind s ih =>
    intro k l hk hl hkl pts hpair hncol hlen
    by_cases hk2 : k = 2
    · subst hk2
      have h2 : 2 ≤ pts.length := by
        simp only [Nat.sub_self, Nat.choose_zero_right] at hlen; omega
      rcases pts with _ | ⟨a, _ | ⟨b, rest⟩⟩
      · simp at h2
      · simp at h2
      · left
        refine ⟨[a, b], List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.nil_sublist _)),
          rfl, ?_, ?_⟩
        · simp [List.pairwise_cons, (List.pairwise_cons.mp hpair).1 b (by simp)]
        · intro i hi; simp at hi
    · by_cases hl2 : l = 2
      · subst hl2
        have h2 : 2 ≤ pts.length := by
          have hchoose : Nat.choose (k + 2 - 4) (k - 2) = 1 := by
            rw [show k + 2 - 4 = k - 2 by omega, Nat.choose_self]
          omega
        rcases pts with _ | ⟨a, _ | ⟨b, rest⟩⟩
        · simp at h2
        · simp at h2
        · right
          refine ⟨[a, b], List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.nil_sublist _)),
            rfl, ?_, ?_⟩
          · simp [List.pairwise_cons, (List.pairwise_cons.mp hpair).1 b (by simp)]
          · intro i hi; simp at hi
      · -- Both k ≥ 3 and l ≥ 3
        have hk3 : 3 ≤ k := by omega
        have hl3 : 3 ≤ l := by omega
        -- Split pts into R (rightmost endpoints of (k-1)-cups) and rest = pts \ R
        classical
        let isRightCup (p : ℝ × ℝ) : Prop :=
          ∃ sub : List (ℝ × ℝ), sub.Sublist pts ∧ sub.length = k - 1 ∧ IsCup sub ∧
            sub.getLast? = some p
        let R := pts.filter (fun p => decide (isRightCup p))
        let L := pts.filter (fun p => !decide (isRightCup p))
        have hRL_len : R.length + L.length = pts.length := by
          have hlen_split : ∀ (p : ℝ × ℝ → Bool) (xs : List (ℝ × ℝ)),
              (xs.filter p).length + (xs.filter (fun x => !p x)).length = xs.length := by
            intro p xs
            induction xs with
            | nil => simp
            | cons x xs ih => cases hpx : p x <;> simp [hpx] <;> omega
          exact hlen_split (fun p => decide (isRightCup p)) pts
        have hpascal : Nat.choose (k + l - 4) (k - 2) =
            Nat.choose (k - 1 + l - 4) (k - 1 - 2) + Nat.choose (k + (l - 1) - 4) (k - 2) := by
          have h1 : k + l - 4 = (k + l - 5) + 1 := by omega
          have h2 : k - 2 = (k - 3) + 1 := by omega
          have h3 : k - 1 + l - 4 = k + l - 5 := by omega
          have h4 : k - 1 - 2 = k - 3 := by omega
          have h5 : k + (l - 1) - 4 = k + l - 5 := by omega
          rw [h1, h2, h3, h4, h5, Nat.choose_succ_succ, add_comm]
        -- Helper: pairwise and non-collinear transfer to any sublist
        have hsub_props : ∀ sub : List (ℝ × ℝ), sub.Sublist pts →
            sub.Pairwise (fun a b => a.1 < b.1) ∧
            (∀ i j r : ℕ, (hi : i < j) → (hj : j < r) → (hr : r < sub.length) →
              (sub[j].2 - sub[i].2) / (sub[j].1 - sub[i].1) ≠
              (sub[r].2 - sub[j].2) / (sub[r].1 - sub[j].1)) := by
          intro sub hsub
          refine ⟨hpair.sublist hsub, ?_⟩
          have hnodup : pts.Nodup := hpair.imp fun h => by intro he; rw [he] at h; exact lt_irrefl _ h
          -- Map indices of sub strictly into indices of pts via order embedding
          have hex : ∀ {a b : List (ℝ × ℝ)}, a.Sublist b →
              ∃ f : Fin a.length → Fin b.length, StrictMono f ∧ ∀ i, a[i.1] = b[(f i).1] := by
            intro a b hab
            induction hab with
            | slnil => exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
            | @cons x l₁ l₂ _ ih =>
              obtain ⟨f, hf, hfeq⟩ := ih
              exact ⟨fun i => (f i).succ, fun i j hij => Fin.succ_lt_succ_iff.mpr (hf hij),
                fun i => by simpa using hfeq i⟩
            | @cons_cons x l₁ l₂ _ ih =>
              obtain ⟨f, hf, hfeq⟩ := ih
              refine ⟨fun i => Fin.cases 0 (fun j => (f j).succ) i, ?_, ?_⟩
              · intro i j hij
                rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
                rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
                · exact absurd hij (lt_irrefl _)
                · simp
                · exact absurd hij (by simp)
                · simp only [Fin.cases_succ, Fin.succ_lt_succ_iff] at hij ⊢; exact hf hij
              · intro i
                refine Fin.cases rfl (fun j => by simpa using hfeq j) i
          obtain ⟨f, hf, hfeq⟩ := hex hsub
          intro i j r hij hjr hr
          have hi' := hfeq ⟨i, by omega⟩
          have hj' := hfeq ⟨j, by omega⟩
          have hr' := hfeq ⟨r, hr⟩
          rw [hi', hj', hr']
          exact hncol _ _ _ (hf (show (⟨i, by omega⟩ : Fin sub.length) < ⟨j, by omega⟩ from hij))
            (hf (show (⟨j, by omega⟩ : Fin sub.length) < ⟨r, hr⟩ from hjr)) (f ⟨r, hr⟩).2
        -- First check if L has length > choose(k-1+l-4, k-3): impossible if L has no (k-1)-cup!
        by_cases hLbig : Nat.choose (k - 1 + l - 4) (k - 1 - 2) < L.length
        · have hLsub : L.Sublist pts := List.filter_sublist
          obtain ⟨hLp, hLnc⟩ := hsub_props L hLsub
          rcases ih (k - 1 + l) (by omega) (k - 1) l (by omega) hl rfl L hLp hLnc hLbig with
            ⟨sub, hsubL, hsublen, hsubcup⟩ | ⟨sub, hsubL, hsublen, hsubcap⟩
          · -- Contradiction: last element of sub would be in R, not L!
            exfalso
            have hne : sub ≠ [] := by intro h; rw [h] at hsublen; simp at hsublen; omega
            obtain ⟨p, hp⟩ : ∃ p, sub.getLast? = some p := by
              cases h : sub.getLast? with
              | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
              | some p => exact ⟨p, rfl⟩
            have hp_mem : p ∈ L := hsubL.subset (List.mem_of_getLast? hp)
            have hp_not : ¬ isRightCup p := by
              have := (List.mem_filter.mp hp_mem).2
              simpa using this
            exact hp_not ⟨sub, hsubL.trans hLsub, hsublen, hsubcup, hp⟩
          · exact Or.inr ⟨sub, hsubL.trans hLsub, hsublen, hsubcap⟩
        · -- Otherwise R.length > choose(k + (l-1) - 4, k - 2)
          have hRbig : Nat.choose (k + (l - 1) - 4) (k - 2) < R.length := by omega
          have hRsub : R.Sublist pts := List.filter_sublist
          obtain ⟨hRp, hRnc⟩ := hsub_props R hRsub
          rcases ih (k + (l - 1)) (by omega) k (l - 1) hk (by omega) rfl R hRp hRnc hRbig with
            ⟨sub, hsubR, hsublen, hsubcup⟩ | ⟨sub, hsubR, hsublen, hsubcap⟩
          · exact Or.inl ⟨sub, hsubR.trans hRsub, hsublen, hsubcup⟩
          · -- sub is an (l-1)-cap in R; its first element p0 is in R, hence last of a (k-1)-cup!
            have hne : sub ≠ [] := by intro h; rw [h] at hsublen; simp at hsublen; omega
            have hsublen2 : 2 ≤ sub.length := by omega
            let p0 := sub[0]'(by omega)
            let p1 := sub[1]'(by omega)
            have hp0_mem : p0 ∈ R := hsubR.subset (List.getElem_mem _)
            have hp0_rc : isRightCup p0 := by
              have := (List.mem_filter.mp hp0_mem).2
              simpa using this
            obtain ⟨cup, hcup_sub, hcup_len, hcup_is, hcup_last⟩ := hp0_rc
            have hcup_len2 : 2 ≤ cup.length := by omega
            have hcup_eq : cup[cup.length - 1]'(by omega) = p0 := by
              rw [List.getLast?_eq_getElem?] at hcup_last
              have := List.getElem?_eq_getElem (by omega : cup.length - 1 < cup.length)
              rw [this] at hcup_last
              exact Option.some.inj hcup_last
            let q := cup[cup.length - 2]'(by omega)
            have hqp0 : q.1 < p0.1 := by
              rw [← hcup_eq]
              exact x_lt_of_pairwise hcup_is.1 (by omega) (by omega)
            have hp0p1 : p0.1 < p1.1 := x_lt_of_pairwise hsubcap.1 (by omega) (by omega)
            -- Compare slope(q, p0) vs slope(p0, p1): cannot be equal by hncol!
            have hne_slope : (p0.2 - q.2) / (p0.1 - q.1) ≠ (p1.2 - p0.2) / (p1.1 - p0.1) := by
              have hq_mem : q ∈ pts := hcup_sub.subset (List.getElem_mem _)
              have hp0_pts : p0 ∈ pts := (hsubR.trans hRsub).subset (List.getElem_mem _)
              have hp1_pts : p1 ∈ pts := (hsubR.trans hRsub).subset (List.getElem_mem _)
              obtain ⟨iq, hiq, hqeq⟩ := List.mem_iff_getElem.mp hq_mem
              obtain ⟨i0, hi0, h0eq⟩ := List.mem_iff_getElem.mp hp0_pts
              obtain ⟨i1, hi1, h1eq⟩ := List.mem_iff_getElem.mp hp1_pts
              have hiq0 : iq < i0 := by
                by_contra! hle
                rcases eq_or_lt_of_le hle with rfl | hlt
                · rw [← hqeq, ← h0eq] at hqp0; exact lt_irrefl _ hqp0
                · have := x_lt_of_pairwise hpair hlt hiq
                  rw [hqeq, h0eq] at this; linarith
              have hi01 : i0 < i1 := by
                by_contra! hle
                rcases eq_or_lt_of_le hle with rfl | hlt
                · rw [← h0eq, ← h1eq] at hp0p1; exact lt_irrefl _ hp0p1
                · have := x_lt_of_pairwise hpair hlt hi0
                  rw [h0eq, h1eq] at this; linarith
              rw [← hqeq, ← h0eq, ← h1eq]
              exact hncol iq i0 i1 hiq0 hi01 hi1
            have hsublist_of_mem_x : ∀ (a : List (ℝ × ℝ)),
                a.Pairwise (fun x y => x.1 < y.1) → (∀ x ∈ a, x ∈ pts) → a.Sublist pts :=
              fun a ha_pair ha_mem => sublist_of_pairwise_subset pts a hpair ha_pair ha_mem
            rcases lt_or_gt_of_ne hne_slope with hlt | hgt
            · -- Extend cup by p1 to get a k-cup!
              left
              let cup' := cup ++ [p1]
              have hpair' : cup'.Pairwise (fun a b => a.1 < b.1) := by
                rw [List.pairwise_append]
                refine ⟨hcup_is.1, by simp, ?_⟩
                intro a ha b hb
                simp only [List.mem_singleton] at hb; subst hb
                obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ha
                by_cases hlast : i = cup.length - 1
                · have : cup[i] = p0 := by subst hlast; exact hcup_eq
                  rw [this]; exact hp0p1
                · have h1 := x_lt_of_pairwise hcup_is.1 (by omega : i < cup.length - 1) (by omega)
                  rw [hcup_eq] at h1; linarith
              refine ⟨cup', hsublist_of_mem_x cup' hpair' ?_, by simp [cup', hcup_len]; omega, hpair', ?_⟩
              · intro x hx
                rcases List.mem_append.mp hx with hx | hx
                · exact hcup_sub.subset hx
                · simp only [List.mem_singleton] at hx; subst hx
                  exact (hsubR.trans hRsub).subset (List.getElem_mem _)
              · intro i hi
                simp only [cup', List.length_append, List.length_singleton] at hi
                by_cases hi2 : i + 2 < cup.length
                · have h0 : cup'[i] = cup[i] := List.getElem_append_left (by omega)
                  have h1 : cup'[i + 1] = cup[i + 1] := List.getElem_append_left (by omega)
                  have h2 : cup'[i + 2] = cup[i + 2] := List.getElem_append_left hi2
                  rw [h0, h1, h2]
                  exact hcup_is.2 i hi2
                · have hi_eq : i = cup.length - 2 := by omega
                  have h0 : cup'[i] = q := by
                    rw [List.getElem_append_left (by omega)]; simp [q, hi_eq]
                  have h1 : cup'[i + 1] = p0 := by
                    rw [List.getElem_append_left (by omega)]
                    simpa [show i + 1 = cup.length - 1 by omega] using hcup_eq
                  have h2 : cup'[i + 2] = p1 := by
                    rw [List.getElem_append_right (by omega)]
                    simp [show i + 2 - cup.length = 0 by omega]
                  rw [h0, h1, h2]; exact hlt
            · -- Extend sub by prepending q to get an l-cap!
              right
              let cap' := q :: sub
              have hpair' : cap'.Pairwise (fun a b => a.1 < b.1) := by
                rw [List.pairwise_cons]
                refine ⟨?_, hsubcap.1⟩
                intro b hb
                obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hb
                by_cases h0 : i = 0
                · subst h0; exact hqp0
                · have h1 := x_lt_of_pairwise hsubcap.1 (by omega : 0 < i) hi
                  linarith
              refine ⟨cap', hsublist_of_mem_x cap' hpair' ?_, by simp [cap', hsublen]; omega, hpair', ?_⟩
              · intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hcup_sub.subset (List.getElem_mem _)
                · exact (hsubR.trans hRsub).subset hx
              · intro i hi
                simp only [cap', List.length_cons] at hi
                cases i with
                | zero => simpa [cap', q, p0, p1] using hgt
                | succ i => exact hsubcap.2 i (by omega)

private lemma planar_nonempty_cardSet (n : ℕ) : (cardSet 2 n).Nonempty := by
  by_cases hn2 : n < 2
  · refine ⟨n, fun X _ hcard => ?_⟩
    obtain ⟨Y, hYX, hYc⟩ := Finset.exists_subset_card_eq hcard
    refine ⟨Y, hYX, hYc, ?_⟩
    have hcard1 : Y.card ≤ 1 := by omega
    have : Subsingleton ↥(Y : Set (E 2)) :=
      ⟨fun a b => Subtype.ext (Finset.card_le_one.mp hcard1 a.1 a.2 b.1 b.2)⟩
    exact Subsingleton.convexIndependent _
  · refine ⟨Nat.choose (2 * n - 4) (n - 2) + 1, fun X hX hcard => ?_⟩
    classical
    obtain ⟨u, hu0, hu_inj⟩ := planar_distinct_x X
    -- Build orthonormal-like basis (u, v) where v = (-u 1, u 0)
    let v : E 2 := (EuclideanSpace.equiv (Fin 2) ℝ).symm ![-(u 1), u 0]
    let f : E 2 →ₗ[ℝ] (ℝ × ℝ) :=
      { toFun := fun p => (inner ℝ p u, inner ℝ p v)
        map_add' := fun x y => by simp [inner_add_left]
        map_smul' := fun c x => by simp [inner_smul_left] }
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have h1 : inner ℝ (x - y) u = 0 := by
        have := congrArg Prod.fst hxy; simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [inner_sub_left, this, sub_self]
      have h2 : inner ℝ (x - y) v = 0 := by
        have := congrArg Prod.snd hxy; simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [inner_sub_left, this, sub_self]
      have hu_sq : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
        intro h
        apply hu0; ext i
        fin_cases i
        · simp; nlinarith [sq_nonneg (u 1)]
        · simp; nlinarith [sq_nonneg (u 0)]
      have h1' : (x - y) 0 * u 0 + (x - y) 1 * u 1 = 0 := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm] using h1
      have h2' : (x - y) 0 * (-(u 1)) + (x - y) 1 * u 0 = 0 := by
        simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, v, mul_comm] using h2
      have hdx : (x - y) 0 = 0 := by
        have : (u 0 ^ 2 + u 1 ^ 2) * (x - y) 0 = 0 := by linear_combination u 0 * h1' - u 1 * h2'
        exact (mul_eq_zero.mp this).resolve_left hu_sq
      have hdy : (x - y) 1 = 0 := by
        have : (u 0 ^ 2 + u 1 ^ 2) * (x - y) 1 = 0 := by linear_combination u 1 * h1' + u 0 * h2'
        exact (mul_eq_zero.mp this).resolve_left hu_sq
      ext i; fin_cases i
      · exact sub_eq_zero.mp hdx
      · exact sub_eq_zero.mp hdy
    let S : Finset (ℝ × ℝ) := X.image f
    let leX : (ℝ × ℝ) → (ℝ × ℝ) → Bool := fun a b => decide (a.1 ≤ b.1)
    obtain ⟨pts, hpts_perm, hle_b⟩ : ∃ pts : List (ℝ × ℝ),
        pts.Perm S.toList ∧ pts.Pairwise (fun a b => leX a b = true) :=
      ⟨S.toList.mergeSort leX, List.mergeSort_perm S.toList leX,
        List.pairwise_mergeSort
          (fun a b c hab hbc => by
            simp only [leX, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
          (fun a b => by
            simp only [leX, Bool.or_eq_true, decide_eq_true_eq]; exact le_total a.1 b.1)
          S.toList⟩
    have hpts_nd : pts.Nodup := hpts_perm.nodup_iff.mpr S.nodup_toList
    have hpts_len : pts.length = X.card := by
      rw [hpts_perm.length_eq, Finset.length_toList, Finset.card_image_of_injective X hf_inj]
    have hpts_mem : ∀ p ∈ pts, p ∈ S := fun p hp => Finset.mem_toList.mp (hpts_perm.mem_iff.mp hp)
    have hpts_pair : pts.Pairwise (fun a b => a.1 < b.1) := by
      have hle : pts.Pairwise (fun a b => a.1 ≤ b.1) :=
        hle_b.imp fun h => by simpa [leX] using h
      refine (hle.and hpts_nd).imp_of_mem fun {a b} ha hb ⟨hab, hne⟩ => ?_
      refine lt_of_le_of_ne hab fun heq => hne ?_
      obtain ⟨pa, hpaX, rfl⟩ := Finset.mem_image.mp (hpts_mem a ha)
      obtain ⟨pb, hpbX, rfl⟩ := Finset.mem_image.mp (hpts_mem b hb)
      have : pa = pb := hu_inj hpaX hpbX heq
      rw [this]
    have hpts_ncol : ∀ i j r : ℕ, (hi : i < j) → (hj : j < r) → (hr : r < pts.length) →
        (pts[j].2 - pts[i].2) / (pts[j].1 - pts[i].1) ≠
        (pts[r].2 - pts[j].2) / (pts[r].1 - pts[j].1) := by
      intro i j r hij hjr hr hslope
      obtain ⟨pa, hpaX, hfa⟩ := Finset.mem_image.mp (hpts_mem pts[i] (List.getElem_mem _))
      obtain ⟨pb, hpbX, hfb⟩ := Finset.mem_image.mp (hpts_mem pts[j] (List.getElem_mem _))
      obtain ⟨pc, hpcX, hfc⟩ := Finset.mem_image.mp (hpts_mem pts[r] (List.getElem_mem _))
      have hdx1 : 0 < pts[j].1 - pts[i].1 := sub_pos.mpr (x_lt_of_pairwise hpts_pair hij (by omega))
      have hdx2 : 0 < pts[r].1 - pts[j].1 := sub_pos.mpr (x_lt_of_pairwise hpts_pair hjr hr)
      have hcross : (pts[j].2 - pts[i].2) * (pts[r].1 - pts[j].1) =
          (pts[r].2 - pts[j].2) * (pts[j].1 - pts[i].1) := by
        rwa [div_eq_div_iff hdx1.ne' hdx2.ne'] at hslope
      have hab : pa ≠ pb := fun h => by
        have h1 : pts[i].1 = pts[j].1 := congrArg Prod.fst (hfa.symm.trans (h ▸ hfb))
        linarith
      have hbc : pb ≠ pc := fun h => by
        have h1 : pts[j].1 = pts[r].1 := congrArg Prod.fst (hfb.symm.trans (h ▸ hfc))
        linarith
      have hac : pa ≠ pc := fun h => by
        have h1 : pts[i].1 = pts[r].1 := congrArg Prod.fst (hfa.symm.trans (h ▸ hfc))
        linarith
      let T : Finset (E 2) := {pa, pb, pc}
      have hTX : T ⊆ X := by
        intro z hz; simp only [T, Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      have hTc : T.card ≤ 3 := by
        exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
          ((Finset.card_insert_le _ _).trans (by simp)) 1)
      have hTgp := hX T hTX hTc
      let a' : ↥(T : Set (E 2)) := ⟨pa, by simp [T]⟩
      let b' : ↥(T : Set (E 2)) := ⟨pb, by simp [T]⟩
      let c' : ↥(T : Set (E 2)) := ⟨pc, by simp [T]⟩
      let w : ↥(T : Set (E 2)) → ℝ := fun z =>
        if z = a' then pts[r].1 - pts[j].1
        else if z = b' then -(pts[r].1 - pts[i].1)
        else pts[j].1 - pts[i].1
      have hwsum : ∑ z ∈ Finset.univ, w z = 0 := by
        have huniv : (Finset.univ : Finset ↥(T : Set (E 2))) = {a', b', c'} := by
          ext ⟨z, hz⟩
          simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
            true_iff, a', b', c']
          simpa [T] using hz
        have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
        have hac' : a' ≠ c' := fun h => hac (congrArg Subtype.val h)
        have hbc' : b' ≠ c' := fun h => hbc (congrArg Subtype.val h)
        rw [huniv, Finset.sum_insert (by simp [hab', hac']),
          Finset.sum_insert (by simp [hbc']), Finset.sum_singleton]
        simp [w, hab'.symm, hac'.symm, hbc'.symm]
      have hcomb : ∑ z ∈ Finset.univ, w z • (z : E 2) = 0 := by
        apply hf_inj
        rw [map_sum, map_zero]
        have huniv : (Finset.univ : Finset ↥(T : Set (E 2))) = {a', b', c'} := by
          ext ⟨z, hz⟩
          simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, Subtype.mk.injEq,
            true_iff, a', b', c']
          simpa [T] using hz
        have hab' : a' ≠ b' := fun h => hab (congrArg Subtype.val h)
        have hac' : a' ≠ c' := fun h => hac (congrArg Subtype.val h)
        have hbc' : b' ≠ c' := fun h => hbc (congrArg Subtype.val h)
        rw [huniv, Finset.sum_insert (by simp [hab', hac']),
          Finset.sum_insert (by simp [hbc']), Finset.sum_singleton]
        simp only [map_smul, w, if_true, if_neg hab'.symm, if_neg hac'.symm, if_neg hbc'.symm]
        change (pts[r].1 - pts[j].1) • f pa + ((-(pts[r].1 - pts[i].1)) • f pb +
          (pts[j].1 - pts[i].1) • f pc) = (0, 0)
        rw [hfa, hfb, hfc]
        apply Prod.ext
        · simp; ring
        · simp; linarith
      have hw0 := affineIndependent_iff.mp hTgp Finset.univ w hwsum hcomb a' (Finset.mem_univ a')
      simp [w] at hw0
      linarith
    have hchoose_lt : Nat.choose (n + n - 4) (n - 2) < pts.length := by
      rw [hpts_len, show n + n = 2 * n by omega]; omega
    -- Extract either an n-cup or an n-cap, and show any separated list is convex independent
    have hfinish : ∀ sub : List (ℝ × ℝ), sub.Sublist pts → sub.length = n →
        (∀ i : ℕ, (hi : i < sub.length) →
          ∃ φ : (ℝ × ℝ) →ₗ[ℝ] ℝ, ∀ j : ℕ, (hj : j < sub.length) → j ≠ i →
            φ sub[i] < φ sub[j]) →
        HasConvexSubset n X := by
      intro sub hsub hsublen hsep
      have hsub_nd : sub.Nodup := hpts_nd.sublist hsub
      let Y := X.filter (fun p => f p ∈ sub)
      have hYX : Y ⊆ X := Finset.filter_subset _ _
      have hYf : Y.image f = sub.toFinset := by
        ext q
        simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset, Y]
        constructor
        · rintro ⟨p, ⟨_, hp⟩, rfl⟩; exact hp
        · intro hq
          obtain ⟨p, hpX, rfl⟩ := Finset.mem_image.mp (hpts_mem q (hsub.subset hq))
          exact ⟨p, ⟨hpX, hq⟩, rfl⟩
      have hYc : Y.card = n := by
        rw [← Finset.card_image_of_injective Y hf_inj, hYf, List.toFinset_card_of_nodup hsub_nd, hsublen]
      refine ⟨Y, hYX, hYc, ?_⟩
      intro s y hy
      by_contra hy_not
      have hy_sub : f y.1 ∈ sub := (Finset.mem_filter.mp y.2).2
      obtain ⟨i, hi, hfi⟩ := List.mem_iff_getElem.mp hy_sub
      obtain ⟨φ, hφ⟩ := hsep i hi
      let ψ : E 2 →ₗ[ℝ] ℝ := φ.comp f
      have hgt : ∀ z ∈ (↑) '' s, ψ y.1 < ψ z := by
        rintro _ ⟨z, hz, rfl⟩
        have hzy : z ≠ y := fun h => hy_not (h ▸ hz)
        have hz_sub : f z.1 ∈ sub := (Finset.mem_filter.mp z.2).2
        obtain ⟨j, hj, hfj⟩ := List.mem_iff_getElem.mp hz_sub
        have hji : j ≠ i := by
          intro h; subst h
          have : f z.1 = f y.1 := hfj.symm.trans hfi
          exact hzy (Subtype.ext (hf_inj this))
        change φ (f y.1) < φ (f z.1)
        rw [← hfi, ← hfj]
        exact hφ j hj hji
      have hmem_gt : ψ y.1 < ψ y.1 := by
        have hconv : Convex ℝ {z : E 2 | ψ y.1 < ψ z} := by
          intro a ha b hb s t hs ht hst
          change ψ y.1 < ψ (s • a + t • b)
          rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
          have ha' : ψ y.1 < ψ a := ha
          have hb' : ψ y.1 < ψ b := hb
          rcases eq_or_lt_of_le hs with rfl | hs'
          · have ht1 : t = 1 := by linarith
            rw [ht1]; linarith
          · have h1 : s * ψ y.1 < s * ψ a := mul_lt_mul_of_pos_left ha' hs'
            have h2 : t * ψ y.1 ≤ t * ψ b := mul_le_mul_of_nonneg_left hb'.le ht
            have h3 : (s + t) * ψ y.1 = ψ y.1 := by rw [hst, one_mul]
            linarith
        exact (convexHull_min hgt hconv) hy
      exact lt_irrefl _ hmem_gt
    rcases cap_cup_exists (n + n) n n (by omega) (by omega) rfl pts hpts_pair hpts_ncol hchoose_lt with
      ⟨sub, hsub, hsublen, hcup⟩ | ⟨sub, hsub, hsublen, hcap⟩
    · refine hfinish sub hsub hsublen fun i hi => ?_
      obtain ⟨m, hm⟩ := isCup_strict_above_line hcup hi
      refine ⟨{ toFun := fun p => p.2 - m * p.1
                map_add' := fun a b => by simp; ring
                map_smul' := fun c a => by simp; ring }, fun j hj hne => ?_⟩
      have := hm j hj hne
      change sub[i].2 - m * sub[i].1 < sub[j].2 - m * sub[j].1
      linarith
    · refine hfinish sub hsub hsublen fun i hi => ?_
      obtain ⟨m, hm⟩ := isCap_strict_below_line hcap hi
      refine ⟨{ toFun := fun p => m * p.1 - p.2
                map_add' := fun a b => by simp; ring
                map_smul' := fun c a => by simp; ring }, fun j hj hne => ?_⟩
      have := hm j hj hne
      change m * sub[i].1 - sub[i].2 < m * sub[j].1 - sub[j].2
      linarith

private lemma nonempty_cardSet_ge_two {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (cardSet k n).Nonempty := by
  induction k, hk using Nat.le_induction with
  | base => exact planar_nonempty_cardSet n
  | succ k hk ih => exact ih.mono (cardSet_subset_succ (by omega) n)

end Erdos651H2

theorem OMA.solution : OMA.R_Erdos651_erdos_651_variants_subexponential_R1.H2 := by
  intro k n hk
  unfold Erdos651.f
  exact csInf_le_csInf (OrderBot.bddBelow _)
    (Erdos651H2.nonempty_cardSet_ge_two (by omega) n)
    (Erdos651H2.cardSet_subset_succ (by omega) n)
