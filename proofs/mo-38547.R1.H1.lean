import OMAReductions.R_mo_38547_R1
import Mathlib

/-
Portions copyright (c) 2026 Juan Pablo Traverso Gianini.
The Cauchy–Binet and incidence-minor lemmas and the spanning-tree indexing
are adapted from MatrixTreeLib/MatrixTree.lean in jtraverso/matrix-tree,
under the Apache License, Version 2.0.
https://github.com/jtraverso/matrix-tree
The marked-row identity uses the bipartition of each spanning tree.
-/

open SimpleGraph Matrix Finset

namespace MatrixTree

theorem det_mul_eq_sum_fun {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ p : Fin m → Fin k, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', mul_apply, prod_univ_sum, Fintype.piFinset_univ, mul_sum, sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib, mul_assoc]

theorem det_submatrix_eq_zero_of_not_injective {R : Type*} [CommRing R] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) R) (p : Fin m → Fin k) (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by
  simp only [Function.Injective, not_forall] at hp
  obtain ⟨i, j, hij, hne⟩ := hp
  exact det_zero_of_column_eq hne (fun l => by simp [hij])

theorem sum_perm_eq_det {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) (e : Fin m → Fin k) :
    ∑ τ : Equiv.Perm (Fin m), (A.submatrix id (e ∘ τ)).det * ∏ i, B (e (τ i)) i =
      (A.submatrix id e).det * (B.submatrix e id).det := by
  have h : ∀ τ : Equiv.Perm (Fin m), A.submatrix id (e ∘ τ) = (A.submatrix id e).submatrix id τ :=
    fun τ => rfl
  simp only [h, det_permute', det_apply' (B.submatrix e id), mul_sum, submatrix_apply, id]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/-- **Cauchy–Binet formula.** `det (A * B) = ∑_{|S| = m} det A[·, S] * det B[S, ·]`, where the
columns of `A` and the rows of `B` indexed by `S` are taken in increasing order. -/
theorem cauchy_binet {R : Type*} [CommRing R] {m k : ℕ} (A : Matrix (Fin m) (Fin k) R)
    (B : Matrix (Fin k) (Fin m) R) :
    (A * B).det = ∑ S : {S : Finset (Fin k) // S.card = m},
      (A.submatrix id (S.1.orderEmbOfFin S.2)).det *
        (B.submatrix (S.1.orderEmbOfFin S.2) id).det := by
  classical
  set F : (Fin m → Fin k) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  rw [det_mul_eq_sum_fun]
  have h1 : ∑ p : Fin m → Fin k, F p = ∑ p ∈ univ.filter Function.Injective, F p := by
    refine (Finset.sum_subset (filter_subset _ _) fun p _ hp => ?_).symm
    simp only [mem_filter, mem_univ, true_and] at hp
    simp [hF, det_submatrix_eq_zero_of_not_injective A p hp]
  have h2 : ∑ p ∈ univ.filter Function.Injective, F p =
      ∑ p : {p : Fin m → Fin k // Function.Injective p}, F p.1 :=
    Finset.sum_subtype _ (by simp) F
  let g : (Σ _ : {S : Finset (Fin k) // S.card = m}, Equiv.Perm (Fin m)) →
      {p : Fin m → Fin k // Function.Injective p} := fun x =>
    ⟨x.1.1.orderEmbOfFin x.1.2 ∘ x.2, (x.1.1.orderEmbOfFin x.1.2).injective.comp x.2.injective⟩
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨⟨S, hS⟩, τ⟩ ⟨⟨S', hS'⟩, τ'⟩ h
      simp only [g, Subtype.mk.injEq] at h
      have hSS : S = S' := by
        have := congrArg Set.range h
        rw [Set.range_comp, Set.range_comp, Equiv.range_eq_univ, Equiv.range_eq_univ,
          Set.image_univ, Set.image_univ, range_orderEmbOfFin, range_orderEmbOfFin] at this
        exact_mod_cast this
      subst hSS
      have : τ = τ' := by
        ext i
        have := congrFun h i
        simp only [Function.comp_apply] at this
        exact congrArg Fin.val ((S.orderEmbOfFin hS).injective this)
      subst this
      rfl
    · rintro ⟨p, hp⟩
      have hc : (univ.image p).card = m := by
        rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
      have hmem : ∀ i, p i ∈ univ.image p := fun i => mem_image_of_mem p (mem_univ i)
      let t : Fin m → Fin m := fun i => ((univ.image p).orderIsoOfFin hc).symm ⟨p i, hmem i⟩
      have ht : ∀ i, (univ.image p).orderEmbOfFin hc (t i) = p i := by
        intro i
        rw [← coe_orderIsoOfFin_apply]
        simp [t]
      have htinj : Function.Injective t := by
        intro i j hij
        apply hp
        rw [← ht i, ← ht j, hij]
      refine ⟨⟨⟨univ.image p, hc⟩, Equiv.ofBijective t (Finite.injective_iff_bijective.mp htinj)⟩,
        ?_⟩
      ext i
      simp [g, ht]
  rw [h1, h2, ← hg.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun S _ => ?_
  exact sum_perm_eq_det A B (S.1.orderEmbOfFin S.2)

section Incidence
variable {V : Type*}

/-- The first endpoint of an (unordered) pair. -/
noncomputable def tl (e : Sym2 V) : V := (Quot.out e).1
/-- The second endpoint of an (unordered) pair. -/
noncomputable def hd (e : Sym2 V) : V := (Quot.out e).2

theorem mk_tl_hd (e : Sym2 V) : s(tl e, hd e) = e := Quot.out_eq e

theorem tl_ne_hd {e : Sym2 V} (he : ¬ e.IsDiag) : tl e ≠ hd e := by
  intro h; apply he; rw [← mk_tl_hd e, Sym2.mk_isDiag_iff]; exact h

theorem mem_iff_tl_or_hd {e : Sym2 V} {x : V} : x ∈ e ↔ x = tl e ∨ x = hd e := by
  conv_lhs => rw [← mk_tl_hd e]
  exact Sym2.mem_iff

variable [DecidableEq V]

/-- Oriented incidence coefficient: `1` at the first endpoint, `-1` at the second one. -/
noncomputable def inc (e : Sym2 V) (x : V) : ℤ :=
  if x = tl e then 1 else if x = hd e then -1 else 0

theorem inc_tl (e : Sym2 V) : inc e (tl e) = 1 := by simp [inc]

theorem inc_hd {e : Sym2 V} (he : ¬ e.IsDiag) : inc e (hd e) = -1 := by
  simp [inc, (tl_ne_hd he).symm]

theorem inc_of_not_mem {e : Sym2 V} {x : V} (hx : x ∉ e) : inc e x = 0 := by
  rw [mem_iff_tl_or_hd, not_or] at hx
  simp [inc, hx.1, hx.2]

theorem mem_of_inc_ne_zero {e : Sym2 V} {x : V} (hx : inc e x ≠ 0) : x ∈ e := by
  by_contra h; exact hx (inc_of_not_mem h)

theorem isUnit_inc {e : Sym2 V} (he : ¬ e.IsDiag) {x : V} (hx : x ∈ e) : IsUnit (inc e x) := by
  rcases mem_iff_tl_or_hd.mp hx with rfl | rfl
  · rw [inc_tl]; exact isUnit_one
  · rw [inc_hd he]; exact isUnit_one.neg

theorem inc_mul_self {e : Sym2 V} (he : ¬ e.IsDiag) (x : V) :
    inc e x * inc e x = if x ∈ e then 1 else 0 := by
  split_ifs with hx
  · rcases mem_iff_tl_or_hd.mp hx with rfl | rfl
    · rw [inc_tl]; norm_num
    · rw [inc_hd he]; norm_num
  · rw [inc_of_not_mem hx, mul_zero]

theorem inc_mul_inc_of_ne {e : Sym2 V} (he : ¬ e.IsDiag) {x y : V} (hxy : x ≠ y) (hx : x ∈ e)
    (hy : y ∈ e) : inc e x * inc e y = -1 := by
  rcases mem_iff_tl_or_hd.mp hx with rfl | rfl <;> rcases mem_iff_tl_or_hd.mp hy with rfl | rfl
  · exact absurd rfl hxy
  · rw [inc_tl, inc_hd he]; norm_num
  · rw [inc_tl, inc_hd he]; norm_num
  · exact absurd rfl hxy
end Incidence

theorem det_eq_prod_diag_of_lt {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (M : Matrix ι ι R) (b : ι → ℕ) (h : ∀ i j, M i j ≠ 0 → i = j ∨ b i < b j) :
    M.det = ∏ i, M i i := by
  rw [det_apply', Finset.sum_eq_single 1]
  · simp
  · intro σ _ hσ
    by_contra hne
    have hall : ∀ i, M (σ i) i ≠ 0 := fun i hi =>
      hne (by rw [Finset.prod_eq_zero (f := fun j => M (σ j) j) (mem_univ i) hi, mul_zero])
    have hle : ∀ i, b (σ i) ≤ b i := fun i =>
      (h _ _ (hall i)).elim (fun e => by rw [e]) le_of_lt
    obtain ⟨i0, hi0⟩ : ∃ i, σ i ≠ i := by
      by_contra hc; push Not at hc; exact hσ (Equiv.ext hc)
    have hlt : b (σ i0) < b i0 := (h _ _ (hall i0)).resolve_left hi0
    have : ∑ i, b (σ i) < ∑ i, b i := Finset.sum_lt_sum (fun i _ => hle i) ⟨i0, mem_univ _, hlt⟩
    rw [Equiv.sum_comp σ b] at this
    exact lt_irrefl _ this
  · simp

section Key
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The square incidence matrix of a family of edges indexed by the vertices other than `v`. -/
noncomputable def incMat (v : V) (g : {u // u ≠ v} → Sym2 V) :
    Matrix {u // u ≠ v} {u // u ≠ v} ℤ :=
  Matrix.of fun u w => inc (g w) u

theorem fromEdgeSet_adj_tl_hd (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag)
    (w : {u // u ≠ v}) : (fromEdgeSet (Set.range g)).Adj (tl (g w)) (hd (g w)) := by
  rw [fromEdgeSet_adj, mk_tl_hd]
  exact ⟨⟨w, rfl⟩, tl_ne_hd (hg w)⟩

theorem det_incMat_eq_zero_of_not_injective (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ¬ Function.Injective g) : (incMat v g).det = 0 := by
  simp only [Function.Injective, not_forall] at hg
  obtain ⟨i, j, hij, hne⟩ := hg
  exact det_zero_of_column_eq hne (fun l => by simp [incMat, hij])

theorem det_incMat_eq_zero_of_not_reachable (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (u : V) (hu : ¬ (fromEdgeSet (Set.range g)).Reachable v u) :
    (incMat v g).det = 0 := by
  set H := fromEdgeSet (Set.range g)
  have huv : u ≠ v := by rintro rfl; exact hu (Reachable.refl _)
  rw [← exists_vecMul_eq_zero_iff]
  refine ⟨fun x => if H.Reachable u x then 1 else 0, ?_, ?_⟩
  · intro hc
    have := congrFun hc ⟨u, huv⟩
    simp at this
  · ext w
    simp only [vecMul, dotProduct, incMat, of_apply, Pi.zero_apply, ite_mul, one_mul, zero_mul]
    have hadj := fromEdgeSet_adj_tl_hd v g hg w
    by_cases ha : H.Reachable u (tl (g w))
    · have hb : H.Reachable u (hd (g w)) := ha.trans hadj.reachable
      have hav : tl (g w) ≠ v := by rintro h; exact hu (h ▸ ha.symm)
      have hbv : hd (g w) ≠ v := by rintro h; exact hu (h ▸ hb.symm)
      rw [Fintype.sum_eq_add (⟨tl (g w), hav⟩ : {u // u ≠ v}) ⟨hd (g w), hbv⟩]
      · simp [ha, hb, inc_tl, inc_hd (hg w)]
      · intro h; exact tl_ne_hd (hg w) (congrArg Subtype.val h)
      · rintro ⟨x, hx⟩ ⟨h1, h2⟩
        have h1' : x ≠ tl (g w) := fun h => h1 (Subtype.ext h)
        have h2' : x ≠ hd (g w) := fun h => h2 (Subtype.ext h)
        rw [inc_of_not_mem (by rw [mem_iff_tl_or_hd]; tauto)]
        simp
    · refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with hx
      · apply inc_of_not_mem
        rw [mem_iff_tl_or_hd]
        rintro (h | h)
        · exact ha (h ▸ hx)
        · exact ha (hx.trans (h ▸ hadj.symm.reachable))
      · rfl

theorem isUnit_det_incMat_of_isTree (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (hT : (fromEdgeSet (Set.range g)).IsTree) :
    IsUnit (incMat v g).det := by
  set H := fromEdgeSet (Set.range g)
  set d : V → ℕ := fun x => H.dist v x with hd_def
  have hadj := fromEdgeSet_adj_tl_hd v g hg
  have hne : ∀ w, d (tl (g w)) ≠ d (hd (g w)) := fun w => hT.dist_ne_of_adj v (hadj w)
  let low : {u // u ≠ v} → V := fun w =>
    if d (tl (g w)) < d (hd (g w)) then hd (g w) else tl (g w)
  have hlow : ∀ w, ∀ x ∈ g w, x = low w ∨ d x < d (low w) := by
    intro w x hx
    have := hne w
    rcases mem_iff_tl_or_hd.mp hx with rfl | rfl <;> simp only [low] <;> split_ifs <;>
      first | exact Or.inl rfl | (right; omega)
  have hlow_mem : ∀ w, low w ∈ g w := by
    intro w; simp only [low]; split_ifs
    · exact mem_iff_tl_or_hd.mpr (Or.inr rfl)
    · exact mem_iff_tl_or_hd.mpr (Or.inl rfl)
  have hlow_ne : ∀ w, low w ≠ v := by
    intro w h
    have := hne w
    have h0 : d v = 0 := dist_self
    simp only [low] at h
    split_ifs at h with hlt
    · rw [← h] at h0; omega
    · rw [← h] at h0; omega
  let lam : {u // u ≠ v} → {u // u ≠ v} := fun w => ⟨low w, hlow_ne w⟩
  have hsurj : Function.Surjective lam := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hp⟩ := hT.connected.exists_walk_length_eq_dist x v
    cases p with
    | nil => exact absurd rfl hx
    | @cons _ y _ h q =>
      have hq := dist_le q
      have hdy : d y < d x := by
        simp only [hd_def, dist_comm (u := v)]
        rw [Walk.length_cons] at hp
        omega
      rw [fromEdgeSet_adj] at h
      obtain ⟨⟨w, hw⟩, -⟩ := h
      refine ⟨w, Subtype.ext ?_⟩
      have hx' : x ∈ g w := by rw [hw]; exact Sym2.mem_mk_left _ _
      have hy' : y ∈ g w := by rw [hw]; exact Sym2.mem_mk_right _ _
      rcases hlow w y hy' with h1 | h1
      · rcases hlow w x hx' with h2 | h2
        · exact h2.symm
        · rw [← h1] at h2; omega
      · rcases hlow w x hx' with h2 | h2
        · exact h2.symm
        · -- both endpoints differ from low w, impossible since low w ∈ {x, y}
          have hm := hlow_mem w
          rw [hw, Sym2.mem_iff] at hm
          rcases hm with hm | hm
          · rw [hm] at h2; omega
          · rw [hm] at h1; omega
  let π := Equiv.ofBijective lam ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  have hπ : ∀ x, low (π.symm x) = x.1 := fun x =>
    congrArg Subtype.val (π.apply_symm_apply x)
  have hdet := det_permute' π.symm (incMat v g)
  have hdiag := det_eq_prod_diag_of_lt ((incMat v g).submatrix id π.symm) (fun x => d x.1) (by
    intro u x hux
    simp only [submatrix_apply, id, incMat, of_apply] at hux
    rcases hlow _ _ (mem_of_inc_ne_zero hux) with h | h
    · left; exact Subtype.ext (h.trans (hπ x))
    · right; rw [hπ x] at h; exact h)
  have hunit : IsUnit ((incMat v g).submatrix id π.symm).det := by
    rw [hdiag]
    refine IsUnit.prod_iff.mpr fun x _ => ?_
    simp only [submatrix_apply, id, incMat, of_apply]
    apply isUnit_inc (hg _)
    rw [← hπ x]; exact hlow_mem _
  rw [hdet] at hunit
  exact (isUnit_of_mul_isUnit_right hunit)

theorem card_ne_add_one [Finite V] (v : V) : Nat.card {u // u ≠ v} + 1 = Nat.card V := by
  classical
  have := Fintype.ofFinite V
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  omega

theorem det_incMat_sq_of_isTree (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag)
    (hT : (fromEdgeSet (Set.range g)).IsTree) : (incMat v g).det ^ 2 = 1 := by
  rcases Int.isUnit_iff.mp (isUnit_det_incMat_of_isTree v g hg hT) with h | h <;>
    rw [h] <;> norm_num

theorem det_incMat_eq_zero_of_not_isTree (v : V) (g : {u // u ≠ v} → Sym2 V)
    (hg : ∀ w, ¬ (g w).IsDiag) (hT : ¬ (fromEdgeSet (Set.range g)).IsTree) :
    (incMat v g).det = 0 := by
  by_cases hinj : Function.Injective g
  · obtain ⟨u, hu⟩ : ∃ u, ¬ (fromEdgeSet (Set.range g)).Reachable v u := by
      by_contra hc
      push Not at hc
      apply hT
      rw [isTree_iff_connected_and_card]
      refine ⟨(connected_iff _).mpr ⟨fun x y => (hc x).symm.trans (hc y), ⟨v⟩⟩, ?_⟩
      have hdisj : Set.range g \ Sym2.diagSet = Set.range g := by
        refine sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_)
        rintro _ ⟨w, rfl⟩
        exact hg w
      rw [edgeSet_fromEdgeSet, hdisj, Nat.card_range_of_injective hinj]
      exact card_ne_add_one v
    exact det_incMat_eq_zero_of_not_reachable v g hg u hu
  · exact det_incMat_eq_zero_of_not_injective v g hinj

end Key


theorem lapMatrix_eq_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    G.lapMatrix ℤ x y = ∑ e ∈ G.edgeFinset, inc e x * inc e y := by
  simp only [lapMatrix, degMatrix, Matrix.sub_apply, adjMatrix_apply, diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [Finset.sum_congr rfl fun e he => inc_mul_self (G.not_isDiag_of_mem_edgeSet
      (mem_edgeFinset.mp he)) x, Finset.sum_boole, ← incidenceFinset_eq_filter,
      card_incidenceFinset_eq_degree]
    simp
  · have hzero : ∀ e, e ≠ s(x, y) → inc e x * inc e y = 0 := by
      intro e hne
      by_cases hx : x ∈ e
      · have hy : y ∉ e := fun hy => hne ((Sym2.mem_and_mem_iff hxy).mp ⟨hx, hy⟩)
        rw [inc_of_not_mem hy, mul_zero]
      · rw [inc_of_not_mem hx, zero_mul]
    by_cases hadj : G.Adj x y
    · rw [Finset.sum_eq_single s(x, y) (fun e _ hne => hzero e hne)
        (fun h => absurd (mem_edgeFinset.mpr hadj) h),
        inc_mul_inc_of_ne (G.not_isDiag_of_mem_edgeSet hadj) hxy (Sym2.mem_mk_left _ _)
          (Sym2.mem_mk_right _ _)]
      simp [hxy, hadj]
    · rw [Finset.sum_eq_zero fun e he => hzero e (by
        rintro rfl; exact hadj (mem_edgeFinset.mp he))]
      simp [hxy, hadj]

end MatrixTree

open Matrix SimpleGraph Finset
open scoped Classical
namespace BacherTransfer
open MatrixTree
private theorem add_self (x : ZMod 2) : x + x = 0 := (by decide : ∀ a : ZMod 2, a+a=0) x
private theorem mul_self (x : ZMod 2) : x * x = x := (by decide : ∀ a : ZMod 2, a*a=a) x

lemma color_on_edge {V : Type*} [Fintype V] [DecidableEq V] (v : V)
    (T : SimpleGraph V) (ht : T.IsTree) (e : Sym2 V) (he : ¬ e.IsDiag)
    (hadj : T.Adj (tl e) (hd e)) :
    (∑ i : {u // u ≠ v}, (T.dist v i : ZMod 2) * (inc e i : ZMod 2)) = 1 := by
  let f := fun i : V => (T.dist v i : ZMod 2) * (inc e i : ZMod 2)
  have hf : (∑ i, f i) = ∑ i : {u // u ≠ v}, f i := by
    rw [Fintype.sum_eq_add_sum_subtype_ne _ v]
    simp [f]
  change (∑ i : {u // u ≠ v}, f i) = 1
  rw [← hf, Fintype.sum_eq_add (tl e) (hd e) (tl_ne_hd he)]
  · dsimp [f]
    rw [inc_tl, inc_hd he]
    push_cast
    rcases ht.dist_eq_dist_add_one_of_adj v hadj with h | h <;> rw [h] <;> push_cast
    · ring
    · have hneg : (-1 : ZMod 2) = 1 := by decide
      linear_combination (norm := ring_nf) hneg
  · intro i hi
    have hzero := inc_of_not_mem (e := e) (x := i) (by simpa [mem_iff_tl_or_hd] using hi)
    simp [f, hzero]

lemma marked_tree_minor {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (g : {u // u ≠ v} → Sym2 V) (hg : ∀ w, ¬ (g w).IsDiag) (w : {u // u ≠ v}) :
    let M := (incMat v g).map (Int.castRingHom (ZMod 2))
    let T := fromEdgeSet (Set.range g)
    (M.updateRow w (fun _ => 1)).det * M.det =
      if T.IsTree then (T.dist v w : ZMod 2) else 0 := by
  classical
  intro M T
  have hdet : M.det = (Int.castRingHom (ZMod 2)) (incMat v g).det :=
    ((Int.castRingHom (ZMod 2)).map_det (incMat v g)).symm
  split_ifs with h
  · let x : {u // u ≠ v} → ZMod 2 := fun i => (T.dist v i : ZMod 2)
    have hx : x ᵥ* M = fun _ => 1 := by
      ext j
      exact color_on_edge v T h _ (hg j) (fromEdgeSet_adj_tl_hd v g hg j)
    rw [← hx, vecMul_eq_sum, det_updateRow_sum, smul_eq_mul, mul_assoc]
    have hu := det_incMat_sq_of_isTree v g hg h
    have hm : M.det * M.det = 1 := by
      rw [hdet]
      simpa only [map_pow, map_mul, map_one, sq] using congrArg (Int.castRingHom (ZMod 2)) hu
    rw [hm, mul_one]
  · have hz := det_incMat_eq_zero_of_not_isTree v g hg h
    have hzero : M.det = 0 := by
      rw [hdet, hz, map_zero]
    rw [hzero, mul_zero]

lemma marked_gram {ι κ : Type*} [Fintype κ] [DecidableEq ι]
    (A : Matrix ι κ (ZMod 2)) (v : ι) :
    (A.updateRow v (fun _ => 1)) * Aᵀ = (A * Aᵀ).updateRow v (A * Aᵀ).diag := by
  rw [Matrix.updateRow_mul]
  congr 1
  ext i
  simp [Matrix.vecMul, dotProduct, Matrix.mul_apply, mul_self]

end BacherTransfer


open Matrix SimpleGraph Finset
open scoped Classical
namespace BacherTransfer
open MatrixTree

lemma bit_transfer (n : ℕ) (G : SimpleGraph (Fin (n+1))) (w : Fin n) :
    let L := (G.lapMatrix (ZMod 2)).submatrix Fin.succ Fin.succ
    L.cramer L.diag w = ∑ H : {H : SimpleGraph (Fin (n+1)) // H ≤ G ∧ H.IsTree},
      (H.1.dist 0 w.succ : ZMod 2) := by
  classical
  intro L
  let v : Fin (n+1) := 0
  let φ := finSuccAboveEquiv v
  have hφ (i : Fin n) : (φ i).1 = i.succ := by simp [φ, v, finSuccAboveEquiv_apply]
  let ψ := (Fintype.equivFin G.edgeSet).symm
  let E : Finset (Fin (Fintype.card G.edgeSet)) → Set (Sym2 (Fin (n+1))) :=
    fun T => (fun j => (ψ j : Sym2 (Fin (n+1)))) '' T
  have hψinj : Function.Injective (fun j => (ψ j : Sym2 (Fin (n+1)))) :=
    Subtype.val_injective.comp ψ.injective
  have hE : ∀ T, (fromEdgeSet (E T)).edgeSet = E T := by
    intro T
    rw [edgeSet_fromEdgeSet]
    refine sdiff_eq_left.mpr (Set.disjoint_left.mpr ?_)
    rintro _ ⟨j, _, rfl⟩
    exact G.not_isDiag_of_mem_edgeSet (ψ j).2
  let A : Matrix (Fin n) (Fin (Fintype.card G.edgeSet)) (ZMod 2) :=
    Matrix.of fun i j => (inc (ψ j : Sym2 (Fin (n+1))) i.succ : ZMod 2)
  have hAA : L = A * Aᵀ := by
    ext i j
    have h := congrArg (Int.castRingHom (ZMod 2)) (lapMatrix_eq_sum G i.succ j.succ)
    simp only [map_sum, map_mul] at h
    rw [Finset.sum_subtype G.edgeFinset (p := (· ∈ G.edgeSet)) (by simp)] at h
    calc
      _ = (Int.castRingHom (ZMod 2)) (G.lapMatrix ℤ i.succ j.succ) := by
        simp [L, lapMatrix, degMatrix, SimpleGraph.adjMatrix_apply, diagonal_apply]
      _ = _ := h
      _ = _ := (Equiv.sum_comp ψ (fun e : G.edgeSet =>
        (inc (e : Sym2 (Fin (n+1))) i.succ : ZMod 2) * (inc e j.succ : ZMod 2))).symm
  let SType := {S : Finset (Fin (Fintype.card G.edgeSet)) // S.card = n}
  have hterm (S : SType) :
      ((A.updateRow w (fun _ => 1)).submatrix id (S.1.orderEmbOfFin S.2)).det *
        (Aᵀ.submatrix (S.1.orderEmbOfFin S.2) id).det =
        if (fromEdgeSet (E S.1)).IsTree then ((fromEdgeSet (E S.1)).dist v w.succ : ZMod 2) else 0 := by
    let g : {u // u ≠ v} → Sym2 (Fin (n+1)) := fun u => (ψ (S.1.orderEmbOfFin S.2 (φ.symm u)) : Sym2 _)
    have hg : ∀ u, ¬ (g u).IsDiag := fun u => G.not_isDiag_of_mem_edgeSet (ψ _).2
    have hrange : Set.range g = E S.1 := by
      ext e
      simp only [g, E, Set.mem_range, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨u, rfl⟩
        exact ⟨_, S.1.orderEmbOfFin_mem S.2 _, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        have : j ∈ Set.range (S.1.orderEmbOfFin S.2) := by rw [range_orderEmbOfFin]; exact hj
        obtain ⟨i, rfl⟩ := this
        exact ⟨φ i, by simp⟩
    let M := (incMat v g).map (Int.castRingHom (ZMod 2))
    have hsub : A.submatrix id (S.1.orderEmbOfFin S.2) = M.submatrix φ φ := by
      ext i j
      simp [A, M, incMat, g, hφ]
    have hsub' : (A.updateRow w (fun _ => 1)).submatrix id (S.1.orderEmbOfFin S.2) =
        (M.updateRow (φ w) (fun _ => 1)).submatrix φ φ := by
      rw [← Matrix.updateRow_submatrix_equiv M w (fun _ => 1)]
      rw [← hsub]
      ext i j
      simp [Matrix.updateRow_apply]
    rw [← transpose_submatrix, det_transpose, hsub', hsub, det_submatrix_equiv_self,
      det_submatrix_equiv_self, ← hrange, ← hφ w]
    exact marked_tree_minor v g hg (φ w)
  let F := {S : SType // (fromEdgeSet (E S.1)).IsTree}
  let Trees := {T : SimpleGraph (Fin (n+1)) // T ≤ G ∧ T.IsTree}
  have incl (S : F) : fromEdgeSet (E S.1.1) ≤ G := by
    intro a b hab
    rw [fromEdgeSet_adj] at hab
    obtain ⟨⟨j, _, hj⟩, _⟩ := hab
    rw [← mem_edgeSet, ← hj]
    exact (ψ j).2
  let mapTree : F → Trees := fun S => ⟨fromEdgeSet (E S.1.1), incl S, S.2⟩
  have hb : Function.Bijective mapTree := by
    constructor
    · intro S S' h
      have h1 := congrArg (fun H : Trees => H.1.edgeSet) h
      change (fromEdgeSet (E S.1.1)).edgeSet = (fromEdgeSet (E S'.1.1)).edgeSet at h1
      simp only [hE] at h1
      have h2 : (S.1.1 : Set _) = S'.1.1 := Set.image_injective.mpr hψinj h1
      exact Subtype.ext (Subtype.ext (Finset.coe_inj.mp h2))
    · rintro ⟨H, hle, hT⟩
      let T := univ.filter (fun j => (ψ j : Sym2 (Fin (n+1))) ∈ H.edgeSet)
      have hET : E T = H.edgeSet := by
        ext e
        simp only [E, T, Set.mem_image, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨j, hj, rfl⟩; exact hj
        · intro he
          refine ⟨ψ.symm ⟨e, edgeSet_mono hle he⟩, ?_, ?_⟩ <;> simp [he]
      have hcard : T.card = n := by
        have h1 := Nat.card_image_of_injective hψinj (T : Set _)
        have h2 := (isTree_iff_connected_and_card.mp hT).2
        change Nat.card (E T) = _ at h1
        rw [hET] at h1
        simp only [Nat.card_coe_set_eq, Set.ncard_coe_finset, Nat.card_fin] at h1 h2
        omega
      refine ⟨⟨⟨T, hcard⟩, ?_⟩, ?_⟩
      · change (fromEdgeSet (E T)).IsTree
        rw [hET, fromEdgeSet_edgeSet]; exact hT
      · apply Subtype.ext
        change fromEdgeSet (E T) = H
        rw [hET, fromEdgeSet_edgeSet]
  have hL : L.IsSymm := (G.isSymm_lapMatrix (ZMod 2)).submatrix Fin.succ
  calc
    L.cramer L.diag w = (L.updateRow w L.diag).det := by
      simpa only [hL.eq] using Matrix.cramer_transpose_apply L L.diag w
    _ = ((A.updateRow w fun _ => 1) * Aᵀ).det := by rw [hAA, marked_gram]
    _ = ∑ S : SType, if (fromEdgeSet (E S.1)).IsTree then
        ((fromEdgeSet (E S.1)).dist v w.succ : ZMod 2) else 0 := by
      rw [MatrixTree.cauchy_binet]
      exact Finset.sum_congr rfl fun S _ => hterm S
    _ = ∑ S : F, ((fromEdgeSet (E S.1.1)).dist v w.succ : ZMod 2) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (p := fun S : SType => (fromEdgeSet (E S.1)).IsTree)
        (univ.filter (fun S : SType => (fromEdgeSet (E S.1)).IsTree)) (by simp)
        (fun S : SType => ((fromEdgeSet (E S.1)).dist v w.succ : ZMod 2))
    _ = _ := (Equiv.ofBijective mapTree hb).sum_comp (fun H : Trees => (H.1.dist v w.succ : ZMod 2))

end BacherTransfer

theorem OMA.solution : OMA.R_mo_38547_R1.H1 := by
  classical
  intro n G _
  unfold OMA.S_mo_38547.output
  rw [List.ofFn_succ]
  congr 1
  · simp
  · congr 1
    funext w
    rw [BacherTransfer.bit_transfer]
    let s := Finset.univ.filter (fun T : SimpleGraph (Fin (n+1)) => T ≤ G ∧ T.IsTree)
    have hn : (∑ T ∈ s, T.dist 0 w.succ) =
        ∑ H : {H : SimpleGraph (Fin (n+1)) // H ≤ G ∧ H.IsTree}, H.1.dist 0 w.succ :=
      Finset.sum_subtype (p := fun T : SimpleGraph (Fin (n+1)) => T ≤ G ∧ T.IsTree)
        s (by simp [s]) _
    have hc := congrArg (Nat.cast : ℕ → ZMod 2) hn
    simp only [Nat.cast_sum] at hc
    rw [← hc, ← Nat.cast_sum]
    simp only [ZMod.natCast_eq_one_iff_odd, Nat.odd_iff]
    rfl
