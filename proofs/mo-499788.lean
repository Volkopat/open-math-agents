import OMAStatements.S_mo_499788
import Mathlib

/-!
# Strict off-diagonal bound for a tree's biadjacency Gram square root

Delete an edge separating the two vertices and compare the absolute values of the full
symmetric adjacency matrices before and after deletion. The squared Frobenius distance
is at most two. The two symmetric entries under study have equal squared size, and a
third row contributes strictly positively because the deleted edge changes its degree.
-/

open Matrix
open scoped MatrixOrder

namespace MO499HS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem trace_mul_psd {A B : Matrix ι ι ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (A * B).trace := by
  let S := CFC.sqrt B
  have hS : S.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self _ hB
  have h := (hA.posSemidef.conjTranspose_mul_mul_same S).trace_nonneg
  rw [hS.eq, Matrix.trace_mul_cycle, hSS] at h
  simpa [Matrix.trace_mul_comm B A] using h

omit [DecidableEq ι] in
private theorem sum_sq_eq_trace {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∑ i, ∑ j, A i j ^ 2) = (A * A).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : A j i = A i j := by simpa using hA.apply i j
  rw [hij, sq]

private theorem abs_cross {H K : Matrix ι ι ℝ} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (H * K).trace ≤ (CFC.abs H * CFC.abs K).trace := by
  have plus (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : 0 ≤ CFC.abs A + A := by
    rw [CFC.abs_add_self A hA.isSelfAdjoint, two_smul]
    exact add_nonneg (CFC.posPart_nonneg _) (CFC.posPart_nonneg _)
  have minus (A : Matrix ι ι ℝ) (hA : A.IsHermitian) : 0 ≤ CFC.abs A - A := by
    rw [CFC.abs_sub_self A hA.isSelfAdjoint, two_smul]
    exact add_nonneg (CFC.negPart_nonneg _) (CFC.negPart_nonneg _)
  have h₁ := trace_mul_psd (plus H hH) (minus K hK)
  have h₂ := trace_mul_psd (minus H hH) (plus K hK)
  simp only [add_mul, mul_add, sub_mul, mul_sub, Matrix.trace_add, Matrix.trace_sub] at h₁ h₂
  linarith

theorem sqrt_sq_frobenius_le (H K : Matrix ι ι ℝ) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    (∑ i, ∑ j, ((CFC.sqrt (H * H)) i j - (CFC.sqrt (K * K)) i j)^2) ≤
      ∑ i, ∑ j, (H i j - K i j)^2 := by
  have liftAbs (A : Matrix ι ι ℝ) (hA : A.IsHermitian) :
      CFC.sqrt (A * A) = CFC.abs A := by
    rw [CFC.abs, hA.isSelfAdjoint.star_eq]
  rw [liftAbs H hH, liftAbs K hK]
  change (∑ i, ∑ j, ((CFC.abs H - CFC.abs K) i j)^2) ≤ ∑ i, ∑ j, ((H-K) i j)^2
  rw [sum_sq_eq_trace ((CFC.abs_nonneg H).posSemidef.isHermitian.sub
      (CFC.abs_nonneg K).posSemidef.isHermitian), sum_sq_eq_trace (hH.sub hK)]
  simp only [sub_mul, mul_sub, Matrix.trace_sub, CFC.abs_mul_abs,
    hH.isSelfAdjoint.star_eq, hK.isSelfAdjoint.star_eq]
  linarith [abs_cross hH hK, abs_cross hK hH]

end MO499HS

open Matrix
open scoped MatrixOrder

namespace MO499Strict

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem diag_sq (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (w : ι) :
    (A * A) w w = ∑ z, (A w z)^2 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro z hz
  have hwz : A z w = A w z := by simpa using hA.apply w z
  rw [hwz, sq]

theorem sqrt_entry_lt_one (H K : Matrix ι ι ℝ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (w v i j : ι) (hij : i ≠ j) (hwi : w ≠ i) (hwj : w ≠ j)
    (hHv : H w v = 1) (hKv : K w v = 0)
    (hrow : ∀ z, z ≠ v → H w z = K w z)
    (hzero : CFC.sqrt (K * K) i j = 0)
    (hbound : (∑ a, ∑ b, (H a b - K a b)^2) ≤ 2) :
    |CFC.sqrt (H * H) i j| < 1 := by
  classical
  let A := CFC.sqrt (H * H)
  let B := CFC.sqrt (K * K)
  have hA : A.IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have hB : B.IsHermitian := (CFC.sqrt_nonneg _).posSemidef.isHermitian
  have square (T : Matrix ι ι ℝ) (hT : T.IsHermitian) :
      CFC.sqrt (T * T) * CFC.sqrt (T * T) = T * T := by
    apply CFC.sqrt_mul_sqrt_self
    simpa [hT.isSelfAdjoint.star_eq] using star_mul_self_nonneg T
  have hdiff : (K * K) w w < (H * H) w w := by
    rw [diag_sq K hK, diag_sq H hH]
    apply Finset.sum_lt_sum
    · intro z hz
      by_cases h : z = v
      · subst z
        simp [hHv, hKv]
      · rw [hrow z h]
    · exact ⟨v, Finset.mem_univ _, by simp [hHv, hKv]⟩
  have hw : ∃ z, A w z ≠ B w z := by
    by_contra! hall
    rw [← square K hK, ← square H hH] at hdiff
    change (B * B) w w < (A * A) w w at hdiff
    rw [diag_sq B hB, diag_sq A hA] at hdiff
    simp_rw [hall] at hdiff
    exact lt_irrefl _ hdiff
  obtain ⟨z,hz⟩ := hw
  let R (a : ι) := ∑ b, (A a b - B a b)^2
  have single (a b : ι) : (A a b - B a b)^2 ≤ R a :=
    Finset.single_le_sum (fun x _ => sq_nonneg (A a x - B a x)) (Finset.mem_univ b)
  have hRw : 0 < R w := lt_of_lt_of_le (sq_pos_of_ne_zero (sub_ne_zero.mpr hz)) (single w z)
  have three : R i + R j + R w ≤ ∑ a, R a := by
    have bound : ∑ a ∈ ({i,j,w} : Finset ι), R a ≤ ∑ a, R a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
    simpa [hij, hwi.symm, hwj.symm, add_assoc] using bound
  have htotal : ∑ a, R a ≤ 2 := (MO499HS.sqrt_sq_frobenius_le H K hH hK).trans hbound
  have Aji : A j i = A i j := by simpa using hA.apply i j
  have Bji : B j i = B i j := by simpa using hB.apply i j
  have hz0 : B i j = 0 := hzero
  have h1 := single i j
  have h2 := single j i
  rw [Aji, Bji] at h2
  rw [hz0, sub_zero] at h1 h2
  change |A i j| < 1
  nlinarith [sq_abs (A i j)]

end MO499Strict

open SimpleGraph
open scoped Sym2

namespace MO499

theorem treeCut {V : Type*} (G : SimpleGraph V) (hG : G.IsTree)
    {i j : V} (hne : i ≠ j) :
    ∃ (s : Set V) (a b : V), i ∈ s ∧ j ∉ s ∧ a ∈ s ∧ b ∉ s ∧ G.Adj a b ∧
      ∀ x ∈ s, ∀ y ∉ s, G.Adj x y → x = a ∧ y = b := by
  obtain ⟨p, hp⟩ := hG.connected.exists_isPath i j
  cases p with
  | nil => exact (hne rfl).elim
  | @cons u v w huv p =>
    let H := G.deleteEdges {s(i,v)}
    let S : Set V := {x | H.Reachable i x}
    have hu : i ∈ S := .refl _
    have hv : v ∉ S := isBridge_iff.mp
      ((isAcyclic_iff_forall_adj_isBridge.mp hG.isAcyclic) huv)
    have hvw : H.Reachable v j := reachable_deleteEdges_iff_exists_walk.mpr
      ⟨p, ((Walk.isTrail_cons huv p).mp hp.isTrail).2⟩
    refine ⟨S, i, v, hu, fun hw => hv (hw.trans hvw.symm), hu, hv, huv, ?_⟩
    intro x hx y hy hxy
    have he : s(x,y) = s(i,v) := by
      by_contra hn
      exact hy (hx.trans (deleteEdges_adj.mpr ⟨hxy, by simpa using hn⟩).reachable)
    rcases Sym2.eq_iff.mp he with h | ⟨rfl,rfl⟩
    · exact h
    · exact (hv hx).elim

end MO499

open SimpleGraph
open scoped BigOperators

namespace MO499

theorem eraseCut {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree) {i j : V} (hne : i ≠ j) (hnadj : ¬ G.Adj i j) :
    ∃ (K : Matrix V V ℝ) (s : Set V) (w v : V), K.IsHermitian ∧ i ∈ s ∧ j ∉ s ∧
      (∀ x ∈ s, ∀ y ∉ s, K x y = 0) ∧ w ≠ i ∧ w ≠ j ∧
      G.adjMatrix ℝ w v = 1 ∧ K w v = 0 ∧
      (∀ z, z ≠ v → G.adjMatrix ℝ w z = K w z) ∧
      (∑ x, ∑ y, (G.adjMatrix ℝ x y - K x y)^2) ≤ 2 := by
  classical
  obtain ⟨s,a,b,hi,hj,ha,hb,hab,hcross⟩ := treeCut G hG hne
  have hba := hab.symm
  have hneab := hab.ne
  let K : Matrix V V ℝ := fun x y =>
    if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then 0 else G.adjMatrix ℝ x y
  have herm : K.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro x y
    simp only [K, star_trivial]
    simp only [adjMatrix_apply, G.adj_comm y x]
    grind
  have cross : ∀ x ∈ s, ∀ y ∉ s, K x y = 0 := by
    intro x hx y hy
    by_cases hxy : G.Adj x y
    · obtain ⟨rfl,rfl⟩ := hcross x hx y hy hxy
      simp [K]
    · simp [K, hxy]
  have entry (x y : V) : (G.adjMatrix ℝ x y - K x y)^2 =
      (if x = a ∧ y = b then (1 : ℝ) else 0) +
      (if x = b ∧ y = a then (1 : ℝ) else 0) := by
    by_cases h : x = a ∧ y = b
    · obtain ⟨rfl,rfl⟩ := h
      simp [K, adjMatrix_apply, hab, hneab]
    by_cases h' : x = b ∧ y = a
    · obtain ⟨rfl,rfl⟩ := h'
      simp [K, adjMatrix_apply, hba, hneab.symm]
    simp [K, h, h']
  have bound : (∑ x, ∑ y, (G.adjMatrix ℝ x y - K x y)^2) ≤ 2 := by
    have row (a b x : V) : (∑ y : V, if x = a ∧ y = b then (1 : ℝ) else 0) =
        if x = a then 1 else 0 := by
      by_cases hx : x = a <;> simp [hx]
    simp_rw [entry, Finset.sum_add_distrib, row]
    norm_num
  by_cases hai : a = i
  · subst a
    refine ⟨K,s,b,i,herm,hi,hj,cross,hneab.symm,fun h => hnadj (h ▸ hab), ?_, ?_, ?_,bound⟩
    · simp [adjMatrix_apply, hba]
    · simp [K]
    · intro z hz
      simp [K, hz, hneab.symm]
  · refine ⟨K,s,a,b,herm,hi,hj,cross,hai,fun h => hj (h ▸ ha), ?_, ?_, ?_,bound⟩
    · simp [adjMatrix_apply, hab]
    · simp [K]
    · intro z hz
      simp [K, hz, hneab]

end MO499

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

namespace MO499Block

variable {U V W : Type*} [Fintype U] [Fintype V] [Fintype W]
  [DecidableEq U] [DecidableEq V] [DecidableEq W]

private theorem blocks_nonneg {P : Matrix U U ℝ} {Q : Matrix V V ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) : 0 ≤ fromBlocks P 0 0 Q := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hP
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hQ
  simpa [Matrix.star_eq_conjTranspose, fromBlocks_transpose, fromBlocks_conjTranspose, fromBlocks_multiply] using
    star_mul_self_nonneg (fromBlocks B 0 0 C)

theorem sqrt_bipart (A : Matrix U V ℝ) :
    let H : Matrix (U ⊕ V) (U ⊕ V) ℝ := fromBlocks 0 A A.transpose 0
    CFC.sqrt (H * H) =
      fromBlocks (CFC.sqrt (A * A.transpose)) 0 0 (CFC.sqrt (A.transpose * A)) := by
  dsimp only
  have hp : 0 ≤ A * A.transpose := by simpa using (posSemidef_self_mul_conjTranspose A).nonneg
  have hq : 0 ≤ A.transpose * A := by simpa using (posSemidef_conjTranspose_mul_self A).nonneg
  refine CFC.sqrt_unique ?_ (blocks_nonneg (CFC.sqrt_nonneg (A * A.transpose)) (CFC.sqrt_nonneg (A.transpose * A)))
  simp [fromBlocks_multiply, CFC.sqrt_mul_sqrt_self _ hp, CFC.sqrt_mul_sqrt_self _ hq]

theorem sqrt_cut (K : Matrix W W ℝ) (s : Set W)
    (hK : ∀ i j, ¬ (i ∈ s ↔ j ∈ s) → K i j = 0)
    {i j : W} (hij : ¬ (i ∈ s ↔ j ∈ s)) : CFC.sqrt (K * K) i j = 0 := by
  classical
  let d : W → ℝ := fun x ↦ if x ∈ s then 1 else 0
  have h : Commute K (diagonal d) := by
    ext x y
    simp only [mul_diagonal, diagonal_mul]
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> simp_all [d]
  have hh := (h.mul_left h).cfcₙ_nnreal NNReal.sqrt
  have eq := congrArg (fun M : Matrix W W ℝ ↦ M i j) hh.eq
  change (CFC.sqrt (K*K) * diagonal d) i j = (diagonal d * CFC.sqrt (K*K)) i j at eq
  simp only [mul_diagonal, diagonal_mul] at eq
  by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;> simp_all [d]

end MO499Block

open Matrix
open scoped MatrixOrder
open OMA.S_mo_499788

namespace MO499Assembly

theorem adjacency_blocks {m n : ℕ} (G : SimpleGraph (Fin m ⊕ Fin n)) [DecidableRel G.Adj]
    (hl : ∀ i j : Fin m, ¬ G.Adj (.inl i) (.inl j))
    (hr : ∀ i j : Fin n, ¬ G.Adj (.inr i) (.inr j)) :
    G.adjMatrix ℝ = Matrix.fromBlocks 0 (biadj G) (biadj G).transpose 0 := by
  classical
  ext (i | u) (j | v)
  · simp [SimpleGraph.adjMatrix_apply, hl]
  · simp [SimpleGraph.adjMatrix_apply, biadj]
  · simp [SimpleGraph.adjMatrix_apply, biadj, G.adj_comm]
  · simp [SimpleGraph.adjMatrix_apply, hr]

theorem adjacency_hermitian {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp [SimpleGraph.adjMatrix_apply, G.adj_comm]

theorem zero_across {V : Type*} (K : Matrix V V ℝ) (s : Set V) (hK : K.IsHermitian)
    (hc : ∀ x ∈ s, ∀ y ∉ s, K x y = 0) :
    ∀ x y, ¬ (x ∈ s ↔ y ∈ s) → K x y = 0 := by
  intro x y h
  by_cases hx : x ∈ s
  · exact hc x hx y (fun hy => h ⟨fun _ => hy, fun _ => hx⟩)
  · have hy : y ∈ s := by tauto
    have hsym : K y x = K x y := by simpa using hK.apply x y
    exact hsym.symm.trans (hc y hy x hx)

end MO499Assembly

open MO499Assembly OMA.S_mo_499788 in
theorem OMA.solution : type_of% @OMA.S_mo_499788.main := by
  classical
  intro m n G hG hl hr i j hij
  have hne : (Sum.inl i : Fin m ⊕ Fin n) ≠ .inl j := fun h => hij (Sum.inl.inj h)
  obtain ⟨K,s,w,v,hK,hi,hj,hcut,hwi,hwj,hone,hzero,hrow,hbound⟩ :=
    MO499.eraseCut G hG hne (hl i j)
  have hz := MO499Block.sqrt_cut K s (zero_across K s hK hcut)
    (show ¬ ((Sum.inl i : Fin m ⊕ Fin n) ∈ s ↔ Sum.inl j ∈ s) from fun h => hj (h.mp hi))
  have h := MO499Strict.sqrt_entry_lt_one (G.adjMatrix ℝ) K (adjacency_hermitian G) hK
    w v (Sum.inl i) (Sum.inl j) hne hwi hwj hone hzero hrow hz hbound
  rw [adjacency_blocks G hl hr, MO499Block.sqrt_bipart (biadj G)] at h
  exact h

