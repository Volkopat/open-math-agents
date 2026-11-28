import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H2_R2
import Mathlib

/-! Splits the finite 7x9x9 full-row-rank certificate into four independent
groups of standard-basis witnesses, with a common explicitly defined matrix.
The parent implication is purely linear algebra. -/

namespace OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H2_R2_H1_R1

def H1 : Prop :=
  let xx : Array ℕ := #[0x28, 0x5, 0x48, 0x19, 0x43, 0x21, 0x4, 0x2a, 0x11, 0x8, 0x10, 0x12, 0x15, 0x2, 0x30, 0x50, 0x40, 0x44, 0x60, 0x20, 0x1c, 0x14, 0x22, 0x42, 0x1]
  let yy : Array ℕ := #[0xc4, 0x3, 0x80, 0x24, 0x54, 0x10, 0xa0, 0x15, 0x1a4, 0x41, 0x2, 0x100, 0x4e, 0x12, 0x20, 0x4, 0xc0, 0x113, 0x19, 0x1, 0x8, 0x34, 0x140, 0x188, 0xa8]
  let zz : Array ℕ := #[0x14, 0x2, 0x81, 0x100, 0x1, 0x108, 0x124, 0x8, 0x40, 0x22, 0x101, 0x30, 0x160, 0x10, 0x90, 0x80, 0x8, 0x1c, 0x2, 0x88, 0x40, 0x20, 0xc0, 0x4, 0x3]
  let bit : Array ℕ → ℕ → ℕ → ℤ := fun arr t i =>
    if (arr[t]?.getD 0).testBit i then 1 else 0
  let E : (Fin 7 × Fin 9 × Fin 9) ≃ Fin 567 :=
    ((Equiv.refl (Fin 7)).prodCongr
      (finProdFinEquiv : (Fin 9 × Fin 9) ≃ Fin 81)).trans
      (finProdFinEquiv : (Fin 7 × Fin 81) ≃ Fin 567)
  let e : (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)) ≃ Fin 25 :=
    (Equiv.sumCongr (Equiv.refl (Fin 7))
      (finSumFinEquiv : (Fin 9 ⊕ Fin 9) ≃ Fin 18)).trans
      (finSumFinEquiv : (Fin 7 ⊕ Fin 18) ≃ Fin 25)
  let F : (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ≃ Fin 625 :=
    ((Equiv.refl (Fin 25)).prodCongr e).trans
      (finProdFinEquiv : (Fin 25 × Fin 25) ≃ Fin 625)
  let tangent : Matrix (Fin 7 × Fin 9 × Fin 9)
      (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ℤ :=
    fun (i,j,k) (t,s) =>
      match s with
      | .inl ii => if ii=i then bit yy t.val j.val * bit zz t.val k.val else 0
      | .inr (.inl jj) => if jj=j then bit xx t.val i.val * bit zz t.val k.val else 0
      | .inr (.inr kk) => if kk=k then bit xx t.val i.val * bit yy t.val j.val else 0
  let A : Matrix (Fin 567) (Fin 625) ℤ := fun i j =>
    tangent (E.symm i) (F.symm j)
  ∀ row : Fin 567, (row.val < 162) → ∃ v : Fin 625 → ℤ,
    (A.map (Int.castRingHom (ZMod 2))).mulVec (fun j => (v j : ZMod 2)) =
      fun i => if i = row then 1 else 0

def H2 : Prop :=
  let xx : Array ℕ := #[0x28, 0x5, 0x48, 0x19, 0x43, 0x21, 0x4, 0x2a, 0x11, 0x8, 0x10, 0x12, 0x15, 0x2, 0x30, 0x50, 0x40, 0x44, 0x60, 0x20, 0x1c, 0x14, 0x22, 0x42, 0x1]
  let yy : Array ℕ := #[0xc4, 0x3, 0x80, 0x24, 0x54, 0x10, 0xa0, 0x15, 0x1a4, 0x41, 0x2, 0x100, 0x4e, 0x12, 0x20, 0x4, 0xc0, 0x113, 0x19, 0x1, 0x8, 0x34, 0x140, 0x188, 0xa8]
  let zz : Array ℕ := #[0x14, 0x2, 0x81, 0x100, 0x1, 0x108, 0x124, 0x8, 0x40, 0x22, 0x101, 0x30, 0x160, 0x10, 0x90, 0x80, 0x8, 0x1c, 0x2, 0x88, 0x40, 0x20, 0xc0, 0x4, 0x3]
  let bit : Array ℕ → ℕ → ℕ → ℤ := fun arr t i =>
    if (arr[t]?.getD 0).testBit i then 1 else 0
  let E : (Fin 7 × Fin 9 × Fin 9) ≃ Fin 567 :=
    ((Equiv.refl (Fin 7)).prodCongr
      (finProdFinEquiv : (Fin 9 × Fin 9) ≃ Fin 81)).trans
      (finProdFinEquiv : (Fin 7 × Fin 81) ≃ Fin 567)
  let e : (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)) ≃ Fin 25 :=
    (Equiv.sumCongr (Equiv.refl (Fin 7))
      (finSumFinEquiv : (Fin 9 ⊕ Fin 9) ≃ Fin 18)).trans
      (finSumFinEquiv : (Fin 7 ⊕ Fin 18) ≃ Fin 25)
  let F : (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ≃ Fin 625 :=
    ((Equiv.refl (Fin 25)).prodCongr e).trans
      (finProdFinEquiv : (Fin 25 × Fin 25) ≃ Fin 625)
  let tangent : Matrix (Fin 7 × Fin 9 × Fin 9)
      (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ℤ :=
    fun (i,j,k) (t,s) =>
      match s with
      | .inl ii => if ii=i then bit yy t.val j.val * bit zz t.val k.val else 0
      | .inr (.inl jj) => if jj=j then bit xx t.val i.val * bit zz t.val k.val else 0
      | .inr (.inr kk) => if kk=k then bit xx t.val i.val * bit yy t.val j.val else 0
  let A : Matrix (Fin 567) (Fin 625) ℤ := fun i j =>
    tangent (E.symm i) (F.symm j)
  ∀ row : Fin 567, (162 ≤ row.val ∧ row.val < 324) → ∃ v : Fin 625 → ℤ,
    (A.map (Int.castRingHom (ZMod 2))).mulVec (fun j => (v j : ZMod 2)) =
      fun i => if i = row then 1 else 0

def H3 : Prop :=
  let xx : Array ℕ := #[0x28, 0x5, 0x48, 0x19, 0x43, 0x21, 0x4, 0x2a, 0x11, 0x8, 0x10, 0x12, 0x15, 0x2, 0x30, 0x50, 0x40, 0x44, 0x60, 0x20, 0x1c, 0x14, 0x22, 0x42, 0x1]
  let yy : Array ℕ := #[0xc4, 0x3, 0x80, 0x24, 0x54, 0x10, 0xa0, 0x15, 0x1a4, 0x41, 0x2, 0x100, 0x4e, 0x12, 0x20, 0x4, 0xc0, 0x113, 0x19, 0x1, 0x8, 0x34, 0x140, 0x188, 0xa8]
  let zz : Array ℕ := #[0x14, 0x2, 0x81, 0x100, 0x1, 0x108, 0x124, 0x8, 0x40, 0x22, 0x101, 0x30, 0x160, 0x10, 0x90, 0x80, 0x8, 0x1c, 0x2, 0x88, 0x40, 0x20, 0xc0, 0x4, 0x3]
  let bit : Array ℕ → ℕ → ℕ → ℤ := fun arr t i =>
    if (arr[t]?.getD 0).testBit i then 1 else 0
  let E : (Fin 7 × Fin 9 × Fin 9) ≃ Fin 567 :=
    ((Equiv.refl (Fin 7)).prodCongr
      (finProdFinEquiv : (Fin 9 × Fin 9) ≃ Fin 81)).trans
      (finProdFinEquiv : (Fin 7 × Fin 81) ≃ Fin 567)
  let e : (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)) ≃ Fin 25 :=
    (Equiv.sumCongr (Equiv.refl (Fin 7))
      (finSumFinEquiv : (Fin 9 ⊕ Fin 9) ≃ Fin 18)).trans
      (finSumFinEquiv : (Fin 7 ⊕ Fin 18) ≃ Fin 25)
  let F : (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ≃ Fin 625 :=
    ((Equiv.refl (Fin 25)).prodCongr e).trans
      (finProdFinEquiv : (Fin 25 × Fin 25) ≃ Fin 625)
  let tangent : Matrix (Fin 7 × Fin 9 × Fin 9)
      (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ℤ :=
    fun (i,j,k) (t,s) =>
      match s with
      | .inl ii => if ii=i then bit yy t.val j.val * bit zz t.val k.val else 0
      | .inr (.inl jj) => if jj=j then bit xx t.val i.val * bit zz t.val k.val else 0
      | .inr (.inr kk) => if kk=k then bit xx t.val i.val * bit yy t.val j.val else 0
  let A : Matrix (Fin 567) (Fin 625) ℤ := fun i j =>
    tangent (E.symm i) (F.symm j)
  ∀ row : Fin 567, (324 ≤ row.val ∧ row.val < 486) → ∃ v : Fin 625 → ℤ,
    (A.map (Int.castRingHom (ZMod 2))).mulVec (fun j => (v j : ZMod 2)) =
      fun i => if i = row then 1 else 0

def H4 : Prop :=
  let xx : Array ℕ := #[0x28, 0x5, 0x48, 0x19, 0x43, 0x21, 0x4, 0x2a, 0x11, 0x8, 0x10, 0x12, 0x15, 0x2, 0x30, 0x50, 0x40, 0x44, 0x60, 0x20, 0x1c, 0x14, 0x22, 0x42, 0x1]
  let yy : Array ℕ := #[0xc4, 0x3, 0x80, 0x24, 0x54, 0x10, 0xa0, 0x15, 0x1a4, 0x41, 0x2, 0x100, 0x4e, 0x12, 0x20, 0x4, 0xc0, 0x113, 0x19, 0x1, 0x8, 0x34, 0x140, 0x188, 0xa8]
  let zz : Array ℕ := #[0x14, 0x2, 0x81, 0x100, 0x1, 0x108, 0x124, 0x8, 0x40, 0x22, 0x101, 0x30, 0x160, 0x10, 0x90, 0x80, 0x8, 0x1c, 0x2, 0x88, 0x40, 0x20, 0xc0, 0x4, 0x3]
  let bit : Array ℕ → ℕ → ℕ → ℤ := fun arr t i =>
    if (arr[t]?.getD 0).testBit i then 1 else 0
  let E : (Fin 7 × Fin 9 × Fin 9) ≃ Fin 567 :=
    ((Equiv.refl (Fin 7)).prodCongr
      (finProdFinEquiv : (Fin 9 × Fin 9) ≃ Fin 81)).trans
      (finProdFinEquiv : (Fin 7 × Fin 81) ≃ Fin 567)
  let e : (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)) ≃ Fin 25 :=
    (Equiv.sumCongr (Equiv.refl (Fin 7))
      (finSumFinEquiv : (Fin 9 ⊕ Fin 9) ≃ Fin 18)).trans
      (finSumFinEquiv : (Fin 7 ⊕ Fin 18) ≃ Fin 25)
  let F : (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ≃ Fin 625 :=
    ((Equiv.refl (Fin 25)).prodCongr e).trans
      (finProdFinEquiv : (Fin 25 × Fin 25) ≃ Fin 625)
  let tangent : Matrix (Fin 7 × Fin 9 × Fin 9)
      (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ℤ :=
    fun (i,j,k) (t,s) =>
      match s with
      | .inl ii => if ii=i then bit yy t.val j.val * bit zz t.val k.val else 0
      | .inr (.inl jj) => if jj=j then bit xx t.val i.val * bit zz t.val k.val else 0
      | .inr (.inr kk) => if kk=k then bit xx t.val i.val * bit yy t.val j.val else 0
  let A : Matrix (Fin 567) (Fin 625) ℤ := fun i j =>
    tangent (E.symm i) (F.symm j)
  ∀ row : Fin 567, (486 ≤ row.val) → ∃ v : Fin 625 → ℤ,
    (A.map (Int.castRingHom (ZMod 2))).mulVec (fun j => (v j : ZMod 2)) =
      fun i => if i = row then 1 else 0

/-- A generic conversion from tangent surjectivity to a complex spanning
witness. The integer factor matrices are kept opaque, so this proof
does not simplify enormous concrete bit arrays. -/
theorem witness_of_surj
    (x : Fin 25 → Fin 7 → ℤ)
    (y z : Fin 25 → Fin 9 → ℤ)
    (tangent : Matrix (Fin 7 × Fin 9 × Fin 9)
      (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ℤ)
    (hU : ∀ i j k t ii,
      tangent (i,j,k) (t,.inl ii) =
        if ii=i then y t j*z t k else 0)
    (hV : ∀ i j k t jj,
      tangent (i,j,k) (t,.inr (.inl jj)) =
        if jj=j then x t i*z t k else 0)
    (hW : ∀ i j k t kk,
      tangent (i,j,k) (t,.inr (.inr kk)) =
        if kk=k then x t i*y t j else 0)
    (honto : Function.Surjective
      (tangent.map (Int.castRingHom ℂ)).mulVec) :
    ∃ X : Fin 25 → Fin 7 → ℂ,
    ∃ Y Z : Fin 25 → Fin 9 → ℂ,
      ∀ T : Fin 7 → Fin 9 → Fin 9 → ℂ,
        ∃ U : Fin 25 → Fin 7 → ℂ,
        ∃ V W : Fin 25 → Fin 9 → ℂ,
          ∀ i j k,
            T i j k = ∑ t, (U t i * (Y t j * Z t k) +
              X t i * (V t j * Z t k) +
              X t i * (Y t j * W t k)) := by
  refine ⟨fun t i => (x t i : ℂ), fun t j => (y t j : ℂ),
    fun t k => (z t k : ℂ), ?_⟩
  intro T
  obtain ⟨b,hb⟩ := honto (fun (i,j,k) => T i j k)
  refine ⟨fun t i => b (t,.inl i),
    fun t j => b (t,.inr (.inl j)),
    fun t k => b (t,.inr (.inr k)), ?_⟩
  intro i j k
  refine (congrFun hb (i,j,k)).symm.trans ?_
  change (∑ t : Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)),
    ((tangent (i,j,k) t : ℤ) : ℂ)*b t) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
  apply Finset.sum_congr rfl
  intro t _
  simp [hU, hV, hW, apply_ite, Finset.sum_ite_eq',
    mul_comm, add_assoc]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem main : H1 → H2 → H3 → H4 → OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H2_R2.H1 := by
  classical
  intro h1 h2 h3 h4
  let xx : Array ℕ := #[0x28, 0x5, 0x48, 0x19, 0x43, 0x21, 0x4, 0x2a, 0x11, 0x8, 0x10, 0x12, 0x15, 0x2, 0x30, 0x50, 0x40, 0x44, 0x60, 0x20, 0x1c, 0x14, 0x22, 0x42, 0x1]
  let yy : Array ℕ := #[0xc4, 0x3, 0x80, 0x24, 0x54, 0x10, 0xa0, 0x15, 0x1a4, 0x41, 0x2, 0x100, 0x4e, 0x12, 0x20, 0x4, 0xc0, 0x113, 0x19, 0x1, 0x8, 0x34, 0x140, 0x188, 0xa8]
  let zz : Array ℕ := #[0x14, 0x2, 0x81, 0x100, 0x1, 0x108, 0x124, 0x8, 0x40, 0x22, 0x101, 0x30, 0x160, 0x10, 0x90, 0x80, 0x8, 0x1c, 0x2, 0x88, 0x40, 0x20, 0xc0, 0x4, 0x3]
  let bit : Array ℕ → ℕ → ℕ → ℤ := fun arr t i =>
    if (arr[t]?.getD 0).testBit i then 1 else 0
  let E : (Fin 7 × Fin 9 × Fin 9) ≃ Fin 567 :=
    ((Equiv.refl (Fin 7)).prodCongr
      (finProdFinEquiv : (Fin 9 × Fin 9) ≃ Fin 81)).trans
      (finProdFinEquiv : (Fin 7 × Fin 81) ≃ Fin 567)
  let e : (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)) ≃ Fin 25 :=
    (Equiv.sumCongr (Equiv.refl (Fin 7))
      (finSumFinEquiv : (Fin 9 ⊕ Fin 9) ≃ Fin 18)).trans
      (finSumFinEquiv : (Fin 7 ⊕ Fin 18) ≃ Fin 25)
  let F : (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ≃ Fin 625 :=
    ((Equiv.refl (Fin 25)).prodCongr e).trans
      (finProdFinEquiv : (Fin 25 × Fin 25) ≃ Fin 625)
  let tangent : Matrix (Fin 7 × Fin 9 × Fin 9)
      (Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9))) ℤ :=
    fun (i,j,k) (t,s) =>
      match s with
      | .inl ii => if ii=i then bit yy t.val j.val * bit zz t.val k.val else 0
      | .inr (.inl jj) => if jj=j then bit xx t.val i.val * bit zz t.val k.val else 0
      | .inr (.inr kk) => if kk=k then bit xx t.val i.val * bit yy t.val j.val else 0
  let A : Matrix (Fin 567) (Fin 625) ℤ := fun i j =>
    tangent (E.symm i) (F.symm j)
  let P : Fin 567 → Prop := fun row =>
    ∃ v : Fin 625 → ℤ,
      (A.map (Int.castRingHom (ZMod 2))).mulVec (fun j => (v j : ZMod 2)) =
        fun i => if i = row then 1 else 0
  have h1' : ∀ row : Fin 567, row.val < 162 → P row := by
    exact h1
  have h2' : ∀ row : Fin 567,
      (162 ≤ row.val ∧ row.val < 324) → P row := by
    exact h2
  have h3' : ∀ row : Fin 567,
      (324 ≤ row.val ∧ row.val < 486) → P row := by
    exact h3
  have h4' : ∀ row : Fin 567, 486 ≤ row.val → P row := by
    exact h4
  have hrows : ∀ row : Fin 567, P row := by
    intro row
    by_cases p1 : row.val < 162
    · exact h1' row p1
    by_cases p2 : row.val < 324
    · exact h2' row ⟨by omega, p2⟩
    by_cases p3 : row.val < 486
    · exact h3' row ⟨by omega, p3⟩
    · exact h4' row (by omega)
  let B : Matrix (Fin 625) (Fin 567) ℤ :=
    fun j i => (Classical.choose (hrows i)) j
  have hAB : A.map (Int.castRingHom (ZMod 2)) *
      B.map (Int.castRingHom (ZMod 2)) = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ k : Fin 625, ((A i k : ℤ) : ZMod 2) *
      ((B k j : ℤ) : ZMod 2)) = (if i = j then 1 else 0)
    exact congrFun (Classical.choose_spec (hrows j)) i
  have surjA : Function.Surjective (A.map (Int.castRingHom ℂ)).mulVec := by
    let C := A * B
    have hd : ((C.det : ℤ) : ZMod 2) = 1 := by
      change (Int.castRingHom (ZMod 2)) C.det = 1
      rw [RingHom.map_det, RingHom.mapMatrix_apply,
        show C = A * B from rfl, Matrix.map_mul, hAB, Matrix.det_one]
    have hn : C.det ≠ 0 := by
      intro hz
      rw [hz, Int.cast_zero] at hd
      exact zero_ne_one hd
    have hu : IsUnit (C.map (Int.castRingHom ℂ)).det := by
      apply isUnit_iff_ne_zero.mpr
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      change (C.det : ℂ) ≠ 0
      exact_mod_cast hn
    have onto : Function.Surjective (C.map (Int.castRingHom ℂ)).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    intro v
    obtain ⟨w,hw⟩ := onto v
    refine ⟨(B.map (Int.castRingHom ℂ)).mulVec w, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul]
    exact hw
  have surjTangent :
      Function.Surjective (tangent.map (Int.castRingHom ℂ)).mulVec := by
    intro T
    obtain ⟨v,hv⟩ := surjA (fun i => T (E.symm i))
    refine ⟨fun j => v (F j), ?_⟩
    funext i
    have h := congrFun hv (E i)
    change (∑ j : Fin 625, ((A (E i) j : ℤ) : ℂ) * v j) =
      T (E.symm (E i)) at h
    change (∑ j : Fin 25 × (Fin 7 ⊕ (Fin 9 ⊕ Fin 9)),
      ((tangent i j : ℤ) : ℂ) * v (F j)) = T i
    have he := F.sum_comp
      (fun j : Fin 625 => ((tangent i (F.symm j) : ℤ) : ℂ) * v j)
    simp only [Equiv.symm_apply_apply] at he
    rw [he]
    simpa only [A, Equiv.symm_apply_apply] using h
  have hw := witness_of_surj
    (fun t i => bit xx t.val i.val)
    (fun t j => bit yy t.val j.val)
    (fun t k => bit zz t.val k.val)
    tangent
    (by intros; rfl)
    (by intros; rfl)
    (by intros; rfl)
    surjTangent
  exact CriticalReduction.bounded_of_witness hw

end OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R1_H2_R2_H1_R1
