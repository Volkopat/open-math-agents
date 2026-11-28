import OMAStatements.S_mo_199635
import Mathlib

/-! Retains @caa1982's orthogonal-group counterexample from merged PR25882.
A common two-coordinate rotation lemma replaces the repeated eigenvector contradictions. -/

open OMA.S_mo_199635
open Matrix

lemma mo199635_det (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : Aᵀ * A = 1) (hd : A.det = 1) :
    (A - 1).det = 0 := by
  have hAA : A * Aᵀ = 1 := mul_eq_one_comm.1 hA
  have h1 : A - 1 = A * (1 - Aᵀ) := by rw [mul_sub, mul_one, hAA]
  have h2 : (A - 1).det = (1 - A).det := by
    rw [h1, det_mul, hd, one_mul, ← det_transpose, transpose_sub, transpose_one,
      transpose_transpose]
  have h3 : (1 : Matrix (Fin 3) (Fin 3) ℂ) - A = -(A - 1) := by abel
  rw [h3, det_neg] at h2
  simp only [Fintype.card_fin] at h2
  have : (2 : ℂ) * (A - 1).det = 0 := by linear_combination h2
  simpa using this

lemma mo199635_rotation {a b : ℂ}
    (h : (-b = a ∧ a = b) ∨ (b = a ∧ a = -b)) : a = 0 ∧ b = 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor
    · linear_combination (h2 - h1) / 2
    · linear_combination -(h1 + h2) / 2
  · constructor
    · linear_combination (h2 - h1) / 2
    · linear_combination (h1 + h2) / 2

noncomputable def mo199635_mkU (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) (h : Mᵀ * M = 1) :
    GL (Fin 3 ⊕ Fin 3) ℂ :=
  ⟨M, Mᵀ, mul_eq_one_comm.1 h, h⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_199635.main) := by
  intro h
  set Rz : Matrix (Fin 3) (Fin 3) ℂ := !![0, -1, 0; 1, 0, 0; 0, 0, 1] with hRzdef
  set Rx : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 0, -1; 0, 1, 0] with hRxdef
  have hRz : Rzᵀ * Rz = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Rz, Matrix.mul_apply, Fin.sum_univ_three]
  have hRx : Rxᵀ * Rx = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Rx, Matrix.mul_apply, Fin.sum_univ_three]
  have dRz : Rz.det = 1 := by simp [Rz, Matrix.det_fin_three]
  have dRx : Rx.det = 1 := by simp [Rx, Matrix.det_fin_three]
  have hblk : ∀ A B : Matrix (Fin 3) (Fin 3) ℂ, Aᵀ * A = 1 → Bᵀ * B = 1 →
      (fromBlocks A 0 0 B)ᵀ * fromBlocks A 0 0 B = 1 := by
    intro A B hA hB
    rw [fromBlocks_transpose, fromBlocks_multiply]
    simp [hA, hB, fromBlocks_one]
  let g1 := mo199635_mkU (fromBlocks Rz 0 0 1) (hblk _ _ hRz (by simp))
  let g2 := mo199635_mkU (fromBlocks Rx 0 0 1) (hblk _ _ hRx (by simp))
  let g3 := mo199635_mkU (fromBlocks 1 0 0 Rz) (hblk _ _ (by simp) hRz)
  let g4 := mo199635_mkU (fromBlocks 1 0 0 Rx) (hblk _ _ (by simp) hRx)
  let G : Subgroup (GL (Fin 3 ⊕ Fin 3) ℂ) := Subgroup.closure {g1, g2, g3, g4}
  have hP : ∀ g ∈ G, ∃ A B : Matrix (Fin 3) (Fin 3) ℂ,
      (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) ℂ) = fromBlocks A 0 0 B ∧
      Aᵀ * A = 1 ∧ A.det = 1 ∧ Bᵀ * B = 1 ∧ B.det = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨Rz, 1, rfl, hRz, dRz, by simp, by simp⟩
      · exact ⟨Rx, 1, rfl, hRx, dRx, by simp, by simp⟩
      · exact ⟨1, Rz, rfl, by simp, by simp, hRz, dRz⟩
      · exact ⟨1, Rx, rfl, by simp, by simp, hRx, dRx⟩
    | one => exact ⟨1, 1, by simp [fromBlocks_one], by simp, by simp, by simp, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨A, B, e, hA, dA, hB, dB⟩ := hx
      obtain ⟨A', B', e', hA', dA', hB', dB'⟩ := hy
      refine ⟨A * A', B * B', ?_, ?_, ?_, ?_, ?_⟩
      · rw [Units.val_mul, e, e', fromBlocks_multiply]; simp
      · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Aᵀ, hA, Matrix.one_mul, hA']
      · rw [det_mul, dA, dA', mul_one]
      · rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ, hB, Matrix.one_mul, hB']
      · rw [det_mul, dB, dB', mul_one]
    | inv x _ hx =>
      obtain ⟨A, B, e, hA, dA, hB, dB⟩ := hx
      have hAA : A * Aᵀ = 1 := mul_eq_one_comm.1 hA
      have hBB : B * Bᵀ = 1 := mul_eq_one_comm.1 hB
      refine ⟨Aᵀ, Bᵀ, ?_, by rw [transpose_transpose, hAA], by rw [det_transpose, dA],
        by rw [transpose_transpose, hBB], by rw [det_transpose, dB]⟩
      apply Units.inv_eq_of_mul_eq_one_right
      rw [e, fromBlocks_multiply]
      simp [hAA, hBB, fromBlocks_one]
  have hcard : Even (Fintype.card (Fin 3 ⊕ Fin 3)) := by decide
  obtain ⟨v, hv0, hv⟩ := h (Fin 3 ⊕ Fin 3) hcard G
    (fun g hg => by
      obtain ⟨A, B, e, hA, dA, hB, dB⟩ := hP g hg
      rw [e]
      refine ⟨hblk A B hA hB, ?_⟩
      rw [det_fromBlocks_zero₂₁, dA, dB, mul_one])
    (fun g hg => by
      obtain ⟨A, B, e, hA, dA, hB, dB⟩ := hP g hg
      obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (mo199635_det A hA dA)
      refine ⟨Sum.elim a 0, ?_, Or.inl ?_⟩
      · intro h0; apply ha0; funext i; exact congrFun h0 (Sum.inl i)
      · rw [e, fromBlocks_mulVec]
        have : A *ᵥ a = a := by
          rw [sub_mulVec, one_mulVec] at ha; exact sub_eq_zero.1 ha
        ext (i | i) <;> simp [this])
  have m1 : g1 ∈ G := Subgroup.subset_closure (by simp)
  have m2 : g2 ∈ G := Subgroup.subset_closure (by simp)
  have m3 : g3 ∈ G := Subgroup.subset_closure (by simp)
  have m4 : g4 ∈ G := Subgroup.subset_closure (by simp)
  have e1 := hv g1 m1
  have e2 := hv g2 m2
  have e3 := hv g3 m3
  have e4 := hv g4 m4
  have ca : v (Sum.inl 0) = 0 ∧ v (Sum.inl 1) = 0 := by
    apply mo199635_rotation
    rcases e1 with e | e
    all_goals
      have q0 := congrFun e (Sum.inl 0)
      have q1 := congrFun e (Sum.inl 1)
      simp [g1, mo199635_mkU, mulVec, dotProduct, Fin.sum_univ_three,
        Rz] at q0 q1
    · exact Or.inl ⟨q0, q1⟩
    · exact Or.inr ⟨q0, q1⟩
  have cb : v (Sum.inl 1) = 0 ∧ v (Sum.inl 2) = 0 := by
    apply mo199635_rotation
    rcases e2 with e | e
    all_goals
      have q0 := congrFun e (Sum.inl 1)
      have q1 := congrFun e (Sum.inl 2)
      simp [g2, mo199635_mkU, mulVec, dotProduct, Fin.sum_univ_three,
        Rx] at q0 q1
    · exact Or.inl ⟨q0, q1⟩
    · exact Or.inr ⟨q0, q1⟩
  have cc : v (Sum.inr 0) = 0 ∧ v (Sum.inr 1) = 0 := by
    apply mo199635_rotation
    rcases e3 with e | e
    all_goals
      have q0 := congrFun e (Sum.inr 0)
      have q1 := congrFun e (Sum.inr 1)
      simp [g3, mo199635_mkU, mulVec, dotProduct, Fin.sum_univ_three,
        Rz] at q0 q1
    · exact Or.inl ⟨q0, q1⟩
    · exact Or.inr ⟨q0, q1⟩
  have cd : v (Sum.inr 1) = 0 ∧ v (Sum.inr 2) = 0 := by
    apply mo199635_rotation
    rcases e4 with e | e
    all_goals
      have q0 := congrFun e (Sum.inr 1)
      have q1 := congrFun e (Sum.inr 2)
      simp [g4, mo199635_mkU, mulVec, dotProduct, Fin.sum_univ_three,
        Rx] at q0 q1
    · exact Or.inl ⟨q0, q1⟩
    · exact Or.inr ⟨q0, q1⟩
  apply hv0
  funext k
  rcases k with k | k <;> fin_cases k
  · exact ca.1
  · exact ca.2
  · exact cb.2
  · exact cc.1
  · exact cc.2
  · exact cd.2
