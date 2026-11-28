import OMAStatements.S_oeis_a231317
import Mathlib.Tactic

namespace OMA.P_oeis_a231317

open OMA.S_oeis_a231317

private def rowIdx {n : ℕ} (p : Fin (n + 1) × Fin 2) : ℕ := 2 * p.1.1 + p.2.1

private def isValidPath (k : ℕ) (p : Fin (k + 2) → Fin 3) : Prop :=
  p ⟨0, by omega⟩ ≠ p ⟨1, by omega⟩ ∧
  p ⟨k, by omega⟩ ≠ p ⟨k + 1, by omega⟩ ∧
  ∀ i : Fin k, ¬ (p ⟨i.1, by omega⟩ = p ⟨i.1 + 1, by omega⟩ ∧
                   p ⟨i.1 + 1, by omega⟩ = p ⟨i.1 + 2, by omega⟩)

private instance (k : ℕ) (p : Fin (k + 2) → Fin 3) : Decidable (isValidPath k p) := by
  unfold isValidPath; infer_instance

private def pathCount (k : ℕ) : ℕ :=
  (Finset.univ.filter (isValidPath k)).card

private def totalValid (n : ℕ) : ℕ :=
  (Finset.univ.filter (noDiagMajority n)).card

private def pathPairEquiv (k : ℕ) :
    (Fin (k + 2) × Fin 2 → Fin 3) ≃ (Fin (k + 2) → Fin 3) × (Fin (k + 2) → Fin 3) where
  toFun A :=
    (fun i => A (i, ⟨i.1 % 2, Nat.mod_lt _ (by omega)⟩),
     fun i => A (i, ⟨(i.1 + 1) % 2, Nat.mod_lt _ (by omega)⟩))
  invFun P q :=
    if q.2.1 = q.1.1 % 2 then P.1 q.1 else P.2 q.1
  left_inv A := by
    funext ⟨i, j⟩
    dsimp only
    by_cases h : j.1 = i.1 % 2
    · rw [if_pos h]; congr 1; exact Prod.ext rfl (Fin.ext h.symm)
    · rw [if_neg h]; congr 1; exact Prod.ext rfl (Fin.ext (by have := j.isLt; dsimp; omega))
  right_inv P := by
    apply Prod.ext
    · funext i; simp
    · funext i
      have hne : (i.1 + 1) % 2 ≠ i.1 % 2 := by omega
      simp [hne]

private lemma diagNeighbors_zero (k : ℕ) (j : Fin 2) :
    Finset.univ.filter (fun q : Fin (k + 2) × Fin 2 =>
      isDiagNeighbor (⟨0, by omega⟩, j) q = true) =
    {(⟨1, by omega⟩, ⟨1 - j.1, by omega⟩)} := by
  ext ⟨qi, qj⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    isDiagNeighbor, decide_eq_true_eq, Prod.mk.injEq, Fin.ext_iff]
  have hqj := qj.isLt; have hj := j.isLt
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : j.1 ≠ qj.1 := fun heq => h2 (Fin.ext heq)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun heq => ?_⟩
    have := congrArg Fin.val heq; omega

private lemma diagNeighbors_last (k : ℕ) (j : Fin 2) :
    Finset.univ.filter (fun q : Fin (k + 2) × Fin 2 =>
      isDiagNeighbor (⟨k + 1, by omega⟩, j) q = true) =
    {(⟨k, by omega⟩, ⟨1 - j.1, by omega⟩)} := by
  ext ⟨qi, qj⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    isDiagNeighbor, decide_eq_true_eq, Prod.mk.injEq, Fin.ext_iff]
  have hqi := qi.isLt; have hqj := qj.isLt; have hj := j.isLt
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : j.1 ≠ qj.1 := fun heq => h2 (Fin.ext heq)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, fun heq => ?_⟩
    have := congrArg Fin.val heq; omega

private lemma diagNeighbors_mid (k : ℕ) (i : Fin (k + 2)) (hi0 : 0 < i.1) (hi1 : i.1 < k + 1)
    (j : Fin 2) :
    Finset.univ.filter (fun q : Fin (k + 2) × Fin 2 => isDiagNeighbor (i, j) q = true) =
    {(⟨i.1 - 1, by omega⟩, ⟨1 - j.1, by omega⟩), (⟨i.1 + 1, by omega⟩, ⟨1 - j.1, by omega⟩)} := by
  ext ⟨qi, qj⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    isDiagNeighbor, decide_eq_true_eq, Prod.mk.injEq, Fin.ext_iff]
  have hqj := qj.isLt; have hj := j.isLt
  constructor
  · rintro ⟨h1, h2⟩
    have h2' : j.1 ≠ qj.1 := fun heq => h2 (Fin.ext heq)
    rcases h1 with h1 | h1
    · right; exact ⟨by omega, by omega⟩
    · left; exact ⟨by omega, by omega⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨Or.inr (by omega), fun heq => ?_⟩
      have := congrArg Fin.val heq; omega
    · refine ⟨Or.inl (by omega), fun heq => ?_⟩
      have := congrArg Fin.val heq; omega

private lemma card_filter_singleton_cond {α : Type*} [DecidableEq α] (a : α) (P : α → Prop)
    [DecidablePred P] :
    (2 * (({a} : Finset α).filter P).card ≤ 1) ↔ ¬ P a := by
  by_cases h : P a
  · rw [Finset.filter_singleton, if_pos h]; simp [h]
  · rw [Finset.filter_singleton, if_neg h]; simp [h]

private lemma card_filter_pair_cond {α : Type*} [DecidableEq α] (a b : α) (hab : a ≠ b)
    (P : α → Prop) [DecidablePred P] :
    (2 * (({a, b} : Finset α).filter P).card ≤ 2) ↔ ¬ (P a ∧ P b) := by
  by_cases ha : P a <;> by_cases hb : P b
  · have : ({a, b} : Finset α).filter P = {a, b} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, by rcases h with rfl | rfl <;> assumption⟩⟩
    rw [this, Finset.card_pair hab]; simp [ha, hb]
  · have : ({a, b} : Finset α).filter P = {a} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact (hb hx).elim
      · rintro rfl; exact ⟨Or.inl rfl, ha⟩
    rw [this]; simp [ha, hb]
  · have : ({a, b} : Finset α).filter P = {b} := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · exact (ha hx).elim
        · rfl
      · rintro rfl; exact ⟨Or.inr rfl, hb⟩
    rw [this]; simp [ha, hb]
  · have : ({a, b} : Finset α).filter P = ∅ := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false]
      rintro ⟨rfl | rfl, hx⟩
      · exact ha hx
      · exact hb hx
    rw [this]; simp [ha, hb]

private lemma noDiagMajority_iff_paths (k : ℕ) (A : Fin (k + 2) × Fin 2 → Fin 3) :
    noDiagMajority (k + 1) A ↔
      isValidPath k (pathPairEquiv k A).1 ∧ isValidPath k (pathPairEquiv k A).2 := by
  have hcell : ∀ p : Fin (k + 2) × Fin 2,
      (2 * (Finset.univ.filter (fun q => isDiagNeighbor p q = true ∧ A q = A p)).card ≤
        (Finset.univ.filter (fun q => isDiagNeighbor p q = true)).card) ↔
      (if h0 : p.1.1 = 0 then A (⟨1, by omega⟩, ⟨1 - p.2.1, by omega⟩) ≠ A p
       else if h1 : p.1.1 = k + 1 then A (⟨k, by omega⟩, ⟨1 - p.2.1, by omega⟩) ≠ A p
       else ¬ (A (⟨p.1.1 - 1, by omega⟩, ⟨1 - p.2.1, by omega⟩) = A p ∧
               A (⟨p.1.1 + 1, by omega⟩, ⟨1 - p.2.1, by omega⟩) = A p)) := by
    intro ⟨i, j⟩
    have hsplit : Finset.univ.filter (fun q => isDiagNeighbor (i, j) q = true ∧ A q = A (i, j)) =
        (Finset.univ.filter (fun q => isDiagNeighbor (i, j) q = true)).filter
          (fun q => A q = A (i, j)) := by
      ext q; simp [and_comm]
    rw [hsplit]
    by_cases h0 : i.1 = 0
    · have hi : i = ⟨0, by omega⟩ := Fin.ext h0
      rw [hi, dif_pos rfl, diagNeighbors_zero, Finset.card_singleton, card_filter_singleton_cond]
    · rw [dif_neg h0]
      by_cases h1 : i.1 = k + 1
      · have hi : i = ⟨k + 1, by omega⟩ := Fin.ext h1
        rw [hi, dif_pos rfl, diagNeighbors_last, Finset.card_singleton, card_filter_singleton_cond]
      · rw [dif_neg h1]
        have hi0 : 0 < i.1 := by omega
        have hi1 : i.1 < k + 1 := by have := i.isLt; omega
        rw [diagNeighbors_mid k i hi0 hi1 j]
        have hne : ((⟨i.1 - 1, by omega⟩, ⟨1 - j.1, by omega⟩) : Fin (k + 2) × Fin 2) ≠
            (⟨i.1 + 1, by omega⟩, ⟨1 - j.1, by omega⟩) := by
          intro h; have := congrArg (fun x => x.1.1) h; dsimp at this; omega
        rw [Finset.card_pair hne, card_filter_pair_cond _ _ hne]
  simp only [noDiagMajority, hcell, isValidPath, pathPairEquiv, Equiv.coe_fn_mk]
  constructor
  · intro h
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · have h0 := h (⟨0, by omega⟩, ⟨0, by omega⟩)
      dsimp at h0; exact Ne.symm h0
    · have h1 := h (⟨k + 1, by omega⟩, ⟨(k + 1) % 2, Nat.mod_lt _ (by omega)⟩)
      have hne0 : k + 1 ≠ 0 := by omega
      simp only [dif_neg hne0] at h1
      dsimp at h1
      have hm : (⟨1 - (k + 1) % 2, by omega⟩ : Fin 2) = ⟨k % 2, Nat.mod_lt _ (by omega)⟩ :=
        Fin.ext (by dsimp; omega)
      rw [hm] at h1; exact h1
    · intro i
      have hmid := h (⟨i.1 + 1, by omega⟩, ⟨(i.1 + 1) % 2, Nat.mod_lt _ (by omega)⟩)
      have hne0 : i.1 + 1 ≠ 0 := by omega
      have hne1 : i.1 + 1 ≠ k + 1 := by have := i.isLt; omega
      simp only [dif_neg hne0, dif_neg hne1] at hmid
      have hm1 : (⟨1 - (i.1 + 1) % 2, by omega⟩ : Fin 2) = ⟨i.1 % 2, Nat.mod_lt _ (by omega)⟩ :=
        Fin.ext (by dsimp; omega)
      have hm2 : (⟨1 - (i.1 + 1) % 2, by omega⟩ : Fin 2) =
          ⟨(i.1 + 2) % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp; omega)
      have hi1 : (⟨i.1 + 1 - 1, by omega⟩ : Fin (k + 2)) = ⟨i.1, by omega⟩ :=
        Fin.ext (Nat.add_sub_cancel i.1 1)
      rintro ⟨ha, hb⟩
      apply hmid
      rw [hi1]
      exact ⟨by rw [hm1]; exact ha, by rw [hm2]; exact hb.symm⟩
    · have h0 := h (⟨0, by omega⟩, ⟨1, by omega⟩)
      dsimp at h0
      exact Ne.symm h0
    · have h1 := h (⟨k + 1, by omega⟩, ⟨(k + 1 + 1) % 2, Nat.mod_lt _ (by omega)⟩)
      have hne0 : k + 1 ≠ 0 := by omega
      simp only [dif_neg hne0] at h1
      dsimp at h1
      have hm : (⟨1 - (k + 1 + 1) % 2, by omega⟩ : Fin 2) =
          ⟨(k + 1) % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp; omega)
      rw [hm] at h1; exact h1
    · intro i
      have hmid := h (⟨i.1 + 1, by omega⟩, ⟨(i.1 + 1 + 1) % 2, Nat.mod_lt _ (by omega)⟩)
      have hne0 : i.1 + 1 ≠ 0 := by omega
      have hne1 : i.1 + 1 ≠ k + 1 := by have := i.isLt; omega
      simp only [dif_neg hne0, dif_neg hne1] at hmid
      have hm1 : (⟨1 - (i.1 + 1 + 1) % 2, by omega⟩ : Fin 2) =
          ⟨(i.1 + 1) % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp; omega)
      have hm2 : (⟨1 - (i.1 + 1 + 1) % 2, by omega⟩ : Fin 2) =
          ⟨(i.1 + 2 + 1) % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp; omega)
      have hi1 : (⟨i.1 + 1 - 1, by omega⟩ : Fin (k + 2)) = ⟨i.1, by omega⟩ :=
        Fin.ext (Nat.add_sub_cancel i.1 1)
      rintro ⟨ha, hb⟩
      apply hmid
      rw [hi1]
      exact ⟨by rw [hm1]; exact ha, by rw [hm2]; exact hb.symm⟩
  · rintro ⟨⟨h00, h01, h0m⟩, ⟨h10, h11, h1m⟩⟩ ⟨i, j⟩
    by_cases hi0 : i.1 = 0
    · rw [dif_pos hi0]
      have hi : i = ⟨0, by omega⟩ := Fin.ext hi0; rw [hi]
      fin_cases j
      · exact Ne.symm h00
      · dsimp; exact Ne.symm h10
    · rw [dif_neg hi0]
      by_cases hi1 : i.1 = k + 1
      · rw [dif_pos hi1]
        have hi : i = ⟨k + 1, by omega⟩ := Fin.ext hi1; rw [hi]
        by_cases hj : j.1 = (k + 1) % 2
        · have hj1 : j = ⟨(k + 1) % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext hj
          have hj2 : (⟨1 - j.1, by omega⟩ : Fin 2) = ⟨k % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by dsimp; omega)
          dsimp; rw [hj2, hj1]; exact h01
        · have hj1 : j = ⟨(k + 1 + 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by have := j.isLt; dsimp; omega)
          have hj2 : (⟨1 - j.1, by omega⟩ : Fin 2) = ⟨(k + 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by have := j.isLt; dsimp; omega)
          dsimp; rw [hj2, hj1]; exact h11
      · rw [dif_neg hi1]
        have hlt : i.1 - 1 < k := by have := i.isLt; omega
        have hi_eq : i = ⟨(i.1 - 1) + 1, by omega⟩ := Fin.ext (by dsimp; omega)
        have hi_p : (⟨i.1 + 1, by omega⟩ : Fin (k + 2)) = ⟨(i.1 - 1) + 2, by omega⟩ :=
          Fin.ext (by dsimp; omega)
        by_cases hj : j.1 = i.1 % 2
        · have hj1 : j = ⟨((i.1 - 1) + 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by dsimp; omega)
          have hj2 : (⟨1 - j.1, by omega⟩ : Fin 2) = ⟨(i.1 - 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by dsimp; omega)
          have hj3 : (⟨1 - j.1, by omega⟩ : Fin 2) =
              ⟨((i.1 - 1) + 2) % 2, Nat.mod_lt _ (by omega)⟩ := Fin.ext (by dsimp; omega)
          rintro ⟨ha, hb⟩
          apply h0m ⟨i.1 - 1, hlt⟩
          refine ⟨?_, ?_⟩
          · rw [← hj2, ← hj1, ← hi_eq]; exact ha
          · rw [← hj3, ← hj1, ← hi_eq, ← hi_p]; exact hb.symm
        · have hj1 : j = ⟨((i.1 - 1) + 1 + 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by have := j.isLt; dsimp; omega)
          have hj2 : (⟨1 - j.1, by omega⟩ : Fin 2) =
              ⟨((i.1 - 1) + 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by have := j.isLt; dsimp; omega)
          have hj3 : (⟨1 - j.1, by omega⟩ : Fin 2) =
              ⟨((i.1 - 1) + 2 + 1) % 2, Nat.mod_lt _ (by omega)⟩ :=
            Fin.ext (by have := j.isLt; dsimp; omega)
          rintro ⟨ha, hb⟩
          apply h1m ⟨i.1 - 1, hlt⟩
          refine ⟨?_, ?_⟩
          · rw [← hj2, ← hj1, ← hi_eq]; exact ha
          · rw [← hj3, ← hj1, ← hi_eq, ← hi_p]; exact hb.symm

private lemma totalValid_eq_sq_pathCount (k : ℕ) :
    totalValid (k + 1) = pathCount k ^ 2 := by
  unfold totalValid pathCount
  have hbij : (Finset.univ.filter (noDiagMajority (k + 1))).card =
      ((Finset.univ.filter (isValidPath k)) ×ˢ (Finset.univ.filter (isValidPath k))).card := by
    refine Finset.card_bij (fun A _ => pathPairEquiv k A) ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hA ⊢
      exact (noDiagMajority_iff_paths k A).mp hA
    · intro A1 _ A2 _ heq
      exact (pathPairEquiv k).injective heq
    · intro P hP
      refine ⟨(pathPairEquiv k).symm P, ?_, (pathPairEquiv k).apply_symm_apply P⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hP ⊢
      rw [noDiagMajority_iff_paths, (pathPairEquiv k).apply_symm_apply]
      exact hP
  rw [hbij, Finset.card_product, sq]

-- S_3-orbit bijection: totalValid (k + 1) = 6 * A231317 (k + 1)
private lemma noDiagMajority_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin 3))
    (A : Fin (n + 1) × Fin 2 → Fin 3) :
    noDiagMajority n (σ ∘ A) ↔ noDiagMajority n A := by
  unfold noDiagMajority
  refine forall_congr' fun p => ?_
  have heq : Finset.univ.filter (fun q => isDiagNeighbor p q = true ∧ (σ ∘ A) q = (σ ∘ A) p) =
      Finset.univ.filter (fun q => isDiagNeighbor p q = true ∧ A q = A p) := by
    ext q; simp [Function.comp_apply, σ.injective.eq_iff]
  rw [heq]

private lemma valid_origin_ne_diag (k : ℕ) (A : Fin (k + 2) × Fin 2 → Fin 3)
    (hA : noDiagMajority (k + 1) A) :
    A (⟨0, by omega⟩, ⟨0, by omega⟩) ≠ A (⟨1, by omega⟩, ⟨1, by omega⟩) := by
  exact ((noDiagMajority_iff_paths k A).mp hA).1.1

private lemma rowMajor_origin_zero (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3)
    (hrm : isRowMajor n A) : A (⟨0, by omega⟩, ⟨0, by omega⟩) = 0 := by
  by_contra hne
  obtain ⟨q, hlt, _⟩ := hrm (⟨0, by omega⟩, ⟨0, by omega⟩) hne
  dsimp at hlt; omega

private def thirdFin3 (a b : Fin 3) : Fin 3 :=
  ⟨(3 - a.1 - b.1) % 3, Nat.mod_lt _ (by omega)⟩

private lemma thirdFin3_spec (a b : Fin 3) (hab : a ≠ b) :
    thirdFin3 a b ≠ a ∧ thirdFin3 a b ≠ b ∧
    ∀ x : Fin 3, x = a ∨ x = b ∨ x = thirdFin3 a b := by
  fin_cases a <;> fin_cases b <;> first | exact (hab rfl).elim | (refine ⟨by decide, by decide, fun x => by fin_cases x <;> decide⟩)

private def mkPerm3 (v0 v1 : Fin 3) (h01 : v0 ≠ v1) : Equiv.Perm (Fin 3) where
  toFun x := if x = 0 then v0 else if x = 1 then v1 else thirdFin3 v0 v1
  invFun y := if y = v0 then 0 else if y = v1 then 1 else 2
  left_inv x := by
    have ⟨h20, h21, _⟩ := thirdFin3_spec v0 v1 h01
    fin_cases x
    · simp
    · simp [h01.symm]
    · simp [h20, h21]
  right_inv y := by
    have ⟨h20, h21, hcov⟩ := thirdFin3_spec v0 v1 h01
    rcases hcov y with rfl | rfl | rfl
    · simp
    · simp [h01.symm]
    · simp [h20, h21]

private lemma totalValid_eq_six_mul_A231317 (k : ℕ) :
    totalValid (k + 1) = 6 * A231317 (k + 1) := by
  unfold totalValid A231317
  set Sall := Finset.univ.filter (noDiagMajority (k + 1))
  set Srm := Finset.univ.filter (fun A : Fin (k + 2) × Fin 2 → Fin 3 =>
    noDiagMajority (k + 1) A ∧ isRowMajor (k + 1) A)
  have hbij : Sall.card = (Finset.univ ×ˢ Srm : Finset (Equiv.Perm (Fin 3) × _)).card := by
    symm
    refine Finset.card_bij (fun p _ => p.1 ∘ p.2) ?_ ?_ ?_
    · intro ⟨σ, A⟩ hp
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Srm, Sall, Finset.mem_filter] at hp ⊢
      exact (noDiagMajority_comp_perm (k + 1) σ A).mpr hp.1
    · rintro ⟨σ1, A1⟩ h1 ⟨σ2, A2⟩ h2 heq
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Srm, Finset.mem_filter] at h1 h2
      have h0_1 := rowMajor_origin_zero (k + 1) A1 h1.2
      have h0_2 := rowMajor_origin_zero (k + 1) A2 h2.2
      have hσ0 : σ1 0 = σ2 0 := by
        have h0 := congrFun heq (⟨0, by omega⟩, ⟨0, by omega⟩)
        simp only [Function.comp_apply] at h0
        rw [h0_1, h0_2] at h0
        exact h0
      have hzero_iff : ∀ p, A1 p = 0 ↔ A2 p = 0 := by
        intro p
        have hp := congrFun heq p
        simp only [Function.comp_apply] at hp
        constructor
        · intro h; rw [h, hσ0] at hp; exact (σ2.injective hp).symm
        · intro h; rw [h, ← hσ0] at hp; exact σ1.injective hp
      have hne_set : (Finset.univ.filter (fun p : Fin (k + 2) × Fin 2 => A1 p ≠ 0)).Nonempty := by
        refine ⟨(⟨1, by omega⟩, ⟨1, by omega⟩), ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro h
        exact valid_origin_ne_diag k A1 h1.1 (by rw [h0_1, h])
      obtain ⟨p1, hp1_mem, hp1_min⟩ :=
        Finset.exists_min_image _ (rowIdx (n := k + 1)) hne_set
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1_mem
      have hA1_p1 : A1 p1 = 1 := by
        have hlt := (A1 p1).isLt
        by_cases h1eq : (A1 p1).1 = 1
        · exact Fin.ext h1eq
        · have h2eq : (A1 p1).1 = 2 := by
            have : (A1 p1).1 ≠ 0 := fun h => hp1_mem (Fin.ext h)
            omega
          obtain ⟨q, hqlt, hqval⟩ := h1.2 p1 hp1_mem
          have hqne : A1 q ≠ 0 := fun h => by rw [h] at hqval; dsimp at hqval; omega
          have hqle := hp1_min q (by simp [hqne])
          unfold rowIdx at hqle; omega
      have hp1_ne2 : A2 p1 ≠ 0 := fun h => hp1_mem ((hzero_iff p1).mpr h)
      have hA2_p1 : A2 p1 = 1 := by
        by_cases h1eq : (A2 p1).1 = 1
        · exact Fin.ext h1eq
        · have h2eq : (A2 p1).1 = 2 := by
            have : (A2 p1).1 ≠ 0 := fun h => hp1_ne2 (Fin.ext h)
            have := (A2 p1).isLt; omega
          obtain ⟨q, hqlt, hqval⟩ := h2.2 p1 hp1_ne2
          have hqne2 : A2 q ≠ 0 := fun h => by rw [h] at hqval; dsimp at hqval; omega
          have hqne1 : A1 q ≠ 0 := fun h => hqne2 ((hzero_iff q).mp h)
          have hqle := hp1_min q (by simp [hqne1])
          unfold rowIdx at hqle; omega
      have hσ1 : σ1 1 = σ2 1 := by
        have := congrFun heq p1
        simpa [Function.comp_apply, hA1_p1, hA2_p1] using this
      have hσ : σ1 = σ2 := by
        ext x
        fin_cases x
        · exact congrArg Fin.val hσ0
        · exact congrArg Fin.val hσ1
        · have hne0 : σ1 0 ≠ σ1 1 := fun h => by have := σ1.injective h; exact absurd this (by decide)
          have ⟨_, _, hcov⟩ := thirdFin3_spec (σ1 0) (σ1 1) hne0
          have ha : σ1 2 = thirdFin3 (σ1 0) (σ1 1) := by
            rcases hcov (σ1 2) with h | h | h
            · exact absurd (σ1.injective h) (by decide)
            · exact absurd (σ1.injective h) (by decide)
            · exact h
          have hb : σ2 2 = thirdFin3 (σ1 0) (σ1 1) := by
            rcases hcov (σ2 2) with h | h | h
            · rw [hσ0] at h; exact absurd (σ2.injective h) (by decide)
            · rw [hσ1] at h; exact absurd (σ2.injective h) (by decide)
            · exact h
          change (σ1 2).1 = (σ2 2).1
          rw [ha, hb]
      subst hσ
      refine Prod.ext rfl (funext fun p => σ1.injective (congrFun heq p))
    · intro A hA
      simp only [Sall, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      set v0 := A (⟨0, by omega⟩, ⟨0, by omega⟩)
      have hne_set : (Finset.univ.filter (fun p : Fin (k + 2) × Fin 2 => A p ≠ v0)).Nonempty := by
        refine ⟨(⟨1, by omega⟩, ⟨1, by omega⟩), ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (valid_origin_ne_diag k A hA).symm
      obtain ⟨p1, hp1_mem, hp1_min⟩ :=
        Finset.exists_min_image _ (rowIdx (n := k + 1)) hne_set
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1_mem
      set v1 := A p1
      have h01 : v0 ≠ v1 := hp1_mem.symm
      let σ : Equiv.Perm (Fin 3) := mkPerm3 v0 v1 h01
      let A' : Fin (k + 2) × Fin 2 → Fin 3 := σ.symm ∘ A
      refine ⟨(σ, A'), ?_, ?_⟩
      · simp only [Finset.mem_product, Finset.mem_univ, true_and, Srm, Finset.mem_filter]
        refine ⟨(noDiagMajority_comp_perm (k + 1) σ.symm A).mpr hA, ?_⟩
        intro p hp
        have hAp0 : A p ≠ v0 := by
          intro h; apply hp; simp only [A', Function.comp_apply, h, σ, mkPerm3, Equiv.symm_mk,
            Equiv.coe_fn_mk, if_true]
        by_cases hAp1 : A p = v1
        · refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), ?_, ?_⟩
          · have hp_ne0 : p ≠ (⟨0, by omega⟩, ⟨0, by omega⟩) := fun h => hAp0 (by rw [h])
            cases p with | mk pi pj =>
              by_contra hle
              dsimp at hle
              have hpi : pi.1 = 0 := by omega
              have hpj : pj.1 = 0 := by omega
              exact hp_ne0 (Prod.ext (Fin.ext hpi) (Fin.ext hpj))
          · have hv0 : A (0, 0) = v0 := rfl
            simp [A', Function.comp_apply, σ, mkPerm3, hv0, hAp1, h01.symm]
        · refine ⟨p1, ?_, ?_⟩
          · have hle : rowIdx p1 ≤ rowIdx p := hp1_min p (by simp [hAp0])
            have hne : p1 ≠ p := fun h => hAp1 (by rw [← h])
            have hlt : rowIdx p1 < rowIdx p := by
              by_contra hge
              have heq_idx : rowIdx p1 = rowIdx p := by omega
              apply hne
              unfold rowIdx at heq_idx
              exact Prod.ext (Fin.ext (by have := p1.2.isLt; have := p.2.isLt; omega))
                (Fin.ext (by have := p1.2.isLt; have := p.2.isLt; omega))
            exact hlt
          · have hv1 : A p1 = v1 := rfl
            simp [A', Function.comp_apply, σ, mkPerm3, hv1, hAp0, hAp1, h01.symm]
      · funext p; simp [A', Function.comp_apply]
  rw [hbij, Finset.card_product, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rfl

-- 9-state transfer matrix for pathCount k
private def stepVec (v : Fin 3 × Fin 3 → ℤ) (r2 : Fin 3 × Fin 3) : ℤ :=
  ∑ r1 : Fin 3 × Fin 3,
    if r1.2 = r2.1 ∧ ¬ (r1.1 = r2.1 ∧ r2.1 = r2.2) then v r1 else 0

private lemma stepVec_add (u v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => u x + v x) r = stepVec u r + stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => c * v x) r = c * stepVec v r := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private def isPrefixValid (k : ℕ) (p : Fin (k + 2) → Fin 3) : Prop :=
  p ⟨0, by omega⟩ ≠ p ⟨1, by omega⟩ ∧
  ∀ i : Fin k, ¬ (p ⟨i.1, by omega⟩ = p ⟨i.1 + 1, by omega⟩ ∧
                   p ⟨i.1 + 1, by omega⟩ = p ⟨i.1 + 2, by omega⟩)

private instance (k : ℕ) (p : Fin (k + 2) → Fin 3) : Decidable (isPrefixValid k p) := by
  unfold isPrefixValid; infer_instance

private def pathVec (k : ℕ) (r : Fin 3 × Fin 3) : ℤ :=
  ∑ p : Fin (k + 2) → Fin 3,
    if isPrefixValid k p ∧ (p ⟨k, by omega⟩, p ⟨k + 1, by omega⟩) = r then 1 else 0

private lemma pathCount_eq_sum_pathVec (k : ℕ) :
    (pathCount k : ℤ) = ∑ r : Fin 3 × Fin 3, if r.1 ≠ r.2 then pathVec k r else 0 := by
  unfold pathCount pathVec
  have hcard : ∀ S : Finset (Fin (k + 2) → Fin 3),
      (S.card : ℤ) = ∑ p : Fin (k + 2) → Fin 3, if p ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  symm
  trans ∑ r : Fin 3 × Fin 3, ∑ p : Fin (k + 2) → Fin 3,
      if isPrefixValid k p ∧ (p ⟨k, by omega⟩, p ⟨k + 1, by omega⟩) = r ∧ r.1 ≠ r.2
      then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : r.1 ≠ r.2 <;> simp [h]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single (p ⟨k, by omega⟩, p ⟨k + 1, by omega⟩)]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isValidPath, isPrefixValid]
      by_cases h1 : p ⟨0, by omega⟩ ≠ p ⟨1, by omega⟩ <;>
        by_cases h2 : p ⟨k, by omega⟩ ≠ p ⟨k + 1, by omega⟩ <;>
        by_cases h3 : ∀ i : Fin k, ¬ (p ⟨i.1, by omega⟩ = p ⟨i.1 + 1, by omega⟩ ∧
          p ⟨i.1 + 1, by omega⟩ = p ⟨i.1 + 2, by omega⟩) <;>
        simp [h2, h3]
    · intro r _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma pathVec_zero (r : Fin 3 × Fin 3) :
    pathVec 0 r = if r.1 ≠ r.2 then 1 else 0 := by
  unfold pathVec isPrefixValid
  let p0 : Fin 2 → Fin 3 := fun i => if i.1 = 0 then r.1 else r.2
  rw [Finset.sum_eq_single p0]
  · simp [p0]
  · intro p _ hne
    rw [if_neg]
    rintro ⟨_, hr⟩
    apply hne
    funext i; fin_cases i
    · exact congrArg Prod.fst hr
    · exact congrArg Prod.snd hr
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma pathVec_succ (k : ℕ) (r : Fin 3 × Fin 3) :
    pathVec (k + 1) r = stepVec (pathVec k) r := by
  let e : (Fin (k + 3) → Fin 3) ≃ ((Fin (k + 2) → Fin 3) × Fin 3) :=
    { toFun := fun p => (fun i => p ⟨i.1, by omega⟩, p ⟨k + 2, by omega⟩)
      invFun := fun ⟨p', c⟩ i => if h : i.1 < k + 2 then p' ⟨i.1, h⟩ else c
      left_inv := fun p => by
        funext i
        by_cases h : i.1 < k + 2
        · simp [h]
        · have hi : i = ⟨k + 2, by omega⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          rw [hi]; simp
      right_inv := fun ⟨p', c⟩ => by
        apply Prod.ext
        · funext i; simp [i.isLt]
        · simp }
  have hiff : ∀ p : Fin (k + 3) → Fin 3,
      (isPrefixValid (k + 1) p ∧ (p ⟨k + 1, by omega⟩, p ⟨k + 2, by omega⟩) = r) ↔
      (isPrefixValid k (e p).1 ∧
       (e p).1 ⟨k + 1, by omega⟩ = r.1 ∧ (e p).2 = r.2 ∧
       ¬ ((e p).1 ⟨k, by omega⟩ = r.1 ∧ r.1 = r.2)) := by
    intro p
    simp only [e, Equiv.coe_fn_mk, isPrefixValid]
    constructor
    · rintro ⟨⟨h0, hno3⟩, hr⟩
      have hr1 := congrArg Prod.fst hr
      have hr2 := congrArg Prod.snd hr
      dsimp at hr1 hr2
      refine ⟨⟨h0, fun i => hno3 ⟨i.1, by omega⟩⟩, hr1, hr2, ?_⟩
      rw [← hr1, ← hr2]; exact hno3 ⟨k, by omega⟩
    · rintro ⟨⟨h0, hno3⟩, hr1, hr2, hlast⟩
      refine ⟨⟨h0, fun i => ?_⟩, Prod.ext hr1 hr2⟩
      by_cases hi : i.1 < k
      · exact hno3 ⟨i.1, hi⟩
      · have hieq : i = ⟨k, by omega⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        rw [hieq]; dsimp; rw [hr1, hr2]; exact hlast
  unfold pathVec stepVec
  rw [Fintype.sum_equiv e _ (fun q =>
      if isPrefixValid k q.1 ∧ q.1 ⟨k + 1, by omega⟩ = r.1 ∧ q.2 = r.2 ∧
         ¬ (q.1 ⟨k, by omega⟩ = r.1 ∧ r.1 = r.2) then (1 : ℤ) else 0)
      (fun p => by simp only [hiff p])]
  rw [Fintype.sum_prod_type]
  have hc_sum : ∀ p' : Fin (k + 2) → Fin 3,
      (∑ c : Fin 3,
        if isPrefixValid k p' ∧ p' ⟨k + 1, by omega⟩ = r.1 ∧ c = r.2 ∧
           ¬ (p' ⟨k, by omega⟩ = r.1 ∧ r.1 = r.2) then (1 : ℤ) else 0) =
      if isPrefixValid k p' ∧ p' ⟨k + 1, by omega⟩ = r.1 ∧
         ¬ (p' ⟨k, by omega⟩ = r.1 ∧ r.1 = r.2) then (1 : ℤ) else 0 := by
    intro p'
    rw [Finset.sum_eq_single r.2]
    · simp
    · intro c _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hc_sum]
  symm
  trans ∑ r1 : Fin 3 × Fin 3, ∑ p' : Fin (k + 2) → Fin 3,
      if isPrefixValid k p' ∧ (p' ⟨k, by omega⟩, p' ⟨k + 1, by omega⟩) = r1 ∧
         r1.2 = r.1 ∧ ¬ (r1.1 = r.1 ∧ r.1 = r.2) then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => ?_
    by_cases h : r1.2 = r.1 ∧ ¬ (r1.1 = r.1 ∧ r.1 = r.2)
    · simp [h]
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun p' _ => ?_).symm
      split_ifs with hp
      · exact (h ⟨hp.2.2.1, hp.2.2.2⟩).elim
      · rfl
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p' _ => ?_
    rw [Finset.sum_eq_single (p' ⟨k, by omega⟩, p' ⟨k + 1, by omega⟩)]
    · simp
    · intro r1 _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma pathVec_zero_fun : pathVec 0 = fun r => if r.1 ≠ r.2 then 1 else 0 :=
  funext pathVec_zero
private lemma pathVec_succ_fun (k : ℕ) : pathVec (k + 1) = stepVec (pathVec k) :=
  funext (pathVec_succ k)

private lemma pathVec_rec_base :
    pathVec 2 = fun r => 2 * pathVec 1 r + 2 * pathVec 0 r := by
  funext r
  simp only [pathVec_succ_fun, pathVec_zero_fun]
  revert r; decide

private lemma pathVec_rec (k : ℕ) :
    pathVec (k + 2) = fun r => 2 * pathVec (k + 1) r + 2 * pathVec k r := by
  induction k with
  | zero => exact pathVec_rec_base
  | succ k ih =>
    funext r
    conv_lhs =>
      rw [pathVec_succ (k + 2) r, ih, stepVec_add, stepVec_smul, stepVec_smul,
        ← pathVec_succ (k + 1) r, ← pathVec_succ k r]

private lemma pathCount_rec (k : ℕ) :
    (pathCount (k + 2) : ℤ) = 2 * pathCount (k + 1) + 2 * pathCount k := by
  simp only [pathCount_eq_sum_pathVec, pathVec_rec k]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> ring

private lemma pathCount_small : pathCount 0 = 6 ∧ pathCount 1 = 12 := by
  have h0 : (pathCount 0 : ℤ) = 6 := by
    rw [pathCount_eq_sum_pathVec, pathVec_zero_fun]; decide
  have h1 : (pathCount 1 : ℤ) = 12 := by
    rw [pathCount_eq_sum_pathVec, pathVec_succ_fun, pathVec_zero_fun]; decide
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

private lemma pathCount_closed (k : ℕ) :
    (pathCount k : ℝ) = Real.sqrt 3 * ((1 + Real.sqrt 3) ^ (k + 1) - (1 - Real.sqrt 3) ^ (k + 1)) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 3
  have hr1 : (1 + s) ^ 2 = 2 * (1 + s) + 2 := by
    have : (1 + s) ^ 2 - (2 * (1 + s) + 2) = s ^ 2 - 3 := by ring
    linarith [this, hs]
  have hr2 : (1 - s) ^ 2 = 2 * (1 - s) + 2 := by
    have : (1 - s) ^ 2 - (2 * (1 - s) + 2) = s ^ 2 - 3 := by ring
    linarith [this, hs]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h0, h1⟩ := pathCount_small
    rcases k with _ | _ | m
    · rw [h0]; norm_num
      have : s * (s + s) = 2 * s ^ 2 := by ring
      rw [this, hs]; ring
    · rw [h1]; norm_num
      have : s * ((1 + s) ^ 2 - (1 - s) ^ 2) = 4 * s ^ 2 := by ring
      rw [this, hs]; ring
    · have hrec : (pathCount (m + 2) : ℝ) = 2 * pathCount (m + 1) + 2 * pathCount m := by
        exact_mod_cast pathCount_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have hp1 : (1 + s) ^ (m + 3) = 2 * (1 + s) ^ (m + 2) + 2 * (1 + s) ^ (m + 1) := by
        calc (1 + s) ^ (m + 3) = (1 + s) ^ 2 * (1 + s) ^ (m + 1) := by ring
          _ = (2 * (1 + s) + 2) * (1 + s) ^ (m + 1) := by rw [hr1]
          _ = 2 * (1 + s) ^ (m + 2) + 2 * (1 + s) ^ (m + 1) := by ring
      have hp2 : (1 - s) ^ (m + 3) = 2 * (1 - s) ^ (m + 2) + 2 * (1 - s) ^ (m + 1) := by
        calc (1 - s) ^ (m + 3) = (1 - s) ^ 2 * (1 - s) ^ (m + 1) := by ring
          _ = (2 * (1 - s) + 2) * (1 - s) ^ (m + 1) := by rw [hr2]
          _ = 2 * (1 - s) ^ (m + 2) + 2 * (1 - s) ^ (m + 1) := by ring
      rw [hrec, ih1, ih0, show m + 2 + 1 = m + 3 by omega, hp1, hp2]
      ring

private lemma A231317_closed (n : ℕ) (hn : 1 ≤ n) :
    (A231317 n : ℝ) =
      ((-2 : ℝ) ^ (1 + n) + (4 - 2 * Real.sqrt 3) ^ n + (2 * (2 + Real.sqrt 3)) ^ n) / 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have hrel : (6 : ℝ) * (A231317 (k + 1) : ℝ) = (pathCount k : ℝ) ^ 2 := by
    have h1 := totalValid_eq_six_mul_A231317 k
    have h2 := totalValid_eq_sq_pathCount k
    have h3 : 6 * A231317 (k + 1) = pathCount k ^ 2 := by omega
    exact_mod_cast h3
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 3
  have ha : (1 + s) ^ 2 = 2 * (2 + s) := by
    have : (1 + s) ^ 2 - 2 * (2 + s) = s ^ 2 - 3 := by ring
    linarith [this, hs]
  have hb : (1 - s) ^ 2 = 4 - 2 * s := by
    have : (1 - s) ^ 2 - (4 - 2 * s) = s ^ 2 - 3 := by ring
    linarith [this, hs]
  have hab : (1 + s) * (1 - s) = -2 := by
    have : (1 + s) * (1 - s) - (-2) = -(s ^ 2 - 3) := by ring
    linarith [this, hs]
  have hsq : (pathCount k : ℝ) ^ 2 =
      3 * ((-2 : ℝ) ^ (1 + (k + 1)) + (4 - 2 * s) ^ (k + 1) + (2 * (2 + s)) ^ (k + 1)) := by
    rw [pathCount_closed k]
    have h1 : (s * ((1 + s) ^ (k + 1) - (1 - s) ^ (k + 1))) ^ 2 =
        s ^ 2 * (((1 + s) ^ 2) ^ (k + 1) - 2 * ((1 + s) * (1 - s)) ^ (k + 1) +
          ((1 - s) ^ 2) ^ (k + 1)) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (k + 1), pow_mul, pow_mul]; ring
    rw [h1, hs, ha, hb, hab, show 1 + (k + 1) = (k + 1) + 1 by omega, pow_succ]
    ring
  linarith

private lemma A231317_small : A231317 1 = 6 ∧ A231317 2 = 24 ∧ A231317 3 = 216 := by
  obtain ⟨h0, h1⟩ := pathCount_small
  have h2 : pathCount 2 = 36 := by
    have := pathCount_rec 0; rw [h0, h1] at this; exact_mod_cast this
  have ha1 : 6 * A231317 1 = pathCount 0 ^ 2 := by
    rw [← totalValid_eq_six_mul_A231317 0, totalValid_eq_sq_pathCount 0]
  have ha2 : 6 * A231317 2 = pathCount 1 ^ 2 := by
    rw [← totalValid_eq_six_mul_A231317 1, totalValid_eq_sq_pathCount 1]
  have ha3 : 6 * A231317 3 = pathCount 2 ^ 2 := by
    rw [← totalValid_eq_six_mul_A231317 2, totalValid_eq_sq_pathCount 2]
  rw [h0] at ha1; rw [h1] at ha2; rw [h2] at ha3
  omega

private lemma A231317_rec (m : ℕ) :
    (A231317 (m + 4) : ℤ) =
      6 * A231317 (m + 3) + 12 * A231317 (m + 2) - 8 * A231317 (m + 1) := by
  suffices h : (A231317 (m + 4) : ℝ) =
      6 * A231317 (m + 3) + 12 * A231317 (m + 2) - 8 * A231317 (m + 1) by
    exact_mod_cast h
  rw [A231317_closed (m + 4) (by omega), A231317_closed (m + 3) (by omega),
    A231317_closed (m + 2) (by omega), A231317_closed (m + 1) (by omega)]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 3
  set u := 4 - 2 * s
  set v := 2 * (2 + s)
  have hu : u ^ 2 = 8 * u - 4 := by
    have : u ^ 2 - (8 * u - 4) = 4 * (s ^ 2 - 3) := by simp only [u]; ring
    linarith [this, hs]
  have hv : v ^ 2 = 8 * v - 4 := by
    have : v ^ 2 - (8 * v - 4) = 4 * (s ^ 2 - 3) := by simp only [v]; ring
    linarith [this, hs]
  have hu3 : u ^ (m + 4) = 6 * u ^ (m + 3) + 12 * u ^ (m + 2) - 8 * u ^ (m + 1) := by
    have hcub : u ^ 3 = 6 * u ^ 2 + 12 * u - 8 := by
      calc u ^ 3 = u * u ^ 2 := by ring
        _ = u * (8 * u - 4) := by rw [hu]
        _ = 8 * u ^ 2 - 4 * u := by ring
        _ = 6 * u ^ 2 + 2 * (8 * u - 4) - 4 * u := by rw [← hu]; ring
        _ = 6 * u ^ 2 + 12 * u - 8 := by ring
    calc u ^ (m + 4) = u ^ 3 * u ^ (m + 1) := by ring
      _ = (6 * u ^ 2 + 12 * u - 8) * u ^ (m + 1) := by rw [hcub]
      _ = 6 * u ^ (m + 3) + 12 * u ^ (m + 2) - 8 * u ^ (m + 1) := by ring
  have hv3 : v ^ (m + 4) = 6 * v ^ (m + 3) + 12 * v ^ (m + 2) - 8 * v ^ (m + 1) := by
    have hcub : v ^ 3 = 6 * v ^ 2 + 12 * v - 8 := by
      calc v ^ 3 = v * v ^ 2 := by ring
        _ = v * (8 * v - 4) := by rw [hv]
        _ = 8 * v ^ 2 - 4 * v := by ring
        _ = 6 * v ^ 2 + 2 * (8 * v - 4) - 4 * v := by rw [← hv]; ring
        _ = 6 * v ^ 2 + 12 * v - 8 := by ring
    calc v ^ (m + 4) = v ^ 3 * v ^ (m + 1) := by ring
      _ = (6 * v ^ 2 + 12 * v - 8) * v ^ (m + 1) := by rw [hcub]
      _ = 6 * v ^ (m + 3) + 12 * v ^ (m + 2) - 8 * v ^ (m + 1) := by ring
  have hw3 : (-2 : ℝ) ^ (1 + (m + 4)) =
      6 * (-2 : ℝ) ^ (1 + (m + 3)) + 12 * (-2 : ℝ) ^ (1 + (m + 2)) -
      8 * (-2 : ℝ) ^ (1 + (m + 1)) := by
    rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega,
      show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega,
      show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_add, pow_add, pow_add]
    ring
  linarith

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A231317_gf :
    (1 + 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X + 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A231317 n : ℤ)) =
      6 * PowerSeries.X * (1 - 2 * PowerSeries.X) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A231317 n : ℤ))
  have hlhs : (1 + 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X + 4 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 6 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 12 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 8 * (PowerSeries.X ^ 3 * F) := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h12 : PowerSeries.C (12 : ℤ) = (12 : PowerSeries ℤ) := rfl
    have h8 : PowerSeries.C (8 : ℤ) = (8 : PowerSeries ℤ) := rfl
    rw [h6, h12, h8, pow_one]; ring
  have hrhs : 6 * (PowerSeries.X : PowerSeries ℤ) * (1 - 2 * PowerSeries.X) =
      PowerSeries.C 6 * PowerSeries.X - PowerSeries.C 12 * PowerSeries.X ^ 2 := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h12 : PowerSeries.C (12 : ℤ) = (12 : PowerSeries ℤ) := rfl
    rw [h6, h12]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A231317_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero]
    have hrec := A231317_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

end OMA.P_oeis_a231317

theorem OMA.solution : type_of% @OMA.S_oeis_a231317.main :=
  ⟨OMA.P_oeis_a231317.A231317_gf, OMA.P_oeis_a231317.A231317_closed⟩
