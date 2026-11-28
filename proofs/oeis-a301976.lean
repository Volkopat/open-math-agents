import OMAStatements.S_oeis_a301976
import Mathlib.Tactic

namespace OMA.P_oeis_a301976

open OMA.S_oeis_a301976

/-! ### Part 1: Transfer-matrix representation of `A301976 (k + 1)` -/

private def b2n (b : Bool) : ℕ := if b then 1 else 0

private def cap2 (m : ℕ) : Fin 3 :=
  if h : m < 2 then ⟨m, by omega⟩ else ⟨2, by omega⟩

private lemma cap2_val (m : ℕ) : (cap2 m).1 = min m 2 := by
  unfold cap2
  split_ifs with h
  · simp [Nat.min_eq_left (by omega : m ≤ 2)]
  · simp [Nat.min_eq_right (by omega : 2 ≤ m)]

private def initState (v01 v12 : Bool) : Fin 3 × Fin 3 × Fin 3 :=
  (cap2 (b2n v01), cap2 (b2n v01 + b2n v12), cap2 (b2n v12))

private def nextState (h0 h1 h2 v01 v12 : Bool) : Fin 3 × Fin 3 × Fin 3 :=
  (cap2 (b2n h0 + b2n v01), cap2 (b2n h1 + b2n v01 + b2n v12), cap2 (b2n h2 + b2n v12))

private def validPrev (s : Fin 3 × Fin 3 × Fin 3) (h0 h1 h2 : Bool) : Prop :=
  s.1.1 + b2n h0 ≠ 1 ∧ s.2.1.1 + b2n h1 ≠ 1 ∧ s.2.2.1 + b2n h2 ≠ 1

private instance (s : Fin 3 × Fin 3 × Fin 3) (h0 h1 h2 : Bool) :
    Decidable (validPrev s h0 h1 h2) := by
  unfold validPrev; infer_instance

private def lastState (k : ℕ) (p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool)) :
    Fin 3 × Fin 3 × Fin 3 :=
  (cap2 (gridDeg (k + 1) p.1 p.2 0 ⟨k, by omega⟩),
   cap2 (gridDeg (k + 1) p.1 p.2 1 ⟨k, by omega⟩),
   cap2 (gridDeg (k + 1) p.1 p.2 2 ⟨k, by omega⟩))

private def validPrefix (k : ℕ) (p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool)) : Prop :=
  ∀ (i : Fin 3) (j : Fin (k + 1)), j.1 < k → gridDeg (k + 1) p.1 p.2 i j ≠ 1

private instance (k : ℕ) (p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool)) :
    Decidable (validPrefix k p) := by
  unfold validPrefix; infer_instance

private def partialCount (k : ℕ) (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
    if validPrefix k p ∧ lastState k p = s then 1 else 0

private def stepVec (w : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  ∑ h0 : Bool, ∑ h1 : Bool, ∑ h2 : Bool, ∑ v01 : Bool, ∑ v12 : Bool,
    if nextState h0 h1 h2 v01 v12 = s then
      ∑ a' ∈ ({(if h0 then (1 : Fin 3) else 0), 2} : Finset (Fin 3)),
        ∑ b' ∈ ({(if h1 then (1 : Fin 3) else 0), 2} : Finset (Fin 3)),
          ∑ c' ∈ ({(if h2 then (1 : Fin 3) else 0), 2} : Finset (Fin 3)),
            w (a', b', c')
    else 0

private lemma sum_validPrev_eq (w : Fin 3 × Fin 3 × Fin 3 → ℤ) (h0 h1 h2 : Bool) :
    (∑ s' : Fin 3 × Fin 3 × Fin 3, if validPrev s' h0 h1 h2 then w s' else 0) =
      ∑ a' ∈ ({(if h0 then (1 : Fin 3) else 0), 2} : Finset (Fin 3)),
        ∑ b' ∈ ({(if h1 then (1 : Fin 3) else 0), 2} : Finset (Fin 3)),
          ∑ c' ∈ ({(if h2 then (1 : Fin 3) else 0), 2} : Finset (Fin 3)),
            w (a', b', c') := by
  have hfin : ∀ (h : Bool) (f : Fin 3 → ℤ),
      (∑ x : Fin 3, if x.1 + b2n h ≠ 1 then f x else 0) =
        ∑ x ∈ ({(if h then (1 : Fin 3) else 0), 2} : Finset (Fin 3)), f x := by
    intro h f
    cases h <;> simp [Fin.sum_univ_three, b2n]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hsplit : ∀ (a b c : Fin 3),
      (if validPrev (a, b, c) h0 h1 h2 then w (a, b, c) else 0) =
      if a.1 + b2n h0 ≠ 1 then
        if b.1 + b2n h1 ≠ 1 then
          if c.1 + b2n h2 ≠ 1 then w (a, b, c) else 0
        else 0
      else 0 := by
    intro a b c; unfold validPrev
    by_cases ha : a.1 + b2n h0 ≠ 1 <;> by_cases hb : b.1 + b2n h1 ≠ 1 <;>
    by_cases hc : c.1 + b2n h2 ≠ 1 <;> simp [ha, hb, hc]
  have hpull : ∀ (P : Prop) [Decidable P] (f : Fin 3 → ℤ),
      (∑ x : Fin 3, if P then f x else 0) = if P then ∑ x : Fin 3, f x else 0 := by
    intro P _ f; split_ifs <;> simp
  simp_rw [hsplit, hpull]
  rw [hfin h0]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hfin h1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hfin h2]

private lemma stepVec_eq_sum (w : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) :
    stepVec w s =
      ∑ h0 : Bool, ∑ h1 : Bool, ∑ h2 : Bool, ∑ v01 : Bool, ∑ v12 : Bool,
        ∑ s' : Fin 3 × Fin 3 × Fin 3,
          if validPrev s' h0 h1 h2 ∧ nextState h0 h1 h2 v01 v12 = s then w s' else 0 := by
  unfold stepVec
  simp_rw [← sum_validPrev_eq]
  refine Finset.sum_congr rfl fun h0 _ =>
    Finset.sum_congr rfl fun h1 _ =>
    Finset.sum_congr rfl fun h2 _ =>
    Finset.sum_congr rfl fun v01 _ =>
    Finset.sum_congr rfl fun v12 _ => ?_
  split_ifs with hn
  · refine Finset.sum_congr rfl fun s' _ => by simp [hn]
  · symm; apply Finset.sum_eq_zero; intro s' _; simp [hn]

private lemma stepVec_linear (c₁ c₂ c₃ c₄ : ℤ)
    (w₁ w₂ w₃ w₄ : Fin 3 × Fin 3 × Fin 3 → ℤ) (s : Fin 3 × Fin 3 × Fin 3) :
    stepVec (fun x => c₁ * w₁ x + c₂ * w₂ x + c₃ * w₃ x + c₄ * w₄ x) s =
      c₁ * stepVec w₁ s + c₂ * stepVec w₂ s + c₃ * stepVec w₃ s + c₄ * stepVec w₄ s := by
  unfold stepVec
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hite : ∀ (P : Prop) [Decidable P] (a b c d : ℤ),
      (if P then c₁ * a + c₂ * b + c₃ * c + c₄ * d else 0) =
        c₁ * (if P then a else 0) + c₂ * (if P then b else 0) +
        c₃ * (if P then c else 0) + c₄ * (if P then d else 0) := by
    intro P _ a b c d; split_ifs <;> ring
  simp only [hite, Finset.sum_add_distrib, ← Finset.mul_sum]

private def vVec : ℕ → Fin 3 × Fin 3 × Fin 3 → ℤ
  | 0, s => ∑ v01 : Bool, ∑ v12 : Bool, if initState v01 v12 = s then 1 else 0
  | k + 1, s => stepVec (vVec k) s

private lemma partialCount_zero (s : Fin 3 × Fin 3 × Fin 3) :
    partialCount 0 s = vVec 0 s := by
  unfold partialCount vVec
  let e : ((Fin 2 × Fin 1 → Bool) × (Fin 3 × Fin 0 → Bool)) ≃ (Bool × Bool) :=
    { toFun := fun p => (p.1 (0, 0), p.1 (1, 0))
      invFun := fun v => (fun q => if q.1 = 0 then v.1 else v.2, fun q => Fin.elim0 q.2)
      left_inv := fun ⟨V, H⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
        · funext ⟨_, j⟩; exact Fin.elim0 j
      right_inv := fun ⟨_, _⟩ => rfl }
  have hsum : (∑ v : Bool × Bool, if initState v.1 v.2 = s then (1 : ℤ) else 0) =
      ∑ v01 : Bool, ∑ v12 : Bool, if initState v01 v12 = s then (1 : ℤ) else 0 :=
    Fintype.sum_prod_type _
  rw [← hsum]
  exact Fintype.sum_equiv e _ (fun v => if initState v.1 v.2 = s then (1 : ℤ) else 0) (fun ⟨V, H⟩ => by
    have hv : validPrefix 0 (V, H) := fun _ j hj => by omega
    have hl : lastState 0 (V, H) = initState (V (0, 0)) (V (1, 0)) := by
      simp [lastState, initState, gridDeg, b2n]
    simp [e, hv, hl])

private lemma partialCount_succ (k : ℕ) (s : Fin 3 × Fin 3 × Fin 3) :
    partialCount (k + 1) s = stepVec (partialCount k) s := by
  let e : ((Fin 2 × Fin (k + 2) → Bool) × (Fin 3 × Fin (k + 1) → Bool)) ≃
      (((Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool)) ×
       ((Bool × Bool × Bool) × (Bool × Bool))) :=
    { toFun := fun ⟨V, H⟩ =>
        ((fun p => V (p.1, ⟨p.2.1, by omega⟩), fun p => H (p.1, ⟨p.2.1, by omega⟩)),
         ((H (0, ⟨k, by omega⟩), H (1, ⟨k, by omega⟩), H (2, ⟨k, by omega⟩)),
          (V (0, ⟨k + 1, by omega⟩), V (1, ⟨k + 1, by omega⟩))))
      invFun := fun ⟨⟨V', H'⟩, ⟨⟨h0, h1, h2⟩, ⟨v01, v12⟩⟩⟩ =>
        (fun p => if hj : p.2.1 < k + 1 then V' (p.1, ⟨p.2.1, hj⟩) else if p.1 = 0 then v01 else v12,
         fun p => if hj : p.2.1 < k then H' (p.1, ⟨p.2.1, hj⟩)
                  else match p.1.1 with | 0 => h0 | 1 => h1 | _ => h2)
      left_inv := fun ⟨V, H⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩
          by_cases hj : j.1 < k + 1
          · simp [hj]
          · have hlt := j.isLt
            have hjeq : j = ⟨k + 1, Nat.lt_succ_self (k + 1)⟩ := Fin.ext (by dsimp; omega)
            subst hjeq; fin_cases i <;> simp
        · funext ⟨i, j⟩
          by_cases hj : j.1 < k
          · simp [hj]
          · have hlt := j.isLt
            have hjeq : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; omega)
            subst hjeq; fin_cases i <;> simp
      right_inv := fun ⟨⟨V', H'⟩, ⟨⟨h0, h1, h2⟩, ⟨v01, v12⟩⟩⟩ => by
        apply Prod.ext
        · apply Prod.ext
          · funext ⟨i, j⟩; simp [j.2]
          · funext ⟨i, j⟩; simp [j.2]
        · simp }
  have hdeg_lt : ∀ (V : Fin 2 × Fin (k + 2) → Bool) (H : Fin 3 × Fin (k + 1) → Bool)
      (i : Fin 3) (j : Fin (k + 1)), j.1 < k →
      gridDeg (k + 2) V H i ⟨j.1, by omega⟩ =
        gridDeg (k + 1) (fun p => V (p.1, ⟨p.2.1, by omega⟩))
          (fun p => H (p.1, ⟨p.2.1, by omega⟩)) i j := by
    intro V H i j hj; unfold gridDeg
    simp only [show j.1 + 1 < k + 2 by omega, show j.1 + 1 < k + 1 by omega, ↓reduceDIte]
  have hdeg_k : ∀ (V : Fin 2 × Fin (k + 2) → Bool) (H : Fin 3 × Fin (k + 1) → Bool) (i : Fin 3),
      gridDeg (k + 2) V H i ⟨k, by omega⟩ =
        gridDeg (k + 1) (fun p => V (p.1, ⟨p.2.1, by omega⟩))
          (fun p => H (p.1, ⟨p.2.1, by omega⟩)) i ⟨k, by omega⟩ +
        b2n (H (i, ⟨k, by omega⟩)) := by
    intro V H i; unfold gridDeg b2n
    simp only [show k + 1 < k + 2 by omega, show ¬ (k + 1 < k + 1) by omega, ↓reduceDIte, add_zero]
  have hdeg_last : ∀ (V : Fin 2 × Fin (k + 2) → Bool) (H : Fin 3 × Fin (k + 1) → Bool),
      lastState (k + 1) (V, H) =
      nextState (H (0, ⟨k, by omega⟩)) (H (1, ⟨k, by omega⟩)) (H (2, ⟨k, by omega⟩))
        (V (0, ⟨k + 1, by omega⟩)) (V (1, ⟨k + 1, by omega⟩)) := by
    intro V H
    simp only [lastState, nextState, gridDeg, b2n, show 0 < k + 1 by omega,
      show ¬ (k + 1 + 1 < k + 2) by omega, ↓reduceDIte, Nat.add_sub_cancel, add_zero, Prod.mk.injEq,
      Fin.val_zero, Fin.val_one, Fin.val_two]
    refine ⟨congrArg cap2 (add_comm _ _), congrArg cap2 (by ring), congrArg cap2 (add_comm _ _)⟩
  have hcap_ne1 : ∀ (d : ℕ) (b : Bool), d + b2n b ≠ 1 ↔ (cap2 d).1 + b2n b ≠ 1 := by
    intro d b; rw [cap2_val]; unfold b2n; cases b <;> simp <;> try omega
  have hiff : ∀ p : (Fin 2 × Fin (k + 2) → Bool) × (Fin 3 × Fin (k + 1) → Bool),
      (validPrefix (k + 1) p ∧ lastState (k + 1) p = s) ↔
      (validPrefix k (e p).1 ∧
       validPrev (lastState k (e p).1) (e p).2.1.1 (e p).2.1.2.1 (e p).2.1.2.2 ∧
       nextState (e p).2.1.1 (e p).2.1.2.1 (e p).2.1.2.2 (e p).2.2.1 (e p).2.2.2 = s) := by
    intro ⟨V, H⟩
    simp only [e, Equiv.coe_fn_mk]
    constructor
    · rintro ⟨hprev, hlast⟩
      refine ⟨fun i j hj => ?_, ?_, ?_⟩
      · have h1 := hdeg_lt V H i j hj
        have h2 := hprev i ⟨j.1, by omega⟩ (by dsimp; omega)
        exact h1 ▸ h2
      · unfold validPrev lastState
        refine ⟨(hcap_ne1 _ _).mp ?_, (hcap_ne1 _ _).mp ?_, (hcap_ne1 _ _).mp ?_⟩
        · exact (hdeg_k V H 0) ▸ (hprev 0 ⟨k, by omega⟩ (by dsimp; omega))
        · exact (hdeg_k V H 1) ▸ (hprev 1 ⟨k, by omega⟩ (by dsimp; omega))
        · exact (hdeg_k V H 2) ▸ (hprev 2 ⟨k, by omega⟩ (by dsimp; omega))
      · rw [← hdeg_last V H]; exact hlast
    · rintro ⟨hprev', hval, hnext⟩
      refine ⟨fun i j hj => ?_, by rw [hdeg_last V H]; exact hnext⟩
      by_cases hlt : j.1 < k
      · have := hdeg_lt V H i ⟨j.1, by omega⟩ hlt
        have hjeq : (⟨j.1, by omega⟩ : Fin (k + 2)) = j := Fin.ext rfl
        rw [hjeq] at this
        rw [this]; exact hprev' i ⟨j.1, by omega⟩ hlt
      · have hjk : j = ⟨k, by omega⟩ := Fin.ext (by dsimp; omega)
        rw [hjk, hdeg_k V H i, hcap_ne1]
        unfold validPrev lastState at hval
        fin_cases i
        · exact hval.1
        · exact hval.2.1
        · exact hval.2.2
  rw [partialCount]
  rw [Fintype.sum_equiv e _ (fun q =>
      if validPrefix k q.1 ∧ validPrev (lastState k q.1) q.2.1.1 q.2.1.2.1 q.2.1.2.2 ∧
         nextState q.2.1.1 q.2.1.2.1 q.2.1.2.2 q.2.2.1 q.2.2.2 = s then (1 : ℤ) else 0)
      (fun p => by simp only [hiff p])]
  rw [Fintype.sum_prod_type, Finset.sum_comm, stepVec_eq_sum]
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext x
    rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext h0
    rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun h0 _ =>
    Finset.sum_congr rfl fun h1 _ =>
    Finset.sum_congr rfl fun h2 _ =>
    Finset.sum_congr rfl fun v01 _ =>
    Finset.sum_congr rfl fun v12 _ => ?_
  simp only [partialCount]
  have hfiber : ∀ (_ : Unit),
      (∑ s' : Fin 3 × Fin 3 × Fin 3,
        if validPrev s' h0 h1 h2 ∧ nextState h0 h1 h2 v01 v12 = s then
          ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
            if validPrefix k p ∧ lastState k p = s' then (1 : ℤ) else 0
        else 0) =
      ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
        if validPrefix k p ∧ validPrev (lastState k p) h0 h1 h2 ∧
           nextState h0 h1 h2 v01 v12 = s then (1 : ℤ) else 0 := by
    intro _
    have hpush : ∀ s' : Fin 3 × Fin 3 × Fin 3,
        (if validPrev s' h0 h1 h2 ∧ nextState h0 h1 h2 v01 v12 = s then
          ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
            if validPrefix k p ∧ lastState k p = s' then (1 : ℤ) else 0
        else 0) =
        ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
          if (validPrev s' h0 h1 h2 ∧ nextState h0 h1 h2 v01 v12 = s) ∧
             (validPrefix k p ∧ lastState k p = s') then (1 : ℤ) else 0 := by
      intro s'
      split_ifs with h
      · refine Finset.sum_congr rfl fun p _ => by simp [h]
      · symm; apply Finset.sum_eq_zero; intro p _; simp [h]
    simp_rw [hpush]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single (lastState k p)]
    · by_cases hp1 : validPrefix k p <;> by_cases hp2 : validPrev (lastState k p) h0 h1 h2 <;>
      by_cases hp3 : nextState h0 h1 h2 v01 v12 = s <;> simp [hp1, hp2, hp3]
    · intro s' _ hne; simp [Ne.symm hne]
    · intro hnot; exfalso; exact hnot (Finset.mem_univ _)
  exact (hfiber ()).symm

private lemma partialCount_eq_vVec (k : ℕ) (s : Fin 3 × Fin 3 × Fin 3) :
    partialCount k s = vVec k s := by
  induction k generalizing s with
  | zero => exact partialCount_zero s
  | succ k ih =>
    rw [partialCount_succ, vVec]
    have hfun : partialCount k = vVec k := funext ih
    rw [hfun]

private def dotEnd (w : Fin 3 × Fin 3 × Fin 3 → ℤ) : ℤ :=
  ∑ s : Fin 3 × Fin 3 × Fin 3,
    if s.1.1 ≠ 1 ∧ s.2.1.1 ≠ 1 ∧ s.2.2.1 ≠ 1 then w s else 0

private lemma A301976_eq_dotEnd (k : ℕ) :
    (A301976 (k + 1) : ℤ) = dotEnd (vVec k) := by
  unfold A301976 dotEnd
  simp_rw [← partialCount_eq_vVec, partialCount]
  rw [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpush : ∀ s : Fin 3 × Fin 3 × Fin 3,
      (if s.1.1 ≠ 1 ∧ s.2.1.1 ≠ 1 ∧ s.2.2.1 ≠ 1 then
        ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
          if validPrefix k p ∧ lastState k p = s then (1 : ℤ) else 0
      else 0) =
      ∑ p : (Fin 2 × Fin (k + 1) → Bool) × (Fin 3 × Fin k → Bool),
        if (s.1.1 ≠ 1 ∧ s.2.1.1 ≠ 1 ∧ s.2.2.1 ≠ 1) ∧
           (validPrefix k p ∧ lastState k p = s) then (1 : ℤ) else 0 := by
    intro s
    split_ifs with h
    · refine Finset.sum_congr rfl fun p _ => by simp [h]
    · symm; apply Finset.sum_eq_zero; intro p _; simp [h]
  simp_rw [hpush]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single (lastState k p)]
  · have hiff : (∀ (i : Fin 3) (j : Fin (k + 1)), gridDeg (k + 1) p.1 p.2 i j ≠ 1) ↔
        (((lastState k p).1.1 ≠ 1 ∧ (lastState k p).2.1.1 ≠ 1 ∧ (lastState k p).2.2.1 ≠ 1) ∧
         validPrefix k p) := by
      have hcap : ∀ d : ℕ, d ≠ 1 ↔ (cap2 d).1 ≠ 1 := by
        intro d; rw [cap2_val]; omega
      constructor
      · intro hall
        refine ⟨⟨(hcap _).mp (hall 0 ⟨k, by omega⟩),
                 (hcap _).mp (hall 1 ⟨k, by omega⟩),
                 (hcap _).mp (hall 2 ⟨k, by omega⟩)⟩,
                fun i j _ => hall i j⟩
      · rintro ⟨⟨h0, h1, h2⟩, hprev⟩ i j
        by_cases hlt : j.1 < k
        · exact hprev i j hlt
        · have hjlt := j.isLt
          have hjk : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by dsimp; omega)
          rw [hjk]
          fin_cases i
          · exact (hcap _).mpr h0
          · exact (hcap _).mpr h1
          · exact (hcap _).mpr h2
    simp only [hiff, and_true]
  · intro s _ hne; simp [Ne.symm hne]
  · intro hnot; exfalso; exact hnot (Finset.mem_univ _)

/-! ### Part 2: Explicit 27-entry vectors `v0..v5` and degree-4 annihilation -/

private def idx27 (s : Fin 3 × Fin 3 × Fin 3) : ℕ :=
  9 * s.1.1 + 3 * s.2.1.1 + s.2.2.1

private def tab0 (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  match idx27 s with
  | 0 | 4 | 12 | 16 => 1
  | _ => 0

private def tab1 (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  match idx27 s with
  | 0 | 8 | 10 | 13 | 14 | 22 | 24 => 1
  | 4 | 12 | 17 | 25 | 26 => 2
  | 16 => 3
  | _ => 0

private def tab2 (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  match idx27 s with
  | 0 | 1 | 5 | 9 | 21 => 5
  | 3 | 7 | 15 => 4
  | 4 | 12 => 13
  | 8 | 24 => 8
  | 10 | 14 | 22 => 10
  | 13 | 26 => 22
  | 16 | 17 | 25 => 25
  | _ => 0

private def tab3 (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  match idx27 s with
  | 0 => 43
  | 1 | 5 | 9 | 21 => 64
  | 3 | 7 | 15 => 52
  | 4 | 12 => 130
  | 8 | 24 => 87
  | 10 | 14 | 22 => 107
  | 13 => 267
  | 16 => 269
  | 17 | 25 => 290
  | 26 => 246
  | _ => 0

private def tab4 (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  match idx27 s with
  | 0 => 463
  | 1 | 5 | 9 | 21 => 739
  | 3 | 7 | 15 => 600
  | 4 | 12 => 1439
  | 8 | 24 => 976
  | 10 | 14 | 22 => 1202
  | 13 => 3054
  | 16 => 3015
  | 17 | 25 => 3291
  | 26 => 2778
  | _ => 0

private def tab5 (s : Fin 3 × Fin 3 × Fin 3) : ℤ :=
  match idx27 s with
  | 0 => 5193
  | 1 | 5 | 9 | 21 => 8384
  | 3 | 7 | 15 => 6808
  | 4 | 12 => 16218
  | 8 | 24 => 11025
  | 10 | 14 | 22 => 13577
  | 13 => 34601
  | 16 => 34051
  | 17 | 25 => 37242
  | 26 => 31410
  | _ => 0

private lemma vVec_0_eq : vVec 0 = tab0 := by funext s; revert s; decide
private lemma step_0_1 : stepVec tab0 = tab1 := by funext s; revert s; decide
private lemma step_1_2 : stepVec tab1 = tab2 := by funext s; revert s; decide
private lemma step_2_3 : stepVec tab2 = tab3 := by funext s; revert s; decide
private lemma step_3_4 : stepVec tab3 = tab4 := by funext s; revert s; decide
private lemma step_4_5 : stepVec tab4 = tab5 := by funext s; revert s; decide

private lemma vVec_1_eq : vVec 1 = tab1 := by change stepVec (vVec 0) = tab1; rw [vVec_0_eq, step_0_1]
private lemma vVec_2_eq : vVec 2 = tab2 := by change stepVec (vVec 1) = tab2; rw [vVec_1_eq, step_1_2]
private lemma vVec_3_eq : vVec 3 = tab3 := by change stepVec (vVec 2) = tab3; rw [vVec_2_eq, step_2_3]
private lemma vVec_4_eq : vVec 4 = tab4 := by change stepVec (vVec 3) = tab4; rw [vVec_3_eq, step_3_4]
private lemma vVec_5_eq : vVec 5 = tab5 := by change stepVec (vVec 4) = tab5; rw [vVec_4_eq, step_4_5]

private lemma tab5_rec :
    ∀ s : Fin 3 × Fin 3 × Fin 3,
      tab5 s = 12 * tab4 s + (-6) * tab3 s + (-20) * tab2 s + (-5) * tab1 s := by
  decide

private lemma vVec_rec (k : ℕ) :
    ∀ s : Fin 3 × Fin 3 × Fin 3,
      vVec (k + 5) s = 12 * vVec (k + 4) s + (-6) * vVec (k + 3) s +
        (-20) * vVec (k + 2) s + (-5) * vVec (k + 1) s := by
  induction k with
  | zero =>
    intro s
    rw [vVec_5_eq, vVec_4_eq, vVec_3_eq, vVec_2_eq, vVec_1_eq]
    exact tab5_rec s
  | succ k ih =>
    intro s
    have hfn : vVec (k + 5) = fun x =>
        12 * vVec (k + 4) x + (-6) * vVec (k + 3) x +
        (-20) * vVec (k + 2) x + (-5) * vVec (k + 1) x := funext ih
    change stepVec (vVec (k + 5)) s =
      12 * stepVec (vVec (k + 4)) s + (-6) * stepVec (vVec (k + 3)) s +
      (-20) * stepVec (vVec (k + 2)) s + (-5) * stepVec (vVec (k + 1)) s
    rw [hfn, stepVec_linear]

private lemma dotEnd_linear (c₁ c₂ c₃ c₄ : ℤ)
    (w₁ w₂ w₃ w₄ : Fin 3 × Fin 3 × Fin 3 → ℤ) :
    dotEnd (fun x => c₁ * w₁ x + c₂ * w₂ x + c₃ * w₃ x + c₄ * w₄ x) =
      c₁ * dotEnd w₁ + c₂ * dotEnd w₂ + c₃ * dotEnd w₃ + c₄ * dotEnd w₄ := by
  unfold dotEnd
  have hite : ∀ (P : Prop) [Decidable P] (a b c d : ℤ),
      (if P then c₁ * a + c₂ * b + c₃ * c + c₄ * d else 0) =
        c₁ * (if P then a else 0) + c₂ * (if P then b else 0) +
        c₃ * (if P then c else 0) + c₄ * (if P then d else 0) := by
    intro P _ a b c d; split_ifs <;> ring
  simp only [hite, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma A301976_vals :
    A301976 1 = 1 ∧ A301976 2 = 5 ∧ A301976 3 = 43 ∧ A301976 4 = 463 ∧
    A301976 5 = 5193 ∧ A301976 6 = 58653 := by
  have h1 : (A301976 1 : ℤ) = 1 := by rw [A301976_eq_dotEnd 0, vVec_0_eq]; decide
  have h2 : (A301976 2 : ℤ) = 5 := by rw [A301976_eq_dotEnd 1, vVec_1_eq]; decide
  have h3 : (A301976 3 : ℤ) = 43 := by rw [A301976_eq_dotEnd 2, vVec_2_eq]; decide
  have h4 : (A301976 4 : ℤ) = 463 := by rw [A301976_eq_dotEnd 3, vVec_3_eq]; decide
  have h5 : (A301976 5 : ℤ) = 5193 := by rw [A301976_eq_dotEnd 4, vVec_4_eq]; decide
  have h6 : (A301976 6 : ℤ) = 58653 := by rw [A301976_eq_dotEnd 5, vVec_5_eq]; decide
  omega

private lemma A301976_rec_shift (k : ℕ) :
    (A301976 (k + 6) : ℤ) =
      12 * A301976 (k + 5) - 6 * A301976 (k + 4) - 20 * A301976 (k + 3) - 5 * A301976 (k + 2) := by
  rw [A301976_eq_dotEnd (k + 5), A301976_eq_dotEnd (k + 4), A301976_eq_dotEnd (k + 3),
    A301976_eq_dotEnd (k + 2), A301976_eq_dotEnd (k + 1)]
  have hfn : vVec (k + 5) = fun x =>
      12 * vVec (k + 4) x + (-6) * vVec (k + 3) x +
      (-20) * vVec (k + 2) x + (-5) * vVec (k + 1) x := funext (vVec_rec k)
  rw [hfn, dotEnd_linear]; ring

private lemma A301976_rec (n : ℕ) (hn : 4 < n) :
    (A301976 n : ℤ) = 12 * A301976 (n - 1) - 6 * A301976 (n - 2) -
      20 * A301976 (n - 3) - 5 * A301976 (n - 4) := by
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := A301976_vals
  by_cases hn5 : n = 5
  · subst hn5; norm_num [h1, h2, h3, h4, h5]
  · have hge6 : 6 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    simpa [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega] using A301976_rec_shift k

private lemma A301976_mod10 (n : ℕ) (hn : 2 < n) : A301976 n % 10 = 3 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    obtain ⟨_, _, h3, h4, h5, h6⟩ := A301976_vals
    by_cases hlt : n ≤ 6
    · interval_cases n <;> omega
    · have hrec := A301976_rec n (by omega)
      have hm1 := ih (n - 1) (by omega) (by omega)
      have hm2 := ih (n - 2) (by omega) (by omega)
      have hm3 := ih (n - 3) (by omega) (by omega)
      have hm4 := ih (n - 4) (by omega) (by omega)
      omega

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

private lemma A301976_gf :
    (1 - 12 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 +
        5 * PowerSeries.X ^ 4) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A301976 n : ℤ)) =
      PowerSeries.X * (1 + PowerSeries.X) * (1 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A301976 n : ℤ))
  have hrhs : (PowerSeries.X : PowerSeries ℤ) * (1 + PowerSeries.X) * (1 - 8 * PowerSeries.X - 3 * PowerSeries.X ^ 2) =
      PowerSeries.X - 7 * PowerSeries.X ^ 2 - 11 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4 := by
    ring
  rw [hrhs]
  ext n
  have hlhs :
      (1 - 12 * PowerSeries.X + 6 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3 +
        5 * PowerSeries.X ^ 4) * F =
      F - PowerSeries.C 12 * (PowerSeries.X ^ 1 * F) + PowerSeries.C 6 * (PowerSeries.X ^ 2 * F) +
      PowerSeries.C 20 * (PowerSeries.X ^ 3 * F) + PowerSeries.C 5 * (PowerSeries.X ^ 4 * F) := by
    have h12 : (12 : PowerSeries ℤ) = PowerSeries.C 12 := rfl
    have h6 : (6 : PowerSeries ℤ) = PowerSeries.C 6 := rfl
    have h20 : (20 : PowerSeries ℤ) = PowerSeries.C 20 := rfl
    have h5 : (5 : PowerSeries ℤ) = PowerSeries.C 5 := rfl
    rw [h12, h6, h20, h5, pow_one]; ring
  rw [hlhs]
  have hrhs_c :
      PowerSeries.coeff n ((PowerSeries.X : PowerSeries ℤ) - 7 * PowerSeries.X ^ 2 -
        11 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4) =
      (if n = 1 then 1 else 0) - 7 * (if n = 2 then 1 else 0) -
        11 * (if n = 3 then 1 else 0) - 3 * (if n = 4 then 1 else 0) := by
    have h7 : (7 : PowerSeries ℤ) = PowerSeries.C 7 := rfl
    have h11 : (11 : PowerSeries ℤ) = PowerSeries.C 11 := rfl
    have h3 : (3 : PowerSeries ℤ) = PowerSeries.C 3 := rfl
    rw [h7, h11, h3]
    simp only [map_sub, PowerSeries.coeff_X, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rw [hrhs_c]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq]
  obtain ⟨h1, h2, h3, h4, _, _⟩ := A301976_vals
  by_cases hn4 : n ≤ 4
  · interval_cases n <;> simp [F, h1, h2, h3, h4]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero]
    have hrec := A301976_rec n (by omega)
    linarith

end OMA.P_oeis_a301976

theorem OMA.solution : type_of% @OMA.S_oeis_a301976.main :=
  ⟨OMA.P_oeis_a301976.A301976_mod10, OMA.P_oeis_a301976.A301976_rec, OMA.P_oeis_a301976.A301976_gf⟩
