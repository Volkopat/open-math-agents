import OMAStatements.S_oeis_a265987

open OMA.S_oeis_a265987 PowerSeries

private abbrev Row := Fin 3 → Fin 5

private def rowD (r : Row) (k : ℤ) (x : Fin 5) : ℕ :=
  if h : 0 ≤ k ∧ k < 3 then (if r ⟨k.toNat, by omega⟩ = x then 0 else 1) else 0

private def optD : Option Row → ℤ → Fin 5 → ℕ
  | none, _, _ => 0
  | some r, k, x => rowD r k x

private theorem optD_some (r : Row) (k : ℤ) (x : Fin 5) : optD (some r) k x = rowD r k x := rfl

private def good (p : Option Row) (r : Row) (q : Option Row) : Prop :=
  ∀ j : Fin 3, (r j).val = rowD r ((j.val : ℤ) - 1) (r j) + rowD r ((j.val : ℤ) + 1) (r j) +
    optD p ((j.val : ℤ) + 1) (r j) + optD q ((j.val : ℤ) - 1) (r j)

private instance (p : Option Row) (r : Row) (q : Option Row) : Decidable (good p r q) := by
  unfold good; infer_instance

private def rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) : Option Row :=
  if h : k < n then some (y ⟨k, h⟩) else none

private def Good (n : ℕ) (p : Option Row) (y : Fin n → Row) : Prop :=
  ∀ i : Fin n, good (if i.val = 0 then p else rowAt y (i.val - 1)) (y i) (rowAt y (i.val + 1))

private instance (n : ℕ) (p : Option Row) : DecidablePred (Good n p) := fun y => by
  unfold Good; infer_instance

private def castA {n : ℕ} (B : Fin n → Row) : Fin n → Fin 3 → ℤ := fun i j => ((B i j).val : ℤ)

private theorem castA_apply {n : ℕ} (B : Fin n → Row) (i : Fin n) (j : Fin 3) :
    castA B i j = ((B i j).val : ℤ) := rfl

private def rowAtZ {n : ℕ} (B : Fin n → Row) (t : ℤ) : Option Row :=
  if h : 0 ≤ t ∧ t < n then some (B ⟨t.toNat, by omega⟩) else none

private theorem differs_cast {n : ℕ} (B : Fin n → Row) (t k : ℤ) (x : Fin 5) :
    differs (castA B) t k (x.val : ℤ) = optD (rowAtZ B t) k x := by
  unfold differs OMA.S_oeis_a265987.get rowAtZ
  by_cases ht : 0 ≤ t ∧ t < n
  · rw [dif_pos ht, optD_some]
    unfold rowD
    by_cases hk : 0 ≤ k ∧ k < 3
    · rw [dif_pos ⟨ht.1, ht.2, hk.1, hk.2⟩, dif_pos hk]
      simp only [castA, Nat.cast_inj, Fin.val_inj]
    · rw [dif_neg (fun h => hk ⟨h.2.2.1, h.2.2.2⟩), dif_neg hk]
  · rw [dif_neg (fun h => ht ⟨h.1, h.2.1⟩), dif_neg ht]
    rfl

private theorem rowAtZ_self {n : ℕ} (B : Fin n → Row) (i : Fin n) :
    rowAtZ B (i.val : ℤ) = some (B i) := by
  unfold rowAtZ
  rw [dif_pos ⟨by omega, by omega⟩]
  congr

private theorem rowAtZ_pred {n : ℕ} (B : Fin n → Row) (i : Fin n) :
    rowAtZ B ((i.val : ℤ) - 1) = if i.val = 0 then none else rowAt B (i.val - 1) := by
  unfold rowAtZ rowAt
  by_cases h : i.val = 0
  · rw [dif_neg (by omega), if_pos h]
  · rw [dif_pos ⟨by omega, by omega⟩, if_neg h, dif_pos (by omega)]
    congr 2
    apply Fin.ext
    simp only
    omega

private theorem rowAtZ_succ {n : ℕ} (B : Fin n → Row) (i : Fin n) :
    rowAtZ B ((i.val : ℤ) + 1) = rowAt B (i.val + 1) := by
  unfold rowAtZ rowAt
  by_cases h : i.val + 1 < n
  · rw [dif_pos ⟨by omega, by omega⟩, dif_pos h]
    congr 2
  · rw [dif_neg (by omega), dif_neg h]

private theorem valid_iff (n : ℕ) (B : Fin n → Row) : valid n (castA B) ↔ Good n none B := by
  unfold valid Good good diffCount
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [castA_apply, differs_cast, differs_cast, differs_cast, differs_cast, rowAtZ_self,
    rowAtZ_pred, rowAtZ_succ, optD_some, optD_some, Nat.cast_inj]

private theorem differs_le {n : ℕ} (A : Fin n → Fin 3 → ℤ) (i j x : ℤ) : differs A i j x ≤ 1 := by
  unfold differs
  split
  · split_ifs <;> simp
  · simp

private theorem bound {n : ℕ} (A : Fin n → Fin 3 → ℤ) (h : valid n A) (i : Fin n) (j : Fin 3) :
    0 ≤ A i j ∧ A i j < 5 := by
  rw [h i j]
  unfold diffCount
  have := differs_le A i (j - 1) (A i j)
  have := differs_le A i (j + 1) (A i j)
  have := differs_le A (i - 1) (j + 1) (A i j)
  have := differs_le A (i + 1) (j - 1) (A i j)
  omega

private def toB {n : ℕ} (A : {A : Fin n → Fin 3 → ℤ // valid n A}) : Fin n → Row :=
  fun i j => ⟨(A.1 i j).toNat, by have := bound A.1 A.2 i j; omega⟩

private theorem castA_toB {n : ℕ} (A : {A : Fin n → Fin 3 → ℤ // valid n A}) :
    castA (toB A) = A.1 := by
  funext i j
  have := bound A.1 A.2 i j
  simp only [castA, toB]
  omega

private def eqvA (n : ℕ) :
    {A : Fin n → Fin 3 → ℤ // valid n A} ≃ {B : Fin n → Row // valid n (castA B)} where
  toFun A := ⟨toB A, by rw [castA_toB]; exact A.2⟩
  invFun B := ⟨castA B.1, B.2⟩
  left_inv A := Subtype.ext (castA_toB A)
  right_inv B := Subtype.ext (by funext i j; apply Fin.ext; simp [toB, castA])

private theorem a_eq (n : ℕ) : a n = (Finset.univ.filter (Good n none)).card := by
  classical
  rw [a, Nat.card_congr (eqvA n), Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact valid_iff n B

private theorem rowAt_cons_zero {n : ℕ} (r : Row) (y : Fin n → Row) :
    rowAt (Fin.cons r y : Fin (n + 1) → Row) 0 = some r := by
  simp [rowAt]

private theorem rowAt_cons_succ {n : ℕ} (r : Row) (y : Fin n → Row) (k : ℕ) :
    rowAt (Fin.cons r y : Fin (n + 1) → Row) (k + 1) = rowAt y k := by
  unfold rowAt
  by_cases h : k < n
  · rw [dif_pos (by omega), dif_pos h]
    exact congrArg some (Fin.cons_succ (α := fun _ => Row) r y ⟨k, h⟩)
  · rw [dif_neg (by omega), dif_neg h]

private theorem Good_cons {n : ℕ} (p : Option Row) (r : Row) (y : Fin n → Row) :
    Good (n + 1) p (Fin.cons r y) ↔ good p r (rowAt y 0) ∧ Good n (some r) y := by
  unfold Good
  rw [Fin.forall_fin_succ]
  apply and_congr
  · simp only [Fin.val_zero, if_true, Fin.cons_zero, zero_add, rowAt_cons_succ]
  · refine forall_congr' fun i => ?_
    have key : rowAt (Fin.cons r y : Fin (n + 1) → Row) i.val =
        if i.val = 0 then some r else rowAt y (i.val - 1) := by
      rcases i with ⟨_ | k, hk⟩
      · simp [rowAt_cons_zero]
      · simp [rowAt_cons_succ]
    simp only [Fin.val_succ, Fin.cons_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      if_false, Nat.add_sub_cancel, rowAt_cons_succ, key]

private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ c : α, (Finset.univ.filter fun y : Fin n → α => P (Fin.cons c y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  simp only [Finset.card_filter]
  congr! 3

private def G (n : ℕ) (p : Option Row) (r : Row) : ℕ :=
  (Finset.univ.filter fun y : Fin n → Row => good p r (rowAt y 0) ∧ Good n (some r) y).card

private theorem a_succ_eq (n : ℕ) : a (n + 1) = ∑ r, G n none r := by
  rw [a_eq, card_cons]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Good_cons, G]

private theorem G_zero (p : Option Row) (r : Row) : G 0 p r = if good p r none then 1 else 0 := by
  have he : ∀ y : Fin 0 → Row, rowAt y 0 = none := fun y => by simp [rowAt]
  have hg : ∀ y : Fin 0 → Row, Good 0 (some r) y := fun y i => i.elim0
  simp only [G, he, hg, and_true]
  by_cases h : good p r none <;> simp [h]

private theorem G_succ (n : ℕ) (p : Option Row) (r : Row) :
    G (n + 1) p r = ∑ c, if good p r (some c) then G n (some r) c else 0 := by
  rw [G, card_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [rowAt_cons_zero, Good_cons]
  by_cases h : good p r (some c) <;> simp [h, G]

private theorem optD_le (p : Option Row) (k : ℤ) (x : Fin 5) : optD p k x ≤ 1 := by
  cases p with
  | none => simp [optD]
  | some r =>
    simp only [optD, rowD]
    split_ifs <;> simp

private theorem optD_three (p : Option Row) (x : Fin 5) : optD p 3 x = 0 := by
  cases p <;> simp [optD, rowD]

private def gU (u0 u1 : ℕ) (r : Row) (q : Option Row) : Prop :=
  (r 0).val = rowD r (-1) (r 0) + rowD r 1 (r 0) + u0 + optD q (-1) (r 0) ∧
  (r 1).val = rowD r 0 (r 1) + rowD r 2 (r 1) + u1 + optD q 0 (r 1) ∧
  (r 2).val = rowD r 1 (r 2) + rowD r 3 (r 2) + 0 + optD q 1 (r 2)

private instance (u0 u1 : ℕ) (r : Row) (q : Option Row) : Decidable (gU u0 u1 r q) := by
  unfold gU; infer_instance

private theorem forall3 (P : Fin 3 → Prop) : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ j => by fin_cases j <;> assumption⟩

private theorem good_iff (p : Option Row) (r : Row) (q : Option Row) :
    good p r q ↔ gU (optD p 1 (r 0)) (optD p 2 (r 1)) r q := by
  unfold good gU
  rw [forall3]
  norm_num [optD_three]

private def clsU (u0 u1 : ℕ) (r : Row) : Fin 8 :=
  if (r 0).val = rowD r (-1) (r 0) + rowD r 1 (r 0) + u0 then
    if (r 1).val = rowD r 0 (r 1) + rowD r 2 (r 1) + u1 ∧
        (r 2).val = rowD r 1 (r 2) + rowD r 3 (r 2) then (if r = 0 then 6 else 7)
    else if (r 1).val = rowD r 0 (r 1) + rowD r 2 (r 1) + u1 ∧
        (r 2).val = rowD r 1 (r 2) + rowD r 3 (r 2) + 1 then (if r 1 = 1 then 0 else 2)
    else if (r 1).val = rowD r 0 (r 1) + rowD r 2 (r 1) + u1 + 1 ∧
        (r 2).val = rowD r 1 (r 2) + rowD r 3 (r 2) then 1
    else if (r 1).val = rowD r 0 (r 1) + rowD r 2 (r 1) + u1 + 1 ∧
        (r 2).val = rowD r 1 (r 2) + rowD r 3 (r 2) + 1 then (if r 1 = 1 then 4 else 3)
    else 5
  else 5

private def cls (p : Option Row) (r : Row) : Fin 8 := clsU (optD p 1 (r 0)) (optD p 2 (r 1)) r

private def T : Fin 8 → Fin 8 → ℕ :=
  ![![0, 1, 1, 1, 0, 16, 0, 1], ![2, 0, 0, 0, 1, 17, 0, 0], ![0, 0, 0, 0, 0, 20, 0, 0],
    ![1, 1, 1, 1, 0, 75, 0, 1], ![0, 1, 1, 1, 0, 76, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 4, 1, 0], ![0, 0, 0, 0, 0, 5, 0, 0]]

private def acc : Fin 8 → ℕ := ![0, 0, 0, 0, 0, 0, 1, 1]

private def K : Fin 8 → ℕ := ![0, 1, 0, 1, 0, 121, 1, 1]

private abbrev e : Fin (5 ^ 3) → Row := finFunctionFinEquiv.symm

private theorem hTM : ∀ (u0 u1 : Fin 2) (r : Fin (5 ^ 3)) (j : Fin 8),
    clsU u0.val u1.val (e r) ≠ 5 →
    (Finset.univ.filter fun c : Fin (5 ^ 3) =>
      gU u0.val u1.val (e r) (some (e c)) ∧ cls (some (e r)) (e c) = j).card =
      T (clsU u0.val u1.val (e r)) j := by
  decide +kernel

private theorem hAcc : ∀ (u0 u1 : Fin 2) (r : Fin (5 ^ 3)),
    (if gU u0.val u1.val (e r) none then 1 else 0) = acc (clsU u0.val u1.val (e r)) := by
  decide +kernel

private theorem hKM : ∀ j, (Finset.univ.filter fun r : Fin (5 ^ 3) => cls none (e r) = j).card =
    K j := by
  decide +kernel

private theorem dead_no (u0 u1 : ℕ) (r : Row) (q : Option Row) (h : clsU u0 u1 r = 5)
    (hg : gU u0 u1 r q) : False := by
  have h0 : optD q (-1) (r 0) = 0 := by cases q <;> simp [optD, rowD]
  have h1 := optD_le q 0 (r 1)
  have h2 := optD_le q 1 (r 2)
  unfold gU at hg
  unfold clsU at h
  split_ifs at h <;> first | exact absurd h (by decide) | omega

private theorem hT (p : Option Row) (r : Row) (j : Fin 8) :
    (Finset.univ.filter fun c => good p r (some c) ∧ cls (some r) c = j).card = T (cls p r) j := by
  have hu0 := optD_le p 1 (r 0)
  have hu1 := optD_le p 2 (r 1)
  by_cases hd : cls p r = 5
  · rw [hd, Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun c _ h =>
      dead_no _ _ r _ hd ((good_iff p r (some c)).1 h.1)))]
    fin_cases j <;> rfl
  · have := hTM ⟨optD p 1 (r 0), by omega⟩ ⟨optD p 2 (r 1), by omega⟩ (finFunctionFinEquiv r) j
      (by simp only [e, Equiv.symm_apply_apply]; exact hd)
    simp only [e, Equiv.symm_apply_apply] at this
    rw [cls, ← this]
    apply Finset.card_equiv finFunctionFinEquiv
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply, good_iff]

private theorem lump {β : Type} [Fintype β] (cl : β → Fin 8) (P : β → Prop) [DecidablePred P]
    (g : Fin 8 → ℕ) :
    ∑ c : β, (if P c then g (cl c) else 0) =
      ∑ j, (Finset.univ.filter fun c => P c ∧ cl c = j).card * g j := by
  rw [← Finset.sum_fiberwise Finset.univ cl]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun c => if P c then g j else 0)
    (fun c hc => by rw [(Finset.mem_filter.1 hc).2])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Finset.filter_filter]
  congr 2
  ext c
  simp [and_comm]

private def wf : ℕ → Fin 8 → ℕ
  | 0 => acc
  | m + 1 => fun k => ∑ i, T k i * wf m i

private theorem G_zero' (p : Option Row) (r : Row) : G 0 p r = wf 0 (cls p r) := by
  have hu0 := optD_le p 1 (r 0)
  have hu1 := optD_le p 2 (r 1)
  have := hAcc ⟨optD p 1 (r 0), by omega⟩ ⟨optD p 2 (r 1), by omega⟩ (finFunctionFinEquiv r)
  simp only [e, Equiv.symm_apply_apply] at this
  rw [G_zero, cls]
  simp only [good_iff]
  exact this

private theorem G_eq (m : ℕ) : ∀ p r, G m p r = wf m (cls p r) := by
  induction m with
  | zero => exact G_zero'
  | succ m ih =>
    intro p r
    rw [G_succ]
    simp only [ih]
    rw [lump (cls (some r)) (fun c => good p r (some c)) (wf m)]
    simp only [wf]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT]

private theorem wf_dead (m : ℕ) : wf m 5 = 0 := by
  cases m with
  | zero => rfl
  | succ m => simp [wf, T, Fin.sum_univ_succ]

private theorem a_succ (n : ℕ) : a (n + 1) = ∑ j, K j * wf n j := by
  rw [a_succ_eq]
  simp only [G_eq]
  have := lump (cls none) (fun _ => True) (wf n)
  simp only [if_true, true_and] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => congrArg (· * wf n j) ?_
  rw [← hKM j]
  apply Finset.card_equiv finFunctionFinEquiv
  intro c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.symm_apply_apply]

private theorem a1 : a 1 = 2 := (a_succ 0).trans (by decide +kernel)
private theorem a2 : a 2 = 2 := (a_succ 1).trans (by decide +kernel)
private theorem a3 : a 3 = 6 := (a_succ 2).trans (by decide +kernel)
private theorem a4 : a 4 = 10 := (a_succ 3).trans (by decide +kernel)

private theorem a_rec (m : ℕ) : a (m + 5) + 4 * a (m + 2) = 2 * a (m + 4) + 3 * a (m + 3) := by
  have h1 : a (m + 5) = ∑ j, K j * wf (m + 4) j := a_succ (m + 4)
  have h2 : a (m + 2) = ∑ j, K j * wf (m + 1) j := a_succ (m + 1)
  have h3 : a (m + 4) = ∑ j, K j * wf (m + 3) j := a_succ (m + 3)
  have h4 : a (m + 3) = ∑ j, K j * wf (m + 2) j := a_succ (m + 2)
  rw [h1, h2, h3, h4]
  simp only [wf, Fin.sum_univ_succ, Fin.sum_univ_zero, K, T]
  simp [wf_dead]
  ring

private theorem a_rec' : ∀ m, a (m + 4) + 4 * a (m + 1) = 2 * a (m + 3) + 3 * a (m + 2)
  | 0 => by simp only [zero_add, a1, a2, a3, a4]
  | m + 1 => a_rec m

private theorem gf :
    ((1 - X) * (1 - X - 4 * X ^ 2)) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X * (1 + X) * (1 - 2 * X) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : ((1 - X) * (1 - X - 4 * X ^ 2)) * s =
      s - (s * C (2 : ℤ)) * X ^ 1 - (s * C (3 : ℤ)) * X ^ 2 + (s * C (4 : ℤ)) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (2 * X * (1 + X) * (1 - 2 * X) : PowerSeries ℤ) =
      C (2 : ℤ) * X ^ 1 - C (2 : ℤ) * X ^ 2 - C (4 : ℤ) * X ^ 3 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with h | h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · subst h; simp [a1, a2, a3, a4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := a_rec m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  1 + (-((1 - Real.sqrt 17) / 2) ^ n + ((1 + Real.sqrt 17) / 2) ^ n) / Real.sqrt 17

private theorem root_step (x : ℝ) (h : x ^ 2 = x + 4) (j : ℕ) :
    x ^ (j + 3) = 2 * x ^ (j + 2) + 3 * x ^ (j + 1) - 4 * x ^ j := by
  linear_combination (x ^ j * (x - 1)) * h

private theorem R_rec (j : ℕ) : R (j + 3) = 2 * R (j + 2) + 3 * R (j + 1) - 4 * R j := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h1 := root_step ((1 - Real.sqrt 17) / 2) (by linear_combination hs / 4) j
  have h2 := root_step ((1 + Real.sqrt 17) / 2) (by linear_combination hs / 4) j
  unfold R
  rw [h1, h2]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  have hne : Real.sqrt 17 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    simp only [zero_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, R]; field_simp; ring
    · rw [a2, R]; field_simp; ring
    · rw [a3, R]; field_simp; linear_combination (-2 * Real.sqrt 17) * hs
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) + 4 * a (m + 1) = 2 * a (m + 3) + 3 * a (m + 2) := by
      exact_mod_cast a_rec' m
    have hR := R_rec (m + 1)
    rw [show m + 1 + 3 = m + 4 from rfl, show m + 1 + 2 = m + 3 from rfl,
      show m + 1 + 1 = m + 2 from rfl] at hR
    rw [show m + 1 + 3 = m + 4 from rfl, hR]
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a265987.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [(closed m).1, R]

