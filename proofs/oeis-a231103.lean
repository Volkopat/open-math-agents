import OMAStatements.S_oeis_a231103

open OMA.S_oeis_a231103 PowerSeries

private abbrev Row := Fin 3 → Fin 4

private def hz (Q : Fin 4 → Prop) (r : Row) (j : Fin 3) : Prop :=
  ∃ j' : Fin 3, (j'.val + 1 = j.val ∨ j'.val = j.val + 1) ∧ Q (r j')

private instance (Q : Fin 4 → Prop) [DecidablePred Q] (r : Row) (j : Fin 3) :
    Decidable (hz Q r j) := by
  unfold hz; infer_instance

private def upP (Q : Fin 4 → Prop) : Option Row → Fin 3 → Prop
  | none, _ => False
  | some q, j => ∃ j' : Fin 3, j'.val = j.val + 1 ∧ Q (q j')

private def dnP (Q : Fin 4 → Prop) : Option Row → Fin 3 → Prop
  | none, _ => False
  | some q, j => ∃ j' : Fin 3, j'.val + 1 = j.val ∧ Q (q j')

private instance (Q : Fin 4 → Prop) [DecidablePred Q] (p : Option Row) (j : Fin 3) :
    Decidable (upP Q p j) := by
  cases p <;> unfold upP <;> infer_instance

private instance (Q : Fin 4 → Prop) [DecidablePred Q] (p : Option Row) (j : Fin 3) :
    Decidable (dnP Q p j) := by
  cases p <;> unfold dnP <;> infer_instance

private def tg (x : Fin 4) : Fin 4 → Prop := fun v => v.val = (x.val + 1) % 4

private def eqv (x : Fin 4) : Fin 4 → Prop := fun v => v = x

private instance (x : Fin 4) : DecidablePred (tg x) := fun v => by unfold tg; infer_instance

private instance (x : Fin 4) : DecidablePred (eqv x) := fun v => by unfold eqv; infer_instance

private def nb (Q : Fin 4 → Prop) (p : Option Row) (r : Row) (q : Option Row) (j : Fin 3) : Prop :=
  hz Q r j ∨ upP Q p j ∨ dnP Q q j

private instance (Q : Fin 4 → Prop) [DecidablePred Q] (p : Option Row) (r : Row)
    (q : Option Row) (j : Fin 3) : Decidable (nb Q p r q j) := by
  unfold nb; infer_instance

private def good (p : Option Row) (r : Row) (q : Option Row) : Prop :=
  ∀ j, nb (tg (r j)) p r q j ∧ ¬ nb (eqv (r j)) p r q j

private instance (p : Option Row) (r : Row) (q : Option Row) : Decidable (good p r q) := by
  unfold good; infer_instance

private def rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) : Option Row :=
  if h : k < n then some (y ⟨k, h⟩) else none

private def Good (n : ℕ) (p : Option Row) (y : Fin n → Row) : Prop :=
  ∀ i : Fin n, good (if i.val = 0 then p else rowAt y (i.val - 1)) (y i) (rowAt y (i.val + 1))

private instance (n : ℕ) (p : Option Row) : DecidablePred (Good n p) := fun y => by
  unfold Good; infer_instance

private theorem upP_rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) (Q : Fin 4 → Prop) (j : Fin 3) :
    upP Q (rowAt y k) j ↔ ∃ i' : Fin n, i'.val = k ∧
      ∃ j' : Fin 3, j'.val = j.val + 1 ∧ Q (y i' j') := by
  unfold rowAt
  split_ifs with h
  · simp only [upP]
    constructor
    · intro hh; exact ⟨⟨k, h⟩, rfl, hh⟩
    · rintro ⟨i', rfl, hh⟩; exact hh
  · simp only [upP, false_iff, not_exists, not_and]
    intro i' hi; have := i'.isLt; omega

private theorem dnP_rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) (Q : Fin 4 → Prop) (j : Fin 3) :
    dnP Q (rowAt y k) j ↔ ∃ i' : Fin n, i'.val = k ∧
      ∃ j' : Fin 3, j'.val + 1 = j.val ∧ Q (y i' j') := by
  unfold rowAt
  split_ifs with h
  · simp only [dnP]
    constructor
    · intro hh; exact ⟨⟨k, h⟩, rfl, hh⟩
    · rintro ⟨i', rfl, hh⟩; exact hh
  · simp only [dnP, false_iff, not_exists, not_and]
    intro i' hi; have := i'.isLt; omega

private theorem nb_iff {n : ℕ} (A : Fin n → Row) (i : Fin n) (j : Fin 3) (Q : Fin 4 → Prop) :
    (∃ (i' : Fin n) (j' : Fin 3), nextTo i.val j.val i'.val j'.val ∧ Q (A i' j')) ↔
      nb Q (if i.val = 0 then none else rowAt A (i.val - 1)) (A i) (rowAt A (i.val + 1)) j := by
  have hup : upP Q (if i.val = 0 then none else rowAt A (i.val - 1)) j ↔
      ∃ i' : Fin n, i'.val + 1 = i.val ∧ ∃ j' : Fin 3, j'.val = j.val + 1 ∧ Q (A i' j') := by
    split_ifs with h
    · simp only [upP, false_iff, not_exists, not_and]
      intro i' hi; omega
    · rw [upP_rowAt]
      constructor
      · rintro ⟨i', h1, h2⟩; exact ⟨i', by omega, h2⟩
      · rintro ⟨i', h1, h2⟩; exact ⟨i', by omega, h2⟩
  unfold nb
  rw [hup, dnP_rowAt]
  unfold hz nextTo
  constructor
  · rintro ⟨i', j', (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩), hP⟩
    · left; have : i' = i := Fin.ext h1
      subst this; exact ⟨j', h2, hP⟩
    · right; left; exact ⟨i', h1, j', h2, hP⟩
    · right; right; exact ⟨i', h1, j', h2, hP⟩
  · rintro (⟨j', h2, hP⟩ | ⟨i', h1, j', h2, hP⟩ | ⟨i', h1, j', h2, hP⟩)
    · exact ⟨i, j', Or.inl ⟨rfl, h2⟩, hP⟩
    · exact ⟨i', j', Or.inr (Or.inl ⟨h1, h2⟩), hP⟩
    · exact ⟨i', j', Or.inr (Or.inr ⟨h1, h2⟩), hP⟩

private theorem valid_iff (n : ℕ) (A : Fin n → Row) :
    valid n A ↔ Good n none A ∧ ∀ i : Fin n, i.val = 0 → A i 0 = 0 := by
  have hX : (∀ (i : Fin n) (j : Fin 3), ∃ (i' : Fin n) (j' : Fin 3),
      nextTo i.val j.val i'.val j'.val ∧ (A i' j').val = ((A i j).val + 1) % 4) ↔
      ∀ (i : Fin n) (j : Fin 3), nb (tg (A i j))
        (if i.val = 0 then none else rowAt A (i.val - 1)) (A i) (rowAt A (i.val + 1)) j :=
    forall_congr' fun i => forall_congr' fun j => nb_iff A i j (tg (A i j))
  have hY : (∀ (i : Fin n) (j : Fin 3) (i' : Fin n) (j' : Fin 3),
      nextTo i.val j.val i'.val j'.val → A i' j' ≠ A i j) ↔
      ∀ (i : Fin n) (j : Fin 3), ¬ nb (eqv (A i j))
        (if i.val = 0 then none else rowAt A (i.val - 1)) (A i) (rowAt A (i.val + 1)) j := by
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [← nb_iff A i j (eqv (A i j))]
    simp only [eqv, ne_eq, not_exists, not_and]
  unfold valid Good good
  rw [hX, hY]
  simp only [forall_and, and_assoc]

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

private theorem corner_cons {n : ℕ} (r : Row) (y : Fin n → Row) :
    (∀ i : Fin (n + 1), i.val = 0 → (Fin.cons r y : Fin (n + 1) → Row) i 0 = 0) ↔ r 0 = 0 := by
  rw [Fin.forall_fin_succ]
  simp

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

private theorem a_succ_eq (n : ℕ) : a (n + 1) = ∑ r, if r 0 = 0 then G n none r else 0 := by
  rw [a, Finset.filter_congr (fun A _ => valid_iff (n + 1) A), card_cons]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Good_cons, corner_cons]
  by_cases h : r 0 = 0 <;> simp [h, G]

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

private def sat (p : Option Row) (r : Row) (j : Fin 3) : Prop :=
  hz (tg (r j)) r j ∨ upP (tg (r j)) p j

private def bad (p : Option Row) (r : Row) (j : Fin 3) : Prop :=
  hz (eqv (r j)) r j ∨ upP (eqv (r j)) p j

private def okp (p : Option Row) (r : Row) : Prop := ∀ j, ¬ bad p r j

private instance (p : Option Row) (r : Row) (j : Fin 3) : Decidable (sat p r j) := by
  unfold sat; infer_instance

private instance (p : Option Row) (r : Row) : Decidable (okp p r) := by
  unfold okp bad; infer_instance

private def clsM (b1 b2 : Bool) (r : Row) : Fin 6 :=
  if b1 ∧ b2 then 5 else if b2 then 0 else if b1 then (if r 2 = r 1 + 1 then 1 else 2) else 3

private def cls (p : Option Row) (r : Row) : Fin 6 :=
  if okp p r ∧ sat p r 0 then clsM (decide (sat p r 1)) (decide (sat p r 2)) r else 4

private def T : Fin 6 → Fin 6 → ℕ :=
  ![![0, 1, 1, 0, 9, 1], ![1, 2, 1, 1, 6, 1], ![1, 1, 0, 1, 9, 0], ![0, 0, 0, 0, 4, 0],
    ![0, 0, 0, 0, 0, 0], ![2, 4, 2, 2, 24, 2]]

private abbrev e : Fin (4 ^ 3) → Row := finFunctionFinEquiv.symm

private theorem hTM : ∀ (b1 b2 : Bool) (r : Fin (4 ^ 3)) (j : Fin 6),
    (∀ k, ¬ hz (eqv (e r k)) (e r) k) →
    (hz (tg (e r 1)) (e r) 1 → b1 = true) → (b2 = true ↔ hz (tg (e r 2)) (e r) 2) →
    (Finset.univ.filter fun c : Fin (4 ^ 3) =>
      (b1 = true ∨ dnP (tg (e r 1)) (some (e c)) 1) ∧
      (b2 = true ∨ dnP (tg (e r 2)) (some (e c)) 2) ∧
      (∀ k, ¬ dnP (eqv (e r k)) (some (e c)) k) ∧ cls (some (e r)) (e c) = j).card =
      T (clsM b1 b2 (e r)) j := by
  decide +kernel

private theorem hKM : ∀ j, (Finset.univ.filter fun r : Fin (4 ^ 3) =>
    e r 0 = 0 ∧ cls none (e r) = j).card = ![1, 1, 0, 1, 13, 0] j := by
  decide +kernel

private theorem forall3 (P : Fin 3 → Prop) : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ j => by fin_cases j <;> assumption⟩

private theorem good_some (p : Option Row) (r c : Row) :
    good p r (some c) ↔ okp p r ∧ (∀ j, sat p r j ∨ dnP (tg (r j)) (some c) j) ∧
      ∀ j, ¬ dnP (eqv (r j)) (some c) j := by
  simp only [good, nb, okp, bad, sat, ← forall_and]
  refine forall_congr' fun j => ?_
  tauto

private theorem good_none (p : Option Row) (r : Row) :
    good p r none ↔ okp p r ∧ ∀ j, sat p r j := by
  simp only [good, nb, okp, bad, sat, dnP, or_false, ← forall_and]
  refine forall_congr' fun j => ?_
  tauto

private theorem dn_zero (Q : Fin 4 → Prop) (c : Row) : ¬ dnP Q (some c) 0 := by
  simp [dnP]

private theorem sat_two (p : Option Row) (r : Row) : sat p r 2 ↔ hz (tg (r 2)) r 2 := by
  unfold sat
  cases p with
  | none => simp [upP]
  | some q =>
    simp only [upP, or_iff_left_iff_imp]
    rintro ⟨j', hj, -⟩
    have := j'.isLt
    simp at hj
    omega

private theorem hT (p : Option Row) (r : Row) (j : Fin 6) :
    (Finset.univ.filter fun c => good p r (some c) ∧ cls (some r) c = j).card = T (cls p r) j := by
  by_cases h0 : okp p r ∧ sat p r 0
  · have := hTM (decide (sat p r 1)) (decide (sat p r 2)) (finFunctionFinEquiv r) j
      (by simp only [e, Equiv.symm_apply_apply]; exact fun k hk => h0.1 k (Or.inl hk))
      (by simp only [e, Equiv.symm_apply_apply, decide_eq_true_eq]; intro h; exact Or.inl h)
      (by simp only [e, Equiv.symm_apply_apply, decide_eq_true_eq]; exact sat_two p r)
    simp only [e, Equiv.symm_apply_apply] at this
    rw [cls, if_pos h0, ← this]
    apply Finset.card_equiv finFunctionFinEquiv
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
      decide_eq_true_eq, good_some, forall3 (fun j => sat p r j ∨ _), h0.1, h0.2, true_or,
      and_assoc]
  · have hn : ∀ c, ¬ good p r (some c) := fun c h =>
      h0 ⟨((good_some p r c).1 h).1, (((good_some p r c).1 h).2.1 0).resolve_right (dn_zero _ c)⟩
    rw [cls, if_neg h0]
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun c _ h => hn c h.1))]
    fin_cases j <;> rfl

private theorem lump {β : Type} [Fintype β] (cl : β → Fin 6) (P : β → Prop) [DecidablePred P]
    (g : Fin 6 → ℕ) :
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

private def wf : ℕ → Fin 6 → ℕ
  | 0 => ![0, 0, 0, 0, 0, 1]
  | m + 1 => fun k => ∑ i, T k i * wf m i

private theorem G_zero' (p : Option Row) (r : Row) : G 0 p r = wf 0 (cls p r) := by
  rw [G_zero]
  simp only [good_none, forall3]
  unfold cls clsM
  by_cases hok : okp p r <;> by_cases h0 : sat p r 0 <;> by_cases h1 : sat p r 1 <;>
    by_cases h2 : sat p r 2 <;> simp [hok, h0, h1, h2, wf] <;> (split_ifs <;> rfl)

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

private theorem wf_dead (m : ℕ) : wf m 4 = 0 := by
  cases m with
  | zero => rfl
  | succ m => simp [wf, T, Fin.sum_univ_succ]

private def K : Fin 6 → ℕ := ![1, 1, 0, 1, 13, 0]

private theorem a_succ (n : ℕ) : a (n + 1) = ∑ j, K j * wf n j := by
  rw [a_succ_eq]
  simp only [G_eq]
  rw [lump (cls none) (fun r => r 0 = 0) (wf n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [show K j = ![1, 1, 0, 1, 13, 0] j from rfl, ← hKM j]
  apply Finset.card_equiv finFunctionFinEquiv
  intro c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.symm_apply_apply]

private theorem a1 : a 1 = 0 := (a_succ 0).trans (by simp [K, wf, Fin.sum_univ_succ])
private theorem a2 : a 2 = 2 := (a_succ 1).trans (by simp [K, wf, T, Fin.sum_univ_succ])

private theorem a_rec (m : ℕ) : a (m + 3) = 4 * a (m + 2) + 5 * a (m + 1) := by
  have h1 : a (m + 3) = ∑ j, K j * wf (m + 2) j := a_succ (m + 2)
  have h2 : a (m + 2) = ∑ j, K j * wf (m + 1) j := a_succ (m + 1)
  have h3 : a (m + 1) = ∑ j, K j * wf m j := a_succ m
  rw [h1, h2, h3]
  simp only [wf, Fin.sum_univ_succ, Fin.sum_univ_zero, K, T]
  simp [wf_dead]
  ring

private theorem gf :
    ((1 + X) * (1 - 5 * X)) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X ^ 2 : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : ((1 + X) * (1 - 5 * X)) * s =
      s - (s * C (4 : ℤ)) * X ^ 1 - (s * C (5 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (2 * X ^ 2 : PowerSeries ℤ) = C (2 : ℤ) * X ^ 2 := by
    simp only [map_ofNat]
  rw [hd, hn]
  ext n
  simp only [map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := a_rec m
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    simp
    omega

private def b (n : ℕ) : ℚ := (5 ^ n + 5 * (-1) ^ n) / 15

private theorem closed (m : ℕ) : (a (m + 1) : ℚ) = b (m + 1) ∧ (a (m + 2) : ℚ) = b (m + 2) := by
  induction m with
  | zero =>
    simp only [zero_add]
    refine ⟨?_, ?_⟩
    · rw [a1, b]; norm_num
    · rw [a2, b]; norm_num
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 3) : ℚ) = 4 * a (m + 2) + 5 * a (m + 1) := by exact_mod_cast a_rec m
    rw [show m + 1 + 2 = m + 3 from rfl, hr, h1, h2, b, b, b]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a231103.main := by
  refine ⟨gf, fun n hn he => ?_, fun n hn ho => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [(closed m).1, b, he.neg_one_pow]
    ring
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [(closed m).1, b, ho.neg_one_pow]
    ring

