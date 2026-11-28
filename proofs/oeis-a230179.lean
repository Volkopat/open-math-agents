import OMAStatements.S_oeis_a230179

open OMA.S_oeis_a230179 PowerSeries

private abbrev Row := Fin 3 → Fin 3

private def horiz (r : Row) (j : Fin 3) : Prop :=
  ∃ j' : Fin 3, (j'.val + 1 = j.val ∨ j'.val = j.val + 1) ∧ (r j').val + (r j).val = 2

private instance (r : Row) (j : Fin 3) : Decidable (horiz r j) := by
  unfold horiz; infer_instance

private def upOK : Option Row → Row → Fin 3 → Prop
  | none, _, _ => False
  | some q, r, j => ∃ j' : Fin 3, j'.val = j.val + 1 ∧ (q j').val + (r j).val = 2

private def dnOK : Option Row → Row → Fin 3 → Prop
  | none, _, _ => False
  | some q, r, j => ∃ j' : Fin 3, j'.val + 1 = j.val ∧ (q j').val + (r j).val = 2

private instance (p : Option Row) (r : Row) (j : Fin 3) : Decidable (upOK p r j) := by
  cases p <;> unfold upOK <;> infer_instance

private instance (p : Option Row) (r : Row) (j : Fin 3) : Decidable (dnOK p r j) := by
  cases p <;> unfold dnOK <;> infer_instance

private def good (p : Option Row) (r : Row) (q : Option Row) : Prop :=
  ∀ j, horiz r j ∨ upOK p r j ∨ dnOK q r j

private instance (p : Option Row) (r : Row) (q : Option Row) : Decidable (good p r q) := by
  unfold good; infer_instance

private def rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) : Option Row :=
  if h : k < n then some (y ⟨k, h⟩) else none

private def Good (n : ℕ) (p : Option Row) (y : Fin n → Row) : Prop :=
  ∀ i : Fin n, good (if i.val = 0 then p else rowAt y (i.val - 1)) (y i) (rowAt y (i.val + 1))

private instance (n : ℕ) (p : Option Row) : DecidablePred (Good n p) := fun y => by
  unfold Good; infer_instance

private theorem upOK_rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) (r : Row) (j : Fin 3) :
    upOK (rowAt y k) r j ↔ ∃ i' : Fin n, i'.val = k ∧
      ∃ j' : Fin 3, j'.val = j.val + 1 ∧ (y i' j').val + (r j).val = 2 := by
  unfold rowAt
  split_ifs with h
  · simp only [upOK]
    constructor
    · intro hh; exact ⟨⟨k, h⟩, rfl, hh⟩
    · rintro ⟨i', rfl, hh⟩; exact hh
  · simp only [upOK, false_iff, not_exists, not_and]
    intro i' hi; have := i'.isLt; omega

private theorem dnOK_rowAt {n : ℕ} (y : Fin n → Row) (k : ℕ) (r : Row) (j : Fin 3) :
    dnOK (rowAt y k) r j ↔ ∃ i' : Fin n, i'.val = k ∧
      ∃ j' : Fin 3, j'.val + 1 = j.val ∧ (y i' j').val + (r j).val = 2 := by
  unfold rowAt
  split_ifs with h
  · simp only [dnOK]
    constructor
    · intro hh; exact ⟨⟨k, h⟩, rfl, hh⟩
    · rintro ⟨i', rfl, hh⟩; exact hh
  · simp only [dnOK, false_iff, not_exists, not_and]
    intro i' hi; have := i'.isLt; omega

private theorem valid_iff (n : ℕ) (A : Fin n → Row) : valid n A ↔ Good n none A := by
  unfold valid Good good
  refine forall_congr' fun i => forall_congr' fun j => ?_
  have hup : upOK (if i.val = 0 then none else rowAt A (i.val - 1)) (A i) j ↔
      ∃ i' : Fin n, i'.val + 1 = i.val ∧
        ∃ j' : Fin 3, j'.val = j.val + 1 ∧ (A i' j').val + (A i j).val = 2 := by
    split_ifs with h
    · simp only [upOK, false_iff, not_exists, not_and]
      intro i' hi; omega
    · rw [upOK_rowAt]
      constructor
      · rintro ⟨i', h1, h2⟩; exact ⟨i', by omega, h2⟩
      · rintro ⟨i', h1, h2⟩; exact ⟨i', by omega, h2⟩
  rw [hup, dnOK_rowAt]
  unfold horiz nextTo
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
  rw [a, Finset.filter_congr (fun A _ => valid_iff (n + 1) A), card_cons]
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


private def sat (p : Option Row) (r : Row) (j : Fin 3) : Prop := horiz r j ∨ upOK p r j

private instance (p : Option Row) (r : Row) (j : Fin 3) : Decidable (sat p r j) := by
  unfold sat; infer_instance

private def clsM (b1 b2 : Bool) : Fin 4 :=
  if b1 ∧ b2 then 3 else if b1 ∨ b2 then 1 else 2

private def cls (p : Option Row) (r : Row) : Fin 4 :=
  if sat p r 0 then clsM (decide (sat p r 1)) (decide (sat p r 2)) else 0

private def T : Fin 4 → Fin 4 → ℕ :=
  ![![0, 0, 0, 0], ![3, 4, 0, 2], ![0, 2, 0, 1], ![12, 6, 4, 5]]

private abbrev e : Fin (3 ^ 3) → Row := finFunctionFinEquiv.symm

private theorem hTM : ∀ (b1 b2 : Bool) (r : Fin (3 ^ 3)) (j : Fin 4),
    (horiz (e r) 1 → b1 = true) → (b2 = true ↔ horiz (e r) 2) →
    (Finset.univ.filter fun c : Fin (3 ^ 3) => (b1 = true ∨ dnOK (some (e c)) (e r) 1) ∧
      (b2 = true ∨ dnOK (some (e c)) (e r) 2) ∧ cls (some (e r)) (e c) = j).card =
      T (clsM b1 b2) j := by
  decide +kernel

private theorem hKM : ∀ j, (Finset.univ.filter fun r : Fin (3 ^ 3) => cls none (e r) = j).card =
    ![18, 6, 0, 3] j := by
  decide +kernel

private theorem forall3 (P : Fin 3 → Prop) : (∀ j, P j) ↔ P 0 ∧ P 1 ∧ P 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun ⟨h0, h1, h2⟩ j => by fin_cases j <;> assumption⟩

private theorem good_some (p : Option Row) (r c : Row) :
    good p r (some c) ↔
      sat p r 0 ∧ (sat p r 1 ∨ dnOK (some c) r 1) ∧ (sat p r 2 ∨ dnOK (some c) r 2) := by
  have hd : ¬ dnOK (some c) r 0 := by simp [dnOK]
  unfold good sat
  rw [forall3]
  simp only [or_assoc]
  tauto

private theorem sat_two (p : Option Row) (r : Row) : sat p r 2 ↔ horiz r 2 := by
  unfold sat
  cases p with
  | none => simp [upOK]
  | some q =>
    simp only [upOK, or_iff_left_iff_imp]
    rintro ⟨j', hj, -⟩
    have := j'.isLt
    simp at hj
    omega

private theorem hT (p : Option Row) (r : Row) (j : Fin 4) :
    (Finset.univ.filter fun c => good p r (some c) ∧ cls (some r) c = j).card = T (cls p r) j := by
  by_cases h0 : sat p r 0
  · have := hTM (decide (sat p r 1)) (decide (sat p r 2)) (finFunctionFinEquiv r) j
      (by simp only [e, Equiv.symm_apply_apply, decide_eq_true_eq]; intro h; exact Or.inl h)
      (by simp only [e, Equiv.symm_apply_apply, decide_eq_true_eq]; exact sat_two p r)
    rw [cls, if_pos h0, ← this]
    apply Finset.card_equiv finFunctionFinEquiv
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.symm_apply_apply,
      decide_eq_true_eq, good_some, h0, and_assoc]
  · have hn : ∀ c, ¬ good p r (some c) := fun c h => h0 ((good_some p r c).1 h).1
    rw [cls, if_neg h0]
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun c _ h => hn c h.1))]
    fin_cases j <;> rfl

private theorem lump {β : Type} [Fintype β] (cl : β → Fin 4) (P : β → Prop) [DecidablePred P]
    (g : Fin 4 → ℕ) :
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

private def w : ℕ → ℕ × ℕ × ℕ
  | 0 => (0, 0, 1)
  | m + 1 => (4 * (w m).1 + 2 * (w m).2.2, 2 * (w m).1 + (w m).2.2,
      6 * (w m).1 + 4 * (w m).2.1 + 5 * (w m).2.2)

private def wf (m : ℕ) : Fin 4 → ℕ := ![0, (w m).1, (w m).2.1, (w m).2.2]

private theorem wf_succ (m : ℕ) (k : Fin 4) : wf (m + 1) k = ∑ i, T k i * wf m i := by
  fin_cases k <;> simp [wf, w, T, Fin.sum_univ_four]

private theorem G_zero' (p : Option Row) (r : Row) : G 0 p r = wf 0 (cls p r) := by
  have hg : good p r none ↔ sat p r 0 ∧ sat p r 1 ∧ sat p r 2 := by
    unfold good sat
    rw [forall3]
    simp only [dnOK, or_false]
  rw [G_zero]
  unfold cls clsM
  by_cases h0 : sat p r 0 <;> by_cases h1 : sat p r 1 <;> by_cases h2 : sat p r 2 <;>
    simp [hg, h0, h1, h2, wf, w]

private theorem G_eq (m : ℕ) : ∀ p r, G m p r = wf m (cls p r) := by
  induction m with
  | zero => exact G_zero'
  | succ m ih =>
    intro p r
    rw [G_succ]
    simp only [ih]
    rw [lump (cls (some r)) (fun c => good p r (some c)) (wf m), wf_succ]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT]

private theorem a_succ (n : ℕ) : a (n + 1) = 6 * (w n).1 + 3 * (w n).2.2 := by
  rw [a_succ_eq]
  simp only [G_eq]
  have := lump (cls none) (fun _ => True) (wf n)
  simp only [if_true, true_and] at this
  rw [this]
  have hK : ∀ j, (Finset.univ.filter fun r : Row => cls none r = j).card = ![18, 6, 0, 3] j := by
    intro j
    rw [← hKM j]
    apply Finset.card_equiv finFunctionFinEquiv
    intro c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, e, Equiv.symm_apply_apply]
  simp only [hK, Fin.sum_univ_four]
  simp [wf]

private theorem a1 : a 1 = 3 := (a_succ 0).trans rfl
private theorem a2 : a 2 = 27 := (a_succ 1).trans rfl
private theorem a3 : a 3 = 231 := (a_succ 2).trans rfl

private theorem a_rec (m : ℕ) : a (m + 4) + 4 * a (m + 2) = 9 * a (m + 3) := by
  have h1 : a (m + 4) = 6 * (w (m + 3)).1 + 3 * (w (m + 3)).2.2 := a_succ (m + 3)
  have h2 : a (m + 2) = 6 * (w (m + 1)).1 + 3 * (w (m + 1)).2.2 := a_succ (m + 1)
  have h3 : a (m + 3) = 6 * (w (m + 2)).1 + 3 * (w (m + 2)).2.2 := a_succ (m + 2)
  rw [h1, h2, h3]
  simp only [w]
  ring

private theorem gf :
    (1 - 9 * X + 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (3 * X : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 9 * X + 4 * X ^ 2) * s =
      s - (s * C (9 : ℤ)) * X ^ 1 + (s * C (4 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (3 * X : PowerSeries ℤ) = C (3 : ℤ) * X ^ 1 := by
    simp only [pow_one, map_ofNat]
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · subst h; simp [a1, a2, a3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have := a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  3 / Real.sqrt 65 * (((9 + Real.sqrt 65) / 2) ^ n - ((9 - Real.sqrt 65) / 2) ^ n)

private theorem root_step (x : ℝ) (h : x ^ 2 = 9 * x - 4) (j : ℕ) :
    x ^ (j + 2) = 9 * x ^ (j + 1) - 4 * x ^ j := by
  linear_combination x ^ j * h

private theorem R_rec (j : ℕ) : R (j + 2) = 9 * R (j + 1) - 4 * R j := by
  have hs : Real.sqrt 65 ^ 2 = 65 := Real.sq_sqrt (by norm_num)
  have h1 := root_step ((9 + Real.sqrt 65) / 2) (by linear_combination hs / 4) j
  have h2 := root_step ((9 - Real.sqrt 65) / 2) (by linear_combination hs / 4) j
  unfold R
  rw [h1, h2]
  ring

private theorem closed (m : ℕ) :
    (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) ∧ (a (m + 3) : ℝ) = R (m + 3) := by
  have hne : Real.sqrt 65 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hs : Real.sqrt 65 ^ 2 = 65 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    simp only [zero_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [a1, R]; field_simp; ring
    · rw [a2, R]; field_simp; ring
    · rw [a3, R]; field_simp; linear_combination (-6 * Real.sqrt 65) * hs
  | succ m ih =>
    obtain ⟨-, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr : (a (m + 4) : ℝ) + 4 * (a (m + 2) : ℝ) = 9 * (a (m + 3) : ℝ) := by
      exact_mod_cast a_rec m
    have hR := R_rec (m + 2)
    rw [show m + 2 + 2 = m + 4 from rfl, show m + 2 + 1 = m + 3 from rfl] at hR
    rw [show m + 1 + 3 = m + 4 from rfl, hR]
    rw [show m + 1 + 2 = m + 3 from rfl] at h3
    rw [show m + 1 + 1 = m + 2 from rfl] at h2
    linarith

private theorem aR (n : ℕ) : (if n = 0 then 0 else (a n : ℝ)) = R n := by
  rcases n with _ | m
  · simp [R]
  · simp [(closed m).1]

private theorem hE (y : ℝ) : HasSum (fun n : ℕ => y ^ n / (n.factorial : ℝ)) (Real.exp y) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp y

private theorem egf (x : ℝ) :
    HasSum (fun n : ℕ => (if n = 0 then 0 else (a n : ℝ)) * x ^ n / (n.factorial : ℝ))
      (6 * Real.exp (9 * x / 2) * Real.sinh (Real.sqrt 65 * x / 2) / Real.sqrt 65) := by
  have h := ((hE ((9 + Real.sqrt 65) / 2 * x)).sub (hE ((9 - Real.sqrt 65) / 2 * x))).mul_left
    (3 / Real.sqrt 65)
  have hv : 3 / Real.sqrt 65 * (Real.exp ((9 + Real.sqrt 65) / 2 * x) -
      Real.exp ((9 - Real.sqrt 65) / 2 * x)) =
      6 * Real.exp (9 * x / 2) * Real.sinh (Real.sqrt 65 * x / 2) / Real.sqrt 65 := by
    rw [Real.sinh_eq, show (9 + Real.sqrt 65) / 2 * x = 9 * x / 2 + Real.sqrt 65 * x / 2 by ring,
      show (9 - Real.sqrt 65) / 2 * x = 9 * x / 2 + -(Real.sqrt 65 * x / 2) by ring,
      Real.exp_add, Real.exp_add]
    ring
  rw [hv] at h
  have hf : (fun n : ℕ => (if n = 0 then 0 else (a n : ℝ)) * x ^ n / (n.factorial : ℝ)) =
      fun n : ℕ => 3 / Real.sqrt 65 * (((9 + Real.sqrt 65) / 2 * x) ^ n / (n.factorial : ℝ) -
        ((9 - Real.sqrt 65) / 2 * x) ^ n / (n.factorial : ℝ)) := by
    funext n
    rw [aR, R, mul_pow, mul_pow]
    ring
  rw [hf]
  exact h

theorem OMA.solution : type_of% @OMA.S_oeis_a230179.main := by
  refine ⟨gf, fun n hn => ?_, egf⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : Real.sqrt 65 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  rw [(closed m).1, R, zpow_neg, zpow_natCast, div_pow, div_pow]
  field_simp
  ring

