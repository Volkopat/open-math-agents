import OMAStatements.S_oeis_a253029

open OMA.S_oeis_a253029 PowerSeries

private abbrev Row := Fin 3 → Fin 3

private def two (x y z : Fin 3) : Prop := ¬ (x = y ∧ y = z) ∧ ¬ (x ≠ y ∧ y ≠ z ∧ x ≠ z)

private instance (x y z : Fin 3) : Decidable (two x y z) := by unfold two; infer_instance

private theorem card_two : ∀ x y z : Fin 3, ({x, y, z} : Finset (Fin 3)).card = 2 ↔ two x y z := by
  decide

private def rowOK (r : Row) : Prop := two (r 0) (r 1) (r 2)

private def colOK (a b c : Row) : Prop := ∀ j, two (a j) (b j) (c j)

private instance (r : Row) : Decidable (rowOK r) := by unfold rowOK; infer_instance

private instance (a b c : Row) : Decidable (colOK a b c) := by unfold colOK; infer_instance

private def VV (n : ℕ) (A : Fin (n + 2) → Row) : Prop :=
  (∀ i, rowOK (A i)) ∧ ∀ i : Fin n,
    colOK (A ⟨i.val, by omega⟩) (A ⟨i.val + 1, by omega⟩) (A ⟨i.val + 2, by omega⟩)

private instance (n : ℕ) : DecidablePred (VV n) := fun A => by unfold VV; infer_instance

private theorem zero_of (x : Fin 3) (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 0 := by
  revert x; decide

private theorem valid_iff (n : ℕ) (A : Fin (n + 2) → Row) :
    valid n A ↔ VV n A ∧ A 0 0 = 0 ∧ ∀ j, A 0 j ≠ 2 := by
  unfold valid VV rowOK colOK
  simp only [card_two]
  constructor
  · rintro ⟨hr, hc, ho⟩
    have h00 : A 0 0 = 0 := by
      by_contra h
      have h1 : 1 ≤ (A 0 0).val := by
        rcases Nat.eq_zero_or_pos (A 0 0).val with h' | h'
        · exact absurd (Fin.ext h') h
        · exact h'
      obtain ⟨i', j', hlt, -⟩ := ho 0 0 h1
      rcases hlt with h | ⟨_, h⟩ <;> simp at h
    refine ⟨⟨hr, hc⟩, h00, fun j hj => ?_⟩
    obtain ⟨i', j', hlt, hv⟩ := ho 0 j (by rw [hj]; decide)
    rcases hlt with h | ⟨rfl, h⟩
    · simp at h
    · have hv' : A 0 j' = 1 := Fin.ext (by rw [hj] at hv; simp at hv; simp; omega)
      have hr0 := hr 0
      unfold two at hr0
      fin_cases j <;> fin_cases j' <;> simp_all
  · rintro ⟨⟨hr, hc⟩, h00, h2⟩
    refine ⟨hr, hc, fun i j hv => ?_⟩
    have hlt := (A i j).isLt
    rcases (by omega : (A i j).val = 1 ∨ (A i j).val = 2) with h1 | h1
    · refine ⟨0, 0, ?_, by rw [h00, h1]; rfl⟩
      by_cases hi : i = 0
      · subst hi
        right
        refine ⟨rfl, ?_⟩
        rcases Nat.eq_zero_or_pos j.val with hj | hj
        · have : j = 0 := Fin.ext hj
          subst this
          rw [h00] at h1
          simp at h1
        · exact hj
      · left
        simp only [Fin.val_zero]
        exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
    · have hi : i ≠ 0 := by
        rintro rfl
        exact h2 j (Fin.ext (by rw [h1]; rfl))
      have hex : ∃ j', A 0 j' = 1 := by
        have hr0 := (hr 0).1
        by_cases h : A 0 1 = 1
        · exact ⟨1, h⟩
        by_cases h' : A 0 2 = 1
        · exact ⟨2, h'⟩
        exfalso
        apply hr0
        exact ⟨h00.trans (zero_of _ h (h2 1)).symm,
          (zero_of _ h (h2 1)).trans (zero_of _ h' (h2 2)).symm⟩
      obtain ⟨j', hj'⟩ := hex
      refine ⟨0, j', Or.inl ?_, by rw [hj', h1]; rfl⟩
      simp only [Fin.val_zero]
      exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))

private theorem VV_cons (m : ℕ) (a b c : Row) (z : Fin m → Row) :
    VV (m + 1) (Fin.cons a (Fin.cons b (Fin.cons c z))) ↔
      rowOK a ∧ colOK a b c ∧ VV m (Fin.cons b (Fin.cons c z)) := by
  unfold VV
  constructor
  · rintro ⟨hr, hc⟩
    exact ⟨hr 0, hc 0, fun i => hr i.succ, fun i => hc i.succ⟩
  · rintro ⟨h1, h2, hr, hc⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · cases i using Fin.cases with
      | zero => exact h1
      | succ i => exact hr i
    · cases i using Fin.cases with
      | zero => exact h2
      | succ i => exact hc i

private theorem VV_two (a b : Row) (z : Fin 0 → Row) :
    VV 0 (Fin.cons a (Fin.cons b z)) ↔ rowOK a ∧ rowOK b := by
  unfold VV
  constructor
  · rintro ⟨hr, -⟩
    exact ⟨hr 0, hr 1⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => i.elim0⟩
    fin_cases i
    · exact h1
    · exact h2

private theorem card_cons {α : Type} [Fintype α] [DecidableEq α] (n : ℕ)
    (P : (Fin (n + 1) → α) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ c : α, (Finset.univ.filter fun y : Fin n → α => P (Fin.cons c y)).card := by
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  simp [Fin.consEquiv]
  simp only [Finset.card_filter]
  congr! 3

private theorem lump {α : Type} [Fintype α] (f : α → Fin 3) (P : α → Prop)
    [DecidablePred P] (g : Fin 3 → ℕ) :
    ∑ c : α, (if P c then g (f c) else 0) =
      ∑ j, (Finset.univ.filter fun c => P c ∧ f c = j).card * g j := by
  rw [← Finset.sum_fiberwise Finset.univ f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun c => if P c then g j else 0)
    (fun c hc => by rw [(Finset.mem_filter.1 hc).2])]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    Finset.filter_filter]
  congr 2
  ext c
  simp [and_comm]

private def H (m : ℕ) (a b : Row) : ℕ :=
  (Finset.univ.filter fun z : Fin m → Row => VV m (Fin.cons a (Fin.cons b z))).card

private theorem H_zero (a b : Row) : H 0 a b = if rowOK a ∧ rowOK b then 1 else 0 := by
  unfold H
  simp only [VV_two]
  by_cases h : rowOK a ∧ rowOK b <;> simp [h]

private theorem H_succ (m : ℕ) (a b : Row) :
    H (m + 1) a b = ∑ c, if rowOK a ∧ colOK a b c then H m b c else 0 := by
  rw [H, card_cons]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [VV_cons]
  by_cases h : rowOK a ∧ colOK a b c
  · rw [if_pos h]; simp [h.1, h.2, H]
  · rw [if_neg h]
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun z _ hz => h ⟨hz.1, hz.2.1⟩))]

private def cls (a b : Row) : Fin 3 :=
  if rowOK a ∧ rowOK b then (if a 0 + a 1 + a 2 = b 0 + b 1 + b 2 then 0 else 1) else 2

private def T : Fin 3 → Fin 3 → ℕ := ![![2, 3, 0], ![3, 3, 0], ![0, 0, 0]]

private abbrev e : Fin (3 ^ 3) → Row := finFunctionFinEquiv.symm

private theorem hTM : ∀ (a b : Fin (3 ^ 3)) (j : Fin 3), j ≠ 2 →
    (Finset.univ.filter fun c : Fin (3 ^ 3) =>
      (rowOK (e a) ∧ colOK (e a) (e b) (e c)) ∧ cls (e b) (e c) = j).card =
      T (cls (e a) (e b)) j := by
  decide +kernel

private theorem hT (a b : Row) (j : Fin 3) (hj : j ≠ 2) :
    (Finset.univ.filter fun c => (rowOK a ∧ colOK a b c) ∧ cls b c = j).card = T (cls a b) j := by
  have := hTM (finFunctionFinEquiv a) (finFunctionFinEquiv b) j hj
  simp only [e, Equiv.symm_apply_apply] at this
  rw [← this]
  apply Finset.card_equiv finFunctionFinEquiv
  intro c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]

private def S (a : Row) : Prop := a 0 = 0 ∧ ∀ j, a j ≠ 2

private instance (a : Row) : Decidable (S a) := by unfold S; infer_instance

private def K : Fin 3 → ℕ := ![27, 27, 54]

private theorem hKM : ∀ j : Fin 3, (Finset.univ.filter fun p : Fin (3 ^ 3) × Fin (3 ^ 3) =>
    S (e p.1) ∧ cls (e p.1) (e p.2) = j).card = K j := by
  decide +kernel

private theorem hK (j : Fin 3) : (Finset.univ.filter fun p : Row × Row =>
    S p.1 ∧ cls p.1 p.2 = j).card = K j := by
  rw [← hKM j]
  apply Finset.card_equiv (finFunctionFinEquiv.prodCongr finFunctionFinEquiv)
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.prodCongr_apply,
    Prod.map_fst, Prod.map_snd, e, Equiv.symm_apply_apply]

private def g : ℕ → Fin 3 → ℕ
  | 0 => ![1, 1, 0]
  | m + 1 => fun k => ∑ i, T k i * g m i

private theorem g_dead (m : ℕ) : g m 2 = 0 := by
  cases m with
  | zero => rfl
  | succ m => simp [g, T, Fin.sum_univ_succ]

private theorem H_eq (m : ℕ) : ∀ a b, H m a b = g m (cls a b) := by
  induction m with
  | zero =>
    intro a b
    rw [H_zero]
    unfold cls
    split_ifs <;> rfl
  | succ m ih =>
    intro a b
    rw [H_succ]
    simp only [ih]
    rw [lump (cls b) (fun c => rowOK a ∧ colOK a b c) (g m)]
    simp only [g]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = 2
    · subst hj
      rw [g_dead, mul_zero, mul_zero]
    · rw [hT a b j hj]

private theorem a_eq (n : ℕ) : a n = ∑ j, K j * g n j := by
  rw [a, Finset.filter_congr (fun A _ => valid_iff n A), card_cons]
  have h1 : ∀ x : Row, (Finset.univ.filter fun y : Fin (n + 1) → Row =>
      VV n (Fin.cons x y) ∧ (Fin.cons x y : Fin (n + 2) → Row) 0 0 = 0 ∧
        ∀ j, (Fin.cons x y : Fin (n + 2) → Row) 0 j ≠ 2).card =
      ∑ b : Row, if S x then g n (cls x b) else 0 := by
    intro x
    rw [card_cons]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Fin.cons_zero]
    by_cases hx : S x
    · rw [if_pos hx, ← H_eq]
      simp [hx.1, hx.2, H]
    · rw [if_neg hx]
      rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 (fun z _ hz => hx hz.2))]
  rw [Finset.sum_congr rfl (fun x _ => h1 x)]
  rw [← Fintype.sum_prod_type' (fun x b => if S x then g n (cls x b) else 0)]
  rw [lump (fun p : Row × Row => cls p.1 p.2) (fun p => S p.1) (g n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hK]

private theorem a1 : a 1 = 297 := (a_eq 1).trans (by decide +kernel)
private theorem a2 : a 2 = 1647 := (a_eq 2).trans (by decide +kernel)

private theorem a_rec (m : ℕ) : a (m + 2) = 5 * a (m + 1) + 3 * a m := by
  rw [a_eq, a_eq, a_eq]
  simp only [g, Fin.sum_univ_succ, Fin.sum_univ_zero, K, T]
  simp [g_dead]
  ring

private theorem gf :
    (1 - 5 * X - 3 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (27 * X * (11 + 6 * X) : PowerSeries ℤ) := by
  set s : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ)) with hs
  have hd : (1 - 5 * X - 3 * X ^ 2) * s =
      s - (s * C (5 : ℤ)) * X ^ 1 - (s * C (3 : ℤ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (27 * X * (11 + 6 * X) : PowerSeries ℤ) = C (297 : ℤ) * X ^ 1 + C (162 : ℤ) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have := a_rec (m + 1)
    rw [show m + 1 + 2 = m + 3 from rfl, show m + 1 + 1 = m + 2 from rfl] at this
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    simp
    omega

private noncomputable def R (n : ℕ) : ℝ :=
  27 / Real.sqrt 37 * (((5 - Real.sqrt 37) / 2) ^ n * (-6 + Real.sqrt 37) +
    ((5 + Real.sqrt 37) / 2) ^ n * (6 + Real.sqrt 37))

private theorem root_step (x : ℝ) (h : x ^ 2 = 5 * x + 3) (j : ℕ) :
    x ^ (j + 2) = 5 * x ^ (j + 1) + 3 * x ^ j := by
  linear_combination x ^ j * h

private theorem R_rec (j : ℕ) : R (j + 2) = 5 * R (j + 1) + 3 * R j := by
  have hs : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  have h1 := root_step ((5 - Real.sqrt 37) / 2) (by linear_combination hs / 4) j
  have h2 := root_step ((5 + Real.sqrt 37) / 2) (by linear_combination hs / 4) j
  unfold R
  rw [h1, h2]
  ring

private theorem closed (m : ℕ) : (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) := by
  have hne : Real.sqrt 37 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  have hs : Real.sqrt 37 ^ 2 = 37 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    simp only [zero_add]
    refine ⟨?_, ?_⟩
    · rw [a1, R]; field_simp; linear_combination (0 : ℝ) * hs
    · rw [a2, R]; field_simp; linear_combination (-54 * Real.sqrt 37) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 3) : ℝ) = 5 * a (m + 2) + 3 * a (m + 1) := by exact_mod_cast a_rec (m + 1)
    have hR := R_rec (m + 1)
    rw [show m + 1 + 2 = m + 3 from rfl, hr, h1, h2, hR]

theorem OMA.solution : type_of% @OMA.S_oeis_a253029.main := by
  refine ⟨gf, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hne : Real.sqrt 37 ≠ 0 := Real.sqrt_ne_zero'.2 (by norm_num)
  rw [(closed m).1, R, zpow_neg, zpow_natCast, div_pow, div_pow]
  field_simp

