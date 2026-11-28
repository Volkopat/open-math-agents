import OMAStatements.S_oeis_a208705

open OMA.S_oeis_a208705 PowerSeries

namespace A208705Proof

abbrev Row := Fin 4 → Fin 2

instance (u v : Row) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

instance (u : Row) : Decidable (Init u) := by unfold Init; infer_instance

-- The condition on the first row of a block below the row p (none for the top row).
def rowOK : Option Row → Row → Prop
  | none, r => Init r
  | some q, r => BlockOK q r

instance (p : Option Row) (r : Row) : Decidable (rowOK p r) := by
  cases p <;> unfold rowOK <;> infer_instance

def ExtOK (p : Option Row) {n : ℕ} (A : Fin n → Row) : Prop :=
  (∀ i j : Fin n, (j : ℕ) = i + 1 → BlockOK (A i) (A j)) ∧
    (∀ i : Fin n, (i : ℕ) = 0 → rowOK p (A i))

instance (p : Option Row) {n : ℕ} (A : Fin n → Row) : Decidable (ExtOK p A) := by
  unfold ExtOK; infer_instance

theorem good_iff {n : ℕ} (A : Fin n → Row) : Good A ↔ ExtOK none A := Iff.rfl

theorem ext_cons (p : Option Row) {n : ℕ} (r : Row) (B : Fin n → Row) :
    ExtOK p (Fin.cons r B : Fin (n + 1) → Row) ↔ rowOK p r ∧ ExtOK (some r) B := by
  unfold ExtOK
  simp only [Fin.forall_fin_succ (n := n), Fin.cons_zero, Fin.cons_succ, Fin.val_zero,
    Fin.val_succ]
  constructor
  · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3, -⟩
    refine ⟨h3 trivial, fun i j hij => (h2 i).2 j (by omega), fun i hi => h1 i (by omega)⟩
  · rintro ⟨h3, h2, h1⟩
    refine ⟨⟨⟨fun h => by omega, fun i hi => h1 i (by omega)⟩, fun i => ⟨fun h => by omega,
      fun j hj => h2 i j (by omega)⟩⟩, fun _ => h3, fun i hi => by omega⟩

def F (p : Option Row) (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Row => ExtOK p A).card

theorem F_succ (p : Option Row) (n : ℕ) :
    F p (n + 1) = ∑ r : Row, if rowOK p r then F (some r) n else 0 := by
  rw [F, Finset.card_filter, ← (Fin.consEquiv fun _ => Row).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, ext_cons]
  by_cases h : rowOK p r
  · rw [if_pos h, F, Finset.card_filter]
    exact Finset.sum_congr rfl fun B _ => by simp [h]
  · simp [h]

def cnt : ℕ → Option Row → ℕ
  | 0, _ => 1
  | n + 1, p => ∑ r : Row, if rowOK p r then cnt n (some r) else 0

theorem cnt_succ (n : ℕ) (p : Option Row) :
    cnt (n + 1) p = ∑ r : Row, if rowOK p r then cnt n (some r) else 0 := by
  rw [cnt]

theorem F_eq (n : ℕ) : ∀ p, F p n = cnt n p := by
  induction n with
  | zero =>
    intro p
    rw [F, Finset.filter_true_of_mem (fun A _ => ⟨fun i => i.elim0, fun i => i.elim0⟩)]
    simp [cnt]
  | succ n ih =>
    intro p
    rw [F_succ, cnt_succ]
    simp only [ih]

theorem a_eq (n : ℕ) : a n = cnt n none := by
  classical
  rw [← F_eq, a, Nat.card_eq_fintype_card, Fintype.card_subtype, F]
  exact congrArg Finset.card (Finset.filter_congr (fun A _ => good_iff A))

def W (n : ℕ) (p : Option Row) : ℤ :=
  (cnt (n + 2) p : ℤ) - 13 * cnt (n + 1) p + 4 * cnt n p

theorem W_succ (n : ℕ) (p : Option Row) :
    W (n + 1) p = ∑ r : Row, if rowOK p r then W n (some r) else 0 := by
  simp only [W, show n + 1 + 2 = n + 2 + 1 by ring]
  rw [cnt_succ (n + 2) p, cnt_succ (n + 1) p, cnt_succ n p]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : rowOK p r
  · simp only [if_pos h]
  · simp only [if_neg h]; ring

theorem W_base : ∀ q : Row, W 1 (some q) = 0 := by
  decide +kernel

theorem W_zero (n : ℕ) : ∀ q, W (n + 1) (some q) = 0 := by
  induction n with
  | zero => exact W_base
  | succ n ih =>
    intro q
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs
    · exact ih _
    · rfl

theorem a1 : a 1 = 8 := by rw [a_eq]; decide +kernel
theorem a2 : a 2 = 100 := by rw [a_eq]; decide +kernel
theorem a3 : a 3 = 1268 := by rw [a_eq]; decide +kernel

theorem a_rec (n : ℕ) : (a (n + 3) : ℤ) = 13 * a (n + 2) - 4 * a (n + 1) := by
  rcases n with _ | n
  · rw [a1, a2, a3]; norm_num
  have h : W (n + 2) none = 0 := by
    rw [W_succ]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs
    · exact W_zero n _
    · rfl
  simp only [W] at h
  rw [a_eq, a_eq, a_eq]
  rw [show n + 1 + 3 = n + 2 + 2 by ring, show n + 1 + 2 = n + 2 + 1 by ring,
    show n + 1 + 1 = n + 2 by ring]
  linarith

theorem gf :
    (1 - 13 * X + 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℚ)) =
      (4 * X * (2 - X) : PowerSeries ℚ) := by
  set s : PowerSeries ℚ := mk (fun n => if n = 0 then 0 else (a n : ℚ)) with hs
  have hd : (1 - 13 * X + 4 * X ^ 2) * s =
      s - (s * C (13 : ℚ)) * X ^ 1 + (s * C (4 : ℚ)) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  have hn : (4 * X * (2 - X) : PowerSeries ℚ) = C (8 : ℚ) * X ^ 1 - C (4 : ℚ) * X ^ 2 := by
    simp only [pow_one, map_ofNat]
    ring
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mul_C, coeff_C, hs, coeff_mk]
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ 3 ≤ n) with h | h | h | h
  · subst h; simp
  · subst h; simp [a1]
  · subst h; simp [a1, a2]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h := a_rec m
    have h' : (a (m + 3) : ℚ) = 13 * a (m + 2) - 4 * a (m + 1) := by exact_mod_cast h
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    simp
    linarith

noncomputable def R (n : ℕ) : ℝ :=
  (((13 - 3 * Real.sqrt 17) / 2) ^ n * (-1 + Real.sqrt 17) +
    (1 + Real.sqrt 17) * ((13 + 3 * Real.sqrt 17) / 2) ^ n) / (2 * Real.sqrt 17)

theorem R_eq (n : ℕ) : ((2 : ℝ) ^ (-1 - (n : ℤ)) * ((13 - 3 * Real.sqrt 17) ^ n *
      (-1 + Real.sqrt 17) + (1 + Real.sqrt 17) * (13 + 3 * Real.sqrt 17) ^ n)) /
      Real.sqrt 17 = R n := by
  rw [R, show (-1 - (n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    div_pow, div_pow, pow_succ]
  ring

theorem root_step (x : ℝ) (h : x ^ 2 = 13 * x - 4) (j : ℕ) :
    x ^ (j + 2) = 13 * x ^ (j + 1) - 4 * x ^ j := by
  linear_combination x ^ j * h

theorem R_rec (j : ℕ) : R (j + 2) = 13 * R (j + 1) - 4 * R j := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h1 := root_step ((13 - 3 * Real.sqrt 17) / 2) (by linear_combination 9 * hs / 4) j
  have h2 := root_step ((13 + 3 * Real.sqrt 17) / 2) (by linear_combination 9 * hs / 4) j
  unfold R
  rw [h1, h2]
  ring

theorem closed (m : ℕ) : (a (m + 1) : ℝ) = R (m + 1) ∧ (a (m + 2) : ℝ) = R (m + 2) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a1, R, eq_div_iff (by positivity)]; push_cast; ring
    · rw [a2, R, eq_div_iff (by positivity)]; push_cast
      linear_combination (-(9 * Real.sqrt 17 / 2)) * hs
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    have hr : (a (m + 3) : ℝ) = 13 * (a (m + 2) : ℝ) - 4 * (a (m + 1) : ℝ) := by
      exact_mod_cast a_rec m
    rw [show m + 1 + 2 = m + 3 by ring, hr, show m + 3 = (m + 1) + 2 by ring, R_rec, h1, h2]

end A208705Proof

open A208705Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a208705.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    exact a_rec m
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp), mul_comm]
    exact gf
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [(closed m).1, R_eq]

