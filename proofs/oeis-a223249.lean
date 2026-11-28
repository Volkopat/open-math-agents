import OMAStatements.S_oeis_a223249

namespace OMA.S_oeis_a223249

open PowerSeries Finset





/-- A row is valid when its two entries are adjacent. -/
def rowOK (r : Fin 2 → Fin 5) : Prop := adj (r 0) (r 1)

instance : DecidablePred rowOK := fun r => by unfold rowOK; infer_instance

/-- Row s may follow row r when the entries in each column are adjacent. -/
def stepOK (r s : Fin 2 → Fin 5) : Prop := ∀ j : Fin 2, adj (r j) (s j)

instance : DecidableRel stepOK := fun r s => by unfold stepOK; infer_instance

/-- The condition on an array used in `a`. -/
def Valid {n : ℕ} (f : Fin n → Fin 2 → Fin 5) : Prop :=
  (∀ i : Fin n, rowOK (f i)) ∧ ∀ i i' : Fin n, i'.val = i.val + 1 → stepOK (f i) (f i')

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → Fin 2 → Fin 5)).filter Valid).card := by
  unfold a Valid rowOK stepOK
  rfl

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 2 → Fin 5) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 2 → Fin 5)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 2 → Fin 5) (g : Fin (n + 1) → Fin 2 → Fin 5) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 2 → Fin 5) ↔
      rowOK x ∧ stepOK x (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, hs⟩
    refine ⟨by simpa using hr 0, by simpa using hs 0 1 (by simp), fun i => ?_,
      fun i i' hii => ?_⟩
    · simpa using hr i.succ
    · simpa using hs i.succ i'.succ (by simp [hii])
  · rintro ⟨hx, h0, hg, hgs⟩
    refine ⟨fun i => ?_, fun i i' hii => ?_⟩
    · induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hg i
    · induction i using Fin.cases with
      | zero =>
        induction i' using Fin.cases with
        | zero => simp at hii
        | succ j =>
          have hj : j = 0 := by ext; simp at hii; omega
          subst hj
          simpa using h0
      | succ i =>
        induction i' using Fin.cases with
        | zero => simp at hii
        | succ j =>
          simp only [Fin.cons_succ]
          exact hgs i j (by simp at hii; omega)

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 5, W n r := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (r : Fin 2 → Fin 5) : W 0 r = if rowOK r then 1 else 0 := by
  unfold W
  split_ifs with hr
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => r, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hf⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hf]
    · rintro rfl
      refine ⟨⟨fun _ => hr, fun i i' hii => ?_⟩, rfl⟩
      have := i'.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hrow, _⟩, h0⟩
    exact hr (h0 ▸ hrow 0)

/-- Prepending a row to an array with n + 1 rows. -/
def consEmb (n : ℕ) (x : Fin 2 → Fin 5) :
    (Fin (n + 1) → Fin 2 → Fin 5) ↪ (Fin (n + 2) → Fin 2 → Fin 5) where
  toFun g := Fin.cons x g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (x : Fin 2 → Fin 5) (g : Fin (n + 1) → Fin 2 → Fin 5) :
    consEmb n x g = Fin.cons x g := rfl

lemma W_succ (n : ℕ) (x : Fin 2 → Fin 5) :
    W (n + 1) x = ∑ y : Fin 2 → Fin 5, if rowOK x ∧ stepOK x y then W n y else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 2 → Fin 5)).filter
      (fun f => Valid f ∧ f 0 = x)) =
      (((univ : Finset (Fin (n + 1) → Fin 2 → Fin 5)).filter
        (fun g => rowOK x ∧ stepOK x (g 0) ∧ Valid g)).map (consEmb n x)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons x (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(valid_cons x g).2 hg, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  split_ifs with hxy
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, _, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨hxy.1, h0 ▸ hxy.2, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hr, hs, _⟩, h0⟩
    exact hxy ⟨hr, h0 ▸ hs⟩

lemma W_rec (n : ℕ) (x : Fin 2 → Fin 5) : W (n + 2) x + 2 * W n x = 5 * W (n + 1) x := by
  induction n generalizing x with
  | zero =>
    rw [W_succ, W_succ]
    simp only [W_succ, W_zero]
    revert x
    decide
  | succ n ih =>
    rw [W_succ (n + 2), W_succ (n + 1), W_succ n]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs
    · exact ih y
    · simp

lemma a_rec (n : ℕ) : a (n + 3) + 2 * a (n + 1) = 5 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => W_rec n x)

lemma a_one : a 1 = 12 := by
  rw [a_succ]
  simp only [W_zero]
  decide

lemma a_two : a 2 = 52 := by
  rw [a_succ]
  simp only [W_succ, W_zero]
  decide

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 4x(3 - 2x)/(1 - 5x + 2x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 5 * X + 2 * X ^ 2) = 4 * X * (3 - 2 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 5 * X + 2 * X ^ 2) = A - A * X ^ 1 * C 5 + A * X ^ 2 * C 2 := by
    rw [show (5 : ℚ⟦X⟧) = C 5 from (map_ofNat C 5).symm,
      show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm]
    ring
  have e2 : (4 : ℚ⟦X⟧) * X * (3 - 2 * X) = X ^ 1 * C 12 - X ^ 2 * C 8 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two]
    norm_num
  · have h := a_rec n
    simp only [show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega]
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 1 = 0) by omega, if_false, show 1 ≤ n + 3 by omega,
      show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega]
    have hq : (a (n + 3) : ℚ) = 5 * a (n + 2) - 2 * a (n + 1) := by
      have : (a (n + 3) : ℚ) + 2 * a (n + 1) = 5 * a (n + 2) := by exact_mod_cast h
      linarith
    rw [hq]
    ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (2 ^ ((1 : ℤ) - n) * ((5 - Real.sqrt 17) ^ n * (-1 + Real.sqrt 17) +
      (1 + Real.sqrt 17) * (5 + Real.sqrt 17) ^ n)) / Real.sqrt 17 := by
  have s17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 17 := Real.sqrt_pos.2 (by norm_num)
  set p := (5 + Real.sqrt 17) / 2 with hp
  set q := (5 - Real.sqrt 17) / 2 with hq
  set G : ℕ → ℝ := fun n => 2 * (q ^ n * (-1 + Real.sqrt 17) + (1 + Real.sqrt 17) * p ^ n) /
    Real.sqrt 17 with hG
  have hrew : ∀ n : ℕ, (2 ^ ((1 : ℤ) - n) * ((5 - Real.sqrt 17) ^ n * (-1 + Real.sqrt 17) +
      (1 + Real.sqrt 17) * (5 + Real.sqrt 17) ^ n)) / Real.sqrt 17 = G n := by
    intro n
    have h2 : (2 : ℝ) ^ ((1 : ℤ) - n) * 2 ^ n = 2 := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      norm_num
    have e5 : (5 - Real.sqrt 17) ^ n = 2 ^ n * q ^ n := by rw [hq, ← mul_pow]; ring
    have e6 : (5 + Real.sqrt 17) ^ n = 2 ^ n * p ^ n := by rw [hp, ← mul_pow]; ring
    rw [e5, e6, hG]
    simp only
    have : (2 : ℝ) ^ ((1 : ℤ) - n) * (2 ^ n * q ^ n * (-1 + Real.sqrt 17) +
        (1 + Real.sqrt 17) * (2 ^ n * p ^ n)) =
        ((2 : ℝ) ^ ((1 : ℤ) - n) * 2 ^ n) * (q ^ n * (-1 + Real.sqrt 17) +
          (1 + Real.sqrt 17) * p ^ n) := by ring
    rw [this, h2]
  have hp2 : p ^ 2 = 5 * p - 2 := by rw [hp]; nlinarith [s17]
  have hq2 : q ^ 2 = 5 * q - 2 := by rw [hq]; nlinarith [s17]
  have G1 : G 1 = 12 := by
    simp only [hG, pow_one, hp, hq]
    field_simp
    nlinarith [s17]
  have G2 : G 2 = 52 := by
    simp only [hG, hp, hq]
    field_simp
    nlinarith [s17]
  have Grec : ∀ n, G (n + 3) = 5 * G (n + 2) - 2 * G (n + 1) := by
    intro n
    simp only [hG]
    have r1 : p ^ (n + 3) = 5 * p ^ (n + 2) - 2 * p ^ (n + 1) := by
      calc p ^ (n + 3) = p ^ (n + 1) * p ^ 2 := by ring
        _ = _ := by rw [hp2]; ring
    have r2 : q ^ (n + 3) = 5 * q ^ (n + 2) - 2 * q ^ (n + 1) := by
      calc q ^ (n + 3) = q ^ (n + 1) * q ^ 2 := by ring
        _ = _ := by rw [hq2]; ring
    rw [r1, r2]
    ring
  have key : ∀ n, (a (n + 1) : ℝ) = G (n + 1) ∧ (a (n + 2) : ℝ) = G (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [a_one, G1]; norm_num, by rw [a_two, G2]; norm_num⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 2 = n + 3 by omega, Grec]
      have h := a_rec n
      have hr : (a (n + 3) : ℝ) = 5 * a (n + 2) - 2 * a (n + 1) := by
        have : (a (n + 3) : ℝ) + 2 * a (n + 1) = 5 * a (n + 2) := by exact_mod_cast h
        linarith
      rw [hr, ih.1, ih.2]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hrew]
  exact (key k).1

/-- Controls: a(1..4) = 12, 52, 236, 1076 (the entry's data). -/
theorem controls : a 1 = 12 ∧ a 2 = 52 ∧ a 3 = 236 ∧ a 4 = 1076 := by
  have h3 : a 3 = 236 := by
    have h := a_rec 0
    rw [show 0 + 3 = 3 from rfl, show 0 + 1 = 1 from rfl, show 0 + 2 = 2 from rfl, a_one,
      a_two] at h
    generalize a 3 = x at h ⊢
    omega
  have h4 : a 4 = 1076 := by
    have h := a_rec 1
    rw [show 1 + 3 = 4 from rfl, show 1 + 1 = 2 from rfl, show 1 + 2 = 3 from rfl, a_two,
      h3] at h
    generalize a 4 = x at h ⊢
    omega
  exact ⟨a_one, a_two, h3, h4⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 5 * X + 2 * X ^ 2) =
      4 * X * (3 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ ((1 : ℤ) - n) * ((5 - Real.sqrt 17) ^ n * (-1 + Real.sqrt 17) +
        (1 + Real.sqrt 17) * (5 + Real.sqrt 17) ^ n)) / Real.sqrt 17 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223249

theorem OMA.solution : type_of% @OMA.S_oeis_a223249.main :=
  OMA.S_oeis_a223249.conjecture
