import OMAStatements.S_oeis_a232950

namespace OMA.S_oeis_a232950

open PowerSeries Finset






/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 4 × Fin 4 × Fin 4) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4 × Fin 4 × Fin 4)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 4 × Fin 4 × Fin 4) (g : Fin (n + 1) → Fin 4 × Fin 4 × Fin 4) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 4 × Fin 4 × Fin 4) ↔
      hrow x ∧ ok x (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hx, h0, hg, hgo⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hx
      | succ i => simpa using hg i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          have hj : j = 0 := by ext; simp at hij; omega
          subst hj
          simpa using h0
      | succ i =>
        induction j using Fin.cases with
        | zero => simp at hij
        | succ j =>
          simp only [Fin.cons_succ]
          exact hgo i j (by simp at hij; omega)

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 4 × Fin 4 × Fin 4, if r.1 = 0 then W n r else 0 := by
  unfold a W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs with hr
  · congr 1
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2, _⟩, h4⟩
      exact ⟨⟨h1, h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      refine ⟨⟨h1, h2, fun i hi => ?_⟩, h4⟩
      have : i = 0 := Fin.ext hi
      rw [this, h4, hr]
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨_, _, h3⟩, h4⟩
    exact hr (h4 ▸ h3 0 rfl)

lemma W_zero (r : Fin 4 × Fin 4 × Fin 4) : W 0 r = if hrow r then 1 else 0 := by
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
      refine ⟨⟨fun _ => hr, ?_⟩, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨h1, _⟩, h0⟩
    exact hr (h0 ▸ h1 0)

/-- Prepending the row r to an array with n + 1 rows. -/
def consEmb (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4) :
    (Fin (n + 1) → Fin 4 × Fin 4 × Fin 4) ↪ (Fin (n + 2) → Fin 4 × Fin 4 × Fin 4) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4) (g : Fin (n + 1) → Fin 4 × Fin 4 × Fin 4) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4) :
    W (n + 1) r = ∑ s : Fin 4 × Fin 4 × Fin 4, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 4 × Fin 4 × Fin 4)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 4 × Fin 4 × Fin 4)).filter
        (fun g => (hrow r ∧ ok r (g 0)) ∧ Valid g)).map (consEmb n r)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons r (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, ⟨⟨h1, h2⟩, hg⟩, rfl⟩
      exact ⟨(valid_cons r g).2 ⟨h1, h2, hg⟩, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hrs
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨⟨hrs.1, h0 ▸ hrs.2⟩, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨⟨h1, h2⟩, _⟩, h0⟩
    exact hrs ⟨h1, h0 ▸ h2⟩

/-- The number of rows that may follow a row (0 for an invalid row), indexed by 16a + 4b + c. -/
def dtab (r : Fin 4 × Fin 4 × Fin 4) : ℕ :=
  [17, 13, 13, 0, 17, 13, 0, 13, 17, 0, 13, 13, 0, 0, 0, 0, 13, 17, 13, 0, 13, 17, 0, 13, 0, 0, 0,
    0, 0, 17, 13, 13, 13, 13, 17, 0, 0, 0, 0, 0, 13, 0, 17, 13, 0, 13, 17, 13, 0, 0, 0, 0, 13, 13,
    0, 17, 13, 0, 13, 17, 0, 13, 13, 17].getD (16 * r.1.val + 4 * r.2.1.val + r.2.2.val) 0

lemma W_one (r : Fin 4 × Fin 4 × Fin 4) : W 1 r = dtab r := by
  rw [W_succ]
  simp only [W_zero]
  revert r
  decide +kernel

lemma base (r : Fin 4 × Fin 4 × Fin 4) :
    (∑ s : Fin 4 × Fin 4 × Fin 4, if hrow r ∧ ok r s then dtab s else 0) +
      6 * (if hrow r then 1 else 0) = 15 * dtab r := by
  revert r
  decide +kernel

lemma W_rec (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4) : W (n + 2) r + 6 * W n r = 15 * W (n + 1) r := by
  induction n generalizing r with
  | zero =>
    rw [show 0 + 2 = 1 + 1 from rfl, W_succ 1 r, W_zero, show 0 + 1 = 1 from rfl, W_one]
    simp only [W_one]
    exact base r
  | succ n ih =>
    rw [W_succ (n + 2), W_succ (n + 1), W_succ n]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma a_rec (n : ℕ) : a (n + 3) + 6 * a (n + 1) = 15 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_one : a 1 = 9 := by
  rw [a_succ]
  simp only [W_zero]
  decide +kernel

lemma a_two : a 2 = 129 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 3x(3 - 2x)/(1 - 15x + 6x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 15 * X + 6 * X ^ 2) = 3 * X * (3 - 2 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 15 * X + 6 * X ^ 2) = A - A * X ^ 1 * C 15 + A * X ^ 2 * C 6 := by
    rw [show (15 : ℚ⟦X⟧) = C 15 from (map_ofNat C 15).symm,
      show (6 : ℚ⟦X⟧) = C 6 from (map_ofNat C 6).symm]
    ring
  have e2 : (3 : ℚ⟦X⟧) * X * (3 - 2 * X) = X ^ 1 * C 9 - X ^ 2 * C 6 := by
    rw [show (3 : ℚ⟦X⟧) = C 3 from (map_ofNat C 3).symm,
      show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, show (9 : ℚ) = 3 * 3 by norm_num,
      show (6 : ℚ) = 3 * 2 by norm_num, map_mul, map_mul]
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
    have hq : ((a (n + 3) : ℕ) : ℚ) + 6 * a (n + 1) = 15 * a (n + 2) := by exact_mod_cast h
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega,
      show ¬ (n + 3 - 2 = 0) by omega, if_false, show 1 ≤ n + 3 by omega,
      show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 1 = 0) by omega]
    linear_combination hq

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (2 ^ (-1 - (n : ℤ)) * ((15 - Real.sqrt 201) ^ n * (-3 + Real.sqrt 201) +
      (3 + Real.sqrt 201) * (15 + Real.sqrt 201) ^ n)) / Real.sqrt 201 := by
  have s2 : Real.sqrt 201 ^ 2 = 201 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 201 := Real.sqrt_pos.2 (by norm_num)
  set G : ℕ → ℝ := fun n => (15 - Real.sqrt 201) ^ n * (-3 + Real.sqrt 201) +
    (3 + Real.sqrt 201) * (15 + Real.sqrt 201) ^ n with hG
  have Grec : ∀ n, G (n + 2) = 30 * G (n + 1) - 24 * G n := by
    intro n
    simp only [hG]
    have h1 : (15 - Real.sqrt 201) ^ 2 = 30 * (15 - Real.sqrt 201) - 24 := by nlinarith [s2]
    have h2 : (15 + Real.sqrt 201) ^ 2 = 30 * (15 + Real.sqrt 201) - 24 := by nlinarith [s2]
    rw [show (15 - Real.sqrt 201) ^ (n + 2) = (15 - Real.sqrt 201) ^ n * (15 - Real.sqrt 201) ^ 2
      by ring, show (15 + Real.sqrt 201) ^ (n + 2) = (15 + Real.sqrt 201) ^ n *
      (15 + Real.sqrt 201) ^ 2 by ring, h1, h2]
    ring
  have G1 : G 1 = 36 * Real.sqrt 201 := by
    simp only [hG]
    nlinarith [s2]
  have G0 : G 0 = 2 * Real.sqrt 201 := by
    simp only [hG]
    ring
  have G2 : G 2 = 1032 * Real.sqrt 201 := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, Grec, G1, G0]
    ring
  have key : ∀ k, (a (k + 1) : ℝ) * 2 ^ (k + 2) * Real.sqrt 201 = G (k + 1) ∧
      (a (k + 2) : ℝ) * 2 ^ (k + 3) * Real.sqrt 201 = G (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, G1]; push_cast; ring
      · rw [a_two, G2]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := a_rec k
      have hr : ((a (k + 3) : ℕ) : ℝ) + 6 * a (k + 1) = 15 * a (k + 2) := by exact_mod_cast h
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 3 = k + 4 by omega,
        show k + 3 = (k + 1) + 2 by omega, Grec (k + 1)]
      rw [show (k + 1) + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega]
      have e1 := ih.1
      have e2 := ih.2
      have hp1 : (2 : ℝ) ^ (k + 4) = 2 ^ (k + 3) * 2 := by ring
      have hp2 : (2 : ℝ) ^ (k + 3) = 2 ^ (k + 2) * 2 := by ring
      rw [hp1]
      rw [hp2] at e2 ⊢
      have ha : (a (k + 3) : ℝ) = 15 * a (k + 2) - 6 * a (k + 1) := by linarith
      rw [ha]
      linear_combination 30 * e2 - 24 * e1
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hz : (2 : ℝ) ^ (-1 - ((k + 1 : ℕ) : ℤ)) = 1 / 2 ^ (k + 2) := by
    rw [show -1 - ((k + 1 : ℕ) : ℤ) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, one_div]
  rw [hz]
  have h2 : (0 : ℝ) < 2 ^ (k + 2) := by positivity
  field_simp
  have : (a (k + 1) : ℝ) * 2 ^ (k + 2) * Real.sqrt 201 = G (k + 1) := hk
  simp only [hG] at this
  linarith [this]

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 15 * X + 6 * X ^ 2) =
      3 * X * (3 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) * ((15 - Real.sqrt 201) ^ n * (-3 + Real.sqrt 201) +
        (3 + Real.sqrt 201) * (15 + Real.sqrt 201) ^ n)) / Real.sqrt 201 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..9), from the recurrence and a(1), a(2). -/
theorem controls : a 1 = 9 ∧ a 2 = 129 ∧ a 3 = 1881 ∧ a 4 = 27441 ∧ a 5 = 400329 ∧
    a 6 = 5840289 ∧ a 7 = 85202361 ∧ a 8 = 1242993681 ∧ a 9 = 18133691049 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3
  have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6
  have h1 := a_one; have h2 := a_two
  norm_num at r0 r1 r2 r3 r4 r5 r6
  omega

end OMA.S_oeis_a232950

theorem OMA.solution : type_of% @OMA.S_oeis_a232950.main :=
  OMA.S_oeis_a232950.conjecture
