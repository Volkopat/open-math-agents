import OMAStatements.S_oeis_a222276

namespace OMA.S_oeis_a222276

open PowerSeries Finset






/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 6 × Fin 6 × Fin 6) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6 × Fin 6 × Fin 6)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 6 × Fin 6 × Fin 6) (g : Fin (n + 1) → Fin 6 × Fin 6 × Fin 6) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 6 × Fin 6 × Fin 6) ↔
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 6 × Fin 6 × Fin 6, if r.1 = 0 then W n r else 0 := by
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

lemma W_zero (r : Fin 6 × Fin 6 × Fin 6) : W 0 r = if hrow r then 1 else 0 := by
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
def consEmb (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) :
    (Fin (n + 1) → Fin 6 × Fin 6 × Fin 6) ↪ (Fin (n + 2) → Fin 6 × Fin 6 × Fin 6) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) (g : Fin (n + 1) → Fin 6 × Fin 6 × Fin 6) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) :
    W (n + 1) r = ∑ s : Fin 6 × Fin 6 × Fin 6, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 6 × Fin 6 × Fin 6)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 6 × Fin 6 × Fin 6)).filter
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

/-- The number of rows allowed below a row: 0 for an invalid row, otherwise 88, or 89 when
x(i,2) = x(i,0) + 4 mod 6. -/
def dtab (r : Fin 6 × Fin 6 × Fin 6) : ℕ :=
  if hrow r then (if r.2.2.val = (r.1.val + 4) % 6 then 89 else 88) else 0

/-- W(1, r) written out from `W_succ` and `W_zero`. -/
def S1 (r : Fin 6 × Fin 6 × Fin 6) : ℕ :=
  (∑ s : Fin 6 × Fin 6 × Fin 6, if hrow r ∧ ok r s then (if hrow s then 1 else 0) else 0)

/-- The base case of the per-row recurrence, written out. -/
def S2 (r : Fin 6 × Fin 6 × Fin 6) : ℕ :=
  (∑ s : Fin 6 × Fin 6 × Fin 6, if hrow r ∧ ok r s then dtab s else 0) + 335 * (if hrow r then 1 else 0)


lemma S1_eq (r : Fin 6 × Fin 6 × Fin 6) : S1 r = dtab r := by
  revert r
  decide +kernel

lemma S2_eq (r : Fin 6 × Fin 6 × Fin 6) : S2 r = 92 * dtab r := by
  revert r
  decide +kernel

lemma W_one (r : Fin 6 × Fin 6 × Fin 6) : W 1 r = dtab r := by
  rw [W_succ]
  simp only [W_zero]
  exact S1_eq r

lemma base (r : Fin 6 × Fin 6 × Fin 6) :
    (∑ s : Fin 6 × Fin 6 × Fin 6, if hrow r ∧ ok r s then dtab s else 0) +
      335 * (if hrow r then 1 else 0) = 92 * dtab r :=
  S2_eq r

lemma W_rec (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) :
    W (n + 2) r + 335 * W n r = 92 * W (n + 1) r := by
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

lemma a_rec (n : ℕ) : a (n + 3) + 335 * a (n + 1) = 92 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_one : a 1 = 25 := by
  rw [a_succ]
  simp only [W_zero]
  decide +kernel

lemma a_two : a 2 = 2205 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 5x(5 - 19x)/(1 - 92x + 335x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 92 * X + 335 * X ^ 2) = 5 * X * (5 - 19 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 92 * X + 335 * X ^ 2) = A - A * X ^ 1 * C 92 + A * X ^ 2 * C 335 := by
    rw [show (92 : ℚ⟦X⟧) = C 92 from (map_ofNat C 92).symm,
      show (335 : ℚ⟦X⟧) = C 335 from (map_ofNat C 335).symm]
    ring
  have e2 : (5 : ℚ⟦X⟧) * X * (5 - 19 * X) = X ^ 1 * C 25 - X ^ 2 * C 95 := by
    rw [show (5 : ℚ⟦X⟧) = C 5 from (map_ofNat C 5).symm,
      show (19 : ℚ⟦X⟧) = C 19 from (map_ofNat C 19).symm, show (25 : ℚ) = 5 * 5 by norm_num,
      show (95 : ℚ) = 5 * 19 by norm_num, map_mul, map_mul]
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
    have hq : ((a (n + 3) : ℕ) : ℚ) + 335 * a (n + 1) = 92 * a (n + 2) := by exact_mod_cast h
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega, if_false,
      show 1 ≤ n + 3 by omega, show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 1 = 0) by omega]
    linear_combination hq

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    ((46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781)) / (134 * Real.sqrt 1781) := by
  have s2 : Real.sqrt 1781 ^ 2 = 1781 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 1781 := Real.sqrt_pos.2 (by norm_num)
  set G : ℕ → ℝ := fun n => (46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
    (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781) with hG
  have Grec : ∀ n, G (n + 2) = 92 * G (n + 1) - 335 * G n := by
    intro n
    simp only [hG]
    have h1 : (46 - Real.sqrt 1781) ^ 2 = 92 * (46 - Real.sqrt 1781) - 335 := by nlinarith [s2]
    have h2 : (46 + Real.sqrt 1781) ^ 2 = 92 * (46 + Real.sqrt 1781) - 335 := by nlinarith [s2]
    rw [show (46 - Real.sqrt 1781) ^ (n + 2) = (46 - Real.sqrt 1781) ^ n * (46 - Real.sqrt 1781) ^ 2
      by ring, show (46 + Real.sqrt 1781) ^ (n + 2) = (46 + Real.sqrt 1781) ^ n *
      (46 + Real.sqrt 1781) ^ 2 by ring, h1, h2]
    ring
  have G0 : G 0 = 38 * Real.sqrt 1781 := by
    simp only [hG]
    ring
  have G1 : G 1 = 3350 * Real.sqrt 1781 := by
    simp only [hG]
    nlinarith [s2]
  have G2 : G 2 = 295470 * Real.sqrt 1781 := by
    rw [show (2 : ℕ) = 0 + 2 from rfl, Grec, G1, G0]
    ring
  have key : ∀ k, (a (k + 1) : ℝ) * (134 * Real.sqrt 1781) = G (k + 1) ∧
      (a (k + 2) : ℝ) * (134 * Real.sqrt 1781) = G (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, G1]; push_cast; ring
      · rw [a_two, G2]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h := a_rec k
      have hr : ((a (k + 3) : ℕ) : ℝ) + 335 * a (k + 1) = 92 * a (k + 2) := by exact_mod_cast h
      rw [show k + 1 + 2 = (k + 1) + 2 by omega, Grec (k + 1),
        show k + 1 + 1 = k + 2 by omega, show k + 1 + 2 = k + 3 by omega]
      have ha : (a (k + 3) : ℝ) = 92 * a (k + 2) - 335 * a (k + 1) := by linarith
      rw [ha]
      linear_combination 92 * ih.2 - 335 * ih.1
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hne : (134 * Real.sqrt 1781) ≠ 0 := by positivity
  rw [eq_div_iff hne]
  exact hk

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 92 * X + 335 * X ^ 2) =
      5 * X * (5 - 19 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((46 - Real.sqrt 1781) ^ n * (-801 + 19 * Real.sqrt 1781) +
      (46 + Real.sqrt 1781) ^ n * (801 + 19 * Real.sqrt 1781)) / (134 * Real.sqrt 1781) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and a(1), a(2). -/
theorem controls : a 1 = 25 ∧ a 2 = 2205 ∧ a 3 = 194485 ∧ a 4 = 17153945 ∧ a 5 = 1513010465 ∧ a 6 = 133450391205 ∧ a 7 = 11770577485085 ∧ a 8 = 1038187247574145 ∧ a 9 = 91570083319317865 ∧ a 10 = 8076654937439905005 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have h1 := a_one; have h2 := a_two
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7
  omega

end OMA.S_oeis_a222276

theorem OMA.solution : type_of% @OMA.S_oeis_a222276.main :=
  OMA.S_oeis_a222276.conjecture
