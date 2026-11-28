import OMAStatements.S_oeis_a223291

namespace OMA.S_oeis_a223291

open PowerSeries Finset





/-- A row, as the pair of its two entries. -/
abbrev S := Fin 9 × Fin 9

/-- A row is allowed when its two entries are adjacent. -/
def rowOK (s : S) : Prop := adj s.1 s.2

/-- Two consecutive rows are compatible when both columns move along edges. -/
def step (s t : S) : Prop := adj s.1 t.1 ∧ adj s.2 t.2

instance : DecidablePred rowOK := fun s => by unfold rowOK; infer_instance

instance : DecidableRel step := fun s t => by unfold step; infer_instance

/-- A valid sequence of rows. -/
def Valid {n : ℕ} (g : Fin n → S) : Prop :=
  (∀ i, rowOK (g i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → step (g i) (g j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun g => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → S)).filter Valid).card := by
  unfold a
  apply Finset.card_bij (fun f _ => fun i => ((f i 0, f i 1) : S))
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    obtain ⟨h1, h2⟩ := hf
    exact ⟨fun i => h1 i, fun i j hij => ⟨h2 i j hij 0, h2 i j hij 1⟩⟩
  · intro f _ g _ hfg
    funext i j
    have := congrFun hfg i
    simp only [Prod.mk.injEq] at this
    fin_cases j
    · exact this.1
    · exact this.2
  · intro g hg
    refine ⟨fun i j => if j = 0 then (g i).1 else (g i).2, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      obtain ⟨h1, h2⟩ := hg
      refine ⟨fun i => by simpa [rowOK] using h1 i, fun i i' hii j => ?_⟩
      fin_cases j
      · simpa using (h2 i i' hii).1
      · simpa using (h2 i i' hii).2
    · funext i
      simp

/-- W(n, s): valid sequences of n + 1 rows whose first row is s. -/
def W (n : ℕ) (s : S) : ℕ :=
  ((univ : Finset (Fin (n + 1) → S)).filter (fun g => Valid g ∧ g 0 = s)).card

lemma valid_cons {n : ℕ} (s : S) (g : Fin (n + 1) → S) :
    Valid (Fin.cons s g : Fin (n + 2) → S) ↔ rowOK s ∧ step s (g 0) ∧ Valid g := by
  constructor
  · rintro ⟨hr, h⟩
    refine ⟨by simpa using hr 0, ?_, fun i => by simpa using hr i.succ, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨hs, h0, hr, hg⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hs
      | succ i => simpa using hr i
    intro i j hij
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
        exact hg i j (by simp at hij; omega)

lemma a_succ (n : ℕ) : a (n + 1) = ∑ s : S, W n s := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  congr 1
  ext g
  simp

lemma W_zero (s : S) : W 0 s = if rowOK s then 1 else 0 := by
  unfold W
  split_ifs with hs
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => s, ?_⟩
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hg⟩
      funext i
      rw [Fin.fin_one_eq_zero i, hg]
    · rintro rfl
      refine ⟨⟨fun _ => hs, ?_⟩, rfl⟩
      intro i j hij
      have := j.isLt
      omega
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hr, _⟩, h0⟩
    exact hs (h0 ▸ hr 0)

/-- Prepending the row s to a sequence of n + 1 rows. -/
def consEmb (n : ℕ) (s : S) : (Fin (n + 1) → S) ↪ (Fin (n + 2) → S) where
  toFun g := Fin.cons s g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (s : S) (g : Fin (n + 1) → S) :
    consEmb n s g = Fin.cons s g := rfl

lemma W_succ (n : ℕ) (s : S) :
    W (n + 1) s = if rowOK s then ∑ t : S, (if step s t then W n t else 0) else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → S)).filter (fun g => Valid g ∧ g 0 = s)) =
      (((univ : Finset (Fin (n + 1) → S)).filter
        (fun g => rowOK s ∧ step s (g 0) ∧ Valid g)).map (consEmb n s)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail g, ?_, ?_⟩
      · have hg : g = Fin.cons s (Fin.tail g) := by
          rw [← h0]; exact (Fin.cons_self_tail g).symm
        rw [hg, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail g
    · rintro ⟨g', hg', rfl⟩
      exact ⟨(valid_cons s g').2 hg', by simp⟩
  unfold W
  rw [e, Finset.card_map]
  split_ifs with hs
  · rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    split_ifs with hst
    · congr 1
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨_, _, hg⟩, h0⟩
        exact ⟨hg, h0⟩
      · rintro ⟨hg, h0⟩
        exact ⟨⟨hs, h0 ▸ hst, hg⟩, h0⟩
    · rw [Finset.card_eq_zero]
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨_, hst', _⟩, h0⟩
      exact hst (h0 ▸ hst')
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hs', _⟩
    exact hs hs'

/-- W(0), W(1), W(2) as tables indexed by the two entries of the first row. -/
def d0 (s : S) : ℕ :=
  ![![0, 1, 1, 1, 1, 1, 1, 1, 1], ![1, 0, 1, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0, 0],
    ![1, 0, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0, 0, 0, 1], ![1, 0, 0, 0, 0, 0, 0, 1, 0]]
    s.1 s.2

def d1 (s : S) : ℕ :=
  ![![0, 9, 9, 9, 9, 9, 9, 9, 9], ![9, 0, 3, 0, 0, 0, 0, 0, 0], ![9, 3, 0, 0, 0, 0, 0, 0, 0],
    ![9, 0, 0, 0, 3, 0, 0, 0, 0], ![9, 0, 0, 3, 0, 0, 0, 0, 0], ![9, 0, 0, 0, 0, 0, 3, 0, 0],
    ![9, 0, 0, 0, 0, 3, 0, 0, 0], ![9, 0, 0, 0, 0, 0, 0, 0, 3], ![9, 0, 0, 0, 0, 0, 0, 3, 0]]
    s.1 s.2

def d2 (s : S) : ℕ :=
  ![![0, 75, 75, 75, 75, 75, 75, 75, 75], ![75, 0, 21, 0, 0, 0, 0, 0, 0],
    ![75, 21, 0, 0, 0, 0, 0, 0, 0], ![75, 0, 0, 0, 21, 0, 0, 0, 0], ![75, 0, 0, 21, 0, 0, 0, 0, 0],
    ![75, 0, 0, 0, 0, 0, 21, 0, 0], ![75, 0, 0, 0, 0, 21, 0, 0, 0], ![75, 0, 0, 0, 0, 0, 0, 0, 21],
    ![75, 0, 0, 0, 0, 0, 0, 21, 0]] s.1 s.2

lemma W_zero' (s : S) : W 0 s = d0 s := by
  rw [W_zero]
  revert s
  decide +kernel

lemma W_one (s : S) : W 1 s = d1 s := by
  rw [W_succ]
  simp only [W_zero']
  revert s
  decide +kernel

lemma W_two (s : S) : W 2 s = d2 s := by
  rw [W_succ]
  simp only [W_one]
  revert s
  decide +kernel

lemma W_rec (n : ℕ) (s : S) : W (n + 2) s + 6 * W n s = 9 * W (n + 1) s := by
  induction n generalizing s with
  | zero =>
    rw [W_two, W_one, W_zero']
    revert s
    decide +kernel
  | succ n ih =>
    rw [W_succ (n + 2), W_succ n, W_succ (n + 1)]
    split_ifs
    · rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      split_ifs
      · exact ih t
      · simp
    · simp

lemma a_rec (n : ℕ) : a (n + 3) + 6 * a (n + 1) = 9 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => W_rec n s)

lemma a_one : a 1 = 24 := by
  rw [a_succ]
  simp only [W_zero']
  decide +kernel

lemma a_two : a 2 = 168 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

/-- Controls: the entry's data a(1..14). -/
theorem controls : a 1 = 24 ∧ a 2 = 168 ∧ a 3 = 1368 ∧ a 4 = 11304 ∧ a 5 = 93528 ∧
    a 6 = 773928 ∧ a 7 = 6404184 ∧ a 8 = 52994088 ∧ a 9 = 438521688 ∧ a 10 = 3628730664 ∧
    a 11 = 30027445848 ∧ a 12 = 248474628648 ∧ a 13 = 2056106982744 ∧
    a 14 = 17014115072808 := by
  have h1 := a_one
  have h2 := a_two
  have h3 : a 3 = 1368 := by
    have h := a_rec 0; norm_num [h1, h2] at h; generalize a 3 = x at h ⊢; omega
  have h4 : a 4 = 11304 := by
    have h := a_rec 1; norm_num [h2, h3] at h; generalize a 4 = x at h ⊢; omega
  have h5 : a 5 = 93528 := by
    have h := a_rec 2; norm_num [h3, h4] at h; generalize a 5 = x at h ⊢; omega
  have h6 : a 6 = 773928 := by
    have h := a_rec 3; norm_num [h4, h5] at h; generalize a 6 = x at h ⊢; omega
  have h7 : a 7 = 6404184 := by
    have h := a_rec 4; norm_num [h5, h6] at h; generalize a 7 = x at h ⊢; omega
  have h8 : a 8 = 52994088 := by
    have h := a_rec 5; norm_num [h6, h7] at h; generalize a 8 = x at h ⊢; omega
  have h9 : a 9 = 438521688 := by
    have h := a_rec 6; norm_num [h7, h8] at h; generalize a 9 = x at h ⊢; omega
  have h10 : a 10 = 3628730664 := by
    have h := a_rec 7; norm_num [h8, h9] at h; generalize a 10 = x at h ⊢; omega
  have h11 : a 11 = 30027445848 := by
    have h := a_rec 8; norm_num [h9, h10] at h; generalize a 11 = x at h ⊢; omega
  have h12 : a 12 = 248474628648 := by
    have h := a_rec 9; norm_num [h10, h11] at h; generalize a 12 = x at h ⊢; omega
  have h13 : a 13 = 2056106982744 := by
    have h := a_rec 10; norm_num [h11, h12] at h; generalize a 13 = x at h ⊢; omega
  have h14 : a 14 = 17014115072808 := by
    have h := a_rec 11; norm_num [h12, h13] at h; generalize a 14 = x at h ⊢; omega
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 24x(1 - 2x)/(1 - 9x + 6x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 9 * X + 6 * X ^ 2) = 24 * X * (1 - 2 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 9 * X + 6 * X ^ 2) = A - C (9 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2) := by
    rw [show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6]
    ring
  have e2 : (24 : ℚ⟦X⟧) * X * (1 - 2 * X) = C (24 : ℚ) * X ^ 1 - C (48 : ℚ) * X ^ 2 := by
    rw [show (C (24 : ℚ) : ℚ⟦X⟧) = 24 from map_ofNat C 24,
      show (C (48 : ℚ) : ℚ⟦X⟧) = 48 from map_ofNat C 48]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> simp [a_one, a_two] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have h' : (a (m + 3) : ℚ) + 6 * a (m + 1) = 9 * a (m + 2) := by
      exact_mod_cast a_rec m
    simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
      show ¬ m + 3 = 0 by omega, show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega,
      show 1 ≤ m + 3 by omega, show 2 ≤ m + 3 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (2 : ℝ) ^ ((2 : ℝ) - n) * ((9 - Real.sqrt 57) ^ n * (3 + Real.sqrt 57) +
      (-3 + Real.sqrt 57) * (9 + Real.sqrt 57) ^ n) / Real.sqrt 57 := by
  have s57 : Real.sqrt 57 ^ 2 = 57 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 57 := Real.sqrt_pos.2 (by norm_num)
  have hrp : ∀ n : ℕ, (2 : ℝ) ^ ((2 : ℝ) - n) * ((9 - Real.sqrt 57) ^ n * (3 + Real.sqrt 57) +
      (-3 + Real.sqrt 57) * (9 + Real.sqrt 57) ^ n) =
      4 * (((9 - Real.sqrt 57) / 2) ^ n * (3 + Real.sqrt 57) +
        (-3 + Real.sqrt 57) * ((9 + Real.sqrt 57) / 2) ^ n) := by
    intro n
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.rpow_two, div_pow, div_pow]
    have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp
    ring
  set s := Real.sqrt 57 with hs
  set H : ℕ → ℝ := fun n =>
    4 * (((9 - s) / 2) ^ n * (3 + s) + (-3 + s) * ((9 + s) / 2) ^ n) with hH
  have H1 : H 1 = 24 * s := by
    simp only [hH]
    ring
  have H2 : H 2 = 168 * s := by
    simp only [hH]
    linear_combination (2 * s) * s57
  have r1 : ∀ m : ℕ, ((9 - s) / 2) ^ (m + 3) =
      9 * ((9 - s) / 2) ^ (m + 2) - 6 * ((9 - s) / 2) ^ (m + 1) := by
    intro m
    have : ((9 - s) / 2) ^ 2 = 9 * ((9 - s) / 2) - 6 := by
      linear_combination (1 / 4) * s57
    calc ((9 - s) / 2) ^ (m + 3) = ((9 - s) / 2) ^ (m + 1) * ((9 - s) / 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have r2 : ∀ m : ℕ, ((9 + s) / 2) ^ (m + 3) =
      9 * ((9 + s) / 2) ^ (m + 2) - 6 * ((9 + s) / 2) ^ (m + 1) := by
    intro m
    have : ((9 + s) / 2) ^ 2 = 9 * ((9 + s) / 2) - 6 := by
      linear_combination (1 / 4) * s57
    calc ((9 + s) / 2) ^ (m + 3) = ((9 + s) / 2) ^ (m + 1) * ((9 + s) / 2) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have Hrec : ∀ m, H (m + 3) = 9 * H (m + 2) - 6 * H (m + 1) := by
    intro m
    simp only [hH]
    rw [r1, r2]
    ring
  have key : ∀ m, (a (m + 1) : ℝ) * s = H (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | _ | m
      · rw [a_one, H1]; norm_num
      · rw [a_two, H2]; norm_num
      · have h' : (a (m + 3) : ℝ) + 6 * a (m + 1) = 9 * a (m + 2) := by
          exact_mod_cast a_rec m
        have e1 : (a (m + 1) : ℝ) * s = H (m + 1) := ih m (by omega)
        have e2 : (a (m + 2) : ℝ) * s = H (m + 2) := ih (m + 1) (by omega)
        show (a (m + 3) : ℝ) * s = H (m + 3)
        rw [Hrec m, ← e1, ← e2]
        linear_combination s * h'
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [hrp, eq_div_iff hpos.ne', key k]

/-- Both of Barker's conjectures. -/
theorem conjecture : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 9 * X + 6 * X ^ 2) = 24 * X * (1 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 : ℝ) ^ ((2 : ℝ) - n) * ((9 - Real.sqrt 57) ^ n * (3 + Real.sqrt 57) +
        (-3 + Real.sqrt 57) * (9 + Real.sqrt 57) ^ n) / Real.sqrt 57 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223291

theorem OMA.solution : type_of% @OMA.S_oeis_a223291.main :=
  OMA.S_oeis_a223291.conjecture
