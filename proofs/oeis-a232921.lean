import OMAStatements.S_oeis_a232921

namespace OMA.S_oeis_a232921

open PowerSeries Finset




/-- The condition on an array used in `a`. -/
def Valid {n : ℕ} (f : Fin n → Fin 3 × Fin 3) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → Fin 3 × Fin 3)).filter Valid).card := by
  unfold a Valid
  rfl

/-- W(n, c): valid arrays with n + 1 columns whose first column is c. -/
def W (n : ℕ) (c : Fin 3 × Fin 3) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 3 × Fin 3)).filter (fun f => Valid f ∧ f 0 = c)).card

lemma valid_cons {n : ℕ} (x : Fin 3 × Fin 3) (g : Fin (n + 1) → Fin 3 × Fin 3) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 3 × Fin 3) ↔ ok x (g 0) ∧ Valid g := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h 0 1 (by simp)
      simpa using this
    · intro i j hij
      have := h i.succ j.succ (by simp [hij])
      simpa using this
  · rintro ⟨h0, hg⟩ i j hij
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ c : Fin 3 × Fin 3, W n c := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (c : Fin 3 × Fin 3) : W 0 c = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => c, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hf⟩
    funext i
    rw [Fin.fin_one_eq_zero i, hf]
  · rintro rfl
    refine ⟨?_, rfl⟩
    intro i j hij
    have := j.isLt
    omega

/-- Prepending the column c to an array with n + 1 columns. -/
def consEmb (n : ℕ) (c : Fin 3 × Fin 3) :
    (Fin (n + 1) → Fin 3 × Fin 3) ↪ (Fin (n + 2) → Fin 3 × Fin 3) where
  toFun g := Fin.cons c g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (c : Fin 3 × Fin 3) (g : Fin (n + 1) → Fin 3 × Fin 3) :
    consEmb n c g = Fin.cons c g := rfl

lemma W_succ (n : ℕ) (c : Fin 3 × Fin 3) :
    W (n + 1) c = ∑ d : Fin 3 × Fin 3, if ok c d then W n d else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 3 × Fin 3)).filter (fun f => Valid f ∧ f 0 = c)) =
      (((univ : Finset (Fin (n + 1) → Fin 3 × Fin 3)).filter (fun g => ok c (g 0) ∧ Valid g)).map
        (consEmb n c)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, consEmb_apply]
    constructor
    · rintro ⟨hv, h0⟩
      refine ⟨Fin.tail f, ?_, ?_⟩
      · have hf : f = Fin.cons c (Fin.tail f) := by
          rw [← h0]; exact (Fin.cons_self_tail f).symm
        rw [hf, valid_cons] at hv
        exact hv
      · rw [← h0]; exact Fin.cons_self_tail f
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(valid_cons c g).2 hg, by simp⟩
  unfold W
  rw [e, Finset.card_map]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  split_ifs with hcd
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hcd, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hok, _⟩, h0⟩
    exact hcd (h0 ▸ hok)

lemma W_rec (n : ℕ) (c : Fin 3 × Fin 3) : W (n + 2) c = 2 * W (n + 1) c + 2 * W n c := by
  induction n generalizing c with
  | zero =>
    rw [W_succ, W_succ]
    simp only [W_succ, W_zero]
    revert c
    decide
  | succ n ih =>
    rw [W_succ (n + 2), W_succ (n + 1), W_succ n]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    split_ifs
    · exact ih d
    · simp

lemma a_rec (n : ℕ) : a (n + 3) = 2 * a (n + 2) + 2 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => W_rec n c)

lemma a_one : a 1 = 9 := by
  rw [a_succ]
  simp [W_zero]

lemma a_two : a 2 = 18 := by
  rw [a_succ]
  simp only [W_succ, W_zero]
  decide

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 9x/(1 - 2x - 2x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X - 2 * X ^ 2) =
    9 * X := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 2 * X - 2 * X ^ 2) = A - A * X ^ 1 * C 2 - A * X ^ 2 * C 2 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm]
    ring
  have e2 : (9 : ℚ⟦X⟧) * X = X ^ 1 * C 9 := by
    rw [show (9 : ℚ⟦X⟧) = C 9 from (map_ofNat C 9).symm]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two]
    norm_num
  · have h := a_rec n
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega,
      show ¬ (n + 3 - 2 = 0) by omega, if_false, show 1 ≤ n + 3 by omega,
      show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show n + 3 - 1 = n + 2 by omega, show n + 3 - 2 = n + 1 by omega]
    rw [h]
    push_cast
    ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (-3) * (Real.sqrt 3 * ((1 - Real.sqrt 3) ^ n - (1 + Real.sqrt 3) ^ n)) / 2 := by
  have s3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  set F : ℕ → ℝ := fun n =>
    (-3) * (Real.sqrt 3 * ((1 - Real.sqrt 3) ^ n - (1 + Real.sqrt 3) ^ n)) / 2 with hF
  have F1 : F 1 = 9 := by
    simp only [hF]
    nlinarith [s3]
  have F2 : F 2 = 18 := by
    simp only [hF]
    nlinarith [s3]
  have Frec : ∀ n, F (n + 3) = 2 * F (n + 2) + 2 * F (n + 1) := by
    intro n
    simp only [hF]
    have r1 : (1 - Real.sqrt 3) ^ (n + 3) =
        2 * (1 - Real.sqrt 3) ^ (n + 2) + 2 * (1 - Real.sqrt 3) ^ (n + 1) := by
      have : (1 - Real.sqrt 3) ^ 2 = 2 * (1 - Real.sqrt 3) + 2 := by nlinarith [s3]
      calc (1 - Real.sqrt 3) ^ (n + 3) = (1 - Real.sqrt 3) ^ (n + 1) * (1 - Real.sqrt 3) ^ 2 := by
            ring
        _ = _ := by rw [this]; ring
    have r2 : (1 + Real.sqrt 3) ^ (n + 3) =
        2 * (1 + Real.sqrt 3) ^ (n + 2) + 2 * (1 + Real.sqrt 3) ^ (n + 1) := by
      have : (1 + Real.sqrt 3) ^ 2 = 2 * (1 + Real.sqrt 3) + 2 := by nlinarith [s3]
      calc (1 + Real.sqrt 3) ^ (n + 3) = (1 + Real.sqrt 3) ^ (n + 1) * (1 + Real.sqrt 3) ^ 2 := by
            ring
        _ = _ := by rw [this]; ring
    rw [r1, r2]
    ring
  have key : ∀ n, (a (n + 1) : ℝ) = F (n + 1) ∧ (a (n + 2) : ℝ) = F (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨by rw [a_one, F1]; norm_num, by rw [a_two, F2]; norm_num⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 2 = n + 3 by omega, a_rec, Frec]
      push_cast
      rw [ih.1, ih.2]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X - 2 * X ^ 2) =
      9 * X ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (-3) * (Real.sqrt 3 * ((1 - Real.sqrt 3) ^ n - (1 + Real.sqrt 3) ^ n)) / 2 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a232921

theorem OMA.solution : type_of% @OMA.S_oeis_a232921.main :=
  OMA.S_oeis_a232921.conjecture
