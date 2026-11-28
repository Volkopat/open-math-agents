import OMAStatements.S_oeis_a223211

namespace OMA.S_oeis_a223211

open PowerSeries Finset





/-- The condition on an array used in `a`. -/
def Valid {n : ℕ} (f : Fin n → Fin 6) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → adj (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → Fin 6)).filter Valid).card := by
  unfold a Valid
  rfl

/-- W(n, x): valid arrays of length n + 1 whose first entry is x. -/
def W (n : ℕ) (x : Fin 6) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 6)).filter (fun f => Valid f ∧ f 0 = x)).card

lemma valid_cons {n : ℕ} (x : Fin 6) (g : Fin (n + 1) → Fin 6) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 6) ↔ adj x (g 0) ∧ Valid g := by
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ x : Fin 6, W n x := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (x : Fin 6) : W 0 x = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => x, ?_⟩
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

/-- Prepending x to an array of length n + 1. -/
def consEmb (n : ℕ) (x : Fin 6) : (Fin (n + 1) → Fin 6) ↪ (Fin (n + 2) → Fin 6) where
  toFun g := Fin.cons x g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (x : Fin 6) (g : Fin (n + 1) → Fin 6) :
    consEmb n x g = Fin.cons x g := rfl

lemma W_succ (n : ℕ) (x : Fin 6) :
    W (n + 1) x = ∑ y : Fin 6, if adj x y then W n y else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 6)).filter (fun f => Valid f ∧ f 0 = x)) =
      (((univ : Finset (Fin (n + 1) → Fin 6)).filter (fun g => adj x (g 0) ∧ Valid g)).map
        (consEmb n x)) := by
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
    · rintro ⟨⟨_, hg⟩, h0⟩
      exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩
      exact ⟨⟨h0 ▸ hxy, hg⟩, h0⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨⟨hadj, _⟩, h0⟩
    exact hxy (h0 ▸ hadj)

lemma W_rec (n : ℕ) (x : Fin 6) : W (n + 2) x = 2 * W (n + 1) x + 4 * W n x := by
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

lemma a_rec (n : ℕ) : a (n + 3) = 2 * a (n + 2) + 4 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => W_rec n x)

lemma a_one : a 1 = 6 := by
  rw [a_succ]
  simp [W_zero]

lemma a_two : a 2 = 18 := by
  rw [a_succ]
  simp only [W_succ, W_zero]
  decide

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 6x(1 + x)/(1 - 2x - 4x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X - 4 * X ^ 2) =
    6 * X * (1 + X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 2 * X - 4 * X ^ 2) = A - A * X ^ 1 * C 2 - A * X ^ 2 * C 4 := by
    rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm,
      show (4 : ℚ⟦X⟧) = C 4 from (map_ofNat C 4).symm]
    ring
  have e2 : (6 : ℚ⟦X⟧) * X * (1 + X) = X ^ 1 * C 6 + X ^ 2 * C 6 := by
    rw [show (6 : ℚ⟦X⟧) = C 6 from (map_ofNat C 6).symm]
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
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega,
      show ¬ (n + 3 - 2 = 0) by omega, if_false, show 1 ≤ n + 3 by omega,
      show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega]
    rw [h]
    push_cast
    ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    3 * ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5)) /
      (4 * Real.sqrt 5) := by
  have s5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  set F : ℕ → ℝ := fun n =>
    3 * ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5)) /
      (4 * Real.sqrt 5) with hF
  have F1 : F 1 = 6 := by
    simp only [hF]
    field_simp
    nlinarith [s5]
  have F2 : F 2 = 18 := by
    simp only [hF]
    field_simp
    nlinarith [s5]
  have Frec : ∀ n, F (n + 3) = 2 * F (n + 2) + 4 * F (n + 1) := by
    intro n
    simp only [hF]
    have r1 : (1 - Real.sqrt 5) ^ (n + 3) =
        2 * (1 - Real.sqrt 5) ^ (n + 2) + 4 * (1 - Real.sqrt 5) ^ (n + 1) := by
      have : (1 - Real.sqrt 5) ^ 2 = 2 * (1 - Real.sqrt 5) + 4 := by nlinarith [s5]
      calc (1 - Real.sqrt 5) ^ (n + 3) = (1 - Real.sqrt 5) ^ (n + 1) * (1 - Real.sqrt 5) ^ 2 := by
            ring
        _ = _ := by rw [this]; ring
    have r2 : (1 + Real.sqrt 5) ^ (n + 3) =
        2 * (1 + Real.sqrt 5) ^ (n + 2) + 4 * (1 + Real.sqrt 5) ^ (n + 1) := by
      have : (1 + Real.sqrt 5) ^ 2 = 2 * (1 + Real.sqrt 5) + 4 := by nlinarith [s5]
      calc (1 + Real.sqrt 5) ^ (n + 3) = (1 + Real.sqrt 5) ^ (n + 1) * (1 + Real.sqrt 5) ^ 2 := by
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
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 2 * X - 4 * X ^ 2) =
      6 * X * (1 + X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      3 * ((1 - Real.sqrt 5) ^ n * (-3 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ n * (3 + Real.sqrt 5)) /
        (4 * Real.sqrt 5) :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223211

theorem OMA.solution : type_of% @OMA.S_oeis_a223211.main :=
  OMA.S_oeis_a223211.conjecture
