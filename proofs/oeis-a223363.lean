import OMAStatements.S_oeis_a223363

namespace OMA.S_oeis_a223363

open PowerSeries Finset





/-- The condition on an array used in `a`. -/
def Valid {n : ℕ} (f : Fin n → Fin 21) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → adj (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → Fin 21)).filter Valid).card := by
  unfold a Valid
  rfl

/-- W(n, x): valid arrays of length n + 1 whose first entry is x. -/
def W (n : ℕ) (x : Fin 21) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 21)).filter (fun f => Valid f ∧ f 0 = x)).card

lemma valid_cons {n : ℕ} (x : Fin 21) (g : Fin (n + 1) → Fin 21) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 21) ↔ adj x (g 0) ∧ Valid g := by
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ x : Fin 21, W n x := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (x : Fin 21) : W 0 x = 1 := by
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
def consEmb (n : ℕ) (x : Fin 21) : (Fin (n + 1) → Fin 21) ↪ (Fin (n + 2) → Fin 21) where
  toFun g := Fin.cons x g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (x : Fin 21) (g : Fin (n + 1) → Fin 21) :
    consEmb n x g = Fin.cons x g := rfl

lemma W_succ (n : ℕ) (x : Fin 21) :
    W (n + 1) x = ∑ y : Fin 21, if adj x y then W n y else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 21)).filter (fun f => Valid f ∧ f 0 = x)) =
      (((univ : Finset (Fin (n + 1) → Fin 21)).filter (fun g => adj x (g 0) ∧ Valid g)).map
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

/-- A 1, A^2 1 and A^3 1. -/
def d1 : Fin 21 → ℕ := ![2, 4, 4, 4, 6, 4, 4, 6, 6, 4, 4, 6, 6, 6, 4, 2, 4, 4, 4, 4, 2]

def d2 : Fin 21 → ℕ :=
  ![8, 16, 16, 20, 28, 20, 20, 32, 32, 20, 16, 28, 32, 28, 16, 8, 16, 20, 20, 16, 8]

def d3 : Fin 21 → ℕ :=
  ![32, 72, 72, 96, 136, 96, 96, 160, 160, 96, 72, 136, 160, 136, 72, 32, 72, 96, 96, 72, 32]

lemma W_one (x : Fin 21) : W 1 x = d1 x := by
  rw [W_succ]
  simp only [W_zero]
  revert x
  decide

lemma W_two (x : Fin 21) : W 2 x = d2 x := by
  rw [W_succ]
  simp only [W_one]
  revert x
  decide

lemma W_three (x : Fin 21) : W 3 x = d3 x := by
  rw [W_succ]
  simp only [W_two]
  revert x
  decide

lemma W_rec (n : ℕ) (x : Fin 21) :
    W (n + 3) x + 4 * W (n + 1) x + 8 * W n x = 6 * W (n + 2) x := by
  induction n generalizing x with
  | zero =>
    rw [W_three, W_two, W_one, W_zero]
    revert x
    decide
  | succ n ih =>
    rw [W_succ (n + 3), W_succ (n + 1), W_succ n, W_succ (n + 2)]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    split_ifs
    · exact ih y
    · simp

lemma a_rec (n : ℕ) : a (n + 4) + 4 * a (n + 2) + 8 * a (n + 1) = 6 * a (n + 3) := by
  rw [a_succ, a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => W_rec n x)

lemma a_one : a 1 = 21 := by
  rw [a_succ]
  simp [W_zero]

lemma a_two : a 2 = 90 := by
  rw [a_succ]
  simp only [W_one]
  decide

lemma a_three : a 3 = 420 := by
  rw [a_succ]
  simp only [W_two]
  decide

/-- Controls: the entry's data a(1..16). -/
theorem controls : a 1 = 21 ∧ a 2 = 90 ∧ a 3 = 420 ∧ a 4 = 1992 ∧ a 5 = 9552 ∧ a 6 = 45984 ∧
    a 7 = 221760 ∧ a 8 = 1070208 ∧ a 9 = 5166336 ∧ a 10 = 24943104 ∧ a 11 = 120431616 ∧
    a 12 = 581486592 ∧ a 13 = 2807648256 ∧ a 14 = 13556490240 ∧ a 15 = 65456455680 ∧
    a 16 = 316051587072 := by
  have h1 := a_one
  have h2 := a_two
  have h3 := a_three
  have h4 : a 4 = 1992 := by
    have h := a_rec 0; norm_num [h1, h2, h3] at h; generalize a 4 = x at h ⊢; omega
  have h5 : a 5 = 9552 := by
    have h := a_rec 1; norm_num [h2, h3, h4] at h; generalize a 5 = x at h ⊢; omega
  have h6 : a 6 = 45984 := by
    have h := a_rec 2; norm_num [h3, h4, h5] at h; generalize a 6 = x at h ⊢; omega
  have h7 : a 7 = 221760 := by
    have h := a_rec 3; norm_num [h4, h5, h6] at h; generalize a 7 = x at h ⊢; omega
  have h8 : a 8 = 1070208 := by
    have h := a_rec 4; norm_num [h5, h6, h7] at h; generalize a 8 = x at h ⊢; omega
  have h9 : a 9 = 5166336 := by
    have h := a_rec 5; norm_num [h6, h7, h8] at h; generalize a 9 = x at h ⊢; omega
  have h10 : a 10 = 24943104 := by
    have h := a_rec 6; norm_num [h7, h8, h9] at h; generalize a 10 = x at h ⊢; omega
  have h11 : a 11 = 120431616 := by
    have h := a_rec 7; norm_num [h8, h9, h10] at h; generalize a 11 = x at h ⊢; omega
  have h12 : a 12 = 581486592 := by
    have h := a_rec 8; norm_num [h9, h10, h11] at h; generalize a 12 = x at h ⊢; omega
  have h13 : a 13 = 2807648256 := by
    have h := a_rec 9; norm_num [h10, h11, h12] at h; generalize a 13 = x at h ⊢; omega
  have h14 : a 14 = 13556490240 := by
    have h := a_rec 10; norm_num [h11, h12, h13] at h; generalize a 14 = x at h ⊢; omega
  have h15 : a 15 = 65456455680 := by
    have h := a_rec 11; norm_num [h12, h13, h14] at h; generalize a 15 = x at h ⊢; omega
  have h16 : a 16 = 316051587072 := by
    have h := a_rec 12; norm_num [h13, h14, h15] at h; generalize a 16 = x at h ⊢; omega
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 3x(7 - 12x - 12x^2)/((1 - 2x)(1 - 4x - 4x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 4 * X - 4 * X ^ 2)) = 3 * X * (7 - 12 * X - 12 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - 2 * X) * (1 - 4 * X - 4 * X ^ 2)) =
      A - C (6 : ℚ) * (A * X ^ 1) + C (4 : ℚ) * (A * X ^ 2) + C (8 : ℚ) * (A * X ^ 3) := by
    rw [show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6,
      show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4,
      show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8]
    ring
  have e2 : (3 : ℚ⟦X⟧) * X * (7 - 12 * X - 12 * X ^ 2) =
      C (21 : ℚ) * X ^ 1 - C (36 : ℚ) * X ^ 2 - C (36 : ℚ) * X ^ 3 := by
    rw [show (C (21 : ℚ) : ℚ⟦X⟧) = 21 from map_ofNat C 21,
      show (C (36 : ℚ) : ℚ⟦X⟧) = 36 from map_ofNat C 36]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> simp [a_one, a_two, a_three] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h' : (a (m + 4) : ℚ) + 4 * a (m + 2) + 8 * a (m + 1) = 6 * a (m + 3) := by
      exact_mod_cast a_rec m
    simp only [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, show 1 ≤ m + 4 by omega,
      show 2 ≤ m + 4 by omega, show 3 ≤ m + 4 by omega, show ¬ m + 4 = 1 by omega,
      show ¬ m + 4 = 2 by omega, show ¬ m + 4 = 3 by omega, if_true, if_false]
    linear_combination h'

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
    (3 / 2) * (2 ^ n - (2 - 2 * Real.sqrt 2) ^ n * (-1 + Real.sqrt 2) +
      (2 : ℝ) ^ ((1 : ℝ) / 2 + n) * (1 + Real.sqrt 2) ^ n + (2 * (1 + Real.sqrt 2)) ^ n) := by
  have s2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrp : ∀ n : ℕ, (2 : ℝ) ^ ((1 : ℝ) / 2 + n) * (1 + Real.sqrt 2) ^ n =
      Real.sqrt 2 * (2 * (1 + Real.sqrt 2)) ^ n := by
    intro n
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, ← Real.sqrt_eq_rpow, mul_pow]
    ring
  set s := Real.sqrt 2 with hs
  set F : ℕ → ℝ := fun n =>
    (3 / 2) * (2 ^ n - (2 - 2 * s) ^ n * (-1 + s) + s * (2 * (1 + s)) ^ n + (2 * (1 + s)) ^ n)
    with hF
  have F1 : F 1 = 21 := by
    simp only [hF]
    linear_combination 6 * s2
  have F2 : F 2 = 90 := by
    simp only [hF]
    linear_combination 36 * s2
  have F3 : F 3 = 420 := by
    simp only [hF]
    linear_combination (192 + 24 * s ^ 2) * s2
  have r1 : ∀ m : ℕ, (2 - 2 * s) ^ (m + 4) =
      6 * (2 - 2 * s) ^ (m + 3) - 4 * (2 - 2 * s) ^ (m + 2) - 8 * (2 - 2 * s) ^ (m + 1) := by
    intro m
    have : (2 - 2 * s) ^ 3 = 6 * (2 - 2 * s) ^ 2 - 4 * (2 - 2 * s) - 8 := by
      linear_combination (-8 * s) * s2
    calc (2 - 2 * s) ^ (m + 4) = (2 - 2 * s) ^ (m + 1) * (2 - 2 * s) ^ 3 := by ring
      _ = _ := by rw [this]; ring
  have r2 : ∀ m : ℕ, (2 * (1 + s)) ^ (m + 4) =
      6 * (2 * (1 + s)) ^ (m + 3) - 4 * (2 * (1 + s)) ^ (m + 2) -
        8 * (2 * (1 + s)) ^ (m + 1) := by
    intro m
    have : (2 * (1 + s)) ^ 3 = 6 * (2 * (1 + s)) ^ 2 - 4 * (2 * (1 + s)) - 8 := by
      linear_combination (8 * s) * s2
    calc (2 * (1 + s)) ^ (m + 4) = (2 * (1 + s)) ^ (m + 1) * (2 * (1 + s)) ^ 3 := by ring
      _ = _ := by rw [this]; ring
  have r3 : ∀ m : ℕ, (2 : ℝ) ^ (m + 4) =
      6 * 2 ^ (m + 3) - 4 * 2 ^ (m + 2) - 8 * 2 ^ (m + 1) := by
    intro m
    ring
  have Frec : ∀ m, F (m + 4) = 6 * F (m + 3) - 4 * F (m + 2) - 8 * F (m + 1) := by
    intro m
    simp only [hF]
    rw [r1, r2, r3]
    ring
  have key : ∀ m, (a (m + 1) : ℝ) = F (m + 1) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | _ | _ | m
      · rw [a_one, F1]; norm_num
      · rw [a_two, F2]; norm_num
      · rw [a_three, F3]; norm_num
      · have h' : (a (m + 4) : ℝ) + 4 * a (m + 2) + 8 * a (m + 1) = 6 * a (m + 3) := by
          exact_mod_cast a_rec m
        have e1 : (a (m + 1) : ℝ) = F (m + 1) := ih m (by omega)
        have e2 : (a (m + 2) : ℝ) = F (m + 2) := ih (m + 1) (by omega)
        have e3 : (a (m + 3) : ℝ) = F (m + 3) := ih (m + 2) (by omega)
        show (a (m + 4) : ℝ) = F (m + 4)
        rw [Frec m, ← e1, ← e2, ← e3]
        linear_combination h'
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [key k, hrp]

/-- Both of Barker's conjectures. -/
theorem conjecture : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - 2 * X) * (1 - 4 * X - 4 * X ^ 2)) = 3 * X * (7 - 12 * X - 12 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (3 / 2) * (2 ^ n - (2 - 2 * Real.sqrt 2) ^ n * (-1 + Real.sqrt 2) +
        (2 : ℝ) ^ ((1 : ℝ) / 2 + n) * (1 + Real.sqrt 2) ^ n + (2 * (1 + Real.sqrt 2)) ^ n) :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223363

theorem OMA.solution : type_of% @OMA.S_oeis_a223363.main :=
  OMA.S_oeis_a223363.conjecture
