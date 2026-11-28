import OMAStatements.S_oeis_a221619

namespace OMA.S_oeis_a221619

open PowerSeries Finset



/-- The condition on an array used in `a`. -/
def Valid {n : ℕ} (f : Fin n → Equiv.Perm (Fin 4)) : Prop :=
  ∀ i j : Fin n, j.val = i.val + 1 → des (f i) ≤ des (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

lemma a_eq (n : ℕ) :
    a n = ((univ : Finset (Fin n → Equiv.Perm (Fin 4))).filter Valid).card := by
  unfold a Valid
  rfl

/-- W(n, p): valid arrays with n + 1 rows whose first row is p. -/
def W (n : ℕ) (p : Equiv.Perm (Fin 4)) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Equiv.Perm (Fin 4))).filter (fun f => Valid f ∧ f 0 = p)).card

lemma valid_cons {n : ℕ} (x : Equiv.Perm (Fin 4)) (g : Fin (n + 1) → Equiv.Perm (Fin 4)) :
    Valid (Fin.cons x g : Fin (n + 2) → Equiv.Perm (Fin 4)) ↔ des x ≤ des (g 0) ∧ Valid g := by
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ p : Equiv.Perm (Fin 4), W n p := by
  rw [a_eq]
  unfold W
  rw [Finset.card_eq_sum_card_fiberwise (f := fun f => f 0) (t := univ) (by simp)]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  ext f
  simp

lemma W_zero (p : Equiv.Perm (Fin 4)) : W 0 p = 1 := by
  unfold W
  rw [Finset.card_eq_one]
  refine ⟨fun _ => p, ?_⟩
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

/-- Prepending a row to an array with n + 1 rows. -/
def consEmb (n : ℕ) (x : Equiv.Perm (Fin 4)) :
    (Fin (n + 1) → Equiv.Perm (Fin 4)) ↪ (Fin (n + 2) → Equiv.Perm (Fin 4)) where
  toFun g := Fin.cons x g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (x : Equiv.Perm (Fin 4)) (g : Fin (n + 1) → Equiv.Perm (Fin 4)) :
    consEmb n x g = Fin.cons x g := rfl

lemma W_succ (n : ℕ) (x : Equiv.Perm (Fin 4)) :
    W (n + 1) x = ∑ y : Equiv.Perm (Fin 4), if des x ≤ des y then W n y else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Equiv.Perm (Fin 4))).filter
      (fun f => Valid f ∧ f 0 = x)) =
      (((univ : Finset (Fin (n + 1) → Equiv.Perm (Fin 4))).filter
        (fun g => des x ≤ des (g 0) ∧ Valid g)).map (consEmb n x)) := by
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
    rintro ⟨⟨hle, _⟩, h0⟩
    exact hxy (h0 ▸ hle)

/-- Eulerian numbers for four letters. -/
def w : ℕ → ℤ
  | 0 => 1
  | 1 => 11
  | 2 => 11
  | _ => 1

lemma des_lt (q : Equiv.Perm (Fin 4)) : des q < 4 := by
  unfold des
  have := Finset.card_le_univ
    ((Finset.univ : Finset (Fin 3)).filter (fun i => q i.succ < q i.castSucc))
  simp only [Fintype.card_fin] at this
  omega

lemma E_card (d : ℕ) (hd : d < 4) :
    (((univ : Finset (Equiv.Perm (Fin 4))).filter (fun q => des q = d)).card : ℤ) = w d := by
  interval_cases d <;> decide

lemma sum_by_des (F : ℕ → ℤ) :
    ∑ q : Equiv.Perm (Fin 4), F (des q) = ∑ d ∈ Finset.range 4, w d * F d := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := Finset.range 4) (g := des)
    (fun q _ => by simpa using des_lt q)]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have h : ∀ q ∈ (univ : Finset (Equiv.Perm (Fin 4))).filter (fun q => des q = d),
      F (des q) = F d := fun q hq => by rw [(Finset.mem_filter.1 hq).2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, E_card d (by simpa using hd)]

/-- The reduced recursion on the number of descents of the first row. -/
def V : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n + 1, d => ∑ d' ∈ Finset.range 4, w d' * (if d ≤ d' then V n d' else 0)

lemma V_succ (n d : ℕ) :
    V (n + 1) d = ∑ d' ∈ Finset.range 4, w d' * (if d ≤ d' then V n d' else 0) := rfl

lemma W_eq_V (n : ℕ) (p : Equiv.Perm (Fin 4)) : (W n p : ℤ) = V n (des p) := by
  induction n generalizing p with
  | zero => rw [W_zero]; rfl
  | succ n ih =>
    rw [W_succ, V_succ]
    push_cast
    have h : ∀ q : Equiv.Perm (Fin 4),
        (if des p ≤ des q then (W n q : ℤ) else 0) =
          (fun d => if des p ≤ d then V n d else 0) (des q) := fun q => by
      simp only [ih q]
    rw [Finset.sum_congr rfl (fun q _ => h q)]
    exact sum_by_des (fun d => if des p ≤ d then V n d else 0)

lemma a_V (n : ℕ) : (a (n + 1) : ℤ) = ∑ d ∈ Finset.range 4, w d * V n d := by
  rw [a_succ]
  push_cast
  rw [Finset.sum_congr rfl (fun q _ => W_eq_V n q), sum_by_des (V n)]

lemma V_rec (n d : ℕ) (hd : d < 4) :
    V (n + 4) d = 24 * V (n + 3) d - 166 * V (n + 2) d + 264 * V (n + 1) d - 121 * V n d := by
  induction n generalizing d with
  | zero => interval_cases d <;> decide
  | succ n ih =>
    rw [show n + 1 + 4 = (n + 4) + 1 by omega, show n + 1 + 3 = (n + 3) + 1 by omega,
      show n + 1 + 2 = (n + 2) + 1 by omega, V_succ (n + 4), V_succ (n + 3), V_succ (n + 2),
      V_succ (n + 1), V_succ n]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [ih 0 (by norm_num), ih 1 (by norm_num), ih 2 (by norm_num), ih 3 (by norm_num)]
    split_ifs <;> ring

lemma a_rec (n : ℕ) :
    (a (n + 5) : ℤ) = 24 * a (n + 4) - 166 * a (n + 3) + 264 * a (n + 2) - 121 * a (n + 1) := by
  rw [a_V (n + 4), a_V (n + 3), a_V (n + 2), a_V (n + 1), a_V n]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [V_rec n 0 (by norm_num), V_rec n 1 (by norm_num), V_rec n 2 (by norm_num),
    V_rec n 3 (by norm_num)]
  ring

lemma values : (a 1 : ℤ) = 24 ∧ (a 2 : ℤ) = 410 ∧ (a 3 : ℤ) = 6120 ∧ (a 4 : ℤ) = 85035 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [a_V 0]; decide
  · rw [a_V 1]; decide
  · rw [a_V 2]; decide
  · rw [a_V 3]; decide

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(12 - 11x)(2 - 12x + 11x^2)/((1 - x)^2(1 - 11x)^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
    ((1 - X) ^ 2 * (1 - 11 * X) ^ 2) = X * (12 - 11 * X) * (2 - 12 * X + 11 * X ^ 2) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have e1 : A * ((1 - X) ^ 2 * (1 - 11 * X) ^ 2) =
      A - C 24 * (A * X ^ 1) + C 166 * (A * X ^ 2) - C 264 * (A * X ^ 3) +
        C 121 * (A * X ^ 4) := by
    simp only [map_ofNat]
    ring
  have e2 : (X : ℤ⟦X⟧) * (12 - 11 * X) * (2 - 12 * X + 11 * X ^ 2) =
      X ^ 1 * C 24 - X ^ 2 * C 166 + X ^ 3 * C 264 - X ^ 4 * C 121 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  obtain ⟨v1, v2, v3, v4⟩ := values
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have h := a_rec m
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega,
      show ¬ m + 5 = 0 by omega, show ¬ m + 4 = 0 by omega, show ¬ m + 3 = 0 by omega,
      show ¬ m + 2 = 0 by omega, show ¬ m + 1 = 0 by omega, show 4 ≤ m + 5 by omega,
      show 3 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 1 ≤ m + 5 by omega,
      show ¬ m + 5 = 4 by omega, show ¬ m + 5 = 3 by omega, show ¬ m + 5 = 2 by omega,
      show ¬ m + 5 = 1 by omega, if_true, if_false]
    rw [h]
    ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n →
    (a n : ℚ) = (4 * (4 + 11 ^ (2 + n)) + 5 * (1 + 11 ^ (2 + n)) * n) / 500 := by
  set F : ℕ → ℚ := fun n => (4 * (4 + 11 ^ (2 + n)) + 5 * (1 + 11 ^ (2 + n)) * n) / 500 with hF
  have Frec : ∀ n, F (n + 5) = 24 * F (n + 4) - 166 * F (n + 3) + 264 * F (n + 2) -
      121 * F (n + 1) := by
    intro n
    simp only [hF]
    push_cast
    ring
  obtain ⟨v1, v2, v3, v4⟩ := values
  have key : ∀ n, (a (n + 1) : ℚ) = F (n + 1) ∧ (a (n + 2) : ℚ) = F (n + 2) ∧
      (a (n + 3) : ℚ) = F (n + 3) ∧ (a (n + 4) : ℚ) = F (n + 4) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [hF] <;> norm_num
      · exact_mod_cast v1
      · exact_mod_cast v2
      · exact_mod_cast v3
      · exact_mod_cast v4
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨h2, h3, h4, ?_⟩
      rw [show n + 1 + 4 = n + 5 by omega, Frec n]
      have hr : (a (n + 5) : ℚ) = 24 * a (n + 4) - 166 * a (n + 3) + 264 * a (n + 2) -
          121 * a (n + 1) := by exact_mod_cast a_rec n
      rw [hr, h1, h2, h3, h4]
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (key k).1

/-- Controls: a(1..4) = 24, 410, 6120, 85035 by the reduced recursion (the entry's data); and the
Eulerian numbers 1, 11, 11, 1 by enumeration of the 24 rows. -/
theorem controls : a 1 = 24 ∧ a 2 = 410 ∧ a 3 = 6120 ∧ a 4 = 85035 ∧
    (List.range 4).map (fun d => ((univ : Finset (Equiv.Perm (Fin 4))).filter
      (fun q => des q = d)).card) = [1, 11, 11, 1] := by
  obtain ⟨v1, v2, v3, v4⟩ := values
  refine ⟨by exact_mod_cast v1, by exact_mod_cast v2, by exact_mod_cast v3, by exact_mod_cast v4,
    by decide⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      ((1 - X) ^ 2 * (1 - 11 * X) ^ 2) = X * (12 - 11 * X) * (2 - 12 * X + 11 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (4 * (4 + 11 ^ (2 + n)) + 5 * (1 + 11 ^ (2 + n)) * n) / 500 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a221619

theorem OMA.solution : type_of% @OMA.S_oeis_a221619.main :=
  OMA.S_oeis_a221619.conjecture
