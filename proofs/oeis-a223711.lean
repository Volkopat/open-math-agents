import OMAStatements.S_oeis_a223711

namespace OMA.S_oeis_a223711

open PowerSeries Finset


instance {m : ℕ} (s : Fin m → ℕ) : Decidable (unimodal s) := by unfold unimodal; infer_instance




/-- A nonincreasing sequence. -/
def noninc {m : ℕ} (s : Fin m → ℕ) : Prop := ∀ i j : Fin m, i ≤ j → s j ≤ s i

instance {m : ℕ} (s : Fin m → ℕ) : Decidable (noninc s) := by unfold noninc; infer_instance

lemma unimodal_two (s : Fin 2 → ℕ) : unimodal s := by
  by_cases h : s 1 ≤ s 0
  · refine ⟨0, fun i j hij hj => ?_, fun i j hi hij => ?_⟩
    · have hj0 : j = 0 := le_antisymm hj (Fin.zero_le _)
      have hi0 : i = 0 := le_antisymm (hij.trans hj) (Fin.zero_le _)
      rw [hi0, hj0]
    · fin_cases i <;> fin_cases j <;> simp_all
  · refine ⟨1, fun i j hij hj => ?_, fun i j hi hij => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all <;> omega
    · fin_cases i <;> fin_cases j <;> simp_all

lemma unimodal_one (s : Fin 1 → ℕ) : unimodal s :=
  ⟨0, fun i j _ _ => by rw [Subsingleton.elim i j], fun i j _ _ => by rw [Subsingleton.elim i j]⟩

lemma noninc_one (s : Fin 1 → ℕ) : noninc s := fun i j _ => by rw [Subsingleton.elim i j]

lemma noninc_cons {m : ℕ} (x : ℕ) (s : Fin (m + 1) → ℕ) :
    noninc (Fin.cons x s : Fin (m + 2) → ℕ) ↔ s 0 ≤ x ∧ noninc s := by
  constructor
  · intro h
    refine ⟨?_, fun i j hij => ?_⟩
    · simpa using h 0 1 (Fin.zero_le _)
    · simpa using h i.succ j.succ (Fin.succ_le_succ_iff.mpr hij)
  · rintro ⟨h0, h1⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact le_refl _
      | succ j => simpa using (h1 0 j (Fin.zero_le _)).trans h0
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp [Fin.le_def])
      | succ j => simpa using h1 i j (Fin.succ_le_succ_iff.mp hij)

lemma unimodal_cons {m : ℕ} (x : ℕ) (s : Fin (m + 1) → ℕ) :
    unimodal (Fin.cons x s : Fin (m + 2) → ℕ) ↔ (x ≤ s 0 ∧ unimodal s) ∨ (s 0 < x ∧ noninc s) := by
  constructor
  · rintro ⟨k, hinc, hdec⟩
    by_cases hx : x ≤ s 0
    · left
      refine ⟨hx, ?_⟩
      induction k using Fin.cases with
      | zero =>
        refine ⟨0, fun i j hij hj => ?_, fun i j _ hij => ?_⟩
        · rw [le_antisymm hj (Fin.zero_le _), le_antisymm (hij.trans hj) (Fin.zero_le _)]
        · simpa using hdec i.succ j.succ (Fin.zero_le _) (Fin.succ_le_succ_iff.mpr hij)
      | succ k =>
        refine ⟨k, fun i j hij hj => ?_, fun i j hi hij => ?_⟩
        · simpa using hinc i.succ j.succ (Fin.succ_le_succ_iff.mpr hij) (Fin.succ_le_succ_iff.mpr hj)
        · simpa using hdec i.succ j.succ (Fin.succ_le_succ_iff.mpr hi) (Fin.succ_le_succ_iff.mpr hij)
    · right
      refine ⟨lt_of_not_ge hx, ?_⟩
      induction k using Fin.cases with
      | zero =>
        intro i j hij
        simpa using hdec i.succ j.succ (Fin.zero_le _) (Fin.succ_le_succ_iff.mpr hij)
      | succ k =>
        exfalso
        have := hinc 0 1 (Fin.zero_le _) (by simp [Fin.le_def])
        simp at this
        exact hx this
  · rintro (⟨hx, k, hinc, hdec⟩ | ⟨hx, hn⟩)
    · refine ⟨k.succ, fun i j hij hj => ?_, fun i j hi hij => ?_⟩
      · induction i using Fin.cases with
        | zero =>
          induction j using Fin.cases with
          | zero => exact le_refl _
          | succ j =>
            simpa using hx.trans (hinc 0 j (Fin.zero_le _) (Fin.succ_le_succ_iff.mp hj))
        | succ i =>
          induction j using Fin.cases with
          | zero => exact absurd hij (by simp [Fin.le_def])
          | succ j =>
            simpa using hinc i j (Fin.succ_le_succ_iff.mp hij) (Fin.succ_le_succ_iff.mp hj)
      · induction i using Fin.cases with
        | zero => exact absurd hi (by simp [Fin.le_def])
        | succ i =>
          induction j using Fin.cases with
          | zero => exact absurd hij (by simp [Fin.le_def])
          | succ j =>
            simpa using hdec i j (Fin.succ_le_succ_iff.mp hi) (Fin.succ_le_succ_iff.mp hij)
    · refine ⟨0, fun i j hij hj => ?_, fun i j _ hij => ?_⟩
      · rw [le_antisymm hj (Fin.zero_le _), le_antisymm (hij.trans hj) (Fin.zero_le _)]
      · exact (noninc_cons x s).2 ⟨hx.le, hn⟩ i j hij

/-- The sum of a row. -/
def rs (r : Fin 2 → Fin 2) : ℕ := (r 0).val + (r 1).val

/-- The number of rows with sum x. -/
def w (x : ℕ) : ℕ := ((univ : Finset (Fin 2 → Fin 2)).filter (fun r => rs r = x)).card

lemma w_vals : w 0 = 1 ∧ w 1 = 2 ∧ w 2 = 1 := by decide

lemma rs_lt (r : Fin 2 → Fin 2) : rs r < 3 := by
  have h0 := (r 0).isLt
  have h1 := (r 1).isLt
  unfold rs
  omega

/-- Arrays of m + 1 rows with first row sum v and unimodal row sums. -/
def U (m v : ℕ) : ℕ := ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter
  (fun g => rs (g 0) = v ∧ unimodal (fun i => rs (g i)))).card

/-- Arrays of m + 1 rows with first row sum v and nonincreasing row sums. -/
def D (m v : ℕ) : ℕ := ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter
  (fun g => rs (g 0) = v ∧ noninc (fun i => rs (g i)))).card

lemma rs_cons {m : ℕ} (r : Fin 2 → Fin 2) (h : Fin (m + 1) → Fin 2 → Fin 2) :
    (fun i => rs ((Fin.cons r h : Fin (m + 2) → Fin 2 → Fin 2) i)) =
      (Fin.cons (rs r) (fun i => rs (h i)) : Fin (m + 2) → ℕ) := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp

/-- Counting arrays of m + 2 rows by their first row and the rest. -/
lemma card_cons {m : ℕ} (x : ℕ) (P : ℕ → (Fin (m + 1) → Fin 2 → Fin 2) → Prop)
    [∀ y, DecidablePred (P y)] :
    ((univ : Finset (Fin (m + 2) → Fin 2 → Fin 2)).filter
      (fun g => rs (g 0) = x ∧ P (rs (g 0)) (Fin.tail g))).card =
    w x * ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter (P x)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => g 0) (t := univ) (by simp)]
  have : ∀ r : Fin 2 → Fin 2,
      (((univ : Finset (Fin (m + 2) → Fin 2 → Fin 2)).filter
        (fun g => rs (g 0) = x ∧ P (rs (g 0)) (Fin.tail g))).filter (fun g => g 0 = r)).card =
      if rs r = x then ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter (P x)).card else 0 := by
    intro r
    split_ifs with hr
    · refine Finset.card_bij' (fun g _ => Fin.tail g) (fun h _ => Fin.cons r h) ?_ ?_ ?_ ?_
      · intro g hg
        simp only [mem_filter, mem_univ, true_and] at hg ⊢
        rw [← hg.1.1]
        exact hg.1.2
      · intro h hh
        simp only [mem_filter, mem_univ, true_and] at hh ⊢
        refine ⟨⟨by simpa using hr, ?_⟩, by simp⟩
        simpa [hr] using hh
      · intro g hg
        simp only [mem_filter, mem_univ, true_and] at hg
        rw [← hg.2]
        exact Fin.cons_self_tail g
      · intro h _
        simp
    · rw [Finset.card_eq_zero]
      ext g
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
      intro h1 h0
      rw [h0] at h1
      exact hr h1.1
  rw [Finset.sum_congr rfl (fun r _ => this r), ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  rfl

/-- Counting arrays by their first row sum. -/
lemma card_split {m : ℕ} (Q : ℕ → (Fin (m + 1) → Fin 2 → Fin 2) → Prop) [∀ y, DecidablePred (Q y)] :
    ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter (fun h => Q (rs (h 0)) h)).card =
    ∑ v ∈ range 3, ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter
      (fun h => rs (h 0) = v ∧ Q v h)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun h => rs (h 0)) (t := range 3)
    (fun h _ => Finset.mem_range.mpr (rs_lt _))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  congr 1
  ext h
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hq, hv⟩
    exact ⟨hv, hv ▸ hq⟩
  · rintro ⟨hv, hq⟩
    exact ⟨hv ▸ hq, hv⟩

lemma U_zero (v : ℕ) : U 0 v = w v := by
  unfold U w
  refine Finset.card_bij' (fun g _ => g 0) (fun r _ => fun _ => r) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    exact hg.1
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact ⟨hr, unimodal_one _⟩
  · intro g _
    funext i
    fin_cases i
    rfl
  · intro r _
    rfl

lemma D_zero (v : ℕ) : D 0 v = w v := by
  unfold D w
  refine Finset.card_bij' (fun g _ => g 0) (fun r _ => fun _ => r) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    exact hg.1
  · intro r hr
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact ⟨hr, noninc_one _⟩
  · intro g _
    funext i
    fin_cases i
    rfl
  · intro r _
    rfl

lemma U_succ (m x : ℕ) :
    U (m + 1) x = w x * ∑ v ∈ range 3, (if x ≤ v then U m v else D m v) := by
  have e : ((univ : Finset (Fin (m + 2) → Fin 2 → Fin 2)).filter
      (fun g => rs (g 0) = x ∧ unimodal (fun i => rs (g i)))) =
      ((univ : Finset (Fin (m + 2) → Fin 2 → Fin 2)).filter
      (fun g => rs (g 0) = x ∧ (fun y h => (y ≤ rs (h 0) ∧ unimodal (fun i => rs (h i))) ∨
        (rs (h 0) < y ∧ noninc (fun i => rs (h i)))) (rs (g 0)) (Fin.tail g))) := by
    ext g
    simp only [mem_filter, mem_univ, true_and]
    rw [← Fin.cons_self_tail g, rs_cons, unimodal_cons]
    simp
  unfold U
  rw [e, card_cons x (fun y h => (y ≤ rs (h 0) ∧ unimodal (fun i => rs (h i))) ∨
    (rs (h 0) < y ∧ noninc (fun i => rs (h i))))]
  congr 1
  rw [card_split (fun y h => (x ≤ y ∧ unimodal (fun i => rs (h i))) ∨
    (y < x ∧ noninc (fun i => rs (h i))))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · congr 1
    ext h
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, (⟨_, h2⟩ | ⟨h2, _⟩)⟩
      · exact ⟨h1, h2⟩
      · omega
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inl ⟨hv, h2⟩⟩
  · congr 1
    ext h
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, (⟨h2, _⟩ | ⟨_, h2⟩)⟩
      · omega
      · exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Or.inr ⟨by omega, h2⟩⟩

lemma D_succ (m x : ℕ) :
    D (m + 1) x = w x * ∑ v ∈ range 3, (if v ≤ x then D m v else 0) := by
  have e : ((univ : Finset (Fin (m + 2) → Fin 2 → Fin 2)).filter
      (fun g => rs (g 0) = x ∧ noninc (fun i => rs (g i)))) =
      ((univ : Finset (Fin (m + 2) → Fin 2 → Fin 2)).filter
      (fun g => rs (g 0) = x ∧ (fun y h => rs (h 0) ≤ y ∧ noninc (fun i => rs (h i)))
        (rs (g 0)) (Fin.tail g))) := by
    ext g
    simp only [mem_filter, mem_univ, true_and]
    rw [← Fin.cons_self_tail g, rs_cons, noninc_cons]
    simp
  unfold D
  rw [e, card_cons x (fun y h => rs (h 0) ≤ y ∧ noninc (fun i => rs (h i)))]
  congr 1
  rw [card_split (fun y h => y ≤ x ∧ noninc (fun i => rs (h i)))]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs with hv
  · congr 1
    ext h
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hv, h2⟩
  · rw [Finset.card_eq_zero]
    ext h
    simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
    intro _ h2
    exact absurd h2 hv

lemma steps (m : ℕ) :
    D (m + 1) 0 = D m 0 ∧ D (m + 1) 1 = 2 * (D m 0 + D m 1) ∧
    D (m + 1) 2 = D m 0 + D m 1 + D m 2 ∧ U (m + 1) 0 = U m 0 + U m 1 + U m 2 ∧
    U (m + 1) 1 = 2 * (D m 0 + U m 1 + U m 2) ∧ U (m + 1) 2 = D m 0 + D m 1 + U m 2 := by
  obtain ⟨w0, w1, w2⟩ := w_vals
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [D_succ, U_succ, w0, w1, w2, Finset.sum_range_succ]

/-- The closed forms of the six counts. -/
lemma closed (m : ℕ) :
    (D m 0 : ℤ) = 1 ∧ (D m 1 : ℤ) = 4 * 2 ^ m - 2 ∧ (D m 2 : ℤ) = 4 * 2 ^ m - 3 - m ∧
    2 * (U m 0 : ℤ) = m ^ 2 + 5 * m + 18 + (8 * m - 16) * 2 ^ m ∧
    (U m 1 : ℤ) = 2 * m + 6 + (4 * m - 4) * 2 ^ m ∧ (U m 2 : ℤ) = 4 * 2 ^ m - 3 - m := by
  obtain ⟨w0, w1, w2⟩ := w_vals
  induction m with
  | zero =>
    simp only [U_zero, D_zero, w0, w1, w2]
    norm_num
  | succ m ih =>
    obtain ⟨d0, d1, d2, u0, u1, u2⟩ := ih
    obtain ⟨s0, s1, s2, s3, s4, s5⟩ := steps m
    rw [s0, s1, s2, s3, s4, s5]
    push_cast
    refine ⟨by linear_combination d0, by linear_combination 2 * d0 + 2 * d1,
      by linear_combination d0 + d1 + d2, by linear_combination u0 + 2 * u1 + 2 * u2,
      by linear_combination 2 * d0 + 2 * u1 + 2 * u2, by linear_combination d0 + d1 + u2⟩

lemma a_succ (m : ℕ) : a (m + 1) = U m 0 + U m 1 + U m 2 := by
  have e : ((univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter good) =
      (univ : Finset (Fin (m + 1) → Fin 2 → Fin 2)).filter
        (fun h => (fun (_ : ℕ) h => unimodal (fun i => rs (h i))) (rs (h 0)) h) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, good]
    exact ⟨fun h => h.1, fun h => ⟨h, unimodal_two _⟩⟩
  unfold a
  rw [e, card_split (fun (_ : ℕ) h => unimodal (fun i => rs (h i))), Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  rfl

/-- The closed form of the entry, for every n >= 1, as an identity of rationals. -/
theorem closed_form (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (-2 * (2 ^ (3 + n) - 9) + (5 + 2 ^ (3 + n)) * n + n ^ 2) / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨_, _, _, u0, u1, u2⟩ := closed m
  have h : 2 * (a (m + 1) : ℤ) = (m + 1) ^ 2 + 5 * (m + 1) + 18 + (16 * m - 16) * 2 ^ m := by
    rw [a_succ]
    push_cast
    linear_combination u0 + 2 * u1 + 2 * u2
  have hq : 2 * (a (m + 1) : ℚ) = (m + 1) ^ 2 + 5 * (m + 1) + 18 + (16 * m - 16) * 2 ^ m := by
    exact_mod_cast h
  rw [show 3 + (m + 1) = m + 4 by ring, pow_add]
  push_cast
  linear_combination hq / 2

lemma a_rec (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 5) : ℚ) = 7 * a (n + 4) - 19 * a (n + 3) + 25 * a (n + 2) - 16 * a (n + 1) + 4 * a n := by
  rw [closed_form (n + 5) (by omega), closed_form (n + 4) (by omega), closed_form (n + 3) (by omega),
    closed_form (n + 2) (by omega), closed_form (n + 1) (by omega), closed_form n hn]
  push_cast
  ring_nf

/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) ^ 3 * (1 - 2 * X) ^ 2) = X * (2 - 3 * X + 2 * X ^ 2) ^ 2 := by
  have v1 : (a 1 : ℚ) = 4 := by rw [closed_form 1 le_rfl]; norm_num
  have v2 : (a 2 : ℚ) = 16 := by rw [closed_form 2 (by norm_num)]; norm_num
  have v3 : (a 3 : ℚ) = 53 := by rw [closed_form 3 (by norm_num)]; norm_num
  have v4 : (a 4 : ℚ) = 155 := by rw [closed_form 4 (by norm_num)]; norm_num
  have v5 : (a 5 : ℚ) = 418 := by rw [closed_form 5 (by norm_num)]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) ^ 3 * (1 - 2 * X) ^ 2) =
      A - A * X ^ 1 * C 7 + A * X ^ 2 * C 19 - A * X ^ 3 * C 25 + A * X ^ 4 * C 16 -
        A * X ^ 5 * C 4 := by
    rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (19 : ℚ) : ℚ⟦X⟧) = 19 from map_ofNat C 19,
      show (C (25 : ℚ) : ℚ⟦X⟧) = 25 from map_ofNat C 25, show (C (16 : ℚ) : ℚ⟦X⟧) = 16 from map_ofNat C 16,
      show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  have e2 : (X * (2 - 3 * X + 2 * X ^ 2) ^ 2 : ℚ⟦X⟧) =
      X ^ 1 * C 4 - X ^ 2 * C 12 + X ^ 3 * C 17 - X ^ 4 * C 12 + X ^ 5 * C 4 := by
    rw [show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4, show (C (12 : ℚ) : ℚ⟦X⟧) = 12 from map_ofNat C 12,
      show (C (17 : ℚ) : ℚ⟦X⟧) = 17 from map_ofNat C 17]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | _ | n
  · simp
  · simp [v1]
  · simp [v1, v2]
    norm_num
  · simp [v1, v2, v3]
    norm_num
  · simp [v1, v2, v3, v4]
    norm_num
  · simp [v1, v2, v3, v4, v5]
    norm_num
  · have hq := a_rec (n + 1) (by omega)
    simp only [show n + 1 + 5 = n + 6 by omega, show n + 1 + 4 = n + 5 by omega,
      show n + 1 + 3 = n + 4 by omega, show n + 1 + 2 = n + 3 by omega,
      show n + 1 + 1 = n + 2 by omega] at hq
    simp only [if_false, if_true, show ¬ (n + 6 = 0) by omega,
      show 1 ≤ n + 6 by omega, show ¬ (n + 6 - 1 = 0) by omega, show n + 6 - 1 = n + 5 by omega,
      show ¬ (n + 5 = 0) by omega,
      show 2 ≤ n + 6 by omega, show ¬ (n + 6 - 2 = 0) by omega, show n + 6 - 2 = n + 4 by omega,
      show ¬ (n + 4 = 0) by omega,
      show 3 ≤ n + 6 by omega, show ¬ (n + 6 - 3 = 0) by omega, show n + 6 - 3 = n + 3 by omega,
      show ¬ (n + 3 = 0) by omega,
      show 4 ≤ n + 6 by omega, show ¬ (n + 6 - 4 = 0) by omega, show n + 6 - 4 = n + 2 by omega,
      show ¬ (n + 2 = 0) by omega,
      show 5 ≤ n + 6 by omega, show ¬ (n + 6 - 5 = 0) by omega, show n + 6 - 5 = n + 1 by omega,
      show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 6 = 1) by omega, show ¬ (n + 6 = 2) by omega, show ¬ (n + 6 = 3) by omega,
      show ¬ (n + 6 = 4) by omega, show ¬ (n + 6 = 5) by omega]
    linear_combination hq

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) ^ 3 * (1 - 2 * X) ^ 2) = X * (2 - 3 * X + 2 * X ^ 2) ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (-2 * (2 ^ (3 + n) - 9) + (5 + 2 ^ (3 + n)) * n + n ^ 2) / 2 :=
  ⟨gf, closed_form⟩

end OMA.S_oeis_a223711

theorem OMA.solution : type_of% @OMA.S_oeis_a223711.main :=
  OMA.S_oeis_a223711.conjecture
