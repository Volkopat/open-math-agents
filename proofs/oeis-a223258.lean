import OMAStatements.S_oeis_a223258

namespace OMA.S_oeis_a223258

open PowerSeries Finset









/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 12 × Fin 12 × Fin 12) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 12 × Fin 12 × Fin 12)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 12 × Fin 12 × Fin 12) (g : Fin (n + 1) → Fin 12 × Fin 12 × Fin 12) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 12 × Fin 12 × Fin 12) ↔
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 12 × Fin 12 × Fin 12, if r.1 = 0 then W n r else 0 := by
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

lemma W_zero (r : Fin 12 × Fin 12 × Fin 12) : W 0 r = if hrow r then 1 else 0 := by
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
def consEmb (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12) :
    (Fin (n + 1) → Fin 12 × Fin 12 × Fin 12) ↪ (Fin (n + 2) → Fin 12 × Fin 12 × Fin 12) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12) (g : Fin (n + 1) → Fin 12 × Fin 12 × Fin 12) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12) :
    W (n + 1) r = ∑ s : Fin 12 × Fin 12 × Fin 12, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 12 × Fin 12 × Fin 12)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 12 × Fin 12 × Fin 12)).filter
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

/-- The adjacency as one bit mask: y is adjacent to x when bit 12 x + y of `MASK` is set. -/
def MASK : ℕ := 10805457639340616869195767250808501889814590

/-- Fast adjacency. -/
def adjB (x y : Fin 12) : Bool := Nat.testBit MASK (12 * x.val + y.val)

set_option maxHeartbeats 4000000 in
lemma adj_iff : ∀ x y : Fin 12, adj x y ↔ adjB x y = true := by
  decide +kernel

/-- Fast row test. -/
def hrowB (r : Fin 12 × Fin 12 × Fin 12) : Bool := adjB r.1 r.2.1 && adjB r.2.1 r.2.2

/-- Fast compatibility test. -/
def okB (r s : Fin 12 × Fin 12 × Fin 12) : Bool := adjB r.1 s.1 && (adjB r.2.1 s.2.1 && (adjB r.2.2 s.2.2))

lemma hrow_iff (r : Fin 12 × Fin 12 × Fin 12) : hrow r ↔ hrowB r = true := by
  simp only [hrow, hrowB, adj_iff, Bool.and_eq_true]

lemma ok_iff (r s : Fin 12 × Fin 12 × Fin 12) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, adj_iff, Bool.and_eq_true]

lemma W_invalid (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12) (h : hrowB r = false) : W n r = 0 := by
  unfold W
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, _⟩, h0⟩
  have h2 := (hrow_iff r).1 (h0 ▸ h1 0)
  rw [h] at h2
  exact Bool.false_ne_true h2

lemma W_zeroB (r : Fin 12 × Fin 12 × Fin 12) : W 0 r = if hrowB r = true then 1 else 0 := by
  rw [W_zero]
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos ((hrow_iff r).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((hrow_iff r).1 h))]

/-- The guards of the rows s = (x, y, z) allowed below r, entry by entry: `gA` tests x alone,
`gB` the conditions on y given x, `gC` those on z given y. -/
def gA (r : Fin 12 × Fin 12 × Fin 12) (x : Fin 12) : Bool := adjB r.1 x

/-- See `gA`. -/
def gB (r : Fin 12 × Fin 12 × Fin 12) (x y : Fin 12) : Bool := adjB r.2.1 y && adjB x y

/-- See `gA`. -/
def gC (r : Fin 12 × Fin 12 × Fin 12) (y z : Fin 12) : Bool := adjB r.2.2 z && adjB y z

/-- The sum of g over the valid rows allowed below r, enumerated entry by entry. -/
def succSum (r : Fin 12 × Fin 12 × Fin 12) (g : Fin 12 × Fin 12 × Fin 12 → ℕ) : ℕ :=
  ∑ x : Fin 12, if gA r x = true then ∑ y : Fin 12, (if gB r x y = true then
    ∑ z : Fin 12, (if gC r y z = true then g (x, y, z) else 0) else 0) else 0

lemma cond_split (r : Fin 12 × Fin 12 × Fin 12) (x y z : Fin 12) :
    (okB r (x, y, z) && hrowB (x, y, z)) = (gA r x && (gB r x y && gC r y z)) := by
  simp only [okB, hrowB, gA, gB, gC]
  generalize adjB r.1 x = b0
  generalize adjB r.2.1 y = b1
  generalize adjB r.2.2 z = b2
  generalize adjB x y = b3
  generalize adjB y z = b4
  revert b0 b1 b2 b3 b4
  decide

lemma succ_eq (r : Fin 12 × Fin 12 × Fin 12) (hr : hrowB r = true) (g : Fin 12 × Fin 12 × Fin 12 → ℕ)
    (hg : ∀ s, hrowB s = false → g s = 0) :
    (∑ s : Fin 12 × Fin 12 × Fin 12, if hrow r ∧ ok r s then g s else 0) = succSum r g := by
  have e1 : ∀ s : Fin 12 × Fin 12 × Fin 12, (if hrow r ∧ ok r s then g s else 0) =
      if (okB r s && hrowB s) = true then g s else 0 := by
    intro s
    by_cases hs : hrowB s = true
    · simp [hrow_iff, ok_iff, hr, hs]
    · have h0 : g s = 0 := hg s (by simpa using hs)
      simp [h0]
  rw [Finset.sum_congr rfl (fun s _ => e1 s), Fintype.sum_prod_type]
  unfold succSum
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Fintype.sum_prod_type]
  by_cases hA : gA r x = true
  · rw [if_pos hA]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases hB : gB r x y = true
    · rw [if_pos hB]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp [cond_split, hA, hB]
    · rw [if_neg hB]
      refine Finset.sum_eq_zero (fun z _ => ?_)
      simp [cond_split, hA, hB]
  · rw [if_neg hA]
    refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun z _ => ?_))
    simp [cond_split, hA]

/-- The number of rows allowed below a row: 0 for an invalid row, otherwise 41 when
x(i,0) = x(i,2) and 32 otherwise. -/
def dtab (r : Fin 12 × Fin 12 × Fin 12) : ℕ :=
  if hrowB r = true then (if r.1 = r.2.2 then 41 else 32) else 0

set_option maxHeartbeats 4000000 in
lemma one_check : ∀ x y : Fin 12, adjB x y = true → ∀ z : Fin 12, adjB y z = true →
    succSum (x, y, z) (fun s => if hrowB s = true then 1 else 0) = dtab (x, y, z) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ x y : Fin 12, adjB x y = true → ∀ z : Fin 12, adjB y z = true →
    succSum (x, y, z) dtab + 129 = 38 * dtab (x, y, z) := by
  decide +kernel

lemma W_zero_fun : W 0 = fun s => if hrowB s = true then 1 else 0 := funext W_zeroB

lemma W_one (r : Fin 12 × Fin 12 × Fin 12) : W 1 r = dtab r := by
  by_cases hr : hrowB r = true
  · rw [W_succ, succ_eq r hr (W 0) (W_invalid 0), W_zero_fun]
    obtain ⟨x, y, z⟩ := r
    have h := hr
    simp only [hrowB, Bool.and_eq_true] at h
    exact one_check x y h.1 z h.2
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 1 r hf]
    simp [dtab, hf]

lemma W_one_fun : W 1 = dtab := funext W_one

lemma W_rec (n : ℕ) (r : Fin 12 × Fin 12 × Fin 12) :
    W (n + 2) r + 129 * W n r = 38 * W (n + 1) r := by
  induction n generalizing r with
  | zero =>
    by_cases hr : hrowB r = true
    · rw [show 0 + 2 = 1 + 1 from rfl, W_succ 1 r, succ_eq r hr (W 1) (W_invalid 1),
        show 0 + 1 = 1 from rfl, W_one_fun, W_zeroB, if_pos hr]
      obtain ⟨x, y, z⟩ := r
      have h := hr
      simp only [hrowB, Bool.and_eq_true] at h
      simpa using base_check x y h.1 z h.2
    · have hf : hrowB r = false := by simpa using hr
      rw [W_invalid _ r hf, W_invalid _ r hf, W_invalid _ r hf]
  | succ n ih =>
    rw [W_succ (n + 2), W_succ (n + 1), W_succ n]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs
    · exact ih s
    · simp

lemma a_rec (n : ℕ) : a (n + 3) + 129 * a (n + 1) = 38 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_one : a 1 = 25 := by
  rw [a_succ]
  simp only [W_zeroB]
  decide +kernel

lemma a_two : a 2 = 845 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 5x(5 - 21x)/(1 - 38x + 129x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 38 * X + 129 * X ^ 2) = 5 * X * (5 - 21 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 38 * X + 129 * X ^ 2) = A - A * X ^ 1 * C 38 + A * X ^ 2 * C 129 := by
    rw [show (38 : ℚ⟦X⟧) = C 38 from (map_ofNat C 38).symm,
      show (129 : ℚ⟦X⟧) = C 129 from (map_ofNat C 129).symm]
    ring
  have e2 : (5 : ℚ⟦X⟧) * X * (5 - 21 * X) = X ^ 1 * C 25 - X ^ 2 * C 105 := by
    rw [show (5 : ℚ⟦X⟧) = C 5 from (map_ofNat C 5).symm,
      show (21 : ℚ⟦X⟧) = C 21 from (map_ofNat C 21).symm, show (25 : ℚ) = 5 * 5 by norm_num,
      show (105 : ℚ) = 5 * 21 by norm_num, map_mul, map_mul]
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
    have hq : ((a (n + 3) : ℕ) : ℚ) + 129 * a (n + 1) = 38 * a (n + 2) := by exact_mod_cast h
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega, if_false,
      show 1 ≤ n + 3 by omega, show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 1 = 0) by omega]
    linear_combination hq

/-- The bracket of Barker's closed form. -/
noncomputable def Gf (n : ℕ) : ℝ := (19 - 2 * Real.sqrt 58) ^ n * (-41 + 7 * Real.sqrt 58) + (19 + 2 * Real.sqrt 58) ^ n * (41 + 7 * Real.sqrt 58)

lemma Gf_rec (n : ℕ) : Gf (n + 2) = 38 * Gf (n + 1) - 129 * Gf n := by
  have s2 : Real.sqrt 58 ^ 2 = 58 := Real.sq_sqrt (by norm_num)
  unfold Gf
  have h1 : (19 - 2 * Real.sqrt 58) ^ 2 = 38 * (19 - 2 * Real.sqrt 58) - 129 := by
    linear_combination 4 * s2
  have h2 : (19 + 2 * Real.sqrt 58) ^ 2 = 38 * (19 + 2 * Real.sqrt 58) - 129 := by
    linear_combination 4 * s2
  rw [show (19 - 2 * Real.sqrt 58) ^ (n + 2) = (19 - 2 * Real.sqrt 58) ^ n * (19 - 2 * Real.sqrt 58) ^ 2 by ring,
    show (19 + 2 * Real.sqrt 58) ^ (n + 2) = (19 + 2 * Real.sqrt 58) ^ n * (19 + 2 * Real.sqrt 58) ^ 2 by ring]
  rw [h1, h2]
  ring

lemma Gf_zero : Gf 0 = 14 * Real.sqrt 58 := by
  have s2 : Real.sqrt 58 ^ 2 = 58 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (0) * s2

lemma Gf_one : Gf 1 = 430 * Real.sqrt 58 := by
  have s2 : Real.sqrt 58 ^ 2 = 58 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (0) * s2

lemma Gf_two : Gf 2 = 14534 * Real.sqrt 58 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, Gf_rec, Gf_one, Gf_zero]
  ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (5 * ((19 - 2 * Real.sqrt 58) ^ n * (-41 + 7 * Real.sqrt 58) +
        (19 + 2 * Real.sqrt 58) ^ n * (41 + 7 * Real.sqrt 58))) / (86 * Real.sqrt 58) := by
  have key : ∀ k, (a (k + 1) : ℝ) * (86 * Real.sqrt 58) = 5 * Gf (k + 1) ∧
      (a (k + 2) : ℝ) * (86 * Real.sqrt 58) = 5 * Gf (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, Gf_one]; push_cast; ring
      · rw [a_two, Gf_two]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ((a (k + 3) : ℕ) : ℝ) + 129 * a (k + 1) = 38 * a (k + 2) := by
        exact_mod_cast a_rec k
      have hg := Gf_rec (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hg
      show (a (k + 3) : ℝ) * (86 * Real.sqrt 58) = 5 * Gf (k + 3)
      linear_combination (86 * Real.sqrt 58) * hr + 38 * ih.2 - 129 * ih.1 - 5 * hg
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  show (a (k + 1) : ℝ) = (5 * Gf (k + 1)) / (86 * Real.sqrt 58)
  rw [eq_div_iff (by positivity)]
  linear_combination hk

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 38 * X + 129 * X ^ 2) =
      5 * X * (5 - 21 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (5 * ((19 - 2 * Real.sqrt 58) ^ n * (-41 + 7 * Real.sqrt 58) +
        (19 + 2 * Real.sqrt 58) ^ n * (41 + 7 * Real.sqrt 58))) / (86 * Real.sqrt 58) :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and a(1), a(2). -/
theorem controls : a 1 = 25 ∧ a 2 = 845 ∧ a 3 = 28885 ∧ a 4 = 988625 ∧ a 5 = 33841585 ∧ a 6 = 1158447605 ∧ a 7 = 39655444525 ∧ a 8 = 1357467150905 ∧ a 9 = 46468199390665 ∧ a 10 = 1590678314378525 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have h1 := a_one; have h2 := a_two
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- Controls on the graph: 30 edges, every vertex has 5 neighbors. -/
theorem graph_controls : edges.length = 30 ∧
    ∀ x : Fin 12, ((univ : Finset (Fin 12)).filter (adj x)).card = 5 := by
  decide +kernel

end OMA.S_oeis_a223258

theorem OMA.solution : type_of% @OMA.S_oeis_a223258.main :=
  OMA.S_oeis_a223258.conjecture
