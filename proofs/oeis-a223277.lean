import OMAStatements.S_oeis_a223277

namespace OMA.S_oeis_a223277

open PowerSeries Finset










/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 20 × Fin 20 × Fin 20) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 20 × Fin 20 × Fin 20) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 20 × Fin 20 × Fin 20)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 20 × Fin 20 × Fin 20) (g : Fin (n + 1) → Fin 20 × Fin 20 × Fin 20) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 20 × Fin 20 × Fin 20) ↔
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 20 × Fin 20 × Fin 20, if r.1 = 0 then W n r else 0 := by
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

lemma W_zero (r : Fin 20 × Fin 20 × Fin 20) : W 0 r = if hrow r then 1 else 0 := by
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
def consEmb (n : ℕ) (r : Fin 20 × Fin 20 × Fin 20) :
    (Fin (n + 1) → Fin 20 × Fin 20 × Fin 20) ↪ (Fin (n + 2) → Fin 20 × Fin 20 × Fin 20) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 20 × Fin 20 × Fin 20) (g : Fin (n + 1) → Fin 20 × Fin 20 × Fin 20) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 20 × Fin 20 × Fin 20) :
    W (n + 1) r = ∑ s : Fin 20 × Fin 20 × Fin 20, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 20 × Fin 20 × Fin 20)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 20 × Fin 20 × Fin 20)).filter
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

/-- The adjacency as one bit mask: y is adjacent to x when bit 20 x + y of `MASK` is set. -/
def MASK : ℕ := 847302299628059881512209833736598988471232463773564974877329715162886529365716318232546312462895219986638180485889523750

/-- Fast adjacency. -/
def adjB (x y : Fin 20) : Bool := Nat.testBit MASK (20 * x.val + y.val)

set_option maxHeartbeats 4000000 in
lemma adj_iff : ∀ x y : Fin 20, adj x y ↔ adjB x y = true := by
  decide +kernel

/-- Fast row test. -/
def hrowB (r : Fin 20 × Fin 20 × Fin 20) : Bool := adjB r.1 r.2.1 && adjB r.2.1 r.2.2

/-- Fast compatibility test. -/
def okB (r s : Fin 20 × Fin 20 × Fin 20) : Bool := adjB r.1 s.2.1 && (adjB r.2.1 s.2.2 && (adjB r.2.1 s.1 && (adjB r.2.2 s.2.1)))

lemma hrow_iff (r : Fin 20 × Fin 20 × Fin 20) : hrow r ↔ hrowB r = true := by
  simp only [hrow, hrowB, adj_iff, Bool.and_eq_true]

lemma ok_iff (r s : Fin 20 × Fin 20 × Fin 20) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, adj_iff, Bool.and_eq_true]

lemma W_invalid (n : ℕ) (r : Fin 20 × Fin 20 × Fin 20) (h : hrowB r = false) : W n r = 0 := by
  unfold W
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, _⟩, h0⟩
  have h2 := (hrow_iff r).1 (h0 ▸ h1 0)
  rw [h] at h2
  exact Bool.false_ne_true h2

lemma W_zeroB (r : Fin 20 × Fin 20 × Fin 20) : W 0 r = if hrowB r = true then 1 else 0 := by
  rw [W_zero]
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos ((hrow_iff r).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((hrow_iff r).1 h))]

/-- The guards of the rows s = (x, y, z) allowed below r, entry by entry: `gA` tests x alone,
`gB` the conditions on y given x, `gC` those on z given y. -/
def gA (r : Fin 20 × Fin 20 × Fin 20) (x : Fin 20) : Bool := adjB r.2.1 x

/-- See `gA`. -/
def gB (r : Fin 20 × Fin 20 × Fin 20) (x y : Fin 20) : Bool := adjB r.1 y && (adjB r.2.2 y && adjB x y)

/-- See `gA`. -/
def gC (r : Fin 20 × Fin 20 × Fin 20) (y z : Fin 20) : Bool := adjB r.2.1 z && adjB y z

/-- The sum of g over the valid rows allowed below r, enumerated entry by entry. -/
def succSum (r : Fin 20 × Fin 20 × Fin 20) (g : Fin 20 × Fin 20 × Fin 20 → ℕ) : ℕ :=
  ∑ x : Fin 20, if gA r x = true then ∑ y : Fin 20, (if gB r x y = true then
    ∑ z : Fin 20, (if gC r y z = true then g (x, y, z) else 0) else 0) else 0

lemma cond_split (r : Fin 20 × Fin 20 × Fin 20) (x y z : Fin 20) :
    (okB r (x, y, z) && hrowB (x, y, z)) = (gA r x && (gB r x y && gC r y z)) := by
  simp only [okB, hrowB, gA, gB, gC]
  generalize adjB r.1 y = b0
  generalize adjB r.2.1 z = b1
  generalize adjB r.2.1 x = b2
  generalize adjB r.2.2 y = b3
  generalize adjB x y = b4
  generalize adjB y z = b5
  revert b0 b1 b2 b3 b4 b5
  decide

lemma succ_eq (r : Fin 20 × Fin 20 × Fin 20) (hr : hrowB r = true) (g : Fin 20 × Fin 20 × Fin 20 → ℕ)
    (hg : ∀ s, hrowB s = false → g s = 0) :
    (∑ s : Fin 20 × Fin 20 × Fin 20, if hrow r ∧ ok r s then g s else 0) = succSum r g := by
  have e1 : ∀ s : Fin 20 × Fin 20 × Fin 20, (if hrow r ∧ ok r s then g s else 0) =
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

/-- The number of rows allowed below a row: 0 for an invalid row, otherwise 11 when
x(i,0) = x(i,2) and 9 otherwise. -/
def dtab (r : Fin 20 × Fin 20 × Fin 20) : ℕ :=
  if hrowB r = true then (if r.1 = r.2.2 then 11 else 9) else 0

set_option maxHeartbeats 4000000 in
lemma one_check : ∀ x y : Fin 20, adjB x y = true → ∀ z : Fin 20, adjB y z = true →
    succSum (x, y, z) (fun s => if hrowB s = true then 1 else 0) = dtab (x, y, z) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ x y : Fin 20, adjB x y = true → ∀ z : Fin 20, adjB y z = true →
    succSum (x, y, z) dtab + 12 = 11 * dtab (x, y, z) := by
  decide +kernel

lemma W_zero_fun : W 0 = fun s => if hrowB s = true then 1 else 0 := funext W_zeroB

lemma W_one (r : Fin 20 × Fin 20 × Fin 20) : W 1 r = dtab r := by
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

lemma W_rec (n : ℕ) (r : Fin 20 × Fin 20 × Fin 20) :
    W (n + 2) r + 12 * W n r = 11 * W (n + 1) r := by
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

lemma a_rec (n : ℕ) : a (n + 3) + 12 * a (n + 1) = 11 * a (n + 2) := by
  rw [a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact W_rec n r
  · simp

lemma a_one : a 1 = 9 := by
  rw [a_succ]
  simp only [W_zeroB]
  decide +kernel

lemma a_two : a 2 = 87 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 3x(3 - 4x)/(1 - 11x + 12x^2). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 11 * X + 12 * X ^ 2) = 3 * X * (3 - 4 * X) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - 11 * X + 12 * X ^ 2) = A - A * X ^ 1 * C 11 + A * X ^ 2 * C 12 := by
    rw [show (11 : ℚ⟦X⟧) = C 11 from (map_ofNat C 11).symm,
      show (12 : ℚ⟦X⟧) = C 12 from (map_ofNat C 12).symm]
    ring
  have e2 : (3 : ℚ⟦X⟧) * X * (3 - 4 * X) = X ^ 1 * C 9 - X ^ 2 * C 12 := by
    rw [show (3 : ℚ⟦X⟧) = C 3 from (map_ofNat C 3).symm,
      show (4 : ℚ⟦X⟧) = C 4 from (map_ofNat C 4).symm, show (9 : ℚ) = 3 * 3 by norm_num,
      show (12 : ℚ) = 3 * 4 by norm_num, map_mul, map_mul]
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
    have hq : ((a (n + 3) : ℕ) : ℚ) + 12 * a (n + 1) = 11 * a (n + 2) := by exact_mod_cast h
    simp only [show ¬ (n + 3 = 0) by omega, show ¬ (n + 3 - 1 = 0) by omega, if_false,
      show 1 ≤ n + 3 by omega, show 2 ≤ n + 3 by omega, if_true, show ¬ (n + 3 = 1) by omega,
      show ¬ (n + 3 = 2) by omega, show n + 3 - 1 = n + 2 by omega,
      show n + 3 - 2 = n + 1 by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 1 = 0) by omega]
    linear_combination hq

/-- The bracket of Barker's closed form. -/
noncomputable def Gf (n : ℕ) : ℝ := (11 - Real.sqrt 73) ^ n * (-7 + Real.sqrt 73) + (7 + Real.sqrt 73) * (11 + Real.sqrt 73) ^ n

lemma Gf_rec (n : ℕ) : Gf (n + 2) = 22 * Gf (n + 1) - 48 * Gf n := by
  have s2 : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  unfold Gf
  have h1 : (11 - Real.sqrt 73) ^ 2 = 22 * (11 - Real.sqrt 73) - 48 := by
    linear_combination 1 * s2
  have h2 : (11 + Real.sqrt 73) ^ 2 = 22 * (11 + Real.sqrt 73) - 48 := by
    linear_combination 1 * s2
  rw [show (11 - Real.sqrt 73) ^ (n + 2) = (11 - Real.sqrt 73) ^ n * (11 - Real.sqrt 73) ^ 2 by ring,
    show (11 + Real.sqrt 73) ^ (n + 2) = (11 + Real.sqrt 73) ^ n * (11 + Real.sqrt 73) ^ 2 by ring]
  rw [h1, h2]
  ring

lemma Gf_zero : Gf 0 = 2 * Real.sqrt 73 := by
  have s2 : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (0) * s2

lemma Gf_one : Gf 1 = 36 * Real.sqrt 73 := by
  have s2 : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (0) * s2

lemma Gf_two : Gf 2 = 696 * Real.sqrt 73 := by
  rw [show (2 : ℕ) = 0 + 2 from rfl, Gf_rec, Gf_one, Gf_zero]
  ring

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) *
        ((11 - Real.sqrt 73) ^ n * (-7 + Real.sqrt 73) +
          (7 + Real.sqrt 73) * (11 + Real.sqrt 73) ^ n)) / Real.sqrt 73 := by
  have key : ∀ k, (a (k + 1) : ℝ) * 2 ^ (k + 2) * Real.sqrt 73 = 1 * Gf (k + 1) ∧
      (a (k + 2) : ℝ) * 2 ^ (k + 3) * Real.sqrt 73 = 1 * Gf (k + 2) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, Gf_one]; push_cast; ring
      · rw [a_two, Gf_two]; push_cast; ring
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ((a (k + 3) : ℕ) : ℝ) + 12 * a (k + 1) = 11 * a (k + 2) := by
        exact_mod_cast a_rec k
      have hg := Gf_rec (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hg
      show (a (k + 3) : ℝ) * 2 ^ (k + 4) * Real.sqrt 73 = 1 * Gf (k + 3)
      linear_combination (2 ^ (k + 4) * Real.sqrt 73) * hr + 22 * ih.2 - 48 * ih.1 - 1 * hg
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk := (key k).1
  have hz : (2 : ℝ) ^ (-1 - ((k + 1 : ℕ) : ℤ)) = 1 / 2 ^ (k + 2) := by
    rw [show -1 - ((k + 1 : ℕ) : ℤ) = -((k + 2 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
      zpow_natCast, one_div]
  have ha : (a (k + 1) : ℝ) = 1 * Gf (k + 1) / (2 ^ (k + 2) * Real.sqrt 73) := by
    rw [eq_div_iff (by positivity)]
    linear_combination hk
  show (a (k + 1) : ℝ) = (2 ^ (-1 - ((k + 1 : ℕ) : ℤ)) * Gf (k + 1)) / Real.sqrt 73
  rw [ha, hz]
  ring

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 11 * X + 12 * X ^ 2) =
      3 * X * (3 - 4 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) *
        ((11 - Real.sqrt 73) ^ n * (-7 + Real.sqrt 73) +
          (7 + Real.sqrt 73) * (11 + Real.sqrt 73) ^ n)) / Real.sqrt 73 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..10), from the recurrence and a(1), a(2). -/
theorem controls : a 1 = 9 ∧ a 2 = 87 ∧ a 3 = 849 ∧ a 4 = 8295 ∧ a 5 = 81057 ∧ a 6 = 792087 ∧ a 7 = 7740273 ∧ a 8 = 75637959 ∧ a 9 = 739134273 ∧ a 10 = 7222821495 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3; have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have h1 := a_one; have h2 := a_two
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7
  omega

/-- The icosahedron graph on the vertex numbering of `faces`. -/
def vedges : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (1, 6), (1, 10), (2, 3), (2, 6), (2, 7),
  (3, 4), (3, 7), (3, 8), (4, 5), (4, 8), (4, 9), (5, 9), (5, 10), (6, 7), (6, 10), (6, 11), (7, 8),
  (7, 11), (8, 9), (8, 11), (9, 10), (9, 11), (10, 11)]

/-- Controls on the faces: every listed triple is a triangle of the icosahedron graph, the 20
triples are distinct, and every face is adjacent to exactly 3 faces. -/
theorem graph_controls : faces.length = 20 ∧ faces.Nodup ∧
    (∀ t ∈ faces, (t.1, t.2.1) ∈ vedges ∧ (t.1, t.2.2) ∈ vedges ∧ (t.2.1, t.2.2) ∈ vedges) ∧
    ∀ x : Fin 20, ((univ : Finset (Fin 20)).filter (adj x)).card = 3 := by
  decide +kernel

end OMA.S_oeis_a223277

theorem OMA.solution : type_of% @OMA.S_oeis_a223277.main :=
  OMA.S_oeis_a223277.conjecture
