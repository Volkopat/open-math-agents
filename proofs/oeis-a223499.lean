import OMAStatements.S_oeis_a223499

namespace OMA.S_oeis_a223499

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

/-- The adjacency as one bit mask: y is adjacent to x when bit 6 x + y of `MASK` is set. -/
def MASK : ℕ := 30782403918

/-- Fast adjacency. -/
def adjB (x y : Fin 6) : Bool := Nat.testBit MASK (6 * x.val + y.val)

set_option maxHeartbeats 4000000 in
lemma adj_iff : ∀ x y : Fin 6, adj x y ↔ adjB x y = true := by
  decide +kernel

/-- Fast row test. -/
def hrowB (r : Fin 6 × Fin 6 × Fin 6) : Bool := adjB r.1 r.2.1 && adjB r.2.1 r.2.2

/-- Fast compatibility test. -/
def okB (r s : Fin 6 × Fin 6 × Fin 6) : Bool := adjB r.1 s.2.1 && (adjB r.2.1 s.2.2 && (adjB r.2.1 s.1 && (adjB r.2.2 s.2.1)))

lemma hrow_iff (r : Fin 6 × Fin 6 × Fin 6) : hrow r ↔ hrowB r = true := by
  simp only [hrow, hrowB, adj_iff, Bool.and_eq_true]

lemma ok_iff (r s : Fin 6 × Fin 6 × Fin 6) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, adj_iff, Bool.and_eq_true]

lemma W_invalid (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) (h : hrowB r = false) : W n r = 0 := by
  unfold W
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, _⟩, h0⟩
  have h2 := (hrow_iff r).1 (h0 ▸ h1 0)
  rw [h] at h2
  exact Bool.false_ne_true h2

lemma W_zeroB (r : Fin 6 × Fin 6 × Fin 6) : W 0 r = if hrowB r = true then 1 else 0 := by
  rw [W_zero]
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos ((hrow_iff r).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((hrow_iff r).1 h))]

/-- The guards of the rows s = (x, y, z) allowed below r, entry by entry: `gA` tests x alone,
`gB` the conditions on y given x, `gC` those on z given y. -/
def gA (r : Fin 6 × Fin 6 × Fin 6) (x : Fin 6) : Bool := adjB r.2.1 x

/-- See `gA`. -/
def gB (r : Fin 6 × Fin 6 × Fin 6) (x y : Fin 6) : Bool := adjB r.1 y && (adjB r.2.2 y && adjB x y)

/-- See `gA`. -/
def gC (r : Fin 6 × Fin 6 × Fin 6) (y z : Fin 6) : Bool := adjB r.2.1 z && adjB y z

/-- The sum of g over the valid rows allowed below r, enumerated entry by entry. -/
def succSum (r : Fin 6 × Fin 6 × Fin 6) (g : Fin 6 × Fin 6 × Fin 6 → ℕ) : ℕ :=
  ∑ x : Fin 6, if gA r x = true then ∑ y : Fin 6, (if gB r x y = true then
    ∑ z : Fin 6, (if gC r y z = true then g (x, y, z) else 0) else 0) else 0

lemma cond_split (r : Fin 6 × Fin 6 × Fin 6) (x y z : Fin 6) :
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

lemma succ_eq (r : Fin 6 × Fin 6 × Fin 6) (hr : hrowB r = true) (g : Fin 6 × Fin 6 × Fin 6 → ℕ)
    (hg : ∀ s, hrowB s = false → g s = 0) :
    (∑ s : Fin 6 × Fin 6 × Fin 6, if hrow r ∧ ok r s then g s else 0) = succSum r g := by
  have e1 : ∀ s : Fin 6 × Fin 6 × Fin 6, (if hrow r ∧ ok r s then g s else 0) =
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

/-- W(1, r) as a table (0 for an invalid row). -/
def tab1 : Fin 6 → Fin 6 → Fin 6 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0], ![14, 0, 9, 0, 13, 0], ![14, 9, 0, 0, 0, 13], ![17, 0, 0, 0, 13, 13], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]],
    ![![0, 14, 9, 13, 0, 0], ![0, 0, 0, 0, 0, 0], ![9, 14, 0, 0, 0, 13], ![0, 0, 0, 0, 0, 0], ![0, 17, 0, 13, 0, 13], ![0, 0, 0, 0, 0, 0]],
    ![![0, 9, 14, 13, 0, 0], ![9, 0, 14, 0, 13, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 17, 13, 13, 0]],
    ![![0, 13, 13, 17, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 13, 0, 14, 0, 9], ![0, 0, 13, 14, 9, 0]],
    ![![0, 0, 0, 0, 0, 0], ![13, 0, 13, 0, 17, 0], ![0, 0, 0, 0, 0, 0], ![13, 0, 0, 0, 14, 9], ![0, 0, 0, 0, 0, 0], ![0, 0, 13, 9, 14, 0]],
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![13, 13, 0, 0, 0, 17], ![13, 0, 0, 0, 9, 14], ![0, 13, 0, 9, 0, 14], ![0, 0, 0, 0, 0, 0]]]

/-- W(2, r) as a table (0 for an invalid row). -/
def tab2 : Fin 6 → Fin 6 → Fin 6 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0], ![186, 0, 115, 0, 172, 0], ![186, 115, 0, 0, 0, 172], ![229, 0, 0, 0, 172, 172], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]],
    ![![0, 186, 115, 172, 0, 0], ![0, 0, 0, 0, 0, 0], ![115, 186, 0, 0, 0, 172], ![0, 0, 0, 0, 0, 0], ![0, 229, 0, 172, 0, 172], ![0, 0, 0, 0, 0, 0]],
    ![![0, 115, 186, 172, 0, 0], ![115, 0, 186, 0, 172, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 229, 172, 172, 0]],
    ![![0, 172, 172, 229, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![0, 172, 0, 186, 0, 115], ![0, 0, 172, 186, 115, 0]],
    ![![0, 0, 0, 0, 0, 0], ![172, 0, 172, 0, 229, 0], ![0, 0, 0, 0, 0, 0], ![172, 0, 0, 0, 186, 115], ![0, 0, 0, 0, 0, 0], ![0, 0, 172, 115, 186, 0]],
    ![![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0], ![172, 172, 0, 0, 0, 229], ![172, 0, 0, 0, 115, 186], ![0, 172, 0, 115, 0, 186], ![0, 0, 0, 0, 0, 0]]]

/-- W(1, r). -/
def dtab (r : Fin 6 × Fin 6 × Fin 6) : ℕ := if hrowB r = true then tab1 r.1 r.2.1 r.2.2 else 0

/-- W(2, r). -/
def dtab2 (r : Fin 6 × Fin 6 × Fin 6) : ℕ := if hrowB r = true then tab2 r.1 r.2.1 r.2.2 else 0

set_option maxHeartbeats 4000000 in
lemma one_check : ∀ x y : Fin 6, adjB x y = true → ∀ z : Fin 6, adjB y z = true →
    succSum (x, y, z) (fun s => if hrowB s = true then 1 else 0) = dtab (x, y, z) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma two_check : ∀ x y : Fin 6, adjB x y = true → ∀ z : Fin 6, adjB y z = true →
    succSum (x, y, z) dtab = dtab2 (x, y, z) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ x y : Fin 6, adjB x y = true → ∀ z : Fin 6, adjB y z = true →
    succSum (x, y, z) dtab2 + 24 * dtab (x, y, z) = 15 * dtab2 (x, y, z) + 10 := by
  decide +kernel

lemma W_zero_fun : W 0 = fun s => if hrowB s = true then 1 else 0 := funext W_zeroB

lemma W_one (r : Fin 6 × Fin 6 × Fin 6) : W 1 r = dtab r := by
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

lemma W_two (r : Fin 6 × Fin 6 × Fin 6) : W 2 r = dtab2 r := by
  by_cases hr : hrowB r = true
  · rw [show W 2 r = W (1 + 1) r from rfl, W_succ, succ_eq r hr (W 1) (W_invalid 1), W_one_fun]
    obtain ⟨x, y, z⟩ := r
    have h := hr
    simp only [hrowB, Bool.and_eq_true] at h
    exact two_check x y h.1 z h.2
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 2 r hf]
    simp [dtab2, hf]

lemma W_two_fun : W 2 = dtab2 := funext W_two

lemma W_rec (n : ℕ) (r : Fin 6 × Fin 6 × Fin 6) :
    W (n + 3) r + 24 * W (n + 1) r = 15 * W (n + 2) r + 10 * W n r := by
  induction n generalizing r with
  | zero =>
    by_cases hr : hrowB r = true
    · rw [show W (0 + 3) r = W (2 + 1) r from rfl, W_succ 2 r, succ_eq r hr (W 2) (W_invalid 2),
        show W (0 + 1) r = W 1 r from rfl, show W (0 + 2) r = W 2 r from rfl, W_two_fun, W_one,
        W_zeroB, if_pos hr]
      obtain ⟨x, y, z⟩ := r
      have h := hr
      simp only [hrowB, Bool.and_eq_true] at h
      simpa using base_check x y h.1 z h.2
    · have hf : hrowB r = false := by simpa using hr
      rw [W_invalid _ r hf, W_invalid _ r hf, W_invalid _ r hf, W_invalid _ r hf]
  | succ n ih =>
    rw [W_succ (n + 3), W_succ (n + 1), W_succ (n + 2), W_succ n]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    by_cases hc : hrow r ∧ ok r s
    · simp only [if_pos hc]
      exact ih s
    · simp [hc]

lemma a_rec (n : ℕ) : a (n + 4) + 24 * a (n + 2) = 15 * a (n + 3) + 10 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hc : r.1 = 0
  · simp only [if_pos hc]
    exact W_rec n r
  · simp [hc]

set_option maxHeartbeats 4000000 in
lemma a_one : a 1 = 9 := by
  rw [a_succ]
  simp only [W_zeroB]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_two : a 2 = 115 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_three : a 3 = 1519 := by
  rw [a_succ]
  simp only [W_two]
  decide +kernel

lemma a_rec_int (n : ℕ) : (a (n + 4) : ℤ) = 15 * a (n + 3) - 24 * a (n + 2) + 10 * a (n + 1) := by
  have h := a_rec n
  have hz : ((a (n + 4) : ℕ) : ℤ) + 24 * a (n + 2) = 15 * a (n + 3) + 10 * a (n + 1) := by
    exact_mod_cast h
  linarith

/-- a(n + 2) - 14 a(n + 1) + 10 a(n) = -1 for n >= 1. -/
lemma a_rec2 (k : ℕ) : (a (k + 3) : ℤ) = 14 * a (k + 2) - 10 * a (k + 1) - 1 := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, a_one, a_two, a_three]
    norm_num
  | succ k ih =>
    rw [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl, a_rec_int k]
    linear_combination ih

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(9 - 20x + 10x^2)/((1 - x)(1 - 14x + 10x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 14 * X + 10 * X ^ 2)) = X * (9 - 20 * X + 10 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 14 * X + 10 * X ^ 2)) =
      A - A * X ^ 1 * C 15 + A * X ^ 2 * C 24 - A * X ^ 3 * C 10 := by
    rw [show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15,
      show (C (24 : ℚ) : ℚ⟦X⟧) = 24 from map_ofNat C 24,
      show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10]
    ring
  have e2 : (X : ℚ⟦X⟧) * (9 - 20 * X + 10 * X ^ 2) = X ^ 1 * C 9 - X ^ 2 * C 20 + X ^ 3 * C 10 := by
    rw [show (C (9 : ℚ) : ℚ⟦X⟧) = 9 from map_ofNat C 9,
      show (C (20 : ℚ) : ℚ⟦X⟧) = 20 from map_ofNat C 20,
      show (C (10 : ℚ) : ℚ⟦X⟧) = 10 from map_ofNat C 10]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · have h := a_rec n
    have hq : ((a (n + 4) : ℕ) : ℚ) + 24 * a (n + 2) = 15 * a (n + 3) + 10 * a (n + 1) := by
      exact_mod_cast h
    simp only [show ¬ (n + 4 = 0) by omega, show ¬ (n + 4 - 1 = 0) by omega, if_false,
      show 1 ≤ n + 4 by omega, show 2 ≤ n + 4 by omega, show 3 ≤ n + 4 by omega, if_true,
      show ¬ (n + 4 = 1) by omega, show ¬ (n + 4 = 2) by omega, show ¬ (n + 4 = 3) by omega,
      show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
      show n + 4 - 3 = n + 1 by omega, show ¬ (n + 3 = 0) by omega, show ¬ (n + 2 = 0) by omega,
      show ¬ (n + 1 = 0) by omega]
    linear_combination hq

/-- The conjugate part of Barker's closed form. -/
noncomputable def Gf (n : ℕ) : ℝ :=
  (13 - 2 * Real.sqrt 39) * (7 - Real.sqrt 39) ^ n + (7 + Real.sqrt 39) ^ n * (13 + 2 * Real.sqrt 39)

lemma Gf_rec (n : ℕ) : Gf (n + 2) = 14 * Gf (n + 1) - 10 * Gf n := by
  have s2 : Real.sqrt 39 ^ 2 = 39 := Real.sq_sqrt (by norm_num)
  unfold Gf
  have h1 : (7 - Real.sqrt 39) ^ 2 = 14 * (7 - Real.sqrt 39) - 10 := by linear_combination s2
  have h2 : (7 + Real.sqrt 39) ^ 2 = 14 * (7 + Real.sqrt 39) - 10 := by linear_combination s2
  rw [show (7 - Real.sqrt 39) ^ (n + 2) = (7 - Real.sqrt 39) ^ n * (7 - Real.sqrt 39) ^ 2 by ring,
    show (7 + Real.sqrt 39) ^ (n + 2) = (7 + Real.sqrt 39) ^ n * (7 + Real.sqrt 39) ^ 2 by ring,
    h1, h2]
  ring

lemma Gf_zero : Gf 0 = 26 := by
  unfold Gf
  ring

lemma Gf_one : Gf 1 = 338 := by
  have s2 : Real.sqrt 39 ^ 2 = 39 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination 4 * s2

lemma Gf_two : Gf 2 = 4472 := by
  rw [show Gf 2 = Gf (0 + 2) from rfl, Gf_rec, show Gf (0 + 1) = Gf 1 from rfl, Gf_one, Gf_zero]
  norm_num

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (13 + (13 - 2 * Real.sqrt 39) * (7 - Real.sqrt 39) ^ n +
        (7 + Real.sqrt 39) ^ n * (13 + 2 * Real.sqrt 39)) / 39 := by
  have key : ∀ k, (a (k + 1) : ℝ) = (13 + Gf (k + 1)) / 39 ∧
      (a (k + 2) : ℝ) = (13 + Gf (k + 2)) / 39 := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, Gf_one]; norm_num
      · rw [a_two, Gf_two]; norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ((a (k + 3) : ℕ) : ℝ) = 14 * a (k + 2) - 10 * a (k + 1) - 1 := by
        exact_mod_cast a_rec2 k
      have hg := Gf_rec (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hg
      show (a (k + 3) : ℝ) = (13 + Gf (k + 3)) / 39
      rw [hr, ih.1, ih.2, hg]
      ring
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [(key k).1]
  unfold Gf
  ring

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 14 * X + 10 * X ^ 2)) = X * (9 - 20 * X + 10 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (13 + (13 - 2 * Real.sqrt 39) * (7 - Real.sqrt 39) ^ n +
        (7 + Real.sqrt 39) ^ n * (13 + 2 * Real.sqrt 39)) / 39 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..12), from the recurrence and a(1), a(2), a(3). -/
theorem controls : a 1 = 9 ∧ a 2 = 115 ∧ a 3 = 1519 ∧ a 4 = 20115 ∧ a 5 = 266419 ∧ a 6 = 3528715 ∧ a 7 = 46737819 ∧ a 8 = 619042315 ∧ a 9 = 8199214219 ∧ a 10 = 108598575915 ∧ a 11 = 1438387920619 ∧ a 12 = 19051445129515 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3
  have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have r8 := a_rec 8
  have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

/-- Controls on the graph: 9 edges, every label has 3 neighbors. -/
theorem graph_controls : edges.length = 9 ∧
    ∀ x : Fin 6, ((univ : Finset (Fin 6)).filter (adj x)).card = 3 := by
  decide +kernel

end OMA.S_oeis_a223499

theorem OMA.solution : type_of% @OMA.S_oeis_a223499.main :=
  OMA.S_oeis_a223499.conjecture
