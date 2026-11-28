import OMAStatements.S_oeis_a232951

namespace OMA.S_oeis_a232951

open PowerSeries Finset








/-- Rows valid and consecutive rows compatible. -/
def Valid {n : ℕ} (f : Fin n → Fin 4 × Fin 4 × Fin 4 × Fin 4) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

/-- W(n, r): valid arrays with n + 1 rows whose first row is r. -/
def W (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : ℕ :=
  ((univ : Finset (Fin (n + 1) → Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter (fun f => Valid f ∧ f 0 = r)).card

lemma valid_cons {n : ℕ} (x : Fin 4 × Fin 4 × Fin 4 × Fin 4) (g : Fin (n + 1) → Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    Valid (Fin.cons x g : Fin (n + 2) → Fin 4 × Fin 4 × Fin 4 × Fin 4) ↔
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

lemma a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 4 × Fin 4 × Fin 4 × Fin 4, if r.1 = 0 then W n r else 0 := by
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

lemma W_zero (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : W 0 r = if hrow r then 1 else 0 := by
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
def consEmb (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    (Fin (n + 1) → Fin 4 × Fin 4 × Fin 4 × Fin 4) ↪ (Fin (n + 2) → Fin 4 × Fin 4 × Fin 4 × Fin 4) where
  toFun g := Fin.cons r g
  inj' g g' h := by
    funext i
    have := congrFun h i.succ
    simpa using this

lemma consEmb_apply (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) (g : Fin (n + 1) → Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    consEmb n r g = Fin.cons r g := rfl

lemma W_succ (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    W (n + 1) r = ∑ s : Fin 4 × Fin 4 × Fin 4 × Fin 4, if hrow r ∧ ok r s then W n s else 0 := by
  have e : ((univ : Finset (Fin (n + 2) → Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter
      (fun f => Valid f ∧ f 0 = r)) =
      (((univ : Finset (Fin (n + 1) → Fin 4 × Fin 4 × Fin 4 × Fin 4)).filter
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

/-- The adjacency as one bit mask: y is adjacent to x when bit 4 x + y of `MASK` is set. -/
def MASK : ℕ := 60855

/-- Fast adjacency. -/
def adjB (x y : Fin 4) : Bool := Nat.testBit MASK (4 * x.val + y.val)

set_option maxHeartbeats 4000000 in
lemma adj_iff : ∀ x y : Fin 4, adj x y ↔ adjB x y = true := by
  decide +kernel

/-- Fast row test. -/
def hrowB (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Bool := adjB r.1 r.2.1 && (adjB r.2.1 r.2.2.1 && (adjB r.2.2.1 r.2.2.2))

/-- Fast compatibility test. -/
def okB (r s : Fin 4 × Fin 4 × Fin 4 × Fin 4) : Bool :=
  adjB r.1 s.2.1 && (adjB r.2.1 s.2.2.1 && (adjB r.2.2.1 s.2.2.2 && (adjB r.2.1 s.1 && (adjB r.2.2.1 s.2.1 && (adjB r.2.2.2 s.2.2.1)))))

lemma hrow_iff (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : hrow r ↔ hrowB r = true := by
  simp only [hrow, hrowB, adj_iff, Bool.and_eq_true]

lemma ok_iff (r s : Fin 4 × Fin 4 × Fin 4 × Fin 4) : ok r s ↔ okB r s = true := by
  simp only [ok, okB, adj_iff, Bool.and_eq_true]

lemma W_invalid (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) (h : hrowB r = false) : W n r = 0 := by
  unfold W
  rw [Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  rintro ⟨⟨h1, _⟩, h0⟩
  have h2 := (hrow_iff r).1 (h0 ▸ h1 0)
  rw [h] at h2
  exact Bool.false_ne_true h2

lemma W_zeroB (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : W 0 r = if hrowB r = true then 1 else 0 := by
  rw [W_zero]
  by_cases hr : hrowB r = true
  · rw [if_pos hr, if_pos ((hrow_iff r).2 hr)]
  · rw [if_neg hr, if_neg (fun h => hr ((hrow_iff r).1 h))]

/-- The labels adjacent to c. -/
def N (c : Fin 4) : Finset (Fin 4) := univ.filter (fun y => adjB c y = true)

lemma sum_N (c : Fin 4) (F : Fin 4 → ℕ) :
    ∑ y ∈ N c, F y = ∑ y : Fin 4, if adjB c y = true then F y else 0 :=
  Finset.sum_filter _ _

lemma ite_and (b1 b2 : Bool) (X : ℕ) :
    (if b1 = true then (if b2 = true then X else 0) else 0) = if (b1 && b2) = true then X else 0 := by
  cases b1 <;> cases b2 <;> rfl

/-- The sum of g over the valid rows allowed below r, enumerated entry by entry: each entry runs
over the neighbors of the entry before it (the first over the neighbors of an entry of r), and
the other conditions on it are tested. -/
def succSum (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) (g : Fin 4 × Fin 4 × Fin 4 × Fin 4 → ℕ) : ℕ :=
  ∑ x ∈ N r.2.1, ∑ y ∈ N x, (if (adjB r.1 y && (adjB r.2.2.1 y)) = true then ∑ z ∈ N y, (if (adjB r.2.1 z && (adjB r.2.2.2 z)) = true then ∑ u ∈ N z, (if adjB r.2.2.1 u = true then g (x, y, z, u) else 0) else 0) else 0)

lemma cond_split (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) (x y z u : Fin 4) :
    (okB r (x, y, z, u) && hrowB (x, y, z, u)) = (adjB r.2.1 x && ((adjB x y && (adjB r.1 y && (adjB r.2.2.1 y))) && ((adjB y z && (adjB r.2.1 z && (adjB r.2.2.2 z))) && ((adjB z u && (adjB r.2.2.1 u)))))) := by
  simp only [okB, hrowB]
  generalize adjB r.1 y = b0
  generalize adjB r.2.1 z = b1
  generalize adjB r.2.2.1 u = b2
  generalize adjB r.2.1 x = b3
  generalize adjB r.2.2.1 y = b4
  generalize adjB r.2.2.2 z = b5
  generalize adjB x y = b6
  generalize adjB y z = b7
  generalize adjB z u = b8
  revert b0 b1 b2 b3 b4 b5 b6 b7 b8
  decide

lemma succ_eq (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) (hr : hrowB r = true) (g : Fin 4 × Fin 4 × Fin 4 × Fin 4 → ℕ)
    (hg : ∀ s, hrowB s = false → g s = 0) :
    (∑ s : Fin 4 × Fin 4 × Fin 4 × Fin 4, if hrow r ∧ ok r s then g s else 0) = succSum r g := by
  have e1 : ∀ s : Fin 4 × Fin 4 × Fin 4 × Fin 4, (if hrow r ∧ ok r s then g s else 0) =
      if (okB r s && hrowB s) = true then g s else 0 := by
    intro s
    by_cases hs : hrowB s = true
    · simp [hrow_iff, ok_iff, hr, hs]
    · have h0 : g s = 0 := hg s (by simpa using hs)
      simp [h0]
  rw [Finset.sum_congr rfl (fun s _ => e1 s)]
  simp only [Fintype.sum_prod_type]
  unfold succSum
  simp only [sum_N, ite_and]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h0 : adjB r.2.1 x = true
  · rw [if_pos h0]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    by_cases h1 : (adjB x y && (adjB r.1 y && (adjB r.2.2.1 y))) = true
    · rw [if_pos h1]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      by_cases h2 : (adjB y z && (adjB r.2.1 z && (adjB r.2.2.2 z))) = true
      · rw [if_pos h2]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        by_cases h3 : (adjB z u && (adjB r.2.2.1 u)) = true
        · rw [if_pos h3]
          simp [cond_split, h0, h1, h2, h3]
        · rw [if_neg h3]
          simp [cond_split, h0, h1, h2, h3]
      · rw [if_neg h2]
        refine Finset.sum_eq_zero (fun u _ => ?_)
        simp [cond_split, h0, h1, h2]
    · rw [if_neg h1]
      refine Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun u _ => ?_))
      simp [cond_split, h0, h1]
  · rw [if_neg h0]
    refine Finset.sum_eq_zero (fun y _ => Finset.sum_eq_zero (fun z _ => Finset.sum_eq_zero (fun u _ => ?_)))
    simp [cond_split, h0]

/-- W(1, r) as a table (0 for an invalid row). -/
def tab1 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![41, 31, 31, 0], ![31, 25, 0, 21], ![31, 0, 25, 21], ![0, 0, 0, 0]], ![![31, 41, 31, 0], ![25, 31, 0, 21], ![0, 0, 0, 0], ![0, 31, 25, 21]], ![![31, 31, 41, 0], ![0, 0, 0, 0], ![25, 0, 31, 21], ![0, 25, 31, 21]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
    ![![![31, 25, 21, 0], ![41, 31, 0, 31], ![31, 0, 21, 25], ![0, 0, 0, 0]], ![![25, 31, 21, 0], ![31, 41, 0, 31], ![0, 0, 0, 0], ![0, 31, 21, 25]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![31, 31, 0, 41], ![25, 0, 21, 31], ![0, 25, 21, 31]]],
    ![![![31, 21, 25, 0], ![31, 21, 0, 25], ![41, 0, 31, 31], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![25, 21, 31, 0], ![0, 0, 0, 0], ![31, 0, 41, 31], ![0, 21, 31, 25]], ![![0, 0, 0, 0], ![25, 21, 0, 31], ![31, 0, 31, 41], ![0, 21, 25, 31]]],
    ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![21, 31, 25, 0], ![21, 31, 0, 25], ![0, 0, 0, 0], ![0, 41, 31, 31]], ![![21, 25, 31, 0], ![0, 0, 0, 0], ![21, 0, 31, 25], ![0, 31, 41, 31]], ![![0, 0, 0, 0], ![21, 25, 0, 31], ![21, 0, 25, 31], ![0, 31, 31, 41]]]]

/-- W(2, r) as a table (0 for an invalid row). -/
def tab2 : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ :=
  ![![![![1233, 925, 925, 0], ![925, 745, 0, 617], ![925, 0, 745, 617], ![0, 0, 0, 0]], ![![925, 1233, 925, 0], ![745, 925, 0, 617], ![0, 0, 0, 0], ![0, 925, 745, 617]], ![![925, 925, 1233, 0], ![0, 0, 0, 0], ![745, 0, 925, 617], ![0, 745, 925, 617]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]]],
    ![![![925, 745, 617, 0], ![1233, 925, 0, 925], ![925, 0, 617, 745], ![0, 0, 0, 0]], ![![745, 925, 617, 0], ![925, 1233, 0, 925], ![0, 0, 0, 0], ![0, 925, 617, 745]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![925, 925, 0, 1233], ![745, 0, 617, 925], ![0, 745, 617, 925]]],
    ![![![925, 617, 745, 0], ![925, 617, 0, 745], ![1233, 0, 925, 925], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![745, 617, 925, 0], ![0, 0, 0, 0], ![925, 0, 1233, 925], ![0, 617, 925, 745]], ![![0, 0, 0, 0], ![745, 617, 0, 925], ![925, 0, 925, 1233], ![0, 617, 745, 925]]],
    ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]], ![![617, 925, 745, 0], ![617, 925, 0, 745], ![0, 0, 0, 0], ![0, 1233, 925, 925]], ![![617, 745, 925, 0], ![0, 0, 0, 0], ![617, 0, 925, 745], ![0, 925, 1233, 925]], ![![0, 0, 0, 0], ![617, 745, 0, 925], ![617, 0, 745, 925], ![0, 925, 925, 1233]]]]

/-- W(1, r). -/
def dtab (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : ℕ := if hrowB r = true then tab1 r.1 r.2.1 r.2.2.1 r.2.2.2 else 0

/-- W(2, r). -/
def dtab2 (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : ℕ := if hrowB r = true then tab2 r.1 r.2.1 r.2.2.1 r.2.2.2 else 0

set_option maxHeartbeats 4000000 in
lemma one_check : ∀ x y : Fin 4, adjB x y = true → ∀ z : Fin 4, adjB y z = true →
    ∀ u : Fin 4, adjB z u = true →
    succSum (x, y, z, u) (fun s => if hrowB s = true then 1 else 0) = dtab (x, y, z, u) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma two_check : ∀ x y : Fin 4, adjB x y = true → ∀ z : Fin 4, adjB y z = true →
    ∀ u : Fin 4, adjB z u = true → succSum (x, y, z, u) dtab = dtab2 (x, y, z, u) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma base_check : ∀ x y : Fin 4, adjB x y = true → ∀ z : Fin 4, adjB y z = true →
    ∀ u : Fin 4, adjB z u = true →
    succSum (x, y, z, u) dtab2 + 35 * dtab (x, y, z, u) = 31 * dtab2 (x, y, z, u) + 5 := by
  decide +kernel

lemma W_zero_fun : W 0 = fun s => if hrowB s = true then 1 else 0 := funext W_zeroB

lemma W_one (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : W 1 r = dtab r := by
  by_cases hr : hrowB r = true
  · rw [W_succ, succ_eq r hr (W 0) (W_invalid 0), W_zero_fun]
    obtain ⟨x, y, z, u⟩ := r
    have h := hr
    simp only [hrowB, Bool.and_eq_true] at h
    exact one_check x y h.1 z h.2.1 u h.2.2
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 1 r hf]
    simp [dtab, hf]

lemma W_one_fun : W 1 = dtab := funext W_one

lemma W_two (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) : W 2 r = dtab2 r := by
  by_cases hr : hrowB r = true
  · rw [show W 2 r = W (1 + 1) r from rfl, W_succ, succ_eq r hr (W 1) (W_invalid 1), W_one_fun]
    obtain ⟨x, y, z, u⟩ := r
    have h := hr
    simp only [hrowB, Bool.and_eq_true] at h
    exact two_check x y h.1 z h.2.1 u h.2.2
  · have hf : hrowB r = false := by simpa using hr
    rw [W_invalid 2 r hf]
    simp [dtab2, hf]

lemma W_two_fun : W 2 = dtab2 := funext W_two

lemma W_rec (n : ℕ) (r : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    W (n + 3) r + 35 * W (n + 1) r = 31 * W (n + 2) r + 5 * W n r := by
  induction n generalizing r with
  | zero =>
    by_cases hr : hrowB r = true
    · rw [show W (0 + 3) r = W (2 + 1) r from rfl, W_succ 2 r, succ_eq r hr (W 2) (W_invalid 2),
        show W (0 + 1) r = W 1 r from rfl, show W (0 + 2) r = W 2 r from rfl, W_two_fun, W_one,
        W_zeroB, if_pos hr]
      obtain ⟨x, y, z, u⟩ := r
      have h := hr
      simp only [hrowB, Bool.and_eq_true] at h
      simpa using base_check x y h.1 z h.2.1 u h.2.2
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

lemma a_rec (n : ℕ) : a (n + 4) + 35 * a (n + 2) = 31 * a (n + 3) + 5 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  by_cases hc : r.1 = 0
  · simp only [if_pos hc]
    exact W_rec n r
  · simp [hc]

set_option maxHeartbeats 4000000 in
lemma a_one : a 1 = 27 := by
  rw [a_succ]
  simp only [W_zeroB]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_two : a 2 = 771 := by
  rw [a_succ]
  simp only [W_one]
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma a_three : a 3 = 22971 := by
  rw [a_succ]
  simp only [W_two]
  decide +kernel

/-- The recurrence in the integers, from a(1) on. -/
lemma a_rec_int (n : ℕ) : (a (n + 4) : ℤ) = 31 * a (n + 3) - 35 * a (n + 2) + 5 * a (n + 1) := by
  have h := a_rec n
  have hz : ((a (n + 4) : ℕ) : ℤ) + 35 * a (n + 2) = 31 * a (n + 3) + 5 * a (n + 1) := by
    exact_mod_cast h
  linarith

/-- d(n) = a(n + 2) - 30 a(n + 1) + 5 a(n) = -24 for n >= 1. -/
lemma a_rec2 (k : ℕ) : (a (k + 3) : ℤ) = 30 * a (k + 2) - 5 * a (k + 1) - 24 := by
  induction k with
  | zero =>
    simp only [Nat.zero_add, a_one, a_two, a_three]
    norm_num
  | succ k ih =>
    rw [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl, a_rec_int k]
    linear_combination ih

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = 3x(9 - 22x + 5x^2)/((1 - x)(1 - 30x + 5x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 30 * X + 5 * X ^ 2)) = 3 * X * (9 - 22 * X + 5 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 30 * X + 5 * X ^ 2)) =
      A - A * X ^ 1 * C 31 + A * X ^ 2 * C 35 - A * X ^ 3 * C 5 := by
    rw [show (C (31 : ℚ) : ℚ⟦X⟧) = 31 from map_ofNat C 31,
      show (C (35 : ℚ) : ℚ⟦X⟧) = 35 from map_ofNat C 35,
      show (C (5 : ℚ) : ℚ⟦X⟧) = 5 from map_ofNat C 5]
    ring
  have e2 : (3 : ℚ⟦X⟧) * X * (9 - 22 * X + 5 * X ^ 2) = X ^ 1 * C 27 - X ^ 2 * C 66 + X ^ 3 * C 15 := by
    rw [show (C (27 : ℚ) : ℚ⟦X⟧) = 27 from map_ofNat C 27,
      show (C (66 : ℚ) : ℚ⟦X⟧) = 66 from map_ofNat C 66,
      show (C (15 : ℚ) : ℚ⟦X⟧) = 15 from map_ofNat C 15]
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
    have hq : ((a (n + 4) : ℕ) : ℚ) + 35 * a (n + 2) = 31 * a (n + 3) + 5 * a (n + 1) := by
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
  (15 - 2 * Real.sqrt 55) ^ n * (55 + Real.sqrt 55) - (-55 + Real.sqrt 55) * (15 + 2 * Real.sqrt 55) ^ n

lemma Gf_rec (n : ℕ) : Gf (n + 2) = 30 * Gf (n + 1) - 5 * Gf n := by
  have s2 : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (by norm_num)
  unfold Gf
  have h1 : (15 - 2 * Real.sqrt 55) ^ 2 = 30 * (15 - 2 * Real.sqrt 55) - 5 := by
    linear_combination 4 * s2
  have h2 : (15 + 2 * Real.sqrt 55) ^ 2 = 30 * (15 + 2 * Real.sqrt 55) - 5 := by
    linear_combination 4 * s2
  rw [show (15 - 2 * Real.sqrt 55) ^ (n + 2) = (15 - 2 * Real.sqrt 55) ^ n *
      (15 - 2 * Real.sqrt 55) ^ 2 by ring,
    show (15 + 2 * Real.sqrt 55) ^ (n + 2) = (15 + 2 * Real.sqrt 55) ^ n *
      (15 + 2 * Real.sqrt 55) ^ 2 by ring, h1, h2]
  ring

lemma Gf_one : Gf 1 = 1430 := by
  have s2 : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination (-4) * s2

lemma Gf_two : Gf 2 = 42350 := by
  have s2 : Real.sqrt 55 ^ 2 = 55 := Real.sq_sqrt (by norm_num)
  unfold Gf
  linear_combination 320 * s2

/-- Barker's closed form, for n >= 1. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (55 + (15 - 2 * Real.sqrt 55) ^ n * (55 + Real.sqrt 55) -
        (-55 + Real.sqrt 55) * (15 + 2 * Real.sqrt 55) ^ n) / 55 := by
  have key : ∀ k, (a (k + 1) : ℝ) = (55 + Gf (k + 1)) / 55 ∧
      (a (k + 2) : ℝ) = (55 + Gf (k + 2)) / 55 := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [a_one, Gf_one]; norm_num
      · rw [a_two, Gf_two]; norm_num
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr : ((a (k + 3) : ℕ) : ℝ) = 30 * a (k + 2) - 5 * a (k + 1) - 24 := by
        exact_mod_cast a_rec2 k
      have hg := Gf_rec (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at hg
      show (a (k + 3) : ℝ) = (55 + Gf (k + 3)) / 55
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
      ((1 - X) * (1 - 30 * X + 5 * X ^ 2)) = 3 * X * (9 - 22 * X + 5 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (55 + (15 - 2 * Real.sqrt 55) ^ n * (55 + Real.sqrt 55) -
        (-55 + Real.sqrt 55) * (15 + 2 * Real.sqrt 55) ^ n) / 55 :=
  ⟨gf, closed_form⟩

/-- Controls: the entry's terms a(1..12), from the recurrence and a(1), a(2), a(3). -/
theorem controls : a 1 = 27 ∧ a 2 = 771 ∧ a 3 = 22971 ∧ a 4 = 685251 ∧ a 5 = 20442651 ∧ a 6 = 609853251 ∧ a 7 = 18193384251 ∧ a 8 = 542752261251 ∧ a 9 = 16191600916251 ∧ a 10 = 483034266181251 ∧ a 11 = 14410069980856251 ∧ a 12 = 429886928094781251 := by
  have r0 := a_rec 0; have r1 := a_rec 1; have r2 := a_rec 2; have r3 := a_rec 3
  have r4 := a_rec 4; have r5 := a_rec 5; have r6 := a_rec 6; have r7 := a_rec 7
  have r8 := a_rec 8
  have h1 := a_one; have h2 := a_two; have h3 := a_three
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7 r8
  omega

end OMA.S_oeis_a232951

theorem OMA.solution : type_of% @OMA.S_oeis_a232951.main :=
  OMA.S_oeis_a232951.conjecture
