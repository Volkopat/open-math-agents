import OMAStatements.S_oeis_a302180

namespace OMA.S_oeis_a302180




/-! ### Free walks and the reflection principle -/

/-- The ±1 sequences of length k with sum -u. -/
def bin1 : ℕ → ℤ → ℤ
  | 0, u => if u = 0 then 1 else 0
  | k + 1, u => bin1 k (u + 1) + bin1 k (u - 1)

lemma bin1_neg : ∀ (k : ℕ) (u : ℤ), bin1 k (-u) = bin1 k u
  | 0, u => by simp [bin1]
  | k + 1, u => by
    rw [bin1, bin1, show -u + 1 = -(u - 1) by ring, show -u - 1 = -(u + 1) by ring, bin1_neg k, bin1_neg k,
      add_comm]

lemma bin1_high : ∀ (k q : ℕ), bin1 k (k + 2 * q + 2) = 0
  | 0, q => by
    rw [bin1, if_neg (by omega)]
  | k + 1, q => by
    rw [bin1, show ((k + 1 : ℕ) : ℤ) + 2 * q + 2 + 1 = k + 2 * ((q + 1 : ℕ) : ℤ) + 2 by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) + 2 * q + 2 - 1 = k + 2 * (q : ℤ) + 2 by push_cast; ring, bin1_high k, bin1_high k,
      add_zero]

lemma bin1_choose : ∀ (k p : ℕ), bin1 k (k - 2 * p) = k.choose p
  | 0, p => by
    rcases p with _ | p
    · simp [bin1]
    · rw [bin1, if_neg (by omega), Nat.choose_zero_succ, Nat.cast_zero]
  | k + 1, p => by
    rw [bin1]
    rcases p with _ | p
    · rw [show ((k + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) + 1 = k + 2 * ((0 : ℕ) : ℤ) + 2 by push_cast; ring,
        show ((k + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) - 1 = k - 2 * ((0 : ℕ) : ℤ) by push_cast; ring,
        bin1_high k, bin1_choose k]
      simp
    · rw [show ((k + 1 : ℕ) : ℤ) - 2 * ((p + 1 : ℕ) : ℤ) + 1 = k - 2 * (p : ℤ) by push_cast; ring,
        show ((k + 1 : ℕ) : ℤ) - 2 * ((p + 1 : ℕ) : ℤ) - 1 = k - 2 * ((p + 1 : ℕ) : ℤ) by push_cast; ring,
        bin1_choose k, bin1_choose k, Nat.choose_succ_succ', Nat.cast_add]

lemma bin1_odd : ∀ (k : ℕ) (j : ℤ), bin1 k (k - 2 * j - 1) = 0
  | 0, j => by
    rw [bin1, if_neg (by omega)]
  | k + 1, j => by
    rw [bin1, show ((k + 1 : ℕ) : ℤ) - 2 * j - 1 + 1 = k - 2 * (j - 1) - 1 by push_cast; ring,
      show ((k + 1 : ℕ) : ℤ) - 2 * j - 1 - 1 = k - 2 * j - 1 by push_cast; ring, bin1_odd k, bin1_odd k,
      add_zero]

/-- Free walks with the four steps ±x, ±y from (h, y) to the origin in k steps: in the coordinates
x + y and x - y they are two independent ±1 walks. -/
def P (k : ℕ) (h y : ℤ) : ℤ := bin1 k (h + y) * bin1 k (h - y)

lemma P_succ (k : ℕ) (h y : ℤ) :
    P (k + 1) h y = P k (h + 1) y + P k (h - 1) y + P k h (y + 1) + P k h (y - 1) := by
  simp only [P, bin1]
  rw [show h + 1 + y = h + y + 1 by ring, show h + 1 - y = h - y + 1 by ring,
    show h - 1 + y = h + y - 1 by ring, show h - 1 - y = h - y - 1 by ring,
    show h + (y + 1) = h + y + 1 by ring, show h - (y + 1) = h - y - 1 by ring,
    show h + (y - 1) = h + y - 1 by ring, show h - (y - 1) = h - y + 1 by ring]
  ring

/-- The walks from (h, y) that keep x ≥ 0, by reflection in x = -1. -/
def AB (k : ℕ) (h y : ℤ) : ℤ := P k h y - P k (h + 2) y

lemma AB_succ (k : ℕ) (h y : ℤ) :
    AB (k + 1) h y = AB k (h + 1) y + AB k (h - 1) y + AB k h (y + 1) + AB k h (y - 1) := by
  simp only [AB, P_succ]
  rw [show h + 2 + 1 = h + 1 + 2 by ring, show h + 2 - 1 = h + 1 by ring, show h - 1 + 2 = h + 1 by ring]
  ring

lemma AB_neg_one (k : ℕ) (y : ℤ) : AB k (-1) y = 0 := by
  simp only [AB, P]
  rw [show (-1 : ℤ) + y = -(1 - y) by ring, show (-1 : ℤ) - y = -(1 + y) by ring, bin1_neg, bin1_neg,
    show (-1 : ℤ) + 2 = 1 by norm_num]
  ring

/-! ### Back to the origin: only even lengths of the x, y part -/

/-- The 2D walks of type ab of length 2i: C(2i, i)^2 - C(2i, i+1)^2 = Cat(i) C(2i+1, i). -/
def w (i : ℕ) : ℤ := ((2 * i).choose i : ℤ) ^ 2 - ((2 * i).choose (i + 1) : ℤ) ^ 2

lemma AB_even (i : ℕ) : AB (2 * i) 0 0 = w i := by
  have h0 : bin1 (2 * i) 0 = (2 * i).choose i := by
    have := bin1_choose (2 * i) i
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * (i : ℤ) = 0 by push_cast; ring] at this
  have h2 : bin1 (2 * i) 2 = (2 * i).choose (i + 1) := by
    have := bin1_choose (2 * i) (i + 1)
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * ((i + 1 : ℕ) : ℤ) = -2 by push_cast; ring, bin1_neg] at this
  simp only [AB, P, w, add_zero, sub_zero, zero_add, h0, h2]
  ring

lemma AB_odd (i : ℕ) : AB (2 * i + 1) 0 0 = 0 := by
  have h0 : bin1 (2 * i + 1) 0 = 0 := by
    have := bin1_odd (2 * i + 1) i
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * (i : ℤ) - 1 = 0 by push_cast; ring] at this
  have h2 : bin1 (2 * i + 1) 2 = 0 := by
    have := bin1_odd (2 * i + 1) (i - 1)
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * ((i : ℤ) - 1) - 1 = 2 by push_cast; ring] at this
  simp only [AB, P, add_zero, sub_zero, zero_add, h0, h2]
  ring

lemma sum_even (g : ℕ → ℤ) (hg : ∀ i, g (2 * i + 1) = 0) :
    ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N), g k = ∑ i ∈ Finset.range N, g (2 * i)
  | 0 => by simp
  | N + 1 => by
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, sum_even g hg N,
      hg, add_zero, Finset.sum_range_succ]

/-! ### The point after a first step, and the one-way steps as a binomial transform -/

lemma pt_zero {n : ℕ} (w : Fin n → Fin 5) : pt w 0 = 0 := by
  simp [pt]

lemma pt_cons {n : ℕ} (c : Fin 5) (w : Fin n → Fin 5) (t : ℕ) :
    pt (Fin.cons c w : Fin (n + 1) → Fin 5) (t + 1) = step c + pt w t := by
  simp [pt, Fin.sum_univ_succ]

/-- The binomial transform: the +z steps are placed freely among the n steps. -/
def T (n : ℕ) (f : ℕ → ℤ) : ℤ := ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f k

lemma T_succ (n : ℕ) (f : ℕ → ℤ) : T (n + 1) f = T n (fun k => f (k + 1)) + T n f := by
  have h1 : T (n + 1) f = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * f (k + 1) +
      ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℤ) * f (k + 1) + f 0 := by
    rw [T, Finset.sum_range_succ', ← Finset.sum_add_distrib]
    simp only [Nat.choose_succ_succ', Nat.choose_zero_right, Nat.cast_add, Nat.cast_one, one_mul, add_mul]
  have h2 : T n f = ∑ k ∈ Finset.range n, (n.choose (k + 1) : ℤ) * f (k + 1) + f 0 := by
    rw [T, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  have h3 : ∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℤ) * f (k + 1) =
      ∑ k ∈ Finset.range n, (n.choose (k + 1) : ℤ) * f (k + 1) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  rw [h1, h2, h3, T]
  ring

/-! ### The quadrant: reflection in x = -1 and in y = -1 -/

lemma AB_neg (k : ℕ) (h y : ℤ) : AB k h (-y) = AB k h y := by
  simp only [AB, P]
  rw [show h + -y = h - y by ring, show h - -y = h + y by ring, show h + 2 + -y = h + 2 - y by ring,
    show h + 2 - -y = h + 2 + y by ring]
  ring

/-- The walks from (h, y) that keep x ≥ 0 and y ≥ 0: the half-plane count reflected in y = -1. -/
def QQ (k : ℕ) (h y : ℤ) : ℤ := AB k h y - AB k h (y + 2)

lemma QQ_succ (k : ℕ) (h y : ℤ) :
    QQ (k + 1) h y = QQ k (h + 1) y + QQ k (h - 1) y + QQ k h (y + 1) + QQ k h (y - 1) := by
  simp only [QQ, AB_succ]
  rw [show y + 2 + 1 = y + 1 + 2 by ring, show y + 2 - 1 = y + 1 by ring, show y - 1 + 2 = y + 1 by ring]
  ring

lemma QQ_neg_one_x (k : ℕ) (y : ℤ) : QQ k (-1) y = 0 := by
  simp [QQ, AB_neg_one]

lemma QQ_neg_one_y (k : ℕ) (h : ℤ) : QQ k h (-1) = 0 := by
  rw [QQ, show (-1 : ℤ) + 2 = 1 by norm_num, AB_neg k h 1, sub_self]

/-- The quadrant walks of type aa of length 2i: C(2i, i)^2 - 2 C(2i, i+1)^2 + C(2i, i) C(2i, i+2), which is
Cat(i) Cat(i+1). -/
def q (i : ℕ) : ℤ :=
  ((2 * i).choose i : ℤ) ^ 2 - 2 * ((2 * i).choose (i + 1) : ℤ) ^ 2 +
    ((2 * i).choose i : ℤ) * ((2 * i).choose (i + 2) : ℤ)

lemma QQ_even (i : ℕ) : QQ (2 * i) 0 0 = q i := by
  have h0 : bin1 (2 * i) 0 = (2 * i).choose i := by
    have := bin1_choose (2 * i) i
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * (i : ℤ) = 0 by push_cast; ring] at this
  have hm2 : bin1 (2 * i) (-2) = (2 * i).choose (i + 1) := by
    have := bin1_choose (2 * i) (i + 1)
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * ((i + 1 : ℕ) : ℤ) = -2 by push_cast; ring] at this
  have h2 : bin1 (2 * i) 2 = (2 * i).choose (i + 1) := by
    rw [← hm2, ← bin1_neg (2 * i) 2]
  have h4 : bin1 (2 * i) 4 = (2 * i).choose (i + 2) := by
    have := bin1_choose (2 * i) (i + 2)
    rwa [show ((2 * i : ℕ) : ℤ) - 2 * ((i + 2 : ℕ) : ℤ) = -4 by push_cast; ring, bin1_neg] at this
  have e : QQ (2 * i) 0 0 = bin1 (2 * i) 0 * bin1 (2 * i) 0 - bin1 (2 * i) 2 * bin1 (2 * i) 2 -
      (bin1 (2 * i) 2 * bin1 (2 * i) (-2) - bin1 (2 * i) 4 * bin1 (2 * i) 0) := by
    simp only [QQ, AB, P]
    norm_num
  rw [e, h0, h2, hm2, h4, q]
  ring

lemma QQ_odd (i : ℕ) : QQ (2 * i + 1) 0 0 = 0 := by
  have hz : ∀ j : ℤ, bin1 (2 * i + 1) (2 * (i - j)) = 0 := fun j => by
    have := bin1_odd (2 * i + 1) j
    rwa [show ((2 * i + 1 : ℕ) : ℤ) - 2 * j - 1 = 2 * (i - j) by push_cast; ring] at this
  have e : QQ (2 * i + 1) 0 0 = bin1 (2 * i + 1) 0 * bin1 (2 * i + 1) 0 -
      bin1 (2 * i + 1) 2 * bin1 (2 * i + 1) 2 -
      (bin1 (2 * i + 1) 2 * bin1 (2 * i + 1) (-2) - bin1 (2 * i + 1) 4 * bin1 (2 * i + 1) 0) := by
    simp only [QQ, AB, P]
    norm_num
  have h0 := hz i
  have h2 := hz (i - 1)
  rw [show 2 * ((i : ℤ) - i) = 0 by ring] at h0
  rw [show 2 * ((i : ℤ) - (i - 1)) = 2 by ring] at h2
  rw [e, h0, h2]
  ring

/-! ### Walks from any start: the first-step recursion -/

/-- The walks of n steps from the point (h, y, ·) that keep x ≥ 0 and y ≥ 0 and end with x = 0 and y = 0. -/
def cnt (n : ℕ) (h y : ℤ) : ℕ :=
  (Finset.univ.filter (fun w : Fin n → Fin 5 =>
    (∀ t ≤ n, 0 ≤ h + (pt w t).1 ∧ 0 ≤ y + (pt w t).2.1) ∧ h + (pt w n).1 = 0 ∧ y + (pt w n).2.1 = 0)).card

lemma a_eq_cnt (n : ℕ) : a n = cnt n 0 0 := by
  simp only [a, cnt, zero_add]

lemma cnt_neg (n : ℕ) {h y : ℤ} (hh : h < 0 ∨ y < 0) : cnt n h y = 0 := by
  rw [cnt, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ hw
  have h0 := hw.1 0 (Nat.zero_le _)
  rw [pt_zero] at h0
  simp only [Prod.fst_zero, Prod.snd_zero, add_zero] at h0
  omega

lemma cond_cons {n : ℕ} (c : Fin 5) (w : Fin n → Fin 5) (h y : ℤ) (hh : 0 ≤ h) (hy : 0 ≤ y) :
    ((∀ t ≤ n + 1, 0 ≤ h + (pt (Fin.cons c w : Fin (n + 1) → Fin 5) t).1 ∧
        0 ≤ y + (pt (Fin.cons c w : Fin (n + 1) → Fin 5) t).2.1) ∧
      h + (pt (Fin.cons c w : Fin (n + 1) → Fin 5) (n + 1)).1 = 0 ∧
      y + (pt (Fin.cons c w : Fin (n + 1) → Fin 5) (n + 1)).2.1 = 0) ↔
    ((∀ t ≤ n, 0 ≤ (h + (step c).1) + (pt w t).1 ∧ 0 ≤ (y + (step c).2.1) + (pt w t).2.1) ∧
      (h + (step c).1) + (pt w n).1 = 0 ∧ (y + (step c).2.1) + (pt w n).2.1 = 0) := by
  rw [pt_cons]
  simp only [Prod.fst_add, Prod.snd_add, ← add_assoc]
  refine and_congr ⟨fun H t ht => ?_, fun H t ht => ?_⟩ Iff.rfl
  · have := H (t + 1) (by omega)
    simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc] at this
    exact this
  · rcases t with _ | t
    · simp only [pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
      exact ⟨hh, hy⟩
    · simp only [pt_cons, Prod.fst_add, Prod.snd_add, ← add_assoc]
      exact H t (by omega)

lemma cnt_succ_sum (n : ℕ) (h y : ℤ) (hh : 0 ≤ h) (hy : 0 ≤ y) :
    cnt (n + 1) h y = ∑ c : Fin 5, cnt n (h + (step c).1) (y + (step c).2.1) := by
  rw [cnt, Finset.card_filter, ← (Fin.consEquiv (fun _ => Fin 5)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [cnt, Finset.card_filter]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  exact if_congr (cond_cons c w h y hh hy) rfl rfl

lemma cnt_succ (n : ℕ) (h y : ℤ) (hh : 0 ≤ h) (hy : 0 ≤ y) :
    (cnt (n + 1) h y : ℤ) = cnt n (h + 1) y + cnt n (h - 1) y + cnt n h (y + 1) + cnt n h (y - 1) +
      cnt n h y := by
  rw [cnt_succ_sum n h y hh hy, Fin.sum_univ_five]
  simp [step]
  ring_nf

lemma cnt_zero (h y : ℤ) (hh : -1 ≤ h) (hy : -1 ≤ y) : (cnt 0 h y : ℤ) = QQ 0 h y := by
  have hc : cnt 0 h y = if h = 0 ∧ y = 0 then 1 else 0 := by
    rw [cnt, Finset.card_filter, Fintype.sum_unique]
    simp only [nonpos_iff_eq_zero, forall_eq, pt_zero, Prod.fst_zero, Prod.snd_zero, add_zero]
    by_cases h0 : h = 0 <;> by_cases y0 : y = 0 <;> simp [h0, y0]
  rw [hc]
  simp only [QQ, AB, P, bin1]
  split_ifs <;> omega

/-- The count from any start with x, y ≥ -1, as the binomial transform of the reflected free walks. -/
theorem cnt_eq (n : ℕ) : ∀ h y : ℤ, -1 ≤ h → -1 ≤ y → (cnt n h y : ℤ) = T n (fun k => QQ k h y) := by
  induction n with
  | zero =>
    intro h y hh hy
    rw [cnt_zero h y hh hy]
    simp [T]
  | succ n ih =>
    intro h y hh hy
    rcases eq_or_lt_of_le hh with e | hh'
    · rw [← e, cnt_neg _ (Or.inl (by norm_num)), Nat.cast_zero]
      simp [T, QQ_neg_one_x]
    rcases eq_or_lt_of_le hy with e | hy'
    · rw [← e, cnt_neg _ (Or.inr (by norm_num)), Nat.cast_zero]
      simp [T, QQ_neg_one_y]
    have h0 : 0 ≤ h := by omega
    have y0 : 0 ≤ y := by omega
    have hs : T n (fun k => QQ (k + 1) h y) = T n (fun k => QQ k (h + 1) y) + T n (fun k => QQ k (h - 1) y) +
        T n (fun k => QQ k h (y + 1)) + T n (fun k => QQ k h (y - 1)) := by
      simp only [T, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [QQ_succ]; ring)
    rw [cnt_succ n h y h0 y0, ih (h + 1) y (by omega) hy, ih (h - 1) y (by omega) hy, ih h (y + 1) hh (by omega),
      ih h (y - 1) hh (by omega), ih h y hh hy, T_succ, hs]

/-! ### The sum and its telescoping certificate -/

/-- The summand: the walks with 2i steps on the x and y axes, placed among n steps, the others +z. -/
def F (n i : ℕ) : ℤ := (n.choose (2 * i) : ℤ) * q i

/-- The sum over the number of x, y steps. -/
def S (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n + 1), F n i

/-- The count of the entry is the sum. -/
theorem a_eq_S (n : ℕ) : (a n : ℤ) = S n := by
  rw [a_eq_cnt, cnt_eq n 0 0 (by norm_num) (by norm_num), T]
  have hz : ∀ k ∈ Finset.range (2 * (n + 1)), k ∉ Finset.range (n + 1) → (n.choose k : ℤ) * QQ k 0 0 = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_subset (Finset.range_subset_range.2 (by omega)) hz,
    sum_even (fun k => (n.choose k : ℤ) * QQ k 0 0) (fun i => by simp [QQ_odd]) (n + 1)]
  exact Finset.sum_congr rfl (fun i _ => by rw [QQ_even, F])

lemma q_mul (i : ℕ) : q i * (((i : ℤ) + 1) ^ 2 * ((i : ℤ) + 2)) = 2 * (2 * i + 1) * ((2 * i).choose i : ℤ) ^ 2 := by
  have h1 := Nat.choose_succ_right_eq (2 * i) i
  rw [show 2 * i - i = i by omega] at h1
  have hc1 : ((2 * i).choose (i + 1) : ℤ) * ((i : ℤ) + 1) = ((2 * i).choose i : ℤ) * i := by
    exact_mod_cast h1
  have hc2 : ((2 * i).choose (i + 2) : ℤ) * ((i : ℤ) + 2) = ((2 * i).choose (i + 1) : ℤ) * ((i : ℤ) - 1) := by
    rcases i with _ | i
    · simp
    · have h2 := Nat.choose_succ_right_eq (2 * (i + 1)) (i + 1 + 1)
      rw [show 2 * (i + 1) - (i + 1 + 1) = i by omega, show i + 1 + 1 + 1 = i + 1 + 2 by ring] at h2
      have e := congrArg (Nat.cast : ℕ → ℤ) h2
      push_cast at e ⊢
      linear_combination e
  simp only [q]
  linear_combination (-2 * ((i : ℤ) + 2) * (((2 * i).choose (i + 1) : ℤ) * ((i : ℤ) + 1) +
      ((2 * i).choose i : ℤ) * i) + ((2 * i).choose i : ℤ) * ((i : ℤ) - 1) * ((i : ℤ) + 1)) * hc1 +
    ((2 * i).choose i : ℤ) * ((i : ℤ) + 1) ^ 2 * hc2

lemma q_succ (i : ℕ) : q (i + 1) * (((i : ℤ) + 2) * ((i : ℤ) + 3)) = 4 * (2 * i + 1) * (2 * i + 3) * q i := by
  have h1 := q_mul (i + 1)
  have h0 := q_mul i
  have hb := Nat.succ_mul_centralBinom_succ i
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at hb
  have hb' : ((i : ℤ) + 1) * ((2 * (i + 1)).choose (i + 1) : ℤ) = 2 * (2 * i + 1) * ((2 * i).choose i : ℤ) := by
    exact_mod_cast hb
  push_cast at h1
  have key : (q (i + 1) * (((i : ℤ) + 2) * ((i : ℤ) + 3)) - 4 * (2 * i + 1) * (2 * i + 3) * q i) *
      (((i : ℤ) + 1) ^ 2 * ((i : ℤ) + 2)) = 0 := by
    linear_combination ((i : ℤ) + 1) ^ 2 * h1 - 4 * (2 * (i : ℤ) + 1) * (2 * i + 3) * h0 +
      2 * (2 * (i : ℤ) + 3) * (((i : ℤ) + 1) * ((2 * (i + 1)).choose (i + 1) : ℤ) + 2 * (2 * i + 1) *
        ((2 * i).choose i : ℤ)) * hb'
  have hne : ((i : ℤ) + 1) ^ 2 * ((i : ℤ) + 2) ≠ 0 := by positivity
  linear_combination (mul_eq_zero.1 key).resolve_right hne

/-- One more step in n. -/
lemma F_succ_n (n i : ℕ) : F n i * ((n : ℤ) + 1) = F (n + 1) i * ((n : ℤ) + 1 - 2 * i) := by
  simp only [F]
  rcases Nat.lt_or_ge n (2 * i) with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul, zero_mul]
    rcases Nat.lt_or_ge (n + 1) (2 * i) with h' | h'
    · rw [Nat.choose_eq_zero_of_lt h']
      simp
    · have e : (n : ℤ) + 1 - 2 * i = 0 := by omega
      rw [e, mul_zero]
  · have hc := Nat.choose_mul_succ_eq n (2 * i)
    have hc' : (n.choose (2 * i) : ℤ) * ((n : ℤ) + 1) = ((n + 1).choose (2 * i) : ℤ) * ((n : ℤ) + 1 - 2 * i) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) hc
      push_cast [Nat.cast_sub (show 2 * i ≤ n + 1 by omega)] at e
      linear_combination e
    linear_combination (q i) * hc'

/-- One more step in i. -/
lemma F_succ_i (n i : ℕ) : F n (i + 1) * ((2 * (i : ℤ) + 2) * (((i : ℤ) + 2) * ((i : ℤ) + 3))) =
    4 * F n i * (((n : ℤ) - 2 * i) * ((n : ℤ) - 2 * i - 1) * (2 * i + 3)) := by
  simp only [F]
  rcases Nat.lt_or_ge n (2 * i + 2) with h | h
  · rw [Nat.choose_eq_zero_of_lt (show n < 2 * (i + 1) by omega), Nat.cast_zero, zero_mul, zero_mul]
    rcases Nat.lt_or_ge n (2 * i) with h' | h'
    · rw [Nat.choose_eq_zero_of_lt h']
      simp
    · rcases Nat.eq_or_lt_of_le h' with e | e
      · have : (n : ℤ) - 2 * i = 0 := by omega
        rw [this]
        simp
      · have : (n : ℤ) - 2 * i - 1 = 0 := by omega
        rw [this]
        simp
  · have e1 := Nat.choose_succ_right_eq n (2 * i)
    have e2 := Nat.choose_succ_right_eq n (2 * i + 1)
    have e1' : (n.choose (2 * i + 1) : ℤ) * (2 * i + 1) = (n.choose (2 * i) : ℤ) * ((n : ℤ) - 2 * i) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) e1
      push_cast [Nat.cast_sub (show 2 * i ≤ n by omega)] at e
      linear_combination e
    have e2' : (n.choose (2 * i + 2) : ℤ) * (2 * i + 2) = (n.choose (2 * i + 1) : ℤ) * ((n : ℤ) - 2 * i - 1) := by
      have e := congrArg (Nat.cast : ℕ → ℤ) e2
      push_cast [Nat.cast_sub (show 2 * i + 1 ≤ n by omega)] at e
      linear_combination e
    have eq := q_succ i
    rw [show 2 * (i + 1) = 2 * i + 2 by ring]
    linear_combination q (i + 1) * (((i : ℤ) + 2) * ((i : ℤ) + 3)) * e2' +
      (n.choose (2 * i + 1) : ℤ) * ((n : ℤ) - 2 * i - 1) * eq +
      4 * ((n : ℤ) - 2 * i - 1) * (2 * i + 3) * q i * e1'

/-- The coefficients of the recurrence at n = m + 3, for a(m), a(m+1), a(m+2), a(m+3). -/
def c0 (m : ℕ) : ℤ := 15 * ((m : ℤ) + 2) * ((m : ℤ) + 1)
def c1 (m : ℕ) : ℤ := -13 * ((m : ℤ) + 2) * ((m : ℤ) + 4)
def c2 (m : ℕ) : ℤ := 3 * (-((m : ℤ) + 3) ^ 2 - 3 * ((m : ℤ) + 3) - 1)
def c3 (m : ℕ) : ℤ := ((m : ℤ) + 7) * ((m : ℤ) + 5)

/-- The telescoping certificate. -/
def G (m k : ℕ) : ℚ := -8 * k * ((k : ℚ) + 1) * ((k : ℚ) + 2) / ((m : ℚ) + 3) * F (m + 3) k

/-- The certificate identity, term by term, for every k. -/
lemma cert (m k : ℕ) :
    (c0 m : ℚ) * F m k + c1 m * F (m + 1) k + c2 m * F (m + 2) k + c3 m * F (m + 3) k = G m (k + 1) - G m k := by
  have e2 := F_succ_n (m + 2) k
  have e1 := F_succ_n (m + 1) k
  have e0 := F_succ_n m k
  have ey := F_succ_i (m + 3) k
  rw [show m + 2 + 1 = m + 3 from rfl] at e2
  rw [show m + 1 + 1 = m + 2 from rfl] at e1
  push_cast at e2 e1 e0 ey
  have q2 : (F (m + 2) k : ℚ) = F (m + 3) k * ((m : ℚ) + 3 - 2 * k) / ((m : ℚ) + 3) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination e2 :
      F (m + 2) k * ((m : ℤ) + 3) = F (m + 3) k * ((m : ℤ) + 3 - 2 * k))
  have q1 : (F (m + 1) k : ℚ) = F (m + 2) k * ((m : ℚ) + 2 - 2 * k) / ((m : ℚ) + 2) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination e1 :
      F (m + 1) k * ((m : ℤ) + 2) = F (m + 2) k * ((m : ℤ) + 2 - 2 * k))
  have q0 : (F m k : ℚ) = F (m + 1) k * ((m : ℚ) + 1 - 2 * k) / ((m : ℚ) + 1) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast e0
  have qy : (F (m + 3) (k + 1) : ℚ) =
      4 * F (m + 3) k * (((m : ℚ) + 3 - 2 * k) * ((m : ℚ) + 3 - 2 * k - 1) * (2 * k + 3)) /
        ((2 * (k : ℚ) + 2) * (((k : ℚ) + 2) * ((k : ℚ) + 3))) := by
    rw [eq_div_iff (by positivity)]
    exact_mod_cast (by linear_combination ey :
      F (m + 3) (k + 1) * ((2 * (k : ℤ) + 2) * (((k : ℤ) + 2) * ((k : ℤ) + 3))) =
        4 * F (m + 3) k * (((m : ℤ) + 3 - 2 * k) * ((m : ℤ) + 3 - 2 * k - 1) * (2 * k + 3)))
  simp only [G]
  rw [q0, q1, q2, qy]
  simp only [c0, c1, c2, c3]
  push_cast
  field_simp
  ring

/-- The recurrence of the sum, at n = m + 3. -/
theorem rec_S (m : ℕ) : c0 m * S m + c1 m * S (m + 1) + c2 m * S (m + 2) + c3 m * S (m + 3) = 0 := by
  have ext : ∀ n, n ≤ m + 3 → (S n : ℚ) = ∑ k ∈ Finset.range (m + 4), (F n k : ℚ) := by
    intro n hn
    rw [S, Int.cast_sum]
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) (fun k _ hk => ?_)
    rw [Finset.mem_range, not_lt] at hk
    rw [F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have g0 : G m 0 = 0 := by simp [G]
  have g1 : G m (m + 4) = 0 := by
    rw [G, F, Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hq : (c0 m : ℚ) * S m + c1 m * S (m + 1) + c2 m * S (m + 2) + c3 m * S (m + 3) = 0 := by
    rw [ext m (by omega), ext (m + 1) (by omega), ext (m + 2) (by omega), ext (m + 3) le_rfl,
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_congr rfl (fun k _ => cert m k),
      Finset.sum_range_sub (G m), g0, g1, sub_zero]
  exact_mod_cast hq

/-! ### The recurrence -/

/-- Mathar's recurrence, for every n ≥ 3. -/
theorem conjecture :
    ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * ((n : ℤ) + 2) * (a n : ℤ) + 3 * (-(n : ℤ) ^ 2 - 3 * (n : ℤ) - 1) * (a (n - 1) : ℤ) -
      13 * ((n : ℤ) - 1) * ((n : ℤ) + 1) * (a (n - 2) : ℤ) +
      15 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (a (n - 3) : ℤ) = 0 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := rec_S m
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega, show m + 3 - 3 = m by omega,
    a_eq_S, a_eq_S, a_eq_S, a_eq_S]
  simp only [c0, c1, c2, c3] at h
  push_cast
  linear_combination h

/-- Controls: the entry's data a(0..27). -/
theorem controls :
    a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 3 ∧ a 3 = 7 ∧ a 4 = 23 ∧ a 5 = 71 ∧ a 6 = 251 ∧ a 7 = 883 ∧ a 8 = 3305
    ∧ a 9 = 12505 ∧ a 10 = 48895 ∧ a 11 = 193755 ∧ a 12 = 783355 ∧ a 13 = 3205931 ∧ a 14 = 13302329
    ∧ a 15 = 55764413 ∧ a 16 = 236174933 ∧ a 17 = 1008773269 ∧ a 18 = 4343533967 ∧ a 19 =
    18834033443 ∧ a 20 = 82201462251 ∧ a 21 = 360883031291 ∧ a 22 = 1592993944723 ∧ a 23 =
    7066748314147 ∧ a 24 = 31493800133173 ∧ a 25 = 140953938878821 ∧ a 26 = 633354801073571 ∧ a 27 =
    2856369029213263 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
  ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    rw [← Int.natCast_inj, a_eq_S]
    decide +kernel

end OMA.S_oeis_a302180

theorem OMA.solution : type_of% @OMA.S_oeis_a302180.main :=
  OMA.S_oeis_a302180.conjecture
