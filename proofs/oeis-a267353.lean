import OMAStatements.S_oeis_a267353

namespace J

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 123 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 123 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of ON cells of stage t among the cells -t..t. -/
def cells (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

/-- A267353(n): the total number of ON cells in stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), cells t



def live (t : ℕ) (i : ℤ) : Prop :=
  (t = 0 ∧ (i = 0)) ∨
  (t = 1 ∧ (i < -1 ∨ 1 < i ∨ i = -1 ∨ i = 1)) ∨
  (2 ≤ t ∧ t % 2 = 0 ∧ (((-1:ℤ) ≤ i ∧ i ≤ (1:ℤ)))) ∨
  (2 ≤ t ∧ t % 2 = 1 ∧ (i < -(t:ℤ) ∨ (t:ℤ) < i ∨ (-(t:ℤ) ≤ i ∧ i ≤ (-1:ℤ)) ∨ ((1:ℤ) ≤ i ∧ i ≤ (t:ℤ))))


lemma table (l c r : Bool) :
    eca 123 l c r = true ↔ (l = false ∧ c = false ∧ r = false) ∨ (l = false ∧ c = false ∧ r = true) ∨ (l = false ∧ c = true ∧ r = true) ∨ (l = true ∧ c = false ∧ r = false) ∨ (l = true ∧ c = false ∧ r = true) ∨ (l = true ∧ c = true ∧ r = false) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    rcases Nat.lt_or_ge t 2 with ht | ht
    · interval_cases t <;> simp only [live, Nat.reduceEqDiff, Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff, false_and, true_and, false_or, or_false, and_true, and_false, le_refl] <;> omega
    · obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 2 ∧ t = 2 * m + (2 + r) :=
        ⟨(t - 2) / 2, (t - 2) % 2, Nat.mod_lt _ (by norm_num), by omega⟩
      interval_cases r
      · simp only [live, show (2 * m + (2 + 0) = 0) = False from eq_false (by omega), show (2 * m + (2 + 0) = 1) = False from eq_false (by omega), show (2 ≤ 2 * m + (2 + 0)) = True from eq_true (by omega), show ((2 * m + (2 + 0)) % 2 = 0) = True from eq_true (by omega), show ((2 * m + (2 + 0)) % 2 = 1) = False from eq_false (by omega), show (2 * m + (2 + 0) + 1 = 0) = False from eq_false (by omega), show (2 * m + (2 + 0) + 1 = 1) = False from eq_false (by omega), show (2 ≤ 2 * m + (2 + 0) + 1) = True from eq_true (by omega), show ((2 * m + (2 + 0) + 1) % 2 = 0) = False from eq_false (by omega), show ((2 * m + (2 + 0) + 1) % 2 = 1) = True from eq_true (by omega), false_and, true_and, false_or, or_false, and_true, and_false]
        push_cast
        omega
      · simp only [live, show (2 * m + (2 + 1) = 0) = False from eq_false (by omega), show (2 * m + (2 + 1) = 1) = False from eq_false (by omega), show (2 ≤ 2 * m + (2 + 1)) = True from eq_true (by omega), show ((2 * m + (2 + 1)) % 2 = 0) = False from eq_false (by omega), show ((2 * m + (2 + 1)) % 2 = 1) = True from eq_true (by omega), show (2 * m + (2 + 1) + 1 = 0) = False from eq_false (by omega), show (2 * m + (2 + 1) + 1 = 1) = False from eq_false (by omega), show (2 ≤ 2 * m + (2 + 1) + 1) = True from eq_true (by omega), show ((2 * m + (2 + 1) + 1) % 2 = 0) = True from eq_true (by omega), show ((2 * m + (2 + 1) + 1) % 2 = 1) = False from eq_false (by omega), false_and, true_and, false_or, or_false, and_true, and_false]
        push_cast
        omega


def g (t k : ℕ) : ℕ := if state t ((k:ℤ) - (t:ℤ)) = true then 1 else 0

lemma ind (t k : ℕ) :
    (if state t ((k:ℤ) - (t:ℤ)) = true then 1 else 0) = g t k := by
  unfold g
  cases state t ((k:ℤ) - (t:ℤ)) <;> simp

lemma split (T a L R : ℕ) :
    ∑ k ∈ Finset.range (L + R), g T (a + k) =
      ∑ k ∈ Finset.range L, g T (a + k) + ∑ k ∈ Finset.range R, g T ((a + L) + k) := by
  rw [Finset.sum_range_add]
  simp only [add_assoc]

lemma seg_c (T a L v : ℕ) (h : ∀ k < L, g T (a + k) = v) :
    ∑ k ∈ Finset.range L, g T (a + k) = L * v := by
  rw [Finset.sum_congr rfl (fun k hk => h k (Finset.mem_range.mp hk))]
  simp

lemma par_count (L o : ℕ) :
    ∑ k ∈ Finset.range L, (if (o + k) % 2 = 0 then 1 else 0) = (L + 1 - o % 2) / 2 := by
  induction L with
  | zero => simp; omega
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

lemma seg_p (T a L o : ℕ) (h : ∀ k < L, g T (a + k) = if (o + k) % 2 = 0 then 1 else 0) :
    ∑ k ∈ Finset.range L, g T (a + k) = (L + 1 - o % 2) / 2 := by
  rw [Finset.sum_congr rfl (fun k hk => h k (Finset.mem_range.mp hk)), par_count]

lemma cells_g (t : ℕ) : cells t = ∑ k ∈ Finset.range (2 * t + 1), g t (0 + k) := by
  unfold cells
  rw [Finset.card_filter]
  simp only [zero_add]
  exact Finset.sum_congr rfl (fun k _ => ind t k)


lemma cls0 (m : ℕ) : cells (2 * m + 2) = 0 * m + 3 := by
  rw [cells_g]
  rw [show 2 * (2 * m + 2) + 1 = ((2 * m + 1) + ((0 * m + 3) + (2 * m + 1))) by omega]
  rw [split (2 * m + 2) (0) (2 * m + 1) ((0 * m + 3) + (2 * m + 1))]
  rw [seg_c (2 * m + 2) (0) (2 * m + 1) 0 (by intro k hk; unfold g; split_ifs with h <;> rw [state_iff] at h <;> unfold live at h <;> push_cast [true_and, false_and, false_or, or_false] at h ⊢ <;> omega)]
  rw [split (2 * m + 2) (0 + (2 * m + 1)) (0 * m + 3) (2 * m + 1)]
  rw [seg_c (2 * m + 2) (0 + (2 * m + 1)) (0 * m + 3) 1 (by intro k hk; unfold g; split_ifs with h <;> rw [state_iff] at h <;> unfold live at h <;> push_cast [true_and, false_and, false_or, or_false] at h ⊢ <;> omega)]
  rw [seg_c (2 * m + 2) (0 + (2 * m + 1) + (0 * m + 3)) (2 * m + 1) 0 (by intro k hk; unfold g; split_ifs with h <;> rw [state_iff] at h <;> unfold live at h <;> push_cast [true_and, false_and, false_or, or_false] at h ⊢ <;> omega)]
  omega

lemma cls1 (m : ℕ) : cells (2 * m + 3) = 4 * m + 6 := by
  rw [cells_g]
  rw [show 2 * (2 * m + 3) + 1 = ((2 * m + 3) + ((0 * m + 1) + (2 * m + 3))) by omega]
  rw [split (2 * m + 3) (0) (2 * m + 3) ((0 * m + 1) + (2 * m + 3))]
  rw [seg_c (2 * m + 3) (0) (2 * m + 3) 1 (by intro k hk; unfold g; split_ifs with h <;> rw [state_iff] at h <;> unfold live at h <;> push_cast [true_and, false_and, false_or, or_false] at h ⊢ <;> omega)]
  rw [split (2 * m + 3) (0 + (2 * m + 3)) (0 * m + 1) (2 * m + 3)]
  rw [seg_c (2 * m + 3) (0 + (2 * m + 3)) (0 * m + 1) 0 (by intro k hk; unfold g; split_ifs with h <;> rw [state_iff] at h <;> unfold live at h <;> push_cast [true_and, false_and, false_or, or_false] at h ⊢ <;> omega)]
  rw [seg_c (2 * m + 3) (0 + (2 * m + 3) + (0 * m + 1)) (2 * m + 3) 1 (by intro k hk; unfold g; split_ifs with h <;> rw [state_iff] at h <;> unfold live at h <;> push_cast [true_and, false_and, false_or, or_false] at h ⊢ <;> omega)]
  omega

lemma a_succ (n : ℕ) : (a (n + 1) : ℤ) = a n + cells (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ]
  push_cast
  ring

lemma tot0 (M : ℕ) : 2 * (a (2 * M + 2) : ℤ) = 4 * M * M + 14 * M + 12 := by
  induction M with
  | zero =>
    have h : a 2 = 6 := by decide
    rw [show 2 * 0 + 2 = 2 from rfl, h]
    norm_num
  | succ M ih =>
    have e1 : (a (2 * M + 2 + 1) : ℤ) = a (2 * M + 2) + cells (2 * M + 2 + 1) := a_succ _
    have c1 : (cells (2 * M + 2 + 1) : ℤ) = 4 * (M + 0) + 6 := by
      rw [show 2 * M + 2 + 1 = 2 * (M + 0) + 3 by ring, cls1]
      push_cast
      ring
    have e2 : (a (2 * M + 2 + 2) : ℤ) = a (2 * M + 2 + 1) + cells (2 * M + 2 + 2) := a_succ _
    have c2 : (cells (2 * M + 2 + 2) : ℤ) = 0 * (M + 1) + 3 := by
      rw [show 2 * M + 2 + 2 = 2 * (M + 1) + 2 by ring, cls0]
      push_cast
      ring
    rw [show 2 * (M + 1) + 2 = 2 * M + 2 + 2 by ring]
    push_cast at ih e1 c1 ⊢
    linear_combination ih + 2 * e1 + 2 * c1 + 2 * e2 + 2 * c2

lemma tot1 (M : ℕ) : 2 * (a (2 * M + 3) : ℤ) = 4 * M * M + 22 * M + 24 := by
  induction M with
  | zero =>
    have h : a 3 = 12 := by decide
    rw [show 2 * 0 + 3 = 3 from rfl, h]
    norm_num
  | succ M ih =>
    have e1 : (a (2 * M + 3 + 1) : ℤ) = a (2 * M + 3) + cells (2 * M + 3 + 1) := a_succ _
    have c1 : (cells (2 * M + 3 + 1) : ℤ) = 0 * (M + 1) + 3 := by
      rw [show 2 * M + 3 + 1 = 2 * (M + 1) + 2 by ring, cls0]
      push_cast
      ring
    have e2 : (a (2 * M + 3 + 2) : ℤ) = a (2 * M + 3 + 1) + cells (2 * M + 3 + 2) := a_succ _
    have c2 : (cells (2 * M + 3 + 2) : ℤ) = 4 * (M + 1) + 6 := by
      rw [show 2 * M + 3 + 2 = 2 * (M + 1) + 3 by ring, cls1]
      push_cast
      ring
    rw [show 2 * (M + 1) + 3 = 2 * M + 3 + 2 by ring]
    push_cast at ih e1 c1 ⊢
    linear_combination ih + 2 * e1 + 2 * c1 + 2 * e2 + 2 * c2

lemma c0 : ∀ n : ℕ, 2 * (a n : ℤ) = n ^ 2 + (4 - (-1) ^ n) * n + (-1) ^ n + 1 := by
  intro n
  rcases Nat.lt_or_ge n 2 with hs | hs
  · interval_cases n
    all_goals (try simp only [Nat.reduceSub])
    all_goals simp [(show a 0 = 1 by decide), (show a 1 = 3 by decide)]
    all_goals norm_num
  · obtain ⟨M, r, hr, rfl⟩ : ∃ M r, r < 2 ∧ n = 2 * (M + 0) + (2 + r) := ⟨(n - 2) / 2, (n - 2) % 2, Nat.mod_lt _ (by norm_num), by omega⟩
    interval_cases r
    · 
      have h0 : 2 * (a (2 * (M + 0) + (2 + 0)) : ℤ) = 4 * (M + 0) * (M + 0) + 14 * (M + 0) + 12 := by rw [show 2 * (M + 0) + (2 + 0) = 2 * (M + 0) + 2 by omega]; exact tot0 (M + 0)
      rw [show (2 : ℤ) * (a (2 * (M + 0) + (2 + 0)) : ℤ) = 1 * (2 * (a (2 * (M + 0) + (2 + 0)) : ℤ)) by ring, h0]
      push_cast
      norm_num [pow_add, pow_mul] <;> ring
    · 
      have h0 : 2 * (a (2 * (M + 0) + (2 + 1)) : ℤ) = 4 * (M + 0) * (M + 0) + 22 * (M + 0) + 24 := by rw [show 2 * (M + 0) + (2 + 1) = 2 * (M + 0) + 3 by omega]; exact tot1 (M + 0)
      rw [show (2 : ℤ) * (a (2 * (M + 0) + (2 + 1)) : ℤ) = 1 * (2 * (a (2 * (M + 0) + (2 + 1)) : ℤ)) by ring, h0]
      push_cast
      norm_num [pow_add, pow_mul] <;> ring

lemma c1 : ∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5) := by
  intro n hn
  rcases Nat.lt_or_ge n 8 with hs | hs
  · interval_cases n
    all_goals (try simp only [Nat.reduceSub])
    all_goals simp [(show a 0 = 1 by decide), (show a 1 = 3 by decide), (show a 2 = 6 by have h := tot0 0; push_cast at h; omega), (show a 3 = 12 by have h := tot1 0; push_cast at h; omega), (show a 4 = 15 by have h := tot0 1; push_cast at h; omega), (show a 5 = 25 by have h := tot1 1; push_cast at h; omega), (show a 6 = 28 by have h := tot0 2; push_cast at h; omega), (show a 7 = 42 by have h := tot1 2; push_cast at h; omega)]
    all_goals norm_num
  · obtain ⟨M, r, hr, rfl⟩ : ∃ M r, r < 2 ∧ n = 2 * (M + 3) + (2 + r) := ⟨(n - 8) / 2, (n - 8) % 2, Nat.mod_lt _ (by norm_num), by omega⟩
    interval_cases r
    · 
      have h0 : 2 * (a (2 * (M + 3) + (2 + 0)) : ℤ) = 4 * (M + 3) * (M + 3) + 14 * (M + 3) + 12 := by rw [show 2 * (M + 3) + (2 + 0) = 2 * (M + 3) + 2 by omega]; exact tot0 (M + 3)
      have h1 : 2 * (a (2 * (M + 3) + (2 + 0) - 1) : ℤ) = 4 * (M + 2) * (M + 2) + 22 * (M + 2) + 24 := by rw [show 2 * (M + 3) + (2 + 0) - 1 = 2 * (M + 2) + 3 by omega]; exact tot1 (M + 2)
      have h2 : 2 * (a (2 * (M + 3) + (2 + 0) - 2) : ℤ) = 4 * (M + 2) * (M + 2) + 14 * (M + 2) + 12 := by rw [show 2 * (M + 3) + (2 + 0) - 2 = 2 * (M + 2) + 2 by omega]; exact tot0 (M + 2)
      have h3 : 2 * (a (2 * (M + 3) + (2 + 0) - 3) : ℤ) = 4 * (M + 1) * (M + 1) + 22 * (M + 1) + 24 := by rw [show 2 * (M + 3) + (2 + 0) - 3 = 2 * (M + 1) + 3 by omega]; exact tot1 (M + 1)
      have h4 : 2 * (a (2 * (M + 3) + (2 + 0) - 4) : ℤ) = 4 * (M + 1) * (M + 1) + 14 * (M + 1) + 12 := by rw [show 2 * (M + 3) + (2 + 0) - 4 = 2 * (M + 1) + 2 by omega]; exact tot0 (M + 1)
      have h5 : 2 * (a (2 * (M + 3) + (2 + 0) - 5) : ℤ) = 4 * (M + 0) * (M + 0) + 22 * (M + 0) + 24 := by rw [show 2 * (M + 3) + (2 + 0) - 5 = 2 * (M + 0) + 3 by omega]; exact tot1 (M + 0)
      have key : 2 * ((a (2 * (M + 3) + (2 + 0)) : ℤ) - ((1 : ℤ) * a (2 * (M + 3) + (2 + 0) - 1) + (2 : ℤ) * a (2 * (M + 3) + (2 + 0) - 2) + (-2 : ℤ) * a (2 * (M + 3) + (2 + 0) - 3) + (-1 : ℤ) * a (2 * (M + 3) + (2 + 0) - 4) + (1 : ℤ) * a (2 * (M + 3) + (2 + 0) - 5))) = 0 := by linear_combination h0 - (1 : ℤ) * h1 - (2 : ℤ) * h2 - (-2 : ℤ) * h3 - (-1 : ℤ) * h4 - (1 : ℤ) * h5
      linarith
    · 
      have h0 : 2 * (a (2 * (M + 3) + (2 + 1)) : ℤ) = 4 * (M + 3) * (M + 3) + 22 * (M + 3) + 24 := by rw [show 2 * (M + 3) + (2 + 1) = 2 * (M + 3) + 3 by omega]; exact tot1 (M + 3)
      have h1 : 2 * (a (2 * (M + 3) + (2 + 1) - 1) : ℤ) = 4 * (M + 3) * (M + 3) + 14 * (M + 3) + 12 := by rw [show 2 * (M + 3) + (2 + 1) - 1 = 2 * (M + 3) + 2 by omega]; exact tot0 (M + 3)
      have h2 : 2 * (a (2 * (M + 3) + (2 + 1) - 2) : ℤ) = 4 * (M + 2) * (M + 2) + 22 * (M + 2) + 24 := by rw [show 2 * (M + 3) + (2 + 1) - 2 = 2 * (M + 2) + 3 by omega]; exact tot1 (M + 2)
      have h3 : 2 * (a (2 * (M + 3) + (2 + 1) - 3) : ℤ) = 4 * (M + 2) * (M + 2) + 14 * (M + 2) + 12 := by rw [show 2 * (M + 3) + (2 + 1) - 3 = 2 * (M + 2) + 2 by omega]; exact tot0 (M + 2)
      have h4 : 2 * (a (2 * (M + 3) + (2 + 1) - 4) : ℤ) = 4 * (M + 1) * (M + 1) + 22 * (M + 1) + 24 := by rw [show 2 * (M + 3) + (2 + 1) - 4 = 2 * (M + 1) + 3 by omega]; exact tot1 (M + 1)
      have h5 : 2 * (a (2 * (M + 3) + (2 + 1) - 5) : ℤ) = 4 * (M + 1) * (M + 1) + 14 * (M + 1) + 12 := by rw [show 2 * (M + 3) + (2 + 1) - 5 = 2 * (M + 1) + 2 by omega]; exact tot0 (M + 1)
      have key : 2 * ((a (2 * (M + 3) + (2 + 1)) : ℤ) - ((1 : ℤ) * a (2 * (M + 3) + (2 + 1) - 1) + (2 : ℤ) * a (2 * (M + 3) + (2 + 1) - 2) + (-2 : ℤ) * a (2 * (M + 3) + (2 + 1) - 3) + (-1 : ℤ) * a (2 * (M + 3) + (2 + 1) - 4) + (1 : ℤ) * a (2 * (M + 3) + (2 + 1) - 5))) = 0 := by linear_combination h0 - (1 : ℤ) * h1 - (2 : ℤ) * h2 - (-2 : ℤ) * h3 - (-1 : ℤ) * h4 - (1 : ℤ) * h5
      linarith

open PowerSeries in
lemma c2 : mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℤ) := by
  have v0 : a 0 = 1 := by decide
  have v1 : a 1 = 3 := by decide
  have v2 : a 2 = 6 := by have h := tot0 0; push_cast at h; omega
  have v3 : a 3 = 12 := by have h := tot1 0; push_cast at h; omega
  have v4 : a 4 = 15 := by have h := tot0 1; push_cast at h; omega
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * ((1 - X) ^ 3 * (1 + X) ^ 2) = F + (-1 : ℤ) • (F * X ^ 1) + (-2 : ℤ) • (F * X ^ 2) + (2 : ℤ) • (F * X ^ 3) + (1 : ℤ) • (F * X ^ 4) + (-1 : ℤ) • (F * X ^ 5) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 2 * X + X ^ 2 + 2 * X ^ 3 - 2 * X ^ 4 : PowerSeries ℤ) = (1 : ℤ) • X ^ 0 + (2 : ℤ) • X ^ 1 + (1 : ℤ) • X ^ 2 + (2 : ℤ) • X ^ 3 + (-2 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := c1 n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [v0, v1, v2, v3, v4]


end J

open PowerSeries

private lemma cell_eq (t : ℕ) : ∀ i, OMA.S_oeis_a267353.cell 123 t i = J.state t i := by
  induction t with
  | zero => intro i; rfl
  | succ t ih => intro i; simp only [OMA.S_oeis_a267353.cell, J.state, ih]; rfl

private lemma onc (t : ℕ) : OMA.S_oeis_a267353.onCount 123 t = J.cells t := by
  unfold OMA.S_oeis_a267353.onCount J.cells
  rw [Finset.card_filter]
  simp only [cell_eq]

private lemma aeq (n : ℕ) : OMA.S_oeis_a267353.a n = (J.a n : ℤ) := by
  unfold OMA.S_oeis_a267353.a J.a
  push_cast
  simp only [onc]

theorem OMA.solution : type_of% @OMA.S_oeis_a267353.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [aeq]
    have h := J.c0 n
    have h2 : ((2 * (J.a n : ℤ) : ℤ) : ℚ) = (((n : ℤ) ^ 2 + (4 - (-1) ^ n) * n + (-1) ^ n + 1 : ℤ) : ℚ) := by
      rw [h]
    push_cast at h2
    rw [eq_div_iff two_ne_zero]
    push_cast
    linarith
  · intro n hn
    simp only [aeq]
    have h := J.c1 n (by omega)
    exact_mod_cast h
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) J.c2
    simp only [map_mul, map_sub, map_add, map_pow, map_one, map_ofNat, PowerSeries.map_X] at h
    convert h using 2
    ext n
    simp [aeq]
