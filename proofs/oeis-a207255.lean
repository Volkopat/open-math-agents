import OMAStatements.S_oeis_a207255

/-!
# Counting four-row grids in OEIS A207255

Both forbidden horizontal triples end in 01. After the first column the
columns therefore form a decreasing sequence in the coordinatewise order.
-/

namespace A207255Proof

open OMA.S_oeis_a207255

abbrev Column := Fin 4 → Bool

def legal (c : Column) : Prop :=
  ∀ i : Fin 2, window c i ≠ (false, true, false) ∧ window c i ≠ (true, false, true)

def below (d c : Column) : Prop := ∀ r, d r = true → c r = true

def follows (c d : Column) : Prop := legal d ∧ below d c

instance (c : Column) : Decidable (legal c) := by unfold legal; infer_instance

instance (c d : Column) : Decidable (follows c d) := by
  unfold follows below
  infer_instance

def full : Column := fun _ => true

/-- Each column follows its predecessor, using c as the initial upper bound. -/
def Chain {n : ℕ} (c : Column) (f : Fin n → Column) : Prop :=
  ∀ i : Fin n, follows (Fin.cons (α := fun _ => Column) c f i.castSucc) (f i)

instance {n : ℕ} (c : Column) (f : Fin n → Column) : Decidable (Chain c f) := by
  unfold Chain
  infer_instance

theorem chain_cons {n : ℕ} (c d : Column) (f : Fin n → Column) :
    Chain c (Fin.cons d f) ↔ follows c d ∧ Chain d f := by
  unfold Chain
  rw [Fin.forall_fin_succ]
  rfl

theorem chain_full {n : ℕ} (f : Fin (n + 1) → Column) :
    Chain full f ↔ (∀ i, legal (f i)) ∧ ∀ i : Fin n, below (f i.succ) (f i.castSucc) := by
  unfold Chain follows
  rw [forall_and]
  apply and_congr_right
  intro _
  rw [Fin.forall_fin_succ]
  change (below (f 0) full ∧ _) ↔ _
  have h : below (f 0) full := fun _ _ => rfl
  rw [and_iff_right h]
  rfl

def assemble {n : ℕ} (c : Column) (f : Fin n → Column) : Grid (n + 1) :=
  fun r j => Fin.cons (α := fun _ => Column) c f j r

def gridEquiv (n : ℕ) : (Column × (Fin n → Column)) ≃ Grid (n + 1) where
  toFun p := assemble p.1 p.2
  invFun g := (fun r => g r 0, fun j r => g r j.succ)
  left_inv := by rintro ⟨c, f⟩; rfl
  right_inv := by
    intro g
    funext r j
    refine Fin.cases ?_ (fun i => ?_) j <;> rfl

theorem horizontal_bits : ∀ x y z : Bool,
    ((x, y, z) ≠ (false, false, true) ∧ (x, y, z) ≠ (true, false, true)) ↔
      (z = true → y = true) := by decide

theorem valid_assemble {n : ℕ} (c : Column) (f : Fin n → Column) :
    IsValid (assemble c f) ↔ legal c ∧ Chain full f := by
  cases n with
  | zero =>
    simp [IsValid, assemble, Chain, legal, Fin.forall_fin_succ]
  | succ n =>
    rw [chain_full]
    have row (r : Fin 4) (j : Fin n) :
        (window (assemble c f r) j ≠ (false, false, true) ∧
         window (assemble c f r) j ≠ (true, false, true)) ↔
          (f j.succ r = true → f j.castSucc r = true) :=
      horizontal_bits _ _ _
    constructor
    · intro h
      exact ⟨h.2 0, (fun j => h.2 j.succ), fun j r => (row r j).mp (h.1 r j)⟩
    · rintro ⟨hc, hf, hm⟩
      refine ⟨fun r j => (row r j).mpr (hm j r), ?_⟩
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hc
      · exact hf i

def successors (c : Column) : Finset Column := Finset.univ.filter (follows c)

/-- Number of ways to append n columns, all weakly below the preceding column. -/
def ways : ℕ → Column → ℤ
  | 0, _ => 1
  | n + 1, c => ∑ d ∈ successors c, ways n d

theorem count_chains (n : ℕ) (c : Column) :
    (∑ f : Fin n → Column, if Chain c f then (1 : ℤ) else 0) = ways n c := by
  induction n generalizing c with
  | zero => simp [ways, Chain]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Column)
    rw [← e.sum_comp (fun f => if Chain c f then (1 : ℤ) else 0), Fintype.sum_prod_type]
    change (∑ d : Column, ∑ f : Fin n → Column, if Chain c (Fin.cons d f) then (1 : ℤ) else 0) = _
    rw [ways, successors, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : follows c d
    · simpa only [chain_cons, hd, true_and, if_true] using ih d
    · simp [chain_cons, hd]

theorem count_grids (n : ℕ) : a (n + 1) = 10 * ways n full := by
  have ten : (Finset.univ.filter legal).card = 10 := by decide +kernel
  calc
    a (n + 1) = ∑ g : Grid (n + 1), if IsValid g then (1 : ℤ) else 0 := by
      simp [a, Finset.sum_boole]
    _ = ∑ p : Column × (Fin n → Column), if IsValid (gridEquiv n p) then (1 : ℤ) else 0 :=
      ((gridEquiv n).sum_comp _).symm
    _ = ∑ c : Column, if legal c then ways n full else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro c _
      change (∑ f : Fin n → Column, if IsValid (assemble c f) then (1 : ℤ) else 0) = _
      by_cases hc : legal c
      · simpa only [valid_assemble, hc, true_and, if_true] using count_chains n full
      · simp [valid_assemble, hc]
    _ = 10 * ways n full := by
      rw [← Finset.sum_filter, Finset.sum_const, ten]
      simp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The first six continuation counts satisfy the same relation at every legal column. -/
theorem initial_relation : ∀ c : Column, legal c →
    ways 5 c = 5 * ways 4 c - 10 * ways 3 c + 10 * ways 2 c - 5 * ways 1 c + ways 0 c := by
  decide +kernel

/-- Appending one column is a linear operation, so it propagates the initial relation. -/
theorem ways_relation (n : ℕ) (c : Column) (hc : legal c) :
    ways (n + 5) c = 5 * ways (n + 4) c - 10 * ways (n + 3) c + 10 * ways (n + 2) c -
      5 * ways (n + 1) c + ways n c := by
  induction n generalizing c with
  | zero => exact initial_relation c hc
  | succ n ih =>
    change (∑ d ∈ successors c, ways (n + 5) d) =
      5 * (∑ d ∈ successors c, ways (n + 4) d) - 10 * (∑ d ∈ successors c, ways (n + 3) d) +
      10 * (∑ d ∈ successors c, ways (n + 2) d) - 5 * (∑ d ∈ successors c, ways (n + 1) d) +
      ∑ d ∈ successors c, ways n d
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d hd => ih d (Finset.mem_filter.mp hd).2.1

theorem recurrence (n : ℕ) (hn : 5 < n) :
    a n = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  change a (k + 6) = 5 * a (k + 5) - 10 * a (k + 4) + 10 * a (k + 3) -
    5 * a (k + 2) + a (k + 1)
  rw [count_grids (k + 5), count_grids (k + 4), count_grids (k + 3),
    count_grids (k + 2), count_grids (k + 1), count_grids k]
  linarith only [ways_relation k full (by decide : legal full)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem first_values :
    a 0 = 0 ∧ a 1 = 10 ∧ a 2 = 100 ∧ a 3 = 370 ∧ a 4 = 940 ∧ a 5 = 1950 := by
  have h : ways 0 full = 1 ∧ ways 1 full = 10 ∧ ways 2 full = 37 ∧
      ways 3 full = 94 ∧ ways 4 full = 195 := by decide +kernel
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨rfl, (count_grids 0).trans (by rw [h0]; decide),
    (count_grids 1).trans (by rw [h1]; decide), (count_grids 2).trans (by rw [h2]; decide),
    (count_grids 3).trans (by rw [h3]; decide), (count_grids 4).trans (by rw [h4]; decide)⟩

open PowerSeries

theorem generating_function :
    PowerSeries.mk a * (1 - X) ^ 5 = 10 * X * (1 + 5 * X - 3 * X ^ 2 - X ^ 3) := by
  have denominator (A : PowerSeries ℤ) :
      A * (1 - X) ^ 5 = A - 5 • (A * X ^ 1) + 10 • (A * X ^ 2) -
        10 • (A * X ^ 3) + 5 • (A * X ^ 4) - A * X ^ 5 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have numerator : (10 : PowerSeries ℤ) * X * (1 + 5 * X - 3 * X ^ 2 - X ^ 3) =
      10 • X ^ 1 + 50 • X ^ 2 - 30 • X ^ 3 - 10 • X ^ 4 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [denominator, numerator]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_mk, coeff_X_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases hn : n ≤ 5
  · obtain ⟨h0, h1, h2, h3, h4, h5⟩ := first_values
    interval_cases n <;> norm_num [h0, h1, h2, h3, h4, h5]
  · have h := recurrence n (by omega)
    simp (disch := omega) only [if_pos, if_neg, mul_zero, add_zero, sub_zero]
    linarith only [h]

end A207255Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a207255.main := by
  exact ⟨A207255Proof.generating_function, A207255Proof.recurrence⟩
