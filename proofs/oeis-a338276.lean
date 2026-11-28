import OMAStatements.S_oeis_a338276

-- Problem: OEIS A338276
-- Credit: @RiverMint78

namespace OMAQueenRecurrence

open OMA.S_oeis_a338276 Finset

abbrev K := ZMod 2
abbrev Grid := ℕ → ℕ → K

def q : Grid := fun r k => (queenPaths (r + 1) (k + 1) : K)

private def delta : Grid := fun r k => if r = 0 ∧ k = 0 then 1 else 0

private def shift (a b : ℕ) (f : Grid) : Grid := fun r k =>
  if a ≤ r ∧ b ≤ k then f (r - a) (k - b) else 0

private theorem shift_add (a b : ℕ) (f g : Grid) :
    shift a b (f + g) = shift a b f + shift a b g := by
  funext r k
  by_cases h : a ≤ r ∧ b ≤ k <;> simp [shift, h]

private theorem shift_comp (a b c d : ℕ) (f : Grid) :
    shift a b (shift c d f) = shift (a + c) (b + d) f := by
  funext r k
  simp only [shift]
  by_cases h : a + c ≤ r ∧ b + d ≤ k
  · obtain ⟨hr, hk⟩ := h
    rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨by omega, by omega⟩, if_pos ⟨hr, hk⟩]
    rw [show r - a - c = r - (a + c) by omega, show k - b - d = k - (b + d) by omega]
  · rw [if_neg h]
    split_ifs with h₀ h₁
    · obtain ⟨ha, hb⟩ := h₀
      obtain ⟨hc, hd⟩ := h₁
      exact False.elim (h ⟨by omega, by omega⟩)
    · rfl
    · rfl

private theorem shift_x_inj : Function.Injective (shift 1 0) := by
  intro f g h
  funext r k
  simpa [shift] using congrFun (congrFun h (r + 1)) k

private theorem k_add_self (x : K) : x + x = 0 := by
  rw [← two_mul, show (2 : K) = 0 from by decide, zero_mul]

private theorem equal_of_sum_zero {x y : K} (h : x + y = 0) : x = y := by
  calc
    x = (x + y) + y := by rw [add_assoc, k_add_self, add_zero]
    _ = y := by rw [h, zero_add]

private theorem reduce_two : (2 : Grid) = 0 := by
  funext r k
  exact (by decide : (2 : K) = 0)

private def east : Grid := fun r k => ∑ i ∈ range r, q i k

private def diagonal : Grid := fun r k =>
  ∑ i ∈ range (min r k), q (r - (i + 1)) (k - (i + 1))

private def northwest : Grid := fun r k =>
  ∑ i ∈ range k, q (r + (i + 1)) (k - (i + 1))

private def boundary : Grid := fun r k =>
  if r = 0 then northwest 0 k + q 0 k else 0

private theorem directions : q = delta + east + northwest + diagonal := by
  funext r k
  by_cases hz : r = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := hz
    rw [show q 0 0 = 1 by simp [q, queenPaths]]
    simp [delta, east, northwest, diagonal]
  · have ho : ¬ (r + 1 = 1 ∧ k + 1 = 1) := by omega
    change q r k = delta r k + east r k + northwest r k + diagonal r k
    rw [show delta r k = 0 by simp [delta, hz], zero_add]
    unfold q east northwest diagonal
    rw [queenPaths]
    simp only [Nat.succ_ne_zero, or_self, if_false, ho, Nat.cast_add, Nat.cast_sum]
    rw [min_add_add_right, Nat.add_sub_cancel]
    change (∑ i : Fin k, (queenPaths (r + 1 + (i.val + 1)) (k + 1 - (i.val + 1)) : K)) +
      (∑ i : Fin (min r k), (queenPaths (r + 1 - (i.val + 1)) (k + 1 - (i.val + 1)) : K)) +
      (∑ i : Fin r, q i.val k) = _
    have hn : (∑ i : Fin k,
        (queenPaths (r + 1 + (i.val + 1)) (k + 1 - (i.val + 1)) : K)) =
        ∑ i ∈ range k, q (r + (i + 1)) (k - (i + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => q (r + (i + 1)) (k - (i + 1)))]
      apply sum_congr rfl
      intro i _
      unfold q
      have h1 : r + 1 + (i.val + 1) = r + (i.val + 1) + 1 := by omega
      have h2 : k + 1 - (i.val + 1) = k - (i.val + 1) + 1 := by have := i.isLt; omega
      rw [h1, h2]
    have hd : (∑ i : Fin (min r k),
        (queenPaths (r + 1 - (i.val + 1)) (k + 1 - (i.val + 1)) : K)) =
        ∑ i ∈ range (min r k), q (r - (i + 1)) (k - (i + 1)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => q (r - (i + 1)) (k - (i + 1)))]
      apply sum_congr rfl
      intro i _
      have hi := i.isLt
      simp only [lt_min_iff] at hi
      unfold q
      have h1 : r + 1 - (i.val + 1) = r - (i.val + 1) + 1 := by omega
      have h2 : k + 1 - (i.val + 1) = k - (i.val + 1) + 1 := by omega
      rw [h1, h2]
    rw [hn, hd, Fin.sum_univ_eq_sum_range (fun i => q i k)]
    ac_rfl

private theorem east_eq : east + shift 1 0 east = shift 1 0 q := by
  funext r k
  cases r with
  | zero => simp [east, shift]
  | succ r =>
    change east (r + 1) k + shift 1 0 east (r + 1) k = shift 1 0 q (r + 1) k
    simp only [shift, Nat.le_add_left, zero_le, and_true, if_true, Nat.add_sub_cancel, tsub_zero]
    rw [show east (r + 1) k = east r k + q r k by simp [east, sum_range_succ]]
    rw [add_right_comm, k_add_self, zero_add]

private theorem diagonal_succ (r k : ℕ) :
    diagonal (r + 1) (k + 1) = q r k + diagonal r k := by
  unfold diagonal
  rw [min_add_add_right, sum_range_succ']
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  apply congrArg (fun x => x + q r k) ?_ |>.trans (add_comm _ _)
  apply sum_congr rfl
  intro i _
  rw [show r + 1 - (i + 1 + 1) = r - (i + 1) by omega,
    show k + 1 - (i + 1 + 1) = k - (i + 1) by omega]

private theorem diagonal_eq : diagonal + shift 1 1 diagonal = shift 1 1 q := by
  funext r k
  cases r with
  | zero => simp [diagonal, shift]
  | succ r =>
    cases k with
    | zero => simp [diagonal, shift]
    | succ k =>
      change diagonal (r + 1) (k + 1) + shift 1 1 diagonal (r + 1) (k + 1) =
        shift 1 1 q (r + 1) (k + 1)
      simp only [shift, Nat.le_add_left, and_self, if_true, Nat.add_sub_cancel,
        diagonal_succ, add_assoc, k_add_self, add_zero]

private theorem northwest_succ (r k : ℕ) :
    northwest r (k + 1) = q (r + 1) k + northwest (r + 1) k := by
  unfold northwest
  rw [sum_range_succ']
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  rw [add_comm]
  apply congrArg (q (r + 1) k + ·)
  apply sum_congr rfl
  intro i _
  rw [show r + (i + 1 + 1) = r + 1 + (i + 1) by omega,
    show k + 1 - (i + 1 + 1) = k - (i + 1) by omega]

private theorem northwest_eq :
    shift 1 0 northwest + shift 0 1 northwest = shift 0 1 q + shift 0 1 boundary := by
  funext r k
  cases k with
  | zero =>
    cases r <;> simp [shift, northwest]
  | succ k =>
    cases r with
    | zero =>
      change (0 : K) + northwest 0 k = q 0 k + (northwest 0 k + q 0 k)
      rw [zero_add, ← add_assoc, add_comm (q 0 k), add_assoc, k_add_self, add_zero]
    | succ r =>
      change northwest r (k + 1) + northwest (r + 1) k = q (r + 1) k + 0
      simp only [northwest_succ, add_assoc, k_add_self, add_zero]

-- X and Y denote the row and column shifts. Multiply the path identity by
-- (1+X)(1+XY)(X+Y), then eliminate the three directional sums.
private theorem cleared :
    shift 1 0 q + shift 1 1 q + shift 1 2 q + shift 3 1 q =
      shift 0 1 delta + shift 1 0 delta + shift 1 1 delta + shift 1 2 delta +
      shift 2 0 delta + shift 2 1 delta + shift 2 2 delta + shift 3 1 delta +
      shift 0 1 boundary + shift 1 1 boundary + shift 1 2 boundary + shift 2 2 boundary := by
  have cQ01 := congrArg (shift 0 1) directions
  have cQ10 := congrArg (shift 1 0) directions
  have cQ11 := congrArg (shift 1 1) directions
  have cQ12 := congrArg (shift 1 2) directions
  have cQ20 := congrArg (shift 2 0) directions
  have cQ21 := congrArg (shift 2 1) directions
  have cQ22 := congrArg (shift 2 2) directions
  have cQ31 := congrArg (shift 3 1) directions
  have cE01 := congrArg (shift 0 1) east_eq
  have cE10 := congrArg (shift 1 0) east_eq
  have cE12 := congrArg (shift 1 2) east_eq
  have cE21 := congrArg (shift 2 1) east_eq
  have cB01 := congrArg (shift 0 1) diagonal_eq
  have cB10 := congrArg (shift 1 0) diagonal_eq
  have cB11 := congrArg (shift 1 1) diagonal_eq
  have cB20 := congrArg (shift 2 0) diagonal_eq
  have cA00 := congrArg (shift 0 0) northwest_eq
  have cA10 := congrArg (shift 1 0) northwest_eq
  have cA11 := congrArg (shift 1 1) northwest_eq
  have cA21 := congrArg (shift 2 1) northwest_eq
  simp only [shift_add, shift_comp, Nat.reduceAdd] at cQ01 cQ10 cQ11 cQ12 cQ20 cQ21 cQ22 cQ31 cE01 cE10 cE12 cE21 cB01 cB10 cB11 cB20 cA00 cA10 cA11 cA21
  linear_combination (norm := (ring_nf; simp [reduce_two])) cQ01 + cQ10 + cQ11 + cQ12 + cQ20 + cQ21 + cQ22 + cQ31 + cE01 + cE10 + cE12 + cE21 + cB01 + cB10 + cB11 + cB20 + cA00 + cA10 + cA11 + cA21

private theorem boundary_eq : boundary = delta := by
  funext r k
  cases r with
  | zero =>
    have h := congrFun (congrFun cleared 0) (k + 1)
    simp [shift] at h
    calc
      boundary 0 k = (delta 0 k + boundary 0 k) + delta 0 k := by
        rw [add_comm (delta 0 k), add_assoc, k_add_self, add_zero]
      _ = delta 0 k := by rw [← h, zero_add]
  | succ r => simp [delta, boundary]

private theorem parity_identity :
    q + shift 0 1 q + shift 0 2 q + shift 2 1 q =
      delta + shift 1 0 delta + shift 1 1 delta + shift 2 1 delta := by
  apply shift_x_inj
  simp only [shift_add, shift_comp, Nat.reduceAdd]
  have h := cleared
  rw [boundary_eq] at h
  linear_combination (norm := (ring_nf; simp [reduce_two])) h

theorem q_zero (r : ℕ) : q r 0 = if r = 0 ∨ r = 1 then 1 else 0 := by
  have h := congrFun (congrFun parity_identity r) 0
  change q r 0 + shift 0 1 q r 0 + shift 0 2 q r 0 + shift 2 1 q r 0 =
    delta r 0 + shift 1 0 delta r 0 + shift 1 1 delta r 0 + shift 2 1 delta r 0 at h
  simp [shift, delta] at h
  rcases r with _ | r
  · simpa using h
  · rcases r with _ | r
    · simpa using h
    · simpa using h

theorem q_one (r : ℕ) : q r 1 = if r = 0 ∨ r = 3 then 1 else 0 := by
  have h := congrFun (congrFun parity_identity r) 1
  change q r 1 + shift 0 1 q r 1 + shift 0 2 q r 1 + shift 2 1 q r 1 =
    delta r 1 + shift 1 0 delta r 1 + shift 1 1 delta r 1 + shift 2 1 delta r 1 at h
  simp only [shift, delta, zero_le, le_refl, and_true, Nat.sub_zero, Nat.sub_self,
    Nat.reduceLeDiff, and_false, if_false, add_zero, q_zero] at h
  by_cases h0 : r = 0
  · subst r
    norm_num at h ⊢
    exact equal_of_sum_zero h
  by_cases h1 : r = 1
  · subst r
    norm_num at h ⊢
    exact h
  by_cases h2 : r = 2
  · subst r
    norm_num at h ⊢
    exact h
  by_cases h3 : r = 3
  · subst r
    norm_num at h ⊢
    exact equal_of_sum_zero h
  have hR : 3 < r := by omega
  simpa [h0, h1, h3, show 2 ≤ r by omega, show r - 1 ≠ 0 by omega,
    show r - 2 ≠ 0 by omega, show r - 2 ≠ 1 by omega] using h

theorem q_recurrence (r k : ℕ) :
    q r (k + 2) = q r (k + 1) + q r k + (if 2 ≤ r then q (r - 2) (k + 1) else 0) := by
  have h := congrFun (congrFun parity_identity r) (k + 2)
  change q r (k + 2) + shift 0 1 q r (k + 2) + shift 0 2 q r (k + 2) +
    shift 2 1 q r (k + 2) = delta r (k + 2) + shift 1 0 delta r (k + 2) +
    shift 1 1 delta r (k + 2) + shift 2 1 delta r (k + 2) at h
  have hk : k + 2 - 1 = k + 1 := by omega
  have hk₁ : 1 ≤ k + 2 := by omega
  have hk₂ : 2 ≤ k + 2 := by omega
  simp [shift, delta, hk, hk₁, hk₂] at h
  let t := q r (k + 1) + q r k + (if 2 ≤ r then q (r - 2) (k + 1) else 0)
  have hz : q r (k + 2) + t = 0 := by simpa only [t, add_assoc] using h
  calc
    q r (k + 2) = (q r (k + 2) + t) + t := by rw [add_assoc, k_add_self, add_zero]
    _ = t := by rw [hz, zero_add]

end OMAQueenRecurrence

namespace OMAQueenPolynomial

open Polynomial

abbrev P := Polynomial (ZMod 2)

lemma add_sq_char_two (a b : P) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have htwo : (2 : P) = 0 := by
    exact CharP.cast_eq_zero P 2
  calc
    (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by ring
    _ = a ^ 2 + b ^ 2 := by rw [htwo, zero_mul, zero_mul, add_zero]

noncomputable def fibPoly (t : P) : ℕ → P
  | 0 => 0
  | 1 => 1
  | n + 2 => t * fibPoly t (n + 1) + fibPoly t n

lemma fibPoly_comp (t z : P) : ∀ n : ℕ,
    (fibPoly t n).comp z = fibPoly (t.comp z) n
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    simp only [fibPoly, add_comp, mul_comp, fibPoly_comp t z n, fibPoly_comp t z (n + 1)]

lemma fibPoly_double (t : P) (m : ℕ) :
    fibPoly t (2 * m) = t * fibPoly t m ^ 2 ∧
    fibPoly t (2 * m + 1) = fibPoly t (m + 1) ^ 2 + fibPoly t m ^ 2 := by
  have htwo : (2 : P) = 0 := by exact CharP.cast_eq_zero P 2
  have hcancel (a : P) : a + a = 0 := by rw [← two_mul, htwo, zero_mul]
  induction m with
  | zero => simp [fibPoly]
  | succ m ih =>
    have heven : fibPoly t (2 * (m + 1)) = t * fibPoly t (m + 1) ^ 2 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, fibPoly, ih.1, ih.2, mul_add]
      rw [add_assoc, hcancel, add_zero]
    refine ⟨heven, ?_⟩
    calc
      fibPoly t (2 * (m + 1) + 1) = t * fibPoly t (2 * (m + 1)) + fibPoly t (2 * m + 1) := by
        conv_lhs => rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, fibPoly]
        congr 2
      _ = fibPoly t (m + 1 + 1) ^ 2 + fibPoly t (m + 1) ^ 2 := by
        rw [heven, ih.2, show m + 1 + 1 = m + 2 by omega, fibPoly, add_sq_char_two]
        ring

lemma fibPoly_pow_two (t : P) (n : ℕ) : fibPoly t (2 ^ n) = t ^ (2 ^ n - 1) := by
  induction n with
  | zero => simp [fibPoly]
  | succ n ih =>
    have hpos : 0 < (2 : ℕ) ^ n := by positivity
    rw [pow_succ', (fibPoly_double t (2 ^ n)).1, ih, ← pow_mul, ← pow_succ']
    congr 1
    omega

lemma fibPoly_natDegree (t : P) (ht : t.natDegree ≤ 1) : ∀ n : ℕ,
    (fibPoly t n).natDegree ≤ n - 1
  | 0 => by simp [fibPoly]
  | 1 => by simp [fibPoly]
  | n + 2 => by
    rw [fibPoly]
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_mul_le_of_le ht (fibPoly_natDegree t ht (n + 1))).trans (by omega)
    · exact (fibPoly_natDegree t ht n).trans (by omega)

noncomputable def column (k : ℕ) : P :=
  (1 + X) * (fibPoly (1 + X ^ 2) (k + 1) + X * fibPoly (1 + X ^ 2) k)

lemma column_zero : column 0 = 1 + X := by simp [column, fibPoly]

lemma column_one : column 1 = 1 + X ^ 3 := by
  have htwo : (2 : P) = 0 := by exact CharP.cast_eq_zero P 2
  simp only [column, fibPoly, mul_one, add_zero]
  calc
    (1 + X) * (1 + X ^ 2 + X) = 1 + X ^ 3 + 2 * (X + X ^ 2) := by ring
    _ = 1 + X ^ 3 := by rw [htwo, zero_mul, add_zero]

lemma column_step (k : ℕ) : column (k + 2) = (1 + X ^ 2) * column (k + 1) + column k := by
  let t : P := 1 + X ^ 2
  change (1 + X) * (fibPoly t (k + 3) + X * fibPoly t (k + 2)) =
    t * ((1 + X) * (fibPoly t (k + 2) + X * fibPoly t (k + 1))) +
    (1 + X) * (fibPoly t (k + 1) + X * fibPoly t k)
  have h₁ : fibPoly t (k + 3) = t * fibPoly t (k + 2) + fibPoly t (k + 1) := rfl
  have h₂ : fibPoly t (k + 2) = t * fibPoly t (k + 1) + fibPoly t k := rfl
  rw [h₁, h₂]
  ring

lemma column_coeff_step (k r : ℕ) : (column (k + 2)).coeff r =
    (column (k + 1)).coeff r + (column k).coeff r +
      (if 2 ≤ r then (column (k + 1)).coeff (r - 2) else 0) := by
  rw [column_step, add_mul, one_mul]
  simp only [coeff_add, coeff_X_pow_mul', add_assoc, add_comm]

lemma column_matches (q : ℕ → ℕ → ZMod 2)
    (hzero : ∀ r, q r 0 = if r = 0 ∨ r = 1 then 1 else 0)
    (hone : ∀ r, q r 1 = if r = 0 ∨ r = 3 then 1 else 0)
    (hstep : ∀ r k, q r (k + 2) = q r (k + 1) + q r k +
      (if 2 ≤ r then q (r - 2) (k + 1) else 0)) :
    ∀ r k, q r k = (column k).coeff r := by
  suffices ∀ k r, q r k = (column k).coeff r by exact fun r k => this k r
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    intro r
    rw [hzero, column_zero, coeff_add, coeff_one, coeff_X]
    by_cases h₀ : r = 0 <;> by_cases h₁ : r = 1 <;> simp_all [eq_comm]
  | one =>
    intro r
    rw [hone, column_one, coeff_add, coeff_one, coeff_X_pow]
    by_cases h₀ : r = 0 <;> by_cases h₁ : r = 3 <;> simp_all [eq_comm]
  | more k ih₀ ih₁ =>
    intro r
    rw [hstep, column_coeff_step, ih₀ r, ih₁ r, ih₁ (r - 2)]

noncomputable def fourthBase (m : ℕ) : P :=
  fibPoly (1 + X) (2 ^ m) + fibPoly (1 + X) (2 ^ m - 1)

lemma fourthBase_natDegree (m : ℕ) : (fourthBase m).natDegree ≤ 2 ^ m - 1 := by
  have h : ((1 + X) : P).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le <;> simp
  apply natDegree_add_le_of_degree_le
  · exact fibPoly_natDegree _ h _
  · exact (fibPoly_natDegree _ h _).trans (by omega)

lemma column_special (m : ℕ) :
    let D := (fourthBase m) ^ 4
    column (2 ^ (m + 2) - 2) =
      (1 + X) * (((1 + X) ^ (2 ^ (m + 2) - 2) + D).comp (X ^ 2) +
        X * (((1 + X) * D).comp (X ^ 2))) := by
  let s : ℕ := 2 ^ m
  have hs : 0 < s := by dsimp [s]; positivity
  have hs4 : 2 ^ (m + 2) = 4 * s := by rw [pow_add]; dsimp [s]; ring
  let t : P := 1 + X ^ 2
  let E : P := fibPoly t s + fibPoly t (s - 1)
  have hE : (fourthBase m).comp (X ^ 2) = E := by
    simp only [fourthBase, add_comp, fibPoly_comp, one_comp, X_comp]
    rfl
  have hs2 : fibPoly t (2 * s) = t ^ (2 * s - 1) := by
    rw [(fibPoly_double t s).1, show s = 2 ^ m by rfl, fibPoly_pow_two, ← pow_mul, ← pow_succ']
    congr 1
    omega
  have hOdd : fibPoly t (2 * s - 1) = E ^ 2 := by
    rw [show 2 * s - 1 = 2 * (s - 1) + 1 by omega, (fibPoly_double t (s - 1)).2,
      show s - 1 + 1 = s by omega, add_sq_char_two]
  have hFodd : fibPoly t (4 * s - 1) = t ^ (4 * s - 2) + E ^ 4 := by
    rw [show 4 * s - 1 = 2 * (2 * s - 1) + 1 by omega, (fibPoly_double t (2 * s - 1)).2,
      show 2 * s - 1 + 1 = 2 * s by omega, hOdd, hs2, ← pow_mul, ← pow_mul]
    congr 2
    omega
  have hFeven : fibPoly t (4 * s - 2) = t * E ^ 4 := by
    rw [show 4 * s - 2 = 2 * (2 * s - 1) by omega, (fibPoly_double t (2 * s - 1)).1,
      hOdd, ← pow_mul]
  dsimp only
  rw [hs4]
  change (1 + X) * (fibPoly t (4 * s - 2 + 1) + X * fibPoly t (4 * s - 2)) = _
  rw [show 4 * s - 2 + 1 = 4 * s - 1 by omega, hFodd, hFeven]
  simp only [add_comp, mul_comp, pow_comp, one_comp, X_comp, hE]
  rfl

end OMAQueenPolynomial

namespace OMAQueenSupport

open Polynomial Finset

private abbrev P := Polynomial (ZMod 2)

private noncomputable def geometric (s : ℕ) : P :=
  ∑ j ∈ range s, X ^ j

private theorem coeff_geometric (s r : ℕ) :
    (geometric s).coeff r = if r < s then 1 else 0 := by
  simp [geometric, coeff_X_pow]

private theorem coeff_four_shift (d r : ℕ) (hd : d < 4) (f : P) :
    ((X ^ d) * expand (ZMod 2) 4 f).coeff r =
      if r % 4 = d then f.coeff (r / 4) else 0 := by
  rw [coeff_X_pow_mul', coeff_expand (by decide : 0 < 4)]
  split_ifs <;> (first | rfl | omega | (congr 1; omega))

private theorem coeff_eight_shift (d r : ℕ) (hd : d < 8) (f : P) :
    ((X ^ d) * expand (ZMod 2) 8 f).coeff r =
      if r % 8 = d then f.coeff (r / 8) else 0 := by
  rw [coeff_X_pow_mul', coeff_expand (by decide : 0 < 8)]
  split_ifs <;> (first | rfl | omega | (congr 1; omega))

private noncomputable def combined (s : ℕ) (f : P) : P :=
  (1 + X) * expand (ZMod 2) 4 (geometric (2 * s)) +
    (1 + X ^ 2 + X ^ 3 + X ^ 4) * expand (ZMod 2) 8 f

private theorem coeff_combined (s r : ℕ) (f : P) :
    (combined s f).coeff r =
      (if r / 8 < s ∧ (r % 8 = 0 ∨ r % 8 = 1 ∨ r % 8 = 4 ∨ r % 8 = 5)
       then 1 else 0) +
      (if r % 8 = 0 ∨ r % 8 = 2 ∨ r % 8 = 3 ∨ r % 8 = 4
       then f.coeff (r / 8) else 0) := by
  unfold combined
  simp only [add_mul, coeff_add]
  have h40 := coeff_four_shift 0 r (by decide) (geometric (2 * s))
  have h41 := coeff_four_shift 1 r (by decide) (geometric (2 * s))
  have h80 := coeff_eight_shift 0 r (by decide) f
  simp only [pow_zero] at h40 h80
  simp only [pow_one] at h41
  rw [h40, h41, h80, coeff_eight_shift 2 r (by decide), coeff_eight_shift 3 r (by decide),
    coeff_eight_shift 4 r (by decide)]
  simp only [coeff_geometric]
  have hm : r % 8 < 8 := Nat.mod_lt _ (by decide)
  have hd : r / 4 < 2 * s ↔ r / 8 < s := by omega
  have hmod : r % 4 = (r % 8) % 4 := by omega
  rw [hmod]
  by_cases h : r / 8 < s
  · have h' := hd.mpr h
    interval_cases r % 8 <;> simp [h, h']
  · have h' : ¬ r / 4 < 2 * s := fun h' => h (hd.mp h')
    simp [h, h']
    interval_cases r % 8 <;> simp
/-- Nonzero offsets in one block of eight coefficients. -/
private def slots (d : ZMod 2) : Finset ℕ :=
  if d = 0 then {0, 1, 4, 5} else {1, 2, 3, 5}

private theorem slots_card (d : ZMod 2) : (slots d).card = 4 := by
  unfold slots
  split_ifs <;> decide

private theorem slots_small {d : ZMod 2} {j : ℕ} (hj : j ∈ slots d) : j < 8 := by
  unfold slots at hj
  split_ifs at hj <;> simp at hj <;> omega

private theorem coeff_combined_mem (s r : ℕ) (f : P) (hf : f.natDegree < s) :
    (combined s f).coeff r ≠ 0 ↔ r / 8 < s ∧ r % 8 ∈ slots (f.coeff (r / 8)) := by
  rw [coeff_combined]
  by_cases hr : r / 8 < s
  · let d := f.coeff (r / 8)
    change _ ≠ 0 ↔ _ ∧ _ ∈ slots d
    have hcases : d = 0 ∨ d = 1 := by
      have h : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
      exact h d
    have hm : r % 8 < 8 := Nat.mod_lt _ (by decide)
    rcases hcases with h | h <;>
      interval_cases r % 8 <;>
      simp [d, hr, h, slots] <;> decide
  · have hz : f.coeff (r / 8) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [hr, hz]

private def blockEmbedding (t : ℕ) : ℕ ↪ ℕ :=
  ⟨fun j => 8 * t + j, fun _ _ h => Nat.add_left_cancel h⟩

private theorem combined_card (s : ℕ) (f : P) (hf : f.natDegree < s) :
    (combined s f).support.card = 4 * s := by
  let blocks (t : ℕ) := (slots (f.coeff t)).map (blockEmbedding t)
  have hsupp : (combined s f).support = (range s).biUnion blocks := by
    ext r
    rw [mem_support_iff, coeff_combined_mem s r f hf, mem_biUnion]
    constructor
    · rintro ⟨hr, hj⟩
      refine ⟨r / 8, mem_range.mpr hr, mem_map.mpr ⟨r % 8, hj, ?_⟩⟩
      change 8 * (r / 8) + r % 8 = r
      omega
    · rintro ⟨t, ht, hmem⟩
      obtain ⟨j, hj, h⟩ := mem_map.mp hmem
      change 8 * t + j = r at h
      have hjlt := slots_small hj
      have hd : r / 8 = t := by omega
      have hm : r % 8 = j := by omega
      simpa only [hd, hm, mem_range] using And.intro ht hj
  rw [hsupp, card_biUnion]
  · simp [blocks, slots_card, Nat.mul_comm]
  · intro a _ b _ hab
    apply disjoint_left.mpr
    intro r ha hb
    obtain ⟨i, hi, ai⟩ := mem_map.mp ha
    obtain ⟨j, hj, bj⟩ := mem_map.mp hb
    change 8 * a + i = r at ai
    change 8 * b + j = r at bj
    have hi' := slots_small hi
    have hj' := slots_small hj
    omega

private theorem geometric_pow_two (m : ℕ) :
    (1 + X : P) ^ (2 ^ m - 1) = geometric (2 ^ m) := by
  have hpos : 0 < (2 : ℕ) ^ m := by positivity
  have hn : (1 + X : P) ≠ 0 := by
    simpa only [add_comm, C_1] using (X_add_C_ne_zero (1 : ZMod 2))
  apply mul_right_cancel₀ hn
  rw [← pow_succ, show 2 ^ m - 1 + 1 = 2 ^ m by omega]
  have hbinom : (1 + X : P) ^ (2 ^ m) = 1 + X ^ (2 ^ m) := by
    rw [add_pow_char_pow (1 : P) X (p := 2), one_pow]
  rw [hbinom]
  simpa [geometric, CharTwo.sub_eq_add, add_comm] using (geom_sum_mul (X : P) (2 ^ m)).symm

private theorem expand_four_eq_fourth_pow (f : P) :
    expand (ZMod 2) 4 f = f ^ 4 := by
  calc
    expand (ZMod 2) 4 f = expand (ZMod 2) 2 (expand (ZMod 2) 2 f) :=
      (expand_expand 2 2 f).symm
    _ = (f ^ 2) ^ 2 := by rw [ZMod.expand_card, ZMod.expand_card]
    _ = f ^ 4 := by rw [← pow_mul]

theorem decomposition_card (m : ℕ) (f : P) (hf : f.natDegree ≤ 2 ^ m - 1) :
    ((1 + X : P) * (((1 + X) ^ (2 ^ (m + 2) - 2) + f ^ 4).comp (X ^ 2) +
      X * (((1 + X) * f ^ 4).comp (X ^ 2)))).support.card = 2 ^ (m + 2) := by
  let s : ℕ := 2 ^ m
  have hp : 0 < s := by dsimp [s]; positivity
  have hp2 : 2 ^ (m + 1) = 2 * s := by rw [pow_succ, mul_comm]
  have hp4 : 2 ^ (m + 2) = 4 * s := by rw [pow_add, mul_comm]; rfl
  have hg := geometric_pow_two (m + 1)
  rw [hp2] at hg
  have hb : (1 + X : P) ^ (4 * s - 2) = expand (ZMod 2) 2 (geometric (2 * s)) := by
    rw [show 4 * s - 2 = (2 * s - 1) * 2 by omega, pow_mul, hg, ZMod.expand_card]
  rw [hp4]
  have hid :
      (1 + X) * (((1 + X) ^ (4 * s - 2) + f ^ 4).comp (X ^ 2) +
        X * (((1 + X) * f ^ 4).comp (X ^ 2))) = combined s f := by
    rw [hb, ← expand_four_eq_fourth_pow]
    simp only [← expand_eq_comp_X_pow, map_add, map_mul, map_one, expand_X, expand_expand]
    unfold combined
    let a := expand (ZMod 2) 4 (geometric (2 * s))
    let b := expand (ZMod 2) 8 f
    change (1 + X) * (a + b + X * ((1 + X ^ 2) * b)) =
      (1 + X) * a + (1 + X ^ 2 + X ^ 3 + X ^ 4) * b
    calc
      _ = (1 + X) * a + (1 + X ^ 2 + X ^ 3 + X ^ 4) * b + (2 : P) * X * b := by ring
      _ = _ := by rw [show (2 : P) = 0 from CharTwo.two_eq_zero, zero_mul, zero_mul, add_zero]
  rw [hid]
  apply combined_card
  exact lt_of_le_of_lt hf (by omega)

theorem column_special_card (m : ℕ) :
    (OMAQueenPolynomial.column (2 ^ (m + 2) - 2)).support.card = 2 ^ (m + 2) := by
  rw [OMAQueenPolynomial.column_special]
  exact decomposition_card m _ (OMAQueenPolynomial.fourthBase_natDegree m)

end OMAQueenSupport

namespace OMA.Proof_oeis_a338276

open OMA.S_oeis_a338276

theorem oddCount_eq_card_support (k : ℕ) (f : Polynomial (ZMod 2))
    (hcoeff : ∀ r : ℕ, f.coeff r = (queenPaths (r + 1) k : ZMod 2)) :
    oddCount k = f.support.card := by
  have hmem (r : ℕ) : r ∈ f.support ↔ Odd (queenPaths (r + 1) k) := by
    simp only [Polynomial.mem_support_iff, hcoeff, ne_eq, ZMod.natCast_eq_zero_iff_even,
      Nat.not_even_iff_odd]
  have hset : {r : ℕ | 0 < r ∧ Odd (queenPaths r k)} =
      Nat.succ '' (↑f.support : Set ℕ) := by
    ext r
    change (0 < r ∧ Odd (queenPaths r k)) ↔ ∃ s ∈ f.support, Nat.succ s = r
    constructor
    · rintro ⟨hr, hodd⟩
      obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
      exact ⟨s, (hmem s).2 hodd, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨Nat.succ_pos s, (hmem s).1 hs⟩
  rw [oddCount, hset, Set.ncard_image_of_injective _ Nat.succ_injective,
    Set.ncard_coe_finset]

theorem card_support_base : (1 + Polynomial.X : Polynomial (ZMod 2)).support.card = 2 := by
  have hs : (1 + Polynomial.X : Polynomial (ZMod 2)).support = {0, 1} := by
    ext r
    rcases r with _ | _ | r <;>
      simp [Polynomial.mem_support_iff, Polynomial.coeff_add, Polynomial.coeff_one,
        Polynomial.coeff_X]
  rw [hs]
  decide

end OMA.Proof_oeis_a338276

open OMA.S_oeis_a338276

/-- The sums for the three directions give a characteristic-two column recurrence.
The support of a target column then breaks into blocks of eight with four nonzero
coefficients each. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a338276.main := by
  intro n hn
  have hmatch := OMAQueenPolynomial.column_matches OMAQueenRecurrence.q
    OMAQueenRecurrence.q_zero OMAQueenRecurrence.q_one OMAQueenRecurrence.q_recurrence
  have hcount (k : ℕ) : oddCount (k + 1) = (OMAQueenPolynomial.column k).support.card :=
    OMA.Proof_oeis_a338276.oddCount_eq_card_support (k + 1) _ (fun r => (hmatch r k).symm)
  by_cases hn₁ : n = 1
  · subst n
    change oddCount (0 + 1) = 2
    rw [hcount, OMAQueenPolynomial.column_zero]
    exact OMA.Proof_oeis_a338276.card_support_base
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
    have hp : 2 ≤ (2 : ℕ) ^ (m + 2) := by
      have hpos : 0 < (2 : ℕ) ^ m := by positivity
      rw [pow_add]
      norm_num
      omega
    have hindex : 2 ^ (m + 2) - 1 = (2 ^ (m + 2) - 2) + 1 := by omega
    rw [hindex, hcount]
    exact OMAQueenSupport.column_special_card m
