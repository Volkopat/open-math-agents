import OMAStatements.S_oeis_a077864

namespace OMA.P077864

open OMA.S_oeis_a077864 Finset Polynomial

/-- The companion sequence, with the same recurrence. -/
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | n + 4 => 2 * b (n + 3) + b (n + 2) - b (n + 1) - b n

lemma a_rec (n : ℕ) : a (n + 4) = 2 * a (n + 3) + a (n + 2) - a (n + 1) - a n := by
  rw [a]

lemma b_rec (n : ℕ) : b (n + 4) = 2 * b (n + 3) + b (n + 2) - b (n + 1) - b n := by
  rw [b]

lemma link (n : ℕ) :
    (a (n + 2) = a (n + 1) + b (n + 3) + a n ∧ b (n + 4) = b (n + 3) + b (n + 2) + a n)
    ∧ (a (n + 3) = a (n + 2) + b (n + 4) + a (n + 1)
      ∧ b (n + 5) = b (n + 4) + b (n + 3) + a (n + 1))
    ∧ (a (n + 4) = a (n + 3) + b (n + 5) + a (n + 2)
      ∧ b (n + 6) = b (n + 5) + b (n + 4) + a (n + 2))
    ∧ (a (n + 5) = a (n + 4) + b (n + 6) + a (n + 3)
      ∧ b (n + 7) = b (n + 6) + b (n + 5) + a (n + 3)) := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨⟨p0, q0⟩, ⟨p1, q1⟩, ⟨p2, q2⟩, ⟨p3, q3⟩⟩ := ih
    have a4 : a (n + 4) = 2 * a (n + 3) + a (n + 2) - a (n + 1) - a n := a_rec n
    have a5 : a (n + 5) = 2 * a (n + 4) + a (n + 3) - a (n + 2) - a (n + 1) := a_rec (n + 1)
    have a6 : a (n + 6) = 2 * a (n + 5) + a (n + 4) - a (n + 3) - a (n + 2) := a_rec (n + 2)
    have b6 : b (n + 6) = 2 * b (n + 5) + b (n + 4) - b (n + 3) - b (n + 2) := b_rec (n + 2)
    have b7 : b (n + 7) = 2 * b (n + 6) + b (n + 5) - b (n + 4) - b (n + 3) := b_rec (n + 3)
    have b8 : b (n + 8) = 2 * b (n + 7) + b (n + 6) - b (n + 5) - b (n + 4) := b_rec (n + 4)
    refine ⟨⟨p1, q1⟩, ⟨p2, q2⟩, ⟨p3, q3⟩, ?_, ?_⟩
    · show a (n + 6) = a (n + 5) + b (n + 7) + a (n + 4)
      linarith
    · show b (n + 8) = b (n + 7) + b (n + 6) + a (n + 4)
      linarith

lemma Tcongr {m m1 k k1 : ℕ} (h1 : m = m1) (h2 : k = k1) : T m k = T m1 k1 := by
  subst h1; subst h2; rfl

lemma hp (m : ℕ) : (1 + X + X ^ 2 : ℤ[X]) ^ (m + 1)
    = (1 + X + X ^ 2) ^ m + (1 + X + X ^ 2) ^ m * X + (1 + X + X ^ 2) ^ m * X ^ 2 := by
  ring

lemma T00 : T 0 0 = 1 := by simp [T]

lemma Tz (k : ℕ) : T 0 (k + 1) = 0 := by simp [T, coeff_one]

lemma ts0 (m : ℕ) : T (m + 1) 0 = T m 0 := by
  unfold T
  rw [hp m, coeff_add, coeff_add]
  simp [mul_coeff_zero]

lemma ts1 (m : ℕ) : T (m + 1) 1 = T m 1 + T m 0 := by
  unfold T
  rw [hp m, coeff_add, coeff_add]
  have h1 : (((1 + X + X ^ 2 : ℤ[X]) ^ m) * X).coeff 1 = ((1 + X + X ^ 2 : ℤ[X]) ^ m).coeff 0 :=
    coeff_mul_X _ 0
  have h2 : (((1 + X + X ^ 2 : ℤ[X]) ^ m) * X ^ 2).coeff 1 = 0 := by
    rw [coeff_mul_X_pow']
    simp
  rw [h1, h2, add_zero]

lemma ts (m k : ℕ) : T (m + 1) (k + 2) = T m (k + 2) + T m (k + 1) + T m k := by
  unfold T
  rw [hp m, coeff_add, coeff_add, coeff_mul_X_pow, coeff_mul_X]

lemma ts2 (m k k1 k2 : ℕ) (h1 : k1 = k + 1) (h2 : k2 = k + 2) :
    T (m + 1) k2 = T m k2 + T m k1 + T m k := by
  subst h1; subst h2; exact ts m k

lemma Tbig (m : ℕ) : ∀ k : ℕ, 2 * m < k → T m k = 0 := by
  induction m with
  | zero =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact Tz j
  | succ m ih =>
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [ts, ih _ (by omega), ih _ (by omega), ih _ (by omega)]
    simp

/-- Odd diagonal sums, over all j up to n. -/
noncomputable def U (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), T (n + 1 - j) (2 * j + 1)

/-- Even diagonal sums, over all j up to n. -/
noncomputable def V (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), T (n - j) (2 * j)

lemma hE (n : ℕ) : U (n + 1) = T (n + 2) 1 + ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 3) := by
  have hl : ∑ j ∈ range (n + 1 + 1), T (n + 1 + 1 - j) (2 * j + 1)
      = ∑ j ∈ range (n + 1), T (n + 1 + 1 - (j + 1)) (2 * (j + 1) + 1)
        + T (n + 1 + 1 - 0) (2 * 0 + 1) := sum_range_succ' _ _
  have hr : ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 3)
      = ∑ j ∈ range (n + 1), T (n + 1 - j) (2 * j + 3)
        + T (n + 1 - (n + 1)) (2 * (n + 1) + 3) := sum_range_succ _ _
  have hc : ∑ j ∈ range (n + 1), T (n + 1 + 1 - (j + 1)) (2 * (j + 1) + 1)
      = ∑ j ∈ range (n + 1), T (n + 1 - j) (2 * j + 3) :=
    sum_congr rfl (fun j _ => Tcongr (by omega) (by omega))
  have z : T (n + 1 - (n + 1)) (2 * (n + 1) + 3) = 0 := Tbig _ _ (by omega)
  have f0 : T (n + 1 + 1 - 0) (2 * 0 + 1) = T (n + 2) 1 := Tcongr (by omega) (by omega)
  unfold U
  rw [hl, hr, hc, z, f0]
  ring

lemma hA (n : ℕ) : V (n + 2) = T (n + 2) 0 + ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 2) := by
  have hl : ∑ j ∈ range (n + 2 + 1), T (n + 2 - j) (2 * j)
      = ∑ j ∈ range (n + 2), T (n + 2 - (j + 1)) (2 * (j + 1))
        + T (n + 2 - 0) (2 * 0) := sum_range_succ' _ _
  have hc : ∑ j ∈ range (n + 2), T (n + 2 - (j + 1)) (2 * (j + 1))
      = ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 2) :=
    sum_congr rfl (fun j _ => Tcongr (by omega) (by omega))
  have f0 : T (n + 2 - 0) (2 * 0) = T (n + 2) 0 := Tcongr (by omega) (by omega)
  unfold V
  rw [hl, hc, f0]
  ring

lemma hB (n : ℕ) : U n = ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 1) := by
  have hr : ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j + 1)
      = ∑ j ∈ range (n + 1), T (n + 1 - j) (2 * j + 1)
        + T (n + 1 - (n + 1)) (2 * (n + 1) + 1) := sum_range_succ _ _
  have z : T (n + 1 - (n + 1)) (2 * (n + 1) + 1) = 0 := Tbig _ _ (by omega)
  unfold U
  rw [hr, z, add_zero]

lemma hC (n : ℕ) : V (n + 1) = ∑ j ∈ range (n + 2), T (n + 1 - j) (2 * j) := rfl

lemma R1 (n : ℕ) : U (n + 2) = U (n + 1) + V (n + 2) + U n := by
  have hl : ∑ j ∈ range (n + 2 + 1), T (n + 2 + 1 - j) (2 * j + 1)
      = ∑ j ∈ range (n + 2), T (n + 2 + 1 - (j + 1)) (2 * (j + 1) + 1)
        + T (n + 2 + 1 - 0) (2 * 0 + 1) := sum_range_succ' _ _
  have hc : ∑ j ∈ range (n + 2), T (n + 2 + 1 - (j + 1)) (2 * (j + 1) + 1)
      = ∑ j ∈ range (n + 2), (T (n + 1 - j) (2 * j + 3) + T (n + 1 - j) (2 * j + 2)
        + T (n + 1 - j) (2 * j + 1)) := by
    refine sum_congr rfl (fun j hj => ?_)
    have hj2 := mem_range.mp hj
    exact (Tcongr (by omega) (by omega)).trans
      (ts2 (n + 1 - j) (2 * j + 1) (2 * j + 2) (2 * j + 3) (by omega) (by omega))
  have f0 : T (n + 2 + 1 - 0) (2 * 0 + 1) = T (n + 2) 1 + T (n + 2) 0 :=
    (Tcongr (by omega) (by omega)).trans (ts1 (n + 2))
  have h : U (n + 2) = ∑ j ∈ range (n + 2), (T (n + 1 - j) (2 * j + 3)
      + T (n + 1 - j) (2 * j + 2) + T (n + 1 - j) (2 * j + 1))
      + (T (n + 2) 1 + T (n + 2) 0) := by
    unfold U
    rw [hl, hc, f0]
  rw [h, sum_add_distrib, sum_add_distrib, hE, hA, hB]
  ring

lemma R2 (n : ℕ) : V (n + 3) = V (n + 2) + V (n + 1) + U n := by
  have hl : ∑ j ∈ range (n + 3 + 1), T (n + 3 - j) (2 * j)
      = ∑ j ∈ range (n + 3), T (n + 3 - (j + 1)) (2 * (j + 1))
        + T (n + 3 - 0) (2 * 0) := sum_range_succ' _ _
  have hs : ∑ j ∈ range (n + 3), T (n + 3 - (j + 1)) (2 * (j + 1))
      = ∑ j ∈ range (n + 2), T (n + 3 - (j + 1)) (2 * (j + 1))
        + T (n + 3 - (n + 2 + 1)) (2 * (n + 2 + 1)) := sum_range_succ _ _
  have z : T (n + 3 - (n + 2 + 1)) (2 * (n + 2 + 1)) = 0 := Tbig _ _ (by omega)
  have hc : ∑ j ∈ range (n + 2), T (n + 3 - (j + 1)) (2 * (j + 1))
      = ∑ j ∈ range (n + 2), (T (n + 1 - j) (2 * j + 2) + T (n + 1 - j) (2 * j + 1)
        + T (n + 1 - j) (2 * j)) := by
    refine sum_congr rfl (fun j hj => ?_)
    have hj2 := mem_range.mp hj
    exact (Tcongr (by omega) (by omega)).trans
      (ts2 (n + 1 - j) (2 * j) (2 * j + 1) (2 * j + 2) (by omega) (by omega))
  have f0 : T (n + 3 - 0) (2 * 0) = T (n + 2) 0 :=
    (Tcongr (by omega) (by omega)).trans (ts0 (n + 2))
  have h : V (n + 3) = ∑ j ∈ range (n + 2), (T (n + 1 - j) (2 * j + 2)
      + T (n + 1 - j) (2 * j + 1) + T (n + 1 - j) (2 * j)) + 0 + T (n + 2) 0 := by
    unfold V
    rw [hl, hs, hc, z, f0]
  rw [h, sum_add_distrib, sum_add_distrib, hA, hC, hB]
  ring

lemma T10 : T 1 0 = 1 := by rw [ts0, T00]

lemma T11 : T 1 1 = 1 := by rw [ts1, Tz, T00]; rfl

lemma T12 : T 1 2 = 1 := by rw [ts 0 0, Tz, Tz, T00]; rfl

lemma T20 : T 2 0 = 1 := by rw [ts0, T10]

lemma T21 : T 2 1 = 2 := by rw [ts1, T11, T10]; rfl

lemma T13 : T 1 3 = 0 := Tbig _ _ (by omega)

lemma T02 : T 0 2 = 0 := Tbig _ _ (by omega)

lemma T04 : T 0 4 = 0 := Tbig _ _ (by omega)

lemma uv (n : ℕ) : U n = a n ∧ U (n + 1) = a (n + 1) ∧ V n = b (n + 1)
    ∧ V (n + 1) = b (n + 2) ∧ V (n + 2) = b (n + 3) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [U, T11, a]
    · simp [U, sum_range_succ, T21, T13, a]
    · simp [V, T00, b]
    · simp [V, sum_range_succ, T10, T02, b]
    · simp [V, sum_range_succ, T20, T12, T04, b]
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    obtain ⟨⟨p0, q0⟩, _⟩ := link n
    have r1 := R1 n
    have r2 := R2 n
    refine ⟨h2, ?_, h4, h5, ?_⟩
    · show U (n + 2) = a (n + 2)
      linarith
    · show V (n + 3) = b (n + 4)
      linarith

end OMA.P077864

open OMA.S_oeis_a077864 OMA.P077864 in
theorem OMA.solution : type_of% @OMA.S_oeis_a077864.main := by
  intro n
  rw [← (uv n).1]
  unfold U
  symm
  refine Finset.sum_subset (Finset.range_mono (by omega)) (fun j hj hnj => ?_)
  have h1 := Finset.mem_range.mp hj
  have h2 : ¬ j < n / 2 + 1 := fun h => hnj (Finset.mem_range.mpr h)
  exact Tbig _ _ (by omega)
