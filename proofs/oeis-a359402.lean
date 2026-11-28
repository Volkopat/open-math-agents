import OMAStatements.S_oeis_a359402

-- Sum of the positions 1..L.
theorem oeis_a359402_gauss (L : ℕ) :
    (∑ i ∈ Finset.range L, ((i : ℝ) + 1)) = (L : ℝ) * ((L : ℝ) + 1) / 2 := by
  induction L with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

-- The centred positions sum to zero.
theorem oeis_a359402_sv (L : ℕ) :
    (∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2)) = 0 := by
  rw [Finset.sum_sub_distrib, oeis_a359402_gauss, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

-- Expansion of the squared error of the line b + m x around the horizontal line a.
theorem oeis_a359402_key (L : ℕ) (y : ℕ → ℝ) (a b m : ℝ) :
    (∑ i ∈ Finset.range L, (y i - (b + m * ((i : ℝ) + 1))) ^ 2) -
      (∑ i ∈ Finset.range L, (y i - (a + 0 * ((i : ℝ) + 1))) ^ 2) =
    (∑ i ∈ Finset.range L, ((b + m * (((L : ℝ) + 1) / 2) - a) ^ 2 +
        m ^ 2 * ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) ^ 2)) +
      (-2 * (b + m * (((L : ℝ) + 1) / 2) - a)) * (∑ i ∈ Finset.range L, (y i - a)) +
      (-2 * m) * (∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) * y i) +
      (2 * m * a + 2 * (b + m * (((L : ℝ) + 1) / 2) - a) * m) *
        (∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2)) := by
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

-- Balanced means the covariance of position and value vanishes, which is exactly when the
-- least-squares line is horizontal.
theorem oeis_a359402_gen (L : ℕ) (y : ℕ → ℝ) :
    ((∑ i ∈ Finset.range L, ((i : ℝ) + 1) * y i) =
        ∑ i ∈ Finset.range L, ((L : ℝ) - i) * y i) ↔
    ∃ a : ℝ, ∀ b m : ℝ,
      (∑ i ∈ Finset.range L, (y i - (a + 0 * ((i : ℝ) + 1))) ^ 2) ≤
      ∑ i ∈ Finset.range L, (y i - (b + m * ((i : ℝ) + 1))) ^ 2 := by
  have hSv := oeis_a359402_sv L
  have hbal : (∑ i ∈ Finset.range L, ((i : ℝ) + 1) * y i) -
      (∑ i ∈ Finset.range L, ((L : ℝ) - i) * y i) =
      2 * ∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) * y i := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  constructor
  · intro h
    have hC : (∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) * y i) = 0 := by
      linarith
    refine ⟨(∑ i ∈ Finset.range L, y i) / L, fun b m => ?_⟩
    have hSu : (∑ i ∈ Finset.range L, (y i - (∑ i ∈ Finset.range L, y i) / L)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos L with h0 | h0
      · rw [h0]
        simp
      · have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h0)
        have e : (L : ℝ) * ((∑ i ∈ Finset.range L, y i) / L) = ∑ i ∈ Finset.range L, y i := by
          field_simp
        linarith
    have k := oeis_a359402_key L y ((∑ i ∈ Finset.range L, y i) / L) b m
    rw [hSu, hC, hSv] at k
    have hnn : 0 ≤ ∑ i ∈ Finset.range L,
        ((b + m * (((L : ℝ) + 1) / 2) - (∑ i ∈ Finset.range L, y i) / L) ^ 2 +
          m ^ 2 * ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) ^ 2) :=
      Finset.sum_nonneg fun i _ => by positivity
    linarith
  · rintro ⟨a, ha⟩
    have hV : 0 ≤ ∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    obtain ⟨C, hC⟩ : ∃ C : ℝ,
        (∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) * y i) = C := ⟨_, rfl⟩
    obtain ⟨V, hVe⟩ : ∃ V : ℝ,
        (∑ i ∈ Finset.range L, ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) ^ 2) = V := ⟨_, rfl⟩
    rw [hC] at hbal
    rw [hVe] at hV
    have hd : V + 1 ≠ 0 := by linarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, C = t * (V + 1) := ⟨C / (V + 1), by field_simp⟩
    have k := oeis_a359402_key L y a (a - t * (((L : ℝ) + 1) / 2)) t
    have hc0 : a - t * (((L : ℝ) + 1) / 2) + t * (((L : ℝ) + 1) / 2) - a = 0 := by ring
    rw [hc0, hSv, hC] at k
    have hsum : (∑ i ∈ Finset.range L,
        ((0 : ℝ) ^ 2 + t ^ 2 * ((i : ℝ) + 1 - ((L : ℝ) + 1) / 2) ^ 2)) = t ^ 2 * V := by
      rw [← hVe, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum] at k
    have hle := ha (a - t * (((L : ℝ) + 1) / 2)) t
    have h1 : 0 ≤ t ^ 2 * V - 2 * (t * C) := by linarith
    have e : t * C = t ^ 2 * V + t ^ 2 := by
      rw [ht]
      ring
    have hp : 0 ≤ t ^ 2 * V := mul_nonneg (sq_nonneg t) hV
    have h2 : t ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg t)
    have h3 : t = 0 := by
      have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
      exact this
    have hC0 : C = 0 := by
      rw [ht, h3]
      ring
    linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a359402.main := by
  intro n
  exact oeis_a359402_gen (OMA.S_oeis_a359402.binaryWord n).length
    (fun i => (((OMA.S_oeis_a359402.binaryWord n).getD i 0 : ℕ) : ℝ))
