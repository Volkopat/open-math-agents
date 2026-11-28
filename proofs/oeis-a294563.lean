import OMAStatements.S_oeis_a294563
import Mathlib

/-!
# A294563: the ratio `a(n+1) / a(n)` tends to the golden ratio

Write the recurrence as `a(n) = a(n-1) + a(n-2) + c(n)`.  In every case `c(n) ≥ 0` and
`c(n) ≤ 4 b(n-1) + 3n + 3`.

* **`b` grows at most linearly.**  From `a(k+1) ≥ a(k) + a(k-1)` and `a(k) ≥ k + 1`, consecutive
  values of `a` differ by at least `2` from index `2` on.  So for `m ≥ a(1)` one of `m + 1`,
  `m + 2` is not a value of `a`, hence is a value of `b`; this gives `b(j) ≤ b(0) + a(1) + 2j`.
* **`a` grows at least quadratically.**  `a(n+1) ≥ a(n) + n` gives `(n+1)² ≤ 3 a(n+1)`.
* Hence `e(n) = c(n+2) / a(n+1) ≤ K / (n + 1) → 0`.
* The ratios `r(n) = a(n+1) / a(n) ≥ 1` satisfy `r(n+1) = 1 + 1 / r(n) + e(n)`, and since
  `φ = 1 + 1 / φ`, `|r(n+1) - φ| ≤ |r(n) - φ| / φ + e(n)`.  A contraction with a vanishing
  perturbation tends to `0`.
-/

namespace OMA.S_oeis_a294563

open Filter Topology

/-- A sequence contracted by a factor `q < 1` up to an error tending to `0` tends to `0`. -/
lemma tendsto_zero_of_contract (d e : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hd : ∀ n, 0 ≤ d n) (hstep : ∀ n, d (n + 1) ≤ q * d n + e n)
    (he : Tendsto e atTop (𝓝 0)) : Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hq' : 0 < 1 - q := by linarith
  have hδ : 0 < ε * (1 - q) / 2 := by positivity
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (he.eventually (gt_mem_nhds hδ))
  -- from `N1` on, `d` is below a geometric term plus `ε / 2`
  have hbound : ∀ k, d (N1 + k) ≤ q ^ k * d N1 + ε / 2 := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, one_mul, Nat.add_zero]
      linarith
    | succ k ih =>
      have h1 := hstep (N1 + k)
      have h2 := hN1 (N1 + k) (Nat.le_add_right _ _)
      have h3 : q * d (N1 + k) ≤ q * (q ^ k * d N1 + ε / 2) := mul_le_mul_of_nonneg_left ih hq0
      have h4 : q * (q ^ k * d N1 + ε / 2) = q ^ (k + 1) * d N1 + q * ε / 2 := by ring
      have h5 : ε * (1 - q) / 2 = ε / 2 - q * ε / 2 := by ring
      have e1 : N1 + (k + 1) = N1 + k + 1 := rfl
      rw [e1]
      linarith
  have hpow : Tendsto (fun k => q ^ k * d N1) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (d N1)
    simpa using this
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpow.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N1 + N2, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = N1 + k := ⟨n - N1, by omega⟩
  have h1 := hbound k
  have h2 := hN2 k (by omega)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd _)]
  linarith

/-- The ratio of consecutive terms. -/
noncomputable def ratio (a : ℕ → ℕ) (n : ℕ) : ℝ := (a (n + 1) : ℝ) / (a n : ℝ)

/-- The relative size of the correction term. -/
noncomputable def err (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((a (n + 2) : ℝ) - (a (n + 1) : ℝ) - (a n : ℝ)) / (a (n + 1) : ℝ)

/-- The general statement behind the conjecture. -/
theorem golden (a b : ℕ → ℕ) (ha : StrictMono a) (hb : StrictMono b)
    (hcov : ∀ m : ℕ, 0 < m → (m ∈ Set.range a ↔ m ∉ Set.range b)) (ha0 : 1 ≤ a 0)
    (hrec : ∀ n, 2 ≤ n → a (n - 1) + a (n - 2) ≤ a n ∧
      a n ≤ a (n - 1) + a (n - 2) + 4 * b (n - 1) + 3 * n + 3) :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 ((1 + Real.sqrt 5) / 2)) := by
  -- the recurrence, shifted
  have hlo : ∀ n, a (n + 1) + a n ≤ a (n + 2) := by
    intro n
    have h := (hrec (n + 2) (by omega)).1
    have e1 : n + 2 - 1 = n + 1 := by omega
    have e2 : n + 2 - 2 = n := by omega
    rw [e1, e2] at h
    exact h
  have hhi : ∀ n, a (n + 2) ≤ a (n + 1) + a n + 4 * b (n + 1) + 3 * n + 9 := by
    intro n
    have h := (hrec (n + 2) (by omega)).2
    have e1 : n + 2 - 1 = n + 1 := by omega
    have e2 : n + 2 - 2 = n := by omega
    rw [e1, e2] at h
    omega
  -- `a n ≥ n + 1`
  have a_ge : ∀ n, n + 1 ≤ a n := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      have : a n < a (n + 1) := ha (Nat.lt_succ_self n)
      omega
  -- consecutive values of `a` differ by at least two from index `2` on
  have gap : ∀ k, 2 ≤ k → a k + 2 ≤ a (k + 1) := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 := hlo j
    have h2 := a_ge j
    show a (j + 1) + 2 ≤ a (j + 2)
    omega
  -- above `a 1`, one of two consecutive numbers is a value of `b`
  have G : ∀ m, a 1 ≤ m → ∃ i, b i = m + 1 ∨ b i = m + 2 := by
    intro m hm
    by_contra hcon
    have hcon' : ∀ i, ¬ (b i = m + 1 ∨ b i = m + 2) := not_exists.mp hcon
    obtain ⟨k, hk⟩ := (hcov (m + 1) (by omega)).mpr (fun ⟨i, hi⟩ => hcon' i (Or.inl hi))
    obtain ⟨k', hk'⟩ := (hcov (m + 2) (by omega)).mpr (fun ⟨i, hi⟩ => hcon' i (Or.inr hi))
    have hk1 : 1 < k := ha.lt_iff_lt.mp (by omega)
    have hkk : k < k' := ha.lt_iff_lt.mp (by omega)
    have h1 := ha.monotone (show k + 1 ≤ k' by omega)
    have h2 := gap k (by omega)
    omega
  -- hence `b` grows at most linearly
  have b_lin : ∀ j, max (b j) (a 1) ≤ b 0 + a 1 + 2 * j := by
    intro j
    induction j with
    | zero => exact max_le (by omega) (by omega)
    | succ j ih =>
      obtain ⟨i, hi⟩ := G (max (b j) (a 1)) (le_max_right _ _)
      have h1 : b j ≤ max (b j) (a 1) := le_max_left _ _
      have h3 : a 1 ≤ max (b j) (a 1) := le_max_right _ _
      have hji : j < i := hb.lt_iff_lt.mp (by rcases hi with h | h <;> omega)
      have h2 : b (j + 1) ≤ b i := hb.monotone (by omega)
      refine max_le ?_ ?_ <;> rcases hi with h | h <;> omega
  have b_le : ∀ j, b j ≤ b 0 + a 1 + 2 * j := fun j => (le_max_left _ _).trans (b_lin j)
  -- and `a` grows at least quadratically
  have a_quad : ∀ j, (j + 1) * (j + 1) + 2 ≤ 2 * a (j + 1) + (j + 1) := by
    intro j
    induction j with
    | zero =>
      have := a_ge 1
      show 1 * 1 + 2 ≤ 2 * a 1 + 1
      omega
    | succ j ih =>
      have h1 := hlo j
      have h2 := a_ge j
      show (j + 2) * (j + 2) + 2 ≤ 2 * a (j + 2) + (j + 2)
      nlinarith
  have apos : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n => by
    have := a_ge n
    exact Nat.cast_pos.mpr (by omega)
  -- the golden ratio
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs1 : (1 : ℝ) < Real.sqrt 5 := by
    have : Real.sqrt 1 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_one] at this
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = (1 + Real.sqrt 5) / 2 := ⟨_, rfl⟩
  rw [← hφ]
  have hφ1 : 1 < φ := by rw [hφ]; linarith
  have hφ2 : φ * φ = φ + 1 := by rw [hφ]; nlinarith
  have hφpos : 0 < φ := by linarith
  have hφeq : φ = 1 + 1 / φ := by
    field_simp
    linarith
  -- ratios and errors
  have hr1 : ∀ n, 1 ≤ ratio a n := by
    intro n
    unfold ratio
    rw [le_div_iff₀ (apos n), one_mul]
    exact_mod_cast (ha (Nat.lt_succ_self n)).le
  have he0 : ∀ n, 0 ≤ err a n := by
    intro n
    unfold err
    have h : ((a (n + 1) + a n : ℕ) : ℝ) ≤ (a (n + 2) : ℝ) := Nat.cast_le.mpr (hlo n)
    push_cast at h
    exact div_nonneg (by linarith) (apos _).le
  have hrr : ∀ n, ratio a (n + 1) = 1 + 1 / ratio a n + err a n := by
    intro n
    unfold ratio err
    have h1 := (apos n).ne'
    have h2 := (apos (n + 1)).ne'
    field_simp
    ring
  -- the contraction step
  have hstep : ∀ n, |ratio a (n + 1) - φ| ≤ 1 / φ * |ratio a n - φ| + err a n := by
    intro n
    have hrpos : 0 < ratio a n := by linarith [hr1 n]
    have h1 : ratio a (n + 1) - φ = (1 / ratio a n - 1 / φ) + err a n := by
      rw [hrr n]
      linarith
    have h2 : 1 / ratio a n - 1 / φ = (φ - ratio a n) / (ratio a n * φ) := by
      field_simp
    have h3 : |ratio a n - φ| / (ratio a n * φ) ≤ |ratio a n - φ| / φ :=
      div_le_div_of_nonneg_left (abs_nonneg _) hφpos (by nlinarith [hr1 n])
    have h4 : |ratio a n - φ| / φ = 1 / φ * |ratio a n - φ| := by ring
    calc |ratio a (n + 1) - φ| = |(φ - ratio a n) / (ratio a n * φ) + err a n| := by rw [h1, h2]
      _ ≤ |(φ - ratio a n) / (ratio a n * φ)| + |err a n| := abs_add_le _ _
      _ = |ratio a n - φ| / (ratio a n * φ) + err a n := by
          rw [abs_div, abs_of_pos (mul_pos hrpos hφpos), abs_sub_comm, abs_of_nonneg (he0 n)]
      _ ≤ 1 / φ * |ratio a n - φ| + err a n := by linarith
  -- the errors tend to zero
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 4 * (b 0 : ℝ) + 4 * (a 1 : ℝ) + 28 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  have he_le : ∀ n, err a n ≤ 3 * C * (1 / ((n : ℝ) + 1)) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    -- numerator
    have hX : (a (n + 2) : ℝ) - (a (n + 1) : ℝ) - (a n : ℝ) ≤ C * ((n : ℝ) + 1) := by
      have h1 := hhi n
      have h2 := b_le (n + 1)
      have h3 : a (n + 2) ≤ a (n + 1) + a n + 11 * n + 4 * b 0 + 4 * a 1 + 17 := by omega
      have h4 : ((a (n + 2) : ℕ) : ℝ) ≤ ((a (n + 1) + a n + 11 * n + 4 * b 0 + 4 * a 1 + 17 : ℕ) : ℝ) :=
        Nat.cast_le.mpr h3
      push_cast at h4
      have h5 : 0 ≤ (4 * (b 0 : ℝ) + 4 * (a 1 : ℝ) + 17) * (n : ℝ) := by positivity
      rw [hC]
      nlinarith
    -- denominator
    have hA : ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ 3 * (a (n + 1) : ℝ) := by
      have h1 := a_quad n
      have h2 := a_ge (n + 1)
      have h3 : (n + 1) * (n + 1) ≤ 3 * a (n + 1) := by nlinarith
      have h4 : (((n + 1) * (n + 1) : ℕ) : ℝ) ≤ ((3 * a (n + 1) : ℕ) : ℝ) := Nat.cast_le.mpr h3
      push_cast at h4
      exact h4
    have hmul : ((a (n + 2) : ℝ) - (a (n + 1) : ℝ) - (a n : ℝ)) * ((n : ℝ) + 1) ≤
        3 * C * (a (n + 1) : ℝ) := by
      calc ((a (n + 2) : ℝ) - (a (n + 1) : ℝ) - (a n : ℝ)) * ((n : ℝ) + 1)
          ≤ C * ((n : ℝ) + 1) * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hX (by positivity)
        _ = C * (((n : ℝ) + 1) * ((n : ℝ) + 1)) := by ring
        _ ≤ C * (3 * (a (n + 1) : ℝ)) := mul_le_mul_of_nonneg_left hA hC0
        _ = 3 * C * (a (n + 1) : ℝ) := by ring
    unfold err
    rw [show 3 * C * (1 / ((n : ℝ) + 1)) = 3 * C / ((n : ℝ) + 1) by ring,
      div_le_div_iff₀ (apos _) (by positivity)]
    exact hmul
  have he_tend : Tendsto (err a) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (3 * C)
    rw [mul_zero] at h
    exact squeeze_zero he0 he_le h
  -- conclusion
  have hd := tendsto_zero_of_contract (fun n => |ratio a n - φ|) (err a) (1 / φ) (by positivity)
    (by rw [div_lt_one hφpos]; exact hφ1) (fun n => abs_nonneg _) hstep he_tend
  have hfinal : Tendsto (ratio a) atTop (𝓝 φ) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hd
  exact hfinal

end OMA.S_oeis_a294563

open OMA.S_oeis_a294563 in
theorem OMA.solution : type_of% @OMA.S_oeis_a294563.main := by
  intro a b ha hb hcov ha0 ha1 hb0 hrec
  refine golden a b ha hb hcov (by omega) (fun n hn => ?_)
  -- the specific recurrence gives the two-sided bound
  have h := hrec n hn
  have h1 : n - 1 ≤ b (n - 1) := hb.id_le (n - 1)
  have h2 : n - 2 ≤ b (n - 2) := hb.id_le (n - 2)
  have h3 : b (n - 2) < b (n - 1) := hb (by omega)
  have h4 : b 0 ≤ b (n - 2) := hb.monotone (Nat.zero_le _)
  constructor <;> omega
