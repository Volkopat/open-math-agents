import OMAStatements.S_oeis_a180319

open Finset OMA.S_oeis_a180319

def OMA.V (k n x : ℕ) : ℕ :=
  (if k ≤ x ∧ x - k < n then 1 else 0) + (if x + k < n then 1 else 0)

lemma OMA.tsum (k x : ℕ) (hk : 1 ≤ k) : ∀ m : ℕ,
    (∑ x' ∈ range m, if ((x : ℤ) - (x' : ℤ)).natAbs = k then 1 else 0) = OMA.V k m x := by
  intro m
  unfold OMA.V
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma OMA.g1 (k n : ℕ) : ∀ m : ℕ, m ≤ n →
    (∑ x ∈ range m, if k ≤ x ∧ x - k < n then 1 else 0) = m - k := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro h
    rw [sum_range_succ, ih (by omega)]
    split_ifs <;> omega

lemma OMA.g2 (k n : ℕ) : ∀ m : ℕ,
    (∑ x ∈ range m, if x + k < n then 1 else 0) = min m (n - k) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

lemma OMA.vsum (k n : ℕ) : ∑ x ∈ range n, OMA.V k n x = n - k + (n - k) := by
  unfold OMA.V
  rw [sum_add_distrib, OMA.g1 k n n le_rfl, OMA.g2]
  omega

lemma OMA.fac (f g : ℕ → ℕ) (s t : Finset ℕ) :
    ∑ x ∈ s, ∑ y ∈ t, f x * g y = (∑ x ∈ s, f x) * ∑ y ∈ t, g y := by
  rw [sum_mul]
  exact sum_congr rfl fun x _ => by rw [mul_sum]

lemma OMA.inner (x x' y m : ℕ) :
    (∑ y' ∈ range m, if (((x : ℤ) - (x' : ℤ)).natAbs = 1 ∧ ((y : ℤ) - (y' : ℤ)).natAbs = 2) ∨
        (((x : ℤ) - (x' : ℤ)).natAbs = 2 ∧ ((y : ℤ) - (y' : ℤ)).natAbs = 1) then 1 else 0) =
      (if ((x : ℤ) - (x' : ℤ)).natAbs = 1 then 1 else 0) *
          (∑ y' ∈ range m, if ((y : ℤ) - (y' : ℤ)).natAbs = 2 then 1 else 0) +
        (if ((x : ℤ) - (x' : ℤ)).natAbs = 2 then 1 else 0) *
          (∑ y' ∈ range m, if ((y : ℤ) - (y' : ℤ)).natAbs = 1 then 1 else 0) := by
  by_cases h1 : ((x : ℤ) - (x' : ℤ)).natAbs = 1
  · simp [h1]
  · by_cases h2 : ((x : ℤ) - (x' : ℤ)).natAbs = 2 <;> simp [h1, h2]

lemma OMA.a_eq (n : ℕ) : a n = (n - 1 + (n - 1)) * (2 * n - 2 + (2 * n - 2)) +
    (n - 2 + (n - 2)) * (2 * n - 1 + (2 * n - 1)) := by
  have e1 := fun x : ℕ => OMA.tsum 1 x le_rfl
  have e2 := fun x : ℕ => OMA.tsum 2 x (by norm_num)
  unfold a board
  rw [card_filter]
  simp only [sum_product, OMA.inner, e1, e2, sum_add_distrib, ← sum_mul]
  rw [OMA.fac (OMA.V 1 n) (OMA.V 2 (2 * n)), OMA.fac (OMA.V 2 n) (OMA.V 1 (2 * n)),
    OMA.vsum, OMA.vsum, OMA.vsum, OMA.vsum]

theorem OMA.solution : type_of% @OMA.S_oeis_a180319.main := by
  have h1 : ∀ n : ℕ, 1 < n → (a n : ℤ) = 4 * (4 - 9 * n + 4 * n ^ 2) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [OMA.a_eq]
    simp only [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega,
      show 2 * (m + 2) - 2 = 2 * m + 2 by omega, show 2 * (m + 2) - 1 = 2 * m + 3 by omega]
    push_cast
    ring
  refine ⟨h1, fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    show (a (m + 5) : ℤ) = 3 * a (m + 4) - 3 * a (m + 3) + a (m + 2)
    rw [h1 (m + 5) (by omega), h1 (m + 4) (by omega), h1 (m + 3) (by omega), h1 (m + 2) (by omega)]
    push_cast
    ring
  · ext k
    have q : ∀ j : ℕ, 1 < j → (a j : ℚ) = 4 * (4 - 9 * j + 4 * j ^ 2) := fun j hj => by
      have := h1 j hj
      exact_mod_cast this
    rw [show ((1 - PowerSeries.X) ^ 3 : PowerSeries ℚ) =
        1 - 3 • PowerSeries.X ^ 1 + 3 • PowerSeries.X ^ 2 - PowerSeries.X ^ 3 by ring,
      show (4 * PowerSeries.X ^ 2 * (2 + 7 * PowerSeries.X - PowerSeries.X ^ 2) : PowerSeries ℚ) =
        8 • PowerSeries.X ^ 2 + 28 • PowerSeries.X ^ 3 - 4 • PowerSeries.X ^ 4 by ring]
    simp only [mul_add, mul_sub, mul_one, mul_smul_comm, map_add, map_sub, map_nsmul,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    by_cases hk : k < 5
    · interval_cases k <;> norm_num [OMA.a_eq]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
      have e1 : m + 5 - 1 = m + 4 := rfl
      have e2 : m + 5 - 2 = m + 3 := rfl
      have e3 : m + 5 - 3 = m + 2 := rfl
      simp only [e1, e2, e3, if_pos (show 1 ≤ m + 5 by omega), if_pos (show 2 ≤ m + 5 by omega),
        if_pos (show 3 ≤ m + 5 by omega), if_neg (show ¬ (m + 5 = 0) by omega),
        if_neg (show ¬ (m + 4 = 0) by omega), if_neg (show ¬ (m + 3 = 0) by omega),
        if_neg (show ¬ (m + 2 = 0) by omega), if_neg (show ¬ (m + 5 = 2) by omega),
        if_neg (show ¬ (m + 5 = 3) by omega), if_neg (show ¬ (m + 5 = 4) by omega),
        q (m + 5) (by omega), q (m + 4) (by omega), q (m + 3) (by omega), q (m + 2) (by omega),
        nsmul_eq_mul]
      push_cast
      ring
