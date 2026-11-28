import OMAStatements.S_oeis_a295070

/-!
Proof of Kimberling's conjecture for A295070: a(n)/a(n-1) tends to 1.
Our own argument. Since b is strictly increasing with b(0) = 3, b(j) >= j + 3, so
a(n+2) = a(n) + b(n+1) + b(n) >= a(n) + 2n + 7; hence a(j) >= 2j and 2 a(n) >= n^2.
Counting the integers in [1, 2n + 3], which are all terms of a or b, gives b(n) <= 2n + 3.
Then 0 <= a(n+1) - a(n) <= b(n) + b(n-1) <= 4n + 6, so a(n+1)/a(n) - 1 <= 20/n.
-/

namespace OMA.S_oeis_a295070

/-- Counting: if every term a(j) is at least 2j, then b(n) <= 2n + 3. -/
theorem b_le (a b : ℕ → ℕ) (hb : StrictMono b)
    (hc : ∀ m : ℕ, 0 < m → (m ∈ Set.range a ↔ m ∉ Set.range b))
    (ha2 : ∀ j, 2 * j ≤ a j) : ∀ n, b n ≤ 2 * n + 3 := by
  intro n
  by_contra h
  push Not at h
  have hsub : Finset.Icc 1 (2 * n + 3) ⊆
      (Finset.range n).image b ∪ (Finset.range (n + 2)).image a := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    by_cases hma : m ∈ Set.range a
    · obtain ⟨j, rfl⟩ := hma
      right
      refine ⟨j, ?_, rfl⟩
      rw [Finset.mem_range]
      have := ha2 j
      omega
    · have hmb : m ∈ Set.range b := by
        by_contra hmb
        exact hma ((hc m (by omega)).mpr hmb)
      obtain ⟨j, rfl⟩ := hmb
      left
      refine ⟨j, ?_, rfl⟩
      rw [Finset.mem_range]
      exact hb.lt_iff_lt.mp (by omega)
  have h0 := Finset.card_le_card hsub
  have h1 := Finset.card_union_le ((Finset.range n).image b) ((Finset.range (n + 2)).image a)
  have h2 := Finset.card_image_le (s := Finset.range n) (f := b)
  have h3 := Finset.card_image_le (s := Finset.range (n + 2)) (f := a)
  simp only [Nat.card_Icc, Finset.card_range] at h0 h1 h2 h3
  omega

end OMA.S_oeis_a295070

theorem OMA.solution : type_of% @OMA.S_oeis_a295070.main := by
  intro a b ha hb hc h0 h1 hb0 hrec
  have hrec' : ∀ n, a (n + 2) = a n + b (n + 1) + b n := by
    intro n
    have := hrec (n + 2) (by omega)
    simpa using this
  have hbge : ∀ j, j + 3 ≤ b j := by
    intro j
    induction j with
    | zero => omega
    | succ k ih =>
      have := hb (show k < k + 1 by omega)
      omega
  have ha2 : ∀ j, 2 * j ≤ a j ∧ 2 * (j + 1) ≤ a (j + 1) := by
    intro j
    induction j with
    | zero => simp [h0, h1]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, hrec' k]
      have := hbge k
      have := hbge (k + 1)
      have := ih.1
      omega
  have hbl := OMA.S_oeis_a295070.b_le a b hb hc (fun j => (ha2 j).1)
  have hsq : ∀ n, n ^ 2 ≤ 2 * a n ∧ (n + 1) ^ 2 ≤ 2 * a (n + 1) := by
    intro n
    induction n with
    | zero => simp [h0, h1]
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [show k + 1 + 1 = k + 2 by ring, hrec' k]
      have := hbge k
      have := hbge (k + 1)
      nlinarith [ih.1]
  have hdiff : ∀ n, a n ≤ a (n + 1) ∧ a (n + 1) ≤ a n + 4 * n + 6 := by
    intro n
    refine ⟨(ha (show n < n + 1 by omega)).le, ?_⟩
    rcases n with _ | m
    · simp [h0, h1]
    · rw [show m + 1 + 1 = m + 2 by ring, hrec' m]
      have := (ha (show m < m + 1 by omega)).le
      have := hb (show m < m + 1 by omega)
      have := hbl (m + 1)
      omega
  have hpos : ∀ n, 0 < a n := by
    intro n
    rcases n with _ | m
    · omega
    · have := (ha2 (m + 1)).1
      omega
  have hkey : ∀ n, (a (n + 1) : ℝ) / a n = 1 + ((a (n + 1) : ℝ) - a n) / a n := by
    intro n
    have : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    field_simp
    ring
  have hlim : Filter.Tendsto (fun n : ℕ => ((a (n + 1) : ℝ) - a n) / a n) Filter.atTop
      (nhds 0) := by
    have hz : Filter.Tendsto (fun n : ℕ => (20 : ℝ) / n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 20
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hapos : (0 : ℝ) < a n := by exact_mod_cast hpos n
    obtain ⟨d1, d2⟩ := hdiff n
    have e1 : (a n : ℝ) ≤ a (n + 1) := by exact_mod_cast d1
    have e2 : (a (n + 1) : ℝ) ≤ a n + 4 * n + 6 := by exact_mod_cast d2
    have hq : (n : ℝ) ^ 2 ≤ 2 * a n := by exact_mod_cast (hsq n).1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hapos, abs_of_nonneg (by linarith),
      div_le_div_iff₀ hapos (by linarith)]
    nlinarith
  have : (fun n : ℕ => (a (n + 1) : ℝ) / a n) = fun n => 1 + ((a (n + 1) : ℝ) - a n) / a n :=
    funext hkey
  rw [this]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hlim
