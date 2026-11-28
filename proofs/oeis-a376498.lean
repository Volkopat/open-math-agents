import OMAStatements.S_oeis_a376498
import Mathlib

-- Problem: A376498: Array read by ascending antidiagonals: A(n, k) = 2^k*Sum_{j=1..n} cos((2*j - 1)*Pi/(2*n + 1))^k.
-- Upstream: formal-conjectures statements/oeis-a376498.lean:0 (declaration OMA.S_oeis_a376498.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a376498

lemma OMA.aux_sum_int {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ j, ∃ z : ℤ, f j = z) :
    ∃ z : ℤ, ∑ j ∈ s, f j = z := by
  choose g hg using h
  exact ⟨∑ j ∈ s, g j, by push_cast; exact Finset.sum_congr rfl (fun j _ => hg j)⟩

lemma OMA.aux_cos_int (m : ℤ) : ∃ z : ℤ, Real.cos (m * Real.pi) = z := by
  rw [Real.cos_int_mul_pi]
  rcases Int.even_or_odd m with h | h
  · exact ⟨1, by rw [h.neg_one_zpow]; norm_num⟩
  · exact ⟨-1, by rw [h.neg_one_zpow]; norm_num⟩

lemma OMA.aux_tele (α : ℝ) (m : ℕ) :
    Real.sin α * ∑ j ∈ Finset.range m, 2 * Real.cos ((2 * (j:ℝ) + 1) * α)
      = Real.sin (2 * m * α) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : (2 * ((m + 1 : ℕ) : ℝ) * α) = (2 * (m:ℝ) + 1) * α + α := by push_cast; ring
    have e2 : (2 * (m : ℝ) * α) = (2 * (m:ℝ) + 1) * α - α := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring

lemma OMA.aux_base (n r : ℕ) :
    ∃ z : ℤ, ∑ j ∈ Finset.range n, 2 * Real.cos (r * theta n j) = z := by
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = r * Real.pi / (2 * n + 1) := ⟨_, rfl⟩
  have hpos : (0:ℝ) < 2 * n + 1 := by positivity
  have hth : ∀ j : ℕ, (r:ℝ) * theta n j = (2 * (j:ℝ) + 1) * α := by
    intro j
    unfold theta
    rw [hα]
    field_simp
  simp_rw [hth]
  by_cases h : Real.sin α = 0
  · obtain ⟨l, hl⟩ := Real.sin_eq_zero_iff.mp h
    apply OMA.aux_sum_int
    intro j
    obtain ⟨z, hz⟩ := OMA.aux_cos_int ((2 * (j:ℤ) + 1) * l)
    refine ⟨2 * z, ?_⟩
    have key : (2 * (j:ℝ) + 1) * α = (((2 * (j:ℤ) + 1) * l : ℤ) : ℝ) * Real.pi := by
      rw [← hl]; push_cast; ring
    rw [key, hz]
    push_cast
    ring
  · have ht := OMA.aux_tele α n
    have e : 2 * (n:ℝ) * α = r * Real.pi - α := by
      rw [hα]; field_simp; ring
    rw [e, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi] at ht
    refine ⟨-(-1)^r, ?_⟩
    push_cast
    have h2 : Real.sin α * ∑ j ∈ Finset.range n, 2 * Real.cos ((2 * (j:ℝ) + 1) * α)
        = Real.sin α * (-(-1)^r) := by rw [ht]; ring
    exact mul_left_cancel₀ h h2

lemma OMA.aux_P (n : ℕ) : ∀ k r : ℕ,
    ∃ z : ℤ, ∑ j ∈ Finset.range n,
      (2 * Real.cos (theta n j)) ^ k * (2 * Real.cos (r * theta n j)) = z := by
  intro k
  induction k with
  | zero => intro r; simpa using OMA.aux_base n r
  | succ k ih =>
    intro r
    cases r with
    | zero =>
      obtain ⟨z, hz⟩ := ih 1
      refine ⟨2 * z, ?_⟩
      push_cast
      rw [← hz, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [zero_mul, Real.cos_zero, Nat.cast_one, one_mul]
      ring
    | succ s =>
      obtain ⟨z1, hz1⟩ := ih (s + 2)
      obtain ⟨z2, hz2⟩ := ih s
      refine ⟨z1 + z2, ?_⟩
      push_cast
      rw [← hz1, ← hz2, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      have key : 2 * Real.cos (theta n j) * (2 * Real.cos (((s:ℝ) + 1) * theta n j))
          = 2 * Real.cos (((s:ℝ) + 2) * theta n j) + 2 * Real.cos ((s:ℝ) * theta n j) := by
        have e1 : ((s:ℝ) + 2) * theta n j = ((s:ℝ) + 1) * theta n j + theta n j := by ring
        have e2 : (s:ℝ) * theta n j = ((s:ℝ) + 1) * theta n j - theta n j := by ring
        rw [e1, e2, Real.cos_add, Real.cos_sub]
        ring
      linear_combination (2 * Real.cos (theta n j)) ^ k * key

theorem OMA.solution : type_of% @OMA.S_oeis_a376498.main := by
  intro n k
  cases k with
  | zero => exact ⟨n, by simp [entry]⟩
  | succ k =>
    obtain ⟨z, hz⟩ := OMA.aux_P n k 1
    refine ⟨z, ?_⟩
    rw [← hz]
    unfold entry
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_one, one_mul]
    ring
