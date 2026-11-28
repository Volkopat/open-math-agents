import FormalConjectures.ErdosProblems.«264»

open Filter Finset
open scoped Topology

private noncomputable def s : ℕ → {t : ℝ // 2 ≤ t ∧ t ≤ 10}
  | 0 => ⟨2, by norm_num⟩
  | n + 1 =>
    let t : ℝ := (s n).1
    let k : ℝ := ⌊t - 1⌋₊
    let x : ℝ := 2 ^ (n + 8)
    ⟨4 * (t - k + k ^ 2 / (x + k)), by
      have ht := (s n).2
      have hlo : k ≤ t - 1 := Nat.floor_le (by linarith)
      have hhi : t - 1 < k + 1 := Nat.lt_floor_add_one _
      have hx : (256 : ℝ) ≤ x := by
        have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
        dsimp [x]; rw [pow_add]; norm_num; linarith
      have hk0 : 0 ≤ k := Nat.cast_nonneg _
      have hden : 0 < x + k := by linarith
      have herr : k ^ 2 / (x + k) ≤ 1 / 2 := (div_le_iff₀ hden).2 (by nlinarith)
      have herr0 : 0 ≤ k ^ 2 / (x + k) := by positivity
      constructor <;> linarith⟩

theorem OMA.solution : type_of% @Erdos264.erdos_264.parts.i := by
  intro h
  let a (n : ℕ) : ℤ := if n < 8 then 1 else ⌊(s (n - 8)).1 - 1⌋₊
  let r (n : ℕ) : ℝ := 2 / (2 : ℝ) ^ (n + 8) - (s n).1 / ((2 : ℝ) ^ (n + 8)) ^ 2
  have ha (n : ℕ) : 1 ≤ a n ∧ a n ≤ 9 := by
    dsimp [a]; split_ifs
    · norm_num
    · have ht := (s (n - 8)).2
      have h1 : 1 ≤ ⌊(s (n - 8)).1 - 1⌋₊ := Nat.le_floor (by norm_num; linarith)
      have h2 : (⌊(s (n - 8)).1 - 1⌋₊ : ℝ) ≤ 9 := (Nat.floor_le (by linarith)).trans (by linarith)
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have hstep (n : ℕ) : r n - r (n + 1) = 1 / ((2 : ℝ) ^ (n + 8) + ⌊(s n).1 - 1⌋₊) := by
    have hx : (0 : ℝ) < 2 ^ (n + 8) := by positivity
    have hd : (0 : ℝ) < 2 ^ (n + 8) + ⌊(s n).1 - 1⌋₊ := by positivity
    simp only [r, s, pow_succ]
    field_simp [hx.ne', hd.ne']; ring
  have hr : Tendsto r atTop (𝓝 0) :=
    squeeze_zero (fun n => by
      have ht := (s n).2
      have h1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hx : (256 : ℝ) ≤ 2 ^ (n + 8) := by rw [pow_add]; norm_num; linarith
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith)
      (fun n => sub_le_self _ (div_nonneg (by linarith [(s n).2.1]) (sq_nonneg _)))
      (tendsto_const_nhds.div_atTop
        ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
          (tendsto_add_atTop_nat 8)))
  have htail : HasSum (fun n => 1 / ((2 : ℝ) ^ (n + 8) + a (n + 8))) (r 0) := by
    have heq : ∀ n, 1 / ((2 : ℝ) ^ (n + 8) + a (n + 8)) = r n - r (n + 1) := fun n => by
      simp [a, hstep]
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => by have := (ha (n + 8)).1; positivity)]
    simp_rw [heq, Finset.sum_range_sub']
    simpa using (tendsto_const_nhds (x := r 0)).sub hr
  have hsum : HasSum (fun n => 1 / ((2 : ℝ) ^ n + a n))
      ((∑ i ∈ range 8, 1 / ((2 : ℝ) ^ i + a i)) + r 0) :=
    (hasSum_nat_add_iff' 8).mp (by simpa using htail)
  refine h a ⟨9, by rintro _ ⟨n, rfl⟩; exact (ha n).2⟩ ⟨1, by rintro _ ⟨n, rfl⟩; exact (ha n).1⟩
    (by rintro ⟨n, hn⟩; dsimp at hn; linarith [(ha n).1, pow_pos (by norm_num : (0 : ℤ) < 2) n])
    (by rintro ⟨n, hn⟩; have := (ha n).1; omega)
    ⟨(∑ i ∈ range 8, 1 / ((2 : ℚ) ^ i + 1)) + 255 / 32768, ?_⟩
  push_cast
  rw [hsum.tsum_eq]
  have hp : ∑ i ∈ range 8, 1 / ((2 : ℝ) ^ i + a i) = ∑ i ∈ range 8, ((2 : ℝ) ^ i + 1)⁻¹ :=
    Finset.sum_congr rfl fun i hi => by simp [a, mem_range.mp hi]
  rw [hp]; norm_num [r, s]
