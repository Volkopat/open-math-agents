import OMAReductions.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2

/-!
Proof of `OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2.H2`.

Take `a n i = ⌊(n + 1) β i⌋ + i`. Since `β` is monotone the floors are monotone in `i`, and adding
`i` makes the tuple strictly increasing. From `(n + 1) β i - 1 < ⌊(n + 1) β i⌋ ≤ (n + 1) β i`,
`β i - 1 / (n + 1) ≤ a n i / (n + 1) ≤ β i + i / (n + 1)`, and both bounds tend to `β i`.
-/

open Filter Topology

theorem OMA.solution : OMA.R_Erdos5_erdos_5_variants_banks_freiberg_maynard_R2.H2 := by
  intro β hβ hmono
  refine ⟨fun n i => ⌊((n : ℝ) + 1) * β i⌋₊ + i.val, ?_, ?_⟩
  · intro n i j hij
    have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h1 : ⌊((n : ℝ) + 1) * β i⌋₊ ≤ ⌊((n : ℝ) + 1) * β j⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_left (hmono hij.le) hpos)
    have h2 : i.val < j.val := hij
    show ⌊((n : ℝ) + 1) * β i⌋₊ + i.val < ⌊((n : ℝ) + 1) * β j⌋₊ + j.val
    omega
  · rw [tendsto_pi_nhds]
    intro i
    have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hlow : Tendsto (fun n : ℕ => β i - 1 / ((n : ℝ) + 1)) atTop (𝓝 (β i)) := by
      simpa using (tendsto_const_nhds (x := β i)).sub hinv
    have hup : Tendsto (fun n : ℕ => β i + (i.val : ℝ) * (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (β i)) := by
      simpa using (tendsto_const_nhds (x := β i)).add (hinv.const_mul (i.val : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => ?_) (fun n => ?_)
    · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hf := Nat.lt_floor_add_one (((n : ℝ) + 1) * β i)
      have hi : (0 : ℝ) ≤ i.val := by positivity
      have key : ((n : ℝ) + 1) * β i - 1 ≤ (⌊((n : ℝ) + 1) * β i⌋₊ : ℝ) + i.val := by linarith
      show β i - 1 / ((n : ℝ) + 1) ≤
        (((⌊((n : ℝ) + 1) * β i⌋₊ + i.val : ℕ) : ℝ)) / ((n : ℝ) + 1)
      push_cast
      calc β i - 1 / ((n : ℝ) + 1) = (((n : ℝ) + 1) * β i - 1) / ((n : ℝ) + 1) := by
            field_simp
        _ ≤ ((⌊((n : ℝ) + 1) * β i⌋₊ : ℝ) + i.val) / ((n : ℝ) + 1) := by gcongr
    · have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hf : (⌊((n : ℝ) + 1) * β i⌋₊ : ℝ) ≤ ((n : ℝ) + 1) * β i :=
        Nat.floor_le (mul_nonneg hpos.le (hβ i))
      show (((⌊((n : ℝ) + 1) * β i⌋₊ + i.val : ℕ) : ℝ)) / ((n : ℝ) + 1) ≤
        β i + (i.val : ℝ) * (1 / ((n : ℝ) + 1))
      push_cast
      calc ((⌊((n : ℝ) + 1) * β i⌋₊ : ℝ) + i.val) / ((n : ℝ) + 1)
          ≤ (((n : ℝ) + 1) * β i + i.val) / ((n : ℝ) + 1) := by gcongr
        _ = β i + (i.val : ℝ) * (1 / ((n : ℝ) + 1)) := by field_simp
