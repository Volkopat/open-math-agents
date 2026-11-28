import OMAStatements.S_mse_2172922

open OMA.S_mse_2172922

private theorem log_sum_succ (n : ℕ) (hn : 2 ≤ n + 1) :
    logSum (n + 1) = logSum n + Real.log ((n + 1 : ℕ) : ℝ) := by
  have hinterval : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Icc 2 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  unfold logSum
  rw [hinterval, Finset.sum_insert (by simp)]
  exact add_comm _ _

private theorem cross_integer (f : ℕ → ℝ) (K : ℕ) (η : ℝ)
    (hspan : f 0 + 1 ≤ f K) (hsteps : ∀ i < K, f (i + 1) - f i < η) :
    ∃ i ≤ K, Int.fract (f i) < η := by
  let z : ℤ := ⌊f 0⌋ + 1
  have h0 : f 0 < (z : ℝ) := by simpa [z] using Int.lt_floor_add_one (f 0)
  have hz : (z : ℝ) ≤ f 0 + 1 := by
    simpa [z] using add_le_add_right (Int.floor_le (f 0)) 1
  have hExists : ∃ i : ℕ, (z : ℝ) ≤ f i := ⟨K, hz.trans hspan⟩
  let i := Nat.find hExists
  have hi : (z : ℝ) ≤ f i := Nat.find_spec hExists
  have hiK : i ≤ K := Nat.find_min' hExists (hz.trans hspan)
  have hipos : 0 < i := by
    by_contra! hle
    have he : i = 0 := by omega
    exact (not_le_of_gt h0) (he ▸ hi)
  have hprev : f (i - 1) < (z : ℝ) :=
    lt_of_not_ge (Nat.find_min hExists (show i - 1 < i by omega))
  have hstep := hsteps (i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at hstep
  have hfloor : (z : ℝ) ≤ (⌊f i⌋ : ℝ) := by
    exact_mod_cast Int.le_floor.mpr hi
  refine ⟨i, hiK, ?_⟩
  change f i - (⌊f i⌋ : ℝ) < η
  linarith only [hprev, hstep, hfloor]

theorem OMA.solution : type_of% @OMA.S_mse_2172922.main := by
  intro ε hε B
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
  have hKδ : 1 < (K : ℝ) * δ := (div_lt_iff₀ hδ).mp hK
  let gap := Real.exp (2 * δ) - Real.exp δ
  have hgap : 0 < gap := sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  obtain ⟨m, hm⟩ := exists_nat_gt (max ((B : ℝ) + 2) (((K : ℝ) + 2) / gap))
  have hmB : (B : ℝ) + 2 < (m : ℝ) := (le_max_left _ _).trans_lt hm
  have hmGap : ((K : ℝ) + 2) / gap < (m : ℝ) := (le_max_right _ _).trans_lt hm
  have hexp : (m : ℝ) < Real.exp m := by linarith [Real.add_one_le_exp (m : ℝ)]
  have hwidth : (K : ℝ) + 2 < Real.exp ((m : ℝ) + 2 * δ) - Real.exp ((m : ℝ) + δ) := by
    rw [Real.exp_add, Real.exp_add, ← mul_sub]
    exact ((div_lt_iff₀ hgap).mp hmGap).trans (mul_lt_mul_of_pos_right hexp hgap)
  let N := ⌈Real.exp ((m : ℝ) + δ)⌉₊
  have hceil : Real.exp ((m : ℝ) + δ) ≤ (N : ℝ) := Nat.le_ceil _
  have hceilUpper : (N : ℝ) < Real.exp ((m : ℝ) + δ) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hNlarge : (B : ℝ) + 2 < (N : ℝ) :=
    hmB.trans (hexp.trans_le ((Real.exp_le_exp.mpr (by linarith)).trans hceil))
  have hNB : B < N := by
    exact_mod_cast (show (B : ℝ) < (N : ℝ) by linarith)
  have hNtwo : 2 ≤ N := by
    exact_mod_cast (show (2 : ℝ) ≤ (N : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) B])
  let f (i : ℕ) := logSum (N + i) - (m : ℝ) * (i : ℝ)
  have increments (i : ℕ) (hi : i < K) :
      δ ≤ f (i + 1) - f i ∧ f (i + 1) - f i < 2 * δ := by
    have hiReal : (i : ℝ) < (K : ℝ) := by exact_mod_cast hi
    have hpos : 0 < ((N + i + 1 : ℕ) : ℝ) := by positivity
    have hlo : Real.exp ((m : ℝ) + δ) ≤ ((N + i + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hhi : ((N + i + 1 : ℕ) : ℝ) < Real.exp ((m : ℝ) + 2 * δ) := by
      push_cast
      linarith only [hceilUpper, hwidth, hiReal]
    have hloLog := (Real.le_log_iff_exp_le hpos).mpr hlo
    have hhiLog := (Real.log_lt_iff_lt_exp hpos).mpr hhi
    have hstep : f (i + 1) - f i = Real.log ((N + i + 1 : ℕ) : ℝ) - m := by
      simp only [f, ← Nat.add_assoc, log_sum_succ (N + i) (by omega), Nat.cast_add, Nat.cast_one]
      ring
    rw [hstep]
    constructor <;> linarith only [hloLog, hhiLog]
  have hgrowth (i : ℕ) (hi : i ≤ K) : f 0 + (i : ℝ) * δ ≤ f i := by
    induction i with
    | zero => simp
    | succ i ih =>
      have h₁ := ih (by omega)
      have h₂ := (increments i (by omega)).1
      push_cast
      linarith only [h₁, h₂]
  have hspan : f 0 + 1 ≤ f K := by linarith only [hgrowth K le_rfl, hKδ]
  obtain ⟨i, _, hi⟩ := cross_integer f K (2 * δ) hspan (fun i hi => (increments i hi).2)
  have htranslate : logSum (N + i) = f i + (((m : ℤ) * (i : ℤ) : ℤ) : ℝ) := by
    simp [f]
  refine ⟨N + i, by omega, ?_⟩
  rw [htranslate, Int.fract_add_intCast]
  dsimp [δ] at hi
  linarith only [hi, hε]
