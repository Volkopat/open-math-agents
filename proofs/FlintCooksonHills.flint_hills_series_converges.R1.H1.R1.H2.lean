import OMAReductions.R_FlintCooksonHills_flint_hills_series_converges_R1_H1_R1
import Mathlib

-- Step FlintCooksonHills.flint_hills_series_converges.R1.H1.R1.H2: hypothesis H2 of reduction FlintCooksonHills.flint_hills_series_converges.R1.H1.R1
-- Credit: @Raimo33

theorem OMA.solution : OMA.R_FlintCooksonHills_flint_hills_series_converges_R1_H1_R1.H2 := by
  unfold OMA.R_FlintCooksonHills_flint_hills_series_converges_R1_H1_R1.H2
  intro ν hν happ m X D
  induction m with
  | zero => exact ⟨fun _ => 0, fun _ => 0, fun n hn => absurd hn (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨p, q, hpq⟩ := ih
    set P : ℝ := D * ((List.range m).reverse.map (fun i : ℕ => (Nat.ceil (Real.log (q i)) : ℝ))).prod with hP
    set M : ℝ := max X P + 1 with hM
    obtain ⟨p', q', hQ, happr⟩ := happ (⌈Real.exp M⌉₊ + 2)
    have hq2 : 2 ≤ q' := by omega
    have hq'pos : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
    have hlog : M < (Nat.ceil (Real.log q') : ℝ) := by
      have h1 : Real.exp M < (q' : ℝ) := by
        have := Nat.le_ceil (Real.exp M)
        have h2 : ((⌈Real.exp M⌉₊ + 2 : ℕ) : ℝ) ≤ q' := by exact_mod_cast hQ
        push_cast at h2
        linarith
      have h3 : M < Real.log q' := by
        rw [Real.lt_log_iff_exp_lt hq'pos]; exact h1
      exact lt_of_lt_of_le h3 (Nat.le_ceil _)
    have hp' : p' ≠ 0 := by
      rintro rfl
      have hle : (q' : ℝ) ^ (-ν) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ q')) (by linarith)
      simp at happr
      have := Real.pi_gt_three
      rw [abs_of_pos Real.pi_pos] at happr
      linarith
    refine ⟨Function.update p m p', Function.update q m q', ?_⟩
    intro n hn
    have hprod : ∀ k ≤ m, ((List.range k).reverse.map
        (fun i : ℕ => (Nat.ceil (Real.log ((Function.update q m q' i : ℕ) : ℝ)) : ℝ))).prod =
        ((List.range k).reverse.map (fun i : ℕ => (Nat.ceil (Real.log (q i : ℝ)) : ℝ))).prod := by
      intro k hk
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [List.mem_reverse, List.mem_range] at hi
      rw [Function.update_of_ne (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | rfl
    · have := hpq n hlt
      simp only [] at this ⊢
      rw [hprod n hlt.le, Function.update_of_ne hlt.ne, Function.update_of_ne hlt.ne]
      exact this
    · simp only []
      rw [hprod n le_rfl, Function.update_self, Function.update_self]
      refine ⟨hq2, hp', happr, ?_, ?_⟩
      · have := le_max_left X P; linarith
      · have := le_max_right X P; rw [← hP]; linarith
