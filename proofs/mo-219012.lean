import OMAStatements.S_mo_219012
import Mathlib

-- Retains @caa1982’s numerical-radius proof (PR #25965).
-- Standard quotient continuity and sum/division identities simplify normalization.

open OMA.S_mo_219012

lemma mo219012_le_one {n : ℕ} (w : Fin n → ℝ) (hw : ∑ k, w k ^ 2 = 1) (i : Fin n) :
    w i ^ 2 ≤ 1 := by
  rw [← hw]
  exact Finset.single_le_sum (f := fun k => w k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)

lemma mo219012_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : ∀ i j, 0 < A i j)
    (w : Fin n → ℝ) (h0 : ∀ i, 0 ≤ w i) (hw : ∑ k, w k ^ 2 = 1) :
    ∑ i, ∑ j, w i * A i j * w j ≤ ∑ i, ∑ j, A i j := by
  apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
  have hi : w i ≤ 1 := by nlinarith [mo219012_le_one w hw i, h0 i]
  have hj : w j ≤ 1 := by nlinarith [mo219012_le_one w hw j, h0 j]
  have hij : w i * w j ≤ 1 := by nlinarith [h0 i, h0 j]
  have := hA i j
  nlinarith [mul_nonneg (h0 i) (h0 j)]

theorem OMA.solution : type_of% @OMA.S_mo_219012.main := by
  intro n A hA
  set S1 := {r : ℝ | ∃ x : Fin n → ℂ, ∑ i, ‖x i‖ ^ 2 = 1 ∧
          r = ‖∑ i, ∑ j, star (x i) * (A i j : ℂ) * x j‖} with hS1
  set S2 := {r : ℝ | ∃ u : Fin n → ℝ, ∑ i, u i ^ 2 = 1 ∧ (∀ i, 0 < u i) ∧
          r = ∑ i, ∑ j, u i * A i j * u j} with hS2
  have hkey1 : ∀ x : Fin n → ℂ, ‖∑ i, ∑ j, star (x i) * (A i j : ℂ) * x j‖ ≤
      ∑ i, ∑ j, ‖x i‖ * A i j * ‖x j‖ := by
    intro x
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)))
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hA i j).le]
  have hbd2 : BddAbove S2 := by
    refine ⟨∑ i, ∑ j, A i j, ?_⟩
    rintro r ⟨u, hu, hpos, rfl⟩
    exact mo219012_bound A hA u (fun i => (hpos i).le) hu
  have hbd1 : BddAbove S1 := by
    refine ⟨∑ i, ∑ j, A i j, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact (hkey1 x).trans (mo219012_bound A hA (fun i => ‖x i‖) (fun i => norm_nonneg _) hx)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have e1 : S1 = ∅ := by
      ext r; simp [hS1]
    have e2 : S2 = ∅ := by
      ext r; simp [hS2]
    rw [e1, e2]
  · have hwle : ∀ w : Fin n → ℝ, (∀ i, 0 ≤ w i) → ∑ k, w k ^ 2 = 1 →
        ∑ i, ∑ j, w i * A i j * w j ≤ sSup S2 := by
      intro w h0 hw
      let f : ℝ → ℝ := fun t =>
        (∑ i, ∑ j, (w i + t) * A i j * (w j + t)) / (∑ k, (w k + t) ^ 2)
      have hcont : ContinuousAt f 0 := by
        dsimp [f]
        fun_prop (disch := simp [hw])
      have hf0 : f 0 = ∑ i, ∑ j, w i * A i j * w j := by simp [f, hw]
      have hmem : ∀ t ∈ Set.Ioi (0 : ℝ), f t ≤ sSup S2 := by
        intro t ht
        have ht' : (0 : ℝ) < t := ht
        have hpos : ∀ k, 0 < w k + t := fun k => by linarith [h0 k]
        set D := ∑ k, (w k + t) ^ 2 with hD
        have hDpos : 0 < D := by
          have k0 : Fin n := ⟨0, hn⟩
          exact Finset.sum_pos (fun k _ => pow_pos (hpos k) 2) ⟨k0, Finset.mem_univ _⟩
        have hs : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hDpos.le
        have hsq : 0 < Real.sqrt D := Real.sqrt_pos.2 hDpos
        apply le_csSup hbd2
        refine ⟨fun k => (w k + t) / Real.sqrt D, ?_, fun k => div_pos (hpos k) hsq, ?_⟩
        · simpa only [div_pow, Real.sq_sqrt hDpos.le, ← Finset.sum_div] using
            div_self hDpos.ne'
        · simp only [f, div_mul_eq_mul_div, ← mul_div_assoc, div_div, hs, ← Finset.sum_div]
          rw [hD]
      have hlim : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
        hcont.tendsto.mono_left nhdsWithin_le_nhds
      have := le_of_tendsto hlim (eventually_nhdsWithin_of_forall hmem)
      rwa [hf0] at this
    have hne2 : S2.Nonempty := by
      refine ⟨_, fun _ => 1 / Real.sqrt n, ?_, fun _ => by positivity, rfl⟩
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp [Real.sq_sqrt hn'.le, hn'.ne']
    have hne1 : S1.Nonempty := by
      obtain ⟨r, u, hu, hpos, rfl⟩ := hne2
      exact ⟨_, fun i => (u i : ℂ), by simpa [Complex.norm_real, sq_abs] using hu, rfl⟩
    apply le_antisymm
    · apply csSup_le hne1
      rintro r ⟨x, hx, rfl⟩
      exact (hkey1 x).trans (hwle (fun i => ‖x i‖) (fun i => norm_nonneg _) hx)
    · apply csSup_le hne2
      rintro r ⟨u, hu, hpos, rfl⟩
      apply le_csSup hbd1
      refine ⟨fun i => (u i : ℂ), by simpa [Complex.norm_real, sq_abs] using hu, ?_⟩
      have e : ∑ i, ∑ j, star ((u i : ℂ)) * (A i j : ℂ) * (u j : ℂ) =
          ((∑ i, ∑ j, u i * A i j * u j : ℝ) : ℂ) := by
        push_cast; simp [Complex.conj_ofReal]
      rw [e, Complex.norm_real, Real.norm_of_nonneg]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        (mul_pos (mul_pos (hpos i) (hA i j)) (hpos j)).le
