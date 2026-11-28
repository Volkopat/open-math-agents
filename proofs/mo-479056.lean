import OMAStatements.S_mo_479056

-- Problem: mo-479056
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

namespace OMA.P479056

open Filter Topology Finset
open OMA.S_mo_479056

theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem star_phase (t : ℝ) : star (phase t) = phase (-t) := by
  unfold phase
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp

theorem phase_zero : phase 0 = 1 := by
  unfold phase
  simp

theorem phase_nat_mul (n : ℕ) (t : ℝ) : phase ((n : ℝ) * t) = phase t ^ n := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem phase_eq_one (t : ℝ) (h : phase t = 1) : ∃ k : ℤ, t = (k : ℝ) * (2 * Real.pi) := by
  unfold phase at h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  have h2 : ((t : ℂ) - (k : ℂ) * (2 * Real.pi)) * Complex.I = 0 := by
    rw [sub_mul, hk]; ring
  have h3 : ((t : ℂ) - (k : ℂ) * (2 * Real.pi)) = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h Complex.I_ne_zero
  have h4 : ((t - (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) = 0 := by
    push_cast; exact h3
  have h5 := Complex.ofReal_eq_zero.1 h4
  linarith

theorem phase_int (k : ℤ) : phase ((k : ℝ) * (2 * Real.pi)) = 1 := by
  unfold phase
  have := Complex.exp_int_mul_two_pi_mul_I k
  rw [← this]
  congr 1
  push_cast
  ring

/-- The candidate unitary matrix. -/
noncomputable def Umat (far : Bool) (s L a b : ℝ) (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => (((Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
    phase (angle far s (outputPoint b s L i.val) (inputPoint a L n j))

theorem angle_diff (far : Bool) (s L a b : ℝ) (hs : 0 < s) (hL : 0 < L) (n : ℕ)
    (i j j' : Fin (n + 1)) :
    angle far s (outputPoint b s L i.val) (inputPoint a L n j') -
      angle far s (outputPoint b s L i.val) (inputPoint a L n j) =
    (Real.pi * ((inputPoint a L n j') ^ 2 - (inputPoint a L n j) ^ 2) / s -
      2 * Real.pi * b * (inputPoint a L n j' - inputPoint a L n j) / s) +
    (i.val : ℝ) * (-(2 * Real.pi) * (((j'.val : ℝ) - (j.val : ℝ)) / ((n + 1 : ℕ) : ℝ))) := by
  have hN : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hs' : s ≠ 0 := hs.ne'
  have hL' : L ≠ 0 := hL.ne'
  unfold angle outputPoint inputPoint
  field_simp
  ring

theorem geom_zero (N : ℕ) (m : ℤ) (hm : m ≠ 0) (hlt : |m| < (N : ℤ)) :
    ∑ i ∈ range N, phase (-(2 * Real.pi) * ((m : ℝ) / (N : ℝ))) ^ i = 0 := by
  have hN : (N : ℝ) ≠ 0 := by
    have : (0 : ℤ) < N := lt_of_le_of_lt (abs_nonneg m) hlt
    have : 0 < N := by exact_mod_cast this
    positivity
  set z := phase (-(2 * Real.pi) * ((m : ℝ) / (N : ℝ))) with hz
  have hz1 : z ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := phase_eq_one _ h
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have h1 : (m : ℝ) = -(k : ℝ) * (N : ℝ) := by
      field_simp at hk
      nlinarith [hk]
    have h2 : m = -k * (N : ℤ) := by exact_mod_cast h1
    have h3 : |m| = |k| * (N : ℤ) := by
      rw [h2, abs_mul, abs_neg, Nat.abs_cast]
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hm
      rw [h2]; ring
    have h4 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
    have h5 : (0 : ℤ) ≤ (N : ℤ) := Int.natCast_nonneg N
    nlinarith
  have hzN : z ^ N = 1 := by
    rw [hz, ← phase_nat_mul]
    have : (N : ℝ) * (-(2 * Real.pi) * ((m : ℝ) / (N : ℝ))) = ((-m : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      field_simp
    rw [this]
    exact phase_int _
  rw [geom_sum_eq hz1, hzN, sub_self, zero_div]

theorem unitary (far : Bool) (s L a b : ℝ) (hs : 0 < s) (hL : 0 < L) (n : ℕ) :
    (Umat far s L a b n).conjTranspose * Umat far s L a b n = 1 := by
  ext j j'
  rw [Matrix.mul_apply]
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set r : ℝ := (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹ with hr
  have hrr : r * r = (((n + 1 : ℕ) : ℝ))⁻¹ := by
    rw [hr, ← mul_inv, Real.mul_self_sqrt hNpos.le]
  set D : ℝ := Real.pi * ((inputPoint a L n j') ^ 2 - (inputPoint a L n j) ^ 2) / s -
      2 * Real.pi * b * (inputPoint a L n j' - inputPoint a L n j) / s with hD
  set w : ℝ := -(2 * Real.pi) * (((j'.val : ℝ) - (j.val : ℝ)) / ((n + 1 : ℕ) : ℝ)) with hw
  have hterm : ∀ i : Fin (n + 1),
      (Umat far s L a b n).conjTranspose j i * Umat far s L a b n i j' =
        (((r * r : ℝ) : ℂ) * phase D) * phase w ^ (i.val) := by
    intro i
    rw [Matrix.conjTranspose_apply]
    unfold Umat
    simp only [← hr]
    rw [star_mul', star_phase, ← phase_nat_mul, mul_assoc (((r * r : ℝ) : ℂ)), ← phase_add,
      ← angle_diff far s L a b hs hL n i j j']
    rw [show angle far s (outputPoint b s L i.val) (inputPoint a L n j') -
        angle far s (outputPoint b s L i.val) (inputPoint a L n j) =
        -angle far s (outputPoint b s L i.val) (inputPoint a L n j) +
        angle far s (outputPoint b s L i.val) (inputPoint a L n j') by ring, phase_add]
    have hstar : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [hstar, Complex.ofReal_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun i => phase w ^ i) (n + 1), Matrix.one_apply]
  by_cases hjj : j = j'
  · subst hjj
    have hw0 : w = 0 := by rw [hw]; simp
    have hD0 : D = 0 := by rw [hD]; simp
    rw [if_pos rfl, hw0, hD0, phase_zero]
    simp only [one_pow, Finset.sum_const, Finset.card_range, mul_one, nsmul_eq_mul]
    rw [hrr]
    push_cast
    have : ((n : ℂ) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
      simpa using this
    field_simp
  · rw [if_neg hjj]
    have hm : ((j'.val : ℤ) - (j.val : ℤ)) ≠ 0 := by
      intro h
      apply hjj
      apply Fin.ext
      omega
    have hlt : |((j'.val : ℤ) - (j.val : ℤ))| < ((n + 1 : ℕ) : ℤ) := by
      have h1 := j.isLt
      have h2 := j'.isLt
      rw [abs_lt]
      constructor <;> push_cast <;> omega
    have hg := geom_zero (n + 1) ((j'.val : ℤ) - (j.val : ℤ)) hm hlt
    have hwe : w = -(2 * Real.pi) * ((((j'.val : ℤ) - (j.val : ℤ) : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
      rw [hw]; push_cast; ring
    rw [hwe, hg, mul_zero]

theorem riemann (g : ℝ → ℂ) (a L : ℝ) (hL : 0 < L) (hg : ContinuousOn g (Set.Icc a (a + L))) :
    Tendsto (fun n : ℕ => ((L / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
      ∑ j : Fin (n + 1), g (a + (j.val : ℝ) * (L / ((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (∫ y in a..a + L, g y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn g (Set.Icc a (a + L)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, H⟩ := huc (ε / (2 * L)) (by positivity)
  obtain ⟨N0, hN0⟩ := exists_nat_gt (L / δ)
  refine ⟨N0, fun n hn => ?_⟩
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set h : ℝ := L / ((n + 1 : ℕ) : ℝ) with hh
  have hhpos : 0 < h := by positivity
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hNpos]
    have h1 : L / δ < ((n + 1 : ℕ) : ℝ) := by
      have : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast
      linarith
    rw [div_lt_iff₀ hδ] at h1
    linarith
  have hNh : ((n + 1 : ℕ) : ℝ) * h = L := by
    rw [hh]; field_simp
  let y : ℕ → ℝ := fun j => a + (j : ℝ) * h
  have hy0 : y 0 = a := by simp [y]
  have hyN : y (n + 1) = a + L := by
    simp only [y]; rw [hNh]
  have hymono : ∀ j : ℕ, y j ≤ y (j + 1) := by
    intro j; simp only [y]; push_cast; nlinarith
  have hysucc : ∀ j : ℕ, y (j + 1) - y j = h := by
    intro j; simp only [y]; push_cast; ring
  have hyge : ∀ j : ℕ, a ≤ y j := by
    intro j; simp only [y]
    have : (0 : ℝ) ≤ (j : ℝ) * h := by positivity
    linarith
  have hyle : ∀ j : ℕ, j ≤ n + 1 → y j ≤ a + L := by
    intro j hj
    simp only [y]
    have : (j : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hj
    have : (j : ℝ) * h ≤ ((n + 1 : ℕ) : ℝ) * h := by nlinarith
    linarith
  have hsub : ∀ j : ℕ, j < n + 1 → Set.uIcc (y j) (y (j + 1)) ⊆ Set.Icc a (a + L) := by
    intro j hj x hx
    rw [Set.uIcc_of_le (hymono j)] at hx
    exact ⟨le_trans (hyge j) hx.1, le_trans hx.2 (hyle (j + 1) (by omega))⟩
  have hint : ∀ j : ℕ, j < n + 1 → IntervalIntegrable g MeasureTheory.volume (y j) (y (j + 1)) :=
    fun j hj => (hg.mono (hsub j hj)).intervalIntegrable
  have hsplit : ∫ x in a..a + L, g x = ∑ j ∈ range (n + 1), ∫ x in y j..y (j + 1), g x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hint, hy0, hyN]
  have hpiece : ∀ j ∈ range (n + 1),
      ‖(h : ℂ) * g (y j) - ∫ x in y j..y (j + 1), g x‖ ≤ ε / (2 * L) * h := by
    intro j hj
    have hj' : j < n + 1 := Finset.mem_range.1 hj
    have hconst : ∫ _x in y j..y (j + 1), g (y j) = (h : ℂ) * g (y j) := by
      rw [intervalIntegral.integral_const, hysucc]
      simp
    rw [← hconst, ← intervalIntegral.integral_sub intervalIntegrable_const (hint j hj')]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := y j) (b := y (j + 1))
      (f := fun x => g (y j) - g x) (C := ε / (2 * L)) (by
        intro x hx
        rw [Set.uIoc_of_le (hymono j)] at hx
        have hxI : x ∈ Set.Icc a (a + L) :=
          hsub j hj' (by rw [Set.uIcc_of_le (hymono j)]; exact ⟨hx.1.le, hx.2⟩)
        have hyI : y j ∈ Set.Icc a (a + L) := ⟨hyge j, hyle j (by omega)⟩
        have hd : dist (y j) x < δ := by
          rw [Real.dist_eq, abs_lt]
          have := hysucc j
          constructor <;> linarith [hx.1, hx.2]
        have := H (y j) hyI x hxI hd
        rw [dist_eq_norm] at this
        exact this.le)
    rw [hysucc, abs_of_pos hhpos] at hb
    exact hb
  rw [dist_eq_norm, hsplit, Fin.sum_univ_eq_sum_range (fun j => g (a + (j : ℝ) * h)) (n + 1),
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc ‖∑ j ∈ range (n + 1), ((h : ℂ) * g (a + (j : ℝ) * h) - ∫ x in y j..y (j + 1), g x)‖
      ≤ ∑ j ∈ range (n + 1), ‖(h : ℂ) * g (a + (j : ℝ) * h) - ∫ x in y j..y (j + 1), g x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (n + 1), ε / (2 * L) * h := Finset.sum_le_sum hpiece
    _ = ε / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm (ε / (2 * L)) h,
          ← mul_assoc, hNh]
        field_simp
    _ < ε := by linarith

theorem out_eq (far : Bool) (s L a b : ℝ) (hs : 0 < s) (n k : ℕ) (hk : k < n + 1) (f : ℝ → ℂ) :
    outputField a L s n (Umat far s L a b n) f ⟨k, hk⟩ =
      ((L / ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
        ∑ j : Fin (n + 1), (fun y => kernel far s (outputPoint b s L k) y * f y)
          (a + (j.val : ℝ) * (L / ((n + 1 : ℕ) : ℝ))) := by
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  set r : ℝ := Real.sqrt ((n + 1 : ℕ) : ℝ) with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hNpos
  have hrr : ((n + 1 : ℕ) : ℝ) = r * r := (Real.mul_self_sqrt hNpos.le).symm
  set q : ℝ := Real.sqrt s with hq
  have hqpos : 0 < q := Real.sqrt_pos.2 hs
  unfold outputField
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold Umat kernel inputPoint
  simp only
  rw [← hr, ← hq, hrr]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
  push_cast
  field_simp

end OMA.P479056

open OMA.P479056 OMA.S_mo_479056 Filter Topology in
theorem OMA.solution : type_of% @OMA.S_mo_479056.main := by
  intro far s L a b hs hL
  refine ⟨fun n => Umat far s L a b n, fun n => unitary far s L a b hs hL n, ?_⟩
  intro f hf k
  have hg : ContinuousOn (fun y => kernel far s (outputPoint b s L k) y * f y)
      (Set.Icc a (a + L)) := by
    apply ContinuousOn.mul _ hf
    apply Continuous.continuousOn
    unfold kernel phase angle
    fun_prop
  have hR := riemann _ a L hL hg
  have hR' := hR.comp (tendsto_add_atTop_nat k)
  refine hR'.congr (fun n => ?_)
  simp only [Function.comp_apply]
  exact (out_eq far s L a b hs (n + k) k (by omega) f).symm
