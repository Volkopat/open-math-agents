import FormalConjectures.Wikipedia.GaussCircleProblem

-- Problem: Gauss circle problem — error le
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/GaussCircleProblem.lean:68 (declaration GaussCircleProblem.error_le)
-- Credit: @philipsaint (original proof and lattice-column/integral argument).
-- This simplification uses Mathlib’s even-function interval sum and square-root
-- inequality to replace the manual symmetry induction and closed-ball calculation.
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Real

namespace OMA.Gauss

noncomputable def f (r x : ℝ) : ℝ := 2 * √(r ^ 2 - x ^ 2)

lemma f_neg (r x : ℝ) : f r (-x) = f r x := by
  simp [f]

lemma f_cont (r : ℝ) : Continuous (f r) := by
  unfold f
  fun_prop

lemma f_zero_of_le (r x : ℝ) (hr : 0 ≤ r) (hx : r ≤ x) : f r x = 0 := by
  unfold f
  rw [Real.sqrt_eq_zero'.2 (by nlinarith)]
  ring

lemma f_anti (r : ℝ) : AntitoneOn (f r) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold f
  have : r ^ 2 - y ^ 2 ≤ r ^ 2 - x ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

lemma col (Y : ℝ) (hY : 0 ≤ Y) (M : ℕ) (hM : ⌊√Y⌋₊ ≤ M) :
    ((Finset.Icc (-(M : ℤ)) M).filter (fun n : ℤ => (n : ℝ) ^ 2 ≤ Y)).card
      = 2 * ⌊√Y⌋₊ + 1 := by
  set k := ⌊√Y⌋₊ with hk
  have hset : (Finset.Icc (-(M : ℤ)) M).filter (fun n : ℤ => (n : ℝ) ^ 2 ≤ Y)
      = Finset.Icc (-(k : ℤ)) k := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨_, hn⟩
      have h1 : |(n : ℝ)| ≤ √Y := Real.abs_le_sqrt hn
      have h2 : ((n.natAbs : ℕ) : ℝ) ≤ √Y := by
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact h1
      have h3 := Nat.le_floor h2
      omega
    · rintro ⟨h1, h2⟩
      have h3 : n.natAbs ≤ k := by omega
      have h4 : ((n.natAbs : ℕ) : ℝ) ≤ √Y :=
        le_trans (by exact_mod_cast h3) (Nat.floor_le (Real.sqrt_nonneg _))
      rw [Nat.cast_natAbs, Int.cast_abs] at h4
      refine ⟨by omega, ?_⟩
      calc (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
        _ ≤ (√Y) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
        _ = Y := Real.sq_sqrt hY
  rw [hset, Int.card_Icc]
  omega

lemma symm_sum (g : ℤ → ℝ) (hg : ∀ m, g (-m) = g m) (M : ℕ) :
    ∑ m ∈ Finset.Icc (-(M : ℤ)) M, g m = g 0 + 2 * ∑ i ∈ Finset.range M, g ((i : ℤ) + 1) := by
  rw [Finset.sum_Icc_of_even_eq_range hg, Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, nsmul_eq_mul]
  ring

lemma half_integral (r : ℝ) (hr : 0 ≤ r) : ∫ x in (0 : ℝ)..r, f r x = π * r ^ 2 / 2 := by
  -- full integral over [-r, r]
  have hfull : ∫ x in (-r)..r, √(r ^ 2 - x ^ 2) = r * (r * (π / 2)) := by
    rcases eq_or_lt_of_le hr with h | h
    · subst h; simp
    have h1 := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1)
      (fun y => √(r ^ 2 - y ^ 2)) (c := r) h.ne'
    simp only [mul_neg, mul_one] at h1
    have h2 : ∫ x in (-1 : ℝ)..1, √(r ^ 2 - (r * x) ^ 2) = r * (π / 2) := by
      have : ∀ x : ℝ, √(r ^ 2 - (r * x) ^ 2) = r * √(1 - x ^ 2) := by
        intro x
        rw [show r ^ 2 - (r * x) ^ 2 = r ^ 2 * (1 - x ^ 2) by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq hr]
      simp_rw [this]
      rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
    rw [h2, smul_eq_mul] at h1
    field_simp at h1 ⊢
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((f_cont r).intervalIntegrable (μ := MeasureTheory.volume) (-r) 0)
    ((f_cont r).intervalIntegrable (μ := MeasureTheory.volume) 0 r)
  have hneg : ∫ x in (-r)..0, f r x = ∫ x in (0 : ℝ)..r, f r x := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := r) (f r)
    simp only [neg_zero, f_neg] at this
    exact this.symm
  have hf : ∫ x in (-r)..r, f r x = 2 * (r * (r * (π / 2))) := by
    unfold f
    rw [intervalIntegral.integral_const_mul, hfull]
  rw [hneg, hf] at hsplit
  nlinarith

lemma integral_M (r : ℝ) (hr : 0 ≤ r) (M : ℕ) (hM : r ≤ (M : ℝ) + 1) :
    ∫ x in (0 : ℝ)..(0 + ((M + 1 : ℕ) : ℝ)), f r x = π * r ^ 2 / 2 := by
  rw [zero_add]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((f_cont r).intervalIntegrable (μ := MeasureTheory.volume) 0 r)
    ((f_cont r).intervalIntegrable (μ := MeasureTheory.volume) r ((M + 1 : ℕ) : ℝ))
  have hz : ∫ x in r..((M + 1 : ℕ) : ℝ), f r x = 0 := by
    have : Set.EqOn (f r) (fun _ => (0 : ℝ)) (Set.uIcc r ((M + 1 : ℕ) : ℝ)) := by
      intro x hx
      push_cast at hx
      rw [Set.uIcc_of_le hM] at hx
      exact f_zero_of_le r x hr hx.1
    rw [intervalIntegral.integral_congr this]
    simp
  rw [← hsplit, hz, half_integral r hr, add_zero]

lemma mem_ball (r : ℝ) (m n : ℤ) :
    !₂[(m : ℝ), (n : ℝ)] ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r ↔
      0 ≤ r ∧ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 ≤ r ^ 2 := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two,
    Real.sqrt_le_iff]

end OMA.Gauss

theorem OMA.solution : type_of% @GaussCircleProblem.error_le := by
  rw [Filter.eventually_atTop]
  refine ⟨1, fun r hr => ?_⟩
  have hr0 : 0 ≤ r := by linarith
  set M := ⌊r⌋₊ with hMdef
  have hMr : (M : ℝ) ≤ r := Nat.floor_le hr0
  have hrM : r < (M : ℝ) + 1 := Nat.lt_floor_add_one r
  set T : Finset (ℤ × ℤ) := ((Finset.Icc (-(M : ℤ)) M) ×ˢ (Finset.Icc (-(M : ℤ)) M)).filter
    (fun p => (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 ≤ r ^ 2) with hTdef
  have habs : ∀ x : ℤ, (x : ℝ) ^ 2 ≤ r ^ 2 → x.natAbs ≤ M := by
    intro x hx
    have h1 : |(x : ℝ)| ≤ r := by
      rw [← abs_of_nonneg hr0]
      exact sq_le_sq.1 hx
    exact Nat.le_floor (by rw [Nat.cast_natAbs, Int.cast_abs]; exact h1)
  have hS : {(m, n) : ℤ × ℤ | !₂[(m : ℝ), (n : ℝ)] ∈
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) r} = (T : Set (ℤ × ℤ)) := by
    ext ⟨m, n⟩
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, hTdef, Finset.mem_filter, Finset.mem_product,
      Finset.mem_Icc]
    rw [OMA.Gauss.mem_ball]
    constructor
    · rintro ⟨_, h⟩
      have hm := habs m (by nlinarith [sq_nonneg (n : ℝ)])
      have hn := habs n (by nlinarith [sq_nonneg (m : ℝ)])
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩, h⟩
    · rintro ⟨_, h⟩
      exact ⟨hr0, h⟩
  have hmem : ∀ m ∈ Finset.Icc (-(M : ℤ)) M, (m : ℝ) ^ 2 ≤ r ^ 2 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have h1 : m.natAbs ≤ M := by omega
    have h2 : ((m.natAbs : ℕ) : ℝ) ≤ r := le_trans (by exact_mod_cast h1) hMr
    rw [Nat.cast_natAbs, Int.cast_abs] at h2
    rw [← sq_abs (m : ℝ)]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hcard : T.card = ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (2 * ⌊√(r ^ 2 - (m : ℝ) ^ 2)⌋₊ + 1) := by
    rw [hTdef, Finset.card_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro m hm
    have hY : 0 ≤ r ^ 2 - (m : ℝ) ^ 2 := by linarith [hmem m hm]
    have hk : ⌊√(r ^ 2 - (m : ℝ) ^ 2)⌋₊ ≤ M := by
      apply Nat.floor_le_floor
      calc √(r ^ 2 - (m : ℝ) ^ 2) ≤ √(r ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = r := Real.sqrt_sq hr0
    rw [← OMA.Gauss.col _ hY M hk, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro n _
    exact if_congr (by constructor <;> intro h <;> linarith) rfl rfl
  have hN : (GaussCircleProblem.N r : ℝ) = ∑ m ∈ Finset.Icc (-(M : ℤ)) M,
      ((2 * ⌊√(r ^ 2 - (m : ℝ) ^ 2)⌋₊ + 1 : ℕ) : ℝ) := by
    show ((Set.ncard _ : ℕ) : ℝ) = _
    rw [hS, Set.ncard_coe_finset, hcard]
    push_cast
    rfl
  -- column errors
  have herr : |(GaussCircleProblem.N r : ℝ) - ∑ m ∈ Finset.Icc (-(M : ℤ)) M, OMA.Gauss.f r m|
      ≤ 2 * M + 1 := by
    rw [hN, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) M,
          |((2 * ⌊√(r ^ 2 - (m : ℝ) ^ 2)⌋₊ + 1 : ℕ) : ℝ) - OMA.Gauss.f r m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc (-(M : ℤ)) M, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro m hm
          have hY : 0 ≤ r ^ 2 - (m : ℝ) ^ 2 := by linarith [hmem m hm]
          have h1 := Nat.floor_le (Real.sqrt_nonneg (r ^ 2 - (m : ℝ) ^ 2))
          have h2 := Nat.lt_floor_add_one (√(r ^ 2 - (m : ℝ) ^ 2))
          unfold OMA.Gauss.f
          push_cast
          rw [abs_le]
          constructor <;> linarith
      _ = 2 * M + 1 := by
          rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
          have : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
          rw [this]
          push_cast
          ring
  -- symmetry
  have hsym : ∑ m ∈ Finset.Icc (-(M : ℤ)) M, OMA.Gauss.f r m
      = OMA.Gauss.f r 0 + 2 * ∑ i ∈ Finset.range M, OMA.Gauss.f r ((i : ℝ) + 1) := by
    have := OMA.Gauss.symm_sum (fun m : ℤ => OMA.Gauss.f r m)
      (fun m => by push_cast; exact OMA.Gauss.f_neg r m) M
    push_cast at this
    exact this
  -- Riemann sums
  have hanti : AntitoneOn (OMA.Gauss.f r) (Set.Icc 0 (0 + ((M + 1 : ℕ) : ℝ))) :=
    (OMA.Gauss.f_anti r).mono Set.Icc_subset_Ici_self
  have hup := hanti.integral_le_sum
  have hlow := hanti.sum_le_integral
  rw [OMA.Gauss.integral_M r hr0 M hrM.le] at hup hlow
  rw [Finset.sum_range_succ'] at hup
  rw [Finset.sum_range_succ] at hlow
  have hz : OMA.Gauss.f r (0 + ((M + 1 : ℕ) : ℝ)) = 0 :=
    OMA.Gauss.f_zero_of_le r _ hr0 (by push_cast; linarith)
  rw [hz] at hlow
  simp only [zero_add, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at hup hlow
  have hf0 : OMA.Gauss.f r 0 = 2 * r := by
    unfold OMA.Gauss.f
    simp [Real.sqrt_sq hr0]
  rw [hf0] at hsym hup
  have hs2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hk : 3 ≤ √2 * π := by nlinarith [Real.pi_gt_three]
  rw [hsym] at herr
  rw [abs_le] at herr
  show |(GaussCircleProblem.N r : ℝ) - π * r ^ 2| ≤ 2 * √2 * π * r
  rw [abs_le]
  constructor <;> nlinarith
