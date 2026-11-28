import OMAStatements.S_oeis_a025426

/-! The integration lemmas below are adapted from @philipsaint’s Gauss circle
error proof in this project. The positive lattice columns, symmetry, and
diagonal correction then give the error for unordered positive squares.
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/639
-/


namespace OMA.S_oeis_a025426

open Finset

private lemma mem_quad {n : ℕ} {p : ℕ × ℕ} :
    p ∈ quadrant n ↔ (p.1+1)^2 + (p.2+1)^2 ≤ n := by
  simp only [quadrant, mem_filter, mem_product, mem_range, Nat.lt_iff_add_one_le, Nat.le_sqrt']
  omega

private lemma mem_tri {n : ℕ} {p : ℕ × ℕ} :
    p ∈ triangle n ↔ (p.1+1)^2 + (p.2+1)^2 ≤ n ∧ p.1 ≤ p.2 := by simp [triangle, mem_quad]

private lemma sum_shell (n : ℕ) : ∑ k ∈ Icc 1 n, a k = (triangle n).card := by
  induction n with
  | zero => simp [triangle, quadrant]
  | succ n ih =>
    have hsub : triangle n ⊆ triangle (n+1) := fun p hp =>
      mem_tri.mpr ⟨(mem_tri.mp hp).1.trans (Nat.le_succ n), (mem_tri.mp hp).2⟩
    have hd : (triangle (n+1)).filter (fun p => (p.1+1)^2 + (p.2+1)^2 = n+1) =
        triangle (n+1) \ triangle n := by
      ext p
      simp only [mem_filter, Finset.mem_sdiff, mem_tri]
      omega
    rw [sum_Icc_succ_top (by omega), ih, a, hd, card_sdiff_of_subset hsub]
    have := card_le_card hsub
    omega

private lemma symmetry (n : ℕ) : (quadrant n).card ≤ 2*(triangle n).card ∧
    2*(triangle n).card ≤ (quadrant n).card + n.sqrt := by
  let Q := quadrant n
  let L := Q.filter (fun p => p.1 < p.2)
  let U := Q.filter (fun p => ¬ p.1 ≤ p.2)
  let D := (triangle n).filter (fun p => ¬ p.1 < p.2)
  have hsplit : (triangle n).card + U.card = Q.card :=
    card_filter_add_card_filter_not (fun p : ℕ × ℕ => p.1 ≤ p.2)
  have hstrict : (triangle n).filter (fun p => p.1 < p.2) = L := by
    ext p
    simp only [L, Q, triangle, mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le⟩, h.2⟩⟩
  have hsplit' : L.card + D.card = (triangle n).card := by
    rw [← hstrict]
    exact card_filter_add_card_filter_not (fun p : ℕ × ℕ => p.1 < p.2)
  have hswap : L.card = U.card := by
    apply card_bij' (fun p _ => p.swap) (fun p _ => p.swap)
    · simp
    · simp
    · intro p hp
      simpa [L, U, Q, mem_quad, add_comm] using hp
    · intro p hp
      simpa [L, U, Q, mem_quad, add_comm] using hp
  have hd : D.card ≤ n.sqrt := by
    rw [← card_range n.sqrt]
    refine card_le_card_of_injOn Prod.fst ?_ ?_
    · intro p hp
      exact ((mem_product.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1).1)
    · rintro ⟨i,j⟩ hp ⟨k,l⟩ hq heq
      change (i,j) ∈ D at hp
      change (k,l) ∈ D at hq
      have hp1 := (mem_tri.mp (mem_filter.mp hp).1).2
      have hp2 := (mem_filter.mp hp).2
      have hq1 := (mem_tri.mp (mem_filter.mp hq).1).2
      have hq2 := (mem_filter.mp hq).2
      change i = k at heq
      simp only at hp1 hp2 hq1 hq2
      congr
      omega
  change Q.card ≤ 2*(triangle n).card ∧ 2*(triangle n).card ≤ Q.card + n.sqrt
  omega

private lemma columns (n : ℕ) : (quadrant n).card =
    ∑ i ∈ range n.sqrt, (n-(i+1)^2).sqrt := by
  rw [quadrant, card_filter, sum_product]
  apply sum_congr rfl
  intro i hi
  have hi' : (i+1)^2 ≤ n := Nat.le_sqrt'.mp (mem_range.mp hi)
  have heq : (range n.sqrt).filter (fun j => (i+1)^2+(j+1)^2 ≤ n) =
      range (n-(i+1)^2).sqrt := by
    ext j
    simp only [mem_filter, mem_range, Nat.lt_iff_add_one_le, Nat.le_sqrt']
    omega
  have h := congrArg card heq
  rw [card_filter, card_range] at h
  exact h


open Filter Real


private noncomputable def f (r x : ℝ) : ℝ := 2 * √(r ^ 2 - x ^ 2)

private lemma f_neg (r x : ℝ) : f r (-x) = f r x := by
  simp [f]

private lemma f_cont (r : ℝ) : Continuous (f r) := by
  unfold f
  fun_prop

private lemma f_zero_of_le (r x : ℝ) (hr : 0 ≤ r) (hx : r ≤ x) : f r x = 0 := by
  unfold f
  rw [Real.sqrt_eq_zero'.2 (by nlinarith)]
  ring

private lemma f_anti (r : ℝ) : AntitoneOn (f r) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  unfold f
  have : r ^ 2 - y ^ 2 ≤ r ^ 2 - x ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt this
  linarith

private lemma half_integral (r : ℝ) (hr : 0 ≤ r) : ∫ x in (0 : ℝ)..r, f r x = π * r ^ 2 / 2 := by
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

private lemma integral_M (r : ℝ) (hr : 0 ≤ r) (M : ℕ) (hM : r ≤ (M : ℝ) + 1) :
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

private lemma sampled (r : ℝ) (hr : 0 ≤ r) (M : ℕ) (hM : r ≤ (M : ℝ)+1) :
    (∑ i ∈ range M, f r ((i:ℝ)+1)) ≤ π*r^2/2 ∧
    π*r^2/2 ≤ 2*r + ∑ i ∈ range M, f r ((i:ℝ)+1) := by
  have hanti : AntitoneOn (f r) (Set.Icc 0 (0 + ((M + 1 : ℕ) : ℝ))) :=
    (f_anti r).mono Set.Icc_subset_Ici_self
  have hup := hanti.integral_le_sum
  have hlow := hanti.sum_le_integral
  rw [integral_M r hr M hM] at hup hlow
  rw [sum_range_succ'] at hup
  rw [sum_range_succ] at hlow
  have hz : f r (0 + ((M + 1 : ℕ) : ℝ)) = 0 := f_zero_of_le r _ hr (by push_cast; linarith)
  rw [hz] at hlow
  simp only [zero_add, Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero] at hup hlow
  have hf0 : f r 0 = 2*r := by simp [f, sqrt_sq hr]
  rw [hf0] at hup
  exact ⟨hlow, by linarith⟩

private lemma round_columns (n : ℕ) :
    2 * ((∑ i ∈ range n.sqrt, (n-(i+1)^2).sqrt : ℕ) : ℝ) ≤
      ∑ i ∈ range n.sqrt, f (√n) ((i:ℝ)+1) ∧
    (∑ i ∈ range n.sqrt, f (√n) ((i:ℝ)+1)) ≤
      2 * ((∑ i ∈ range n.sqrt, (n-(i+1)^2).sqrt : ℕ) : ℝ) + 2*n.sqrt := by
  have hbounds (i : ℕ) (hi : i ∈ range n.sqrt) :
      2 * ((n-(i+1)^2).sqrt : ℝ) ≤ f (√n) ((i:ℝ)+1) ∧
      f (√n) ((i:ℝ)+1) ≤ 2 * ((n-(i+1)^2).sqrt : ℝ) + 2 := by
    have hi' : (i+1)^2 ≤ n := Nat.le_sqrt'.mp (mem_range.mp hi)
    have hl := Real.nat_sqrt_le_real_sqrt (a := n-(i+1)^2)
    have hu := Real.real_sqrt_le_nat_sqrt_succ (a := n-(i+1)^2)
    rw [Nat.cast_sub hi'] at hl hu
    push_cast at hl hu
    rw [f, Real.sq_sqrt (by positivity)]
    constructor <;> linarith
  push_cast
  rw [Finset.mul_sum]
  constructor
  · exact sum_le_sum fun i hi => (hbounds i hi).1
  · have hu := sum_le_sum fun i hi => (hbounds i hi).2
    simpa [Finset.sum_add_distrib, mul_comm] using hu

/-- The averaging error is bounded by the radius of the disk. -/
theorem summatory_error (n : ℕ) :
    |((∑ k ∈ Icc 1 n, a k : ℕ) : ℝ) - n*π/8| ≤ √n := by
  have hs := sampled (√n) (sqrt_nonneg _) n.sqrt (real_sqrt_le_nat_sqrt_succ (a := n))
  rw [sq_sqrt (by positivity)] at hs
  have hc := round_columns n
  rw [← columns] at hc
  have ht := symmetry n
  have h1 : ((quadrant n).card : ℝ) ≤ 2*(triangle n).card := by exact_mod_cast ht.1
  have h2 : (2:ℝ)*(triangle n).card ≤ (quadrant n).card + n.sqrt := by exact_mod_cast ht.2
  have hm := nat_sqrt_le_real_sqrt (a := n)
  rw [sum_shell, abs_le]
  constructor <;> linarith [hs.1, hs.2, hc.1, hc.2]

end OMA.S_oeis_a025426

open Filter Real Finset

open OMA.S_oeis_a025426

theorem OMA.solution : type_of% @OMA.S_oeis_a025426.main := by
  rw [Asymptotics.IsEquivalent, Asymptotics.isLittleO_iff]
  intro c hc
  have hlim : Tendsto (fun n : ℕ => √(n:ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [tendsto_atTop.1 hlim (8/(c*π))] with n hn
  change |((∑ k ∈ Icc 1 n, a k : ℕ) : ℝ) - n*π/8| ≤ c*|(n:ℝ)*π/8|
  rw [abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)*π/8)]
  apply (summatory_error n).trans
  have hp : 0 < c*π := mul_pos hc pi_pos
  have hprod := mul_le_mul_of_nonneg_right ((div_le_iff₀ hp).mp hn) (sqrt_nonneg (n:ℝ))
  nlinarith [sq_sqrt (Nat.cast_nonneg (α:=ℝ) n),
    congrArg (fun x : ℝ => x*(c*π)) (sq_sqrt (Nat.cast_nonneg (α:=ℝ) n))]
