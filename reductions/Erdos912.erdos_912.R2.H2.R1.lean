import OMAReductions.R_Erdos912_erdos_912_R2
import Mathlib

/-!
For the large-prime quotient bins of Erdős 912, only compact windows around
the transition scale √(n/log n) need to be understood. The short-interval and
long-interval sides may have different limiting profiles. No formula or
compatibility for the individual window limits is assumed.
-/
-- Credit: @AlfredMelson. The Chebyshev estimate is from the merged R2 by @cj-55m.
namespace OMA.R_Erdos912_erdos_912_R2_H2_R1
open Finset Filter
open scoped Topology
noncomputable section

private def scale (n : ℕ) := Real.sqrt ((n : ℝ)/Real.log n)
private def bins (n : ℕ) : Finset ℕ :=
  (((range (n+1)).filter (fun p => p.Prime ∧ n < p*p)).image (fun p => n/p))
private def lower (n M : ℕ) := (bins n).filter (fun j : ℕ => scale n/M < (j:ℝ) ∧ (j:ℝ) ≤ scale n)
private def upper (n M : ℕ) := (bins n).filter (fun j : ℕ => scale n < (j:ℝ) ∧ (j:ℝ) ≤ M*scale n)
private def total (n : ℕ) : ℝ := (bins n).card / scale n
private def middle (n M : ℕ) : ℝ := (((lower n M).card : ℝ) + ((upper n M).card : ℝ))/scale n

private theorem count_bound (n M : ℕ) (y x : ℝ) (hy : y = scale n) (hy0 : 0 < y)
    (hm : (0:ℝ) < M) (hxy : x*(M*y)=n) (hx : 0 ≤ x) :
    (bins n).card ≤ (lower n M).card + (upper n M).card +
        ⌊y/M⌋₊ + Nat.primeCounting ⌊x⌋₊ := by
  classical
  have sub : bins n ⊆ (lower n M ∪ upper n M) ∪ Icc 1 ⌊y/M⌋₊ ∪
      (Nat.primesLE ⌊x⌋₊).image (fun p => n/p) := by
    intro j hj
    obtain ⟨p,hp,hpj⟩ := mem_image.mp hj
    obtain ⟨hpN, hprime, -⟩ := mem_filter.mp hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hprime.pos
    by_cases hlo : (j:ℝ) ≤ y/M
    · apply mem_union_left
      apply mem_union_right
      apply mem_Icc.mpr
      refine ⟨?_, (Nat.le_floor_iff (by positivity)).2 hlo⟩
      rw [← hpj]
      exact Nat.div_pos (by simpa using mem_range.mp hpN) hprime.pos
    by_cases hhi : M*y < (j:ℝ)
    · apply mem_union_right
      refine mem_image.mpr ⟨p, Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff hx).2 ?_,hprime⟩,hpj⟩
      have hjp : (j:ℝ)*p ≤ n := by rw [← hpj]; exact_mod_cast Nat.div_mul_le_self n p
      have hh := (mul_lt_mul_of_pos_right hhi hp0).trans_le hjp
      rw [← hxy, mul_comm x] at hh
      exact le_of_lt (lt_of_mul_lt_mul_left hh (by positivity))
    · apply mem_union_left
      apply mem_union_left
      subst y
      by_cases hmid : (j:ℝ) ≤ scale n
      · exact mem_union_left _ (mem_filter.mpr ⟨hj,lt_of_not_ge hlo,hmid⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hj,lt_of_not_ge hmid,le_of_not_gt hhi⟩)
  have h := card_le_card sub
  have h₁ := card_union_le ((lower n M ∪ upper n M) ∪ Icc 1 ⌊y/M⌋₊)
    ((Nat.primesLE ⌊x⌋₊).image (fun p => n/p))
  have h₂ := card_union_le (lower n M ∪ upper n M) (Icc 1 ⌊y/M⌋₊)
  have h₃ := card_union_le (lower n M) (upper n M)
  have h₄ : ((Nat.primesLE ⌊x⌋₊).image (fun p => n/p)).card ≤ Nat.primeCounting ⌊x⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting]; exact card_image_le
  rw [Nat.card_Icc] at h₂
  omega

private theorem window_error (M : ℕ) (hm : 1 ≤ M) : ∀ᶠ n : ℕ in atTop,
    dist (total n) (middle n M) ≤ 11/(M:ℝ) := by
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop ((M:ℝ)^2)
  filter_upwards [hlog,eventually_ge_atTop 3] with n hl hn
  change (M:ℝ)^2 ≤ Real.log n at hl
  have hm1 : (1:ℝ) ≤ M := by exact_mod_cast hm
  have hm0 : (0:ℝ) < M := by linarith
  have hn1 : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
  let L := Real.log (n:ℝ)
  let y := scale n
  let x := y * L / M
  have hL : 0 < L := Real.log_pos hn1
  have hy : 0 < y := Real.sqrt_pos.mpr (div_pos (by linarith) hL)
  have hy2 : y^2 = (n:ℝ)/L := Real.sq_sqrt (by positivity)
  have hyL : y^2 * L = n := (eq_div_iff hL.ne').mp hy2
  have hxy : x*((M:ℝ)*y) = n := by dsimp [x]; field_simp; nlinarith [hyL]
  have hx : 0 < x := div_pos (mul_pos hy hL) hm0
  have hs : Real.sqrt (n:ℝ) ≤ x := by
    have hs0 := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
    have h1 : (y*L)^2 = n*L := by nlinarith only [congrArg (· * L) hyL]
    have h2 : (Real.sqrt n * (M:ℝ))^2 ≤ (y*L)^2 := by
      rw [mul_pow, hs0, h1]; exact mul_le_mul_of_nonneg_left hl (by positivity)
    apply (le_div_iff₀ hm0).2
    nlinarith [Real.sqrt_nonneg (n:ℝ), mul_nonneg (Real.sqrt_nonneg (n:ℝ)) hm0.le,
      mul_pos hy hL]
  have hx1 : 1 < x := by
    have hh := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
    nlinarith [Real.sqrt_nonneg (n:ℝ)]
  have hLX : L/2 ≤ Real.log x := by
    simpa [L,Real.log_sqrt (show 0 ≤ (n:ℝ) by positivity)] using
      Real.log_le_log (Real.sqrt_pos.mpr (by linarith : 0 < (n:ℝ))) hs
  have hp := R_Erdos912_erdos_912_R2.prime_count_upper hx1
  have hp' : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 10*y/M := by
    apply hp.trans
    apply (div_le_iff₀ (Real.log_pos hx1)).2
    have h := mul_le_mul_of_nonneg_left hLX (show 0 ≤ 10*y/M by positivity)
    calc
      5*x = 10*y/M*(L/2) := by dsimp [x]; ring
      _ ≤ _ := h
  have hi := count_bound n M y x rfl hy hm0 hxy hx.le
  have hcard : ((bins n).card:ℝ) ≤ (lower n M).card + (upper n M).card + 11*y/M := by
    have hh := (Nat.cast_le (α:=ℝ)).2 hi
    push_cast at hh
    linarith [Nat.floor_le (show 0 ≤ y/M by positivity),show 11*y/M = y/M+10*y/M by ring]
  have dis : Disjoint (lower n M) (upper n M) := by
    apply disjoint_left.mpr
    intro j hj hj'
    exact (not_lt_of_ge (mem_filter.mp hj).2.2) (mem_filter.mp hj').2.1
  have hlo : (lower n M).card + (upper n M).card ≤ (bins n).card := by
    rw [← card_union_of_disjoint dis]
    exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  have hreal := (Nat.cast_le (α:=ℝ)).2 hlo
  push_cast at hreal
  rw [Real.dist_eq]
  unfold total middle
  rw [abs_of_nonneg (sub_nonneg.mpr (div_le_div_of_nonneg_right hreal hy.le))]
  change (bins n).card / y - (((lower n M).card:ℝ)+(upper n M).card)/y ≤ 11/M
  rw [← sub_div, div_le_iff₀ hy]
  linarith [show 11/(M:ℝ)*y = 11*y/M by ring]

/-- Convergence on the long-interval side of the transition scale, for each fixed window. -/
def H1 : Prop := ∀ M : ℕ, 1 ≤ M → ∃ c : ℝ, Tendsto (fun n : ℕ =>
  let Y := Real.sqrt ((n : ℝ) / Real.log n)
  let J := (((range (n+1)).filter (fun p => p.Prime ∧ n < p*p)).image (fun p => n/p))
  (((J.filter (fun j : ℕ => Y / M < (j : ℝ) ∧ (j : ℝ) ≤ Y)).card : ℝ) / Y)) atTop (𝓝 c)

/-- Convergence on the short-interval side of the transition scale, for each fixed window. -/
def H2 : Prop := ∀ M : ℕ, 1 ≤ M → ∃ c : ℝ, Tendsto (fun n : ℕ =>
  let Y := Real.sqrt ((n : ℝ) / Real.log n)
  let J := (((range (n+1)).filter (fun p => p.Prime ∧ n < p*p)).image (fun p => n/p))
  (((J.filter (fun j : ℕ => Y < (j : ℝ) ∧ (j : ℝ) ≤ M * Y)).card : ℝ) / Y)) atTop (𝓝 c)

theorem main : H1 → H2 → OMA.R_Erdos912_erdos_912_R2.H2 := by
  intro h1 h2
  have hC : CauchySeq total := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨m,hm⟩ := exists_nat_gt (44 / ε)
    let M := m+1
    have hM : 1 ≤ M := Nat.succ_pos _
    have hMr : (0:ℝ) < M := by exact_mod_cast (show 0<M by omega)
    have hsmall : 11/(M:ℝ) < ε/4 := by
      have haux := (div_lt_iff₀ hε).mp hm
      apply (div_lt_iff₀ hMr).2
      have hmm : (m:ℝ) ≤ M := by exact_mod_cast Nat.le_succ m
      nlinarith [mul_le_mul_of_nonneg_right hmm hε.le]
    obtain ⟨a,ha⟩ := h1 M hM
    obtain ⟨b,hb⟩ := h2 M hM
    have hmid : Tendsto (fun n => middle n M) atTop (𝓝 (a+b)) := by
      change Tendsto (fun n => ((lower n M).card : ℝ)/scale n) atTop (𝓝 a) at ha
      change Tendsto (fun n => ((upper n M).card : ℝ)/scale n) atTop (𝓝 b) at hb
      simpa only [middle, add_div] using ha.add hb
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hmid.cauchySeq (ε/2) (by positivity)
    obtain ⟨K,hK⟩ := (window_error M hM).exists_forall_of_atTop
    refine ⟨max N K, ?_⟩
    intro i hi j hj
    have hiK := hK i ((le_max_right ..).trans hi)
    have hjK := hK j ((le_max_right ..).trans hj)
    have hpair := hN i ((le_max_left ..).trans hi) j ((le_max_left ..).trans hj)
    have htri := dist_triangle4 (total i) (middle i M) (middle j M) (total j)
    rw [dist_comm (middle j M) (total j)] at htri
    linarith
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete hC
  have ht : Tendsto (fun n : ℕ => ((bins n).card : ℝ) /
      ((n:ℝ)/Real.log n)^(1/2:ℝ)) atTop (𝓝 c) := by
    change Tendsto (fun n => ((bins n).card : ℝ)/Real.sqrt ((n:ℝ)/Real.log n)) atTop (𝓝 c) at hc
    simpa only [Real.sqrt_eq_rpow] using hc
  exact ht.liminf_eq.trans ht.limsup_eq.symm

end
end OMA.R_Erdos912_erdos_912_R2_H2_R1
