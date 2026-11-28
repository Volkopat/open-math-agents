import OMAStatements.S_mo_147075
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
A series with a logarithmic bound on symmetric second differences.
Ravi's MathOverflow question 147075, formalized in the parent statement.
Proof by @xlh1551. The dyadic construction uses the bounded profile
x/(1+|x|); its slopes at zero form the harmonic series.
-/

namespace OMA.SecondDifference

noncomputable def profile (x : ℝ) : ℝ := x / (1 + |x|)

lemma profile_neg (x : ℝ) : profile (-x) = -profile x := by simp [profile, neg_div]

theorem abs_profile_le_one (x : ℝ) : |profile x| ≤ 1 := by
  have ha := abs_nonneg x
  rw [profile, abs_div, abs_of_pos (show 0 < 1 + |x| by linarith)]
  exact (div_le_one (by linarith)).mpr (by linarith)

theorem abs_profile_sub_id (x : ℝ) : |profile x - x| ≤ x^2 := by
  have ha := abs_nonneg x
  have hp : 0 < 1 + |x| := by linarith
  have eqn : profile x - x = -(x * |x|) / (1 + |x|) := by
    unfold profile
    field_simp
    ring
  rw [eqn, abs_div, abs_neg, abs_mul, abs_abs, ← sq, sq_abs, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  nlinarith [mul_nonneg (sq_nonneg x) ha]

private theorem positive_side (x h : ℝ) (hx : 0 ≤ x) (hh : 0 ≤ h) :
    |profile (x+h) + profile (x-h) - 2*profile x| ≤ 6*h^2 := by
  by_cases hc : h ≤ x
  · have hxp : 0 < 1 + (x+h) := by linarith
    have hxm : 0 < 1 + (x-h) := by linarith
    have hx0 : 0 < 1+x := by linarith
    let D := (1+x+h)*(1+x-h)*(1+x)
    have hD : 1 ≤ D := by
      apply one_le_mul_of_one_le_of_one_le _ (by linarith : 1 ≤ 1+x)
      exact one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    have hfactor : profile (x+h) + profile (x-h) - 2*profile x = -(2*h^2)/D := by
      simp only [profile, abs_of_nonneg (show 0 ≤ x+h by linarith),
        abs_of_nonneg (sub_nonneg.mpr hc), abs_of_nonneg hx, D]
      rw [show 1+x+h = 1+(x+h) by ring, show 1+x-h = 1+(x-h) by ring]
      field_simp
      ring
    have hp : 0 < D := by linarith
    rw [hfactor, abs_div, abs_neg, abs_of_nonneg (by nlinarith [sq_nonneg h] : 0 ≤ 2*h^2), abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hD), sq_nonneg h]
  · have hp := abs_le.mp (abs_profile_sub_id (x+h))
    have hm := abs_le.mp (abs_profile_sub_id (x-h))
    have h0 := abs_le.mp (abs_profile_sub_id x)
    have hx2 : x^2 ≤ h^2 := by nlinarith [mul_nonneg (show 0 ≤ h-x by linarith) (show 0 ≤ h+x by linarith)]
    apply abs_le.mpr
    constructor <;> nlinarith [hp.1, hp.2, hm.1, hm.2, h0.1, h0.2]

theorem second_difference (x h : ℝ) :
    |profile (x+h) + profile (x-h) - 2*profile x| ≤ 6*h^2 := by
  have nonneg_step (x h : ℝ) (hh : 0 ≤ h) :
      |profile (x+h) + profile (x-h) - 2*profile x| ≤ 6*h^2 := by
    by_cases hx : 0 ≤ x
    · exact positive_side x h hx hh
    · have H := positive_side (-x) h (by linarith) hh
      rw [show -x+h = -(x-h) by ring, show -x-h = -(x+h) by ring, profile_neg, profile_neg, profile_neg] at H
      rwa [show -profile (x-h) + -profile (x+h) - 2* -profile x =
        -(profile (x+h) + profile (x-h) - 2*profile x) by ring, abs_neg] at H
  by_cases hh : 0 ≤ h
  · exact nonneg_step x h hh
  · have H := nonneg_step x (-h) (by linarith)
    simpa only [← sub_eq_add_neg, sub_neg_eq_add, add_comm (profile (x-h)) (profile (x+h)), neg_sq] using H


private theorem ordered_positive_pair {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    0 ≤ profile y - profile x ∧ profile y - profile x ≤ y-x := by
  have hy : 0 ≤ y := hx.trans hxy
  have hden : 1 ≤ (1+y)*(1+x) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hpos : 0 < (1+y)*(1+x) := by linarith
  have H : profile y - profile x = (y-x)/((1+y)*(1+x)) := by
    simp only [profile, abs_of_nonneg hx, abs_of_nonneg hy]
    have hp : 0 < 1+x := by linarith
    have hq : 0 < 1+y := by linarith
    field_simp
    ring
  rw [H]
  exact ⟨div_nonneg (sub_nonneg.mpr hxy) hpos.le, (div_le_iff₀ hpos).mpr
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hden)])⟩

theorem profile_increments {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ profile y - profile x ∧ profile y - profile x ≤ y-x := by
  by_cases hx : 0 ≤ x
  · exact ordered_positive_pair hx hxy
  by_cases hy : y ≤ 0
  · have H := ordered_positive_pair (neg_nonneg.mpr hy) (neg_le_neg hxy)
    simp only [profile_neg] at H
    constructor <;> linarith [H.1, H.2]
  · have H := ordered_positive_pair (x := 0) le_rfl (y := -x) (by linarith)
    have K := ordered_positive_pair (x := 0) le_rfl (y := y) (by linarith)
    have hz : profile 0 = 0 := by simp [profile]
    simp only [profile_neg, hz] at H K
    constructor <;> linarith [H.1,H.2,K.1,K.2]

end OMA.SecondDifference

open Finset Set

namespace OMA.SecondDifference

/-- The total increase on pairwise disjoint intervals is at most the full range of a
bounded increasing function, independently of the number of intervals. -/
theorem disjoint_interval_variation {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (f : ℝ → ℝ) (hf : Monotone f) {L U : ℝ} (hLU : L ≤ U)
    (hab : ∀ i ∈ s, a i ≤ b i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))
    (hl : ∀ i ∈ s, L ≤ f (a i)) (hu : ∀ i ∈ s, f (b i) ≤ U) :
    ∑ i ∈ s, (f (b i) - f (a i)) ≤ U-L := by
  classical
  induction s using Finset.strongInductionOn generalizing L with
  | _ s ih =>
    by_cases hempty : s = ∅
    · simpa [hempty] using sub_nonneg.mpr hLU
    have hne := Finset.nonempty_iff_ne_empty.mpr hempty
    by_cases hdeg : ∃ i ∈ s, a i = b i
    · obtain ⟨i, hi, hiab⟩ := hdeg
      have hsub := s.erase_subset i
      have H := ih (s.erase i) (s.erase_ssubset hi) hLU
        (fun j hj => hab j (hsub hj))
        (fun j hj k hk => hdis j (hsub hj) k (hsub hk))
        (fun j hj => hl j (hsub hj)) (fun j hj => hu j (hsub hj))
      rw [← s.add_sum_erase (fun j => f (b j) - f (a j)) hi, hiab, sub_self, zero_add]
      exact H
    obtain ⟨i, hi, hmin⟩ := s.exists_min_image a hne
    have hsub := s.erase_subset i
    have lower (j) (hj : j ∈ s.erase i) : f (b i) ≤ f (a j) := by
      apply hf
      have hj' := hsub hj
      have hd := Set.Ioo_disjoint_Ioo.mp (hdis i hi j hj' (Finset.ne_of_mem_erase hj).symm)
      rw [max_eq_right (hmin j hj')] at hd
      rcases min_le_iff.mp hd with h | h
      · exact h
      · exact (hdeg ⟨j, hj', le_antisymm (hab j hj') h⟩).elim
    have H := ih (s.erase i) (s.erase_ssubset hi) (hu i hi)
      (fun j hj => hab j (hsub hj)) (fun j hj k hk => hdis j (hsub hj) k (hsub hk))
      lower (fun j hj => hu j (hsub hj))
    rw [← s.add_sum_erase (fun j => f (b j) - f (a j)) hi]
    linarith [hl i hi]

end OMA.SecondDifference

open Finset Set

namespace OMA.SecondDifference

/-- A function uniformly approximable by Lipschitz functions with increasing remainders
of arbitrarily small total variation is absolutely continuous on the entire line. -/
theorem absolutely_continuous_of_monotone_tails {f : ℝ → ℝ}
    (h : ∀ δ > (0 : ℝ), ∃ (g q : ℝ → ℝ) (K L U : ℝ),
      0 ≤ K ∧ L ≤ U ∧ U-L < δ ∧ (∀ x, f x = g x + q x) ∧ Monotone q ∧
      (∀ x, L ≤ q x ∧ q x ≤ U) ∧ (∀ x y, x ≤ y → |g y - g x| ≤ K * (y-x))) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
        (∀ i j, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
        (∑ i, (b i - a i)) < η → (∑ i, |f (b i) - f (a i)|) < ε := by
  intro ε hε
  obtain ⟨g,q,K,L,U,hK,hLU,hδ,heq,hq,hbound,hg⟩ := h (ε/2) (by linarith)
  have hK' : 0 < K+1 := by linarith
  refine ⟨(ε/2)/(K+1), div_pos (by linarith) hK', ?_⟩
  intro n a b hab hd hlen
  have hvar := disjoint_interval_variation (univ : Finset (Fin n)) a b q hq hLU
    (fun i _ => hab i) (fun i _ j _ => hd i j)
    (fun i _ => (hbound (a i)).1) (fun i _ => (hbound (b i)).2)
  have hinc (i : Fin n) : |f (b i) - f (a i)| ≤ K*(b i - a i) + (q (b i)-q (a i)) := by
    rw [heq, heq, show g (b i) + q (b i) - (g (a i) + q (a i)) =
      (g (b i)-g (a i)) + (q (b i)-q (a i)) by linarith]
    have htriangle := abs_add_le (g (b i)-g (a i)) (q (b i)-q (a i))
    rw [abs_of_nonneg (sub_nonneg.mpr (hq (hab i)))] at htriangle
    exact htriangle.trans (add_le_add (hg _ _ (hab i)) le_rfl)
  have htot := Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => hinc i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at htot
  have hs : 0 ≤ ∑ i, (b i - a i) := Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (hab i))
  have small := (lt_div_iff₀ hK').mp hlen
  nlinarith

end OMA.SecondDifference

open Finset

namespace OMA.SecondDifference

/-- The low-frequency part of the smooth series bound grows like the last term. -/
theorem dyadic_weight_sum (n : ℕ) (hn : 2 ≤ n) :
    ∑ j ∈ range n, (2 : ℝ)^(j+1) / (j+1 : ℕ) ≤ 4 * (2 : ℝ)^n / n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [sum_range_succ]
  | succ n hn ih =>
    rw [sum_range_succ]
    refine (add_le_add ih le_rfl).trans ?_
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hn1 : (0 : ℝ) < (n:ℝ)+1 := by linarith
    simp only [Nat.cast_succ, pow_succ]
    field_simp
    nlinarith [mul_nonneg (le_of_lt (pow_pos (by norm_num : (0:ℝ)<2) n)) (sub_nonneg.mpr h2)]

end OMA.SecondDifference

open Finset Filter Set

namespace OMA.SecondDifference

noncomputable def geo (j : ℕ) : ℝ := (1 / 2 : ℝ) ^ (j+1)
noncomputable def amplitude (j : ℕ) : ℝ := geo j / ((j:ℝ)+1)
noncomputable def scale (j : ℕ) : ℝ := (2 : ℝ) ^ (j+1)
noncomputable def term (j : ℕ) (x : ℝ) : ℝ := amplitude j * profile (scale j * x)
noncomputable def witness (x : ℝ) : ℝ := ∑' j, term j x

theorem geo_pos (j : ℕ) : 0 < geo j := pow_pos (by norm_num) _
theorem scale_pos (j : ℕ) : 0 < scale j := pow_pos (by norm_num) _
theorem amplitude_pos (j : ℕ) : 0 < amplitude j :=
  div_pos (geo_pos j) (by exact_mod_cast Nat.succ_pos j)

theorem amplitude_scale (j : ℕ) : amplitude j * scale j = 1 / ((j:ℝ)+1) := by
  unfold amplitude geo scale
  rw [div_mul_eq_mul_div, ← mul_pow]
  norm_num

theorem abs_term_le_geo (j : ℕ) (x : ℝ) : |term j x| ≤ geo j := by
  rw [term,abs_mul,abs_of_pos (amplitude_pos j)]
  calc
    _ ≤ amplitude j * 1 := mul_le_mul_of_nonneg_left (abs_profile_le_one _) (amplitude_pos j).le
    _ ≤ geo j := by
      rw [mul_one, amplitude]
      exact div_le_self (geo_pos j).le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))

theorem term_increments (j : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    0 ≤ term j y - term j x ∧ term j y - term j x ≤ y-x := by
  have h1 := profile_increments (mul_le_mul_of_nonneg_left hxy (scale_pos j).le)
  simp only [term, ← mul_sub]
  refine ⟨mul_nonneg (amplitude_pos j).le h1.1, ?_⟩
  calc
    _ ≤ amplitude j * (scale j*y - scale j*x) := mul_le_mul_of_nonneg_left h1.2 (amplitude_pos j).le
    _ = (y-x) / ((j:ℝ)+1) := by rw [← mul_sub, ← mul_assoc, amplitude_scale]; ring
    _ ≤ y-x := div_le_self (sub_nonneg.mpr hxy) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))

theorem summable_geo : Summable geo :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem summable_term (x : ℝ) : Summable (fun j => term j x) :=
  Summable.of_norm_bounded summable_geo (fun j => by simpa [Real.norm_eq_abs] using abs_term_le_geo j x)

theorem witness_ac :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) →
        (∀ i j, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) →
        (∑ i, (b i - a i)) < η → (∑ i, |witness (b i) - witness (a i)|) < ε := by
  apply absolutely_continuous_of_monotone_tails
  intro δ hδ
  obtain ⟨N,hN⟩ := ((tendsto_sum_nat_add geo).eventually_lt_const (show 0 < δ/2 by linarith)).exists
  let T := ∑' j, geo (j+N)
  let g (x : ℝ) := ∑ j ∈ range N, term j x
  let q (x : ℝ) := ∑' j, term (j+N) x
  have hT : 0 ≤ T := tsum_nonneg (fun j => (geo_pos (j+N)).le)
  have hsumG : Summable (fun j => geo (j+N)) := (summable_nat_add_iff N).mpr summable_geo
  have hsum (x : ℝ) : Summable (fun j => term (j+N) x) := (summable_nat_add_iff N).mpr (summable_term x)
  refine ⟨g,q,N,-T,T,Nat.cast_nonneg _,by linarith,by change T < δ/2 at hN; linarith,?_,?_,?_,?_⟩
  · intro x
    exact ((summable_term x).sum_add_tsum_nat_add N).symm
  · intro x y hxy
    exact (hsum x).tsum_le_tsum (fun j => sub_nonneg.mp (term_increments _ hxy).1) (hsum y)
  · intro x
    have hneg := hsumG.neg.tsum_le_tsum (fun j => (abs_le.mp (abs_term_le_geo (j+N) x)).1) (hsum x)
    exact ⟨by simpa [q,T,tsum_neg] using hneg, (hsum x).tsum_le_tsum (fun j => (abs_le.mp (abs_term_le_geo (j+N) x)).2) hsumG⟩
  · intro x y hxy
    dsimp [g]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ j ∈ range N, |term j y - term j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range N, (y-x) := Finset.sum_le_sum fun j _ => by
        rw [abs_of_nonneg (term_increments j hxy).1]; exact (term_increments j hxy).2
      _ = _ := by simp [mul_sub]

end OMA.SecondDifference

open Finset Set Filter Topology

namespace OMA.SecondDifference

theorem term_derivative_zero (j : ℕ) : HasDerivAt (term j) (1 / ((j:ℝ)+1)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  let F (t : ℝ) := amplitude j * scale j / (1 + |scale j*t|)
  have hc : ContinuousAt F 0 := by
    dsimp [F]
    fun_prop (disch := norm_num)
  have ht : Tendsto F (𝓝[≠] 0) (𝓝 (1 / ((j:ℝ)+1))) := by
    simpa [F, amplitude_scale] using hc.continuousWithinAt.tendsto (s := ({0}ᶜ : Set ℝ))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  have hp : 0 < 1 + |scale j*t| := by linarith [abs_nonneg (scale j*t)]
  simp only [F, term, profile, zero_add, mul_zero, abs_zero, add_zero, zero_div, sub_zero, smul_eq_mul]
  field_simp

/-- On passing from 2^m to 2^(m+1) terms, the harmonic sum increases by at least 1/2. -/
theorem harmonic_block_lower (m : ℕ) :
    (m:ℝ)/2 ≤ ∑ j ∈ range (2^m), 1 / ((j:ℝ)+1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    let N := 2^m
    have hN : 0 < N := pow_pos (by decide) _
    have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
    have hb : (1/2:ℝ) ≤ ∑ j ∈ range N, 1 / (((N+j:ℕ):ℝ)+1) := by
      calc
        (1/2:ℝ) = ∑ _j ∈ range N, 1/(2*(N:ℝ)) := by simp; field_simp
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' : (j:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast (Finset.mem_range.mp hj)
          apply one_div_le_one_div_of_le (by positivity)
          push_cast
          linarith
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    push_cast
    change (m + 1 : ℝ)/2 ≤ (∑ j ∈ range N, 1/((j:ℝ)+1)) + _
    change (m:ℝ)/2 ≤ ∑ j ∈ range N, 1/((j:ℝ)+1) at ih
    dsimp [N] at ih hb ⊢
    push_cast at hb
    linarith

theorem not_differentiable_witness : ¬ DifferentiableAt ℝ witness 0 := by
  intro h
  obtain ⟨m,hm⟩ := exists_nat_gt (2 * deriv witness 0)
  let N := 2 ^ m
  let G (x : ℝ) := ∑ j ∈ range N, term j x
  have hg : HasDerivAt G (∑ j ∈ range N, 1/((j:ℝ)+1)) 0 :=
    HasDerivAt.fun_sum (fun j _ => term_derivative_zero j)
  have eqtail (x : ℝ) : witness x - G x = ∑' j, term (j+N) x := by
    rw [sub_eq_iff_eq_add, add_comm]
    exact ((summable_term x).sum_add_tsum_nat_add N).symm
  have hm' : Monotone (fun x => witness x - G x) := by
    intro x y hxy
    change witness x - G x ≤ witness y - G y
    rw [eqtail, eqtail]
    exact ((summable_nat_add_iff N).mpr (summable_term x)).tsum_le_tsum
      (fun j => sub_nonneg.mp (term_increments _ hxy).1) ((summable_nat_add_iff N).mpr (summable_term y))
  have hbound := hm'.deriv_nonneg (x := 0)
  change 0 ≤ deriv (witness - G) 0 at hbound
  rw [(h.hasDerivAt.sub hg).deriv] at hbound
  have lower := harmonic_block_lower m
  change (m:ℝ)/2 ≤ ∑ j ∈ range N, 1/((j:ℝ)+1) at lower
  linarith

end OMA.SecondDifference

open Finset Filter Set

namespace OMA.SecondDifference

noncomputable def second (f : ℝ → ℝ) (x h : ℝ) : ℝ := f (x+h) + f (x-h) - 2*f x
noncomputable def head (N : ℕ) (x : ℝ) : ℝ := ∑ j ∈ range N, term j x
noncomputable def tail (N : ℕ) (x : ℝ) : ℝ := ∑' j, term (j+N) x

lemma split_witness (N : ℕ) (x : ℝ) : witness x = head N x + tail N x :=
  ((summable_term x).sum_add_tsum_nat_add N).symm

lemma term_second (j : ℕ) (x h : ℝ) :
    |second (term j) x h| ≤ (6*h^2) * (scale j / ((j:ℝ)+1)) := by
  have hest := second_difference (scale j * x) (scale j * h)
  have hid : second (term j) x h = amplitude j *
      (profile (scale j*x + scale j*h) + profile (scale j*x - scale j*h) - 2*profile (scale j*x)) := by
    simp only [second,term,mul_add,mul_sub]; ring
  rw [hid, abs_mul,abs_of_pos (amplitude_pos j)]
  refine (mul_le_mul_of_nonneg_left hest (amplitude_pos j).le).trans_eq ?_
  calc
    _ = (6*h^2) * (amplitude j * scale j) * scale j := by ring
    _ = _ := by rw [amplitude_scale]; ring

lemma head_bound {N : ℕ} (hN : 2 ≤ N) (x h : ℝ) :
    |second (head N) x h| ≤ (6*h^2)*(4*(2:ℝ)^N/N) := by
  have he : second (head N) x h = ∑ j ∈ range N, second (term j) x h := by
    simp only [second,head,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ∑ j ∈ range N, |second (term j) x h| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range N, (6*h^2)*(scale j/((j:ℝ)+1)) :=
      Finset.sum_le_sum fun j _ => term_second j x h
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by nlinarith [sq_nonneg h])
      simpa [scale] using dyadic_weight_sum N hN

lemma tail_bound (N : ℕ) (x : ℝ) :
    |tail N x| ≤ (1/2 : ℝ)^N / ((N:ℝ)+1) := by
  let C := (1/2 : ℝ)^(N+1) / ((N:ℝ)+1)
  have hs0 : HasSum (fun j : ℕ => (1/2 : ℝ)^j) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1) using 1
    norm_num
  have hs := hs0.mul_right C
  have hle (j : ℕ) : |term (j+N) x| ≤ (1/2 : ℝ)^j*C := by
    rw [term, abs_mul, abs_of_pos (amplitude_pos _)]
    calc
      _ ≤ amplitude (j+N) * 1 := mul_le_mul_of_nonneg_left (abs_profile_le_one _) (amplitude_pos _).le
      _ ≤ geo (j+N) / ((N:ℝ)+1) := by
        rw [mul_one,amplitude]
        apply div_le_div_of_nonneg_left (geo_pos _).le (by positivity)
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) j]
      _ = _ := by simp only [geo,C,Nat.add_assoc,pow_add]; ring
  have sm : Summable (fun j => term (j+N) x) := (summable_nat_add_iff N).mpr (summable_term x)
  have hh := sm.tsum_le_tsum (fun j => (abs_le.mp (hle j)).2) hs.summable
  have hl := hs.summable.neg.tsum_le_tsum (fun j => (abs_le.mp (hle j)).1) sm
  rw [tsum_neg, hs.tsum_eq] at hl
  rw [hs.tsum_eq] at hh
  have he : 2*C = (1/2:ℝ)^N / ((N:ℝ)+1) := by simp only [C,pow_succ]; ring
  rw [he] at hl hh
  exact abs_le.mpr ⟨hl,hh⟩

lemma tail_second_bound (N : ℕ) (x h : ℝ) :
    |second (tail N) x h| ≤ 4*((1/2:ℝ)^N/((N:ℝ)+1)) := by
  have H := abs_le.mp (tail_bound N (x+h))
  have K := abs_le.mp (tail_bound N (x-h))
  have L := abs_le.mp (tail_bound N x)
  unfold second
  apply abs_le.mpr
  constructor <;> linarith [H.1,H.2,K.1,K.2,L.1,L.2]

lemma pieces (N : ℕ) (x h : ℝ) :
    second witness x h = second (head N) x h + second (tail N) x h := by
  simp only [second,split_witness N]; ring


theorem witness_modulus (x h : ℝ) (hpos : 0 < |h|) (hsmall : |h| < 1) :
    |second witness x h| ≤ 64 * |h| / Real.log (1/|h|) := by
  let u := |h|
  have hu : 0 < u := hpos
  have hl : 0 < Real.log (1/u) := Real.log_pos ((lt_div_iff₀ hu).mpr (by simpa [u] using hsmall))
  have h1 : 0 < 1/u := one_div_pos.mpr hu
  by_cases hbig : 1/4 ≤ u
  · have bound (z : ℝ) : |witness z| ≤ 1 := by
      simpa [witness,tail] using tail_bound 0 z
    have A := abs_le.mp (bound (x+h))
    have B := abs_le.mp (bound (x-h))
    have D := abs_le.mp (bound x)
    have hw : |second witness x h| ≤ 4 := by
      unfold second; apply abs_le.mpr; constructor <;> linarith [A.1,A.2,B.1,B.2,D.1,D.2]
    apply hw.trans
    apply (le_div_iff₀ hl).mpr
    have hr : 1/u ≤ 4 := (div_le_iff₀ hu).mpr (by linarith)
    change 4 * Real.log (1/u) ≤ 64*u
    linarith [Real.log_le_sub_one_of_pos h1]
  obtain ⟨N,hlo,hhi⟩ := exists_nat_pow_near (x := 1/u) (y := (2:ℝ))
    ((le_div_iff₀ hu).mpr (by linarith [show u < 1 from hsmall])) (by norm_num)
  have h4 : 4 < 1/u := (lt_div_iff₀ hu).mpr (by linarith)
  have hN : 2 ≤ N := by
    by_contra! H
    have hor : N = 0 ∨ N = 1 := by omega
    rcases hor with rfl | rfl <;> norm_num at hhi h4 <;> linarith
  have hn2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0:ℝ) < N := by linarith
  have hp : 0 < (2:ℝ)^N := pow_pos (by norm_num) _
  have hpU := (le_div_iff₀ hu).mp hlo
  have hU := (div_lt_iff₀ hu).mp hhi
  have hg : (1/2:ℝ)^N ≤ 2*u := by
    rw [one_div_pow]
    apply (div_le_iff₀ hp).mpr
    rw [pow_succ] at hU
    linarith
  have hhead : |second (head N) x h| ≤ 24*u/N := by
    apply (head_bound hN x h).trans
    rw [← sq_abs]
    change 6*u^2*(4*(2:ℝ)^N/N) ≤ 24*u/N
    calc
      _ = (24*u/N)*((2:ℝ)^N*u) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hpU
  have htail : |second (tail N) x h| ≤ 8*u/N := by
    apply (tail_second_bound N x h).trans
    have hlo' := div_le_div_of_nonneg_left (show 0 ≤ 2*u by linarith) hn (show (N:ℝ) ≤ N+1 by linarith)
    have hup := div_le_div_of_nonneg_right hg (show (0:ℝ) ≤ N+1 by linarith)
    calc
      _ ≤ 4 * (2*u/(N:ℝ)) := mul_le_mul_of_nonneg_left (hup.trans hlo') (by norm_num)
      _ = _ := by ring
  have hlogN : Real.log (1/u) ≤ 2*(N:ℝ) := by
    have hz := Real.log_le_log h1 hhi.le
    rw [Real.log_pow, Nat.cast_succ] at hz
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (x := 2) (by norm_num)]
    have hm := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (N:ℝ)+1 by linarith)
    linarith
  rw [pieces N x h]
  apply (abs_add_le _ _).trans
  calc
    _ ≤ 24*u/N + 8*u/N := add_le_add hhead htail
    _ = 32*u/N := by ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ hn hl).mpr
      change 32*u*Real.log (1/u) ≤ 64*u*N
      nlinarith [mul_le_mul_of_nonneg_left hlogN hu.le]

end OMA.SecondDifference

open OMA.SecondDifference

theorem OMA.solution : type_of% @OMA.S_mo_147075.main := by
  refine ⟨witness, 64, witness_ac, by norm_num, ?_, ?_⟩
  · exact witness_modulus
  · intro hf
    exact not_differentiable_witness ((hf.differentiable (by norm_num)).differentiableAt)
