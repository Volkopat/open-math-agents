import OMAReductions.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1
import Mathlib

-- Credit: @marcusbuffett

namespace OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1

open Set Filter Real Erdos448
open scoped Topology

/-- Small-ratio density estimate restricted to squarefree arguments. -/
def H1 : Prop := ∀ s : ℝ, 0 < s → s < 1 → ∃ C > 0, ∀ t : ℝ, 0 < t →
  {m : ℕ | Squarefree m ∧ (tauPlus m : ℝ) < t * m.divisors.card}.upperDensity ≤ C*t^s

/-- Squarefull dilation estimate. The weights after dilation are the divisor
counts of the squarefull numbers divided by those numbers. Their sum converges;
the tail of all positive multiples is bounded by the unweighted reciprocal tail. -/
def H2 : Prop := ∃ K : ℝ, 0 < K ∧ ∀ (c : ℝ), 0 ≤ c → ∀ B : ℕ → Set ℕ,
  (∀ d : ℕ, 0 < d → (∀ p : ℕ, p.Prime → p ∣ d → p^2 ∣ d) →
    (B d).upperDensity ≤ c * d.divisors.card) →
  {n : ℕ | ∃ d m : ℕ, 0 < d ∧ (∀ p : ℕ, p.Prime → p ∣ d → p^2 ∣ d) ∧
    n = d*m ∧ m ∈ B d}.upperDensity ≤ K*c

/-- Split off all prime powers of exponent at least two, without sharing a prime. -/
def H3 : Prop := ∀ n : ℕ, 0 < n →
  ∃ d m : ℕ, 0 < d ∧ n = d*m ∧ d.Coprime m ∧ Squarefree m ∧
    ∀ p : ℕ, p.Prime → p ∣ d → p^2 ∣ d

private theorem upperMono {S T : Set ℕ} (h : S ⊆ T) : S.upperDensity ≤ T.upperDensity := by
  apply Filter.limsup_le_limsup
  · apply Filter.Eventually.of_forall
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Set.ncard_le_ncard
      (Set.inter_subset_inter_left _ (Set.inter_subset_inter_left Set.univ h))
      ((Set.finite_Iio n).subset Set.inter_subset_right)
  · exact isCoboundedUnder_le_of_le atTop (x := (0:ℝ)) (fun _ => by unfold Set.partialDensity; positivity)
  · exact isBoundedUnder_of_eventually_le (a := (1:ℝ))
      (Filter.Eventually.of_forall (fun _ => Set.partialDensity_le_one _ _ _))

theorem main : H1 → H2 → H3 → OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1.H2 := by
  intro square dilate split η hη
  let s : ℝ := max (1/2) (1-η)
  have hs : 0 < s := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (le_max_left _ _)
  have hs' : s < 1 := max_lt (by norm_num) (by linarith)
  obtain ⟨C,hC,est⟩ := square s hs hs'
  obtain ⟨K,hK,hDil⟩ := dilate
  refine ⟨K*C, mul_pos hK hC, ?_⟩
  have pos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  filter_upwards [pos, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))] with ε hε hsmall
  let B (d : ℕ) : Set ℕ :=
    {m | Squarefree m ∧ (tauPlus m : ℝ) < (ε*d.divisors.card)*m.divisors.card}
  have hB (d : ℕ) (hd : 0 < d) :
      (B d).upperDensity ≤ C * ε^s * d.divisors.card := by
    have hd1 : (1:ℝ) ≤ d.divisors.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hd.ne'⟩
    have h := est (ε*d.divisors.card) (mul_pos hε (by linarith))
    rw [Real.mul_rpow hε.le (Nat.cast_nonneg _), ← mul_assoc] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hd1 hs'.le) (by positivity))
  have bound := hDil (C*ε^s) (by positivity) B (fun d hd _ => hB d hd)
  refine (upperMono ?_).trans (bound.trans ?_)
  · intro n hn
    change (tauPlus n : ℝ) < ε * n.divisors.card at hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp [tauPlus] at hn
    obtain ⟨d,m,hd,rfl,hdm,hm,hdf⟩ := split n (Nat.pos_of_ne_zero hn0)
    refine ⟨d,m,hd,hdf,rfl,hm,?_⟩
    have hdiv : m.divisors ⊆ (d*m).divisors := by
      intro a ha
      exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp ha).1.trans (dvd_mul_left _ _),hn0⟩
    have hτ : tauPlus m ≤ tauPlus (d*m) := Finset.card_le_card (Finset.image_subset_image hdiv)
    rw [hdm.card_divisors_mul, Nat.cast_mul, ← mul_assoc] at hn
    exact lt_of_le_of_lt (by exact_mod_cast hτ) hn
  · rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε hsmall.le
      (le_max_right _ _)) (by positivity)

end OMA.R_Erdos448_erdos_448_variants_erdos_tenenbaum_R1_H2_R1
