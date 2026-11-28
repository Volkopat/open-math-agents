import FormalConjectures.ErdosProblems.«542»

/-!
A refinement by multiples reduces the reciprocal-sum problem to bounded
quotients. A near-unit packing inside each parent's multiples retains almost
all its reciprocal weight. Different parents have disjoint descendants.

The first hypothesis follows on paper by iterating Weingartner's family B(x)
(Theorem 2 of arXiv:2310.13038). Its elements exceed the square root of x,
and its reciprocal-weight deficit is O(1/log x). The second hypothesis is the
remaining estimate, with the multiplier cutoff fixed before the limit in n.
-/

namespace OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R2

open Erdos542 Finset Filter
open scoped Topology

/-- At every scale, capture almost unit reciprocal weight near the top of the interval. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K : ℕ, 1 ≤ K ∧ ∀ x : ℕ, 1 ≤ x →
    ∃ B : Finset ℕ, IsLcmFree x B ∧ (∀ b ∈ B, x < K*b) ∧
      1 - η ≤ ∑ b ∈ B, (1 : ℝ) / b

/-- For each fixed cutoff, bound packings whose allowed multipliers are below it. -/
def H2 : Prop :=
  ∀ K : ℕ, 1 ≤ K → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    ∀ A : Finset ℕ, IsLcmFree n A → (∀ a ∈ A, n < K*a) →
      ∑ a ∈ A, (1 : ℝ) / a ≤ 1 + η

/-- Dilating a packing at each parent preserves separation and multiplies weights. -/
theorem refine_packing (n K : ℕ) (η : ℝ) (A : Finset ℕ) (hA : IsLcmFree n A)
    (pack : ∀ x : ℕ, 1 ≤ x → ∃ B : Finset ℕ, IsLcmFree x B ∧
      (∀ b ∈ B, x < K*b) ∧ 1 - η ≤ ∑ b ∈ B, (1 : ℝ) / b) :
    ∃ D : Finset ℕ, IsLcmFree n D ∧ (∀ d ∈ D, n < K*d) ∧
      (1-η) * (∑ a ∈ A, (1 : ℝ)/a) ≤ ∑ d ∈ D, (1 : ℝ)/d := by
  classical
  have pa {a : ℕ} (ha : a ∈ A) : 0 < a := (mem_Icc.mp (hA.1 ha)).1
  have avail (a : ℕ) : ∃ B : Finset ℕ, a ∈ A →
      IsLcmFree (n/a) B ∧ (∀ b ∈ B, n/a < K*b) ∧ 1-η ≤ ∑ b ∈ B, (1 : ℝ)/b := by
    by_cases ha : a ∈ A
    · obtain ⟨B,hB⟩ := pack (n/a) ((Nat.le_div_iff_mul_le (pa ha)).mpr
        (by simpa using (mem_Icc.mp (hA.1 ha)).2))
      exact ⟨B, fun _ => hB⟩
    · exact ⟨∅, fun h => (ha h).elim⟩
  choose B hB using avail
  let fam (a : ℕ) := (B a).image (a*·)
  have bounds {a b : ℕ} (ha : a ∈ A) (hb : b ∈ B a) :
      0 < a*b ∧ a*b ≤ n := by
    have hb' := mem_Icc.mp ((hB a ha).1.1 hb)
    exact ⟨Nat.mul_pos (pa ha) hb'.1, by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le (pa ha)).mp hb'.2⟩
  have distinct {a c z : ℕ} (ha : a ∈ A) (hc : c ∈ A) (hac : a ≠ c)
      (hz : 0 < z) (haz : a ∣ z) (hcz : c ∣ z) : n < z :=
    (hA.2 ha hc hac).trans_le (Nat.le_of_dvd hz (Nat.lcm_dvd haz hcz))
  have disj : (A : Set ℕ).PairwiseDisjoint fam := by
    intro a ha c hc hac
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hz
    obtain ⟨e,_,he⟩ := mem_image.mp hz'
    have bound := bounds ha hb
    exact (Nat.not_lt_of_ge bound.2) (distinct ha hc hac bound.1 ⟨_,rfl⟩ ⟨e,he.symm⟩)
  refine ⟨A.biUnion fam, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro d hd
    obtain ⟨a,ha,hd⟩ := mem_biUnion.mp hd
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr (bounds ha hb)
  · intro d hd e he hde
    obtain ⟨a,ha,hd⟩ := mem_biUnion.mp hd
    obtain ⟨c,hc,he⟩ := mem_biUnion.mp he
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hd
    obtain ⟨t,ht,rfl⟩ := mem_image.mp he
    by_cases h : a = c
    · subst c
      have ht' : b ≠ t := fun hh => hde (by rw [hh])
      have hl := (hB a ha).1.2 hb ht ht'
      rw [Nat.lcm_mul_left]
      simpa [mul_comm] using (Nat.div_lt_iff_lt_mul (pa ha)).mp hl
    · exact distinct ha hc h (Nat.lcm_pos (bounds ha hb).1 (bounds hc ht).1)
        (dvd_trans (dvd_mul_right a b) (Nat.dvd_lcm_left _ _))
        (dvd_trans (dvd_mul_right c t) (Nat.dvd_lcm_right _ _))
  · intro d hd
    obtain ⟨a,ha,hd⟩ := mem_biUnion.mp hd
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hd
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Nat.div_lt_iff_lt_mul (pa ha)).mp ((hB a ha).2.1 b hb)
  · rw [Finset.mul_sum, Finset.sum_biUnion disj]
    apply Finset.sum_le_sum
    intro a ha
    change _ ≤ ∑ d ∈ (B a).image (a*·), (1 : ℝ)/d
    rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (pa ha) h)]
    calc (1-η) * (1/(a:ℝ)) ≤ (∑ b ∈ B a, (1:ℝ)/b) * (1/(a:ℝ)) :=
            mul_le_mul_of_nonneg_right (hB a ha).2.2 (by positivity)
      _ = _ := by simp [Finset.mul_sum, one_div, mul_comm]

theorem main : H1 → H2 → type_of% @Erdos542.erdos_542.variants.one_add_little_o := by
  classical
  intro h1 h2
  let w (A : Finset ℕ) := ∑ a ∈ A, (1 : ℝ)/a
  have best (n : ℕ) : ∃ A : Finset ℕ, IsLcmFree n A ∧
      ∀ B : Finset ℕ, IsLcmFree n B → w B ≤ w A := by
    let F := (Finset.Icc 1 n).powerset.filter (IsLcmFree n)
    have hmem (B : Finset ℕ) : B ∈ F ↔ IsLcmFree n B := by
      simp only [F, mem_filter, mem_powerset]
      exact ⟨And.right, fun h => ⟨h.1,h⟩⟩
    have empty : IsLcmFree n ∅ := by simp [IsLcmFree]
    obtain ⟨A,ha,hm⟩ := F.exists_max_image w ⟨∅,(hmem _).mpr empty⟩
    exact ⟨A,(hmem _).mp ha,fun B hb => hm B ((hmem _).mpr hb)⟩
  choose A hA hmax using best
  refine ⟨fun n => max (w (A n)-1) 0, ?_, ?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε he
    let η := min (ε/8) (1/4)
    have hη : 0 < η := lt_min (by positivity) (by norm_num)
    have hsmall : η ≤ 1/4 := min_le_right _ _
    have heps : η ≤ ε/8 := min_le_left _ _
    obtain ⟨K,hK,hpack⟩ := h1 η hη
    filter_upwards [h2 K hK η hη] with n hn
    obtain ⟨D,hD,hcut,hgain⟩ := refine_packing n K η (A n) (hA n) hpack
    have hd := hn D hD hcut
    change (1-η)*w (A n) ≤ w D at hgain
    change w D ≤ 1+η at hd
    have hb : w (A n) < 1+4*η := by
      by_contra! hh
      have ht := mul_le_mul_of_nonneg_left hh (show 0 ≤ 1-η by linarith)
      nlinarith [mul_nonneg hη.le (show 0 ≤ 1-4*η by linarith)]
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
    exact max_lt (by linarith) he
  · intro n B hB
    have hb := hmax n B hB
    change w B ≤ _
    linarith [le_max_left (w (A n)-1) 0]

end OMA.R_Erdos542_erdos_542_variants_one_add_little_o_R2
