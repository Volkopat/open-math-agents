import FormalConjectures.GreensOpenProblems.«40»

-- Credit: @Pixelstorm44
/-!
A radius-(s+1) cover must repair every vertex missed by the exact outer
shells using its radius-s interiors. Count these repairs before taking
either limit. H1 asks only for shell deficits above every fixed multiple
of the inverse dimension, allowing the uncovered fraction to tend to zero.
The one-ball volume estimate H2 is proved below by counting binary supports.
-/

namespace OMA.R_Green40_green_40_variants_arbitrary_subsets_R2

open Filter Topology Green40
open scoped Pointwise ENNReal

/-- At bounded density, exact shells must miss more than A/n of the cube
in sufficiently high dimensions. The dimension threshold may depend on A. -/
def H1 : Prop :=
  ∀ K : ℕ, ∀ᶠ s : ℕ in atTop, ∀ A : ℕ, ∀ᶠ n : ℕ in atTop,
    ∀ C : Finset (𝔽₂ n), C.card * n.choose (s+1) ≤ K * 2^n →
      A * 2^n < n * (Finset.univ \ (C + Finset.univ.filter (fun x : 𝔽₂ n => hammingNorm x = s+1))).card

/-- For each fixed radius the interior costs at most 2(s+1)/n of the ball. -/
def H2 : Prop :=
  ∀ s : ℕ, ∀ᶠ n : ℕ in atTop,
    n * (hammingBallFinset n s).card ≤ 2 * (s+1) * (hammingBallFinset n (s+1)).card

theorem repair (n s : ℕ) (C : Finset (𝔽₂ n)) (hc : IsCoveringFinset n (s+1) C) :
    (Finset.univ \ (C + Finset.univ.filter (fun x : 𝔽₂ n => hammingNorm x = s+1))).card ≤ C.card * (hammingBallFinset n s).card := by
  classical
  refine (Finset.card_le_card (show (Finset.univ \ (C + Finset.univ.filter (fun x : 𝔽₂ n => hammingNorm x = s+1))) ⊆ C + hammingBallFinset n s from ?_)).trans
    Finset.card_add_le
  intro x hx
  have hmiss := (Finset.mem_sdiff.mp hx).2
  have hcover : x ∈ C + hammingBallFinset n (s+1) := hc ▸ Finset.mem_univ x
  obtain ⟨c, hC, e, he, hce⟩ := Finset.mem_add.mp hcover
  have hle : hammingNorm e ≤ s+1 := (Finset.mem_filter.mp he).2
  have hne : hammingNorm e ≠ s+1 := fun h =>
    hmiss (Finset.mem_add.mpr ⟨c, hC, e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, hce⟩)
  exact Finset.mem_add.mpr ⟨c, hC, e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, hce⟩

theorem ballCard (n r : ℕ) : Nat.card (hammingBall n r) = (hammingBallFinset n r).card := by
  have h : hammingBall n r = ↑(hammingBallFinset n r) := by
    ext x
    simp [hammingBall, hammingBallFinset]
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem weight_count (n k : ℕ) :
    (Finset.univ.filter (fun x : 𝔽₂ n => hammingNorm x = k)).card = n.choose k := by
  classical
  let supp (x : 𝔽₂ n) := Finset.univ.filter (fun i => x i ≠ 0)
  have hc : ((Finset.univ : Finset (Fin n)).powersetCard k).card = n.choose k := by
    simp [Finset.card_powersetCard]
  rw [← hc]
  apply Finset.card_bij (fun x _ => supp x)
  · intro x hx
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy he
    funext i
    have hm : i ∈ supp x ↔ i ∈ supp y := he ▸ Iff.rfl
    have hb : x i ≠ 0 ↔ y i ≠ 0 := by simpa [supp] using hm
    exact (by decide : ∀ a b : ZMod 2, (a ≠ 0 ↔ b ≠ 0) → a = b) _ _ hb
  · intro t ht
    let x : 𝔽₂ n := fun i => if i ∈ t then 1 else 0
    have he : supp x = t := by ext i; simp [supp, x]
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
    change (supp x).card = k
    rw [he, (Finset.mem_powersetCard.mp ht).2]

private theorem ball_count (n s : ℕ) :
    (hammingBallFinset n s).card = ∑ i ∈ Finset.range (s+1), n.choose i := by
  induction s with
  | zero =>
    simpa [hammingBallFinset] using weight_count n 0
  | succ s ih =>
    rw [Finset.sum_range_succ, ← ih, ← weight_count]
    have hu : hammingBallFinset n (s+1) = hammingBallFinset n s ∪
        Finset.univ.filter (fun x : 𝔽₂ n => hammingNorm x = s+1) := by
      ext x
      simp only [hammingBallFinset, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and]
      omega
    rw [hu, Finset.card_union_of_disjoint]
    apply Finset.disjoint_left.mpr
    intro x hl hr
    have hl' : hammingNorm x ≤ s := (Finset.mem_filter.mp hl).2
    have hr' : hammingNorm x = s+1 := (Finset.mem_filter.mp hr).2
    omega

theorem interior_estimate (n s : ℕ) (hn : 2*s ≤ n) :
    n * (hammingBallFinset n s).card ≤ 2*(s+1)*(hammingBallFinset n (s+1)).card := by
  rw [ball_count, ball_count, Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range (s+1), 2*(s+1)*n.choose (k+1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hks : k ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      calc
        n * n.choose k ≤ (2*(n-k)) * n.choose k := Nat.mul_le_mul_right _ (by omega)
        _ = 2*(k+1)*n.choose (k+1) := by
          have h := Nat.choose_succ_right_eq n k
          nlinarith
        _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_range_succ' (fun k => n.choose k)]
      simp


/-- The volume hypothesis follows from adjacent binomial coefficients. -/
theorem interior_proved : H2 := fun s =>
  eventually_atTop.mpr ⟨2*s, fun n hn => interior_estimate n s hn⟩

theorem main : H1 → H2 → type_of% @Green40.green_40.variants.arbitrary_subsets := by
  intro hShell hInterior
  apply ENNReal.tendsto_nhds_top_iff_nat.mpr
  intro k
  let K := k + 1
  obtain ⟨S, hS⟩ := eventually_atTop.mp (hShell K)
  apply eventually_atTop.mpr
  refine ⟨S+1, fun r hr => ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show r ≠ 0 by omega)
  have hgap := hS s (by omega) (2 * (s+1) * K)
  have hdens : ∀ᶠ n : ℕ in atTop, (K : ℝ≥0∞) ≤ minDensityFinset n (s+1) := by
    filter_upwards [hgap, hInterior s] with n hg hi
    refine le_iInf₂ fun C hc => ?_
    have hcost : K * 2^n ≤ C.card * (hammingBallFinset n (s+1)).card := by
      by_contra! hcheap
      have hsize : n.choose (s+1) ≤ (hammingBallFinset n (s+1)).card := by
        rw [ball_count, Finset.sum_range_succ]
        omega
      have lower := hg C ((Nat.mul_le_mul_left _ hsize).trans hcheap.le)
      have upper : n * (Finset.univ \ (C + Finset.univ.filter (fun x : 𝔽₂ n => hammingNorm x = s+1))).card ≤ 2 * (s+1) * K * 2^n := calc
        _ ≤ n * (C.card * (hammingBallFinset n s).card) := Nat.mul_le_mul_left _ (repair n s C hc)
        _ = C.card * (n * (hammingBallFinset n s).card) := by ring
        _ ≤ C.card * (2 * (s+1) * (hammingBallFinset n (s+1)).card) := Nat.mul_le_mul_left _ hi
        _ = 2 * (s+1) * (C.card * (hammingBallFinset n (s+1)).card) := by ring
        _ ≤ 2 * (s+1) * (K * 2^n) := Nat.mul_le_mul_left _ hcheap.le
        _ = _ := by ring
      exact lower.not_ge upper
    rw [ballCard, ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
    exact_mod_cast hcost
  have hk : (k : ℝ≥0∞) < (K : ℝ≥0∞) := by exact_mod_cast Nat.lt_succ_self k
  exact hk.trans_le (le_liminf_of_le (by isBoundedDefault) hdens)

/-- Thus the exact-shell obstruction alone suffices. -/
theorem shell_criterion (h : H1) : type_of% @Green40.green_40.variants.arbitrary_subsets :=
  main h interior_proved

end OMA.R_Green40_green_40_variants_arbitrary_subsets_R2
