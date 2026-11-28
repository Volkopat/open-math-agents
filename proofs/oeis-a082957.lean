import OMAStatements.S_oeis_a082957

-- Source module Analysis.lean

namespace A082957Analysis

open Finset Filter Asymptotics
open scoped BigOperators Topology

noncomputable def frequency (P : ℕ → Prop) (N : ℕ) : ℝ := by
  classical
  exact ((range N).filter P).card / (N : ℝ)

theorem frequency_eq_count (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    frequency P N = (Nat.count P N : ℝ) / N := by
  classical
  rw [frequency, Nat.count_eq_card_filter_range]
  apply congrArg (fun s : Finset ℕ => (s.card : ℝ) / N)
  exact filter_congr_decidable _ _ _

theorem frequency_nonneg (P : ℕ → Prop) (N : ℕ) : 0 ≤ frequency P N := by
  unfold frequency
  positivity

theorem frequency_add_le_one_of_disjoint {P Q : ℕ → Prop}
    (h : ∀ n, P n → ¬ Q n) (N : ℕ) :
    frequency P N + frequency Q N ≤ 1 := by
  classical
  by_cases hN : N = 0
  · simp [hN, frequency]
  have hDisj : Disjoint ((range N).filter P) ((range N).filter Q) := by
    rw [Finset.disjoint_left]
    exact fun n hp hq => h n (mem_filter.mp hp).2 (mem_filter.mp hq).2
  have hSub : (range N).filter P ∪ (range N).filter Q ⊆ range N := by
    exact union_subset (filter_subset _ _) (filter_subset _ _)
  have hC := card_le_card hSub
  rw [card_union_of_disjoint hDisj, card_range] at hC
  have hNR : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  unfold frequency
  rw [← add_div, div_le_iff₀ hNR, one_mul]
  exact_mod_cast hC

theorem frequency_le_union {P Q R : ℕ → Prop} (h : ∀ n, P n → Q n ∨ R n) (N : ℕ) :
    frequency P N ≤ frequency Q N + frequency R N := by
  classical
  have hsub : (range N).filter P ⊆ (range N).filter Q ∪ (range N).filter R := by
    intro n hn
    obtain ⟨hn, hp⟩ := mem_filter.mp hn
    rcases h n hp with hq | hr
    · exact mem_union_left _ (mem_filter.mpr ⟨hn, hq⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hn, hr⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  unfold frequency
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)

theorem frequency_abs_sub_le {P Q E : ℕ → Prop} (h : ∀ n, ¬ E n → (P n ↔ Q n))
    (N : ℕ) : |frequency P N - frequency Q N| ≤ frequency E N := by
  have hp := frequency_le_union (P := P) (Q := Q) (R := E) (fun n hp => by
    by_cases he : E n
    · exact Or.inr he
    · exact Or.inl ((h n he).mp hp)) N
  have hq := frequency_le_union (P := Q) (Q := P) (R := E) (fun n hq => by
    by_cases he : E n
    · exact Or.inr he
    · exact Or.inl ((h n he).mpr hq)) N
  rw [abs_le]
  constructor <;> linarith

theorem frequency_markov {P : ℕ → Prop} (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (ε : ℝ) (hε : 0 < ε) (he : ∀ n, P n → ε ≤ f n) (N : ℕ) :
    frequency P N ≤ (∑ n ∈ range N, f n) / (ε * N) := by
  classical
  let event := (range N).filter P
  have h : ε * (event.card : ℝ) ≤ ∑ n ∈ range N, f n := by
    calc
      _ = ∑ _n ∈ event, ε := by rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ n ∈ event, f n :=
        sum_le_sum (fun n hn => he n (mem_filter.mp hn).2)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n _ _ => hf n)
  unfold frequency
  have h' : ((event.card : ℕ) : ℝ) ≤ (∑ n ∈ range N, f n) / ε :=
    (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using h)
  simpa only [div_div] using div_le_div_of_nonneg_right h' (Nat.cast_nonneg (α := ℝ) N)

theorem const_div_nat_zero (c : ℝ) :
    Tendsto (fun n : ℕ => c / n) atTop (𝓝 0) := by
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
  simpa only [div_eq_mul_inv, mul_zero] using hc.mul hInv

private theorem frequency_of_finite {P : ℕ → Prop} (hfinite : (Set.ofPred P).Finite) :
    Tendsto (frequency P) atTop (𝓝 0) := by
  classical
  refine squeeze_zero (frequency_nonneg P) ?_ (const_div_nat_zero hfinite.toFinset.card)
  intro n
  have hs : (range n).filter P ⊆ hfinite.toFinset := by
    intro k hk
    exact hfinite.mem_toFinset.mpr (mem_filter.mp hk).2
  unfold frequency
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hs) (by positivity)

theorem frequency_of_eventually_not {P : ℕ → Prop} (hP : ∀ᶠ n in atTop, ¬ P n) :
    Tendsto (frequency P) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.mp hP
  refine frequency_of_finite (Set.Finite.subset (Set.finite_lt_nat K) ?_)
  intro n hn
  exact lt_of_not_ge (fun h => hK n h hn)

theorem frequency_periodic (P : ℕ → Prop) [DecidablePred P] (M : ℕ) (hM : 0 < M)
    (period : ∀ n, P (n + M) ↔ P n) :
    Tendsto (frequency P) atTop (𝓝 (frequency P M)) := by
  have hShift (n q : ℕ) : P (n + M * q) ↔ P n := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, period, ih]
  have hBlock (q : ℕ) : Nat.count P (M * q) = q * Nat.count P M := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Nat.count_add, ih, Nat.succ_mul]
      congr 1
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      apply congrArg Finset.card
      apply filter_congr
      intro n hn
      simpa only [Nat.add_comm] using hShift n q
  have hCard (N : ℕ) : Nat.count P N = N / M * Nat.count P M + Nat.count P (N % M) := by
    nth_rw 1 [← Nat.div_add_mod N M]
    rw [Nat.count_add, hBlock]
    congr 1
    rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    apply filter_congr
    intro n hn
    simpa only [Nat.add_comm] using hShift n (N / M)
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_
    (const_div_nat_zero (M : ℝ))
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hmlo : 0 ≤ frequency P M := frequency_nonneg _ _
  have hmhi : frequency P M ≤ 1 := by
    rw [frequency_eq_count, div_le_iff₀ hMR, one_mul]
    exact_mod_cast (Nat.count_le (p := P) (n := M))
  have hMul : frequency P M * (M : ℝ) = (Nat.count P M : ℝ) := by
    rw [frequency_eq_count, div_mul_cancel₀ _ hMR.ne']
  have hNat := congrArg (fun k : ℕ => (k : ℝ)) (Nat.div_add_mod n M)
  have hC := congrArg (fun k : ℕ => (k : ℝ)) (hCard n)
  push_cast at hNat hC
  have hDiff : frequency P n - frequency P M =
      ((Nat.count P (n % M) : ℝ) - frequency P M * ((n % M : ℕ) : ℝ)) / n := by
    apply (eq_div_iff hnR.ne').mpr
    rw [sub_mul, frequency_eq_count P n, div_mul_cancel₀ _ hnR.ne']
    nlinarith [congrArg (fun r : ℝ => frequency P M * r) hNat,
      congrArg (fun r : ℝ => ((n / M : ℕ) : ℝ) * r) hMul]
  have hCount : (Nat.count P (n % M) : ℝ) ≤ ((n % M : ℕ) : ℝ) := by
    exact_mod_cast (Nat.count_le (p := P) (n := n % M))
  have hMul0 := mul_nonneg hmlo (Nat.cast_nonneg (α := ℝ) (n % M))
  have hMul1 := mul_le_of_le_one_left (Nat.cast_nonneg (α := ℝ) (n % M)) hmhi
  rw [Real.dist_eq, hDiff, abs_div, abs_of_pos hnR]
  apply div_le_div_of_nonneg_right _ hnR.le
  have hRem : ((n % M : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.mod_lt n hM).le
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (n % M))]

theorem enumeration_growth {P : ℕ → Prop} {δ : ℝ} (hδ : 0 < δ)
    (hDensity : Tendsto (frequency P) atTop (𝓝 δ)) :
    (fun n : ℕ => (Nat.nth P (n - 1) : ℝ)) ~[atTop] fun n : ℕ => δ⁻¹ * n := by
  classical
  have hInfinite : (Set.ofPred P).Infinite := by
    intro hFinite
    exact hδ.ne' (tendsto_nhds_unique hDensity (frequency_of_finite hFinite))
  have hNth : Tendsto (Nat.nth P) atTop atTop := (Nat.nth_strictMono hInfinite).tendsto_atTop
  have hIndex : Tendsto (fun n : ℕ => Nat.nth P (n - 1) + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (hNth.comp (tendsto_sub_atTop_nat 1))
  have hRatio : Tendsto (fun n : ℕ => (n : ℝ) / ((Nat.nth P (n - 1) : ℝ) + 1))
      atTop (𝓝 δ) := by
    refine (hDensity.comp hIndex).congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    change frequency P (Nat.nth P (n - 1) + 1) = _
    rw [frequency_eq_count, Nat.count_nth_succ_of_infinite hInfinite,
      show n - 1 + 1 = n by omega, Nat.cast_succ]
  have hInv : Tendsto (fun n : ℕ => ((Nat.nth P (n - 1) : ℝ) + 1) / n)
      atTop (𝓝 δ⁻¹) := by
    simpa only [inv_div] using hRatio.inv₀ hδ.ne'
  have hGrowth : Tendsto (fun n : ℕ => (Nat.nth P (n - 1) : ℝ) / n)
      atTop (𝓝 δ⁻¹) := by
    have h := hInv.sub (const_div_nat_zero 1)
    simp only [sub_zero, add_div, add_sub_cancel_right] at h
    exact h
  apply isEquivalent_of_tendsto_one
  have h := hGrowth.div_const (δ⁻¹)
  rw [div_self (inv_ne_zero hδ.ne')] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  change (Nat.nth P (n - 1) : ℝ) / n / δ⁻¹ = (Nat.nth P (n - 1) : ℝ) / (δ⁻¹ * n)
  rw [div_div, mul_comm (n : ℝ)]

theorem growth_from_density_bounds {P : ℕ → Prop} {δ : ℝ}
    (hDensity : Tendsto (frequency P) atTop (𝓝 δ))
    (hLower : 2 / 37 < δ) (hUpper : δ < 1 / 18) :
    ∃ c : ℝ, 18 < c ∧ c < 18.5 ∧
      (fun n : ℕ => (Nat.nth P (n - 1) : ℝ)) ~[atTop] fun n : ℕ => c * n := by
  have hδ : 0 < δ := lt_trans (by norm_num) hLower
  refine ⟨δ⁻¹, ?_, ?_, enumeration_growth hδ hDensity⟩
  · rw [← one_div, lt_div_iff₀ hδ]
    linarith
  · rw [← one_div, div_lt_iff₀ hδ]
    linarith

theorem density_of_frequency_approximation (P : ℕ → Prop)
    (hApprox : ∀ η > 0, ∃ (Q : ℕ → Prop) (l : ℝ),
      Tendsto (frequency Q) atTop (𝓝 l) ∧
        ∀ᶠ N in atTop, |frequency P N - frequency Q N| ≤ η) :
    ∃ δ, Tendsto (frequency P) atTop (𝓝 δ) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨Q, l, hlim, h⟩ := hApprox (ε / 5) (by positivity)
  have hClose : ∀ᶠ n in atTop, dist (frequency P n) l < 2 * (ε / 5) := by
    filter_upwards [h, Metric.tendsto_nhds.mp hlim (ε / 5) (by positivity)] with n h₁ h₂
    calc
      _ ≤ dist (frequency P n) (frequency Q n) + dist (frequency Q n) l := dist_triangle _ _ _
      _ < _ := by
        simp only [Real.dist_eq] at h₂ ⊢
        linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp hClose
  refine ⟨M, fun m hm n hn => ?_⟩
  calc
    _ ≤ dist _ l + dist l _ := dist_triangle _ _ _
    _ < _ := by
      rw [dist_comm l]
      linarith [hM m hm, hM n hn]

theorem density_of_approximation (full : ℕ → ℝ) (small : ℕ → ℕ → ℝ) (threshold : ℕ → ℝ)
    (hThreshold : Tendsto threshold atTop (𝓝 0))
    (hFinite : ∀ Y, ∃ l, Tendsto (frequency (fun n => 0 < small Y n)) atTop (𝓝 l))
    (hTail : ∀ ε > 0, ∀ η > 0, ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
      ∀ᶠ N in atTop, frequency (fun n => ε ≤ |full n - small Y n|) N ≤ η)
    (hMargin : ∀ η > 0, ∃ ε > 0, ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
      ∀ᶠ N in atTop, frequency (fun n => |small Y n| ≤ 2 * ε) N ≤ η) :
    ∃ δ, Tendsto (frequency (fun n => threshold n < full n)) atTop (𝓝 δ) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro tolerance hTolerance
  let η := tolerance / 9
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ε, hε, Y₁, hY₁⟩ := hMargin η hη
  obtain ⟨Y₂, hY₂⟩ := hTail ε hε η hη
  let Y := max Y₁ Y₂
  let margin : ℕ → Prop := fun n => |small Y n| ≤ 2 * ε
  let error : ℕ → Prop := fun n => ε ≤ |full n - small Y n|
  let early : ℕ → Prop := fun n => ε ≤ |threshold n|
  let bad : ℕ → Prop := fun n => margin n ∨ error n ∨ early n
  have hmargin := hY₁ Y (le_max_left _ _)
  have herror := hY₂ Y (le_max_right _ _)
  have hEarly : Tendsto (frequency early) atTop (𝓝 0) := by
    apply frequency_of_eventually_not
    filter_upwards [(Metric.tendsto_nhds.mp hThreshold ε hε)] with n hn
    simpa [early, Real.dist_eq] using hn
  have hearly := hEarly.eventually_lt (tendsto_const_nhds (x := η)) hη
  obtain ⟨l, hl⟩ := hFinite Y
  have hl' := Metric.tendsto_nhds.mp hl η hη
  have hGood (n : ℕ) (hn : ¬ bad n) : (threshold n < full n) ↔ (0 < small Y n) := by
    have hm : 2 * ε < |small Y n| := lt_of_not_ge (fun h => hn (Or.inl h))
    have he : |full n - small Y n| < ε := lt_of_not_ge (fun h => hn (Or.inr (Or.inl h)))
    have ht : |threshold n| < ε := lt_of_not_ge (fun h => hn (Or.inr (Or.inr h)))
    rw [abs_lt] at he ht
    by_cases hs : 0 < small Y n
    · rw [abs_of_pos hs] at hm
      exact iff_of_true (by linarith [he.1, ht.2]) hs
    · rw [abs_of_nonpos (le_of_not_gt hs)] at hm
      exact iff_of_false (by linarith [he.2, ht.1]) hs
  have hClose : ∀ᶠ N in atTop,
      dist (frequency (fun n => threshold n < full n) N) l < 4 * η := by
    filter_upwards [hmargin, herror, hearly, hl'] with N hM hE hT hL
    have hB := frequency_le_union (P := bad) (Q := margin) (R := fun n => error n ∨ early n)
      (fun _ h => h) N
    have hB' := frequency_le_union (P := fun n => error n ∨ early n) (Q := error) (R := early)
      (fun _ h => h) N
    have hD := frequency_abs_sub_le hGood N
    calc
      _ ≤ dist _ (frequency (fun n => 0 < small Y n) N) +
          dist (frequency (fun n => 0 < small Y n) N) l := dist_triangle _ _ _
      _ < 4 * η := by
        simp only [Real.dist_eq] at hL ⊢
        change frequency margin N ≤ η at hM
        change frequency error N ≤ η at hE
        linarith
  obtain ⟨M, hM⟩ := eventually_atTop.mp hClose
  refine ⟨M, fun m hm n hn => ?_⟩
  calc
    _ ≤ dist _ l + dist l _ := dist_triangle _ _ _
    _ < tolerance := by
      rw [dist_comm l]
      have h₁ := hM m hm
      have h₂ := hM n hn
      dsimp [η] at h₁ h₂
      linarith

end A082957Analysis

-- Source module Tail.lean

namespace A082957Tail

open Finset Filter
open scoped BigOperators Topology

def primesThrough (Y : ℕ) : Finset ℕ := (range (Y + 1)).filter Nat.Prime

noncomputable def small (term : ℕ → ℕ → ℝ) (Y n : ℕ) : ℝ :=
  ∑ p ∈ primesThrough Y, term p n

noncomputable def full (term : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  small term (2 * n + 1) n

noncomputable def majorant (p r n : ℕ) : ℝ :=
  if p ∣ 2 * n + r then 1 / ((p : ℝ) - 1) else 0

private def tailPrimes (Y N : ℕ) : Finset ℕ :=
  (range (2 * N + 2)).filter fun p => p.Prime ∧ Y < p

private theorem affine_count_le (p r N : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    ((range N).filter (fun n => p ∣ 2 * n + r)).card ≤ N / p + 1 := by
  rw [← card_range (N / p + 1)]
  apply card_le_card_of_injOn (fun n => n / p)
  · intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right
      ((mem_range.mp (mem_filter.mp hn).1).le)))
  · have hs : ∀ a b : ℕ, a ≤ b → p ∣ 2 * a + r → p ∣ 2 * b + r → a / p = b / p → a = b := by
      intro a b hab ha hb hq
      have hd := Nat.dvd_sub hb ha
      have hd' : p ∣ 2 * (b - a) := by
        rwa [show (2 * b + r) - (2 * a + r) = 2 * (b - a) by omega] at hd
      have hpnot : ¬p ∣ 2 := fun h => (Nat.not_le_of_gt hp2) (Nat.le_of_dvd (by decide) h)
      have hdab := (hp.dvd_mul.mp hd').resolve_left hpnot
      by_contra! hne
      have hpos : 0 < b - a := by omega
      have hbig := Nat.le_of_dvd hpos hdab
      have ha' := Nat.mod_add_div a p
      have hb' := Nat.mod_add_div b p
      rw [hq] at ha'
      have hsmall := Nat.mod_lt b hp.pos
      omega
    intro a ha b hb hq
    obtain h | h := le_total a b
    · exact hs a b h (mem_filter.mp ha).2 (mem_filter.mp hb).2 hq
    · exact (hs b a h (mem_filter.mp hb).2 (mem_filter.mp ha).2 hq.symm).symm

private theorem reciprocal_tail (Y N : ℕ) (hY : 0 < Y) (hYN : Y ≤ N) :
    ∑ p ∈ tailPrimes Y N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 / (Y : ℝ) := by
  have hs : tailPrimes Y N ⊆ Ico (Y + 1) (2 * N + 2) := by
    intro p hp
    simp only [tailPrimes, mem_filter, mem_range, mem_Ico] at hp ⊢
    omega
  refine (sum_le_sum_of_subset_of_nonneg hs ?_).trans ?_
  · intro p hp _
    have hpR : (2 : ℝ) ≤ p := by
      exact_mod_cast (show 2 ≤ p by have := (mem_Ico.mp hp).1; omega)
    exact div_nonneg zero_le_one (by nlinarith)
  have hweight (p : ℕ) (hp : p ∈ Ico (Y + 1) (2 * N + 2)) :
      (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) =
        1 / ((p : ℝ) - 1) - 1 / (p : ℝ) := by
    have hpR : (2 : ℝ) ≤ p := by
      exact_mod_cast (show 2 ≤ p by have := (mem_Ico.mp hp).1; omega)
    have h0 : (p : ℝ) ≠ 0 := by linarith
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [sum_congr rfl hweight, sum_Ico_eq_sum_range]
  have hShift (j : ℕ) :
      (1 : ℝ) / (((Y + 1 + j : ℕ) : ℝ) - 1) - 1 / ((Y + 1 + j : ℕ) : ℝ) =
        1 / ((Y : ℝ) + j) - 1 / ((Y : ℝ) + (j + 1 : ℕ)) := by
    push_cast
    ring_nf
  simp_rw [hShift]
  rw [sum_range_sub']
  simp only [Nat.cast_zero, add_zero]
  apply sub_le_self
  positivity

theorem correction_le (s : Finset ℕ) (N K : ℕ) (hK : 0 < K)
    (hS : ∀ p ∈ s, 2 ≤ p ∧ p < 2 * N + 2) :
    ∑ p ∈ s, (1 : ℝ) / ((p : ℝ) - 1) ≤ (K : ℝ) + 1 + (2 * (N : ℝ) + 2) / K := by
  have hPoint (p : ℕ) (hp : p ∈ s) :
      (1 : ℝ) / ((p : ℝ) - 1) ≤ if p ≤ K then 1 else 1 / (K : ℝ) := by
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (hS p hp).1
    by_cases hpK : p ≤ K
    · rw [if_pos hpK, div_le_iff₀ (by linarith : (0 : ℝ) < (p : ℝ) - 1), one_mul]
      linarith
    · rw [if_neg hpK]
      apply one_div_le_one_div_of_le (by exact_mod_cast hK : (0 : ℝ) < K)
      have hKR : (K : ℝ) + 1 ≤ p := by exact_mod_cast (show K + 1 ≤ p by omega)
      linarith
  have hCounts₁ : ((s.filter (fun p => p ≤ K)).card : ℝ) ≤ K + 1 := by
    have hs : s.filter (fun p => p ≤ K) ⊆ range (K + 1) := by
      intro p hp
      exact mem_range.mpr (Nat.lt_succ_of_le ((mem_filter.mp hp).2))
    have hc := card_le_card hs
    rw [card_range] at hc
    exact_mod_cast hc
  have hCounts₂ : ((s.filter (fun p => ¬ p ≤ K)).card : ℝ) ≤ 2 * (N : ℝ) + 2 := by
    have hs : s.filter (fun p => ¬ p ≤ K) ⊆ range (2 * N + 2) :=
      fun p hp => mem_range.mpr (hS p (mem_filter.mp hp).1).2
    have hc := card_le_card hs
    rw [card_range] at hc
    exact_mod_cast hc
  refine (sum_le_sum hPoint).trans ?_
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one_div]
  exact add_le_add hCounts₁ (div_le_div_of_nonneg_right hCounts₂ (by positivity))

theorem correction_tendsto (s : ℕ → Finset ℕ)
    (hS : ∀ N p, p ∈ s N → 2 ≤ p ∧ p < 2 * N + 2) :
    Tendsto (fun N : ℕ => (∑ p ∈ s N, (1 : ℝ) / ((p : ℝ) - 1)) / N) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (8 / ε)
  have hKR : (0 : ℝ) < K := lt_trans (by positivity) hK
  have hKnat : 0 < K := by exact_mod_cast hKR
  obtain ⟨J, hJ⟩ := exists_nat_gt (2 * ((K : ℝ) + 1) / ε)
  filter_upwards [eventually_ge_atTop (max J 1)] with N hN
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast ((le_max_right J 1).trans hN)
  have hJ' : (J : ℝ) ≤ N := by exact_mod_cast ((le_max_left J 1).trans hN)
  have hN0 : (0 : ℝ) < N := by linarith
  have hMake₁ : (K : ℝ) + 1 < (N : ℝ) * (ε / 2) := by
    have h := (div_lt_iff₀ hε).mp (hJ.trans_le hJ')
    linarith
  have hMake₂ : (2 * (N : ℝ) + 2) / (K : ℝ) < (N : ℝ) * (ε / 2) := by
    have h := (div_lt_iff₀ hε).mp hK
    apply (div_lt_iff₀ hKR).mpr
    nlinarith [mul_pos (sub_pos.mpr h) hN0]
  have hNonneg : 0 ≤ (∑ p ∈ s N, (1 : ℝ) / ((p : ℝ) - 1)) / N := by
    apply div_nonneg _ hN0.le
    apply sum_nonneg
    intro p hp
    have hpR : (2 : ℝ) ≤ p := by exact_mod_cast (hS N p hp).1
    exact div_nonneg zero_le_one (by linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hNonneg, div_lt_iff₀ hN0]
  linarith [correction_le (s N) N K hKnat (hS N)]

private theorem mean_majorant_le (Y N r : ℕ) (hY : 2 ≤ Y) (hYN : Y ≤ N) :
    ∑ n ∈ range N, ∑ p ∈ tailPrimes Y N, majorant p r n ≤
      (N : ℝ) / Y + ∑ p ∈ tailPrimes Y N, (1 : ℝ) / ((p : ℝ) - 1) := by
  rw [sum_comm]
  have hPoint (p : ℕ) (hp : p ∈ tailPrimes Y N) :
      ∑ n ∈ range N, majorant p r n ≤
        (N : ℝ) * (1 / ((p : ℝ) * ((p : ℝ) - 1))) + 1 / ((p : ℝ) - 1) := by
    have hprime := (mem_filter.mp hp).2.1
    have hp2 : 2 < p := hY.trans_lt (mem_filter.mp hp).2.2
    have hpR : (2 : ℝ) < p := by exact_mod_cast hp2
    have hpR0 : (p : ℝ) ≠ 0 := by linarith
    have hpR1 : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [show (∑ n ∈ range N, majorant p r n) =
      (((range N).filter (fun n => p ∣ 2 * n + r)).card : ℝ) * (1 / ((p : ℝ) - 1)) by
        unfold majorant
        rw [← sum_filter, sum_const, nsmul_eq_mul]]
    have hC : (((range N).filter (fun n => p ∣ 2 * n + r)).card : ℝ) ≤ (N : ℝ) / p + 1 := by
      have hC₁ : (((range N).filter (fun n => p ∣ 2 * n + r)).card : ℝ) ≤
          ((N / p : ℕ) : ℝ) + 1 := by exact_mod_cast affine_count_le p r N hprime hp2
      have hC₂ : ((N / p : ℕ) : ℝ) ≤ (N : ℝ) / p :=
        (le_div_iff₀ (by linarith)).mpr (by exact_mod_cast Nat.div_mul_le_self N p)
      linarith
    refine (mul_le_mul_of_nonneg_right hC (div_nonneg zero_le_one (by linarith))).trans ?_
    apply le_of_eq
    field_simp
  refine (sum_le_sum hPoint).trans ?_
  rw [sum_add_distrib, ← mul_sum]
  exact add_le_add
    (by simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (reciprocal_tail Y N (by omega) hYN) (Nat.cast_nonneg N))
    le_rfl

private theorem tail_point (term : ℕ → ℕ → ℝ)
    (hBound : ∀ p n, p.Prime → 2 < p → |term p n| ≤ majorant p 0 n + majorant p 1 n)
    (hZero : ∀ p n, p.Prime → 2 * n + 1 < p → term p n = 0)
    {Y N n : ℕ} (hY : 2 ≤ Y) (hYN : Y ≤ N) (hn : n < N) :
    |full term n - small term Y n| ≤
      ∑ p ∈ tailPrimes Y N, (majorant p 0 n + majorant p 1 n) := by
  have hfullsubset : primesThrough (2 * n + 1) ⊆ primesThrough (2 * N + 1) := by
    intro p hp
    simp only [primesThrough, mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsmallsubset : primesThrough Y ⊆ primesThrough (2 * N + 1) := by
    intro p hp
    simp only [primesThrough, mem_filter, mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hs := sum_subset hfullsubset (f := fun p => term p n) (fun p hp hpnot =>
    hZero p n (mem_filter.mp hp).2 (by
      simp only [primesThrough, mem_filter, mem_range, (mem_filter.mp hp).2, and_true,
        not_lt] at hpnot
      omega))
  have ht : primesThrough (2 * N + 1) \ primesThrough Y = tailPrimes Y N := by
    ext p
    simp only [primesThrough, tailPrimes, Finset.mem_sdiff, mem_filter, mem_range]
    by_cases h : p.Prime <;> simp [h] <;> omega
  unfold full small
  rw [hs, ← sum_sdiff hsmallsubset, add_sub_cancel_right, ht]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun p hp =>
    hBound p n (mem_filter.mp hp).2.1 (hY.trans_lt (mem_filter.mp hp).2.2)))

theorem raw_tail_bound (term : ℕ → ℕ → ℝ)
    (hBound : ∀ p n, p.Prime → 2 < p → |term p n| ≤ majorant p 0 n + majorant p 1 n)
    (hZero : ∀ p n, p.Prime → 2 * n + 1 < p → term p n = 0)
    (Y N : ℕ) (hY : 2 ≤ Y) (hYN : Y ≤ N) :
    ∑ n ∈ range N, |full term n - small term Y n| ≤
      2 * ((N : ℝ) / Y + ∑ p ∈ tailPrimes Y N, (1 : ℝ) / ((p : ℝ) - 1)) := by
  refine (sum_le_sum (fun n hn => tail_point term hBound hZero hY hYN (mem_range.mp hn))).trans ?_
  simp only [sum_add_distrib]
  linarith [mean_majorant_le Y N 0 hY hYN, mean_majorant_le Y N 1 hY hYN]

theorem uniform_tail (term : ℕ → ℕ → ℝ)
    (hBound : ∀ p n, p.Prime → 2 < p → |term p n| ≤ majorant p 0 n + majorant p 1 n)
    (hZero : ∀ p n, p.Prime → 2 * n + 1 < p → term p n = 0) :
    ∀ ε > 0, ∀ η > 0, ∃ Y₀ : ℕ, ∀ Y ≥ Y₀, ∀ᶠ N in atTop,
      A082957Analysis.frequency (fun n => ε ≤ |full term n - small term Y n|) N ≤ η := by
  intro ε hε η hη
  obtain ⟨Y₀, hY₀⟩ := exists_nat_gt (4 / (ε * η))
  refine ⟨max Y₀ 2, fun Y hY => ?_⟩
  have hY2 : 2 ≤ Y := (le_max_right Y₀ 2).trans hY
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hY' : (Y₀ : ℝ) ≤ Y := by exact_mod_cast ((le_max_left Y₀ 2).trans hY)
  have hMain : 2 / (ε * (Y : ℝ)) < η / 2 := by
    have h := (div_lt_iff₀ (mul_pos hε hη)).mp (hY₀.trans_le hY')
    apply (div_lt_iff₀ (mul_pos hε hYpos)).mpr
    nlinarith
  let correction (N : ℕ) : ℝ := ∑ p ∈ tailPrimes Y N, (1 : ℝ) / ((p : ℝ) - 1)
  have hClosing : Tendsto (fun N : ℕ => (2 / ε) * (correction N / N)) atTop (𝓝 0) := by
    have h := correction_tendsto (tailPrimes Y) (fun N p hp =>
      ⟨(mem_filter.mp hp).2.1.two_le, mem_range.mp (mem_filter.mp hp).1⟩)
    simpa only [mul_zero] using (tendsto_const_nhds (x := 2 / ε)).mul h
  filter_upwards [eventually_ge_atTop Y, hClosing.eventually_lt
    (tendsto_const_nhds (x := η / 2)) (by positivity)] with N hN hLoss
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfc := A082957Analysis.frequency_markov (fun n => |full term n - small term Y n|)
    (fun _ => abs_nonneg _) ε hε (fun _ h => h) N
  refine hfc.trans ?_
  have hEstimate := div_le_div_of_nonneg_right (raw_tail_bound term hBound hZero Y N hY2 hN)
    (mul_nonneg hε.le hNpos.le)
  refine hEstimate.trans ?_
  change 2 * ((N : ℝ) / Y + correction N) / (ε * N) ≤ η
  have hSplit : 2 * ((N : ℝ) / Y + correction N) / (ε * N) =
      2 / (ε * (Y : ℝ)) + (2 / ε) * (correction N / N) := by
    field_simp
  rw [hSplit]
  linarith

end A082957Tail

-- Source module Signs.lean

namespace A082957Signs

open Finset Filter
open scoped BigOperators Topology

noncomputable def ratio (n : ℕ) : ℝ :=
  (n.centralBinom : ℝ) / 4 ^ n

private theorem ratio_nonneg (n : ℕ) : 0 ≤ ratio n := by
  unfold ratio
  positivity

private theorem ratio_succ (n : ℕ) : ratio (n + 1) = ratio n * ((2 * (n : ℝ) + 1) / (2 * (n + 1))) := by
  have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  unfold ratio
  rw [pow_succ]
  have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  linear_combination 2 * h

theorem square_ratio_bound (n : ℕ) : ratio n ^ 2 * ((n : ℝ) + 1) ≤ 1 := by
  induction n with
  | zero => norm_num [ratio]
  | succ n ih =>
    rw [ratio_succ]
    push_cast
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have ht : ((2 * (n : ℝ) + 1) / (2 * (n + 1))) ^ 2 * ((n : ℝ) + 1 + 1) ≤ (n : ℝ) + 1 := by
      rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < (2 * (n + 1)) ^ 2)]
      nlinarith
    calc
      _ = ratio n ^ 2 *
          (((2 * (n : ℝ) + 1) / (2 * (n + 1))) ^ 2 * ((n : ℝ) + 1 + 1)) := by ring
      _ ≤ ratio n ^ 2 * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left ht (sq_nonneg _)
      _ ≤ 1 := ih

theorem exists_even_sign_ratio_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, (((2 * k).choose k : ℕ) : ℝ) / 2 ^ (2 * k) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε ^ 2)
  refine ⟨k, ?_⟩
  rw [← Nat.centralBinom_eq_two_mul_choose, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num]
  change ratio k < ε
  by_contra! h
  have hp : (1 : ℝ) < (k : ℝ) * ε ^ 2 := (div_lt_iff₀ (by positivity)).mp hk
  have hi := square_ratio_bound k
  have hsq : ε ^ 2 ≤ ratio k ^ 2 := by gcongr
  have hm := mul_le_mul_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ k + 1)
  nlinarith [sq_nonneg ε]

noncomputable def activationHalf (p : ℕ) : ℝ := ((p : ℝ) - 1) / (p : ℝ)^2

private theorem activationHalf_nonneg {p : ℕ} (h : 2 ≤ p) : 0 ≤ activationHalf p := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast h
  unfold activationHalf
  exact div_nonneg (by linarith) (sq_nonneg _)

private theorem activationHalf_le_one {p : ℕ} (h : 2 ≤ p) : activationHalf p ≤ 1 := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast h
  unfold activationHalf
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (p : ℝ)^2)).mpr
  rw [one_mul]
  nlinarith

private theorem activationHalf_ge {p : ℕ} (h : 2 ≤ p) : 1 / (p : ℝ) ≤ 2 * activationHalf p := by
  have hp : (2 : ℝ) ≤ p := by exact_mod_cast h
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  unfold activationHalf
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < p) (by positivity : (0 : ℝ) < (p : ℝ)^2)).mpr
  nlinarith

def smallOddPrimes (B : ℕ) : Finset ℕ :=
  (range B).filter fun p => p.Prime ∧ 2 < p

theorem exists_small_activation_product (k : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℕ, 2 ^ k * ∏ p ∈ smallOddPrimes B, (1 - activationHalf p) < η := by
  have hLarge (L : ℝ) : ∃ B : ℕ, L < ∑ p ∈ smallOddPrimes B, activationHalf p := by
    by_contra! hBound
    apply not_summable_one_div_on_primes
    apply summable_of_sum_range_le (c := 2 * L + 1 / 2)
    · intro n
      exact Set.indicator_nonneg (fun _ _ => by positivity) n
    · intro B
      have hterm (p : ℕ) :
          Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) p ≤
            (if p.Prime ∧ 2 < p then 2 * activationHalf p else 0) +
              (if p = 2 then (1 / 2 : ℝ) else 0) := by
        by_cases hp : p.Prime
        · have hp2 := hp.two_le
          by_cases hpeq : p = 2
          · subst p
            norm_num [Set.indicator, hp]
          · have h3 : 2 < p := by omega
            simpa [Set.indicator, hp, hpeq, h3] using activationHalf_ge hp2
        · have h2 : p ≠ 2 := fun h => hp (h ▸ Nat.prime_two)
          simp [Set.indicator, hp, h2]
      refine (sum_le_sum (fun p _ => hterm p)).trans ?_
      rw [sum_add_distrib, ← sum_filter, ← mul_sum]
      have hp2 : (∑ p ∈ range B, if p = 2 then (1 / 2 : ℝ) else 0) ≤ 1 / 2 := by
        rw [sum_ite_eq']
        split <;> norm_num
      change 2 * (∑ p ∈ smallOddPrimes B, activationHalf p) + _ ≤ _
      linarith [hBound B]
  obtain ⟨B, hB⟩ := hLarge ((2 : ℝ)^k / η)
  refine ⟨B, ?_⟩
  let A := ∑ p ∈ smallOddPrimes B, activationHalf p
  have hA : 0 ≤ A := sum_nonneg (fun p hp =>
    activationHalf_nonneg ((mem_filter.mp hp).2.1.two_le))
  have hProd : (∏ p ∈ smallOddPrimes B, (1 - activationHalf p)) ≤ Real.exp (-A) := by
    dsimp [A]
    rw [← sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact sub_nonneg.mpr (activationHalf_le_one ((mem_filter.mp hp).2.1.two_le))
    · intro p hp
      rw [sub_eq_add_neg, add_comm]
      exact Real.add_one_le_exp (-activationHalf p)
  calc
    _ ≤ (2 : ℝ)^k * Real.exp (-A) := mul_le_mul_of_nonneg_left hProd (by positivity)
    _ ≤ (2 : ℝ)^k / (A + 1) := by
      rw [Real.exp_neg, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (Real.add_one_le_exp A)) (by positivity)
    _ < η := by
      have hP : (2 : ℝ)^k < A * η := (div_lt_iff₀ hη).mp hB
      apply (div_lt_iff₀ (by positivity : 0 < A + 1)).mpr
      nlinarith

end A082957Signs

-- Source module SignedWindows.lean

namespace A082957Windows

open Finset
open scoped BigOperators

private theorem subset_sum_interval_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (d : ℝ) (hd : 0 < d) (hw : ∀ i, d ≤ w i) (x y : ℝ) (hxy : y - x < d) :
    ((univ : Finset ι).powerset.filter (fun s : Finset ι =>
      x ≤ ∑ i ∈ s, w i ∧ ∑ i ∈ s, w i ≤ y)).card ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let family := (univ : Finset ι).powerset.filter (fun s : Finset ι =>
    x ≤ ∑ i ∈ s, w i ∧ ∑ i ∈ s, w i ≤ y)
  have hf : IsAntichain (· ⊆ ·) (↑family : Set (Finset ι)) := by
    intro a ha b hb hne hab
    have ha' := (mem_filter.mp (show a ∈ family from ha)).2
    have hb' := (mem_filter.mp (show b ∈ family from hb)).2
    have hsdiff : (b \ a).Nonempty := sdiff_nonempty.mpr (fun hba => hne (Subset.antisymm hab hba))
    obtain ⟨i, hi⟩ := hsdiff
    have hSingle : d ≤ ∑ j ∈ b \ a, w j :=
      (hw i).trans (single_le_sum (fun j _ => hd.le.trans (hw j)) hi)
    have hSums := sum_sdiff (f := w) hab
    linarith [ha'.1, hb'.2]
  exact hf.sperner

noncomputable def score {ι : Type*} [Fintype ι] (w : ι → ℝ) (sign : ι → Bool) : ℝ :=
  ∑ i, if sign i then w i else -w i

theorem signed_window_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (d : ℝ) (hd : 0 < d)
    (hw : ∀ i, d ≤ w i) (x y : ℝ) (hxy : y - x < 2 * d) :
    ((univ : Finset (ι → Bool)).filter (fun sign => x ≤ score w sign ∧ score w sign ≤ y)).card ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let pos : (ι → Bool) → Finset ι := fun sign => univ.filter (sign ·)
  let l := (x + ∑ i, w i) / 2
  let u := (y + ∑ i, w i) / 2
  have hl : u - l < d := by dsimp [l, u]; linarith
  have hCard := subset_sum_interval_bound w d hd hw l u hl
  apply le_trans ?_ hCard
  apply card_le_card_of_injOn pos
  · intro sign hs
    have hsign := (mem_filter.mp (show sign ∈ _ from hs)).2
    have hscore : score w sign = 2 * (∑ i ∈ pos sign, w i) - ∑ i, w i := by
      unfold score pos
      rw [sum_filter, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro i hi
      cases sign i <;> simp [two_mul]
    rw [hscore] at hsign
    refine mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), ?_⟩
    constructor <;> dsimp [l, u] <;> linarith [hsign.1, hsign.2]
  · intro first _ second _ heq
    funext i
    have h := congrArg (fun s : Finset ι => i ∈ s) heq
    change (i ∈ univ.filter (first ·)) = (i ∈ univ.filter (second ·)) at h
    simp only [mem_filter, mem_univ, true_and] at h
    cases hf : first i <;> cases hs : second i <;> simp_all

private theorem card_window_eq_sum {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (((univ : Finset ι).filter P).card : ℝ) = ∑ i : ι, if P i then (1 : ℝ) else 0 := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

theorem split_signed_window_card {γ ι ω : Type*} [Fintype γ] [Fintype ι] [DecidableEq ι]
    [Fintype ω] (split : γ ≃ (ι → Bool) × ω) (f : γ → ℝ) (baseline : ω → ℝ) (w : ι → ℝ)
    (d : ℝ) (hd : 0 < d) (hw : ∀ i, d ≤ w i) (x y : ℝ) (hxy : y - x < 2 * d)
    (hf : ∀ t, f t = baseline (split t).2 + score w (split t).1) :
    ((univ : Finset γ).filter (fun t => x ≤ f t ∧ f t ≤ y)).card ≤
      Fintype.card ω * (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  let P (t : γ) : Prop := x ≤ f t ∧ f t ≤ y
  let Q (c : ω) (b : ι → Bool) : Prop :=
    x - baseline c ≤ score w b ∧ score w b ≤ y - baseline c
  have hReindex : (∑ t : γ, if P t then (1 : ℝ) else 0) =
      ∑ p : (ι → Bool) × ω, if Q p.2 p.1 then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv split
    intro t
    have hPred : P t ↔ Q (split t).2 (split t).1 := by
      unfold P Q
      rw [hf t]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [hPred]
  rw [Fintype.sum_prod_type, sum_comm] at hReindex
  have hEach (c : ω) : (∑ b : ι → Bool, if Q c b then (1 : ℝ) else 0) ≤
      ((Fintype.card ι).choose (Fintype.card ι / 2) : ℝ) := by
    rw [← card_window_eq_sum]
    exact_mod_cast signed_window_count w d hd hw (x - baseline c) (y - baseline c) (by linarith)
  have h := sum_le_sum (s := (univ : Finset ω)) (fun c _ => hEach c)
  rw [← hReindex, ← card_window_eq_sum, sum_const, card_univ, nsmul_eq_mul] at h
  exact_mod_cast h

theorem symmetrization_bound {Ω B : Type*} [Fintype Ω] [Fintype B]
    [Nonempty B] (perm : B → Equiv.Perm Ω)
    (P E : Ω → Prop) [DecidablePred P] [DecidablePred E]
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hSign : ∀ s : Ω, ¬ E s →
      (((univ : Finset B).filter (fun b => P (perm b s))).card : ℝ) ≤ (Fintype.card B : ℝ) * ρ) :
    (((univ : Finset Ω).filter P).card : ℝ) ≤
      (((univ : Finset Ω).filter E).card : ℝ) + (Fintype.card Ω : ℝ) * ρ := by
  classical
  have hInv (b : B) : (∑ s : Ω, if P (perm b s) then (1 : ℝ) else 0) =
      ∑ s : Ω, if P s then (1 : ℝ) else 0 :=
    Fintype.sum_equiv (perm b) _ _ (fun _ => rfl)
  have hLe (s : Ω) :
      (∑ b : B, if P (perm b s) then (1 : ℝ) else 0) ≤
        (Fintype.card B : ℝ) * ((if E s then 1 else 0) + ρ) := by
    rw [← card_window_eq_sum]
    by_cases hs : E s
    · rw [if_pos hs]
      have hc : ((univ.filter (fun b : B => P (perm b s))).card : ℝ) ≤ (Fintype.card B : ℝ) := by
        exact_mod_cast card_le_univ _
      apply hc.trans
      nth_rw 1 [← mul_one (Fintype.card B : ℝ)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · simpa only [if_neg hs, zero_add] using hSign s hs
  have hsum := sum_le_sum (s := (univ : Finset Ω)) (fun s _ => hLe s)
  rw [sum_comm] at hsum
  simp_rw [hInv] at hsum
  rw [sum_const, card_univ, nsmul_eq_mul, ← mul_sum, sum_add_distrib, sum_const, card_univ,
    nsmul_eq_mul, ← card_window_eq_sum, ← card_window_eq_sum] at hsum
  exact le_of_mul_le_mul_left hsum (by exact_mod_cast Fintype.card_pos)

def activeCount {ι : Type*} [Fintype ι] {α : ι → Type*}
    (active : ∀ i, α i → Prop) [∀ i, DecidablePred (active i)] (sample : ∀ i, α i) : ℕ :=
  (univ.filter fun i => active i (sample i)).card

theorem activation_shortage {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (active : ∀ i, α i → Prop) [∀ i, DecidablePred (active i)] (k : ℕ) :
    (((univ : Finset (∀ i, α i)).filter (fun sample => activeCount active sample < k)).card : ℝ) /
        (Fintype.card (∀ i, α i) : ℝ) ≤
      2 ^ k * ∏ i, (1 - ((univ.filter (active i)).card : ℝ) / (2 * Fintype.card (α i))) := by
  classical
  let step (i : ι) (x : α i) : ℝ := if active i x then 1 / 2 else 1
  have hMoment (sample : ∀ i, α i) :
      (1 / 2 : ℝ) ^ activeCount active sample = ∏ i, step i (sample i) := by
    unfold step activeCount
    rw [← prod_filter, prod_const]
  have hPoint (sample : ∀ i, α i) :
      (if activeCount active sample < k then (1 : ℝ) else 0) ≤
        2 ^ k * (1 / 2 : ℝ) ^ activeCount active sample := by
    by_cases h : activeCount active sample < k
    · rw [if_pos h]
      calc
        1 = 2 ^ k * (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; norm_num
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h.le
    · rw [if_neg h]
      positivity
  have hSum := sum_le_sum (s := (univ : Finset (∀ i, α i))) (fun sample _ => hPoint sample)
  simp only [hMoment, ← mul_sum, ← Fintype.prod_sum, ← card_window_eq_sum] at hSum
  have hLocal (i : ι) : ∑ x : α i, step i x =
      (Fintype.card (α i) : ℝ) * (1 - ((univ.filter (active i)).card : ℝ) /
        (2 * Fintype.card (α i))) := by
    have hStep (x : α i) : step i x = 1 - (if active i x then (1 : ℝ) else 0) / 2 := by
      unfold step
      split <;> norm_num
    simp_rw [hStep, div_eq_mul_inv _ (2 : ℝ), sum_sub_distrib, sum_const, card_univ,
      nsmul_eq_mul, mul_one, ← sum_mul, ← card_window_eq_sum]
    have hCard : (Fintype.card (α i) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (α i) ≠ 0)
    field_simp
  simp_rw [hLocal] at hSum
  rw [prod_mul_distrib, ← Nat.cast_prod, ← Fintype.card_pi] at hSum
  apply (div_le_iff₀ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (∀ i, α i)))).mpr
  linear_combination hSum

theorem area_window_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, Nonempty (α i)]
    (value : ∀ i, α i → ℝ) (active : ∀ i, α i → Prop) [∀ i, DecidablePred (active i)]
    (flip : ∀ i, Equiv.Perm (α i)) (w : ι → ℝ)
    (d : ℝ) (hd : 0 < d) (hw : ∀ i a, active i a → d ≤ w i)
    (hsign : ∀ i a, active i a → value i a = w i ∨ value i a = -w i)
    (hflip : ∀ i a, active i a → value i (flip i a) = -value i a)
    (k : ℕ) (x y : ℝ) (hxy : y - x < 2 * d) :
    (((univ : Finset (∀ i, α i)).filter (fun sample =>
      x ≤ ∑ i, value i (sample i) ∧ (∑ i, value i (sample i)) ≤ y)).card : ℝ) /
      (Fintype.card (∀ i, α i) : ℝ) ≤
    2 ^ (2 * k) * (∏ i, (1 - ((univ.filter (active i)).card : ℝ) / (2 * Fintype.card (α i)))) +
      ((2 * k).choose k : ℝ) / 2 ^ (2 * k) := by
  classical
  let Ω := ∀ i, α i
  let P (sample : Ω) : Prop := x ≤ ∑ i, value i (sample i) ∧ (∑ i, value i (sample i)) ≤ y
  let E (sample : Ω) : Prop := activeCount active sample < 2 * k
  let perm (b : ι → Bool) : Equiv.Perm Ω :=
    Equiv.piCongrRight (fun i => if b i then flip i else Equiv.refl _)
  have perm_apply (b : ι → Bool) (a : Ω) (i : ι) :
      (perm b a) i = if b i then flip i (a i) else a i := by
    change ((if b i then flip i else Equiv.refl _) (a i)) = _
    by_cases h : b i = true <;> simp [h]
  let ρ := ((2 * k).choose k : ℝ) / 2 ^ (2 * k)
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hSign (sample : Ω) (hNot : ¬ E sample) :
      (((univ : Finset (ι → Bool)).filter (fun b => P (perm b sample))).card : ℝ) ≤
        (Fintype.card (ι → Bool) : ℝ) * ρ := by
    have hCount : 2 * k ≤ (univ.filter (fun i => active i (sample i))).card := by
      exact le_of_not_gt hNot
    obtain ⟨selected, hSel, hSize⟩ := exists_subset_card_eq hCount
    let I := {i : ι // i ∈ selected}
    let J := {i : ι // i ∉ selected}
    let split₀ : (ι → Bool) ≃ (I → Bool) × (J → Bool) :=
      Equiv.piEquivPiSubtypeProd (· ∈ selected) (fun _ => Bool)
    let orient (i : I) : Equiv.Perm Bool :=
      if value i (sample i) = w i then Equiv.boolNot else Equiv.refl Bool
    let split : (ι → Bool) ≃ (I → Bool) × (J → Bool) :=
      split₀.trans ((Equiv.piCongrRight orient).prodCongr (Equiv.refl _))
    let baseline (bits : J → Bool) : ℝ :=
      ∑ i : J, value i (if bits i then flip i (sample i) else sample i)
    let transformed (mask : ι → Bool) : ℝ := ∑ i, value i ((perm mask sample) i)
    have hActive (i : I) : active i (sample i) := (mem_filter.mp (hSel i.2)).2
    have hMin (i : I) : d ≤ w i := hw i (sample i) (hActive i)
    have hValue (mask : ι → Bool) (i : I) :
        value i ((perm mask sample) i) =
          if (split mask).1 i then w i else -w i := by
      rw [perm_apply]
      change value i (if mask i then flip i (sample i) else sample i) =
        if orient i (mask i) then w i else -w i
      have hflip' := hflip i (sample i) (hActive i)
      obtain hpos | hneg := hsign i (sample i) (hActive i)
      · cases hm : mask i <;>
          simp [orient, hpos, hflip', hm, Equiv.boolNot]
      · have hne : -w i ≠ w i := by linarith [hMin i]
        cases hm : mask i <;>
          simp [orient, hneg, hne, hflip', hm]
    have hDecomp (mask : ι → Bool) : transformed mask =
        baseline (split mask).2 + score (fun i : I => w i) (split mask).1 := by
      unfold transformed baseline score
      rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ selected), add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        exact congrArg (value i) (perm_apply mask sample i)
      · refine Finset.sum_congr (Finset.ext (by intro i; simp)) ?_
        intro i hi
        exact hValue mask i
    have hWin := split_signed_window_card split transformed baseline (fun i : I => w i)
      d hd hMin x y hxy hDecomp
    have hLabel : Fintype.card I = 2 * k := by
      change Fintype.card ↥selected = 2 * k
      rw [Fintype.card_coe, hSize]
    rw [hLabel, show 2 * k / 2 = k by omega] at hWin
    have hCard := Fintype.card_congr split
    have hFirst : Fintype.card (I → Bool) = 2 ^ (2 * k) := by
      rw [Fintype.card_fun, Fintype.card_bool, hLabel]
    rw [Fintype.card_prod, hFirst] at hCard
    have hCast : (Fintype.card (ι → Bool) : ℝ) = 2 ^ (2 * k) * Fintype.card (J → Bool) := by
      exact_mod_cast hCard
    calc
      _ ≤ (Fintype.card (J → Bool) : ℝ) * ((2 * k).choose k : ℝ) := by
        exact_mod_cast hWin
      _ = _ := by
        rw [hCast]
        dsimp [ρ]
        have hpow : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
        field_simp
  have hCard := symmetrization_bound perm P E ρ hρ hSign
  have hΩ : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Ω)
  have hNormalized := div_le_div_of_nonneg_right hCard hΩ.le
  rw [add_div, mul_div_cancel_left₀ _ hΩ.ne'] at hNormalized
  have hSmall := activation_shortage active (2 * k)
  dsimp only [E, ρ, Ω] at hNormalized
  linarith

end A082957Windows

-- Source module DivisorRatio.lean

namespace A082957Certificate

open Finset

noncomputable def valuationRatio (p e : ℕ) : ℝ := ∑ i ∈ range (e + 1), ((p : ℝ)⁻¹) ^ i

def valuationRatioRat (p e : ℕ) : ℚ := ∑ i ∈ range (e + 1), ((p : ℚ)⁻¹) ^ i

theorem valuationRatioRat_cast (p e : ℕ) : (valuationRatioRat p e : ℝ) = valuationRatio p e := by
  simp [valuationRatioRat, valuationRatio]

theorem valuationRatio_zero (p : ℕ) : valuationRatio p 0 = 1 := by
  simp [valuationRatio]

theorem valuationRatio_mono (p : ℕ) : Monotone (valuationRatio p) := by
  intro e f h
  unfold valuationRatio
  refine sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ h)) ?_
  intro i hi hnot
  positivity

theorem valuationRatio_ge_one (p e : ℕ) : 1 ≤ valuationRatio p e := by
  simpa only [valuationRatio_zero] using valuationRatio_mono p (show 0 ≤ e by omega)

theorem valuationRatio_le_cap {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    valuationRatio p e ≤ (p : ℝ) / ((p : ℝ) - 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp₀ : 0 < (p : ℝ) := by linarith
  have hpos : 0 < (p : ℝ) - 1 := by linarith
  unfold valuationRatio
  rw [geom_sum_inv (by linarith : (p : ℝ) ≠ 1) hp₀.ne', div_eq_mul_inv, mul_comm]
  gcongr
  exact sub_le_self _ (by positivity)

theorem valuationCap_le_two {p : ℕ} (hp : 2 ≤ p) :
    (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  apply (div_le_iff₀ (by linarith)).2
  linarith

theorem valuationRatioRat_range {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    1 ≤ valuationRatioRat p e ∧ valuationRatioRat p e ≤ 2 := by
  have hlo : 1 ≤ (valuationRatioRat p e : ℝ) := by
    rw [valuationRatioRat_cast]
    exact valuationRatio_ge_one p e
  have hhi : (valuationRatioRat p e : ℝ) ≤ 2 := by
    rw [valuationRatioRat_cast]
    exact (valuationRatio_le_cap hp e).trans (valuationCap_le_two hp)
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

theorem log_valuationRatio_le {p : ℕ} (hp : 2 ≤ p) (e : ℕ) :
    Real.log (valuationRatio p e) ≤ ((p : ℝ) - 1)⁻¹ := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (p : ℝ) - 1 ≠ 0 := by linarith
  calc
    _ ≤ valuationRatio p e - 1 :=
      Real.log_le_sub_one_of_pos (zero_lt_one.trans_le (valuationRatio_ge_one p e))
    _ ≤ (p : ℝ) / ((p : ℝ) - 1) - 1 := sub_le_sub_right (valuationRatio_le_cap hp e) _
    _ = _ := by field_simp [hpos] <;> ring

theorem valuationRatio_eq_div {p : ℕ} (hp : 0 < p) (e : ℕ) :
    valuationRatio p e = (∑ i ∈ range (e + 1), (p : ℝ) ^ i) / (p : ℝ) ^ e := by
  have hp₀ : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold valuationRatio
  rw [div_eq_mul_inv, sum_mul, ← sum_range_reflect (fun i => (p : ℝ) ^ i * ((p : ℝ) ^ e)⁻¹)]
  refine sum_congr rfl ?_
  intro i hi
  have h : i ≤ e := by simpa using mem_range.1 hi
  rw [Nat.add_sub_cancel, inv_pow, ← div_eq_mul_inv]
  apply (eq_div_iff (pow_ne_zero _ hp₀)).2
  have hsplit : (p : ℝ) ^ e = (p : ℝ) ^ i * (p : ℝ) ^ (e - i) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  rw [hsplit, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp₀), one_mul]

theorem sigma_ratio_product {m : ℕ} (hm : 0 < m) :
    (ArithmeticFunction.sigma 1 m : ℝ) / m =
      ∏ p ∈ m.primeFactors, valuationRatio p (padicValNat p m) := by
  have hfac := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
    _ (ArithmeticFunction.isMultiplicative_sigma (k := 1)) hm.ne'
  change ArithmeticFunction.sigma 1 m =
    ∏ p ∈ m.factorization.support, ArithmeticFunction.sigma 1 (p ^ m.factorization p) at hfac
  rw [Nat.support_factorization] at hfac
  have hmprod : (m : ℝ) = ∏ p ∈ m.primeFactors, (p : ℝ) ^ (m.factorization p) := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hm.ne')
  rw [hfac, Nat.cast_prod, hmprod, ← prod_div_distrib]
  refine prod_congr rfl (fun p hp => ?_)
  have hprime := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.sigma_one_apply_prime_pow hprime, Nat.cast_sum]
  simp only [Nat.cast_pow]
  rw [valuationRatio_eq_div hprime.pos, Nat.factorization_def m hprime]

theorem log_sigma_ratio {m : ℕ} (hm : 0 < m) :
    Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) =
      ∑ p ∈ m.primeFactors, Real.log (valuationRatio p (padicValNat p m)) := by
  rw [sigma_ratio_product hm, Real.log_prod]
  exact fun p _ => (zero_lt_one.trans_le (valuationRatio_ge_one p _)).ne'

noncomputable def logContribution (p n : ℕ) : ℝ :=
  Real.log (valuationRatio p (padicValNat p (2 * n + 1))) -
    Real.log (valuationRatio p (padicValNat p (2 * n)))

end A082957Certificate

-- Source module Valuations.lean

namespace A082957Certificate

inductive ValuationSide where
  | unit
  | even (e : ℕ)
  | odd (e : ℕ)
  deriving DecidableEq

def cappedVal (p E m : ℕ) : ℕ :=
  Nat.findGreatest (fun e => p ^ e ∣ m) E

theorem cappedVal_le (p E m : ℕ) : cappedVal p E m ≤ E :=
  Nat.findGreatest_le E

theorem le_cappedVal_iff {p E m e : ℕ} : e ≤ cappedVal p E m ↔ e ≤ E ∧ p ^ e ∣ m := by
  refine ⟨fun h => ⟨h.trans (cappedVal_le _ _ _), ?_⟩, fun h => Nat.le_findGreatest h.1 h.2⟩
  have hv := Nat.findGreatest_spec (P := fun i : ℕ => p ^ i ∣ m)
    (Nat.zero_le E) (by simp : p ^ 0 ∣ m)
  exact (pow_dvd_pow _ h).trans hv

theorem cappedVal_eq_of_lt {p E m e : ℕ} (he : e < E) :
    cappedVal p E m = e ↔ p ^ e ∣ m ∧ ¬ p ^ (e + 1) ∣ m := by
  have hc : cappedVal p E m ≤ e ↔ ¬e + 1 ≤ cappedVal p E m := by omega
  rw [le_antisymm_iff, hc, le_cappedVal_iff, le_cappedVal_iff]
  simp [he.le, he, and_comm]

theorem cappedVal_eq_cap {p E m : ℕ} : cappedVal p E m = E ↔ p ^ E ∣ m := by
  rw [le_antisymm_iff, le_cappedVal_iff]
  simp only [cappedVal_le, le_refl, true_and]

theorem cappedVal_eq_min {p E m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    cappedVal p E m = min E (padicValNat p m) := by
  let : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · apply le_min (cappedVal_le _ _ _)
    exact (padicValNat_dvd_iff_le hm).1 (le_cappedVal_iff.1 le_rfl).2
  · exact le_cappedVal_iff.2 ⟨min_le_left _ _, (padicValNat_dvd_iff_le hm).2 (min_le_right _ _)⟩

theorem cappedVal_modeq {p E m n : ℕ} (h : m ≡ n [MOD p ^ E]) :
    cappedVal p E m = cappedVal p E n := by
  have eq_dvd {e : ℕ} (he : e ≤ E) : p ^ e ∣ m ↔ p ^ e ∣ n := by
    have h' := h.of_dvd (pow_dvd_pow _ he)
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨h'.symm.trans, h'.trans⟩
  apply le_antisymm
  · have hm := le_cappedVal_iff.1 (le_refl (cappedVal p E m))
    exact le_cappedVal_iff.2 ⟨hm.1, (eq_dvd hm.1).1 hm.2⟩
  · have hn := le_cappedVal_iff.1 (le_refl (cappedVal p E n))
    exact le_cappedVal_iff.2 ⟨hn.1, (eq_dvd hn.1).2 hn.2⟩

def valuationSide (p E n : ℕ) : ValuationSide :=
  if p ∣ 2 * n then .even (cappedVal p E (2 * n))
  else if p ∣ 2 * n + 1 then .odd (cappedVal p E (2 * n + 1))
  else .unit

theorem valuationSide_modeq {p E m n : ℕ} (hE : 0 < E) (h : m ≡ n [MOD p ^ E]) :
    valuationSide p E m = valuationSide p E n := by
  have hdiv : p ∣ p ^ E := by
    simpa using (pow_dvd_pow p hE : p ^ 1 ∣ p ^ E)
  have hEven := h.mul_left 2
  have hOdd := hEven.add_right 1
  have eq_dvd {a b : ℕ} (hab : a ≡ b [MOD p ^ E]) : p ∣ a ↔ p ∣ b := by
    have hh := hab.of_dvd hdiv
    rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
    exact ⟨hh.symm.trans, hh.trans⟩
  simp only [valuationSide, eq_dvd hEven, eq_dvd hOdd, cappedVal_modeq hEven, cappedVal_modeq hOdd]

theorem not_dvd_both {p n : ℕ} (hp : p.Prime) (h₀ : p ∣ 2 * n) (h₁ : p ∣ 2 * n + 1) : False := by
  apply hp.not_dvd_one
  simpa using Nat.dvd_sub h₁ h₀

theorem valuationSide_even_iff {p E n e : ℕ} (he : 0 < e) :
    valuationSide p E n = .even e ↔ cappedVal p E (2 * n) = e := by
  by_cases h : p ∣ 2 * n
  · simp [valuationSide, h]
  · have hn : cappedVal p E (2 * n) ≠ e := by
      intro hv
      have hle : 1 ≤ cappedVal p E (2 * n) := hv ▸ he
      apply h
      simpa using (le_cappedVal_iff.1 hle).2
    by_cases h' : p ∣ 2 * n + 1 <;> simp [valuationSide, h, h', hn]

theorem valuationSide_odd_iff {p E n e : ℕ} (hp : p.Prime) (he : 0 < e) :
    valuationSide p E n = .odd e ↔ cappedVal p E (2 * n + 1) = e := by
  by_cases h : p ∣ 2 * n + 1
  · have h' : ¬p ∣ 2 * n := fun hz => not_dvd_both hp hz h
    simp [valuationSide, h, h']
  · have hn : cappedVal p E (2 * n + 1) ≠ e := by
      intro hv
      have hle : 1 ≤ cappedVal p E (2 * n + 1) := hv ▸ he
      apply h
      simpa using (le_cappedVal_iff.1 hle).2
    by_cases h' : p ∣ 2 * n <;> simp [valuationSide, h, h', hn]

def valuationCounts (p E : ℕ) : List (ValuationSide × ℕ) :=
  let middle := (List.range E).drop 1
  if p = 2 then
    middle.map (fun e => (.even e, 2 ^ (E - e))) ++ [(.even E, 2)]
  else
    (.unit, (p - 2) * p ^ (E - 1)) ::
      (middle.flatMap fun e =>
        [(.even e, (p - 1) * p ^ (E - e - 1)), (.odd e, (p - 1) * p ^ (E - e - 1))]) ++
      [(.even E, 1), (.odd E, 1)]

theorem count_modeq_bounds {N m r : ℕ} (hm : 0 < m) :
    N / m ≤ Nat.count (fun n => n ≡ r [MOD m]) N ∧
      Nat.count (fun n => n ≡ r [MOD m]) N ≤ N / m + 1 := by
  rw [Nat.count_modEq_card N hm r]
  split <;> omega

theorem count_modeq_mul {m r : ℕ} (hm : 0 < m) (k : ℕ) :
    Nat.count (fun n => n ≡ r [MOD m]) (m * k) = k := by
  rw [Nat.count_modEq_card _ hm r, Nat.mul_div_cancel_left _ hm]
  simp

theorem count_congr {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (N : ℕ) (h : ∀ n, P n ↔ Q n) : Nat.count P N = Nat.count Q N := by
  simp only [Nat.count_eq_card_filter_range, h]

theorem count_diff {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ n, Q n → P n) (N : ℕ) :
    Nat.count (fun n => P n ∧ ¬Q n) N = Nat.count P N - Nat.count Q N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ, ih]
    have hle : Nat.count Q n ≤ Nat.count P n := Nat.count_mono_left (fun m _ => h m)
    by_cases hp : P n
    · by_cases hq : Q n <;> simp [hp, hq] <;> omega
    · have hq : ¬Q n := fun hq => hp (h n hq)
      simp [hp, hq]

theorem count_or {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ n, P n → Q n → False) (N : ℕ) :
    Nat.count (fun n => P n ∨ Q n) N = Nat.count P N + Nat.count Q N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ, ih]
    by_cases hp : P n
    · have hq : ¬Q n := h n hp
      simp [hp, hq] <;> omega
    · by_cases hq : Q n <;> simp [hp, hq] <;> omega

theorem affine_dvd_iff_modeq {d : ℕ} (hOdd : Odd d) (side : Bool) :
    ∃ r : ℕ, ∀ n : ℕ, d ∣ 2 * n + (if side then 1 else 0) ↔ n ≡ r [MOD d] := by
  have hc : Nat.Coprime d 2 := Nat.coprime_two_right.2 hOdd
  let r := if side then (d - 1) / 2 else 0
  have hR : 2 * r + (if side then 1 else 0) ≡ 0 [MOD d] := by
    apply Nat.modEq_zero_iff_dvd.2
    cases side with
    | false => simp [r]
    | true =>
      change d ∣ 2 * ((d - 1) / 2) + 1
      obtain ⟨k, hk⟩ := hOdd
      have heq : 2 * ((d - 1) / 2) + 1 = d := by omega
      rw [heq]
  refine ⟨r, fun n => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · have h' := (Nat.modEq_zero_iff_dvd.2 hn).trans hR.symm
    exact Nat.ModEq.cancel_left_of_coprime hc (h'.add_right_cancel' _)
  · exact Nat.modEq_zero_iff_dvd.1 (((hn.mul_left 2).add_right _).trans hR)

theorem count_affine_pow_odd {p E e : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (he : e ≤ E)
    (side : Bool) :
    Nat.count (fun n => p ^ e ∣ 2 * n + (if side then 1 else 0)) (p ^ E) = p ^ (E - e) := by
  have ho : Odd (p ^ e) := (hp.eq_two_or_odd'.resolve_left hp₂).pow
  obtain ⟨r, hr⟩ := affine_dvd_iff_modeq ho side
  rw [count_congr _ hr]
  have hpow : p ^ E = p ^ e * p ^ (E - e) := by rw [← pow_add, Nat.add_sub_of_le he]
  rw [hpow, count_modeq_mul (pow_pos hp.pos _)]

theorem count_even_pow_two {E e : ℕ} (he₁ : 0 < e) (he₂ : e ≤ E) :
    Nat.count (fun n => 2 ^ e ∣ 2 * n) (2 ^ E) = 2 ^ (E - (e - 1)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he₁.ne'
  have h : ∀ n : ℕ, 2 ^ (k + 1) ∣ 2 * n ↔ n ≡ 0 [MOD 2 ^ k] := by
    intro n
    rw [Nat.modEq_zero_iff_dvd, pow_succ', Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)]
  rw [count_congr _ h]
  have hpow : (2 : ℕ) ^ E = 2 ^ k * 2 ^ (E - k) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : k ≤ E)]
  rw [hpow, count_modeq_mul (by positivity)]
  simp

def residueProduct {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    Fin (m * n) ≃ Fin m × Fin n where
  toFun x := (⟨x.val % m, Nat.mod_lt _ hm⟩, ⟨x.val % n, Nat.mod_lt _ hn⟩)
  invFun x := ⟨Nat.chineseRemainder h x.1.val x.2.val,
    Nat.chineseRemainder_lt_mul h _ _ hm.ne' hn.ne'⟩
  left_inv x := by
    apply Fin.ext
    let y := Nat.chineseRemainder h (x.val % m) (x.val % n)
    have hxy : x.val ≡ y.val [MOD m * n] := Nat.chineseRemainder_modEq_unique h
      (Nat.mod_modEq _ _).symm (Nat.mod_modEq _ _).symm
    have hy : y.val < m * n := Nat.chineseRemainder_lt_mul h _ _ hm.ne' hn.ne'
    change y.val = x.val
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt hy] using hxy.symm
  right_inv x := by
    apply Prod.ext <;> apply Fin.ext
    · exact Eq.trans (Nat.chineseRemainder h x.1.val x.2.val).prop.1 (Nat.mod_eq_of_lt x.1.isLt)
    · exact Eq.trans (Nat.chineseRemainder h x.1.val x.2.val).prop.2 (Nat.mod_eq_of_lt x.2.isLt)

theorem joint_modeq {m n : ℕ} (h : m.Coprime n) (a b : ℕ) :
    ∃ r : ℕ, ∀ k : ℕ, (k ≡ a [MOD m] ∧ k ≡ b [MOD n]) ↔ k ≡ r [MOD m * n] := by
  let r := Nat.chineseRemainder h a b
  exact ⟨r.val, fun k => ⟨fun hk => Nat.chineseRemainder_modEq_unique h hk.1 hk.2,
    fun hk => let hc := (Nat.modEq_and_modEq_iff_modEq_mul h).2 hk
      ⟨hc.1.trans r.prop.1, hc.2.trans r.prop.2⟩⟩⟩

theorem count_joint_modeq_le {N m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n)
    (a b : ℕ) : Nat.count (fun k => k ≡ a [MOD m] ∧ k ≡ b [MOD n]) N ≤ N / (m * n) + 1 := by
  obtain ⟨r, hr⟩ := joint_modeq h a b
  rw [count_congr _ hr]
  exact (count_modeq_bounds (r := r) (Nat.mul_pos hm hn)).2

theorem count_capped_affine_odd {p E e : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (he : e ≤ E) (side : Bool) :
    Nat.count (fun n => cappedVal p E (2 * n + (if side then 1 else 0)) = e) (p ^ E) =
      if e = E then 1 else (p - 1) * p ^ (E - e - 1) := by
  by_cases h : e = E
  · subst e
    simp only [if_pos rfl]
    rw [count_congr _ (fun _ => cappedVal_eq_cap), count_affine_pow_odd hp hp₂ le_rfl side]
    simp
  · have he' : e < E := lt_of_le_of_ne he h
    rw [if_neg h, count_congr _ (fun _ => cappedVal_eq_of_lt he'),
      count_diff (fun _ hd => (pow_dvd_pow p (Nat.le_succ e)).trans hd),
      count_affine_pow_odd hp hp₂ he side, count_affine_pow_odd hp hp₂ he' side]
    have hstep : E - e = (E - e - 1) + 1 := by omega
    have hsub : E - (e + 1) = E - e - 1 := by omega
    rw [hsub, hstep, pow_succ']
    have hback : (E - e - 1 + 1) - 1 = E - e - 1 := by omega
    rw [hback]
    simpa only [Nat.sub_mul, one_mul]

theorem count_even_side_odd {p E e : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (he₁ : 0 < e) (he₂ : e ≤ E) :
    Nat.count (fun n => valuationSide p E n = .even e) (p ^ E) =
      if e = E then 1 else (p - 1) * p ^ (E - e - 1) := by
  rw [count_congr _ (fun _ => valuationSide_even_iff he₁)]
  simpa using count_capped_affine_odd hp hp₂ he₂ false

theorem count_odd_side_odd {p E e : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2)
    (he₁ : 0 < e) (he₂ : e ≤ E) :
    Nat.count (fun n => valuationSide p E n = .odd e) (p ^ E) =
      if e = E then 1 else (p - 1) * p ^ (E - e - 1) := by
  rw [count_congr _ (fun _ => valuationSide_odd_iff hp he₁)]
  simpa using count_capped_affine_odd hp hp₂ he₂ true

theorem count_even_side_two {E e : ℕ} (he₁ : 0 < e) (he₂ : e ≤ E) :
    Nat.count (fun n => valuationSide 2 E n = .even e) (2 ^ E) =
      if e = E then 2 else 2 ^ (E - e) := by
  rw [count_congr _ (fun _ => valuationSide_even_iff he₁)]
  by_cases h : e = E
  · subst e
    rw [if_pos rfl, count_congr _ (fun _ => cappedVal_eq_cap), count_even_pow_two he₁ le_rfl]
    rw [show E - (E - 1) = 1 by omega]
    simp
  · have he' := lt_of_le_of_ne he₂ h
    rw [if_neg h, count_congr _ (fun _ => cappedVal_eq_of_lt he'),
      count_diff (fun _ hd => (pow_dvd_pow 2 (Nat.le_succ e)).trans hd),
      count_even_pow_two he₁ he₂, count_even_pow_two (by omega : 0 < e + 1) he']
    have hstep : E - (e - 1) = (E - e) + 1 := by omega
    simp [hstep, pow_succ', two_mul]

theorem count_unit_side_odd {p E : ℕ} (hp : p.Prime) (hp₂ : p ≠ 2) (hE : 0 < E) :
    Nat.count (fun n => valuationSide p E n = .unit) (p ^ E) = (p - 2) * p ^ (E - 1) := by
  have hunit (n : ℕ) : valuationSide p E n = .unit ↔
      True ∧ ¬(p ∣ 2 * n ∨ p ∣ 2 * n + 1) := by
    by_cases h : p ∣ 2 * n <;> by_cases h' : p ∣ 2 * n + 1 <;> simp [valuationSide, h, h']
  rw [count_congr _ hunit, count_diff (fun _ _ => trivial), Nat.count_true,
    count_or (fun _ => not_dvd_both hp)]
  have h₀ := count_affine_pow_odd hp hp₂ hE false
  have h₁ := count_affine_pow_odd hp hp₂ hE true
  simp only [pow_one, Bool.false_eq_true, ↓reduceIte, add_zero] at h₀
  simp only [pow_one, ↓reduceIte] at h₁
  rw [h₀, h₁]
  have heq : p ^ E = p * p ^ (E - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hE]
  rw [heq, Nat.sub_mul, two_mul]

end A082957Certificate

-- Source module ResiduePi.lean

namespace A082957Certificate

open Finset

noncomputable def residuePi {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => (m i).Coprime (m j))) :
    Fin (∏ i, m i) ≃ (∀ i, Fin (m i)) := by
  letI : NeZero (∏ i, m i) := ⟨(prod_pos (fun i _ => hm i)).ne'⟩
  letI (i : ι) : NeZero (m i) := ⟨(hm i).ne'⟩
  exact (ZMod.finEquiv _).toEquiv.trans
    ((ZMod.prodEquivPi m hc).toEquiv.trans
      (Equiv.piCongrRight (fun i => (ZMod.finEquiv (m i)).symm.toEquiv)))

theorem zmod_finEquiv_val (m : ℕ) [NeZero m] (r : Fin m) :
    (ZMod.finEquiv m r).val = r.val := by
  cases m with
  | zero => exact r.elim0
  | succ _ => rfl

theorem residuePi_val {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hc : Pairwise (fun i j => (m i).Coprime (m j)))
    (k : Fin (∏ i, m i)) (i : ι) :
    (residuePi m hm hc k i).val = k.val % m i := by
  letI : NeZero (∏ i, m i) := ⟨(prod_pos (fun j _ => hm j)).ne'⟩
  letI (j : ι) : NeZero (m j) := ⟨(hm j).ne'⟩
  let z := ZMod.finEquiv (∏ i, m i) k
  have hz : z = (k.val : ZMod (∏ i, m i)) := by
    apply ZMod.val_injective _
    rw [ZMod.val_natCast_of_lt k.isLt]
    exact zmod_finEquiv_val _ _
  change ((ZMod.finEquiv (m i)).symm (ZMod.prodEquivPi m hc z i)).val = _
  rw [← zmod_finEquiv_val (m i) ((ZMod.finEquiv (m i)).symm (ZMod.prodEquivPi m hc z i))]
  rw [RingEquiv.apply_symm_apply, ZMod.prodEquivPi_apply, hz, map_natCast, ZMod.val_natCast]

end A082957Certificate

-- Source module Bridge.lean

namespace A082957Bridge

open Finset Filter
open scoped BigOperators Topology
open A082957Tail A082957Certificate

private theorem local_log_nonneg (p e : ℕ) : 0 ≤ Real.log (valuationRatio p e) :=
  Real.log_nonneg (valuationRatio_ge_one p e)

private theorem local_log_le_indicator {p m r n : ℕ} (hp : p.Prime) (hm : m = 2 * n + r) :
    Real.log (valuationRatio p (padicValNat p m)) ≤ majorant p r n := by
  subst m
  unfold majorant
  split
  · simpa only [one_div] using log_valuationRatio_le hp.two_le _
  · rename_i hd
    rw [padicValNat.eq_zero_of_not_dvd hd, valuationRatio_zero, Real.log_one]

theorem contribution_bound (p n : ℕ) (hp : p.Prime) (_ : 2 < p) :
    |logContribution p n| ≤ majorant p 0 n + majorant p 1 n := by
  have hOdd := local_log_le_indicator (p := p) (r := 1) (n := n) hp rfl
  have hEven := local_log_le_indicator (p := p) (m := 2 * n) (n := n) (r := 0) hp (by simp)
  have hOdd0 := local_log_nonneg p (padicValNat p (2 * n + 1))
  have hEven0 := local_log_nonneg p (padicValNat p (2 * n))
  unfold logContribution
  rw [abs_le]
  constructor <;> linarith

theorem contribution_zero (p n : ℕ) (_ : p.Prime) (h : 2 * n + 1 < p) :
    logContribution p n = 0 := by
  have hOdd : ¬ p ∣ 2 * n + 1 := fun hd =>
    (not_le_of_gt h) (Nat.le_of_dvd (by omega) hd)
  unfold logContribution
  rw [padicValNat.eq_zero_of_not_dvd hOdd, valuationRatio_zero, Real.log_one]
  by_cases hn : n = 0
  · simp [hn, valuationRatio_zero]
  have hEven : ¬ p ∣ 2 * n := fun hd =>
    (not_le_of_gt h) ((Nat.le_of_dvd (by omega) hd).trans (by omega))
  rw [padicValNat.eq_zero_of_not_dvd hEven, valuationRatio_zero, Real.log_one, sub_zero]

noncomputable def threshold (n : ℕ) : ℝ :=
  -Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ)))

theorem threshold_limit : Tendsto threshold atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / (2 * (n : ℝ))) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹ / 2) atTop (𝓝 1) := by
      simpa only [zero_div, add_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).add (hinv.div_const 2)
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hlog : Tendsto (fun n : ℕ => Real.log ((2 * (n : ℝ) + 1) / (2 * (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  unfold threshold
  simpa only [neg_zero] using hlog.neg

private theorem extended_log_sigma_ratio (m B : ℕ) (hm : 0 < m) (hB : m ≤ B) :
    ∑ p ∈ primesThrough B, Real.log (valuationRatio p (padicValNat p m)) =
      Real.log ((ArithmeticFunction.sigma 1 m : ℝ) / m) := by
  rw [log_sigma_ratio hm]
  symm
  apply sum_subset
  · intro p hp
    have hpInfo := Nat.mem_primeFactors.mp hp
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.le_of_dvd hm hpInfo.2.1).trans hB)), hpInfo.1⟩
  · intro p hp hnot
    have hprime := (mem_filter.mp hp).2
    have hDvd : ¬ p ∣ m := fun hd => hnot (Nat.mem_primeFactors.mpr ⟨hprime, hd, hm.ne'⟩)
    rw [padicValNat.eq_zero_of_not_dvd hDvd, valuationRatio_zero, Real.log_one]

theorem full_log_sigma (n : ℕ) (hn : 0 < n) :
    full logContribution n =
      Real.log ((ArithmeticFunction.sigma 1 (2 * n + 1) : ℝ) / (2 * n + 1 : ℕ)) -
        Real.log ((ArithmeticFunction.sigma 1 (2 * n) : ℝ) / (2 * n : ℕ)) := by
  unfold full small logContribution
  rw [sum_sub_distrib, extended_log_sigma_ratio _ _ (by omega) le_rfl,
    extended_log_sigma_ratio _ _ (by omega : 0 < 2 * n) (by omega)]

theorem compare_divisor_sums (n : ℕ) :
    (threshold n < full logContribution n) ↔
      1 ≤ n ∧ (∑ d ∈ (2 * n).divisors, d) < ∑ d ∈ (2 * n + 1).divisors, d := by
  by_cases hn : 0 < n
  · have he : 0 < 2 * n := by omega
    have ho : 0 < 2 * n + 1 := by omega
    have heR : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast he
    have hoR : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast ho
    have hse : (0 : ℝ) < (ArithmeticFunction.sigma 1 (2 * n) : ℝ) := by
      exact_mod_cast (ArithmeticFunction.sigma_pos_iff.mpr he : 0 < ArithmeticFunction.sigma 1 (2 * n))
    have hso : (0 : ℝ) < (ArithmeticFunction.sigma 1 (2 * n + 1) : ℝ) := by
      exact_mod_cast (ArithmeticFunction.sigma_pos_iff.mpr ho :
        0 < ArithmeticFunction.sigma 1 (2 * n + 1))
    rw [full_log_sigma n hn, threshold, ← ArithmeticFunction.sigma_one_apply,
      ← ArithmeticFunction.sigma_one_apply]
    have hth : (2 * (n : ℝ) + 1) / (2 * (n : ℝ)) =
        ((2 * n + 1 : ℕ) : ℝ) / ((2 * n : ℕ) : ℝ) := by push_cast; rfl
    rw [hth, Real.log_div hoR.ne' heR.ne', Real.log_div hso.ne' hoR.ne',
      Real.log_div hse.ne' heR.ne']
    simp only [show 1 ≤ n by omega, true_and]
    have hLog : Real.log (ArithmeticFunction.sigma 1 (2 * n) : ℝ) <
          Real.log (ArithmeticFunction.sigma 1 (2 * n + 1) : ℝ) ↔
        ArithmeticFunction.sigma 1 (2 * n) < ArithmeticFunction.sigma 1 (2 * n + 1) := by
      rw [Real.log_lt_log_iff hse hso]
      exact_mod_cast Iff.rfl
    rw [← hLog]
    constructor <;> intro h <;> linarith
  · obtain rfl : n = 0 := by omega
    simp [threshold, full, small, primesThrough, logContribution, valuationRatio_zero]

end A082957Bridge

-- Source module CappedApprox.lean

namespace A082957Capped

open Finset Filter
open scoped BigOperators Topology
open A082957Analysis A082957Tail A082957Certificate

noncomputable def sideScore (p : ℕ) : ValuationSide → ℝ
  | .unit => 0
  | .even e => -Real.log (valuationRatio p e)
  | .odd e => Real.log (valuationRatio p e)

noncomputable def clipped (Y E n : ℕ) : ℝ :=
  ∑ p ∈ primesThrough Y, sideScore p (valuationSide p E n)

def modulus (Y E : ℕ) : ℕ :=
  ∏ p ∈ primesThrough Y, p ^ E

theorem modulus_pos (Y E : ℕ) : 0 < modulus Y E := by
  unfold modulus
  exact Finset.prod_pos (fun p hp => pow_pos (mem_filter.mp hp).2.pos _)

theorem clipped_periodic (Y E : ℕ) (hE : 0 < E) (n : ℕ) :
    clipped Y E (n + modulus Y E) = clipped Y E n := by
  apply sum_congr rfl
  intro p hp
  have hDvd : p ^ E ∣ modulus Y E := dvd_prod_of_mem (fun p => p ^ E) hp
  have hMod : n + modulus Y E ≡ n [MOD p ^ E] := by
    simpa only [add_zero] using (Nat.ModEq.refl n).add (Nat.modEq_zero_iff_dvd.mpr hDvd)
  rw [valuationSide_modeq hE hMod]

theorem clipped_frequency (Y E : ℕ) (hE : 0 < E) (P : ℝ → Prop) :
    Tendsto (frequency (fun n => P (clipped Y E n))) atTop
      (𝓝 (frequency (fun n => P (clipped Y E n)) (modulus Y E))) := by
  classical
  apply frequency_periodic _ _ (modulus_pos Y E)
  intro n
  rw [clipped_periodic Y E hE]

def clippingFailure (Y E n : ℕ) : Prop :=
  n = 0 ∨ ∃ p ∈ primesThrough Y, p ^ E ∣ 2 * n ∨ p ^ E ∣ 2 * n + 1

theorem clipped_matches (Y E n : ℕ) (h : ¬ clippingFailure Y E n) :
    clipped Y E n = small logContribution Y n := by
  apply sum_congr rfl
  intro p hp
  have hpPrime := (mem_filter.mp hp).2
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hn : 0 < n := Nat.pos_of_ne_zero (fun h0 => h (Or.inl h0))
  have hEven : ¬ p ^ E ∣ 2 * n := fun hd => h (Or.inr ⟨p, hp, Or.inl hd⟩)
  have hOdd : ¬ p ^ E ∣ 2 * n + 1 := fun hd => h (Or.inr ⟨p, hp, Or.inr hd⟩)
  have hEven0 : 2 * n ≠ 0 := by omega
  have hOdd0 : 2 * n + 1 ≠ 0 := by omega
  have hEvenLt : padicValNat p (2 * n) < E :=
    lt_of_not_ge (fun hLe => hEven ((padicValNat_dvd_iff_le hEven0).mpr hLe))
  have hOddLt : padicValNat p (2 * n + 1) < E :=
    lt_of_not_ge (fun hLe => hOdd ((padicValNat_dvd_iff_le hOdd0).mpr hLe))
  have hEvenCap : cappedVal p E (2 * n) = padicValNat p (2 * n) := by
    rw [cappedVal_eq_min hpPrime hEven0, min_eq_right hEvenLt.le]
  have hOddCap : cappedVal p E (2 * n + 1) = padicValNat p (2 * n + 1) := by
    rw [cappedVal_eq_min hpPrime hOdd0, min_eq_right hOddLt.le]
  by_cases he : p ∣ 2 * n
  · have ho : ¬ p ∣ 2 * n + 1 := not_dvd_both hpPrime he
    simp [valuationSide, he, hEvenCap, sideScore, logContribution,
      padicValNat.eq_zero_of_not_dvd ho, valuationRatio_zero]
  · by_cases ho : p ∣ 2 * n + 1
    · simp [valuationSide, he, ho, hOddCap, sideScore, logContribution,
        padicValNat.eq_zero_of_not_dvd he, valuationRatio_zero]
    · simp [valuationSide, he, ho, sideScore, logContribution,
        padicValNat.eq_zero_of_not_dvd he, padicValNat.eq_zero_of_not_dvd ho, valuationRatio_zero]

private theorem frequency_modeq_upper (N d r : ℕ) (hd : 0 < d) (hN : 0 < N) :
    frequency (fun n => n ≡ r [MOD d]) N ≤ 1 / (d : ℝ) + 1 / (N : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : (Nat.count (fun n => n ≡ r [MOD d]) N : ℝ) ≤ (((N / d : ℕ) : ℝ) + 1) := by
    exact_mod_cast (count_modeq_bounds (N := N) (r := r) hd).2
  have hdiv : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d :=
    (le_div_iff₀ hdR).mpr (by exact_mod_cast Nat.div_mul_le_self N d)
  rw [frequency_eq_count]
  refine (div_le_div_of_nonneg_right (hc.trans (add_le_add hdiv le_rfl)) hNR.le).trans ?_
  field_simp
  exact le_rfl

private theorem frequency_cap_affine_upper (N p E : ℕ) (hp : p.Prime) (hE : 2 ≤ E)
    (hN : 0 < N) (side : Bool) :
    frequency (fun n => p ^ E ∣ 2 * n + (if side then 1 else 0)) N ≤
      1 / (2 : ℝ) ^ (E - 1) + 1 / (N : ℝ) := by
  by_cases h2 : p = 2
  · subst p
    cases side with
    | false =>
      have hD (n : ℕ) : 2 ^ E ∣ 2 * n + (if false then 1 else 0) ↔
          n ≡ 0 [MOD 2 ^ (E - 1)] := by
        change 2 ^ E ∣ 2 * n ↔ n ≡ 0 [MOD 2 ^ (E - 1)]
        rw [Nat.modEq_zero_iff_dvd,
          show (2 : ℕ)^E = 2 * 2 ^ (E - 1) by
            nth_rw 1 [show E = (E - 1) + 1 by omega]
            rw [pow_succ, Nat.mul_comm],
          mul_dvd_mul_iff_left (by decide : (2 : ℕ) ≠ 0)]
      have heq := funext (fun n => propext (hD n))
      rw [heq]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        frequency_modeq_upper N (2 ^ (E - 1)) 0 (by positivity) hN
    | true =>
      have hempty : (fun n => ((2 : ℕ) ^ E ∣ 2 * n + (if true then 1 else 0))) =
          (fun _ => False) := by
        funext n
        apply propext (iff_false_intro (fun hd => ?_))
        have htw : 2 ∣ (2 : ℕ)^E := by
          simpa using (pow_dvd_pow (2 : ℕ) (by omega : 1 ≤ E))
        exact Nat.two_not_dvd_two_mul_add_one _ (htw.trans hd)
      rw [hempty]
      simp only [frequency, filter_false, card_empty, Nat.cast_zero, zero_div]
      positivity
  · have ho : Odd (p ^ E) := (hp.eq_two_or_odd'.resolve_left h2).pow
    obtain ⟨r, hr⟩ := affine_dvd_iff_modeq ho side
    rw [funext (fun n => propext (hr n))]
    refine (frequency_modeq_upper N (p^E) r (pow_pos hp.pos _) hN).trans ?_
    push_cast
    refine add_le_add ?_ le_rfl
    apply one_div_le_one_div_of_le (by positivity)
    have hpe : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact (pow_le_pow_left₀ (by norm_num) hpe _).trans
      (pow_right_mono₀ (by linarith) (Nat.sub_le _ _))

private theorem frequency_exists_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → ℕ → Prop) (N : ℕ) :
    frequency (fun n => ∃ i ∈ s, P i n) N ≤ ∑ i ∈ s, frequency (P i) N := by
  classical
  induction s using Finset.induction with
  | empty => simp [frequency]
  | insert i s hi ih =>
    rw [sum_insert hi]
    refine (frequency_le_union (Q := P i) (R := fun n => ∃ i ∈ s, P i n) (fun n hn => ?_) N).trans
      (add_le_add le_rfl ih)
    obtain ⟨j, hj, hp⟩ := hn
    rcases mem_insert.mp hj with rfl | h
    · exact Or.inl hp
    · exact Or.inr ⟨j, h, hp⟩

private theorem frequency_clip_le (Y E N : ℕ) (hE : 2 ≤ E) (hN : 0 < N) :
    frequency (clippingFailure Y E) N ≤
      (2 * ((Y : ℝ) + 1)) / (2 : ℝ) ^ (E - 1) + (2 * ((Y : ℝ) + 1) + 1) / (N : ℝ) := by
  have hZero : frequency (fun n => n = 0) N ≤ 1 / (N : ℝ) := by
    have hs : (range N).filter (fun n => n = 0) ⊆ ({0} : Finset ℕ) := by
      intro n hn
      simpa using (mem_filter.mp hn).2
    have hc := card_le_card hs
    rw [card_singleton] at hc
    rw [frequency_eq_count, Nat.count_eq_card_filter_range]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
  have hEach (p : ℕ) (hp : p ∈ primesThrough Y) :
      frequency (fun n => p ^ E ∣ 2 * n ∨ p ^ E ∣ 2 * n + 1) N ≤
        2 * (1 / (2 : ℝ) ^ (E - 1) + 1 / (N : ℝ)) := by
    have hPr := (mem_filter.mp hp).2
    have hEven := frequency_cap_affine_upper N p E hPr hE hN false
    have hOdd := frequency_cap_affine_upper N p E hPr hE hN true
    simp only [Bool.false_eq_true, if_false, add_zero, if_true] at hEven hOdd
    have hUnion := frequency_le_union (Q := fun n => p ^ E ∣ 2 * n)
      (R := fun n => p ^ E ∣ 2 * n + 1) (fun n h => h) N
    linarith
  have hU := frequency_le_union (P := clippingFailure Y E) (Q := fun n => n = 0)
    (R := fun n => ∃ p ∈ primesThrough Y, p ^ E ∣ 2 * n ∨ p ^ E ∣ 2 * n + 1)
    (fun _ h => h) N
  have hSum := frequency_exists_le_sum (primesThrough Y)
    (fun p n => p ^ E ∣ 2 * n ∨ p ^ E ∣ 2 * n + 1) N
  have hEachSum := sum_le_sum hEach
  rw [sum_const, nsmul_eq_mul] at hEachSum
  have hC : ((primesThrough Y).card : ℝ) ≤ Y + 1 := by
    have hc := card_filter_le (s := range (Y + 1)) (p := Nat.Prime)
    rw [card_range] at hc
    exact_mod_cast hc
  have hB := mul_le_mul_of_nonneg_right hC
    (by positivity : 0 ≤ 2 * (1 / (2 : ℝ) ^ (E - 1) + 1 / (N : ℝ)))
  calc
    _ ≤ 1 / (N : ℝ) + ((Y : ℝ) + 1) * (2 * (1 / (2 : ℝ) ^ (E - 1) + 1 / (N : ℝ))) := by
      linarith
    _ = _ := by ring

theorem clipping_negligible (Y : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ᶠ N in atTop, frequency (clippingFailure Y E) N ≤ η := by
  have hPow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨k, hk1, hk⟩ := exists_lt_of_tendsto_atTop hPow 1 (4 * ((Y : ℝ) + 1) / η)
  have hBase : 2 * ((Y : ℝ) + 1) / (2 : ℝ) ^ k < η / 2 := by
    have hk' := (div_lt_iff₀ hη).mp hk
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)).mpr
    linarith
  refine ⟨k + 1, by omega, ?_⟩
  have hSmall := (const_div_nat_zero (2 * ((Y : ℝ) + 1) + 1)).eventually_lt
    (tendsto_const_nhds (x := η / 2)) (by positivity)
  filter_upwards [eventually_gt_atTop (0 : ℕ), hSmall] with N hN hLoss
  have h := frequency_clip_le Y (k + 1) N (by omega) hN
  rw [Nat.add_sub_cancel] at h
  linarith

theorem finite_prime_frequency (Y : ℕ) (P : ℝ → Prop) :
    ∃ δ, Tendsto (frequency (fun n => P (small logContribution Y n))) atTop (𝓝 δ) := by
  apply density_of_frequency_approximation
  intro η hη
  obtain ⟨E, hE, hClip⟩ := clipping_negligible Y η hη
  refine ⟨fun n => P (clipped Y E n), _, clipped_frequency Y E (by omega) P, ?_⟩
  filter_upwards [hClip] with N hN
  refine (frequency_abs_sub_le (fun n h => ?_) N).trans hN
  rw [clipped_matches Y E n h]

end A082957Capped

-- Source module CappedWindows.lean

namespace A082957Capped

open Finset Filter
open scoped BigOperators Topology
open A082957Analysis A082957Tail A082957Certificate A082957Signs A082957Windows

private theorem card_fin_filter_eq_count (M : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((univ : Finset (Fin M)).filter (fun n : Fin M => P n.val)).card = Nat.count P M := by
  rw [Nat.count_eq_card_filter_range]
  refine Finset.card_bij (fun n _ => n.val) ?_ ?_ ?_
  · intro n hn
    exact mem_filter.mpr ⟨mem_range.mpr n.isLt, (mem_filter.mp hn).2⟩
  · exact fun n _ m _ h => Fin.ext h
  · intro n hn
    have h := mem_filter.mp hn
    exact ⟨⟨n, mem_range.mp h.1⟩, mem_filter.mpr ⟨mem_univ _, h.2⟩, rfl⟩

private noncomputable def swapFn {α : Type*} (L R : α → Prop) [DecidablePred L]
    [DecidablePred R] (e : {a // L a} ≃ {a // R a}) (a : α) : α :=
  if h : L a then (e ⟨a, h⟩).val
  else if h : R a then (e.symm ⟨a, h⟩).val
  else a

private theorem swapFn_involutive {α : Type*} (L R : α → Prop) [DecidablePred L]
    [DecidablePred R] (disj : ∀ a, L a → ¬ R a) (e : {a // L a} ≃ {a // R a}) :
    Function.Involutive (swapFn L R e) := by
  intro a
  by_cases hL : L a
  · have hr : R (e ⟨a, hL⟩).val := (e ⟨a, hL⟩).2
    have hl : ¬ L (e ⟨a, hL⟩).val := fun h => disj _ h hr
    simp only [swapFn, dif_pos hL, dif_neg hl, dif_pos hr]
    exact congrArg (fun x : {x // L x} => x.val) (e.symm_apply_apply ⟨a, hL⟩)
  · by_cases hR : R a
    · have hl : L (e.symm ⟨a, hR⟩).val := (e.symm ⟨a, hR⟩).2
      simp only [swapFn, dif_neg hL, dif_pos hR, dif_pos hl]
      exact congrArg (fun x : {x // R x} => x.val) (e.apply_symm_apply ⟨a, hR⟩)
    · simp only [swapFn, dif_neg hL, dif_neg hR]

private def evenOne (p E : ℕ) (n : Fin (p ^ E)) : Prop := valuationSide p E n = .even 1
private def oddOne (p E : ℕ) (n : Fin (p ^ E)) : Prop := valuationSide p E n = .odd 1

private instance (p E : ℕ) : DecidablePred (evenOne p E) := fun _ => inferInstanceAs (Decidable (_ = _))
private instance (p E : ℕ) : DecidablePred (oddOne p E) := fun _ => inferInstanceAs (Decidable (_ = _))

private theorem even_odd_disj (p E : ℕ) (a : Fin (p ^ E)) :
    evenOne p E a → ¬ oddOne p E a := by
  unfold evenOne oddOne
  intro h₁ h₂
  rw [h₁] at h₂
  contradiction

private theorem even_odd_card (p E : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) (hE : 2 ≤ E) :
    Fintype.card {a // evenOne p E a} = Fintype.card {a // oddOne p E a} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  change ((univ : Finset (Fin (p ^ E))).filter (fun n : Fin (p ^ E) =>
      valuationSide p E n.val = .even 1)).card =
      (univ.filter (fun n : Fin (p ^ E) => valuationSide p E n.val = .odd 1)).card
  rw [card_fin_filter_eq_count (p ^ E) (fun n => valuationSide p E n = .even 1),
    card_fin_filter_eq_count (p ^ E) (fun n => valuationSide p E n = .odd 1),
    count_even_side_odd hp hp₂ (by decide) (by omega : 1 ≤ E),
    count_odd_side_odd hp hp₂ (by decide) (by omega : 1 ≤ E)]

private noncomputable def evenOddEquiv (p E : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2)
    (hE : 2 ≤ E) : {a // evenOne p E a} ≃ {a // oddOne p E a} :=
  Fintype.equivOfCardEq (even_odd_card p E hp hp₂ hE)

private noncomputable def sideFlip (p E : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2)
    (hE : 2 ≤ E) : Equiv.Perm (Fin (p ^ E)) :=
  (swapFn_involutive _ _ (even_odd_disj p E) (evenOddEquiv p E hp hp₂ hE)).toPerm

private theorem sideFlip_even (p E : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) (hE : 2 ≤ E)
    {n : Fin (p ^ E)} (hn : evenOne p E n) :
    oddOne p E (sideFlip p E hp hp₂ hE n) := by
  change oddOne p E (swapFn _ _ (evenOddEquiv p E hp hp₂ hE) n)
  rw [swapFn, dif_pos hn]
  exact (evenOddEquiv p E hp hp₂ hE ⟨n, hn⟩).2

private theorem sideFlip_odd (p E : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) (hE : 2 ≤ E)
    {n : Fin (p ^ E)} (hn : oddOne p E n) :
    evenOne p E (sideFlip p E hp hp₂ hE n) := by
  have hn' : ¬ evenOne p E n := fun h => even_odd_disj p E n h hn
  change evenOne p E (swapFn _ _ (evenOddEquiv p E hp hp₂ hE) n)
  rw [swapFn, dif_neg hn', dif_pos hn]
  exact ((evenOddEquiv p E hp hp₂ hE).symm ⟨n, hn⟩).2

private theorem active_ratio (p E : ℕ) (hp : p.Prime) (hp₂ : p ≠ 2) (hE : 2 ≤ E) :
    (((univ : Finset (Fin (p ^ E))).filter (fun n => evenOne p E n ∨ oddOne p E n)).card : ℝ) /
      (2 * ((p ^ E : ℕ) : ℝ)) = activationHalf p := by
  have hc : ((univ : Finset (Fin (p ^ E))).filter
      (fun n => evenOne p E n ∨ oddOne p E n)).card = 2 * ((p - 1) * p ^ (E - 2)) := by
    change ((univ : Finset (Fin (p ^ E))).filter (fun n : Fin (p ^ E) =>
        valuationSide p E n.val = .even 1 ∨ valuationSide p E n.val = .odd 1)).card = _
    rw [card_fin_filter_eq_count (p ^ E) (fun n =>
      valuationSide p E n = .even 1 ∨ valuationSide p E n = .odd 1),
      count_or (fun n h₁ h₂ => by rw [h₁] at h₂; contradiction),
      count_even_side_odd hp hp₂ (by decide) (by omega : 1 ≤ E),
      count_odd_side_odd hp hp₂ (by decide) (by omega : 1 ≤ E),
      if_neg (by omega : 1 ≠ E)]
    rw [show E - 1 - 1 = E - 2 by omega, two_mul]
  rw [hc]
  have hp1 : 1 ≤ p := (show 1 ≤ 2 by decide).trans hp.two_le
  push_cast [Nat.cast_sub hp1]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hPow : (p : ℝ) ^ E = (p : ℝ) ^ (E - 2) * (p : ℝ)^2 := by
    rw [← pow_add, Nat.sub_add_cancel hE]
  rw [hPow, activationHalf]
  field_simp

private theorem capped_crt_frequency (Y E : ℕ) (hE : 0 < E) (P : ℝ → Prop) [DecidablePred P]
    (coords : Fin (modulus Y E) ≃ ((p : primesThrough Y) → Fin (p.val ^ E)))
    (hCoords : ∀ n p, (coords n p).val = n.val % p.val ^ E) :
    frequency (fun n => P (clipped Y E n)) (modulus Y E) =
    (((univ : Finset ((p : primesThrough Y) → Fin (p.val ^ E))).filter
      (fun r : (p : primesThrough Y) → Fin (p.val ^ E) =>
        P (∑ p : primesThrough Y, sideScore p (valuationSide p E (r p).val)))).card : ℝ) /
      (Fintype.card ((p : primesThrough Y) → Fin (p.val ^ E)) : ℝ) := by
  classical
  let Q (r : (p : primesThrough Y) → Fin (p.val ^ E)) : Prop :=
    P (∑ p : primesThrough Y, sideScore p (valuationSide p E (r p).val))
  have hperiod (n : Fin (modulus Y E)) :
      clipped Y E n = ∑ p : primesThrough Y, sideScore p (valuationSide p E (coords n p).val) := by
    unfold clipped
    rw [← Finset.sum_attach (primesThrough Y) (fun p => sideScore p (valuationSide p E n))]
    change (∑ p : primesThrough Y, sideScore p (valuationSide p E n)) = _
    apply sum_congr rfl
    intro p hp
    rw [hCoords]
    exact congrArg (sideScore p) (valuationSide_modeq hE
      (by simp [Nat.ModEq, Nat.mod_mod] : n.val ≡ n.val % p.val ^ E [MOD p.val ^ E]))
  have hTest (n : Fin (modulus Y E)) : P (clipped Y E n) ↔ Q (coords n) := by
    simp only [Q, hperiod]
  have hCard := Fintype.card_congr (coords.subtypeEquiv hTest)
  rw [Fintype.card_subtype, Fintype.card_subtype,
    card_fin_filter_eq_count (modulus Y E) (fun n => P (clipped Y E n))] at hCard
  have hDenom := Fintype.card_congr coords
  rw [Fintype.card_fin] at hDenom
  rw [frequency_eq_count, hCard, hDenom]

private noncomputable def width (B : ℕ) : ℝ :=
  Real.log (valuationRatio (B + 2) 1)

private theorem width_pos (B : ℕ) : 0 < width B := by
  unfold width
  apply Real.log_pos
  simp only [valuationRatio, show 1 + 1 = 2 by decide, sum_range_succ, sum_range_zero, pow_zero,
    pow_one, zero_add]
  linarith [show 0 < (((B + 2 : ℕ) : ℝ))⁻¹ by positivity]

private theorem width_le (B p : ℕ) (hp : p.Prime) (hB : p ∈ smallOddPrimes B) :
    width B ≤ Real.log (valuationRatio p 1) := by
  unfold width
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (valuationRatio_ge_one _ _))
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hBP : (p : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show p ≤ B + 2 by have := mem_range.mp (mem_filter.mp hB).1; omega)
  have hInv := one_div_le_one_div_of_le hpR hBP
  simp only [valuationRatio, show 1 + 1 = 2 by decide, sum_range_succ, sum_range_one, pow_zero, pow_one,
    ← one_div]
  linarith

theorem capped_window_bound (B Y E k : ℕ) (hY : B ≤ Y) (hE : 2 ≤ E)
    (coords : Fin (modulus Y E) ≃ ((p : primesThrough Y) → Fin (p.val ^ E)))
    (hCoords : ∀ n p, (coords n p).val = n.val % p.val ^ E) :
    frequency (fun n => |clipped Y E n| ≤ width B / 2) (modulus Y E) ≤
      2 ^ (2 * k) * (∏ p ∈ smallOddPrimes B, (1 - activationHalf p)) +
        ((2 * k).choose k : ℝ) / 2 ^ (2 * k) := by
  classical
  let ι := primesThrough Y
  let α (p : ι) := Fin (p.val ^ E)
  have hprime (p : ι) : p.val.Prime := (mem_filter.mp p.2).2
  have hNeTwo {p : ℕ} (h : p ∈ smallOddPrimes B) : p ≠ 2 :=
    ne_of_gt (mem_filter.mp h).2.2
  letI instNE (p : ι) : Nonempty (α p) := ⟨⟨0, pow_pos (hprime p).pos _⟩⟩
  let value (p : ι) (n : α p) := sideScore p (valuationSide p E n.val)
  let active (p : ι) (n : α p) : Prop :=
    p.val ∈ smallOddPrimes B ∧ (evenOne p E n ∨ oddOne p E n)
  letI instAct (p : ι) : DecidablePred (active p) := fun n =>
    inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))
  let flip (p : ι) : Equiv.Perm (α p) :=
    if hp : p.val ∈ smallOddPrimes B then sideFlip p E (hprime p) (hNeTwo hp) hE
    else Equiv.refl _
  let w (p : ι) := Real.log (valuationRatio p 1)
  have hw (p : ι) (n : α p) (hn : active p n) : width B ≤ w p :=
    width_le B p (hprime p) hn.1
  have hEven (p : ι) (n : α p) (hn : evenOne p E n) : value p n = -w p := by
    unfold evenOne at hn
    simp [value, hn, sideScore, w]
  have hOdd (p : ι) (n : α p) (hn : oddOne p E n) : value p n = w p := by
    unfold oddOne at hn
    simp [value, hn, sideScore, w]
  have hPolarity (p : ι) (n : α p) (hn : active p n) : value p n = w p ∨ value p n = -w p :=
    hn.2.elim (fun h => Or.inr (hEven p n h)) (fun h => Or.inl (hOdd p n h))
  have hFlip (p : ι) (n : α p) (hn : active p n) : value p (flip p n) = -value p n := by
    have hp := hn.1
    dsimp only [flip]
    rw [dif_pos hp]
    rcases hn.2 with hn | hn
    · rw [hOdd _ _ (sideFlip_even p E (hprime p) (hNeTwo hp) hE hn), hEven _ _ hn, neg_neg]
    · rw [hEven _ _ (sideFlip_odd p E (hprime p) (hNeTwo hp) hE hn), hOdd _ _ hn]
  have hFactor (p : ι) :
      1 - (((univ : Finset (α p)).filter (active p)).card : ℝ) / (2 * Fintype.card (α p)) =
        if p.val ∈ smallOddPrimes B then 1 - activationHalf p else 1 := by
    by_cases hp : p.val ∈ smallOddPrimes B
    · rw [if_pos hp]
      have hs : (univ : Finset (α p)).filter (active p) =
          univ.filter (fun n => evenOne p E n ∨ oddOne p E n) := by
        ext n
        simp [active, hp]
      rw [hs]
      change 1 - _ / (2 * (Fintype.card (Fin (p.val ^ E)) : ℝ)) = _
      rw [Fintype.card_fin, active_ratio _ _ (hprime p) (hNeTwo hp) hE]
    · simp [active, hp]
  have hProd :
      (∏ p : ι, (1 - (((univ : Finset (α p)).filter (active p)).card : ℝ) /
        (2 * Fintype.card (α p)))) = ∏ p ∈ smallOddPrimes B, (1 - activationHalf p) := by
    simp_rw [hFactor]
    change (∏ p : primesThrough Y,
      if p.val ∈ smallOddPrimes B then 1 - activationHalf p.val else 1) = _
    rw [Finset.univ_eq_attach, Finset.prod_attach (primesThrough Y) (fun p : ℕ =>
      if p ∈ smallOddPrimes B then 1 - activationHalf p else 1), ← Finset.prod_filter]
    have hSub : smallOddPrimes B ⊆ primesThrough Y := by
      intro p hp
      have hpp := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hpp.1; omega), hpp.2.1⟩
    have hf : (primesThrough Y).filter (· ∈ smallOddPrimes B) = smallOddPrimes B := by
      ext p
      rw [mem_filter]
      exact and_iff_right_of_imp (fun hp => hSub hp)
    rw [hf]
  have hWindow := area_window_bound value active flip w (width B) (width_pos B)
    hw hPolarity hFlip k (-(width B / 2)) (width B / 2) (by linarith [width_pos B])
  rw [hProd] at hWindow
  rw [capped_crt_frequency Y E (by omega) (fun x => |x| ≤ width B / 2) coords hCoords]
  simpa only [abs_le] using hWindow

private theorem remove_clipping_for_window (Y E N : ℕ) (r : ℝ) :
    frequency (fun n => |small logContribution Y n| ≤ r) N ≤
      frequency (fun n => |clipped Y E n| ≤ r) N + frequency (clippingFailure Y E) N := by
  apply frequency_le_union
  intro n hn
  by_cases h : clippingFailure Y E n
  · exact Or.inr h
  · exact Or.inl (by rwa [clipped_matches Y E n h])

set_option maxHeartbeats 1200000 in
theorem uncapped_margin
    (hCrt : ∀ Y E, ∃ coords : Fin (modulus Y E) ≃ ((p : primesThrough Y) → Fin (p.val ^ E)),
      ∀ n p, (coords n p).val = n.val % p.val ^ E) :
    ∀ η > 0, ∃ ε > 0, ∃ Y₀ : ℕ, ∀ Y ≥ Y₀, ∀ᶠ N in atTop,
      frequency (fun n => |small logContribution Y n| ≤ 2 * ε) N ≤ η := by
  intro η hη
  obtain ⟨k, hk⟩ := exists_even_sign_ratio_lt (η / 8) (by positivity)
  obtain ⟨B, hB⟩ := exists_small_activation_product (2 * k) (η / 8) (by positivity)
  refine ⟨width B / 4, div_pos (width_pos B) (by norm_num), B, fun Y hY => ?_⟩
  obtain ⟨E, hE, hClip⟩ := clipping_negligible Y (η / 4) (by positivity)
  obtain ⟨coords, hCoords⟩ := hCrt Y E
  have hBound := capped_window_bound B Y E k hY hE coords hCoords
  have hPred := clipped_frequency Y E (by omega : 0 < E) (fun x : ℝ => |x| ≤ width B / 2)
  have hBound' : frequency (fun n => |clipped Y E n| ≤ width B / 2) (modulus Y E) < η / 2 :=
    hBound.trans_lt (by linarith [hB, hk])
  have hWin := hPred.eventually_lt (tendsto_const_nhds (x := η / 2)) hBound'
  filter_upwards [hClip, hWin] with N hFailure hSmall
  change frequency (fun n => |small logContribution Y n| ≤ 2 * (width B / 4)) N ≤ η
  rw [show 2 * (width B / 4) = width B / 2 by ring]
  linarith [remove_clipping_for_window Y E N (width B / 2)]

theorem divisor_comparison_density
    (hCrt : ∀ Y E, ∃ coords : Fin (modulus Y E) ≃ ((p : primesThrough Y) → Fin (p.val ^ E)),
      ∀ n p, (coords n p).val = n.val % p.val ^ E) :
    ∃ δ, Tendsto (frequency (fun n => 1 ≤ n ∧
      (∑ d ∈ (2 * n).divisors, d) < ∑ d ∈ (2 * n + 1).divisors, d))
      atTop (𝓝 δ) := by
  have h := density_of_approximation (full logContribution) (small logContribution)
    A082957Bridge.threshold A082957Bridge.threshold_limit
    (fun Y => finite_prime_frequency Y ((0 : ℝ) < ·))
    (uniform_tail logContribution A082957Bridge.contribution_bound A082957Bridge.contribution_zero)
    (uncapped_margin hCrt)
  obtain ⟨δ, hδ⟩ := h
  refine ⟨δ, ?_⟩
  have hEq := funext (fun n => propext (A082957Bridge.compare_divisor_sums n))
  rw [← hEq]
  exact hδ

theorem residue_coordinates (Y E : ℕ) :
    ∃ coords : Fin (modulus Y E) ≃ ((p : primesThrough Y) → Fin (p.val ^ E)),
      ∀ n p, (coords n p).val = n.val % p.val ^ E := by
  let m (p : primesThrough Y) := p.val ^ E
  have hp (p : primesThrough Y) : p.val.Prime := (mem_filter.mp p.2).2
  have hm (p : primesThrough Y) : 0 < m p := pow_pos (hp p).pos _
  have hc : Pairwise (fun p q : primesThrough Y => (m p).Coprime (m q)) := by
    intro p q h
    exact Nat.coprime_pow_primes _ _ (hp p) (hp q) (fun he => h (Subtype.ext he))
  have hM : modulus Y E = ∏ p : primesThrough Y, m p := by
    unfold modulus
    rw [Finset.univ_eq_attach]
    exact (Finset.prod_attach (primesThrough Y) (fun p : ℕ => p ^ E)).symm
  let adjust := Equiv.cast (congrArg Fin hM)
  refine ⟨adjust.trans (residuePi m hm hc), fun n p => ?_⟩
  have hCast {a b : ℕ} (h : a = b) (x : Fin a) :
      ((Equiv.cast (congrArg Fin h)) x).val = x.val := by
    cases h
    rfl
  rw [Equiv.trans_apply, residuePi_val]
  exact congrArg (fun r : ℕ => r % p.val ^ E) (hCast hM n)

theorem divisor_comparison_has_density :
    ∃ δ, Tendsto (frequency (fun n => 1 ≤ n ∧
      (∑ d ∈ (2 * n).divisors, d) < ∑ d ∈ (2 * n + 1).divisors, d))
      atTop (𝓝 δ) :=
  divisor_comparison_density residue_coordinates

end A082957Capped

namespace A082957Certificate

open Finset

def logCoordinate (z : ℚ) : ℚ := (z - 1) / (z + 1)

def logPolynomial (x : ℚ) : ℚ :=
  ∑ i ∈ range 8, x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℚ)

def logLower (z : ℚ) : ℚ := 2 * logPolynomial (logCoordinate z)

def logUpper (z : ℚ) : ℚ := logLower z + 3 * logCoordinate z ^ 17

theorem log_interval {z : ℚ} (h₁ : 1 ≤ z) (h₂ : z ≤ 2) :
    ((logLower z : ℚ) : ℝ) ≤ Real.log (z : ℝ) ∧
      Real.log (z : ℝ) ≤ ((logUpper z : ℚ) : ℝ) := by
  let x : ℝ := (logCoordinate z : ℝ)
  have hx : x = ((z : ℝ) - 1) / ((z : ℝ) + 1) := by simp [x, logCoordinate]
  have hr₁ : 1 ≤ (z : ℝ) := by exact_mod_cast h₁
  have hr₂ : (z : ℝ) ≤ 2 := by exact_mod_cast h₂
  have hpos : 0 < (z : ℝ) + 1 := by linarith
  have hx₀ : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (by linarith) hpos.le
  have hx₃ : x ≤ 1 / 3 := by
    rw [hx, div_le_iff₀ hpos]
    linarith
  have hx₁ : x < 1 := by linarith
  have hratio : (1 + x) / (1 - x) = (z : ℝ) := by
    apply (div_eq_iff (by linarith : 1 - x ≠ 0)).2
    rw [hx]
    field_simp [hpos.ne']
    ring
  have hpoly : (logPolynomial (logCoordinate z) : ℝ) =
      ∑ i ∈ range 8, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) := by
    simp [logPolynomial, x]
  have hlo := Real.sum_range_le_log_div hx₀ hx₁ 8
  have hhi := Real.log_div_le_sum_range_add hx₀ hx₁ 8
  rw [hratio, ← hpoly] at hlo hhi
  have hsq : x ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hx₀ hx₃ 2
  have htail : x ^ 17 / (1 - x ^ 2) ≤ 3 / 2 * x ^ 17 := by
    calc
      _ ≤ x ^ 17 / (2 / 3) :=
        div_le_div_of_nonneg_left (pow_nonneg hx₀ _) (by norm_num) (by nlinarith)
      _ = _ := by ring
  change 1 / 2 * Real.log (z : ℝ) ≤
    (logPolynomial (logCoordinate z) : ℝ) + x ^ 17 / (1 - x ^ 2) at hhi
  simp only [logLower, logUpper, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  change 2 * (logPolynomial (logCoordinate z) : ℝ) ≤ Real.log (z : ℝ) ∧
    Real.log (z : ℝ) ≤ 2 * (logPolynomial (logCoordinate z) : ℝ) + 3 * x ^ 17
  exact ⟨by linarith, by linarith⟩

def positiveShift (grid : ℕ) (z : ℚ) : ℤ := ⌊grid * logLower z⌋

def negativeShift (grid : ℕ) (z : ℚ) : ℤ := ⌊-(grid * logUpper z)⌋

theorem positiveShift_le {grid : ℕ} (hg : 0 < grid) {z : ℚ} (h₁ : 1 ≤ z) (h₂ : z ≤ 2) :
    (positiveShift grid z : ℝ) / grid ≤ Real.log (z : ℝ) := by
  have h := Int.floor_le ((grid : ℚ) * logLower z)
  have hc : (positiveShift grid z : ℝ) ≤ (grid : ℝ) * (logLower z : ℝ) := by
    unfold positiveShift
    exact_mod_cast h
  have hgrid : (0 : ℝ) < grid := by exact_mod_cast hg
  apply (div_le_iff₀ hgrid).2
  calc
    _ ≤ (grid : ℝ) * (logLower z : ℝ) := hc
    _ ≤ (grid : ℝ) * Real.log (z : ℝ) :=
      mul_le_mul_of_nonneg_left (log_interval h₁ h₂).1 hgrid.le
    _ = _ := mul_comm _ _

theorem negativeShift_le {grid : ℕ} (hg : 0 < grid) {z : ℚ} (h₁ : 1 ≤ z) (h₂ : z ≤ 2) :
    (negativeShift grid z : ℝ) / grid ≤ -Real.log (z : ℝ) := by
  have h := Int.floor_le (-((grid : ℚ) * logUpper z))
  have hc : (negativeShift grid z : ℝ) ≤ -((grid : ℝ) * (logUpper z : ℝ)) := by
    unfold negativeShift
    exact_mod_cast h
  have hgrid : (0 : ℝ) < grid := by exact_mod_cast hg
  apply (div_le_iff₀ hgrid).2
  calc
    _ ≤ -((grid : ℝ) * (logUpper z : ℝ)) := hc
    _ ≤ -((grid : ℝ) * Real.log (z : ℝ)) :=
      neg_le_neg (mul_le_mul_of_nonneg_left (log_interval h₁ h₂).2 hgrid.le)
    _ = _ := by ring

end A082957Certificate

namespace A082957Certificate

def valuationCapRat (p : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1)

theorem valuationCapRat_cast (p : ℕ) :
    (valuationCapRat p : ℝ) = (p : ℝ) / ((p : ℝ) - 1) := by
  simp [valuationCapRat]

theorem valuationCapRat_range {p : ℕ} (hp : 2 ≤ p) :
    1 ≤ valuationCapRat p ∧ valuationCapRat p ≤ 2 := by
  have hlo : 1 ≤ (valuationCapRat p : ℝ) := by
    rw [valuationCapRat_cast]
    exact (valuationRatio_ge_one p 0).trans (valuationRatio_le_cap hp 0)
  have hhi : (valuationCapRat p : ℝ) ≤ 2 := by
    rw [valuationCapRat_cast]
    exact valuationCap_le_two hp
  exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩

def lowerValuationShift (grid p E : ℕ) (negative : Bool) (e : ℕ) : ℤ :=
  if negative then
    negativeShift grid (if e = E then valuationCapRat p else valuationRatioRat p e)
  else positiveShift grid (valuationRatioRat p e)

theorem lowerValuationShift_sound {grid p E m e : ℕ} (hg : 0 < grid) (hp : p.Prime)
    (hm : m ≠ 0) (hv : cappedVal p E m = e) (negative : Bool) :
    (lowerValuationShift grid p E negative e : ℝ) / grid ≤
      if negative then -Real.log (valuationRatio p (padicValNat p m))
      else Real.log (valuationRatio p (padicValNat p m)) := by
  have hmin := (cappedVal_eq_min hp hm).symm.trans hv
  have hRatio := valuationRatioRat_range hp.two_le e
  cases negative with
  | false =>
    simp only [lowerValuationShift, Bool.false_eq_true, ↓reduceIte]
    have h := positiveShift_le hg hRatio.1 hRatio.2
    rw [valuationRatioRat_cast] at h
    exact h.trans (Real.log_le_log (zero_lt_one.trans_le (valuationRatio_ge_one p e))
      (valuationRatio_mono p (by omega)))
  | true =>
    rw [lowerValuationShift]
    simp only [↓reduceIte]
    by_cases hE : e = E
    · rw [if_pos hE]
      have hRange := valuationCapRat_range hp.two_le
      have h := negativeShift_le hg hRange.1 hRange.2
      rw [valuationCapRat_cast] at h
      exact h.trans (neg_le_neg (Real.log_le_log
        (zero_lt_one.trans_le (valuationRatio_ge_one p _)) (valuationRatio_le_cap hp.two_le _)))
    · rw [if_neg hE]
      have he : e = padicValNat p m := by omega
      have h := negativeShift_le hg hRatio.1 hRatio.2
      rw [valuationRatioRat_cast] at h
      rwa [← he]

def gridShift (grid p E : ℕ) (reverse : Bool) : ValuationSide → ℤ
  | .unit => 0
  | .even e => lowerValuationShift grid p E (!reverse) e
  | .odd e => lowerValuationShift grid p E reverse e

noncomputable def signedContribution (reverse : Bool) (p n : ℕ) : ℝ :=
  if reverse then -logContribution p n else logContribution p n

theorem gridShift_sound {grid p E n : ℕ} (hg : 0 < grid) (hp : p.Prime)
    (hn : 0 < n) (reverse : Bool) :
    (gridShift grid p E reverse (valuationSide p E n) : ℝ) / grid ≤
      signedContribution reverse p n := by
  have hEven : 2 * n ≠ 0 := by omega
  have hOdd : 2 * n + 1 ≠ 0 := by omega
  by_cases he : p ∣ 2 * n
  · have ho : ¬p ∣ 2 * n + 1 := fun h => not_dvd_both hp he h
    have hzero : padicValNat p (2 * n + 1) = 0 := padicValNat.eq_zero_of_not_dvd ho
    have h := lowerValuationShift_sound hg hp hEven
      (rfl : cappedVal p E (2 * n) = cappedVal p E (2 * n)) (!reverse)
    cases reverse <;> simpa [valuationSide, gridShift, signedContribution, logContribution, he,
      hzero, valuationRatio_zero] using h
  · have hzero : padicValNat p (2 * n) = 0 := padicValNat.eq_zero_of_not_dvd he
    by_cases ho : p ∣ 2 * n + 1
    · have h := lowerValuationShift_sound hg hp hOdd
        (rfl : cappedVal p E (2 * n + 1) = cappedVal p E (2 * n + 1)) reverse
      cases reverse <;> simpa [valuationSide, gridShift, signedContribution, logContribution,
        he, ho, hzero, valuationRatio_zero] using h
    · have hzero' : padicValNat p (2 * n + 1) = 0 := padicValNat.eq_zero_of_not_dvd ho
      simp [valuationSide, gridShift, signedContribution, logContribution, he, ho, hzero,
        hzero', valuationRatio_zero]

end A082957Certificate

namespace A082957Packing

def trialPrime (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range' 2 (p.sqrt - 1)).all fun d => decide (¬d ∣ p)

theorem trialPrime_iff (p : ℕ) : trialPrime p = true ↔ p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [trialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  apply and_congr_right
  intro _
  have hrange (d : ℕ) : d ∈ List.range' 2 (p.sqrt - 1) ↔ 2 ≤ d ∧ d ≤ p.sqrt := by
    rw [List.mem_range'_1]
    omega
  simp_rw [hrange, and_imp]

end A082957Packing

namespace A082957Packing

abbrev Law := List (ℕ × ℕ)

/-- Encode degree and multiplicity pairs as digits in a natural number. -/
def pack (base : ℕ) : Law → ℕ
  | [] => 0
  | (degree, count) :: rest => count * base ^ degree + pack base rest

def convolve (xs ys : Law) : Law :=
  xs.flatMap fun x => ys.map fun y => (x.1 + y.1, x.2 * y.2)

def jointLaw : List Law → Law
  | [] => [(0, 1)]
  | law :: laws => convolve law (jointLaw laws)

def countAtLeast (t : ℕ) : Law → ℕ
  | [] => 0
  | (degree, count) :: rest => (if t ≤ degree then count else 0) + countAtLeast t rest

def packBelow (base t : ℕ) : Law → ℕ
  | [] => 0
  | (degree, count) :: rest =>
      (if degree < t then count * base ^ degree else 0) + packBelow base t rest

def packFrom (base t : ℕ) : Law → ℕ
  | [] => 0
  | (degree, count) :: rest =>
      (if t ≤ degree then count * base ^ (degree - t) else 0) + packFrom base t rest

theorem pack_append (base : ℕ) (xs ys : Law) :
    pack base (xs ++ ys) = pack base xs + pack base ys := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    simp [pack, ih, add_assoc]

theorem pack_translate (base : ℕ) (x : ℕ × ℕ) (ys : Law) :
    pack base (ys.map fun y => (x.1 + y.1, x.2 * y.2)) =
      (x.2 * base ^ x.1) * pack base ys := by
  induction ys with
  | nil => simp [pack]
  | cons y ys ih =>
    rcases y with ⟨degree, count⟩
    simp only [List.map_cons, pack, ih, pow_add, Nat.mul_add]
    ring

theorem pack_convolve (base : ℕ) (xs ys : Law) :
    pack base (convolve xs ys) = pack base xs * pack base ys := by
  induction xs with
  | nil => simp [convolve, pack]
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    simp [convolve, pack_append, pack, add_mul] at ih ⊢
    rw [ih]
    exact congrArg (fun k => k + pack base xs * pack base ys) (pack_translate base (degree, count) ys)

theorem pack_split (base t : ℕ) (xs : Law) :
    pack base xs = packBelow base t xs + base ^ t * packFrom base t xs := by
  induction xs with
  | nil => simp [pack, packBelow, packFrom]
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    by_cases ht : t ≤ degree
    · have h : base ^ degree = base ^ t * base ^ (degree - t) := by
        rw [← pow_add, Nat.add_sub_of_le ht]
      simp only [pack, packBelow, packFrom, ht, Nat.not_lt.mpr ht, if_true, if_false, zero_add]
      rw [h, ih]
      ring
    · simp only [pack, packBelow, packFrom, ht, Nat.lt_of_not_ge ht, if_true, if_false, zero_add]
      rw [ih]
      ring

theorem packBelow_le (base t : ℕ) (hb : 0 < base) (xs : Law) :
    packBelow base (t + 1) xs ≤ pack 1 xs * base ^ t := by
  induction xs with
  | nil => simp [packBelow, pack]
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    simp only [packBelow, pack, one_pow, mul_one, add_mul]
    apply Nat.add_le_add _ ih
    split
    · rename_i h
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb (by omega))
    · exact Nat.zero_le _

theorem packBelow_lt (base t : ℕ) (hb : 0 < base) (xs : Law) (hm : pack 1 xs < base) :
    packBelow base t xs < base ^ t := by
  cases t with
  | zero =>
    induction xs with
    | nil => simp [packBelow]
    | cons x xs ih =>
      rcases x with ⟨degree, count⟩
      simp [pack, one_pow] at hm
      exact (by simpa [packBelow] using ih (by omega))
  | succ t =>
    simpa [pow_succ, mul_comm] using
      (packBelow_le base t hb xs).trans_lt
        (Nat.mul_lt_mul_of_pos_right hm (pow_pos hb t))

theorem countAtLeast_le (t : ℕ) (xs : Law) : countAtLeast t xs ≤ pack 1 xs := by
  induction xs with
  | nil => simp [countAtLeast, pack]
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    simp only [countAtLeast, pack, one_pow, mul_one]
    exact Nat.add_le_add (by split <;> omega) ih

theorem packFrom_modEq (base t : ℕ) (hb : 1 ≤ base) (xs : Law) :
    packFrom base t xs ≡ countAtLeast t xs [MOD base - 1] := by
  have hb₁ : base ≡ 1 [MOD base - 1] := (Nat.modEq_iff_dvd' hb).mpr dvd_rfl |>.symm
  induction xs with
  | nil => exact Nat.ModEq.refl 0
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    by_cases ht : t ≤ degree
    · simpa [packFrom, countAtLeast, ht] using
        ((Nat.ModEq.refl count).mul (hb₁.pow (degree - t))).add ih
    · simpa [packFrom, countAtLeast, ht] using ih

theorem decode (base t : ℕ) (xs : Law) (hm : pack 1 xs < base - 1) :
    (pack base xs / base ^ t) % (base - 1) = countAtLeast t xs := by
  have hp : 0 < base := by omega
  rw [pack_split, Nat.add_mul_div_left _ _ (pow_pos hp t),
    Nat.div_eq_of_lt (packBelow_lt base t hp xs (by omega)), zero_add]
  have h := packFrom_modEq base t (by omega) xs
  change packFrom base t xs % (base - 1) = countAtLeast t xs % (base - 1) at h
  simpa only [Nat.mod_eq_of_lt ((countAtLeast_le t xs).trans_lt hm)] using h

def packedStep (bits current : ℕ) : Law → ℕ
  | [] => 0
  | (degree, count) :: rest =>
      ((current * count) <<< (bits * degree)) + packedStep bits current rest

def packedJoint (bits : ℕ) : List Law → ℕ
  | [] => 1
  | law :: laws => packedStep bits (packedJoint bits laws) law

theorem packedStep_eq (bits current : ℕ) (xs : Law) :
    packedStep bits current xs = pack (2 ^ bits) xs * current := by
  induction xs with
  | nil => simp [packedStep, pack]
  | cons x xs ih =>
    rcases x with ⟨degree, count⟩
    simp only [packedStep, pack, Nat.shiftLeft_eq_mul_pow, pow_mul, ih]
    ring

theorem packedJoint_eq (bits : ℕ) (laws : List Law) :
    packedJoint bits laws = pack (2 ^ bits) (jointLaw laws) := by
  induction laws with
  | nil => simp [packedJoint, jointLaw, pack]
  | cons law laws ih => simp [packedJoint, jointLaw, packedStep_eq, pack_convolve, ih]

def query (bits code t : ℕ) : ℕ := (code >>> (bits * t)) % (2 ^ bits - 1)

theorem query_joint (bits : ℕ) (laws : List Law) (t : ℕ)
    (hm : pack 1 (jointLaw laws) < 2 ^ bits - 1) :
    query bits (packedJoint bits laws) t = countAtLeast t (jointLaw laws) := by
  simpa [query, packedJoint_eq, Nat.shiftRight_eq_div_pow, pow_mul] using
    decode (2 ^ bits) t (jointLaw laws) hm

end A082957Packing

namespace A082957Packing

def compressThresholds : List ℕ → List (ℕ × ℕ)
  | [] => []
  | t :: ts =>
      match compressThresholds ts with
      | [] => [(t, 1)]
      | (u, c) :: unused =>
          if t = u then (u, c + 1) :: unused else (t, 1) :: (u, c) :: unused

theorem compressThresholds_eq (ts : List ℕ) (f : ℕ → ℕ) :
    ((compressThresholds ts).map fun p => f p.1 * p.2).sum = (ts.map f).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases h : compressThresholds ts with
    | nil =>
      simp only [h, List.map_nil, List.sum_nil] at ih
      simp [compressThresholds, h, ← ih]
    | cons u us =>
      rcases u with ⟨u, c⟩
      by_cases hu : t = u
      · subst u
        simp only [h, List.map_cons, List.sum_cons] at ih
        simp only [compressThresholds, h, if_true, List.map_cons, List.sum_cons, Nat.mul_succ]
        omega
      · simp only [h, List.map_cons, List.sum_cons] at ih
        simp [compressThresholds, h, hu, ← ih]

def thresholdCount (ts : List ℕ) (j : ℕ) : ℕ := (ts.filter (· ≤ j)).length

theorem weightedThresholdCount (ts : List ℕ) (j count : ℕ) :
    (ts.map fun t => if t ≤ j then count else 0).sum = count * thresholdCount ts j := by
  induction ts with
  | nil => simp [thresholdCount]
  | cons t ts ih =>
    by_cases h : t ≤ j
    · simp [thresholdCount, h, ih, Nat.mul_add, add_comm]
    · simp [thresholdCount, h, ih]

theorem sum_countAtLeast (ts : List ℕ) (law : Law) :
    (ts.map fun t => countAtLeast t law).sum =
      (law.map fun x => x.2 * thresholdCount ts x.1).sum := by
  induction law with
  | nil => simp [countAtLeast]
  | cons x xs ih =>
    rcases x with ⟨j, count⟩
    simp only [countAtLeast, List.sum_map_add, weightedThresholdCount, ih, List.map_cons,
      List.sum_cons]

theorem pack_one_jointLaw (laws : List Law) :
    pack 1 (jointLaw laws) = (laws.map (pack 1)).prod := by
  induction laws with
  | nil => simp [jointLaw, pack]
  | cons law ls ih => simp [jointLaw, pack_convolve, ih]

def massCount (law : Law) : ℕ := (law.map Prod.snd).sum

theorem massCount_eq (law : Law) : massCount law = pack 1 law := by
  induction law with
  | nil => rfl
  | cons a law ih =>
    rcases a with ⟨degree, count⟩
    simpa only [massCount, List.map_cons, List.sum_cons, pack, one_pow, mul_one] using
      congrArg (count + ·) ih

def radixBits (laws : List Law) : ℕ := (((laws.map massCount).prod + 1).log2 + 1)

theorem radixBits_lt (laws : List Law) : pack 1 (jointLaw laws) < 2 ^ radixBits laws - 1 := by
  rw [pack_one_jointLaw]
  have h := Nat.lt_log2_self (n := (laws.map (pack 1)).prod + 1)
  have hmap : laws.map massCount = laws.map (pack 1) :=
    List.map_congr_left (fun law _ => massCount_eq law)
  unfold radixBits
  rw [hmap]
  omega

def weightedPackedCount (laws : List Law) (thresholds : List ℕ) : ℕ :=
  let bits := radixBits laws
  let code := packedJoint bits laws
  ((compressThresholds thresholds).map fun p => query bits code p.1 * p.2).sum

theorem weightedPackedCount_eq (laws : List Law) (thresholds : List ℕ) :
    weightedPackedCount laws thresholds =
      ((jointLaw laws).map (fun x => x.2 * thresholdCount thresholds x.1)).sum := by
  unfold weightedPackedCount
  dsimp only
  rw [compressThresholds_eq]
  rw [← sum_countAtLeast thresholds (jointLaw laws)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  exact query_joint (radixBits laws) laws t (radixBits_lt laws)

def gainThreshold (grid layers markov r : ℕ) : ℕ := (grid * layers - 1) / (markov * (layers - r)) + 1

def successThresholds (grid layers markov : ℕ) : List ℕ :=
  (List.range' 1 (layers - 1)).map (gainThreshold grid layers markov)

theorem gainThreshold_le_iff {grid layers markov r j : ℕ}
    (hgrid : 0 < grid) (hlayers : 0 < layers) (hmarkov : 0 < markov) (hr : r < layers) :
    gainThreshold grid layers markov r ≤ j ↔ grid * layers ≤ j * markov * (layers - r) := by
  have hpos := Nat.mul_pos hgrid hlayers
  unfold gainThreshold
  rw [← Nat.lt_iff_add_one_le, Nat.div_lt_iff_lt_mul (Nat.mul_pos hmarkov (by omega)), mul_assoc]
  omega

theorem successThresholds_weight_bound {grid layers markov j : ℕ}
    (hgrid : 0 < grid) (hlayers : 0 < layers) (hmarkov : 0 < markov) (hj : 0 < j) :
    (thresholdCount (successThresholds grid layers markov) j : ℝ) / layers ≤
      max 0 (1 - (grid : ℝ) / ((j : ℝ) * markov)) := by
  let ranks := (List.range' 1 (layers - 1)).filter (fun r => gainThreshold grid layers markov r ≤ j)
  let accepted := ranks.toFinset
  have nd : ranks.Nodup := (List.nodup_range' 1).filter _
  have hcard : accepted.card = thresholdCount (successThresholds grid layers markov) j := by
    rw [List.toFinset_card_of_nodup nd]
    simp [thresholdCount, successThresholds, List.filter_map, Function.comp_def, ranks]
  rw [← hcard]
  by_cases hn : accepted.Nonempty
  · let r := accepted.max' hn
    have hr : r ∈ accepted := Finset.max'_mem _ _
    have hranks : r ∈ ranks := List.mem_toFinset.mp hr
    have hrg := List.mem_filter.mp hranks
    have hrinterval := List.mem_range'_1.mp hrg.1
    have hlt : r < layers := by omega
    have hm := (gainThreshold_le_iff hgrid hlayers hmarkov hlt).mp (by simpa using hrg.2)
    have hc : accepted.card ≤ r := by
      have hsub : accepted ⊆ Finset.Icc 1 r := by
        intro q hq
        apply Finset.mem_Icc.mpr
        exact ⟨(List.mem_range'_1.mp (List.mem_filter.mp (List.mem_toFinset.mp hq)).1).1,
          Finset.le_max' _ _ hq⟩
      simpa using Finset.card_le_card hsub
    have hrbound : (r : ℝ) / layers ≤ 1 - (grid : ℝ) / ((j : ℝ) * markov) := by
      have hjm : 0 < (j : ℝ) * markov := by positivity
      have hl : 0 < (layers : ℝ) := by positivity
      have hmul : (grid : ℝ) * layers ≤ (j : ℝ) * markov * ((layers : ℝ) - r) := by
        rw [← Nat.cast_sub hlt.le]
        exact_mod_cast hm
      apply (div_le_iff₀ hl).2
      rw [sub_mul, one_mul]
      suffices (grid : ℝ) / ((j : ℝ) * markov) * layers ≤ (layers : ℝ) - r by linarith
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hjm).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)).trans
      (hrbound.trans (le_max_right _ _))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

end A082957Packing

namespace A082957Packing

def residueAfter (bits code advance residue : ℕ) : ℕ :=
  let modulus := 2 ^ bits - 1
  let removed := (code &&& (2 ^ (bits * advance) - 1)) % modulus
  (residue + modulus - removed) % modulus

theorem residueAfter_eq (bits code advance : ℕ) (hbits : 0 < bits) :
    residueAfter bits code advance (code % (2 ^ bits - 1)) =
      (code >>> (bits * advance)) % (2 ^ bits - 1) := by
  let base := 2 ^ bits
  let modulus := base - 1
  let gap := 2 ^ (bits * advance)
  let lo := code % gap
  let hi := code / gap
  have hb₂ : 1 < base := one_lt_pow₀ (by decide) hbits.ne'
  have hm : 0 < modulus := by omega
  have hb₁ : base ≡ 1 [MOD modulus] :=
    (Nat.modEq_iff_dvd' hb₂.le).mpr dvd_rfl |>.symm
  have hg : gap ≡ 1 [MOD modulus] := by simpa [gap, base, pow_mul] using hb₁.pow advance
  have hd : code ≡ lo + hi [MOD modulus] := calc
    code = lo + gap * hi := (Nat.mod_add_div _ _).symm
    _ ≡ lo + hi [MOD modulus] := by
      simpa using (Nat.ModEq.refl lo).add (hg.mul_right hi)
  change code % modulus = (lo + hi) % modulus at hd
  rw [Nat.add_mod] at hd
  unfold residueAfter
  simp only [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  change (code % modulus + modulus - lo % modulus) % modulus = hi % modulus
  rw [hd]
  have hlo := Nat.mod_lt lo hm
  have hhi := Nat.mod_lt hi hm
  by_cases hsum : lo % modulus + hi % modulus < modulus
  · rw [Nat.mod_eq_of_lt hsum, show lo % modulus + hi % modulus + modulus - lo % modulus =
       hi % modulus + modulus by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt hhi
  · rw [Nat.mod_eq_sub_mod (Nat.le_of_not_gt hsum), Nat.mod_eq_of_lt (show
      lo % modulus + hi % modulus - modulus < modulus by omega)]
    have he : lo % modulus + hi % modulus - modulus + modulus - lo % modulus = hi % modulus := by
      omega
    rw [he, Nat.mod_eq_of_lt hhi]

theorem shiftBetween (bits code start t : ℕ) (hst : start ≤ t) :
    (code >>> (bits * start)) >>> (bits * (t - start)) = code >>> (bits * t) := by
  rw [← Nat.shiftRight_add, ← Nat.mul_add, Nat.add_sub_of_le hst]

def sweep (bits start code residue : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (t, count) :: ts =>
      let advance := t - start
      let nextCode := code >>> (bits * advance)
      let nextResidue := residueAfter bits code advance residue
      nextResidue * count + sweep bits t nextCode nextResidue ts

theorem sweep_eq (bits code : ℕ) (hbits : 0 < bits) (rows : List (ℕ × ℕ))
    (hs : rows.Pairwise (fun x y => x.1 ≤ y.1)) (start : ℕ)
    (hst : ∀ x ∈ rows, start ≤ x.1) :
    sweep bits start (code >>> (bits * start)) (query bits code start) rows =
      (rows.map fun p => query bits code p.1 * p.2).sum := by
  induction rows generalizing start with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨t, count⟩
    obtain ⟨ht, hxs⟩ := List.pairwise_cons.mp hs
    have hsa := hst (t, count) List.mem_cons_self
    have hshift := shiftBetween bits code start t hsa
    have hresidue : residueAfter bits (code >>> (bits * start)) (t - start)
        (query bits code start) = query bits code t := by
      simp only [query, residueAfter_eq _ _ _ hbits, hshift]
    simp only [sweep, hresidue, hshift, ih hxs t ht, List.map_cons, List.sum_cons]

def orderedWeightedQuery (bits code : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (t, count) :: ts =>
      let top := code >>> (bits * t)
      let residue := top % (2 ^ bits - 1)
      residue * count + sweep bits t top residue ts

theorem orderedWeightedQuery_eq (bits code : ℕ) (hbits : 0 < bits) (rows : List (ℕ × ℕ))
    (hs : rows.Pairwise (fun x y => x.1 ≤ y.1)) :
    orderedWeightedQuery bits code rows = (rows.map fun p => query bits code p.1 * p.2).sum := by
  cases rows with
  | nil => rfl
  | cons x xs =>
    rcases x with ⟨t, count⟩
    obtain ⟨ht, hxs⟩ := List.pairwise_cons.mp hs
    change query bits code t * count +
      sweep bits t (code >>> (bits * t)) (query bits code t) xs = _
    rw [sweep_eq bits code hbits xs hxs t ht]
    rfl

def pairProducts : List ℕ → List ℕ
  | a :: b :: rest => a * b :: pairProducts rest
  | l => l

theorem pairProducts_prod : ∀ l : List ℕ, (pairProducts l).prod = l.prod
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => by simp [pairProducts, pairProducts_prod rest, mul_assoc]

def balancedProduct : ℕ → List ℕ → ℕ
  | 0, l => l.prod
  | _ + 1, [] => 1
  | _ + 1, [a] => a
  | fuel + 1, a :: b :: rest => balancedProduct fuel (pairProducts (a :: b :: rest))

theorem balancedProduct_eq (fuel : ℕ) (l : List ℕ) : balancedProduct fuel l = l.prod := by
  induction fuel generalizing l with
  | zero => rfl
  | succ fuel ih =>
    match l with
    | [] => rfl
    | [a] => simp [balancedProduct]
    | a :: b :: rest =>
      rw [balancedProduct, ih, pairProducts_prod]

def balancedJoint (bits : ℕ) (laws : List Law) : ℕ :=
  balancedProduct (laws.length.log2 + 1) (laws.map (packedStep bits 1))

theorem balancedJoint_eq (bits : ℕ) (laws : List Law) :
    balancedJoint bits laws = packedJoint bits laws := by
  unfold balancedJoint
  rw [balancedProduct_eq]
  induction laws with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, packedJoint]
    rw [ih, packedStep_eq, packedStep_eq, mul_one]

def insertRow (row : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [row]
  | head :: tail =>
    if row.1 ≤ head.1 then row :: head :: tail else head :: insertRow row tail

theorem insertRow_perm (row : ℕ × ℕ) (rows : List (ℕ × ℕ)) :
    (insertRow row rows).Perm (row :: rows) := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    by_cases h : row.1 ≤ head.1
    · simp [insertRow, h]
    · simpa [insertRow, h] using (List.Perm.cons head ih).trans (List.Perm.swap row head tail)

theorem insertRow_sorted (row : ℕ × ℕ) (rows : List (ℕ × ℕ))
    (hr : rows.Pairwise (fun x y => x.1 ≤ y.1)) :
    (insertRow row rows).Pairwise (fun x y => x.1 ≤ y.1) := by
  induction rows with
  | nil => simp [insertRow]
  | cons head tail ih =>
    obtain ⟨hs, ht⟩ := List.pairwise_cons.mp hr
    by_cases h : row.1 ≤ head.1
    · rw [insertRow, if_pos h]
      refine List.pairwise_cons.mpr ⟨?_, hr⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h
      · exact h.trans (hs x hx)
    · rw [insertRow, if_neg h]
      refine List.pairwise_cons.mpr ⟨?_, ih ht⟩
      intro x hx
      rcases List.mem_cons.mp ((insertRow_perm row tail).mem_iff.mp hx) with rfl | hx
      · exact le_of_not_ge h
      · exact hs x hx

def sortRows : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | row :: rows => insertRow row (sortRows rows)

theorem sortRows_perm (rows : List (ℕ × ℕ)) : (sortRows rows).Perm rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    exact (insertRow_perm row (sortRows rows)).trans (List.Perm.cons row ih)

theorem sortRows_sorted (rows : List (ℕ × ℕ)) :
    (sortRows rows).Pairwise (fun x y => x.1 ≤ y.1) := by
  induction rows with
  | nil => simp [sortRows]
  | cons row rows ih => exact insertRow_sorted row (sortRows rows) ih

def fastWeightedPackedCount (laws : List Law) (thresholds : List ℕ) : ℕ :=
  let bits := radixBits laws
  let code := balancedJoint bits laws
  let rows := sortRows (compressThresholds thresholds)
  orderedWeightedQuery bits code rows

theorem fastWeightedPackedCount_eq (laws : List Law) (thresholds : List ℕ) :
    fastWeightedPackedCount laws thresholds = weightedPackedCount laws thresholds := by
  unfold fastWeightedPackedCount weightedPackedCount
  dsimp only
  rw [balancedJoint_eq]
  rw [orderedWeightedQuery_eq _ _ (by unfold radixBits; omega) _ (sortRows_sorted _)]
  exact ((sortRows_perm _).map _).sum_eq

end A082957Packing

namespace A082957Packing

abbrev SignedLaw := List (ℤ × ℕ)

def lawOrigin : SignedLaw → ℤ
  | [] => 0
  | (j, _) :: law => min j (lawOrigin law)

theorem lawOrigin_le (law : SignedLaw) (x : ℤ × ℕ) (hx : x ∈ law) : lawOrigin law ≤ x.1 := by
  induction law with
  | nil => simp at hx
  | cons y ys ih =>
    rcases y with ⟨j, count⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih hx)

def jointOrigin (laws : List SignedLaw) : ℤ := (laws.map lawOrigin).sum

def shiftLaw (law : SignedLaw) : Law :=
  law.map (fun x => ((x.1 - lawOrigin law).toNat, x.2))

def restoreLaw (origin : ℤ) (law : Law) : SignedLaw :=
  law.map (fun x => ((x.1 : ℤ) + origin, x.2))

theorem restoreLaw_shiftLaw (law : SignedLaw) : restoreLaw (lawOrigin law) (shiftLaw law) = law := by
  conv_rhs => rw [← List.map_id law]
  unfold restoreLaw shiftLaw
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  rcases x with ⟨j, count⟩
  have h : lawOrigin law ≤ j := lawOrigin_le _ (j, count) hx
  simp [Int.toNat_of_nonneg (sub_nonneg.mpr h)]

def signedConvolve (xs ys : SignedLaw) : SignedLaw :=
  xs.flatMap fun x => ys.map fun y => (x.1 + y.1, x.2 * y.2)

def signedJointLaw : List SignedLaw → SignedLaw
  | [] => [(0, 1)]
  | x :: xs => signedConvolve x (signedJointLaw xs)

theorem restoreLaw_convolve (x y : ℤ) (xs ys : Law) :
    restoreLaw (x + y) (convolve xs ys) = signedConvolve (restoreLaw x xs) (restoreLaw y ys) := by
  simp only [restoreLaw, convolve, signedConvolve, List.flatMap_map, List.map_flatMap,
    List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro a _
  apply List.map_congr_left
  intro b _
  simp [add_assoc, add_left_comm]

theorem restoreLaw_jointLaw (laws : List SignedLaw) :
    restoreLaw (jointOrigin laws) (jointLaw (laws.map shiftLaw)) = signedJointLaw laws := by
  induction laws with
  | nil => rfl
  | cons law laws ih =>
    simp only [jointOrigin, List.map_cons, List.sum_cons, jointLaw, signedJointLaw]
    rw [restoreLaw_convolve, restoreLaw_shiftLaw]
    exact congrArg (signedConvolve law) ih

theorem pack_one (law : Law) : pack 1 law = (law.map Prod.snd).sum := by
  induction law with
  | nil => rfl
  | cons x law ih =>
    rcases x with ⟨j, count⟩
    simp [pack, ih]

theorem signedJointLaw_weight (laws : List SignedLaw) :
    ((signedJointLaw laws).map Prod.snd).sum = (laws.map fun law => (law.map Prod.snd).sum).prod := by
  rw [← restoreLaw_jointLaw]
  simp only [restoreLaw, List.map_map, Function.comp_def]
  rw [← pack_one, pack_one_jointLaw, List.map_map]
  congr 1
  apply List.map_congr_left
  intro law _
  simp [Function.comp_def, pack_one, shiftLaw, List.map_map]

def signedThresholdCount (thresholds : List ℕ) (j : ℤ) : ℕ :=
  (thresholds.filter (fun t : ℕ => (t : ℤ) ≤ j)).length

theorem thresholdCount_shift (thresholds : List ℕ) (origin : ℤ) (j : ℕ) :
    thresholdCount (thresholds.map (fun t : ℕ => ((t : ℤ) - origin).toNat)) j =
      signedThresholdCount thresholds ((j : ℤ) + origin) := by
  unfold thresholdCount signedThresholdCount
  rw [List.filter_map, List.length_map]
  apply congrArg List.length
  apply congrArg (fun predicate => thresholds.filter predicate)
  funext t
  simp only [Function.comp_def, decide_eq_decide]
  omega

def signedPackedCount (laws : List SignedLaw) (thresholds : List ℕ) : ℕ :=
  let origin := jointOrigin laws
  fastWeightedPackedCount (laws.map shiftLaw)
    (thresholds.map (fun t : ℕ => ((t : ℤ) - origin).toNat))

theorem signedPackedCount_eq (laws : List SignedLaw) (thresholds : List ℕ) :
    signedPackedCount laws thresholds =
      ((signedJointLaw laws).map (fun x => x.2 * signedThresholdCount thresholds x.1)).sum := by
  unfold signedPackedCount
  rw [fastWeightedPackedCount_eq, weightedPackedCount_eq, ← restoreLaw_jointLaw]
  simp only [restoreLaw, List.map_map, Function.comp_def, thresholdCount_shift]

end A082957Packing

namespace A082957Packing

noncomputable def markovGain (grid markov : ℕ) (j : ℤ) : ℝ :=
  if 0 < j then max 0 (1 - (grid : ℝ) / ((j : ℝ) * markov)) else 0

theorem signedThresholdCount_le_gain {grid layers markov : ℕ} (j : ℤ)
    (hgrid : 0 < grid) (hlayers : 0 < layers) (hmarkov : 0 < markov) :
    (signedThresholdCount (successThresholds grid layers markov) j : ℝ) / layers ≤
      markovGain grid markov j := by
  by_cases hj : 0 < j
  · have hnat : (0 : ℕ) < j.toNat := by omega
    have hz : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj.le
    have hcast : (j.toNat : ℝ) = (j : ℝ) := by exact_mod_cast hz
    have he : thresholdCount (successThresholds grid layers markov) j.toNat =
        signedThresholdCount (successThresholds grid layers markov) j := by
      simpa [hz] using thresholdCount_shift (successThresholds grid layers markov) 0 j.toNat
    rw [← he, markovGain, if_pos hj]
    simpa only [hcast] using successThresholds_weight_bound hgrid hlayers hmarkov hnat
  · have hfilter : ((successThresholds grid layers markov).filter
        (fun t : ℕ => (t : ℤ) ≤ j)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro t ht htj
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp ht
      simp only [decide_eq_true_eq] at htj
      have hpositive : 0 < gainThreshold grid layers markov r := Nat.succ_pos _
      exact (not_lt_of_ge (htj.trans (le_of_not_gt hj))) (by exact_mod_cast hpositive)
    simp [signedThresholdCount, hfilter, markovGain, hj]

theorem weightedGainBound (law : SignedLaw) {grid layers markov : ℕ}
    (hgrid : 0 < grid) (hlayers : 0 < layers) (hmarkov : 0 < markov) :
    ((((law.map fun x => x.2 * signedThresholdCount (successThresholds grid layers markov) x.1)).sum : ℕ) : ℝ) /
      layers ≤ (law.map fun x => (x.2 : ℝ) * markovGain grid markov x.1).sum := by
  induction law with
  | nil => simp
  | cons x law ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_mul, add_div, mul_div_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (signedThresholdCount_le_gain x.1 hgrid hlayers hmarkov) (Nat.cast_nonneg _)) ih

theorem signedPackedCount_le_gain (laws : List SignedLaw) {grid layers markov : ℕ}
    (hgrid : 0 < grid) (hlayers : 0 < layers) (hmarkov : 0 < markov) :
    (signedPackedCount laws (successThresholds grid layers markov) : ℝ) / layers ≤
      ((signedJointLaw laws).map fun x => (x.2 : ℝ) * markovGain grid markov x.1).sum := by
  rw [signedPackedCount_eq]
  exact weightedGainBound (signedJointLaw laws) hgrid hlayers hmarkov

end A082957Packing

namespace A082957Packing

def grid : ℕ := 4096
def layers : ℕ := 16384
def markov : ℕ := 9700

def primes : List ℕ := (List.range' 2 1499).filter trialPrime

theorem mem_primes_iff (p : ℕ) : p ∈ primes ↔ 2 ≤ p ∧ p ≤ 1500 ∧ p.Prime := by
  simp [primes, trialPrime_iff, Nat.lt_succ_iff, and_assoc]

theorem primes_nodup : primes.Nodup := (List.nodup_range' 1).filter _

def cap (p : ℕ) : ℕ :=
  ((List.range' 1 9).find? fun e => 512 ≤ p ^ e).getD 9

theorem cap_pos (p : ℕ) : 0 < cap p := by
  cases he : (List.range' 1 9).find? (fun e => 512 ≤ p ^ e) with
  | none => simp [cap, he]
  | some e =>
    have hm := List.mem_of_find?_eq_some he
    have hp : 1 ≤ e := (List.mem_range'_1.mp hm).1
    rw [cap, he]
    exact Nat.succ_le_iff.mp hp

def localGridLaw (reverse : Bool) (p : ℕ) : SignedLaw :=
  (A082957Certificate.valuationCounts p (cap p)).map fun (side, count) =>
    (A082957Certificate.gridShift grid p (cap p) reverse side, count)

def computationDenominator : ℕ := layers * (primes.map fun p => p ^ cap p).prod

theorem computationDenominator_pos : 0 < computationDenominator := by
  unfold computationDenominator
  apply Nat.mul_pos (by decide)
  apply List.prod_pos_iff_forall_pos_nat.mpr
  intro power hmem
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmem
  have ht := (mem_primes_iff p).mp hp
  exact Nat.pow_pos (by omega)

def computationNumerator (reverse : Bool) : ℕ :=
  signedPackedCount (primes.map (localGridLaw reverse)) (successThresholds grid layers markov)

end A082957Packing

namespace A082957Certificate

open Finset

theorem middleExponents_mem_iff {E e : ℕ} :
    e ∈ (List.range E).drop 1 ↔ 0 < e ∧ e < E := by
  rw [List.range_eq_range', List.drop_range', List.mem_range'_1]
  omega

theorem valuationCounts_weight {p E : ℕ} (hp : p.Prime) (hE : 0 < E)
    {row : ValuationSide × ℕ} (hr : row ∈ valuationCounts p E) :
    Nat.count (fun n => valuationSide p E n = row.1) (p ^ E) = row.2 := by
  by_cases htwo : p = 2
  · subst p
    simp only [valuationCounts] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
      have h := middleExponents_mem_iff.mp he
      simpa [h.2.ne] using count_even_side_two h.1 h.2.le
    · have he := List.mem_singleton.mp hr
      subst row
      simpa using count_even_side_two hE le_rfl
  · simp only [valuationCounts, if_neg htwo, List.cons_append] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact count_unit_side_odd hp htwo hE
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨e, he, hr⟩ := List.mem_flatMap.mp hr
      have h := middleExponents_mem_iff.mp he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa [h.2.ne] using count_even_side_odd hp htwo h.1 h.2.le
      · simpa [h.2.ne] using count_odd_side_odd hp htwo h.1 h.2.le
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simpa using count_even_side_odd hp htwo hE le_rfl
      · simpa using count_odd_side_odd hp htwo hE le_rfl

theorem valuationCounts_first_nodup (p E : ℕ) : ((valuationCounts p E).map Prod.fst).Nodup := by
  let middle := (List.range E).drop 1
  have hmiddle : middle.Nodup := (List.nodup_range (n := E)).drop
  by_cases htwo : p = 2
  · simp only [valuationCounts, if_pos htwo, List.map_append, List.map_map,
      List.map_cons, List.map_nil]
    change (middle.map ValuationSide.even ++ [ValuationSide.even E]).Nodup
    refine List.nodup_append.mpr ⟨hmiddle.map (fun _ _ h => ValuationSide.even.inj h), by simp, ?_⟩
    intro x hx y hy hxy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    rw [List.mem_singleton.mp hy] at hxy
    exact (middleExponents_mem_iff.mp he).2.ne (ValuationSide.even.inj hxy)
  · simp only [valuationCounts, if_neg htwo, List.cons_append, List.map_cons, List.map_append,
      List.map_flatMap, List.map_nil]
    let both (e : ℕ) : List ValuationSide := [.even e, .odd e]
    change (ValuationSide.unit :: (middle.flatMap both ++ [ValuationSide.even E, ValuationSide.odd E])).Nodup
    rw [List.nodup_cons]
    constructor
    · simp [both, List.mem_flatMap]
    · refine List.nodup_append.mpr ⟨?_, by simp, ?_⟩
      · apply List.nodup_flatMap.mpr
        refine ⟨fun _ _ => by simp [both], hmiddle.imp ?_⟩
        intro e f hef
        apply List.disjoint_left.mpr
        intro z hz hz'
        simp only [both, List.mem_cons, List.not_mem_nil, or_false] at hz hz'
        rcases hz with rfl | rfl <;> simp [hef] at hz'
      · intro x hx y hy hxy
        obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
        have he' := (middleExponents_mem_iff.mp he).2.ne
        simp only [both, List.mem_cons, List.not_mem_nil, or_false] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp [he'] at hxy

theorem valuationSide_in_counts (p E n : ℕ) (hE : 0 < E) :
    valuationSide p E n ∈ (valuationCounts p E).map Prod.fst := by
  by_cases he : p ∣ 2 * n
  · let e := cappedVal p E (2 * n)
    have he0 : 0 < e := Nat.succ_le_iff.mp (le_cappedVal_iff.mpr ⟨hE, by simpa using he⟩)
    have heE : e ≤ E := cappedVal_le _ _ _
    simp only [valuationSide, if_pos he]
    change .even e ∈ (valuationCounts p E).map Prod.fst
    by_cases h : e = E
    · by_cases htwo : p = 2 <;> simp [valuationCounts, htwo, h]
    · have hm := middleExponents_mem_iff.mpr ⟨he0, heE.lt_of_ne h⟩
      by_cases htwo : p = 2
      · simp only [valuationCounts, if_pos htwo, List.map_append, List.map_map, List.mem_append]
        exact Or.inl (List.mem_map.mpr ⟨e, hm, rfl⟩)
      · simp only [valuationCounts, if_neg htwo, List.cons_append, List.map_cons, List.map_append,
          List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (List.mem_map.mpr ⟨(ValuationSide.even e, (p - 1) * p ^ (E - e - 1)),
          List.mem_flatMap.mpr ⟨e, hm, by simp⟩, rfl⟩))
  · have htwo : p ≠ 2 := by rintro rfl; exact he (dvd_mul_right _ _)
    by_cases ho : p ∣ 2 * n + 1
    · let e := cappedVal p E (2 * n + 1)
      have he0 : 0 < e := Nat.succ_le_iff.mp (le_cappedVal_iff.mpr ⟨hE, by simpa using ho⟩)
      have heE : e ≤ E := cappedVal_le _ _ _
      simp only [valuationSide, if_neg he, if_pos ho]
      change .odd e ∈ (valuationCounts p E).map Prod.fst
      by_cases h : e = E
      · simp [valuationCounts, htwo, h]
      · have hm := middleExponents_mem_iff.mpr ⟨he0, heE.lt_of_ne h⟩
        simp only [valuationCounts, if_neg htwo, List.cons_append, List.map_cons, List.map_append,
          List.mem_cons, List.mem_append]
        exact Or.inr (Or.inl (List.mem_map.mpr ⟨(ValuationSide.odd e, (p - 1) * p ^ (E - e - 1)),
          List.mem_flatMap.mpr ⟨e, hm, by simp⟩, rfl⟩))
    · simp [valuationSide, he, ho, htwo, valuationCounts, List.cons_append]

theorem sum_residues_of_counts {β A : Type*} [DecidableEq β] [AddCommMonoid A]
    {N : ℕ} (rows : List (β × ℕ)) (v : ℕ → β) (f : β → A)
    (hn : (rows.map Prod.fst).Nodup)
    (hcover : ∀ n < N, v n ∈ rows.map Prod.fst)
    (hweight : ∀ row ∈ rows, Nat.count (fun n => v n = row.1) N = row.2) :
    (∑ n : Fin N, f (v n.val)) = (rows.map (fun row => row.2 • f row.1)).sum := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => f (v n))]
  have hs : ∀ n ∈ Finset.range N, v n ∈ rows.toFinset.image Prod.fst := by
    intro n h
    obtain ⟨row, hm, hEq⟩ := List.mem_map.mp (hcover n (Finset.mem_range.mp h))
    exact Finset.mem_image.mpr ⟨row, List.mem_toFinset.mpr hm, hEq⟩
  calc
    _ = ∑ s ∈ rows.toFinset.image Prod.fst,
        ((Finset.range N).filter (fun n => v n = s)).card • f s := by
      simpa only [Finset.sum_const] using (Finset.sum_fiberwise_of_maps_to' hs f).symm
    _ = ∑ row ∈ rows.toFinset, row.2 • f row.1 := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro row hr
        rw [← Nat.count_eq_card_filter_range, hweight row (List.mem_toFinset.mp hr)]
      · exact fun _ ha _ hb hab => List.inj_on_of_nodup_map hn
          (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    _ = _ := List.sum_toFinset _ (List.Nodup.of_map Prod.fst hn)

theorem sum_valuationSide_counts {A : Type*} [AddCommMonoid A] {p E : ℕ}
    (hp : p.Prime) (hE : 0 < E) (f : ValuationSide → A) :
    (∑ r : Fin (p ^ E), f (valuationSide p E r.val)) =
      ((valuationCounts p E).map fun row => row.2 • f row.1).sum := by
  exact sum_residues_of_counts _ _ _ (valuationCounts_first_nodup p E)
    (fun n _ => valuationSide_in_counts p E n hE) (fun _ h => valuationCounts_weight hp hE h)

end A082957Certificate

namespace A082957Packing

open A082957Certificate Finset

def gridModulus (ps : List ℕ) : ℕ := (ps.map fun p => p ^ cap p).prod

def gridScore (ps : List ℕ) (reverse : Bool) (r : ℕ) : ℤ :=
  (ps.map fun p => gridShift grid p (cap p) reverse (valuationSide p (cap p) r)).sum

def weightedScore {A : Type*} [AddCommMonoid A] (law : SignedLaw) (f : ℤ → A) : A :=
  (law.map (fun row => row.2 • f row.1)).sum

theorem gridModulus_pos {ps : List ℕ} (hp : ∀ p ∈ ps, p.Prime) : 0 < gridModulus ps := by
  unfold gridModulus
  apply List.prod_pos_iff_forall_pos_nat.mpr
  intro q hq
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hq
  exact pow_pos (hp p hp').pos _

theorem primePower_dvd_gridModulus {p : ℕ} {ps : List ℕ} (hp : p ∈ ps) : p ^ cap p ∣ gridModulus ps :=
  List.dvd_prod (List.mem_map.mpr ⟨p, hp, rfl⟩)

theorem gridScore_cons (p : ℕ) (ps : List ℕ) (reverse : Bool) (r : ℕ) :
    gridScore (p :: ps) reverse r =
      gridShift grid p (cap p) reverse (valuationSide p (cap p) r) + gridScore ps reverse r := rfl

theorem gridScore_modeq {ps : List ℕ} {r s : ℕ} (hm : r ≡ s [MOD gridModulus ps]) (reverse : Bool) :
    gridScore ps reverse r = gridScore ps reverse s := by
  unfold gridScore
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [valuationSide_modeq (cap_pos p) (hm.of_dvd (primePower_dvd_gridModulus hp))]

theorem weightedScore_convolve {A : Type*} [AddCommMonoid A] (left right : SignedLaw) (f : ℤ → A) :
    weightedScore (signedConvolve left right) f =
      (left.map fun row => row.2 • weightedScore right (fun z => f (row.1 + z))).sum := by
  induction left with
  | nil => rfl
  | cons row rows ih =>
    have hrow :
        (right.map (fun y => (row.2 * y.2) • f (row.1 + y.1))).sum =
          row.2 • weightedScore right (fun z => f (row.1 + z)) := by
      clear ih
      induction right with
      | nil => simp [weightedScore]
      | cons y ys ih' =>
        simp only [List.map_cons, List.sum_cons, weightedScore, nsmul_add] at ih' ⊢
        rw [ih', mul_nsmul']
    simp only [weightedScore, signedConvolve, List.flatMap_cons, List.map_append, List.sum_append,
      List.map_map, Function.comp_def, List.map_cons, List.sum_cons] at ih ⊢
    exact congrArg₂ (· + ·) hrow ih

theorem sum_localGridLaw {A : Type*} [AddCommMonoid A] {p : ℕ} (hp : p.Prime)
    (reverse : Bool) (f : ℤ → A) :
    (∑ a : Fin (p ^ cap p), f (gridShift grid p (cap p) reverse (valuationSide p (cap p) a.val))) =
      weightedScore (localGridLaw reverse p) f := by
  simpa [weightedScore, localGridLaw, List.map_map, Function.comp_def] using
    (sum_valuationSide_counts hp (cap_pos p) (fun side => f (gridShift grid p (cap p) reverse side)))

theorem sum_gridScore_jointLaw {A : Type*} [AddCommMonoid A] {ps : List ℕ}
    (hp : ∀ p ∈ ps, p.Prime) (hn : ps.Nodup) (reverse : Bool) (f : ℤ → A) :
    (∑ r : Fin (gridModulus ps), f (gridScore ps reverse r.val)) =
      weightedScore (signedJointLaw (ps.map (localGridLaw reverse))) f := by
  classical
  induction ps generalizing f with
  | nil =>
    change (∑ _ : Fin 1, f 0) = (1 : ℕ) • f 0 + 0
    rw [Finset.sum_const, Finset.card_fin]
    simp
  | cons p ps ih =>
    have hp₀ := hp p List.mem_cons_self
    have hp₁ : ∀ q ∈ ps, q.Prime := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hn₁ := (List.nodup_cons.mp hn).2
    have hcop : (p ^ cap p).Coprime (gridModulus ps) := by
      apply Nat.coprime_list_prod_right_iff.mpr
      intro factor hmem
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmem
      have hne : p ≠ q := fun h => (List.nodup_cons.mp hn).1 (h ▸ hq)
      exact Nat.coprime_pow_primes _ _ hp₀ (hp₁ q hq) hne
    let d := p ^ cap p
    let m := gridModulus ps
    let e := residueProduct (show 0 < d from pow_pos hp₀.pos _) (gridModulus_pos hp₁) hcop
    change (∑ r : Fin (d * m), f (gridScore (p :: ps) reverse r.val)) = _
    let shift (a : Fin d) := gridShift grid p (cap p) reverse (valuationSide p (cap p) a.val)
    let tail := signedJointLaw (ps.map (localGridLaw reverse))
    have hsplit (a : Fin d) (b : Fin m) :
        gridScore (p :: ps) reverse (e.symm (a,b)).val = shift a + gridScore ps reverse b.val := by
      have hf := congrArg (fun x : Fin d × Fin m => x.1.val) (e.apply_symm_apply (a,b))
      have hg := congrArg (fun x : Fin d × Fin m => x.2.val) (e.apply_symm_apply (a,b))
      change (e.symm (a,b)).val % d = a.val at hf
      change (e.symm (a,b)).val % m = b.val at hg
      have hda : (e.symm (a,b)).val ≡ a.val [MOD d] := by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt a.isLt] using hf
      have hmb : (e.symm (a,b)).val ≡ b.val [MOD m] := by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt b.isLt] using hg
      rw [gridScore_cons, valuationSide_modeq (cap_pos p) hda, gridScore_modeq hmb reverse]
    calc
      _ = ∑ ab : Fin d × Fin m, f (gridScore (p :: ps) reverse (e.symm ab).val) :=
        (e.symm.sum_comp _).symm
      _ = ∑ a : Fin d, ∑ b : Fin m, f (shift a + gridScore ps reverse b.val) := by
        rw [Fintype.sum_prod_type]
        simp_rw [hsplit]
      _ = ∑ a : Fin d, weightedScore tail (fun z => f (shift a + z)) := by
        exact Finset.sum_congr rfl fun a _ => ih hp₁ hn₁ (fun z => f (shift a + z))
      _ = weightedScore (localGridLaw reverse p) (fun a => weightedScore tail (fun z => f (a + z))) :=
        sum_localGridLaw hp₀ reverse (fun a => weightedScore tail (fun z => f (a + z)))
      _ = _ := (weightedScore_convolve (localGridLaw reverse p) tail f).symm

theorem sum_gridScore_primes_jointLaw {A : Type*} [AddCommMonoid A] (reverse : Bool) (f : ℤ → A) :
    (∑ r : Fin (gridModulus primes), f (gridScore primes reverse r.val)) =
      weightedScore (signedJointLaw (primes.map (localGridLaw reverse))) f :=
  sum_gridScore_jointLaw (fun p hp => (mem_primes_iff p).1 hp |>.2.2) primes_nodup reverse f

theorem gridModulus_eq_prime_product {ps : List ℕ} (hn : ps.Nodup) :
    (∏ p : ps.toFinset, (p : ℕ) ^ cap p.val) = gridModulus ps := by
  rw [Finset.prod_coe_sort (s := ps.toFinset) (f := fun p : ℕ => p ^ cap p),
    gridModulus, List.prod_toFinset _ hn]

theorem gridScore_eq_prime_sum {ps : List ℕ} (hn : ps.Nodup) (reverse : Bool) (r : ℕ) :
    gridScore ps reverse r = ∑ p : ps.toFinset,
      gridShift grid p.val (cap p.val) reverse (valuationSide p.val (cap p.val) r) := by
  rw [Finset.sum_coe_sort (s := ps.toFinset)
    (f := fun p : ℕ => gridShift grid p (cap p) reverse (valuationSide p (cap p) r)),
    gridScore, List.sum_toFinset _ hn]

theorem sum_gridScore_product_jointLaw {A : Type*} [AddCommMonoid A] {ps : List ℕ}
    (hp : ∀ p ∈ ps, p.Prime) (hn : ps.Nodup) (reverse : Bool) (f : ℤ → A) :
    (∑ r : (∀ p : ps.toFinset, Fin (p.val ^ cap p.val)), f (∑ p : ps.toFinset,
        gridShift grid p.val (cap p.val) reverse (valuationSide p.val (cap p.val) (r p).val))) =
      weightedScore (signedJointLaw (ps.map (localGridLaw reverse))) f := by
  classical
  let m (p : ps.toFinset) := p.val ^ cap p.val
  have hpp (p : ps.toFinset) : p.val.Prime := hp _ (List.mem_toFinset.mp p.prop)
  have hm (p : ps.toFinset) : 0 < m p := pow_pos (hpp p).pos _
  have hc : Pairwise (fun p q => (m p).Coprime (m q)) := fun p q hne =>
    Nat.coprime_pow_primes _ _ (hpp p) (hpp q) (fun h => hne (Subtype.ext h))
  let e := residuePi m hm hc
  let total := ∏ p, m p
  let w (r : ∀ p : ps.toFinset, Fin (m p)) := f (∑ p : ps.toFinset,
    gridShift grid p.val (cap p.val) reverse (valuationSide p.val (cap p.val) (r p).val))
  change (∑ r, w r) = _
  calc
    _ = ∑ r : Fin total, w (e r) := (e.sum_comp w).symm
    _ = ∑ r : Fin total, f (gridScore ps reverse r.val) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply congrArg f
      rw [gridScore_eq_prime_sum hn]
      apply Finset.sum_congr rfl
      intro p _
      rw [show (e r p).val = r.val % m p from residuePi_val m hm hc r p]
      exact congrArg (gridShift grid p.val (cap p.val) reverse)
        (valuationSide_modeq (cap_pos p.val) (Nat.mod_modEq _ _))
    _ = ∑ r : Fin (gridModulus ps), f (gridScore ps reverse r.val) := by
      have htotal : total = gridModulus ps := gridModulus_eq_prime_product hn
      rw [htotal]
    _ = _ := sum_gridScore_jointLaw hp hn reverse f

theorem sum_thresholdCounts_eq (reverse : Bool) (thresholds : List ℕ) :
    (∑ r : Fin (gridModulus primes), signedThresholdCount thresholds (gridScore primes reverse r.val)) =
      signedPackedCount (primes.map (localGridLaw reverse)) thresholds := by
  rw [sum_gridScore_primes_jointLaw, signedPackedCount_eq]
  simp only [weightedScore, Nat.nsmul_eq_mul]

theorem computationNumerator_eq_residueSum (reverse : Bool) :
    computationNumerator reverse = ∑ r : Fin (gridModulus primes),
      signedThresholdCount (successThresholds grid layers markov) (gridScore primes reverse r.val) :=
  (sum_thresholdCounts_eq reverse (successThresholds grid layers markov)).symm

theorem primes_toFinset_eq : primes.toFinset = (Finset.range 1501).filter Nat.Prime := by
  ext p
  simp only [List.mem_toFinset, mem_primes_iff, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun hp => ⟨Nat.lt_succ_of_le hp.2.1, hp.2.2⟩, fun hp =>
    ⟨hp.2.two_le, Nat.le_of_lt_succ hp.1, hp.2⟩⟩

theorem gridScore_le_smallSum {n : ℕ} (hn : 0 < n) (reverse : Bool) :
    (gridScore primes reverse n : ℝ) / grid ≤
      ∑ p ∈ (Finset.range 1501).filter Nat.Prime, signedContribution reverse p n := by
  rw [gridScore_eq_prime_sum primes_nodup, Int.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.sum_coe_sort (s := primes.toFinset) (f := fun p : ℕ =>
    (gridShift grid p (cap p) reverse (valuationSide p (cap p) n) : ℝ) * (grid : ℝ)⁻¹),
    primes_toFinset_eq]
  apply Finset.sum_le_sum
  intro p hp
  simpa only [div_eq_mul_inv] using
    (gridShift_sound (by decide : 0 < grid) (Finset.mem_filter.mp hp).2 hn reverse)

end A082957Packing

namespace A082957Packing

open Finset

noncomputable def packedDensityBound (reverse : Bool) : ℝ :=
  (computationNumerator reverse : ℝ) / (computationDenominator : ℝ)

theorem density_between_thresholds {δ : ℝ}
    (hLower : 2 * computationDenominator < 37 * computationNumerator false)
    (hUpper : 17 * computationDenominator < 18 * computationNumerator true)
    (hForward : packedDensityBound false ≤ δ) (hReverse : packedDensityBound true ≤ 1 - δ) :
    2 / 37 < δ ∧ δ < 1 / 18 := by
  have hD : (0 : ℝ) < (computationDenominator : ℝ) := by
    exact_mod_cast computationDenominator_pos
  have hlo : (2 : ℝ) * (computationDenominator : ℝ) <
      37 * (computationNumerator false : ℝ) := by
    exact_mod_cast hLower
  have hhi : (17 : ℝ) * (computationDenominator : ℝ) <
      18 * (computationNumerator true : ℝ) := by
    exact_mod_cast hUpper
  have h₀ : (2 : ℝ) / 37 < packedDensityBound false := by
    apply (lt_div_iff₀ hD).2
    linarith
  have h₁ : (17 : ℝ) / 18 < packedDensityBound true := by
    apply (lt_div_iff₀ hD).2
    linarith
  exact ⟨h₀.trans_le hForward, by linarith⟩

theorem concrete_markovGain (j : ℤ) :
    markovGain grid markov j =
      if 0 < j then 1 - ((1 : ℝ) / markov) / ((j : ℝ) / grid) else 0 := by
  by_cases hj : 0 < j
  · rw [markovGain, if_pos hj, if_pos hj]
    have hj₀ : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
    have hj₁ : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (show (1 : ℤ) ≤ j by omega)
    have hm : (0 : ℝ) < (markov : ℝ) := by norm_num [markov]
    have hg : (0 : ℝ) < (grid : ℝ) := by norm_num [grid]
    have hprod : (0 : ℝ) < (j : ℝ) * (markov : ℝ) := mul_pos hj₀ hm
    have hGridLe : (grid : ℝ) ≤ (j : ℝ) * (markov : ℝ) := by
      have h := mul_le_mul_of_nonneg_right hj₁ hm.le
      norm_num [grid, markov] at h ⊢
      linarith
    have hGain : (0 : ℝ) ≤ 1 - (grid : ℝ) / ((j : ℝ) * markov) :=
      sub_nonneg.mpr ((div_le_iff₀ hprod).2 (by simpa using hGridLe))
    rw [max_eq_right hGain]
    field_simp [hj₀.ne', hm.ne', hg.ne']
  · simp [markovGain, hj]

theorem packedDensityBound_le_residue_gain (reverse : Bool) (M : ℕ) (score : Fin M → ℤ)
    (hDen : computationDenominator = layers * M)
    (hNum : computationNumerator reverse = ∑ r : Fin M,
      signedThresholdCount (successThresholds grid layers markov) (score r)) :
    packedDensityBound reverse ≤
      ∑ r ∈ univ.filter (fun r : Fin M => 0 < score r),
        (1 - ((1 : ℝ) / markov) / ((score r : ℝ) / grid)) / (M : ℝ) := by
  have hgrid : 0 < grid := by decide
  have hlayers : 0 < layers := by decide
  have hmarkov : 0 < markov := by decide
  calc
    packedDensityBound reverse = ∑ r : Fin M,
        ((signedThresholdCount (successThresholds grid layers markov) (score r) : ℕ) : ℝ) /
          (layers : ℝ) / (M : ℝ) := by
      rw [packedDensityBound, hNum, hDen]
      simp only [Nat.cast_sum, Nat.cast_mul, ← div_div, sum_div]
    _ ≤ ∑ r : Fin M, markovGain grid markov (score r) / (M : ℝ) :=
      sum_le_sum (fun r _ => div_le_div_of_nonneg_right
        (signedThresholdCount_le_gain (score r) hgrid hlayers hmarkov) (Nat.cast_nonneg _))
    _ = _ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro r _
      rw [concrete_markovGain]
      split_ifs <;> simp

theorem gridModulus_coprime_tail {p : ℕ} (hp : p.Prime) (hLarge : 1500 < p) :
    (gridModulus primes).Coprime p := by
  rw [gridModulus, Nat.coprime_list_prod_left_iff]
  intro m hm
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
  obtain ⟨_, hqLe, hqPrime⟩ := (mem_primes_iff q).mp hq
  simpa only [pow_one] using Nat.coprime_pow_primes (cap q) 1 hqPrime hp
    (by omega : q ≠ p)

theorem concretePackedDensityBound_le_residue_gain (reverse : Bool) :
    packedDensityBound reverse ≤
      ∑ r ∈ univ.filter (fun r : Fin (gridModulus primes) =>
        0 < (gridScore primes reverse r.val : ℝ) / grid),
        (1 - ((1 : ℝ) / markov) / ((gridScore primes reverse r.val : ℝ) / grid)) /
          (gridModulus primes : ℝ) := by
  have hgrid : (0 : ℝ) < (grid : ℝ) := by norm_num [grid]
  have hfilter : (univ.filter (fun r : Fin (gridModulus primes) =>
      0 < gridScore primes reverse r.val)) = univ.filter (fun r =>
        0 < (gridScore primes reverse r.val : ℝ) / grid) := by
    apply filter_congr
    intro r _
    rw [div_pos_iff_of_pos_right hgrid, Int.cast_pos]
  rw [← hfilter]
  exact packedDensityBound_le_residue_gain reverse (gridModulus primes)
    (fun r => gridScore primes reverse r.val) rfl (computationNumerator_eq_residueSum reverse)

end A082957Packing

namespace A082957Certificate

open Finset Real Filter

def tailPrimes (Y U : ℕ) : Finset ℕ := (range (U + 1)).filter fun p => Y < p ∧ p.Prime

noncomputable def tailWeight (p : ℕ) : ℝ := ((p : ℝ) - 1)⁻¹

noncomputable def divisorTail (Y : ℕ) (side : Bool) (n : ℕ) : ℝ :=
  ∑ p ∈ tailPrimes Y (2 * n + 1),
    if p ∣ 2 * n + (if side then 1 else 0) then tailWeight p else 0

theorem tailPrimes_subset {Y U V : ℕ} (h : U ≤ V) : tailPrimes Y U ⊆ tailPrimes Y V := by
  intro p hp
  simp only [tailPrimes, mem_filter, mem_range] at hp ⊢
  exact ⟨hp.1.trans_le (by omega), hp.2⟩

theorem prime_tailWeight_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ tailWeight p := by
  have h : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  exact inv_nonneg.2 (sub_nonneg.2 h)

theorem sum_indicator_class (N M a : ℕ) (f : ℕ → Prop) [DecidablePred f] (w : ℝ) :
    (∑ n ∈ (range N).filter (fun k => k ≡ a [MOD M]), if f n then w else 0) =
      (Nat.count (fun n => n ≡ a [MOD M] ∧ f n) N : ℝ) * w := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, Nat.count_eq_card_filter_range, filter_filter]

theorem tail_residue_sum_le {Y M : ℕ} (hY : 2 ≤ Y) (hM : 0 < M)
    (hC : ∀ p : ℕ, p.Prime → Y < p → M.Coprime p)
    (a : ℕ) (side : Bool) (N : ℕ) :
    (∑ n ∈ (range N).filter (fun k => k ≡ a [MOD M]), divisorTail Y side n) ≤
      (N : ℝ) / M * (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p / (p : ℝ)) +
        ∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p := by
  let cls := (range N).filter (fun k => k ≡ a [MOD M])
  let primes := tailPrimes Y (2 * N + 1)
  have hP {p : ℕ} (hp : p ∈ primes) : Y < p ∧ p.Prime := (mem_filter.1 hp).2
  change (∑ n ∈ cls, divisorTail Y side n) ≤
    (N : ℝ) / M * (∑ p ∈ primes, tailWeight p / (p : ℝ)) + ∑ p ∈ primes, tailWeight p
  calc
    _ ≤ ∑ n ∈ cls, ∑ p ∈ primes,
        if p ∣ 2 * n + (if side then 1 else 0) then tailWeight p else 0 := by
      refine sum_le_sum (fun n hn => ?_)
      unfold divisorTail
      have hn' := mem_range.1 (mem_filter.1 hn).1
      apply sum_le_sum_of_subset_of_nonneg (tailPrimes_subset (by omega))
      intro p hp _
      by_cases hd : p ∣ 2 * n + (if side then 1 else 0)
      · simpa only [if_pos hd] using prime_tailWeight_nonneg (hP hp).2
      · simp only [if_neg hd, le_refl]
    _ = ∑ p ∈ primes, ∑ n ∈ cls,
        if p ∣ 2 * n + (if side then 1 else 0) then tailWeight p else 0 := sum_comm
    _ ≤ ∑ p ∈ primes, ((N : ℝ) / ((M : ℝ) * (p : ℝ)) + 1) * tailWeight p := by
      refine sum_le_sum (fun p hp => ?_)
      have hp' := hP hp
      have hp₂ : p ≠ 2 := by omega
      obtain ⟨r, hr⟩ := affine_dvd_iff_modeq (hp'.2.eq_two_or_odd'.resolve_left hp₂) side
      rw [sum_indicator_class N M a]
      rw [count_congr _ (fun k => and_congr_right (fun _ => hr k))]
      apply mul_le_mul_of_nonneg_right _ (prime_tailWeight_nonneg hp'.2)
      have hc := count_joint_modeq_le (N := N) hM hp'.2.pos (hC p hp'.2 hp'.1) a r
      have hcast : (Nat.count (fun k => k ≡ a [MOD M] ∧ k ≡ r [MOD p]) N : ℝ) ≤
          ((N / (M * p) : ℕ) : ℝ) + 1 := by exact_mod_cast hc
      have hdiv : ((N / (M * p) : ℕ) : ℝ) ≤ (N : ℝ) / ((M * p : ℕ) : ℝ) := Nat.cast_div_le
      rw [Nat.cast_mul] at hdiv
      exact hcast.trans (add_le_add_left hdiv 1)
    _ = _ := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro p hp
      simp only [add_mul, one_mul, div_eq_mul_inv, mul_inv_rev]
      ac_rfl

end A082957Certificate

namespace A082957Certificate

open Finset

theorem count_or_le {P Q : ℕ → Prop} [DecidablePred P] [DecidablePred Q] (N : ℕ) :
    Nat.count (fun n => P n ∨ Q n) N ≤ Nat.count P N + Nat.count Q N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.count_succ, Nat.count_succ, Nat.count_succ]
    by_cases hP : P N
    · by_cases hQ : Q N <;> (simp [hP, hQ]; omega)
    · by_cases hQ : Q N <;> (simp [hP, hQ]; omega)

theorem count_prefix_le (n₀ N : ℕ) : Nat.count (fun n => n < n₀) N ≤ n₀ := by
  rw [Nat.count_eq_card_filter_range]
  calc
    _ ≤ (range n₀).card := card_mono (fun n h => mem_range.2 (mem_filter.1 h).2)
    _ = _ := card_range _

theorem divisorTail_nonneg (Y : ℕ) (side : Bool) (n : ℕ) : 0 ≤ divisorTail Y side n := by
  refine sum_nonneg (fun p hp => ?_)
  have hpart := prime_tailWeight_nonneg (mem_filter.1 hp).2.2
  by_cases h : p ∣ 2 * n + (if side then 1 else 0)
  · simpa only [if_pos h] using hpart
  · simp only [if_neg h, le_refl]

theorem class_tail_count_mul_le (Y M a : ℕ) (side : Bool) (u : ℝ) (N : ℕ) :
    (Nat.count (fun n => n ≡ a [MOD M] ∧ u ≤ divisorTail Y side n) N : ℝ) * u ≤
      ∑ n ∈ (range N).filter (fun n => n ≡ a [MOD M]), divisorTail Y side n := by
  classical
  rw [← sum_indicator_class]
  refine sum_le_sum (fun n _ => ?_)
  split_ifs with h
  · exact h
  · exact divisorTail_nonneg Y side n

theorem class_count_lower {M : ℕ} (hM : 0 < M) (a N : ℕ) :
    (N : ℝ) / M - 1 ≤ (Nat.count (fun n => n ≡ a [MOD M]) N : ℝ) := by
  have hcast : (0 : ℝ) < M := by exact_mod_cast hM
  have hmod := Nat.mod_lt N hM
  have hsum := Nat.div_add_mod N M
  have hb : N ≤ (N / M + 1) * M := by
    rw [Nat.add_mul, one_mul]
    rw [Nat.mul_comm M] at hsum
    omega
  have h : (N : ℝ) / M ≤ ((N / M : ℕ) : ℝ) + 1 := by
    apply (div_le_iff₀ hcast).2
    exact_mod_cast hb
  have hlow := (count_modeq_bounds (N := N) (r := a) hM).1
  have hlow' : ((N / M : ℕ) : ℝ) ≤ (Nat.count (fun n => n ≡ a [MOD M]) N : ℝ) := by
    exact_mod_cast hlow
  linarith

theorem class_good_count {Y M : ℕ} (hY : 2 ≤ Y) (hM : 0 < M)
    (hC : ∀ p : ℕ, p.Prime → Y < p → M.Coprime p) (a : ℕ)
    (side : Bool) {u : ℝ} (hu : 0 < u) (b : ℝ) (N n₀ : ℕ)
    (P : ℕ → Prop) [DecidablePred P]
    (hMean : (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p / (p : ℝ)) ≤ b)
    (hGood : ∀ n, n₀ ≤ n → n ≡ a [MOD M] → divisorTail Y side n < u → P n) :
    (N : ℝ) / M * (1 - b / u) -
        (1 + (n₀ : ℝ) + (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / u) ≤
      (Nat.count (fun n => n ≡ a [MOD M] ∧ P n) N : ℝ) := by
  classical
  let isClass := fun n : ℕ => n ≡ a [MOD M]
  let isGood := fun n : ℕ => isClass n ∧ P n
  let isBad := fun n : ℕ => isClass n ∧ u ≤ divisorTail Y side n
  let isPrefix := fun n : ℕ => n < n₀
  have hcount : Nat.count isClass N ≤ Nat.count isGood N + Nat.count isBad N + n₀ := by
    calc
      _ ≤ Nat.count (fun n => (isGood n ∨ isBad n) ∨ isPrefix n) N := by
        refine Nat.count_mono_left (fun n _ hcls => ?_)
        by_cases hlarge : n₀ ≤ n
        · by_cases htail : divisorTail Y side n < u
          · exact Or.inl (Or.inl ⟨hcls, hGood n hlarge hcls htail⟩)
          · exact Or.inl (Or.inr ⟨hcls, le_of_not_gt htail⟩)
        · exact Or.inr (Nat.lt_of_not_ge hlarge)
      _ ≤ _ := (count_or_le N).trans (Nat.add_le_add (count_or_le N) (count_prefix_le n₀ N))
  have hcountR : (Nat.count isClass N : ℝ) ≤
      (Nat.count isGood N : ℝ) + (Nat.count isBad N : ℝ) + (n₀ : ℝ) := by exact_mod_cast hcount
  have hlarge : (Nat.count isBad N : ℝ) ≤
      ((N : ℝ) / M * b + ∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / u := by
    apply (le_div_iff₀ hu).2
    calc
      _ ≤ _ := class_tail_count_mul_le Y M a side u N
      _ ≤ _ := tail_residue_sum_le hY hM hC a side N
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hMean
        (show 0 ≤ (N : ℝ) / M by positivity)) _
  have hsmall : (N : ℝ) / M - 1 ≤ (Nat.count isClass N : ℝ) := class_count_lower hM a N
  change _ ≤ (Nat.count isGood N : ℝ)
  rw [add_div] at hlarge
  have heq : ((N : ℝ) / M * b) / u = (N : ℝ) / M * (b / u) := by ring
  rw [heq] at hlarge
  rw [mul_sub, mul_one]
  linarith

end A082957Certificate

namespace A082957Certificate

open Finset Filter
open scoped Topology

theorem count_partitions_by_residue {M : ℕ} (hM : 0 < M) (P : ℕ → Prop)
    [DecidablePred P] (N : ℕ) :
    Nat.count P N = ∑ a : Fin M, Nat.count (fun n => n ≡ a.val [MOD M] ∧ P n) N := by
  let residue : ℕ → Fin M := fun n => ⟨n % M, Nat.mod_lt _ hM⟩
  simp only [Nat.count_eq_card_filter_range]
  rw [card_eq_sum_card_fiberwise (f := residue) (t := univ) (fun n _ => mem_univ (residue n))]
  refine sum_congr rfl (fun a _ => congrArg Finset.card ?_)
  ext n
  have ha : (residue n = a) ↔ n ≡ a.val [MOD M] := by
    rw [Fin.ext_iff, Nat.ModEq, Nat.mod_eq_of_lt a.isLt]
  simp only [mem_filter, ha]
  tauto

theorem count_selected_residues_le {M : ℕ} (hM : 0 < M) (I : Finset (Fin M))
    (P : ℕ → Prop) [DecidablePred P] (N : ℕ) :
    (∑ a ∈ I, Nat.count (fun n => n ≡ a.val [MOD M] ∧ P n) N) ≤ Nat.count P N := by
  rw [count_partitions_by_residue hM P N]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ I) (fun _ _ _ => Nat.zero_le _)

theorem aggregate_class_density_le {Y M : ℕ} (hY : 2 ≤ Y) (hM : 0 < M)
    (hC : ∀ p : ℕ, p.Prime → Y < p → M.Coprime p)
    (I : Finset (Fin M)) (side : Bool) (b : ℝ) (u : Fin M → ℝ)
    (hu : ∀ a ∈ I, 0 < u a) (n₀ : ℕ)
    (P : ℕ → Prop) [DecidablePred P] (q : ℝ)
    (hMean : ∀ U, (∑ p ∈ tailPrimes Y U, tailWeight p / (p : ℝ)) ≤ b)
    (hErr : Tendsto (fun N : ℕ => (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / (N : ℝ))
      atTop (𝓝 0))
    (hGood : ∀ a ∈ I, ∀ n, n₀ ≤ n → n ≡ a.val [MOD M] → divisorTail Y side n < u a → P n)
    (hQ : ∀ᶠ N : ℕ in atTop, (Nat.count P N : ℝ) / (N : ℝ) ≤ q)
    : (∑ a ∈ I, (1 - b / u a) / (M : ℝ)) ≤ q := by
  have hLoc {N : ℕ} (hN : 0 < N) (a : Fin M) (ha : a ∈ I) :
      (1 - b / u a) / (M : ℝ) -
        ((1 + (n₀ : ℝ)) / (N : ℝ) +
          ((∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / (N : ℝ)) / u a) ≤
      (Nat.count (fun n => n ≡ a.val [MOD M] ∧ P n) N : ℝ) / (N : ℝ) := by
    have h := class_good_count hY hM hC a.val side (hu a ha) b N n₀ P
      (hMean _) (hGood a ha)
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have hu' := hu a ha
    have hdiv := div_le_div_of_nonneg_right h hN'.le
    have he : (1 - b / u a) / (M : ℝ) -
        ((1 + (n₀ : ℝ)) / (N : ℝ) +
          ((∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / (N : ℝ)) / u a) =
      ((N : ℝ) / M * (1 - b / u a) -
        (1 + (n₀ : ℝ) + (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / u a)) / (N : ℝ) := by
      field_simp [hN'.ne', hM'.ne', hu'.ne'] <;> ring
    rwa [he]
  let errorFixed : ℕ → ℝ := fun N => (1 + (n₀ : ℝ)) / (N : ℝ)
  let errorTail : ℕ → ℝ := fun N => (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / (N : ℝ)
  have hfix : Tendsto errorFixed atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have htotal : Tendsto (fun N : ℕ =>
      ∑ a ∈ I, ((1 - b / u a) / (M : ℝ) - (errorFixed N + errorTail N / u a)))
    atTop (𝓝 (∑ a ∈ I, (1 - b / u a) / (M : ℝ))) := by
    refine tendsto_finset_sum _ (fun a ha => ?_)
    have hzero : Tendsto (fun N => errorFixed N + errorTail N / u a) atTop (𝓝 0) := by
      simpa using hfix.add (hErr.div_const (u a))
    simpa using tendsto_const_nhds.sub hzero
  apply le_of_tendsto htotal
  filter_upwards [hQ, eventually_gt_atTop (0 : ℕ)] with N hq hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hcount : (∑ a ∈ I, (Nat.count (fun n => n ≡ a.val [MOD M] ∧ P n) N : ℝ)) ≤
      (Nat.count P N : ℝ) := by exact_mod_cast count_selected_residues_le hM I P N
  calc
    _ ≤ ∑ a ∈ I, (Nat.count (fun n => n ≡ a.val [MOD M] ∧ P n) N : ℝ) / (N : ℝ) :=
      sum_le_sum (hLoc hN)
    _ ≤ (Nat.count P N : ℝ) / (N : ℝ) := by
      simp only [div_eq_mul_inv, ← sum_mul]
      exact mul_le_mul_of_nonneg_right hcount (inv_nonneg.2 hpos.le)
    _ ≤ q := hq


theorem aggregate_class_density_open_thresholds_le {Y M : ℕ} (hY : 2 ≤ Y) (hM : 0 < M)
    (hC : ∀ p : ℕ, p.Prime → Y < p → M.Coprime p)
    (I : Finset (Fin M)) (side : Bool) (b : ℝ) (score : Fin M → ℝ)
    (hScore : ∀ a ∈ I, 0 < score a)
    (P : ℕ → Prop) [DecidablePred P] (q : ℝ)
    (hMean : ∀ U, (∑ p ∈ tailPrimes Y U, tailWeight p / (p : ℝ)) ≤ b)
    (hErr : Tendsto (fun N : ℕ => (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / (N : ℝ))
      atTop (𝓝 0))
    (hGood : ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∃ n₀ : ℕ, ∀ a ∈ I, ∀ n,
      n₀ ≤ n → n ≡ a.val [MOD M] → divisorTail Y side n < θ * score a → P n)
    (hQ : ∀ᶠ N : ℕ in atTop, (Nat.count P N : ℝ) / (N : ℝ) ≤ q)
    : (∑ a ∈ I, (1 - b / score a) / (M : ℝ)) ≤ q := by
  have hθ : ∀ θ ∈ Set.Ioo (0 : ℝ) 1,
      (∑ a ∈ I, (1 - b / (θ * score a)) / (M : ℝ)) ≤ q := by
    intro θ h
    obtain ⟨n₀, hn₀⟩ := hGood θ h
    exact aggregate_class_density_le hY hM hC I side b (fun a => θ * score a)
      (fun a ha => mul_pos h.1 (hScore a ha)) n₀ P q hMean hErr hn₀ hQ
  have hnb : NeBot (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ)) := by
    apply mem_closure_iff_nhdsWithin_neBot.1
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  let : NeBot (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ)) := hnb
  have ht : Tendsto (fun θ : ℝ => ∑ a ∈ I, (1 - b / (θ * score a)) / (M : ℝ))
      (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ))
      (𝓝 (∑ a ∈ I, (1 - b / score a) / (M : ℝ))) := by
    refine tendsto_finset_sum _ (fun a ha => ?_)
    have hid : Tendsto id (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hp : Tendsto (fun θ : ℝ => θ * score a) (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ))
        (𝓝 (score a)) := by
      simpa only [id_eq, one_mul] using hid.mul_const (score a)
    have hb : Tendsto (fun _ : ℝ => b) (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ)) (𝓝 b) :=
      tendsto_const_nhds
    have hOne : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[Set.Ioo (0 : ℝ) 1] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    exact (hOne.sub (hb.div hp (hScore a ha).ne')).div_const (M : ℝ)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with θ h
  exact hθ θ h

end A082957Certificate

namespace A082957Certificate

open Finset

theorem tailWeight_div_telescope {p : ℕ} (hp : 1 < p) :
    tailWeight p / (p : ℝ) = ((p : ℝ) - 1)⁻¹ - (p : ℝ)⁻¹ := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp
  have hp₀ : (p : ℝ) ≠ 0 := by linarith
  have hp₁ : (p : ℝ) - 1 ≠ 0 := by linarith
  unfold tailWeight
  field_simp [hp₀, hp₁] <;> ring

theorem integer_tail_exact {K U : ℕ} (hK : 0 < K) (hKU : K ≤ U) :
    (∑ p ∈ Ioc K U, tailWeight p / (p : ℝ)) =
      (K : ℝ)⁻¹ - (U : ℝ)⁻¹ := by
  induction U, hKU using Nat.le_induction with
  | base => simp
  | succ U hU ih =>
    rw [sum_Ioc_succ_top hU, ih, tailWeight_div_telescope (by omega)]
    push_cast
    ring

theorem integer_tail_le {K : ℕ} (hK : 0 < K) (U : ℕ) :
    (∑ p ∈ Ioc K U, tailWeight p / (p : ℝ)) ≤ (K : ℝ)⁻¹ := by
  by_cases h : K ≤ U
  · rw [integer_tail_exact hK h]
    exact sub_le_self _ (by positivity)
  · have hset : Ioc K U = ∅ := Ioc_eq_empty (by omega)
    rw [hset, sum_empty]
    positivity

def ceilCount (q d : ℕ) : ℕ := (q + d - 1) / d

theorem ceilCount_upper {q d : ℕ} (hd : 0 < d) : (q : ℝ) / d ≤ (ceilCount q d : ℝ) := by
  have hmod := Nat.mod_lt (q + d - 1) hd
  have hsum := Nat.div_add_mod (q + d - 1) d
  rw [Nat.mul_comm d] at hsum
  have h : q ≤ ceilCount q d * d := by unfold ceilCount; omega
  apply (div_le_iff₀ (by exact_mod_cast hd)).2
  exact_mod_cast h

def tailBoundScale : ℕ := 2 ^ 60

def tailBoundNumerator (K : ℕ) : ℕ :=
  (∑ p ∈ tailPrimes 1500 K, ceilCount tailBoundScale (p * (p - 1))) + ceilCount tailBoundScale K

theorem finite_tail_le_certificate {K : ℕ} (hK : 0 < K)
    (hNum : 9700 * tailBoundNumerator K ≤ tailBoundScale) :
    (∑ p ∈ tailPrimes 1500 K, tailWeight p / (p : ℝ)) + (K : ℝ)⁻¹ ≤
      (1 : ℝ) / 9700 := by
  have hQn : 0 < tailBoundScale := by decide
  have hQ : (0 : ℝ) < tailBoundScale := by exact_mod_cast hQn
  have hcheck : (9700 : ℝ) * (tailBoundNumerator K : ℝ) ≤ tailBoundScale := by
    exact_mod_cast hNum
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 9700)).2
  have hfloor :
      (tailBoundScale : ℝ) *
        ((∑ p ∈ tailPrimes 1500 K, tailWeight p / (p : ℝ)) + (K : ℝ)⁻¹) ≤
      (tailBoundNumerator K : ℝ) := by
    unfold tailBoundNumerator
    push_cast
    rw [mul_add, mul_sum]
    apply add_le_add
    · refine sum_le_sum (fun p hp => ?_)
      have hprime : p.Prime := (mem_filter.1 hp).2.2
      have hm : 0 < p * (p - 1) := Nat.mul_pos hprime.pos (Nat.sub_pos_of_lt hprime.one_lt)
      have hcast : ((p * (p - 1) : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub hprime.one_lt.le, Nat.cast_one]
      have h := ceilCount_upper (q := tailBoundScale) hm
      rw [hcast] at h
      have hpos : (1 : ℝ) < p := by exact_mod_cast hprime.one_lt
      have hp₀ : (p : ℝ) ≠ 0 := by linarith
      have hp₁ : (p : ℝ) - 1 ≠ 0 := by linarith
      have he : (tailBoundScale : ℝ) * (tailWeight p / (p : ℝ)) =
          (tailBoundScale : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        unfold tailWeight
        field_simp [hp₀, hp₁] <;> ring
      rw [he]
      exact h
    · have h := ceilCount_upper (q := tailBoundScale) hK
      simpa [div_eq_mul_inv] using h
  apply (mul_le_mul_iff_right₀ hQ).1
  calc
    _ = (9700 : ℝ) * ((tailBoundScale : ℝ) *
          ((∑ p ∈ tailPrimes 1500 K, tailWeight p / (p : ℝ)) + (K : ℝ)⁻¹)) := by ring
    _ ≤ (9700 : ℝ) * (tailBoundNumerator K : ℝ) := mul_le_mul_of_nonneg_left hfloor (by norm_num)
    _ ≤ (tailBoundScale : ℝ) * 1 := by simpa only [mul_one] using hcheck

theorem tail_mean_le {K : ℕ} (hK : 0 < K) (hNum : 9700 * tailBoundNumerator K ≤ tailBoundScale) (U : ℕ) :
    (∑ p ∈ tailPrimes 1500 U, tailWeight p / (p : ℝ)) ≤ (1 : ℝ) / 9700 := by
  have hsub : tailPrimes 1500 U ⊆ tailPrimes 1500 K ∪ Ioc K U := by
    intro p hp
    simp only [tailPrimes, mem_filter, mem_range] at hp
    rw [mem_union]
    by_cases h : p ≤ K
    · exact Or.inl (mem_filter.2 ⟨mem_range.2 (by omega), hp.2⟩)
    · exact Or.inr (mem_Ioc.2 ⟨by omega, by omega⟩)
  have hd : Disjoint (tailPrimes 1500 K) (Ioc K U) := by
    refine disjoint_left.2 (fun p hp hq => ?_)
    have hl := mem_range.1 (mem_filter.1 hp).1
    have ht := (mem_Ioc.1 hq).1
    omega
  calc
    _ ≤ ∑ p ∈ tailPrimes 1500 K ∪ Ioc K U, tailWeight p / (p : ℝ) := by
      refine sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)
      have h : 1 ≤ p := by
        rcases mem_union.1 hp with ha | hb
        · exact (mem_filter.1 ha).2.2.one_lt.le
        · have hh := (mem_Ioc.1 hb).1
          omega
      have hc : (1 : ℝ) ≤ p := by exact_mod_cast h
      unfold tailWeight
      positivity
    _ = _ + _ := sum_union hd
    _ ≤ _ + (K : ℝ)⁻¹ := add_le_add_right (integer_tail_le hK U) _
    _ ≤ _ := finite_tail_le_certificate hK hNum

end A082957Certificate

namespace A082957Certificate

open Finset Filter A082957Analysis A082957Bridge
open scoped Topology

theorem signed_small_le_full_add_tail {Y n : ℕ} (h : Y ≤ 2 * n + 1) (reverse : Bool) :
    (∑ p ∈ A082957Tail.primesThrough Y, signedContribution reverse p n) ≤
      (if reverse then -(A082957Tail.full logContribution n) else A082957Tail.full logContribution n) +
        divisorTail Y reverse n := by
  let S := A082957Tail.primesThrough Y
  let T := A082957Tail.primesThrough (2 * n + 1)
  have hSub : S ⊆ T := fun p hp => mem_filter.mpr
    ⟨mem_range.mpr ((mem_range.mp (mem_filter.mp hp).1).trans_le (Nat.succ_le_succ h)),
      (mem_filter.mp hp).2⟩
  have hDiff : T \ S = tailPrimes Y (2 * n + 1) := by
    apply Finset.ext
    intro p
    rw [Finset.mem_sdiff]
    simp only [S, T, A082957Tail.primesThrough, tailPrimes, mem_filter, mem_range]
    constructor
    · rintro ⟨⟨hu, hp⟩, hnot⟩
      refine ⟨hu, ?_, hp⟩
      by_contra! hne
      exact hnot ⟨by omega, hp⟩
    · rintro ⟨hu, hlo, hp⟩
      exact ⟨⟨hu, hp⟩, fun q => (Nat.not_lt_of_ge (by omega : Y + 1 ≤ p)) q.1⟩
  have hLocal {p : ℕ} (hp : p.Prime) (side : Bool) :
      Real.log (valuationRatio p (padicValNat p (2 * n + (if side then 1 else 0)))) ≤
        if p ∣ 2 * n + (if side then 1 else 0) then tailWeight p else 0 := by
    by_cases hd : p ∣ 2 * n + (if side then 1 else 0)
    · rw [if_pos hd]
      simpa only [tailWeight, one_div] using log_valuationRatio_le hp.two_le
        (padicValNat p (2 * n + (if side then 1 else 0)))
    · rw [if_neg hd, padicValNat.eq_zero_of_not_dvd hd, valuationRatio_zero, Real.log_one]
  have hTail : -(∑ p ∈ T \ S, signedContribution reverse p n) ≤ divisorTail Y reverse n := by
    rw [hDiff, ← sum_neg_distrib]
    apply sum_le_sum
    intro p hp
    have hp' := (mem_filter.mp hp).2.2
    have hn₀ := Real.log_nonneg (valuationRatio_ge_one p (padicValNat p (2 * n)))
    have hn₁ := Real.log_nonneg (valuationRatio_ge_one p (padicValNat p (2 * n + 1)))
    cases reverse with
    | false =>
      have hb := hLocal hp' false
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb ⊢
      unfold signedContribution logContribution
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact le_trans (by linarith) hb
    | true =>
      have hb := hLocal hp' true
      simp only [↓reduceIte] at hb ⊢
      unfold signedContribution logContribution
      simp only [↓reduceIte, neg_neg]
      exact le_trans (by linarith) hb
  have hsum : (∑ p ∈ T \ S, signedContribution reverse p n) +
      ∑ p ∈ S, signedContribution reverse p n = ∑ p ∈ T, signedContribution reverse p n :=
    sum_sdiff hSub
  have hfull : (∑ p ∈ T, signedContribution reverse p n) =
      (if reverse then -(A082957Tail.full logContribution n) else A082957Tail.full logContribution n) := by
    cases reverse <;> simp [T, signedContribution, A082957Tail.full, A082957Tail.small, sum_neg_distrib]
  rw [← hfull]
  change (∑ p ∈ S, signedContribution reverse p n) ≤ _
  linarith

theorem frequency_complement_of_pos (P : ℕ → Prop) [DecidablePred P] {N : ℕ} (hN : 0 < N) :
    frequency (fun n => ¬ P n) N = 1 - frequency P N := by
  have hCard := card_filter_add_card_filter_not (s := range N) P
  rw [card_range] at hCard
  have hCast : (((range N).filter P).card : ℝ) +
      (((range N).filter (fun n => ¬ P n)).card : ℝ) = (N : ℝ) := by exact_mod_cast hCard
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [frequency_eq_count P N, frequency_eq_count (fun n => ¬P n) N, Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range]
  field_simp [hN'.ne']
  linarith

theorem gain_le_frequency_limit {Y M : ℕ} (hY : 2 ≤ Y) (hM : 0 < M)
    (hC : ∀ p, p.Prime → Y < p → M.Coprime p) (hMean : ∀ U,
      (∑ p ∈ tailPrimes Y U, tailWeight p / (p : ℝ)) ≤ (1 : ℝ) / 9700)
    (reverse : Bool) (score : ℕ → ℝ) (hPeriod : ∀ {n a}, n ≡ a [MOD M] → score n = score a)
    (hScore : ∀ {n}, 0 < n → score n ≤ ∑ p ∈ A082957Tail.primesThrough Y, signedContribution reverse p n)
    (lo : ℝ) (hlo : 0 < lo) (hMin : ∀ n, 0 < score n → lo ≤ score n) {δ : ℝ}
    (hDensity : Tendsto (frequency (fun n => 1 ≤ n ∧
      (∑ d ∈ (2 * n).divisors, d) < ∑ d ∈ (2 * n + 1).divisors, d)) atTop (𝓝 δ)) :
    (∑ a ∈ univ.filter (fun a : Fin M => 0 < score a.val),
      (1 - ((1 : ℝ) / 9700) / score a.val) / (M : ℝ)) ≤ if reverse then 1 - δ else δ := by
  classical
  let P (n : ℕ) := 1 ≤ n ∧ (∑ d ∈ (2 * n).divisors, d) < ∑ d ∈ (2 * n + 1).divisors, d
  let Pdir (n : ℕ) := if reverse then ¬ P n else P n
  let limit := if reverse then 1 - δ else δ
  let I := univ.filter (fun a : Fin M => 0 < score a.val)
  have hPdir : Tendsto (frequency Pdir) atTop (𝓝 limit) := by
    cases reverse with
    | false => exact hDensity
    | true =>
      refine (tendsto_const_nhds.sub hDensity).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      exact (frequency_complement_of_pos P hN).symm
  have hErr : Tendsto (fun N : ℕ => (∑ p ∈ tailPrimes Y (2 * N + 1), tailWeight p) / (N : ℝ))
      atTop (𝓝 0) := by
    simpa only [tailWeight, one_div] using A082957Tail.correction_tendsto
      (fun N : ℕ => tailPrimes Y (2 * N + 1)) (fun N p hp =>
        ⟨(mem_filter.mp hp).2.2.two_le, mem_range.mp (mem_filter.mp hp).1⟩)
  have hGood (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) : ∃ n₀ : ℕ, ∀ a ∈ I, ∀ n,
      n₀ ≤ n → n ≡ a.val [MOD M] → divisorTail Y reverse n < θ * score a.val → Pdir n := by
    have hevent : ∀ᶠ n : ℕ in atTop, |threshold n| < (1 - θ) * lo := by
      simpa only [Real.dist_eq, sub_zero] using
        Metric.tendsto_nhds.mp threshold_limit ((1 - θ) * lo) (mul_pos (sub_pos.mpr hθ.2) hlo)
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
    refine ⟨max N₀ (Y + 1), ?_⟩
    intro a ha n hn hm ht
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hnY : Y + 1 ≤ n := (le_max_right _ _).trans hn
    have hPos : 0 < score a.val := (mem_filter.mp ha).2
    have hAbs : |threshold n| < (1 - θ) * score a.val :=
      (hN₀ n hn₀).trans_le (mul_le_mul_of_nonneg_left (hMin _ hPos) (sub_nonneg.mpr hθ.2.le))
    have hsmall := (hScore (by omega : 0 < n)).trans
      (signed_small_le_full_add_tail (by omega : Y ≤ 2 * n + 1) reverse)
    rw [hPeriod hm] at hsmall
    obtain ⟨hl, hu⟩ := abs_lt.mp hAbs
    have hCompare := compare_divisor_sums n
    cases reverse with
    | false =>
      change P n
      apply hCompare.mp
      simp only [Bool.false_eq_true, ↓reduceIte] at hsmall
      linarith
    | true =>
      change ¬ P n
      intro hp
      have hFull := hCompare.mpr hp
      simp only [↓reduceIte] at hsmall
      linarith
  change (∑ a ∈ I, (1 - ((1 : ℝ) / 9700) / score a.val) / (M : ℝ)) ≤ limit
  apply le_of_forall_pos_le_add
  intro ε hε
  have hQ : ∀ᶠ N : ℕ in atTop, (Nat.count Pdir N : ℝ) / (N : ℝ) ≤ limit + ε := by
    simp_rw [← frequency_eq_count]
    exact (hPdir.eventually (eventually_lt_nhds (lt_add_of_pos_right _ hε))).mono (fun _ h => h.le)
  exact aggregate_class_density_open_thresholds_le hY hM hC I reverse (1 / 9700)
    (fun a => score a.val) (fun _ ha => (mem_filter.mp ha).2) Pdir (limit + ε) hMean hErr hGood hQ

end A082957Certificate

namespace A082957Packing

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem threshold_checks :
    (2 * computationDenominator < 37 * computationNumerator false) ∧
    (17 * computationDenominator < 18 * computationNumerator true) := by
  constructor
  · decide +kernel
  · decide +kernel

end A082957Packing

namespace A082957Effective

open Finset
open scoped BigOperators

private def wheelModulus : ℕ := 788657867364790503552363213932185062295135977687173263294742533244359449963403342920304284011984623904177212138919638830257642790242637105061926624952829931113462857270763317237396988943922445621451664240254033291864131227428294853277524242407573903240321257405579568660226031904170324062351700858796178922222789623703897374720000000000000000000000000000000000000000000000000

private theorem wheelModulus_eq : wheelModulus = Nat.factorial 200 := by decide +kernel

def wheelPrime (p : ℕ) : Bool := decide (p.gcd wheelModulus = 1)

theorem wheelPrime_iff {p : ℕ} (hlo : 1500 < p) (hhi : p ≤ 40000) :
    wheelPrime p = true ↔ p.Prime := by
  rw [wheelPrime, decide_eq_true_eq, wheelModulus_eq]
  constructor
  · intro h
    refine Nat.prime_def_le_sqrt.mpr ⟨by omega, fun d hd hds hdvd => ?_⟩
    have hs : p.sqrt ≤ 200 := Nat.lt_succ_iff.mp
      (Nat.sqrt_lt.mpr (hhi.trans_lt (by decide : 40000 < 201 * 201)))
    have hF : d ∣ Nat.factorial 200 := Nat.dvd_factorial (by omega) (hds.trans hs)
    have hu := Nat.dvd_gcd hdvd hF
    rw [h] at hu
    have hle := Nat.le_of_dvd (by decide : 0 < 1) hu
    omega
  · intro hp
    exact hp.coprime_factorial_of_lt (by omega)

def blockSum (f : ℕ → ℕ) (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => blockSum f start n + f (start + n)

theorem blockSum_eq (f : ℕ → ℕ) (start n : ℕ) :
    blockSum f start n = ∑ j ∈ range n, f (start + j) := by
  induction n with
  | zero => simp [blockSum]
  | succ n ih => rw [blockSum, sum_range_succ, ih]

theorem blockSum_add (f : ℕ → ℕ) (start l r : ℕ) :
    blockSum f start (l + r) = blockSum f start l + blockSum f (start + l) r := by
  simp only [blockSum_eq, sum_range_add, Nat.add_assoc]

def weightedPrime (p : ℕ) : ℕ :=
  if wheelPrime p then ((2 : ℕ) ^ 60 + p * (p - 1) - 1) / (p * (p - 1)) else 0

private theorem blockSum_mul (f : ℕ → ℕ) (start width count : ℕ) :
    blockSum f start (width * count) =
      ∑ k ∈ range count, blockSum f (start + width * k) width := by
  induction count with
  | zero => simp [blockSum]
  | succ count ih =>
    rw [Nat.mul_succ, blockSum_add, ih, sum_range_succ]

private def sums : List ℕ := [
  14442207657714, 10162244122709, 7985437117468, 6820104160167, 5638739132379, 4065848442773, 3208335847439,
  3259372429121, 2907672435815, 2160595061329, 2179006021005, 1691583961015, 1567664406584, 1451945497666,
  1232825878783, 1115408875341, 1166311865741, 871404709664, 892186605334, 855308126132, 708323920442,
  755274791488, 612009136415, 485846811130, 636073361554, 465413232178, 488460766156, 395843522558,
  495264324781, 381074959032, 401842143185, 405775903033, 322747807052, 308169561217, 303675402426,
  300408152937, 265179700657, 243476565192, 223681717823, 249562281487, 187520807127, 236958030304,
  196162417028, 218346615809, 210045757931, 180723242991, 187541282597, 160923638090, 154953543685,
  161903730319, 127197862546, 133777743573, 156270837485, 140944268185, 125949597040, 151374311094,
  127302215967, 114476167463, 115311399551, 103044204074, 100004836052, 97018623928, 98354738342,
  110552840057, 88997227332, 93654569276, 91215888535, 95703861242, 73119188822, 58275103482,
  78790914774, 88904846381, 65911717804, 81708664258, 76868949846, 66664140123, 65016824584,
  60856579264, 72393752269, 60497308334, 66641756404, 60295518343, 63693332130, 55323960042,
  60771635588, 48501285952, 60487458104, 44376722322, 57856706087, 54640742481, 59473770334,
  38756161457, 38031080483, 44699906287, 43798640847, 42973643398, 43866554275, 43030136205,
  40531453893, 43105123254, 42214526082, 39886104102, 32936881756, 33856691830, 34717200040,
  41580477253, 32093085715, 32924755730, 42230796597, 31847581357, 35337783236, 32073968043,
  27603479089, 27142635638, 31761195116, 28746690590, 27046222535, 30252090492, 33296708543,
  24625157137, 28824617934, 20431865149, 29063630062, 31908523631, 27095212814, 27718720215,
  25221223136, 24830702320, 27548138315, 25142719677, 18807314226, 27338869348, 25005381984,
  19915588309, 20571414626, 22129683113, 18199624231, 23286524086, 19447245917, 20913723674,
  22342996984, 22898755906, 18410164476, 18984695689, 22017271496, 17666044702, 15848846859,
  16455722857, 20840701934, 16776977397, 20319896745, 15617635348, 16890156683, 18131550273
]

private def chunkAgrees (i : ℕ) : Prop :=
  blockSum weightedPrime (1501 + 250 * i) 250 = sums.getD i 0

private instance (i : ℕ) : Decidable (chunkAgrees i) := by
  unfold chunkAgrees
  infer_instance

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block0 : ∀ i : Fin 7, chunkAgrees (0 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block1 : ∀ i : Fin 7, chunkAgrees (7 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block2 : ∀ i : Fin 7, chunkAgrees (14 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block3 : ∀ i : Fin 7, chunkAgrees (21 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block4 : ∀ i : Fin 7, chunkAgrees (28 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block5 : ∀ i : Fin 7, chunkAgrees (35 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block6 : ∀ i : Fin 7, chunkAgrees (42 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block7 : ∀ i : Fin 7, chunkAgrees (49 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block8 : ∀ i : Fin 7, chunkAgrees (56 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block9 : ∀ i : Fin 7, chunkAgrees (63 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block10 : ∀ i : Fin 7, chunkAgrees (70 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block11 : ∀ i : Fin 7, chunkAgrees (77 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block12 : ∀ i : Fin 7, chunkAgrees (84 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block13 : ∀ i : Fin 7, chunkAgrees (91 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block14 : ∀ i : Fin 7, chunkAgrees (98 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block15 : ∀ i : Fin 7, chunkAgrees (105 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block16 : ∀ i : Fin 7, chunkAgrees (112 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block17 : ∀ i : Fin 7, chunkAgrees (119 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block18 : ∀ i : Fin 7, chunkAgrees (126 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block19 : ∀ i : Fin 7, chunkAgrees (133 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block20 : ∀ i : Fin 7, chunkAgrees (140 + i.val) := by
  decide +kernel

set_option maxRecDepth 25000 in
set_option maxHeartbeats 0 in
private def block21 : ∀ i : Fin 7, chunkAgrees (147 + i.val) := by
  decide +kernel

private theorem allChunks (i : Fin 154) : chunkAgrees i.val := by
  have verified (b : Fin 22) (r : Fin 7) : chunkAgrees (7 * b.val + r.val) := by
    fin_cases b
    · exact block0 r
    · exact block1 r
    · exact block2 r
    · exact block3 r
    · exact block4 r
    · exact block5 r
    · exact block6 r
    · exact block7 r
    · exact block8 r
    · exact block9 r
    · exact block10 r
    · exact block11 r
    · exact block12 r
    · exact block13 r
    · exact block14 r
    · exact block15 r
    · exact block16 r
    · exact block17 r
    · exact block18 r
    · exact block19 r
    · exact block20 r
    · exact block21 r
  have hi := i.isLt
  have hx : 7 * (i.val / 7) + i.val % 7 = i.val := by omega
  simpa only [hx] using verified ⟨i.val / 7, by omega⟩ ⟨i.val % 7, by omega⟩

set_option maxRecDepth 25000 in
theorem full_block : blockSum weightedPrime 1501 38500 = 89357176421369 := by
  rw [show (38500 : ℕ) = 250 * 154 from rfl, blockSum_mul, ← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin 154, sums.getD i.val 0 := sum_congr rfl fun i _ => allChunks i
    _ = _ := by decide +kernel

end A082957Effective

namespace A082957Certificate

open Finset
open A082957Effective

private theorem weighted_wheel_sum_eq {K : ℕ} (hK : K ≤ 40000) :
    (∑ p ∈ tailPrimes 1500 K, ceilCount tailBoundScale (p * (p - 1))) =
      blockSum weightedPrime 1501 (K - 1500) := by
  have hprimes : tailPrimes 1500 K = (Ico 1501 (K + 1)).filter Nat.Prime := by
    ext p
    simp only [tailPrimes, mem_filter, mem_range, mem_Ico]
    constructor
    · rintro ⟨hu, hl, hp⟩
      exact ⟨⟨by omega, hu⟩, hp⟩
    · rintro ⟨⟨hl, hu⟩, hp⟩
      exact ⟨hu, by omega, hp⟩
  have hWheel : (Ico 1501 (K + 1)).filter (fun p => wheelPrime p = true) =
      (Ico 1501 (K + 1)).filter Nat.Prime := by
    apply filter_congr
    intro p hp
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hp
    exact wheelPrime_iff (by omega) (by omega)
  calc
    _ = ∑ p ∈ (Ico 1501 (K + 1)).filter (fun p => wheelPrime p = true),
        ceilCount tailBoundScale (p * (p - 1)) := by rw [hprimes, hWheel]
    _ = ∑ p ∈ Ico 1501 (K + 1), weightedPrime p := by rw [sum_filter]; rfl
    _ = ∑ j ∈ range (K + 1 - 1501), weightedPrime (1501 + j) := by rw [sum_Ico_eq_sum_range]
    _ = _ := by rw [← blockSum_eq, show K + 1 - 1501 = K - 1500 by omega]

theorem tail_bound_of_wheel {K : ℕ} (hK : K ≤ 40000)
    (hNum : 9700 * (blockSum weightedPrime 1501 (K - 1500) + ceilCount tailBoundScale K) ≤
      tailBoundScale) : 9700 * tailBoundNumerator K ≤ tailBoundScale := by
  rw [tailBoundNumerator, weighted_wheel_sum_eq hK]
  exact hNum

end A082957Certificate

namespace A082957Packing

open Finset Filter A082957Certificate
open scoped Topology

theorem growth_of_effective_tail
    (hMean : ∀ U, (∑ p ∈ tailPrimes 1500 U, tailWeight p / (p : ℝ)) ≤ (1 : ℝ) / 9700)
    (hExact : (2 * computationDenominator < 37 * computationNumerator false) ∧
      (17 * computationDenominator < 18 * computationNumerator true)) :
    type_of% @OMA.S_oeis_a082957.main := by
  obtain ⟨δ, hDensity⟩ := A082957Capped.divisor_comparison_has_density
  have hM : 0 < gridModulus primes := gridModulus_pos (fun p h => ((mem_primes_iff p).mp h).2.2)
  have hGrid : (0 : ℝ) < (grid : ℝ) := by norm_num [grid]
  have hGain (reverse : Bool) : packedDensityBound reverse ≤ if reverse then 1 - δ else δ := by
    let score (n : ℕ) := (gridScore primes reverse n : ℝ) / grid
    have hPer {n a : ℕ} (h : n ≡ a [MOD gridModulus primes]) : score n = score a := by
      simp only [score, gridScore_modeq h reverse]
    have hMin (n : ℕ) (h : 0 < score n) : (1 : ℝ) / grid ≤ score n := by
      change 0 < (gridScore primes reverse n : ℝ) / grid at h
      have hz : 0 < gridScore primes reverse n := by
        exact_mod_cast (div_pos_iff_of_pos_right hGrid).mp h
      have hone : (1 : ℝ) ≤ (gridScore primes reverse n : ℝ) := by
        exact_mod_cast (show (1 : ℤ) ≤ gridScore primes reverse n by omega)
      exact div_le_div_of_nonneg_right hone hGrid.le
    have h := gain_le_frequency_limit (by decide : 2 ≤ 1500) hM
      (fun _ => gridModulus_coprime_tail) hMean reverse score @hPer
      (fun hn => gridScore_le_smallSum hn reverse) (1 / grid) (one_div_pos.mpr hGrid) hMin hDensity
    exact (concretePackedDensityBound_le_residue_gain reverse).trans h
  obtain ⟨hLower, hUpper⟩ := density_between_thresholds hExact.1 hExact.2
    (hGain false) (hGain true)
  exact A082957Analysis.growth_from_density_bounds hDensity hLower hUpper

end A082957Packing

/-- The effective density bounds give the growth constant for the original sequence. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a082957.main := by
  have hSize : (40000 : ℕ) - 1500 = 38500 := by decide
  have hWheel : 9700 * (A082957Effective.blockSum A082957Effective.weightedPrime 1501 (40000 - 1500) +
      A082957Certificate.ceilCount A082957Certificate.tailBoundScale 40000) ≤
      A082957Certificate.tailBoundScale := by
    rw [hSize, A082957Effective.full_block]
    decide +kernel
  have hNum := A082957Certificate.tail_bound_of_wheel (le_rfl : 40000 ≤ 40000) hWheel
  exact A082957Packing.growth_of_effective_tail
    (A082957Certificate.tail_mean_le (by decide : 0 < (40000 : ℕ))
      hNum) A082957Packing.threshold_checks
