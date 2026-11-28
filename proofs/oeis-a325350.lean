import OMAStatements.S_oeis_a325350

open Filter
open scoped Topology PowerSeries.WithPiTopology

namespace OMA.P_a325350

open OMA.S_oeis_a325350

instance instTransGe : Trans (fun a b : ℕ => a ≥ b) (fun a b : ℕ => a ≥ b) (fun a b : ℕ => a ≥ b) :=
  ⟨fun h1 h2 => le_trans h2 h1⟩

/-- Add the ramp `(k, k - 1, ..., 1)` to a list of length `k`. -/
def addR : List ℕ → List ℕ
  | [] => []
  | x :: t => (x + t.length + 1) :: addR t

/-- Subtract the ramp `(k, k - 1, ..., 1)` from a list of length `k`. -/
def subR : List ℕ → List ℕ
  | [] => []
  | x :: t => (x - (t.length + 1)) :: subR t

lemma length_addR (l : List ℕ) : (addR l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [addR, ih]

lemma length_subR (l : List ℕ) : (subR l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [subR, ih]

lemma subR_addR (l : List ℕ) : subR (addR l) = l := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [addR, subR, ih, length_addR]

lemma sum_addR (l : List ℕ) : (addR l).sum = l.sum + l.length * (l.length + 1) / 2 := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [addR, List.sum_cons, ih, List.length_cons]
    have : (t.length + 1) * (t.length + 1 + 1) = t.length * (t.length + 1) + (t.length + 1) * 2 := by
      ring
    rw [this, Nat.add_mul_div_right _ _ (by norm_num)]
    generalize t.length * (t.length + 1) / 2 = c
    omega

lemma augDiff_cons_cons (x z : ℕ) (t : List ℕ) :
    augDiff (x :: z :: t) = (x - z + 1) :: augDiff (z :: t) := by
  simp [augDiff]

lemma augDiff_append_one : ∀ (y : List ℕ), (∀ x ∈ y, 1 ≤ x) → augDiff (y ++ [1]) = augDiff y ++ [1]
  | [], _ => rfl
  | [x], h => by
    have : 1 ≤ x := h x (by simp)
    show augDiff [x, 1] = [x] ++ [1]
    rw [augDiff_cons_cons]
    simp [augDiff]
    omega
  | x :: z :: t, h => by
    have ih := augDiff_append_one (z :: t) (fun w hw => h w (List.mem_cons_of_mem _ hw))
    show augDiff (x :: z :: (t ++ [1])) = augDiff (x :: z :: t) ++ [1]
    rw [augDiff_cons_cons, augDiff_cons_cons, ← List.cons_append, ih]
    rfl

lemma augDiff_append_last : ∀ (y : List ℕ) (b : ℕ), ∃ L, augDiff (y ++ [b]) = L ++ [b]
  | [], b => ⟨[], rfl⟩
  | [x], b => ⟨[x - b + 1], by show augDiff [x, b] = _; rw [augDiff_cons_cons]; rfl⟩
  | x :: z :: t, b => by
    obtain ⟨L, hL⟩ := augDiff_append_last (z :: t) b
    refine ⟨(x - z + 1) :: L, ?_⟩
    show augDiff (x :: z :: (t ++ [b])) = _
    rw [augDiff_cons_cons, ← List.cons_append, hL]
    rfl

lemma augDiff_ge_one : ∀ (y : List ℕ), (∀ x ∈ y, 1 ≤ x) → ∀ e ∈ augDiff y, 1 ≤ e
  | [], _ => by simp [augDiff]
  | [x], h => by simpa [augDiff] using h x (by simp)
  | x :: z :: t, h => by
    rw [augDiff_cons_cons]
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · exact augDiff_ge_one (z :: t) (fun w hw => h w (List.mem_cons_of_mem _ hw)) e he

lemma augDiff_addR : ∀ y : List ℕ, y.IsChain (· ≥ ·) →
    augDiff (addR y) = (augDiff y).map (· + 1)
  | [], _ => rfl
  | [x], _ => by simp [addR, augDiff]
  | x :: z :: t, h => by
    rw [List.isChain_cons_cons] at h
    have ih := augDiff_addR (z :: t) h.2
    have h1 : z ≤ x := h.1
    have e : addR (x :: z :: t) = (x + (t.length + 1) + 1) :: addR (z :: t) := rfl
    have e2 : addR (z :: t) = (z + t.length + 1) :: addR t := rfl
    rw [e, e2, augDiff_cons_cons, ← e2, ih, augDiff_cons_cons, List.map_cons]
    congr 1
    omega

lemma isChain_addR : ∀ y : List ℕ, y.IsChain (· ≥ ·) → (addR y).IsChain (· ≥ ·)
  | [], _ => List.IsChain.nil
  | [x], _ => List.isChain_singleton _
  | x :: z :: t, h => by
    rw [List.isChain_cons_cons] at h
    have ih := isChain_addR (z :: t) h.2
    have e : addR (x :: z :: t) = (x + (t.length + 1) + 1) :: (z + t.length + 1) :: addR t := rfl
    rw [e, List.isChain_cons_cons]
    refine ⟨?_, ih⟩
    have h1 : z ≤ x := h.1
    show z + t.length + 1 ≤ x + (t.length + 1) + 1
    omega

lemma addR_ge_two : ∀ y : List ℕ, (∀ x ∈ y, 1 ≤ x) → ∀ w ∈ addR y, 2 ≤ w
  | [], _ => by simp [addR]
  | x :: t, h => by
    intro w hw
    simp only [addR, List.mem_cons] at hw
    rcases hw with rfl | hw
    · have := h x (by simp); omega
    · exact addR_ge_two t (fun u hu => h u (List.mem_cons_of_mem _ hu)) w hw

lemma subR_spec : ∀ y : List ℕ, (∀ e ∈ augDiff y, 2 ≤ e) →
    addR (subR y) = y ∧ (subR y).IsChain (· ≥ ·) ∧ (∀ x ∈ subR y, 1 ≤ x) ∧
      (∀ x, y.head? = some x → y.length + 1 ≤ x)
  | [], _ => by simp [subR, addR]
  | [x], h => by
    have hx : 2 ≤ x := h x (by simp [augDiff])
    refine ⟨?_, List.isChain_singleton _, ?_, ?_⟩
    · show [x - 1 + 0 + 1] = [x]
      congr 1; omega
    · intro w hw
      simp only [subR, List.length_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      omega
    · intro w hw
      simp only [List.head?_cons, Option.some.injEq] at hw
      simp only [List.length_cons, List.length_nil]
      omega
  | x :: z :: t, h => by
    rw [augDiff_cons_cons] at h
    have hxz : 2 ≤ x - z + 1 := h _ (by simp)
    obtain ⟨ih1, ih2, ih3, ih4⟩ := subR_spec (z :: t) (fun e he => h e (List.mem_cons_of_mem _ he))
    have hz := ih4 z rfl
    simp only [List.length_cons] at hz
    have e : subR (x :: z :: t) = (x - (t.length + 2)) :: subR (z :: t) := rfl
    have e2 : subR (z :: t) = (z - (t.length + 1)) :: subR t := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e]
      show (x - (t.length + 2) + (subR (z :: t)).length + 1) :: addR (subR (z :: t)) = x :: z :: t
      rw [ih1, length_subR]
      simp only [List.length_cons, List.cons.injEq, and_true]
      omega
    · rw [e, e2, List.isChain_cons_cons, ← e2]
      exact ⟨by show z - (t.length + 1) ≤ x - (t.length + 2); omega, ih2⟩
    · rw [e]
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · exact ih3 w hw
    · intro w hw
      simp only [List.head?_cons, Option.some.injEq] at hw
      subst hw
      simp only [List.length_cons]
      omega

/-- Partitions of `n` (as weakly decreasing lists) with the property. -/
def W (n : ℕ) : Finset (List ℕ) :=
  ((Finset.univ : Finset (Nat.Partition n)).image (fun p => p.parts.sort (· ≥ ·))).filter
    (fun y => (augDiff y).Pairwise (· ≥ ·))

/-- Those with exactly `k` parts. -/
def V (k n : ℕ) : Finset (List ℕ) := (W n).filter (fun y => y.length = k)

lemma mem_W {n : ℕ} {y : List ℕ} : y ∈ W n ↔
    y.Pairwise (· ≥ ·) ∧ (∀ x ∈ y, 0 < x) ∧ y.sum = n ∧ (augDiff y).Pairwise (· ≥ ·) := by
  simp only [W, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨p, rfl⟩, h2⟩
    refine ⟨Multiset.pairwise_sort _ _, fun x hx => p.parts_pos (by simpa using hx), ?_, h2⟩
    rw [← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]
  · rintro ⟨h1, h2, h3, h5⟩
    refine ⟨⟨⟨(y : Multiset ℕ), fun hx => h2 _ hx, by simpa using h3⟩, ?_⟩, h5⟩
    simp only [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ h1

lemma mem_V {k n : ℕ} {y : List ℕ} : y ∈ V k n ↔
    y.Pairwise (· ≥ ·) ∧ (∀ x ∈ y, 0 < x) ∧ y.sum = n ∧ (augDiff y).Pairwise (· ≥ ·) ∧
      y.length = k := by
  simp only [V, Finset.mem_filter, mem_W, and_assoc]

lemma a_eq (n : ℕ) : a n = (W n).card := by
  have hinj : Function.Injective (fun p : Nat.Partition n => p.parts.sort (· ≥ ·)) := by
    intro p q h
    apply Nat.Partition.ext
    rw [← Multiset.sort_eq p.parts (· ≥ ·), ← Multiset.sort_eq q.parts (· ≥ ·)]
    exact congrArg _ h
  rw [W, Finset.filter_image, Finset.card_image_of_injective _ hinj]
  rfl

lemma V_eq_empty {k n : ℕ} (h : n < k) : V k n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_V] at hy
  have := List.length_le_sum_of_one_le y (fun i hi => hy.2.1 i hi)
  omega

lemma card_V_zero (n : ℕ) : ((V 0 n).card : ℚ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    have : V 0 0 = {[]} := by
      ext y
      rw [mem_V, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -, -, -, h⟩
        exact List.length_eq_zero_iff.mp h
      · rintro rfl
        simp [augDiff]
    simp [this]
  · have : V 0 n = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y hy
      rw [mem_V] at hy
      obtain ⟨-, -, h3, -, h5⟩ := hy
      rw [List.length_eq_zero_iff] at h5
      subst h5
      simp at h3
      omega
    simp [this, hn]

lemma tri_pos (k : ℕ) : 1 ≤ (k + 1) * (k + 1 + 1) / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

lemma pairwise_append_one {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) :
    (l ++ [1]).Pairwise (· ≥ ·) ↔ l.Pairwise (· ≥ ·) := by
  rw [List.pairwise_append]
  constructor
  · exact fun h' => h'.1
  · intro h'
    refine ⟨h', List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    exact h a ha

lemma card_A (k n : ℕ) :
    ((V (k + 1) (n + 1)).filter (fun y => y.getLast? = some 1)).card = (V k n).card := by
  refine Finset.card_nbij' (fun y => y.dropLast) (fun z => z ++ [1]) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨hy, hl⟩ := hy
    have e := List.dropLast_append_getLast? 1 hl
    simp only [Finset.mem_coe]
    generalize y.dropLast = z at e
    subst e
    rw [mem_V] at hy ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    have hz : ∀ x ∈ z, 1 ≤ x := fun x hx => h2 x (by simp [hx])
    rw [augDiff_append_one z hz, pairwise_append_one (augDiff_ge_one z hz)] at h4
    refine ⟨(List.pairwise_append.mp h1).1, fun x hx => hz x hx, ?_, h4, ?_⟩
    · simp at h3; omega
    · simp at h5; omega
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    rw [mem_V] at hz ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    have hz : ∀ x ∈ z, 1 ≤ x := fun x hx => h2 x hx
    refine ⟨⟨(pairwise_append_one hz).mpr h1, ?_, ?_, ?_, ?_⟩, by simp⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 x hx
      · norm_num
    · simp [h3]
    · rw [augDiff_append_one z hz, pairwise_append_one (augDiff_ge_one z hz)]
      exact h4
    · simp [h5]
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    exact List.dropLast_append_getLast? 1 hy.2
  · intro z _
    simp

lemma aug_ge_two {k m : ℕ} {y : List ℕ} (hy : y ∈ V (k + 1) m) (hl : ¬ y.getLast? = some 1) :
    ∀ e ∈ augDiff y, 2 ≤ e := by
  rw [mem_V] at hy
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy
  rcases hb : y.getLast? with _ | b
  · rw [List.getLast?_eq_none_iff] at hb
    subst hb
    simp at h5
  · rw [hb] at hl
    have hbm : b ∈ y := List.mem_of_getLast? hb
    have hb1 := h2 b hbm
    have hb2 : b ≠ 1 := fun h => hl (by rw [h])
    have e := List.dropLast_append_getLast? b hb
    obtain ⟨L, hL⟩ := augDiff_append_last y.dropLast b
    rw [e] at hL
    rw [hL] at h4 ⊢
    rw [List.pairwise_append] at h4
    intro x hx
    rw [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have := h4.2.2 x hx b (by simp)
      omega
    · omega

lemma card_B (k n : ℕ) (hT : (k + 1) * (k + 1 + 1) / 2 ≤ n + 1) :
    ((V (k + 1) (n + 1)).filter (fun y => ¬ y.getLast? = some 1)).card =
      (V (k + 1) (n + 1 - (k + 1) * (k + 1 + 1) / 2)).card := by
  refine Finset.card_nbij' subR addR ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hy, hl⟩ := hy
    obtain ⟨s1, s2, s3, -⟩ := subR_spec y (aug_ge_two hy hl)
    rw [mem_V] at hy ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy
    have hs := sum_addR (subR y)
    rw [s1, length_subR, h5, h3] at hs
    refine ⟨(List.isChain_iff_pairwise).mp s2, fun x hx => s3 x hx, by omega, ?_, by
      rw [length_subR, h5]⟩
    rw [← s1, augDiff_addR _ s2, List.pairwise_map] at h4
    exact h4.imp (fun h => by omega)
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    rw [mem_V] at hz ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hz
    have hc : z.IsChain (· ≥ ·) := h1.isChain
    have hz1 : ∀ x ∈ z, 1 ≤ x := fun x hx => h2 x hx
    have hs := sum_addR z
    rw [h5, h3] at hs
    refine ⟨⟨(List.isChain_iff_pairwise).mp (isChain_addR z hc),
      fun x hx => by have := addR_ge_two z hz1 x hx; omega, by omega, ?_, by
        rw [length_addR, h5]⟩, ?_⟩
    · rw [augDiff_addR _ hc, List.pairwise_map]
      exact h4.imp (fun h => by omega)
    · intro h
      have := addR_ge_two z hz1 1 (List.mem_of_getLast? h)
      omega
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    exact (subR_spec y (aug_ge_two hy.1 hy.2)).1
  · intro z _
    exact subR_addR z

lemma card_B_empty (k n : ℕ) (hT : ¬ (k + 1) * (k + 1 + 1) / 2 ≤ n + 1) :
    ((V (k + 1) (n + 1)).filter (fun y => ¬ y.getLast? = some 1)).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro y hy hl
  obtain ⟨s1, -, -, -⟩ := subR_spec y (aug_ge_two hy hl)
  rw [mem_V] at hy
  have hs := sum_addR (subR y)
  rw [s1, length_subR, hy.2.2.2.2, hy.2.2.1] at hs
  omega

lemma card_V_succ (k n : ℕ) : ((V (k + 1) (n + 1)).card : ℚ) = (V k n).card +
    (if (k + 1) * (k + 1 + 1) / 2 ≤ n + 1 then
      ((V (k + 1) (n + 1 - (k + 1) * (k + 1 + 1) / 2)).card : ℚ) else 0) := by
  rw [← Finset.card_filter_add_card_filter_not (fun y => y.getLast? = some 1), card_A]
  split_ifs with hT
  · rw [card_B k n hT]; push_cast; ring
  · rw [card_B_empty k n hT]; simp

/-- Generating function of the partitions with `k` parts. -/
noncomputable def F (k : ℕ) : PowerSeries ℚ := PowerSeries.mk (fun n => ((V k n).card : ℚ))

lemma F_zero : F 0 = 1 := by
  ext n
  rw [F, PowerSeries.coeff_mk, card_V_zero, PowerSeries.coeff_one]

lemma F_succ (k : ℕ) : F (k + 1) =
    PowerSeries.X * F k * (1 - PowerSeries.X ^ ((k + 1) * (k + 1 + 1) / 2))⁻¹ := by
  have hT := tri_pos k
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by
    rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega)]
    norm_num)]
  ext n
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow']
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_X_mul]
    simp only [F, PowerSeries.coeff_mk]
    rw [if_neg (by omega), V_eq_empty (by omega)]
    simp
  · rw [PowerSeries.coeff_succ_X_mul]
    simp only [F, PowerSeries.coeff_mk]
    rw [card_V_succ]
    split_ifs <;> ring

lemma F_eq (k : ℕ) : F k = (PowerSeries.X : PowerSeries ℚ) ^ k *
    ∏ j ∈ Finset.Icc 1 k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (j * (j + 1) / 2))⁻¹ := by
  induction k with
  | zero => simp [F_zero]
  | succ k ih =>
    rw [F_succ, ih, Finset.prod_Icc_succ_top (by omega), pow_succ]
    ring

end OMA.P_a325350

open OMA.P_a325350 in
theorem OMA.solution : type_of% @OMA.S_oeis_a325350.main := by
  have hfun : (fun N : ℕ => ∑ k ∈ Finset.range N,
        (PowerSeries.X : PowerSeries ℚ) ^ k *
          ∏ j ∈ Finset.Icc 1 k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (j * (j + 1) / 2))⁻¹) =
      fun N : ℕ => ∑ k ∈ Finset.range N, F k := by
    funext N
    exact Finset.sum_congr rfl (fun k _ => (F_eq k).symm)
  rw [hfun, PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_atTop_of_eventually_const (i₀ := n + 1)
  intro N hN
  rw [map_sum, PowerSeries.coeff_mk, a_eq]
  simp only [F, PowerSeries.coeff_mk]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hN)]
  · norm_cast
    rw [Finset.card_eq_sum_card_fiberwise (f := List.length) (t := Finset.range (n + 1))]
    · rfl
    · intro y hy
      rw [Finset.mem_coe, mem_W] at hy
      have := List.length_le_sum_of_one_le y (fun i hi => hy.2.1 i hi)
      rw [Finset.mem_coe, Finset.mem_range]
      omega
  · intro k _ hk
    rw [Finset.mem_range] at hk
    rw [V_eq_empty (by omega)]
    simp
