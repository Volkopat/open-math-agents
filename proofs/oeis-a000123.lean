import OMAStatements.S_oeis_a000123

/-! Binary partition counts by marking copies of a part and sampling at dyadic intervals. -/

open scoped BigOperators Classical Topology

namespace OMA.BinaryRatio

open Finset Filter
open OMA.S_oeis_a000123 (a)

def binary (w : ℕ) : Prop := ∃ k : ℕ, w = 2 ^ k

abbrev BP (n : ℕ) := {p : Nat.Partition n // ∀ w ∈ p.parts, binary w}

noncomputable def b (n : ℕ) : ℕ := Fintype.card (BP n)

lemma a_eq (n : ℕ) : a n = b (2 * n) := by
  unfold a b
  symm
  apply Fintype.card_of_subtype
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, binary]

lemma binary_one : binary 1 := ⟨0, by simp⟩

lemma binary_pos {w : ℕ} (h : binary w) : 0 < w := by
  obtain ⟨k, rfl⟩ := h
  exact Nat.two_pow_pos k

lemma binary_two_mul {w : ℕ} (h : binary w) : binary (2 * w) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k + 1, by rw [pow_succ']⟩

lemma binary_split {w : ℕ} (h : binary w) (hw : w ≠ 1) :
    2 * (w / 2) = w ∧ binary (w / 2) := by
  obtain ⟨k, rfl⟩ := h
  cases k with
  | zero => simp at hw
  | succ k =>
    simp only [pow_succ', Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
    exact ⟨trivial, ⟨k, rfl⟩⟩

noncomputable def removeCopies {n w j : ℕ} (hw : binary w) (hj : w * j ≤ n) :
    {p : BP n // j ≤ p.val.parts.count w} ≃ BP (n - w * j) where
  toFun p := by
    let s := p.val.val.parts
    have hr : Multiset.replicate j w ≤ s := Multiset.le_count_iff_replicate_le.mp p.property
    have hs : s - Multiset.replicate j w + Multiset.replicate j w = s :=
      tsub_add_cancel_of_le hr
    have hp : (s - Multiset.replicate j w).sum + w * j = n := by
      simpa [s, p.val.val.parts_sum, mul_comm] using congrArg Multiset.sum hs
    refine ⟨⟨s - Multiset.replicate j w, ?_, by omega⟩, ?_⟩
    · intro x hx
      exact p.val.val.parts_pos (Multiset.mem_of_le (tsub_le_self) hx)
    · intro x hx
      exact p.val.property x (Multiset.mem_of_le (tsub_le_self) hx)
  invFun p := by
    refine ⟨⟨⟨p.val.parts + Multiset.replicate j w, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro x hx
      rw [Multiset.mem_add] at hx
      rcases hx with h | h
      · exact p.val.parts_pos h
      · exact (Multiset.eq_of_mem_replicate h) ▸ binary_pos hw
    · simp [p.val.parts_sum, mul_comm j w, Nat.sub_add_cancel hj]
    · intro x hx
      rw [Multiset.mem_add] at hx
      rcases hx with h | h
      · exact p.property x h
      · exact (Multiset.eq_of_mem_replicate h) ▸ hw
    · simp [Multiset.count_add]
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Nat.Partition.ext
    exact tsub_add_cancel_of_le (Multiset.le_count_iff_replicate_le.mp p.property)
  right_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    exact add_tsub_cancel_right _ _

lemma b_mono : Monotone b := by
  apply monotone_nat_of_le_succ
  intro n
  have h := Fintype.card_subtype_le (fun p : BP (n + 1) ↦ 1 ≤ p.val.parts.count 1)
  rw [Fintype.card_congr (removeCopies binary_one (n := n + 1) (j := 1) (by omega))] at h
  simpa [b] using h

lemma b_pos (n : ℕ) : 0 < b n := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨Multiset.replicate n 1, ?_, by simp⟩, ?_⟩⟩
  · intro x hx
    simp [Multiset.eq_of_mem_replicate hx]
  · intro x hx
    exact (Multiset.eq_of_mem_replicate hx) ▸ binary_one

lemma double_half_parts {n : ℕ} (p : BP n) (h : 1 ∉ p.val.parts) :
    (p.val.parts.map (· / 2)).map (2 * ·) = p.val.parts := by
  rw [Multiset.map_map]
  calc
    _ = p.val.parts.map id := by
      apply Multiset.map_congr rfl
      intro w hw
      exact (binary_split (p.property w hw) (by rintro rfl; exact h hw)).1
    _ = _ := Multiset.map_id _

lemma sum_double (s : Multiset ℕ) : (s.map (2 * ·)).sum = 2 * s.sum := by
  simpa using Multiset.sum_map_mul_left (s := s) (f := id) (a := (2 : ℕ))

noncomputable def evenParts (n : ℕ) :
    {p : BP (2 * n) // ¬ 1 ≤ p.val.parts.count 1} ≃ BP n where
  toFun p := by
    have h1 : 1 ∉ p.val.val.parts := fun h ↦ p.property (Multiset.one_le_count_iff_mem.mpr h)
    let s := p.val.val.parts.map (· / 2)
    have hs := congrArg Multiset.sum (double_half_parts p.val h1)
    rw [sum_double, p.val.val.parts_sum] at hs
    refine ⟨⟨s, ?_, by change 2 * s.sum = 2 * n at hs; omega⟩, ?_⟩
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
      exact binary_pos (binary_split (p.val.property x hx) (by rintro rfl; exact h1 hx)).2
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
      exact (binary_split (p.val.property x hx) (by rintro rfl; exact h1 hx)).2
  invFun p := by
    let s := p.val.parts.map (2 * ·)
    refine ⟨⟨⟨s, ?_, by dsimp [s]; rw [sum_double, p.val.parts_sum]⟩, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
      exact Nat.mul_pos (by decide) (p.val.parts_pos hx)
    · intro w hw
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hw
      exact binary_two_mul (p.property x hx)
    · rw [Multiset.one_le_count_iff_mem]
      intro h
      obtain ⟨x, hx, he⟩ := Multiset.mem_map.mp h
      omega
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Nat.Partition.ext
    exact double_half_parts p.val (fun h ↦ p.property (Multiset.one_le_count_iff_mem.mpr h))
  right_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    change ((p.val.parts.map (2 * ·)).map (· / 2)) = p.val.parts
    simp [Multiset.map_map]

lemma b_odd (n : ℕ) : b (2 * n + 1) = b (2 * n) := by
  have h (p : BP (2 * n + 1)) : 1 ≤ p.val.parts.count 1 := by
    rw [Multiset.one_le_count_iff_mem]
    by_contra h1
    have hs := congrArg Multiset.sum (double_half_parts p h1)
    rw [sum_double, p.val.parts_sum] at hs
    omega
  let e : BP (2 * n + 1) ≃ {p : BP (2 * n + 1) // 1 ≤ p.val.parts.count 1} :=
    { toFun := fun p ↦ ⟨p, h p⟩
      invFun := Subtype.val
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (Fintype.card_congr e).trans (by
    simpa [b] using Fintype.card_congr (removeCopies binary_one (n := 2 * n + 1) (j := 1) (by omega)))

lemma b_even_succ (n : ℕ) : b (2 * (n + 1)) = b (2 * n) + b (n + 1) := by
  let P (p : BP (2 * (n + 1))) := 1 ≤ p.val.parts.count 1
  have hc := Fintype.card_subtype_compl P
  have h₁ : Fintype.card {p // P p} = b (2 * n + 1) := by
    change Fintype.card {p : BP (2 * (n + 1)) // 1 ≤ p.val.parts.count 1} = b (2 * n + 1)
    have h := Fintype.card_congr (removeCopies binary_one (n := 2 * (n + 1)) (j := 1) (by omega))
    simpa [b, show 2 * (n + 1) - 1 * 1 = 2 * n + 1 by omega] using h
  have h₂ : Fintype.card {p // ¬ P p} = b (n + 1) := Fintype.card_congr (evenParts (n + 1))
  rw [h₁, h₂, b_odd] at hc
  change b (n + 1) = b (2 * (n + 1)) - b (2 * n) at hc
  have hle : b (2 * n) ≤ b (2 * (n + 1)) := b_mono (by omega)
  omega

def partialSum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ j ∈ range n, f j

lemma prefix_succ (f : ℕ → ℕ) (n : ℕ) : partialSum f (n + 1) = partialSum f n + f n :=
  sum_range_succ f n

lemma prefix_b_even (n : ℕ) : partialSum b (2 * n) = 2 * partialSum a n := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, prefix_succ, prefix_succ, ih,
      b_odd, ← a_eq, prefix_succ]
    omega

lemma a_double (n : ℕ) : a (2 * n) = 2 * partialSum a n + a n := by
  have h (k : ℕ) : b (2 * k) = partialSum b k + b k := by
    induction k with
    | zero => simp [partialSum]
    | succ k ih =>
      rw [b_even_succ, ih, prefix_succ]
  rw [a_eq, h, prefix_b_even, ← a_eq]

def sample (f : ℕ → ℕ) (n w : ℕ) : ℕ :=
  w * ∑ j ∈ range (n / w), f (n - w * (j + 1))

lemma sample_one (f : ℕ → ℕ) (n : ℕ) : sample f n 1 = partialSum f n := by
  simpa [sample, partialSum, Nat.sub_sub, Nat.add_comm] using sum_range_reflect f n

lemma sample_add (f : ℕ → ℕ) (n w : ℕ) (hw : 0 < w) :
    sample f (n + w) w = w * f n + sample f n w := by
  unfold sample
  rw [Nat.add_div_of_dvd_left (dvd_refl w), Nat.div_self hw, sum_range_succ']
  simp only [zero_add, mul_one, Nat.add_sub_cancel, mul_add]
  rw [add_comm (w * f n)]
  congr 1
  apply congrArg (w * ·)
  apply sum_congr rfl
  intro j _
  congr 1
  omega

lemma prefix_add (f : ℕ → ℕ) (n w : ℕ) :
    partialSum f (n + w) = partialSum f n + ∑ j ∈ range w, f (n + j) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [← Nat.add_assoc, prefix_succ, ih, sum_range_succ, add_assoc]

lemma sample_bounds {f : ℕ → ℕ} (hf : Monotone f) (w : ℕ) (hw : 0 < w) (n : ℕ) :
    sample f n w ≤ partialSum f n ∧ partialSum f n ≤ sample f n w + w * f n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < w
    · have hzero : sample f n w = 0 := by simp [sample, Nat.div_eq_of_lt h]
      rw [hzero, zero_add]
      refine ⟨Nat.zero_le _, ?_⟩
      calc
        partialSum f n ≤ ∑ _ ∈ range n, f n :=
          sum_le_sum fun j hj ↦ hf (mem_range.mp hj).le
        _ = n * f n := by simp
        _ ≤ w * f n := Nat.mul_le_mul_right _ h.le
    · have hle : w ≤ n := Nat.le_of_not_gt h
      obtain ⟨h₁, h₂⟩ := ih (n - w) (by omega)
      have hLo : w * f (n - w) ≤ ∑ j ∈ range w, f (n - w + j) := by
        calc
          _ = ∑ _ ∈ range w, f (n - w) := by simp
          _ ≤ _ := sum_le_sum fun j _ ↦ hf (by omega)
      have hHi : (∑ j ∈ range w, f (n - w + j)) ≤ w * f n := by
        calc
          _ ≤ ∑ _ ∈ range w, f n :=
            sum_le_sum fun j hj ↦ hf (by have := mem_range.mp hj; omega)
          _ = w * f n := by simp
      have he : n - w + w = n := Nat.sub_add_cancel hle
      have ha := sample_add f (n - w) w hw
      have hb := prefix_add f (n - w) w
      rw [he] at ha hb
      omega

lemma multiplicity_le (p : BP n) {w : ℕ} (hw : 0 < w) :
    p.val.parts.count w ≤ n / w := by
  have hr : Multiset.replicate (p.val.parts.count w) w ≤ p.val.parts :=
    Multiset.le_count_iff_replicate_le.mp le_rfl
  have hs := congrArg Multiset.sum (tsub_add_cancel_of_le hr)
  simp only [Multiset.sum_add, Multiset.sum_replicate, nsmul_eq_mul, p.val.parts_sum] at hs
  apply (Nat.le_div_iff_mul_le hw).mpr
  exact (Nat.le_add_left (p.val.parts.count w * w) _).trans_eq hs

lemma count_sum (n w : ℕ) (hw : binary w) :
    ∑ p : BP n, p.val.parts.count w = ∑ j ∈ range (n / w), b (n - w * (j + 1)) := by
  have hterm (p : BP n) : (∑ j ∈ range (n / w), if j < p.val.parts.count w then 1 else 0)
      = p.val.parts.count w := by
    rw [← sum_filter]
    have h : (range (n / w)).filter (fun j ↦ j < p.val.parts.count w) =
        range (p.val.parts.count w) := by
      ext j
      simp only [mem_filter, mem_range]
      have := multiplicity_le p (binary_pos hw)
      omega
    rw [h]
    simp
  have heq :
      (∑ p : BP n, ∑ j ∈ range (n / w), if j < p.val.parts.count w then 1 else 0) =
        ∑ p : BP n, p.val.parts.count w :=
    sum_congr rfl fun p _ ↦ hterm p
  rw [← heq, sum_comm]
  apply sum_congr rfl
  intro j hj
  have hnj : w * (j + 1) ≤ n := by
    have hle : j + 1 ≤ n / w := mem_range.mp hj
    simpa [mul_comm] using (Nat.le_div_iff_mul_le (binary_pos hw)).mp hle
  rw [← sum_filter, ← card_eq_sum_ones]
  have he := Fintype.card_congr (removeCopies hw hnj)
  rwa [Fintype.card_subtype] at he

lemma partition_weight (n : ℕ) (p : BP n) :
    ∑ i ∈ range (Nat.log 2 n + 1), (2 ^ i) * p.val.parts.count (2 ^ i) = n := by
  let s := range (Nat.log 2 n + 1)
  have hpow : Function.Injective (fun i : ℕ ↦ (2 : ℕ) ^ i) :=
    (pow_right_strictMono₀ (by decide : (1 : ℕ) < 2)).injective
  have hs : p.val.parts.toFinset ⊆ s.image (fun i ↦ 2 ^ i) := by
    intro w hw
    rw [Multiset.mem_toFinset] at hw
    obtain ⟨i, rfl⟩ := p.property w hw
    have hn := Nat.Partition.le_of_mem_parts hw
    have hnpos : n ≠ 0 := (Nat.two_pow_pos i).trans_le hn |>.ne'
    exact mem_image.mpr ⟨i, mem_range.mpr (Nat.lt_succ_of_le
      ((Nat.le_log_iff_pow_le (by decide) hnpos).mpr hn)), rfl⟩
  calc
    _ = ∑ w ∈ s.image (fun i ↦ 2 ^ i), p.val.parts.count w * w := by
      rw [sum_image hpow.injOn]
      apply sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = ∑ w ∈ p.val.parts.toFinset, p.val.parts.count w * w := by
      symm
      apply sum_subset hs
      intro w _ hw
      rw [Multiset.mem_toFinset] at hw
      simp [Multiset.count_eq_zero_of_notMem hw]
    _ = n := by simpa [smul_eq_mul, p.val.parts_sum] using (Finset.sum_multiset_count p.val.parts).symm

lemma weight_b (n : ℕ) :
    n * b n = ∑ i ∈ range (Nat.log 2 n + 1), sample b n (2 ^ i) := by
  calc
    n * b n = ∑ p : BP n, n := by simp [b, mul_comm]
    _ = ∑ p : BP n, ∑ i ∈ range (Nat.log 2 n + 1), 2 ^ i * p.val.parts.count (2 ^ i) := by
      simp_rw [partition_weight]
    _ = ∑ i ∈ range (Nat.log 2 n + 1), ∑ p : BP n, 2 ^ i * p.val.parts.count (2 ^ i) :=
      sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      rw [← mul_sum, count_sum n _ ⟨i, rfl⟩]
      rfl

lemma sample_b_even (n w : ℕ) :
    sample b (2 * n) (2 * w) = 2 * sample a n w := by
  unfold sample
  rw [Nat.mul_div_mul_left _ _ (by decide : 0 < 2), mul_assoc]
  congr 2
  apply sum_congr rfl
  intro j _
  rw [mul_assoc, ← Nat.mul_sub_left_distrib, ← a_eq]

lemma weight_a {n : ℕ} (hn : 0 < n) :
    n * a n = partialSum a n + ∑ i ∈ range (Nat.log 2 n + 1), sample a n (2 ^ i) := by
  have h := weight_b (2 * n)
  rw [show Nat.log 2 (2 * n) = Nat.log 2 n + 1 by
    rw [mul_comm, Nat.log_mul_base (by decide) hn.ne']] at h
  rw [sum_range_succ', pow_zero, sample_one, prefix_b_even] at h
  simp_rw [pow_succ', sample_b_even, ← mul_sum, ← a_eq] at h
  rw [mul_assoc] at h
  omega

lemma a_mono : Monotone a := by
  intro i j hij
  simp only [a_eq]
  exact b_mono (Nat.mul_le_mul_left _ hij)

lemma a_pos (n : ℕ) : 0 < a n := by
  rw [a_eq]
  exact b_pos _

lemma dyadic_upper {n : ℕ} (hn : 0 < n) :
    n * a n ≤ (Nat.log 2 n + 2) * partialSum a n := by
  rw [weight_a hn]
  have hs : (∑ i ∈ range (Nat.log 2 n + 1), sample a n (2 ^ i)) ≤
      (Nat.log 2 n + 1) * partialSum a n := by
    calc
      _ ≤ ∑ _ ∈ range (Nat.log 2 n + 1), partialSum a n :=
        sum_le_sum fun i _ ↦ (sample_bounds a_mono _ (Nat.two_pow_pos i) n).1
      _ = _ := by simp
  rw [show Nat.log 2 n + 2 = (Nat.log 2 n + 1) + 1 by rfl, add_mul, one_mul]
  omega

lemma geom_two (d : ℕ) : (∑ i ∈ range d, (2 : ℕ) ^ i) + 1 = 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, pow_succ]
    omega

lemma dyadic_trunc {n t : ℕ} (hn : 0 < n) (ht : t ≤ Nat.log 2 n) :
    2 ^ t * (Nat.log 2 n - t + 2) * partialSum a n ≤ (2 ^ t + 2) * (n * a n) := by
  let d := Nat.log 2 n - t + 1
  have hs : d * partialSum a n ≤
      (∑ i ∈ range d, sample a n (2 ^ i)) + (∑ i ∈ range d, (2 : ℕ) ^ i) * a n := by
    calc
      _ = ∑ _ ∈ range d, partialSum a n := by simp
      _ ≤ ∑ i ∈ range d, (sample a n (2 ^ i) + 2 ^ i * a n) :=
        sum_le_sum fun i _ ↦ (sample_bounds a_mono _ (Nat.two_pow_pos i) n).2
      _ = _ := by rw [sum_add_distrib, sum_mul]
  have hsub : (∑ i ∈ range d, sample a n (2 ^ i)) ≤
      ∑ i ∈ range (Nat.log 2 n + 1), sample a n (2 ^ i) :=
    sum_le_sum_of_subset (range_subset_range.mpr (by dsimp [d]; omega))
  have hpow : 2 ^ t * (∑ i ∈ range d, (2 : ℕ) ^ i) ≤ 2 * n := by
    calc
      _ ≤ 2 ^ t * 2 ^ d := Nat.mul_le_mul_left _ (by have := geom_two d; omega)
      _ = 2 ^ (Nat.log 2 n + 1) := by rw [← pow_add]; congr 1; dsimp [d]; omega
      _ ≤ 2 * n := by rw [pow_succ']; exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 hn.ne')
  have hsmall : (d + 1) * partialSum a n ≤
      n * a n + (∑ i ∈ range d, (2 : ℕ) ^ i) * a n := by
    rw [add_mul, one_mul, weight_a hn]
    omega
  calc
    _ = 2 ^ t * ((d + 1) * partialSum a n) := by rw [mul_assoc]
    _ ≤ 2 ^ t * (n * a n + (∑ i ∈ range d, (2 : ℕ) ^ i) * a n) :=
      Nat.mul_le_mul_left _ hsmall
    _ = 2 ^ t * (n * a n) + (2 ^ t * ∑ i ∈ range d, (2 : ℕ) ^ i) * a n := by ring
    _ ≤ 2 ^ t * (n * a n) + (2 * n) * a n :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hpow) _
    _ = _ := by ring

lemma tendsto_index : Tendsto (fun n : ℕ ↦ (Nat.log 2 n : ℝ)) atTop atTop := by
  apply tendsto_natCast_atTop_atTop.comp
  apply tendsto_atTop_atTop.mpr
  intro k
  refine ⟨2 ^ k, fun n hn ↦ ?_⟩
  have hn0 : n ≠ 0 := ((Nat.two_pow_pos k).trans_le hn).ne'
  exact (Nat.le_log_iff_pow_le (by decide) hn0).mpr hn

noncomputable def normalized (n : ℕ) : ℝ :=
  (Nat.log 2 n + 2 : ℕ) * (partialSum a n : ℝ) / (n * (a n : ℝ))

lemma normalized_limit : Tendsto normalized atTop (𝓝 1) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hW : 0 < (n : ℝ) * a n := by
      exact_mod_cast Nat.mul_pos (show 0 < n by omega) (a_pos n)
    have hlow : (n : ℝ) * a n ≤ (Nat.log 2 n + 2 : ℕ) * (partialSum a n : ℝ) := by
      exact_mod_cast dyadic_upper (show 0 < n by omega)
    exact hc.trans_le ((le_div_iff₀ hW).mpr (by simpa using hlow))
  · intro c hc
    obtain ⟨t, ht⟩ := exists_nat_gt (2 / (c - 1))
    let P : ℝ := ↑((2 : ℕ) ^ t)
    let K : ℝ := 1 + 2 / P
    have hP : 0 < P := by
      dsimp [P]
      exact_mod_cast Nat.two_pow_pos t
    have htP : (t : ℝ) ≤ P := by
      dsimp [P]
      exact_mod_cast (Nat.lt_two_pow_self (n := t)).le
    have hK : K < c := by
      have ht' : 2 / (c - 1) < P := ht.trans_le htP
      have hp' := (div_lt_iff₀ (sub_pos.mpr hc)).mp ht'
      have hpp := (div_lt_iff₀ hP).mpr (show (2 : ℝ) < (c - 1) * P by
        simpa [mul_comm] using hp')
      dsimp [K]
      linarith
    filter_upwards [tendsto_index.eventually_gt_atTop (c * t / (c - K)),
      eventually_ge_atTop ((2 : ℕ) ^ t)] with n hn hn2
    have hn0 : 0 < n := (Nat.two_pow_pos t).trans_le hn2
    have hL : t ≤ Nat.log 2 n := (Nat.le_log_iff_pow_le (by decide) hn0.ne').mpr hn2
    let J : ℝ := ↑(Nat.log 2 n + 2 : ℕ)
    let D : ℝ := ↑(Nat.log 2 n - t + 2 : ℕ)
    let S : ℝ := partialSum a n
    let W : ℝ := (n : ℝ) * a n
    have hW : 0 < W := by
      dsimp [W]
      exact_mod_cast Nat.mul_pos hn0 (a_pos n)
    have hJ : 0 ≤ J := Nat.cast_nonneg _
    have hD : 0 < D := by
      dsimp [D]
      exact_mod_cast (by omega : 0 < Nat.log 2 n - t + 2)
    have hJD : J = D + t := by
      dsimp [J, D]
      exact_mod_cast (by omega : Nat.log 2 n + 2 = (Nat.log 2 n - t + 2) + t)
    have htr : P * D * S ≤ (P + 2) * W := by
      dsimp [P, D, S, W]
      exact_mod_cast dyadic_trunc hn0 hL
    have hPK : P * K = P + 2 := by
      dsimp [K]
      field_simp
    have hDS : D * S ≤ K * W := by
      apply (mul_le_mul_iff_of_pos_left hP).mp
      simpa only [← mul_assoc, hPK] using htr
    have hcut := (div_lt_iff₀ (sub_pos.mpr hK)).mp hn
    have hLogPos : (0 : ℝ) < 2 * (c - K) := by positivity
    have hcmp : J * K < D * c := by
      have hJ' : J = (Nat.log 2 n : ℝ) + 2 := by simp [J]
      have hshift : D = (Nat.log 2 n : ℝ) + 2 - t := by linarith only [hJD, hJ']
      rw [hJ', hshift]
      nlinarith only [hcut, hLogPos]
    change J * S / W < c
    apply (div_lt_iff₀ hW).mpr
    apply (mul_lt_mul_iff_of_pos_left hD).mp
    calc
      D * (J * S) = J * (D * S) := by ring
      _ ≤ J * (K * W) := mul_le_mul_of_nonneg_left hDS hJ
      _ = (J * K) * W := by ring
      _ < (D * c) * W := mul_lt_mul_of_pos_right hcmp hW
      _ = D * (c * W) := by ring

lemma log_bounds {n : ℕ} (hn : 0 < n) :
    (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n ∧
      Real.log n < (Nat.log 2 n + 1 : ℕ) * Real.log 2 := by
  have hlo : (2 : ℝ) ^ Nat.log 2 n ≤ n := by
    exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  have hhi : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by
    exact_mod_cast Nat.lt_pow_of_log_lt (by decide : 1 < (2 : ℕ)) (Nat.lt_succ_self (Nat.log 2 n))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hlo
  · rw [← Real.log_pow]
    exact Real.log_lt_log hnR hhi

lemma log_ratio_limit :
    Tendsto (fun n : ℕ ↦ Real.log n / (Nat.log 2 n + 2 : ℕ)) atTop (𝓝 (Real.log 2)) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    filter_upwards [tendsto_index.eventually_gt_atTop (2 * c / (Real.log 2 - c)),
      eventually_ge_atTop (1 : ℕ)] with n hL hn
    have hj : (0 : ℝ) < (Nat.log 2 n + 2 : ℕ) := by positivity
    have hl := (div_lt_iff₀ (sub_pos.mpr hc)).mp hL
    have hlo := (log_bounds (show 0 < n by omega)).1
    apply (lt_div_iff₀ hj).mpr
    push_cast
    nlinarith only [hl, hlo]
  · intro c hc
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hj : (0 : ℝ) < (Nat.log 2 n + 2 : ℕ) := by positivity
    have hhi := (log_bounds (show 0 < n by omega)).2
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    apply (div_lt_iff₀ hj).mpr
    calc
      _ < (Nat.log 2 n + 1 : ℕ) * Real.log 2 := hhi
      _ ≤ (Nat.log 2 n + 2 : ℕ) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ (Nat.log 2 n + 1)) hlog.le
      _ < c * (Nat.log 2 n + 2 : ℕ) := by
        simpa only [mul_comm] using mul_lt_mul_of_pos_right hc hj

end OMA.BinaryRatio

open Filter OMA.BinaryRatio OMA.S_oeis_a000123

theorem OMA.solution : type_of% @OMA.S_oeis_a000123.main := by
  have ht := (tendsto_const_nhds (x := (2 : ℝ))).mul (log_ratio_limit.mul normalized_limit)
  have hzero : Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  convert ht.add hzero using 1
  · ext n
    rw [a_double]
    by_cases hn : n = 0
    · simp [hn, normalized]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have haR : (a n : ℝ) ≠ 0 := by exact_mod_cast (a_pos n).ne'
      have hj : (0 : ℝ) < (Nat.log 2 n + 2 : ℕ) := by positivity
      simp only [normalized, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      push_cast at hj
      field_simp
  · ring_nf
