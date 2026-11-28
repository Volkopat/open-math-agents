import OMAReductions.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1
import Mathlib

/-!
# Factor approximation and the arithmetic-progression counting bound

This reduction follows Leng, Sah and Sawhney, *Improved Bounds for
Szemerédi's Theorem*, arXiv:2402.17995v2, Lemma 3.7.
https://arxiv.org/html/2402.17995v2#S3.SS2

H1 is the structured approximation from Lemma 3.8, refined to long
arithmetic progression pieces using Lemma 2.1 and boundary regularity.
H2 is the generalized von Neumann bound in Lemma 3.3. The proof below
handles the finite clipping, discrepancy and density transfer.
-/

/-
The finite arithmetic-progression average and its elementary Lipschitz bound.
This is the real-valued specialization of the first bound in Leng–Sah–Sawhney,
arXiv:2402.17995v2, Lemma 3.3.
-/

namespace OMA.Erdos3ProgressionAverage

open Finset

private theorem abs_prod_sub_prod_le {M : ℝ} (hM : 0 ≤ M)
    (f g : ℕ → ℝ) (hf : ∀ i, 0 ≤ f i ∧ f i ≤ M) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ M)
    (k : ℕ) :
    |(∏ i ∈ range (k + 1), f i) - ∏ i ∈ range (k + 1), g i| ≤
      M^k * ∑ i ∈ range (k + 1), |f i - g i| := by
  induction k with
  | zero => simp
  | succ k ih =>
    let F := ∏ i ∈ range (k + 1), f i
    let G := ∏ i ∈ range (k + 1), g i
    let U := ∑ i ∈ range (k + 1), |f i - g i|
    have hG0 : 0 ≤ G := prod_nonneg (fun i _ => (hg i).1)
    have hG : G ≤ M^(k + 1) := by
      calc
        G ≤ ∏ _i ∈ range (k + 1), M :=
          prod_le_prod (fun i _ => (hg i).1) (fun i _ => (hg i).2)
        _ = _ := by simp
    have hU : 0 ≤ U := sum_nonneg (fun _ _ => abs_nonneg _)
    have hid : F * f (k + 1) - G * g (k + 1) =
        (F - G) * f (k + 1) + G * (f (k + 1) - g (k + 1)) := by ring
    rw [prod_range_succ f (k + 1), prod_range_succ g (k + 1), sum_range_succ]
    change |F * f (k + 1) - G * g (k + 1)| ≤
      M^(k + 1) * (U + |f (k + 1) - g (k + 1)|)
    rw [hid]
    calc
      _ ≤ |(F - G) * f (k + 1)| + |G * (f (k + 1) - g (k + 1))| := abs_add_le ..
      _ = |F - G| * f (k + 1) + G * |f (k + 1) - g (k + 1)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hf _).1, abs_of_nonneg hG0]
      _ ≤ (M^k * U) * M + M^(k + 1) * |f (k + 1) - g (k + 1)| := by
        exact add_le_add (mul_le_mul ih (hf _).2 (hf _).1 (mul_nonneg (pow_nonneg hM _) hU))
          (mul_le_mul_of_nonneg_right hG (abs_nonneg _))
      _ = _ := by rw [pow_succ]; ring

private theorem sum_shift_le (N shift : ℕ) (u : ℕ → ℝ)
    (hu : ∀ a, 0 ≤ u a) (hs : ∀ a ∉ Icc 1 N, u a = 0) :
    (∑ a ∈ range (N + 1), u (a + shift)) ≤ ∑ a ∈ Icc 1 N, u a := by
  let T := (range (N + 1)).image (fun a => a + shift)
  have heq : (∑ a ∈ T, u a) = ∑ a ∈ range (N + 1), u (a + shift) :=
    sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)
  rw [← heq]
  calc
    _ = ∑ a ∈ T ∩ Icc 1 N, u a := by
      symm
      apply sum_subset inter_subset_left
      intro a ha hna
      exact hs a (fun h => hna (mem_inter.mpr ⟨ha, h⟩))
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right (fun a _ _ => hu a)

/-- Changing a bounded input function changes its progression average by at most
the normalized total pointwise change multiplied by the product bound. -/
theorem abs_average_sub_le (N k : ℕ) {M : ℝ} (hM : 0 ≤ M) (f g : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ M) (hg : ∀ n, 0 ≤ g n ∧ g n ≤ M)
    (hs : ∀ n ∉ Icc 1 N, f n = g n) :
  let average (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
    (∑ d ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ∏ i ∈ range k, f (a + i * d)) / ((N : ℝ) + 1)^2;
    |average N (k + 1) f - average N (k + 1) g| ≤
      ((k + 1 : ℕ) : ℝ) * M^k * (∑ n ∈ Icc 1 N, |f n - g n|) / ((N : ℝ) + 1) := by
  intro average
  let R := range (N + 1)
  let S := range (k + 1)
  let u (n : ℕ) := |f n - g n|
  have hden : 0 < ((N : ℝ) + 1)^2 := by positivity
  have hu : ∀ n, 0 ≤ u n := fun _ => abs_nonneg _
  have hus : ∀ n ∉ Icc 1 N, u n = 0 := fun n hn => by simp [u, hs n hn]
  have hpoint (a d : ℕ) :
      |(∏ i ∈ S, f (a + i * d)) - ∏ i ∈ S, g (a + i * d)| ≤
        M^k * ∑ i ∈ S, u (a + i * d) :=
    abs_prod_sub_prod_le hM _ _ (fun _ => hf _) (fun _ => hg _) k
  dsimp only [average]
  rw [← sub_div, abs_div, abs_of_pos hden]
  change |(∑ d ∈ R, ∑ a ∈ R, ∏ i ∈ S, f (a + i * d)) -
      (∑ d ∈ R, ∑ a ∈ R, ∏ i ∈ S, g (a + i * d))| / _ ≤ _
  simp only [← sum_sub_distrib]
  calc
    _ ≤ (∑ d ∈ R, ∑ a ∈ R,
        |(∏ i ∈ S, f (a + i * d)) - ∏ i ∈ S, g (a + i * d)|) / ((N : ℝ) + 1)^2 := by
      apply div_le_div_of_nonneg_right _ hden.le
      refine (abs_sum_le_sum_abs _ _).trans ?_
      exact sum_le_sum fun d _ => abs_sum_le_sum_abs _ _
    _ ≤ (∑ d ∈ R, ∑ a ∈ R, M^k * ∑ i ∈ S, u (a + i * d)) / ((N : ℝ) + 1)^2 :=
      div_le_div_of_nonneg_right
        (sum_le_sum <| fun d _ => sum_le_sum fun a _ => hpoint a d) hden.le
    _ = (M^k * ∑ d ∈ R, ∑ i ∈ S, ∑ a ∈ R, u (a + i * d)) / ((N : ℝ) + 1)^2 := by
      congr 1
      rw [mul_sum]
      refine sum_congr rfl (fun d _ => ?_)
      rw [← mul_sum]
      congr 1
      exact sum_comm
    _ ≤ (M^k * ∑ _d ∈ R, ∑ _i ∈ S, ∑ n ∈ Icc 1 N, u n) / ((N : ℝ) + 1)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (sum_le_sum <| fun d _ => sum_le_sum fun i _ => sum_shift_le N (i * d) u hu hus)
        (pow_nonneg hM _)) hden.le
    _ = _ := by
      simp only [R, S, u, sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      field_simp

/-- Counting ordered progression parameters is the progression average of the indicator. -/
theorem average_indicator (N k : ℕ) (A : Finset ℕ) :
  let average (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
    (∑ d ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ∏ i ∈ range k, f (a + i * d)) / ((N : ℝ) + 1)^2;
    average N k (fun n => if n ∈ A then 1 else 0) =
      (((range (N + 1) ×ˢ range (N + 1)).filter
        (fun p => ∀ i < k, p.1 + i * p.2 ∈ A)).card : ℝ) / ((N : ℝ) + 1)^2 := by
  intro average
  classical
  dsimp only [average]
  congr 1
  rw [← sum_comm, card_filter, Nat.cast_sum, Finset.sum_product]
  refine sum_congr rfl fun a _ => sum_congr rfl fun d _ => ?_
  by_cases h : ∀ i < k, a + i * d ∈ A
  · simp only [if_pos h, Nat.cast_one]
    exact prod_eq_one (fun i hi => if_pos (h i (mem_range.mp hi)))
  · push Not at h
    obtain ⟨i, hik, hi⟩ := h
    have hz := Finset.prod_eq_zero (mem_range.mpr hik)
      (f := fun j : ℕ => if a + j * d ∈ A then (1 : ℝ) else 0) (if_neg hi)
    rw [hz, if_neg (fun hh => hi (hh i hik)), Nat.cast_zero]

end OMA.Erdos3ProgressionAverage

/-
The quantitative heavy-factor estimate in the first step of Leng–Sah–Sawhney's
proof of Lemma 3.7. The progression count detects a positive mass of points
whose factor density exceeds the mean by a fixed multiplicative gain.
-/

namespace OMA.Erdos3HighDensityFactor

open Finset OMA.Erdos3ProgressionAverage

theorem count_gap_le_high_mass (N k : ℕ) (δ γ : ℝ) (g : ℕ → ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (hγ : 0 ≤ γ) (hγpow : (1 + γ)^k ≤ 2)
    (hg : ∀ n, 0 ≤ g n ∧ g n ≤ 1) (hs : ∀ n ∉ Icc 1 N, g n = 0)
    (hmean : ∑ n ∈ Icc 1 N, g n = δ * N) :
  let average (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
    (∑ d ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ∏ i ∈ range k, f (a + i * d)) / ((N : ℝ) + 1)^2;
    let S := Icc 1 N
    let heavy := S.filter (fun n => (1 + γ) * δ < g n)
    |average N (k + 1) g - average N (k + 1) (fun n => if n ∈ S then δ else 0)| ≤
      7 * ((k + 1 : ℕ) : ℝ) * heavy.card / ((N : ℝ) + 1) +
        4 * ((k + 1 : ℕ) : ℝ) * γ * δ^(k + 1) := by
  classical
  intro average S heavy
  let M := (1 + γ) * δ
  let K : ℝ := ((k + 1 : ℕ) : ℝ)
  let B : ℝ := heavy.card
  let D : ℝ := (N : ℝ) + 1
  let v (n : ℕ) := if n ∈ S then δ else 0
  let clip (n : ℕ) := if n ∈ heavy then 0 else g n
  have hM : 0 ≤ M := mul_nonneg (by linarith) hδ
  have hvbound : δ ≤ M := by dsimp [M]; nlinarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hheavy : heavy ⊆ S := filter_subset _ _
  have hcardS : S.card = N := by simp [S]
  have hindicator : (∑ n ∈ S, if n ∈ heavy then (1 : ℝ) else 0) = B := by
    rw [← sum_filter]
    have he : S.filter (fun n => n ∈ heavy) = heavy :=
      ext fun _ => (mem_filter).trans (and_iff_right_of_imp fun h => hheavy h)
    simp [he, B]
  have hclipOut : ∀ n ∉ S, clip n = 0 := fun n hn =>
    if_neg (fun h => hn (hheavy h)) |>.trans (hs n hn)
  have hclip0 (n : ℕ) : 0 ≤ clip n := by
    dsimp [clip]
    split_ifs
    · exact le_rfl
    · exact (hg n).1
  have hclip1 (n : ℕ) : clip n ≤ 1 := by
    dsimp [clip]
    split_ifs
    · exact zero_le_one
    · exact (hg n).2
  have hclipM (n : ℕ) : clip n ≤ M := by
    by_cases hn : n ∈ S
    · dsimp only [clip]
      split_ifs with hh
      · exact hM
      · exact le_of_not_gt (fun hc => hh (mem_filter.mpr ⟨hn, hc⟩))
    · simpa only [hclipOut n hn] using hM
  have hvM (n : ℕ) : 0 ≤ v n ∧ v n ≤ M := by
    dsimp only [v]
    split_ifs
    · exact ⟨hδ, hvbound⟩
    · exact ⟨le_rfl, hM⟩
  have hU : ∑ n ∈ S, |g n - clip n| ≤ B := calc
    _ ≤ ∑ n ∈ S, if n ∈ heavy then (1 : ℝ) else 0 := by
      refine sum_le_sum (fun n _ => ?_)
      by_cases hn : n ∈ heavy
      · simpa [clip, hn, abs_of_nonneg (hg n).1] using (hg n).2
      · simp [clip, hn]
    _ = _ := hindicator
  have hpospart (n : ℕ) (hn : n ∈ S) :
      max (g n - δ) 0 ≤ γ * δ + (if n ∈ heavy then 1 else 0) := by
    apply max_le
    · by_cases h : n ∈ heavy
      · simp only [if_pos h]
        nlinarith [(hg n).2, mul_nonneg hγ hδ]
      · have hMle : g n ≤ M := le_of_not_gt (fun hc => h (mem_filter.mpr ⟨hn, hc⟩))
        simp only [if_neg h, add_zero]
        dsimp [M] at hMle
        nlinarith
    · exact add_nonneg (mul_nonneg hγ hδ) (by split_ifs <;> norm_num)
  have hzero : ∑ n ∈ S, (g n - δ) = 0 := by
    have hmeanS : ∑ n ∈ S, g n = δ * N := hmean
    rw [sum_sub_distrib, hmeanS, sum_const, nsmul_eq_mul, hcardS]
    ring
  have hpoint (n : ℕ) (hn : n ∈ S) :
      |g n - v n| = 2 * max (g n - δ) 0 - (g n - δ) := by
    rw [show v n = δ by simp [v, hn]]
    by_cases h : 0 ≤ g n - δ
    · rw [abs_of_nonneg h, max_eq_left h]
      ring
    · rw [abs_of_neg (lt_of_not_ge h), max_eq_right (le_of_not_ge h)]
      ring
  have hV : ∑ n ∈ S, |g n - v n| ≤ 2 * (γ * δ * N + B) := by
    calc
      _ = 2 * ∑ n ∈ S, max (g n - δ) 0 := by
        rw [sum_congr rfl hpoint, sum_sub_distrib, ← mul_sum, hzero, sub_zero]
      _ ≤ 2 * ∑ n ∈ S, (γ * δ + if n ∈ heavy then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hpospart) (by norm_num)
      _ = _ := by rw [sum_add_distrib, sum_const, nsmul_eq_mul, hcardS, hindicator, mul_comm (N : ℝ)]
  have hW : ∑ n ∈ S, |clip n - v n| ≤ 3 * B + 2 * γ * δ * N := by
    calc
      _ ≤ ∑ n ∈ S, (|g n - clip n| + |g n - v n|) := by
        refine sum_le_sum (fun n _ => ?_)
        rw [abs_sub_comm (g n) (clip n)]
        exact abs_sub_le (clip n) (g n) (v n)
      _ ≤ B + 2 * (γ * δ * N + B) := by
        rw [sum_add_distrib]
        exact add_le_add hU hV
      _ = _ := by ring
  have hbound₁ : |average N (k + 1) g - average N (k + 1) clip| ≤ K * B / D := by
    have hl := abs_average_sub_le N k zero_le_one g clip hg
      (fun n => ⟨hclip0 n, hclip1 n⟩) (fun n hn => (hs n hn).trans (hclipOut n hn).symm)
    rw [one_pow, mul_one] at hl
    exact hl.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hU hK) hD.le)
  have hP : M^k ≤ 2 * δ^k := by
    dsimp only [M]
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hγpow (pow_nonneg hδ _)
  have hbound₂ : |average N (k + 1) clip - average N (k + 1) v| ≤
      K * (2 * δ^k) * (3 * B + 2 * γ * δ * N) / D := by
    refine (abs_average_sub_le N k hM clip v (fun n => ⟨hclip0 n, hclipM n⟩) hvM
      (fun n hn => (hclipOut n hn).trans (if_neg hn).symm)).trans ?_
    apply div_le_div_of_nonneg_right _ hD.le
    exact mul_le_mul (mul_le_mul_of_nonneg_left hP hK) hW
      (sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  have hpow : δ^k ≤ 1 := pow_le_one₀ hδ hδ'
  have hnum : (N : ℝ) / D ≤ 1 := (div_le_one hD).2 (by dsimp [D]; linarith)
  change |average N (k + 1) g - average N (k + 1) v| ≤ 7 * K * B / D + 4 * K * γ * δ^(k + 1)
  calc
    _ ≤ K * B / D + K * (2 * δ^k) * (3 * B + 2 * γ * δ * N) / D :=
      (abs_sub_le _ _ _).trans (add_le_add hbound₁ hbound₂)
    _ = K * B / D + (6 * K * B / D) * δ^k + (4 * K * γ * δ^(k + 1)) * ((N : ℝ) / D) := by
      rw [pow_succ]
      ring
    _ ≤ K * B / D + (6 * K * B / D) * 1 + (4 * K * γ * δ^(k + 1)) * 1 :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hpow (show 0 ≤ 6 * K * B / D by positivity)))
        (mul_le_mul_of_nonneg_left hnum (show 0 ≤ 4 * K * γ * δ^(k + 1) by positivity))
    _ = _ := by ring

end OMA.Erdos3HighDensityFactor

/-
Transfer a density increment from a heavy factor set to a single progression
piece. This is the finite averaging step in Leng–Sah–Sawhney, Lemma 3.7.
-/

namespace OMA.Erdos3GoodProgressionAverage

open Finset

theorem exists_dense_piece {ι : Type} [DecidableEq ι] (S H : Finset ℕ)
    (P : Finset ι) (piece : ι → Finset ℕ) (f : ℕ → ℝ) (δ γ : ℝ)
    (hδ : 0 < δ) (hγ : 0 ≤ γ) (hH : H.Nonempty) (hHS : H ⊆ S)
    (hpair : (P : Set ι).PairwiseDisjoint piece)
    (hconst : ∀ p ∈ P, ∀ x ∈ piece p, ∀ y ∈ piece p, x ∈ H ↔ y ∈ H)
    (hbound : ∀ n ∈ H, f n ≤ 1)
    (hmass : (1 + γ) * δ * H.card ≤ ∑ n ∈ H, f n)
    (hbad : ((S \ P.biUnion piece).card : ℝ) ≤ γ * δ * H.card / 2) :
    ∃ p ∈ P, (piece p).Nonempty ∧ piece p ⊆ H ∧
      (1 + γ / 2) * δ * (piece p).card ≤ ∑ n ∈ piece p, f n := by
  classical
  let Q := P.filter (fun p => (piece p).Nonempty ∧ piece p ⊆ H)
  let U := Q.biUnion piece
  let μ := (1 + γ / 2) * δ
  have hμ : 0 < μ := mul_pos (by linarith) hδ
  have hUH : U ⊆ H := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := mem_biUnion.mp hx
    exact (mem_filter.mp hp).2.2 hx
  have hRem : H \ U ⊆ S \ P.biUnion piece := by
    intro n hn
    obtain ⟨hnH, hnU⟩ := mem_sdiff.mp hn
    refine mem_sdiff.mpr ⟨hHS hnH, ?_⟩
    intro hnP
    obtain ⟨p, hp, hnp⟩ := mem_biUnion.mp hnP
    have hpH : piece p ⊆ H := fun m hm => (hconst p hp n hnp m hm).mp hnH
    exact hnU (mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨hp, ⟨n, hnp⟩, hpH⟩, hnp⟩)
  have hRemMass : ∑ n ∈ H \ U, f n ≤ γ * δ * H.card / 2 := by
    calc
      _ ≤ ∑ _n ∈ H \ U, (1 : ℝ) := sum_le_sum fun n hn => hbound n (mem_sdiff.mp hn).1
      _ = ((H \ U).card : ℝ) := by simp
      _ ≤ ((S \ P.biUnion piece).card : ℝ) := by exact_mod_cast card_le_card hRem
      _ ≤ _ := hbad
  have hsum : (∑ n ∈ H \ U, f n) + (∑ n ∈ U, f n) = ∑ n ∈ H, f n :=
    sum_sdiff hUH
  have hsumU : μ * H.card ≤ ∑ n ∈ U, f n := by
    dsimp only [μ]
    linarith only [hmass, hRemMass, hsum]
  have hHcard : (0 : ℝ) < H.card := by exact_mod_cast card_pos.mpr hH
  have hUne : U.Nonempty := by
    by_contra hNo
    have he := not_nonempty_iff_eq_empty.mp hNo
    rw [he, sum_empty] at hsumU
    exact (mul_pos hμ hHcard).not_ge hsumU
  have hQne : Q.Nonempty := by
    obtain ⟨n, hn⟩ := hUne
    obtain ⟨p, hp, -⟩ := mem_biUnion.mp hn
    exact ⟨p, hp⟩
  have hpairQ : (Q : Set ι).PairwiseDisjoint piece := by
    intro p hp q hq hpq
    exact hpair (mem_filter.mp hp).1 (mem_filter.mp hq).1 hpq
  have hmassU : μ * U.card ≤ ∑ n ∈ U, f n :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card hUH) hμ.le).trans hsumU
  by_contra! hNo
  have hlt : (∑ p ∈ Q, ∑ n ∈ piece p, f n) < ∑ p ∈ Q, μ * ((piece p).card : ℝ) := by
    apply sum_lt_sum_of_nonempty hQne
    intro p hp
    obtain ⟨hP, hne, hsub⟩ := mem_filter.mp hp
    exact hNo p hP hne hsub
  rw [← sum_biUnion hpairQ, ← mul_sum, ← Nat.cast_sum, ← card_biUnion hpairQ] at hlt
  exact hlt.not_ge hmassU

end OMA.Erdos3GoodProgressionAverage

/-
Finite inputs for the trichotomy of Leng, Sah and Sawhney, Lemma 3.7.
The structured witness uses their Lemmas 3.8 and 2.1.
The second input is the progression-count estimate in Lemma 3.3.
-/

namespace OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1

open Finset
open scoped Classical

/-- A count-approximating factor together with long progression pieces on which
the factor is constant. The fibres have the same indicator and factor masses. -/
def H1 : Prop := ∀ k : ℕ, 5 ≤ k → ∀ θ β : ℝ, 0 < θ → 0 < β →
  ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ,
    ∀ (N : ℕ) (A : Finset ℕ), 3 ≤ N → 0 < A.card → A ⊆ Icc 1 N →
      let S := Icc 1 N
      let δ := (A.card : ℝ) / N
      let loss := C * (1 + Real.log ((N : ℝ) / A.card)) ^ D
      let f (x : ℕ) : ℝ := if x ∈ A then 1 else 0
      let L := 2^k * N + 1
      let r := k-1
      let ap (p : ℕ × ℕ × ℕ) := (range p.2.2).image (fun i => p.1 + i*p.2.1)
      Real.exp (Real.exp loss) < (N : ℝ) →
      ∃ (g : ℕ → ℝ) (P : Finset (ℕ × ℕ × ℕ)),
        (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧ (∀ x ∉ S, g x = 0) ∧
        (∀ V : Set ℝ, ∑ x ∈ S.filter (fun x => g x ∈ V), f x =
          ∑ x ∈ S.filter (fun x => g x ∈ V), g x) ∧
        (P : Set (ℕ × ℕ × ℕ)).PairwiseDisjoint ap ∧ P.biUnion ap ⊆ S ∧
        ((S \ P.biUnion ap).card : ℝ) ≤ β * δ^(k+1) * N ∧
        (∀ p ∈ P, 0 < p.2.1 ∧ (N : ℝ)^Real.exp (-loss) ≤ (p.2.2 : ℝ) ∧
          ∀ x ∈ ap p, ∀ y ∈ ap p, g x = g y) ∧
        (∑ x : ZMod L, ∑ t : Fin r → ZMod L, ∏ ω : Fin r → Bool,
          (f - g) (x + ∑ i : Fin r, if ω i then t i else 0).val) / ((L : ℝ)^k)
          ≤ θ * δ^(k * 2^r)

/-- Generalized von Neumann for two bounded inputs with the same support. -/
def H2 : Prop := ∀ k : ℕ, 5 ≤ k → ∃ C : ℝ, 0 < C ∧
  ∀ (N : ℕ) (f g : ℕ → ℝ), 3 ≤ N →
    (∀ x, (0 ≤ f x ∧ f x ≤ 1) ∧ (0 ≤ g x ∧ g x ≤ 1)) →
    (∀ x ∉ Icc 1 N, f x = 0 ∧ g x = 0) →
    let L := 2^k * N + 1
    let r := k-1
    let count (h : ℕ → ℝ) := ∑ d ∈ range (N+1), ∑ a ∈ range (N+1),
      ∏ i ∈ range k, h (a+i*d)
    |count f / ((N : ℝ)+1)^2 - count g / ((N : ℝ)+1)^2|^(2^r) ≤
      C * ((∑ x : ZMod L, ∑ t : Fin r → ZMod L, ∏ ω : Fin r → Bool,
        (f-g) (x + ∑ i : Fin r, if ω i then t i else 0).val) / ((L : ℝ)^k))

/- The finite part of the Leng–Sah–Sawhney indicator trichotomy. -/



open Finset Real OMA.Erdos3ProgressionAverage OMA.Erdos3HighDensityFactor
  OMA.Erdos3GoodProgressionAverage
open scoped Classical

private theorem sum_indicator_card (S A : Finset ℕ) :
    (∑ n ∈ S, if n ∈ A then (1 : ℝ) else 0) =
      ((S.filter (fun n => n ∈ A)).card : ℝ) := by
  rw [← sum_filter]
  simp

private theorem average_smul (N k : ℕ) (δ : ℝ) (f : ℕ → ℝ) :
  let average (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
    (∑ d ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ∏ i ∈ range k, f (a + i * d)) / ((N : ℝ) + 1)^2;
    average N k (fun n => δ * f n) = δ^k * average N k f := by
  intro average
  simp only [average, prod_mul_distrib, prod_const, card_range, ← mul_sum, mul_div_assoc]

private theorem gain_power_bound (k : ℕ) :
    (1 + 1 / (4096 * (((k + 1 : ℕ) : ℝ))^2))^k ≤ (2 : ℝ) := by
  let κ : ℝ := ((k + 1 : ℕ) : ℝ)
  let γ : ℝ := 1 / (4096 * κ^2)
  have hκ : 1 ≤ κ := by dsimp [κ]; exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hκp : 0 < κ := by linarith
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hkκ : (k : ℝ) ≤ κ := by dsimp [κ]; exact_mod_cast Nat.le_succ k
  have hγk : (k : ℝ) * γ ≤ 1 / 2 := by
    have hγκ : κ * γ = 1 / (4096 * κ) := by dsimp [γ]; field_simp
    calc
      _ ≤ κ * γ := mul_le_mul_of_nonneg_right hkκ hγ.le
      _ = _ := hγκ
      _ ≤ _ := (div_le_iff₀ (by positivity)).2 (by nlinarith)
  have hsquare : (Real.exp (1 / 2 : ℝ))^2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hhalf : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    nlinarith [Real.exp_one_lt_three, Real.exp_pos (1 / 2 : ℝ)]
  change (1 + γ)^k ≤ _
  calc
    _ ≤ (Real.exp γ)^k := pow_le_pow_left₀ (by linarith)
      (by simpa only [add_comm] using Real.add_one_le_exp γ) k
    _ = Real.exp ((k : ℝ) * γ) := (Real.exp_nat_mul γ k).symm
    _ ≤ Real.exp (1 / 2 : ℝ) := Real.exp_le_exp.mpr hγk
    _ ≤ _ := hhalf

private theorem sum_affine_piece (a d M : ℕ) (hd : 0 < d) (A : Finset ℕ) :
    (∑ n ∈ (range M).image (fun i => a + i*d), if n ∈ A then (1 : ℝ) else 0) =
      (((Icc 1 M).filter (fun i => a + (i-1)*d ∈ A)).card : ℝ) := by
  have hinj : Function.Injective (fun i : ℕ => a + i*d) :=
    fun _ _ he => Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel he)
  rw [sum_image hinj.injOn]
  have hshift : (Icc 1 M).image (fun i => i-1) = range M := by
    ext i
    constructor
    · rintro hi
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      have hj' := mem_Icc.mp hj
      exact mem_range.mpr (by omega)
    · intro hi
      have hi' := mem_range.mp hi
      exact mem_image.mpr ⟨i+1, mem_Icc.mpr (by omega), by omega⟩
  have hshiftInj : Set.InjOn (fun i : ℕ => i-1) (Icc 1 M : Finset ℕ) := by
    intro x hx y hy h
    have hx' := mem_Icc.mp (show x ∈ Icc 1 M from hx)
    have hy' := mem_Icc.mp (show y ∈ Icc 1 M from hy)
    change x - 1 = y - 1 at h
    omega
  rw [← hshift, sum_image hshiftInj]
  rw [← sum_filter]
  simp

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 →
    OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1.H1 := by
  intro structured countApprox j hj
  let average (N k : ℕ) (f : ℕ → ℝ) : ℝ :=
    (∑ d ∈ range (N + 1), ∑ a ∈ range (N + 1),
      ∏ i ∈ range k, f (a + i * d)) / ((N : ℝ) + 1)^2
  cases j with
  | zero => omega
  | succ k =>
    let K : ℕ := k+1
    let κ : ℝ := (K : ℝ)
    have hκ : 0 < κ := by dsimp [κ, K]; positivity
    have hK : 5 ≤ K := hj
    let σ : ℝ := 1 / (256 * κ)
    let γ : ℝ := 1 / (4096 * κ^2)
    let α : ℝ := σ / (28 * κ)
    let β : ℝ := γ * α / 2
    let q : ℕ := 2^k
    have hσ : 0 < σ := by dsimp [σ]; positivity
    have hγ : 0 < γ := by dsimp [γ]; positivity
    have hα : 0 < α := by dsimp [α]; positivity
    have hβ : 0 < β := by dsimp [β]; positivity
    have hγPow : (1 + γ)^k ≤ 2 := gain_power_bound k
    have hcoef : 4 * κ * γ = σ / 4 := by dsimp [σ, γ]; field_simp; ring
    obtain ⟨c, hc, hcount⟩ := countApprox K hK
    let θ : ℝ := (σ/2)^q / c
    have hθ : 0 < θ := by dsimp [θ]; positivity
    obtain ⟨C, hC, D, hstructure⟩ := structured K hK θ β hθ hβ
    refine ⟨1 + γ / 2, C, by linarith, hC, D, ?_⟩
    intro N A hN hA hsub count δ loss total
    by_cases hsmall : (N : ℝ) ≤ Real.exp (Real.exp loss)
    · exact Or.inl hsmall
    right
    by_cases hclose : |(count A : ℝ) / total - δ^K * count (Icc 1 N) / total| ≤ δ^K / (256 * κ)
    · exact Or.inl hclose
    right
    let S := Icc 1 N
    let f (n : ℕ) : ℝ := if n ∈ A then 1 else 0
    let v (n : ℕ) : ℝ := if n ∈ S then δ else 0
    let ap (p : ℕ × ℕ × ℕ) := (range p.2.2).image (fun i => p.1 + i*p.2.1)
    let DN : ℝ := (N : ℝ) + 1
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA
    have hδ : 0 < δ := div_pos hApos hNr
    have hδone : δ ≤ 1 := by
      have hAN : A.card ≤ N := by simpa using card_le_card hsub
      exact (div_le_one hNr).2 (by exact_mod_cast hAN)
    obtain ⟨g, P, hg, hgZero, hmass, hpair, hsubset, hbad, hpiece, hMoment⟩ :=
      hstructure N A hN hA hsub (lt_of_not_ge hsmall)
    have hf (n : ℕ) : 0 ≤ f n ∧ f n ≤ 1 := by dsimp [f]; split_ifs <;> norm_num
    have hfZero (n : ℕ) (hn : n ∉ S) : f n = 0 := if_neg (fun ha => hn (hsub ha))
    have hMean : ∑ n ∈ S, g n = δ * N := by
      have h := hmass Set.univ
      simp only [Set.mem_univ, filter_true] at h
      rw [← h, sum_indicator_card]
      have he : S.filter (fun n => n ∈ A) = A := by
        ext n
        exact mem_filter.trans (and_iff_right_of_imp fun hn => hsub hn)
      rw [he]
      exact (div_mul_cancel₀ _ hNr.ne').symm
    have hDifference : |average N K f - average N K g| ≤ σ * δ^K / 2 := by
      have h := hcount N f g hN (fun n => ⟨hf n, hg n⟩)
        (fun n hn => ⟨hfZero n hn, hgZero n hn⟩)
      apply le_of_pow_le_pow_left₀ (n := q) (by dsimp [q]; positivity) (by positivity)
      change |average N K f - average N K g|^q ≤ _ at h
      calc
        |average N K f - average N K g|^q ≤ c * (θ * δ^(K*q)) :=
          h.trans (mul_le_mul_of_nonneg_left hMoment hc.le)
        _ = (σ * δ^K / 2)^q := by
          dsimp [θ]
          rw [show σ * δ^K / 2 = (σ / 2) * δ^K by ring, mul_pow, ← pow_mul]
          field_simp
    have hDist : σ * δ^K < |average N K f - average N K v| := by
      have hff : average N K f = (count A : ℝ) / total := average_indicator N K A
      have hvv : average N K v = δ^K * count S / total := by
        have hv : v = fun n => δ * (if n ∈ S then 1 else 0) := by
          funext n
          dsimp [v]
          split_ifs <;> ring
        have hscale : average N K (fun n => δ * (if n ∈ S then 1 else 0)) =
            δ^K * average N K (fun n => if n ∈ S then 1 else 0) :=
          average_smul N K δ (fun n => if n ∈ S then 1 else 0)
        have hind : average N K (fun n => if n ∈ S then 1 else 0) =
            (count S : ℝ) / total := average_indicator N K S
        rw [hv, hscale, hind, mul_div_assoc]
      rw [hff, hvv]
      rw [show σ * δ^K = δ^K / (256 * κ) by dsimp [σ]; ring]
      exact lt_of_not_ge hclose
    have hLarge : σ * δ^K / 2 < |average N K g - average N K v| := by
      linarith only [hDist, hDifference, abs_sub_le (average N K f) (average N K g) (average N K v)]
    let H := S.filter (fun n => (1 + γ) * δ < g n)
    have hUpper := count_gap_le_high_mass N k δ γ g hδ.le hδone hγ.le hγPow hg hgZero hMean
    change |average N K g - average N K v| ≤
      7*κ*H.card / DN + 4*κ*γ*δ^K at hUpper
    rw [hcoef] at hUpper
    have hDN : 0 < DN := by dsimp [DN]; positivity
    have hlowerRate : σ * δ^K / 4 ≤ 7 * κ * H.card / DN := by linarith only [hLarge, hUpper]
    have hlower : α * δ^K * DN ≤ (H.card : ℝ) := by
      have he : α * δ^K * DN = (σ * δ^K / 4 * DN) / (7 * κ) := by
        dsimp [α]
        field_simp
        ring
      rw [he, div_le_iff₀ (by positivity)]
      simpa only [mul_comm (H.card : ℝ) (7 * κ)] using (le_div_iff₀ hDN).mp hlowerRate
    have hH : H.Nonempty := by
      have hpos : (0 : ℝ) < H.card := (by positivity : 0 < α * δ^K * DN).trans_le hlower
      exact card_pos.mp (by exact_mod_cast hpos)
    have hbad' : ((S \ P.biUnion ap).card : ℝ) ≤ γ * δ * H.card / 2 := by
      apply hbad.trans
      calc
        β * δ^(K + 1) * N = (γ * δ / 2) * (α * δ^K * N) := by dsimp [β]; rw [pow_succ]; ring
        _ ≤ (γ * δ / 2) * (α * δ^K * DN) := by gcongr; dsimp [DN]; linarith
        _ ≤ _ := (mul_le_mul_of_nonneg_left hlower (by positivity)).trans_eq (by ring)
    have hHeavyMass : (1 + γ) * δ * H.card ≤ ∑ n ∈ H, f n := by
      have hEq : (∑ n ∈ H, f n) = ∑ n ∈ H, g n := hmass (Set.Ioi ((1 + γ) * δ))
      rw [hEq, mul_comm ((1 + γ) * δ), ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun n hn => (mem_filter.mp hn).2.le
    obtain ⟨p, hp, -, -, hdensity⟩ := exists_dense_piece S H P ap f δ γ hδ hγ.le hH
      (filter_subset _ _) hpair
      (fun p hp n hn m hm => by
        have hS (z : ℕ) (hz : z ∈ ap p) : z ∈ S :=
          hsubset (mem_biUnion.mpr ⟨p, hp, hz⟩)
        simp only [H, mem_filter, hS n hn, hS m hm, true_and, (hpiece p hp).2.2 n hn m hm])
      (fun n _ => (hf n).2) hHeavyMass hbad'
    obtain ⟨hd, hlength, -⟩ := hpiece p hp
    refine ⟨p.1, p.2.1, p.2.2, hd, ?_, hlength, ?_⟩
    · intro i hi
      have hi' : i - 1 < p.2.2 := by have hh := mem_Icc.mp hi; omega
      exact hsubset (mem_biUnion.mpr ⟨p, hp, mem_image.mpr ⟨i-1, mem_range.mpr hi', rfl⟩⟩)
    · have hinj : Function.Injective (fun i : ℕ => p.1 + i*p.2.1) :=
        fun _ _ h => Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)
      have hcard : (ap p).card = p.2.2 := by simp only [ap, card_image_of_injective _ hinj, card_range]
      have hsum := sum_affine_piece p.1 p.2.1 p.2.2 hd A
      change (∑ n ∈ ap p, f n) = _ at hsum
      rw [hcard, hsum] at hdensity
      have hM : (0 : ℝ) < p.2.2 := (Real.rpow_pos_of_pos hNr _).trans_le hlength
      exact (le_div_iff₀ hM).mpr hdensity

end OMA.R_Erdos3_erdos_3_variants_leng_sah_sawhney_R1_H1_R1_H1_R1
