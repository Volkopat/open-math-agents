import OMAReductions.R_erdos_132_R1_H2_R1

/-
Step erdos-132.R1.H2.R1.H1: hypothesis H1 of reduction erdos-132.R1.H2.R1.
Credit: @Pampasgras

Every complete grid P i j = o + x i • u + y j • v (i ≤ r, j ≤ s, ⟪u,v⟫ ≥ 0, x and y strictly
increasing) with at least 128 k³ points has at least k rare distances.

Idea. A box is a pair of index intervals [a,b] × [c,e]; its diagonal is dist (P a c) (P b e) and its
defect is a + (r - b) + c + (s - e). Every pair of grid points is at most as long as the diagonal
of the box it spans, and enlarging a box strictly lengthens its diagonal. Growing a box one index
at a time up to the full grid therefore shows that at least defect-many distances of the grid
exceed its diagonal. So a distance d with fewer than k larger distances is only realised by pairs
whose box has defect < k: the indices i, j, i' lie within k of an end of their range, and for fixed
(i, j, i') at most two j' work (a circle meets a line twice). That gives at most 2(2k)³ ordered
pairs, hence multiplicity ≤ 8k³ ≤ |grid|. Finally the grid has at least k distances, so at least
k of them have fewer than k larger ones.
-/

open Finset
open scoped Classical InnerProductSpace
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

namespace OMA.GridPlan

lemma sq_le_imp_le {p q : ℝ} (hq : 0 ≤ q) (h : p ^ 2 ≤ q ^ 2) : p ≤ q := by
  by_contra hlt
  rw [not_le] at hlt
  nlinarith

lemma sq_lt_imp_lt {p q : ℝ} (hq : 0 ≤ q) (h : p ^ 2 < q ^ 2) : p < q := by
  by_contra hlt
  rw [not_lt] at hlt
  nlinarith

lemma fst_ne_zero {u v : EuclideanSpace ℝ (Fin 2)} (hind : LinearIndependent ℝ ![u, v]) :
    u ≠ 0 := by
  have h := hind.ne_zero 0
  simpa using h

lemma snd_ne_zero {u v : EuclideanSpace ℝ (Fin 2)} (hind : LinearIndependent ℝ ![u, v]) :
    v ≠ 0 := by
  have h := hind.ne_zero 1
  simpa using h

/-- The quadratic form X²A + Y²B + 2XYC is strictly increasing on X, Y ≥ 0. -/
lemma form_lt {A B C X Y X' Y' : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 ≤ C)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hXX : X ≤ X') (hYY : Y ≤ Y') (hs : X < X' ∨ Y < Y') :
    X ^ 2 * A + Y ^ 2 * B + 2 * (X * Y) * C < X' ^ 2 * A + Y' ^ 2 * B + 2 * (X' * Y') * C := by
  have h1 : X ^ 2 ≤ X' ^ 2 := pow_le_pow_left₀ hX hXX 2
  have h2 : Y ^ 2 ≤ Y' ^ 2 := pow_le_pow_left₀ hY hYY 2
  have h3 : X * Y ≤ X' * Y' := mul_le_mul hXX hYY hY (hX.trans hXX)
  have h4 : 2 * (X * Y) * C ≤ 2 * (X' * Y') * C :=
    mul_le_mul_of_nonneg_right (by linarith) hC
  have h5 : X ^ 2 * A ≤ X' ^ 2 * A := mul_le_mul_of_nonneg_right h1 hA.le
  have h6 : Y ^ 2 * B ≤ Y' ^ 2 * B := mul_le_mul_of_nonneg_right h2 hB.le
  rcases hs with hs | hs
  · have h7 : X ^ 2 < X' ^ 2 := pow_lt_pow_left₀ hs hX two_ne_zero
    have h8 : X ^ 2 * A < X' ^ 2 * A := mul_lt_mul_of_pos_right h7 hA
    linarith
  · have h7 : Y ^ 2 < Y' ^ 2 := pow_lt_pow_left₀ hs hY two_ne_zero
    have h8 : Y ^ 2 * B < Y' ^ 2 * B := mul_lt_mul_of_pos_right h7 hB
    linarith

/-- Passing to a larger threshold loses at least that threshold. -/
lemma card_gt_step (S : Finset ℝ) {d d' : ℝ} (h : d < d') (hd' : d' ∈ S) :
    (S.filter (fun e => d' < e)).card + 1 ≤ (S.filter (fun e => d < e)).card := by
  have hnot : d' ∉ S.filter (fun e => d' < e) := by
    intro hmem
    exact lt_irrefl d' (mem_filter.mp hmem).2
  rw [← card_insert_of_notMem hnot]
  apply card_le_card
  intro e he
  rcases mem_insert.mp he with heq | he
  · rw [heq]
    exact mem_filter.mpr ⟨hd', h⟩
  · exact mem_filter.mpr ⟨(mem_filter.mp he).1, h.trans (mem_filter.mp he).2⟩

lemma card_gt_succ_le (S : Finset ℝ) {d : ℝ} (hd : d ∈ S) :
    (S.filter (fun e => d < e)).card + 1 ≤ S.card := by
  have h : (S.filter (fun e => d < e)).card < S.card :=
    card_lt_card (filter_ssubset.mpr ⟨d, hd, lt_irrefl d⟩)
  omega

/-- L1. Squared distance between two grid points. -/
lemma grid_dist_sq (o u v : EuclideanSpace ℝ (Fin 2)) (x y : ℕ → ℝ) (i j i' j' : ℕ) :
    dist (o + x i • u + y j • v) (o + x i' • u + y j' • v) ^ 2 =
      (x i' - x i) ^ 2 * ‖u‖ ^ 2 + (y j' - y j) ^ 2 * ‖v‖ ^ 2
        + 2 * ((x i' - x i) * (y j' - y j)) * ⟪u, v⟫_ℝ := by
  have h : o + x i • u + y j • v - (o + x i' • u + y j' • v)
      = -((x i' - x i) • u + (y j' - y j) • v) := by
    module
  rw [dist_eq_norm, h, norm_neg, norm_add_sq_real]
  simp only [norm_smul, real_inner_smul_left, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
    sq_abs]
  ring

/-- L2. Grid points with different indices are different points. -/
lemma grid_injective (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) {i j i' j' : ℕ}
    (h : o + x i • u + y j • v = o + x i' • u + y j' • v) : i = i' ∧ j = j' := by
  have h0 : (x i - x i') • u + (y j - y j') • v = 0 := by
    have h1 : (x i - x i') • u + (y j - y j') • v
        = (o + x i • u + y j • v) - (o + x i' • u + y j' • v) := by
      module
    rw [h1, h, sub_self]
  obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hind _ _ h0
  exact ⟨hx.injective (sub_eq_zero.mp h1), hy.injective (sub_eq_zero.mp h2)⟩

/-- L3. The grid has exactly (r+1)(s+1) points. -/
lemma grid_card (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s : ℕ) :
    (((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).card
      = (r+1)*(s+1) := by
  rw [card_image_of_injOn, card_product, card_range, card_range]
  intro p _ q _ h
  have h' : o + x p.1 • u + y p.2 • v = o + x q.1 • u + y q.2 • v := h
  obtain ⟨h1, h2⟩ := grid_injective o u v hind x y hx hy h'
  exact Prod.ext h1 h2

/-- Two grid points with different indices give a distance of the grid. -/
lemma dist_mem (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s : ℕ) {i j i' j' : ℕ}
    (hi : i ≤ r) (hi' : i' ≤ r) (hj : j ≤ s) (hj' : j' ≤ s) (hne : i ≠ i' ∨ j ≠ j') :
    dist (o + x i • u + y j • v) (o + x i' • u + y j' • v) ∈
      ((((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image
        (fun p => dist p.1 p.2)) := by
  refine mem_image.mpr ⟨(o + x i • u + y j • v, o + x i' • u + y j' • v),
    mem_offDiag.mpr ⟨?_, ?_, ?_⟩, rfl⟩
  · exact mem_image.mpr ⟨(i, j),
      mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, rfl⟩
  · exact mem_image.mpr ⟨(i', j'),
      mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, rfl⟩
  · intro h
    obtain ⟨h1, h2⟩ := grid_injective o u v hind x y hx hy h
    omega

/-- L4. Every pair is at most as long as the diagonal of the box it spans
(the cross term 2·Δx·Δy·⟪u,v⟫ is at most 2·|Δx|·|Δy|·⟪u,v⟫ because ⟪u,v⟫ ≥ 0). -/
lemma dist_le_box (o u v : EuclideanSpace ℝ (Fin 2)) (huv : 0 ≤ ⟪u, v⟫_ℝ)
    (x y : ℕ → ℝ) (hx : Monotone x) (hy : Monotone y) (i j i' j' : ℕ) :
    dist (o + x i • u + y j • v) (o + x i' • u + y j' • v) ≤
      dist (o + x (min i i') • u + y (min j j') • v)
        (o + x (max i i') • u + y (max j j') • v) := by
  apply sq_le_imp_le dist_nonneg
  rw [grid_dist_sq, grid_dist_sq]
  rcases le_total i i' with h | h <;> rcases le_total j j' with h' | h'
  · rw [min_eq_left h, max_eq_right h, min_eq_left h', max_eq_right h']
  · rw [min_eq_left h, max_eq_right h, min_eq_right h', max_eq_left h']
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (hx h)) (sub_nonneg.mpr (hy h'))) huv]
  · rw [min_eq_right h, max_eq_left h, min_eq_left h', max_eq_right h']
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (hx h)) (sub_nonneg.mpr (hy h'))) huv]
  · rw [min_eq_right h, max_eq_left h, min_eq_right h', max_eq_left h']
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr (hx h)) (sub_nonneg.mpr (hy h'))) huv]

/-- L5. Enlarging a box strictly makes its diagonal strictly longer. -/
lemma diag_lt_diag (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (huv : 0 ≤ ⟪u, v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y)
    {a b c e a' b' c' e' : ℕ} (hab : a ≤ b) (hce : c ≤ e)
    (ha : a' ≤ a) (hb : b ≤ b') (hc : c' ≤ c) (he : e ≤ e')
    (hstrict : a' < a ∨ b < b' ∨ c' < c ∨ e < e') :
    dist (o + x a • u + y c • v) (o + x b • u + y e • v) <
      dist (o + x a' • u + y c' • v) (o + x b' • u + y e' • v) := by
  apply sq_lt_imp_lt dist_nonneg
  rw [grid_dist_sq, grid_dist_sq]
  have hab' := hx.monotone hab
  have hce' := hy.monotone hce
  have ha' := hx.monotone ha
  have hb' := hx.monotone hb
  have hc' := hy.monotone hc
  have he' := hy.monotone he
  apply form_lt (pow_pos (norm_pos_iff.mpr (fst_ne_zero hind)) 2)
    (pow_pos (norm_pos_iff.mpr (snd_ne_zero hind)) 2) huv
  · linarith
  · linarith
  · linarith
  · linarith
  · rcases hstrict with h | h | h | h
    · left
      have := hx h
      linarith
    · left
      have := hx h
      linarith
    · right
      have := hy h
      linarith
    · right
      have := hy h
      linarith

/-- L6. KEY. The diagonal of a box of defect δ has at least δ distinct grid distances above it:
grow the box one index at a time up to the full grid (L5); each step gives a new, larger distance.
Induction on the defect. -/
lemma defect_le_card_gt (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (huv : 0 ≤ ⟪u, v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s : ℕ)
    {a b c e : ℕ} (hab : a ≤ b) (hbr : b ≤ r) (hce : c ≤ e) (hes : e ≤ s) :
    a + (r - b) + c + (s - e) ≤
      (((((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image
        (fun p => dist p.1 p.2)).filter
          (fun d => dist (o + x a • u + y c • v) (o + x b • u + y e • v) < d)).card := by
  have key : ∀ n a b c e : ℕ, a ≤ b → b ≤ r → c ≤ e → e ≤ s → a + (r - b) + c + (s - e) = n →
      n ≤ (((((range (r+1)) ×ˢ (range (s+1))).image
        (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image (fun p => dist p.1 p.2)).filter
          (fun d => dist (o + x a • u + y c • v) (o + x b • u + y e • v) < d)).card := by
    intro n
    induction n with
    | zero =>
      intro a b c e _ _ _ _ _
      exact Nat.zero_le _
    | succ n ih =>
      intro a b c e hab hbr hce hes hn
      have step : ∀ a' b' c' e' : ℕ, a' ≤ a → b ≤ b' → c' ≤ c → e ≤ e' → b' ≤ r → e' ≤ s →
          (a' < a ∨ b < b' ∨ c' < c ∨ e < e') → a' + (r - b') + c' + (s - e') = n →
          n + 1 ≤ (((((range (r+1)) ×ˢ (range (s+1))).image
            (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image (fun p => dist p.1 p.2)).filter
              (fun d => dist (o + x a • u + y c • v) (o + x b • u + y e • v) < d)).card := by
        intro a' b' c' e' ha hb hc he hbr' hes' hstrict hn'
        have hlt := diag_lt_diag o u v hind huv x y hx hy hab hce ha hb hc he hstrict
        have hmem := dist_mem o u v hind x y hx hy r s (i := a') (j := c') (i' := b') (j' := e')
          (by omega) hbr' (by omega) hes' (by omega)
        have hih := ih a' b' c' e' (by omega) hbr' (by omega) hes' hn'
        exact (Nat.add_le_add_right hih 1).trans (card_gt_step _ hlt hmem)
      by_cases h1 : 0 < a
      · exact step (a - 1) b c e (by omega) le_rfl le_rfl le_rfl hbr hes (by omega) (by omega)
      by_cases h2 : b < r
      · exact step a (b + 1) c e le_rfl (by omega) le_rfl le_rfl (by omega) hes (by omega)
          (by omega)
      by_cases h3 : 0 < c
      · exact step a b (c - 1) e le_rfl le_rfl (by omega) le_rfl hbr hes (by omega) (by omega)
      · exact step a b c (e + 1) le_rfl le_rfl le_rfl (by omega) hbr (by omega) (by omega)
          (by omega)
  exact key _ a b c e hab hbr hce hes rfl

/-- L7. Any pair of grid points: its box defect is at most its rank (L4 + L6). -/
lemma defect_le_rank (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (huv : 0 ≤ ⟪u, v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s : ℕ)
    {i j i' j' : ℕ} (hi : i ≤ r) (hi' : i' ≤ r) (hj : j ≤ s) (hj' : j' ≤ s) :
    min i i' + (r - max i i') + min j j' + (s - max j j') ≤
      (((((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image
        (fun p => dist p.1 p.2)).filter
          (fun d => dist (o + x i • u + y j • v) (o + x i' • u + y j' • v) < d)).card := by
  have h6 := defect_le_card_gt o u v hind huv x y hx hy r s (a := min i i') (b := max i i')
    (c := min j j') (e := max j j') (by omega) (by omega) (by omega) (by omega)
  have h4 := dist_le_box o u v huv x y hx.monotone hy.monotone i j i' j'
  refine h6.trans (card_le_card ?_)
  intro d hd
  exact mem_filter.mpr ⟨(mem_filter.mp hd).1, lt_of_le_of_lt h4 (mem_filter.mp hd).2⟩

/-- Squared distance from w to the point of parameter t on the line q0 + t • v. -/
lemma dist_line_sq (q0 v w : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    dist w (q0 + t • v) ^ 2 = ‖w - q0‖ ^ 2 - 2 * t * ⟪w - q0, v⟫_ℝ + t ^ 2 * ‖v‖ ^ 2 := by
  have h : w - (q0 + t • v) = (w - q0) - t • v := by
    abel
  rw [dist_eq_norm, h, norm_sub_sq_real]
  simp only [norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- L8. A circle meets a line in at most two points. -/
lemma line_sphere (q0 v w : EuclideanSpace ℝ (Fin 2)) (hv : v ≠ 0) (y : ℕ → ℝ)
    (hy : Function.Injective y) (s : ℕ) (d : ℝ) :
    ((range (s+1)).filter (fun j => dist w (q0 + y j • v) = d)).card ≤ 2 := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨j1, j2, j3, h1, h2, h3, h12, h13, h23⟩ := two_lt_card_iff.mp hcon
  have e1 := (mem_filter.mp h1).2
  have e2 := (mem_filter.mp h2).2
  have e3 := (mem_filter.mp h3).2
  have q1 := dist_line_sq q0 v w (y j1)
  have q2 := dist_line_sq q0 v w (y j2)
  have q3 := dist_line_sq q0 v w (y j3)
  rw [e1] at q1
  rw [e2] at q2
  rw [e3] at q3
  have hB : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
  have n12 : y j1 ≠ y j2 := fun h => h12 (hy h)
  have n13 : y j1 ≠ y j3 := fun h => h13 (hy h)
  have n23 : y j2 ≠ y j3 := fun h => h23 (hy h)
  have a12 : (y j1 - y j2) * (‖v‖ ^ 2 * (y j1 + y j2) - 2 * ⟪w - q0, v⟫_ℝ) = 0 := by
    linear_combination q2 - q1
  have a13 : (y j1 - y j3) * (‖v‖ ^ 2 * (y j1 + y j3) - 2 * ⟪w - q0, v⟫_ℝ) = 0 := by
    linear_combination q3 - q1
  have b12 := (mul_eq_zero.mp a12).resolve_left (sub_ne_zero.mpr n12)
  have b13 := (mul_eq_zero.mp a13).resolve_left (sub_ne_zero.mpr n13)
  have hz : ‖v‖ ^ 2 * (y j2 - y j3) = 0 := by
    linear_combination b12 - b13
  rcases mul_eq_zero.mp hz with h | h
  · exact hB.ne' h
  · exact n23 (sub_eq_zero.mp h)

/-- L9. Indices within k of either end of [0, r]: at most 2k of them. -/
lemma window_card (r k : ℕ) :
    ((range (r+1)).filter (fun t => t < k ∨ r < t + k)).card ≤ 2 * k := by
  have hsub : (range (r+1)).filter (fun t => t < k ∨ r < t + k) ⊆
      range k ∪ (range k).image (fun i => r - i) := by
    intro t ht
    obtain ⟨htr, h⟩ := mem_filter.mp ht
    have htr' := mem_range.mp htr
    rcases h with h | h
    · exact mem_union_left _ (mem_range.mpr h)
    · refine mem_union_right _ (mem_image.mpr ⟨r - t, mem_range.mpr (by omega), ?_⟩)
      show r - (r - t) = t
      omega
  have h1 := card_le_card hsub
  have h2 := card_union_le (range k) ((range k).image (fun i => r - i))
  have h3 := card_image_le (s := range k) (f := fun i => r - i)
  rw [card_range] at h2 h3
  omega

/-- L10. COUNT. A distance of rank < k is realised by at most 2(2k)³ ordered pairs. -/
lemma top_mult_le (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (huv : 0 ≤ ⟪u, v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s k : ℕ)
    (d : ℝ)
    (hd : ((((((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image
        (fun p => dist p.1 p.2)).filter (fun e => d < e)).card < k)) :
    ((((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).offDiag.filter
      (fun p => dist p.1 p.2 = d)).card ≤ 2 * (2 * k) ^ 3 := by
  have hsub : ((((range (r+1)) ×ˢ (range (s+1))).image
      (fun p => o + x p.1 • u + y p.2 • v)).offDiag.filter (fun p => dist p.1 p.2 = d)) ⊆
      (((range (r+1)).filter (fun t => t < k ∨ r < t + k)) ×ˢ
        ((range (s+1)).filter (fun t => t < k ∨ s < t + k)) ×ˢ
        ((range (r+1)).filter (fun t => t < k ∨ r < t + k))).biUnion
        (fun t => ((range (s+1)).filter
          (fun j' => dist (o + x t.1 • u + y t.2.1 • v) (o + x t.2.2 • u + y j' • v) = d)).image
          (fun j' => (o + x t.1 • u + y t.2.1 • v, o + x t.2.2 • u + y j' • v))) := by
    intro p hp
    obtain ⟨hp1, hpd⟩ := mem_filter.mp hp
    obtain ⟨hpa, hpb, -⟩ := mem_offDiag.mp hp1
    obtain ⟨⟨i, j⟩, hij, e1⟩ := mem_image.mp hpa
    obtain ⟨⟨i', j'⟩, hij', e2⟩ := mem_image.mp hpb
    obtain ⟨hi, hj⟩ := mem_product.mp hij
    obtain ⟨hi', hj'⟩ := mem_product.mp hij'
    have hi2 : i < r + 1 := mem_range.mp hi
    have hj2 : j < s + 1 := mem_range.mp hj
    have hi2' : i' < r + 1 := mem_range.mp hi'
    have hj2' : j' < s + 1 := mem_range.mp hj'
    have e1' : o + x i • u + y j • v = p.1 := e1
    have e2' : o + x i' • u + y j' • v = p.2 := e2
    have h7 := defect_le_rank o u v hind huv x y hx hy r s (i := i) (j := j) (i' := i') (j' := j')
      (by omega) (by omega) (by omega) (by omega)
    rw [e1', e2', hpd] at h7
    have hlt := lt_of_le_of_lt h7 hd
    refine mem_biUnion.mpr ⟨(i, j, i'), ?_, ?_⟩
    · have w1 : i < k ∨ r < i + k := by omega
      have w2 : j < k ∨ s < j + k := by omega
      have w3 : i' < k ∨ r < i' + k := by omega
      exact mem_product.mpr ⟨mem_filter.mpr ⟨hi, w1⟩,
        mem_product.mpr ⟨mem_filter.mpr ⟨hj, w2⟩, mem_filter.mpr ⟨hi', w3⟩⟩⟩
    · refine mem_image.mpr ⟨j', mem_filter.mpr ⟨hj', ?_⟩, ?_⟩
      · show dist (o + x i • u + y j • v) (o + x i' • u + y j' • v) = d
        rw [e1', e2']
        exact hpd
      · exact Prod.ext e1' e2'
  refine (card_le_card hsub).trans ((card_biUnion_le_card_mul _ _ 2 ?_).trans ?_)
  · intro t _
    exact card_image_le.trans (line_sphere (o + x t.2.2 • u) v (o + x t.1 • u + y t.2.1 • v)
      (snd_ne_zero hind) y hy.injective s d)
  · rw [card_product, card_product]
    have h1 := window_card r k
    have h2 := window_card s k
    calc _ ≤ (2 * k * (2 * k * (2 * k))) * 2 :=
          Nat.mul_le_mul_right 2 (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h1))
      _ = 2 * (2 * k) ^ 3 := by ring

/-- L11. A finite set of reals with at least k elements has at least k elements of rank < k
(rank is injective on S with values in range S.card, hence onto it). -/
lemma top_k (S : Finset ℝ) (k : ℕ) (hk : k ≤ S.card) :
    k ≤ (S.filter (fun d => (S.filter (fun e => d < e)).card < k)).card := by
  have hanti : ∀ d ∈ S, ∀ d' ∈ S, d < d' →
      (S.filter (fun e => d' < e)).card < (S.filter (fun e => d < e)).card := by
    intro d _ d' hd' h
    have := card_gt_step S h hd'
    omega
  have hinj : Set.InjOn (fun d => (S.filter (fun e => d < e)).card) (S : Set ℝ) := by
    intro d hd d' hd' h
    have h' : (S.filter (fun e => d < e)).card = (S.filter (fun e => d' < e)).card := h
    rcases lt_trichotomy d d' with hlt | heq | hgt
    · have := hanti d (mem_coe.mp hd) d' (mem_coe.mp hd') hlt
      omega
    · exact heq
    · have := hanti d' (mem_coe.mp hd') d (mem_coe.mp hd) hgt
      omega
  have himg : S.image (fun d => (S.filter (fun e => d < e)).card) = range S.card := by
    apply eq_of_subset_of_card_le
    · intro n hn
      obtain ⟨d, hd, rfl⟩ := mem_image.mp hn
      have := card_gt_succ_le S hd
      exact mem_range.mpr (by omega)
    · rw [card_image_of_injOn hinj, card_range]
  have hsub : range k ⊆ (S.filter (fun d => (S.filter (fun e => d < e)).card < k)).image
      (fun d => (S.filter (fun e => d < e)).card) := by
    intro n hn
    have hn' := mem_range.mp hn
    have hmem : n ∈ S.image (fun d => (S.filter (fun e => d < e)).card) := by
      rw [himg]
      exact mem_range.mpr (by omega)
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hmem
    exact mem_image.mpr ⟨d, mem_filter.mpr ⟨hd, hn'⟩, rfl⟩
  have h1 := card_le_card hsub
  have h2 := card_image_le (s := S.filter (fun d => (S.filter (fun e => d < e)).card < k))
    (f := fun d => (S.filter (fun e => d < e)).card)
  rw [card_range] at h1
  exact h1.trans h2

/-- L12. A grid with at least 128k³ points (k ≥ 1) has at least k distinct distances. -/
lemma k_le_distances (o u v : EuclideanSpace ℝ (Fin 2)) (hind : LinearIndependent ℝ ![u, v])
    (huv : 0 ≤ ⟪u, v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s k : ℕ)
    (hk1 : 1 ≤ k) (hk : 128*k^3 ≤ (r+1)*(s+1)) :
    k ≤ ((((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)).offDiag.image
      (fun p => dist p.1 p.2)).card := by
  have hrs : k ≤ r + s := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (r+1)*(s+1) ≤ k * k := Nat.mul_le_mul (by omega) (by omega)
    have h2 : k * k ≤ k ^ 3 := by
      calc k * k = k * k * 1 := (mul_one _).symm
        _ ≤ k * k * k := Nat.mul_le_mul_left _ hk1
        _ = k ^ 3 := by ring
    have h3 : 0 < k ^ 3 := pow_pos hk1 3
    have h4 : 128 * k ^ 3 ≤ k ^ 3 := hk.trans (h1.trans h2)
    omega
  rcases Nat.eq_zero_or_pos s with hs | hs
  · have h6 := defect_le_card_gt o u v hind huv x y hx hy r s (a := 0) (b := 1) (c := 0) (e := 0)
      (by omega) (by omega) le_rfl (by omega)
    have hm := dist_mem o u v hind x y hx hy r s (i := 0) (j := 0) (i' := 1) (j' := 0)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have h := (Nat.add_le_add_right h6 1).trans (card_gt_succ_le _ hm)
    omega
  · have h6 := defect_le_card_gt o u v hind huv x y hx hy r s (a := 0) (b := 0) (c := 0) (e := 1)
      le_rfl (by omega) (by omega) (by omega)
    have hm := dist_mem o u v hind x y hx hy r s (i := 0) (j := 0) (i' := 0) (j' := 1)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have h := (Nat.add_le_add_right h6 1).trans (card_gt_succ_le _ hm)
    omega

end OMA.GridPlan

/-- Assembly: the distances of rank < k are rare, and there are at least k of them. -/
theorem OMA.solution : OMA.R_erdos_132_R1_H2_R1.H1 := by
  intro o u v hind huv x y hx hy r s k hk
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact Nat.zero_le _
  set A := ((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v) with hA
  set D := A.offDiag.image (fun p => dist p.1 p.2) with hD
  have hsub : D.filter (fun d => (D.filter (fun e => d < e)).card < k) ⊆ rareDistances A := by
    intro d hd
    obtain ⟨hdD, hrank⟩ := mem_filter.mp hd
    refine mem_filter.mpr ⟨hdD, OMA.R_erdos_132_R1.multiplicity_pos hdD, ?_⟩
    have hm : (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card ≤ 2 * (2 * k) ^ 3 :=
      GridPlan.top_mult_le o u v hind huv x y hx hy r s k d hrank
    have hcard : A.card = (r+1)*(s+1) := GridPlan.grid_card o u v hind x y hx hy r s
    have h8 : 2 * (2 * k) ^ 3 = 2 * (8 * k ^ 3) := by ring
    show (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2 ≤ A.card
    rw [hcard]
    have h1 : (A.offDiag.filter (fun p => dist p.1 p.2 = d)).card / 2 ≤ 8 * k ^ 3 := by
      rw [h8] at hm; omega
    have h2 : 8 * k ^ 3 ≤ 128 * k ^ 3 := by omega
    omega
  calc k ≤ (D.filter (fun d => (D.filter (fun e => d < e)).card < k)).card :=
        GridPlan.top_k D k (GridPlan.k_le_distances o u v hind huv x y hx hy r s k hk1 hk)
    _ ≤ (rareDistances A).card := card_le_card hsub
