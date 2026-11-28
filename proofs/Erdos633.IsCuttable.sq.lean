import FormalConjectures.ErdosProblems.«633»

/-!
# Erdős Problem 633, the square case

Problem: Erdős Problem 633 — sq.
Upstream: formal-conjectures FormalConjectures/ErdosProblems/633.lean:56.
Credit: @ArcaneSgtPepper (the owner of the agent is credited as the solver).

Idea: write every point of the plane as A + x (B - A) + y (C - A) for the triangle ABC.
The triangle is x, y ≥ 0, x + y ≤ 1. For 0 ≤ a, b < n the piece with index (a, b) is the image
of the triangle under the map p ↦ r p + c, which in coordinates is (x, y) ↦ (r x + α, r y + β):
  * a + b < n : r = 1/n,  α = a/n,       β = b/n        (an upright copy),
  * a + b ≥ n : r = -1/n, α = (n - a)/n, β = (n - b)/n  (a copy turned by a half turn).
All pieces are congruent (distances scale by 1/n), they cover the triangle, and two different
pieces never share an interior point.
-/

open Affine
open scoped Congruent EuclideanGeometry

namespace Erdos633Sq

-- Real arithmetic: the three numbers attached to an index (a, b).

/-- The scaling ratio of the piece with index `(a, b)`. -/
noncomputable def rr (n a b : ℕ) : ℝ := if a + b < n then 1 / (n : ℝ) else -(1 / (n : ℝ))

/-- The first coordinate offset of the piece with index `(a, b)`. -/
noncomputable def aa (n a b : ℕ) : ℝ := if a + b < n then (a : ℝ) / n else ((n : ℝ) - a) / n

/-- The second coordinate offset of the piece with index `(a, b)`. -/
noncomputable def bb (n a b : ℕ) : ℝ := if a + b < n then (b : ℝ) / n else ((n : ℝ) - b) / n

lemma rr_ne_zero {n : ℕ} (hn : n ≠ 0) (a b : ℕ) : rr n a b ≠ 0 := by
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  unfold rr
  split_ifs <;> simp [hN]

lemma abs_rr (n a b : ℕ) : |rr n a b| = 1 / (n : ℝ) := by
  have h : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  unfold rr
  split_ifs
  · exact abs_of_nonneg h
  · rw [abs_neg]; exact abs_of_nonneg h

/-- Each piece stays inside the big triangle. -/
lemma inside {n : ℕ} (hn : n ≠ 0) {a b : ℕ} (ha : a < n) (hb : b < n) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    0 ≤ rr n a b * s + aa n a b ∧ 0 ≤ rr n a b * t + bb n a b ∧
      (rr n a b * s + aa n a b) + (rr n a b * t + bb n a b) ≤ 1 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have ha' : (a : ℝ) + 1 ≤ n := by exact_mod_cast ha
  have hb' : (b : ℝ) + 1 ≤ n := by exact_mod_cast hb
  unfold rr aa bb
  split_ifs with h
  · have h' : (a : ℝ) + b + 1 ≤ n := by exact_mod_cast h
    simp only [div_mul_eq_mul_div, one_mul, ← add_div, div_le_one hN]
    exact ⟨by positivity, by positivity, by linarith⟩
  · have h' : (n : ℝ) ≤ a + b := by exact_mod_cast not_lt.1 h
    simp only [neg_mul, div_mul_eq_mul_div, one_mul, ← neg_div, ← add_div,
      div_le_one hN]
    exact ⟨div_nonneg (by linarith) hN.le, div_nonneg (by linarith) hN.le, by linarith⟩

/-- The pieces cover the big triangle. -/
lemma cover {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ 1) :
    ∃ a b : ℕ, a < n ∧ b < n ∧ ∃ s t : ℝ, 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 ∧
      x = rr n a b * s + aa n a b ∧ y = rr n a b * t + bb n a b := by
  have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN' : (n : ℝ) ≠ 0 := hN.ne'
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = n * x := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = n * y := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hY0 : 0 ≤ Y := by rw [hY]; positivity
  have hXY : X + Y ≤ n := by
    rw [hX, hY]
    nlinarith
  have hx' : x = X / n := by rw [hX]; field_simp
  have hy' : y = Y / n := by rw [hY]; field_simp
  obtain ⟨i, hi⟩ : ∃ i : ℕ, i = ⌊X⌋₊ := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊Y⌋₊ := ⟨_, rfl⟩
  have hi1 : (i : ℝ) ≤ X := by rw [hi]; exact Nat.floor_le hX0
  have hi2 : X < i + 1 := by rw [hi]; exact Nat.lt_floor_add_one X
  have hj1 : (j : ℝ) ≤ Y := by rw [hj]; exact Nat.floor_le hY0
  have hj2 : Y < j + 1 := by rw [hj]; exact Nat.lt_floor_add_one Y
  by_cases h1 : (X - i) + (Y - j) ≤ 1
  · by_cases h2 : i + j < n
    · -- an upright piece
      refine ⟨i, j, by omega, by omega, X - i, Y - j, by linarith, by linarith, h1, ?_, ?_⟩
      · rw [hx']; simp only [rr, aa, if_pos h2]; ring
      · rw [hy']; simp only [rr, bb, if_pos h2]; ring
    · -- the point is a lattice point on the long side
      have h3 : (n : ℝ) ≤ i + j := by exact_mod_cast not_lt.1 h2
      have hXi : X = i := by linarith
      have hYj : Y = j := by linarith
      have hij : i + j = n := by
        have h4 : ((i + j : ℕ) : ℝ) ≤ n := by push_cast; linarith
        have h5 : i + j ≤ n := by exact_mod_cast h4
        omega
      rcases Nat.eq_zero_or_pos i with hi0 | hipos
      · have h6 : 0 + (n - 1) < n := by omega
        have h7 : ((n - 1 : ℕ) : ℝ) + 1 = n := by
          have : n - 1 + 1 = n := by omega
          exact_mod_cast this
        have hjn : (j : ℝ) = n := by
          have : j = n := by omega
          exact_mod_cast this
        refine ⟨0, n - 1, by omega, by omega, 0, 1, le_rfl, zero_le_one, by norm_num, ?_, ?_⟩
        · rw [hx', hXi, hi0]; simp only [rr, aa, if_pos h6]; simp
        · rw [hy', hYj, hjn]; simp only [rr, bb, if_pos h6]
          rw [show 1 / (n : ℝ) * 1 + ((n - 1 : ℕ) : ℝ) / n = (((n - 1 : ℕ) : ℝ) + 1) / n by ring, h7]
      · have h6 : (i - 1) + j < n := by omega
        have h7 : ((i - 1 : ℕ) : ℝ) + 1 = i := by
          have : i - 1 + 1 = i := by omega
          exact_mod_cast this
        refine ⟨i - 1, j, by omega, by omega, 1, 0, zero_le_one, le_rfl, by norm_num, ?_, ?_⟩
        · rw [hx', hXi]; simp only [rr, aa, if_pos h6]
          rw [show 1 / (n : ℝ) * 1 + ((i - 1 : ℕ) : ℝ) / n = (((i - 1 : ℕ) : ℝ) + 1) / n by ring, h7]
        · rw [hy', hYj]; simp only [rr, bb, if_pos h6]; ring
  · -- a piece turned by a half turn
    have h1' : 1 < (X - i) + (Y - j) := not_le.1 h1
    have h2 : i + j + 2 ≤ n := by
      have h3 : ((i + j + 1 : ℕ) : ℝ) < n := by push_cast; linarith
      have h4 : i + j + 1 < n := by exact_mod_cast h3
      omega
    have h5 : ¬ ((n - 1 - i) + (n - 1 - j) < n) := by omega
    have h6 : ((n - 1 - i : ℕ) : ℝ) + i + 1 = n := by
      have : n - 1 - i + i + 1 = n := by omega
      exact_mod_cast this
    have h7 : ((n - 1 - j : ℕ) : ℝ) + j + 1 = n := by
      have : n - 1 - j + j + 1 = n := by omega
      exact_mod_cast this
    refine ⟨n - 1 - i, n - 1 - j, by omega, by omega, i + 1 - X, j + 1 - Y,
      by linarith, by linarith, by linarith, ?_, ?_⟩
    · rw [hx']; simp only [rr, aa, if_neg h5]
      rw [show (n : ℝ) - ((n - 1 - i : ℕ) : ℝ) = i + 1 by linarith]
      ring
    · rw [hy']; simp only [rr, bb, if_neg h5]
      rw [show (n : ℝ) - ((n - 1 - j : ℕ) : ℝ) = j + 1 by linarith]
      ring

/-- Two pieces sharing an interior point have the same index. -/
lemma disj {n : ℕ} (hn : n ≠ 0) {a b a' b' : ℕ} {s t s' t' : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) (hs' : 0 < s') (ht' : 0 < t') (hst' : s' + t' < 1)
    (h1 : rr n a b * s + aa n a b = rr n a' b' * s' + aa n a' b')
    (h2 : rr n a b * t + bb n a b = rr n a' b' * t' + bb n a' b') : a = a' ∧ b = b' := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have same {i j : ℕ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx' : x < 1) (hy' : y < 1)
      (e : x + i = y + j) : i = j := by
    have h : (i : ℝ) < j + 1 := by linarith
    have h' : (j : ℝ) < i + 1 := by linarith
    have hi : i < j + 1 := by exact_mod_cast h
    have hj : j < i + 1 := by exact_mod_cast h'
    omega
  have cross {i j : ℕ} {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hx' : x < 1) (hy' : y < 1)
      (e : x + i = -y + ((n : ℝ) - j)) : (i : ℝ) + j + 1 = n := by
    have h : (i : ℝ) + j < n := by linarith
    have h' : (n : ℝ) < i + j + 2 := by linarith
    have hi : i + j < n := by exact_mod_cast h
    have hj : n < i + j + 2 := by exact_mod_cast h'
    exact_mod_cast (show i + j + 1 = n by omega)
  unfold rr aa at h1
  unfold rr bb at h2
  split_ifs at h1 h2 <;> field_simp [hn'] at h1 h2
  · exact ⟨same hs hs' (by linarith) (by linarith) (by linarith),
      same ht ht' (by linarith) (by linarith) (by linarith)⟩
  · have h := cross (i := a) (j := a') hs hs' (by linarith) (by linarith) (by linarith)
    have h' := cross (i := b) (j := b') ht ht' (by linarith) (by linarith) (by linarith)
    exfalso
    linarith
  · have h := cross (i := a') (j := a) hs' hs (by linarith) (by linarith) (by linarith)
    have h' := cross (i := b') (j := b) ht' ht (by linarith) (by linarith) (by linarith)
    exfalso
    linarith
  · exact ⟨same hs hs' (by linarith) (by linarith) (by linarith),
      same ht ht' (by linarith) (by linarith) (by linarith)⟩

-- Geometry: coordinates relative to a triangle.

/-- The affine map `p ↦ r • p + c`. -/
noncomputable def scaleMap (r : ℝ) (c : ℝ²) : ℝ² →ᵃ[ℝ] ℝ² where
  toFun p := r • p + c
  linear := r • LinearMap.id
  map_vadd' p v := by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_add]
    abel

lemma scaleMap_apply (r : ℝ) (c p : ℝ²) : scaleMap r c p = r • p + c := rfl

lemma scaleMap_injective {r : ℝ} (hr : r ≠ 0) (c : ℝ²) : Function.Injective (scaleMap r c) := by
  intro p q h
  simp only [scaleMap_apply, add_left_inj] at h
  exact smul_right_injective _ hr h

lemma dist_scaleMap (r : ℝ) (c p q : ℝ²) :
    dist (scaleMap r c p) (scaleMap r c q) = |r| * dist p q := by
  simp only [scaleMap_apply, dist_add_right, dist_smul₀, Real.norm_eq_abs]

/-- The point with coordinates `(x, y)` relative to the triangle `T`. -/
noncomputable def bary (T : Triangle ℝ ℝ²) (x y : ℝ) : ℝ² :=
  (1 - x - y) • T.points 0 + x • T.points 1 + y • T.points 2

lemma sum_weights (x y : ℝ) : ∑ i, ![1 - x - y, x, y] i = 1 := by
  have h : ∑ i, ![1 - x - y, x, y] i = 1 - x - y + x + y := by simp [Fin.sum_univ_three]
  rw [h]
  ring

lemma bary_eq_comb (T : Triangle ℝ ℝ²) (x y : ℝ) :
    bary T x y = Finset.univ.affineCombination ℝ T.points ![1 - x - y, x, y] := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (sum_weights x y)]
  simp [bary, Fin.sum_univ_three]

lemma comb_eq_bary (T : Triangle ℝ ℝ²) (w : Fin 3 → ℝ) (hw : ∑ i, w i = 1) :
    Finset.univ.affineCombination ℝ T.points w = bary T (w 1) (w 2) := by
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
  have h0 : w 0 = 1 - w 1 - w 2 := by
    rw [Fin.sum_univ_three] at hw
    linarith
  simp [bary, Fin.sum_univ_three, h0]

lemma bary_inj (T : Triangle ℝ ℝ²) {x y x' y' : ℝ} (h : bary T x y = bary T x' y') :
    x = x' ∧ y = y' := by
  rw [bary_eq_comb, bary_eq_comb] at h
  have key := (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ T.points).1
    T.independent _ _ (sum_weights x y) (sum_weights x' y') h
  exact ⟨by simpa using congrFun key 1, by simpa using congrFun key 2⟩

lemma mem_closedInterior_iff (T : Triangle ℝ ℝ²) (p : ℝ²) :
    p ∈ T.closedInterior ↔ ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 ∧ p = bary T x y := by
  constructor
  · rintro ⟨w, hw, hI, rfl⟩
    have h0 : w 0 = 1 - w 1 - w 2 := by
      rw [Fin.sum_univ_three] at hw
      linarith
    have := (hI 0).1
    exact ⟨w 1, w 2, (hI 1).1, (hI 2).1, by linarith, comb_eq_bary T w hw⟩
  · rintro ⟨x, y, hx, hy, hxy, rfl⟩
    refine ⟨![1 - x - y, x, y], sum_weights x y, ?_, (bary_eq_comb T x y).symm⟩
    intro i
    fin_cases i
    · exact ⟨by simp; linarith, by simp; linarith⟩
    · exact ⟨by simpa using hx, by simp; linarith⟩
    · exact ⟨by simpa using hy, by simp; linarith⟩

lemma mem_interior_iff (T : Triangle ℝ ℝ²) (p : ℝ²) :
    p ∈ T.interior ↔ ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + y < 1 ∧ p = bary T x y := by
  constructor
  · rintro ⟨w, hw, hI, rfl⟩
    have h0 : w 0 = 1 - w 1 - w 2 := by
      rw [Fin.sum_univ_three] at hw
      linarith
    have := (hI 0).1
    exact ⟨w 1, w 2, (hI 1).1, (hI 2).1, by linarith, comb_eq_bary T w hw⟩
  · rintro ⟨x, y, hx, hy, hxy, rfl⟩
    refine ⟨![1 - x - y, x, y], sum_weights x y, ?_, (bary_eq_comb T x y).symm⟩
    intro i
    fin_cases i
    · exact ⟨by simp; linarith, by simp; linarith⟩
    · exact ⟨by simpa using hx, by simp; linarith⟩
    · exact ⟨by simpa using hy, by simp; linarith⟩

-- The pieces.

/-- The translation part of the map producing a piece. -/
noncomputable def cc (T : Triangle ℝ ℝ²) (r α β : ℝ) : ℝ² :=
  (1 - r) • T.points 0 + α • (T.points 1 - T.points 0) + β • (T.points 2 - T.points 0)

lemma scaleMap_bary (T : Triangle ℝ ℝ²) (r α β x y : ℝ) :
    scaleMap r (cc T r α β) (bary T x y) = bary T (r * x + α) (r * y + β) := by
  simp only [scaleMap_apply, cc, bary]
  module

/-- The piece: the image of `T` under `p ↦ r • p + cc T r α β`. -/
noncomputable def tri (T : Triangle ℝ ℝ²) (r α β : ℝ) (hr : r ≠ 0) : Triangle ℝ ℝ² :=
  T.map (scaleMap r (cc T r α β)) (scaleMap_injective hr _)

lemma mem_closedInterior_tri (T : Triangle ℝ ℝ²) (r α β : ℝ) (hr : r ≠ 0) (p : ℝ²) :
    p ∈ (tri T r α β hr).closedInterior ↔
      ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 ∧ p = bary T (r * x + α) (r * y + β) := by
  have himg : (tri T r α β hr).closedInterior = scaleMap r (cc T r α β) '' T.closedInterior :=
    Simplex.setInterior_map _ T (scaleMap_injective hr _)
  rw [himg]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := (mem_closedInterior_iff T q).1 hq
    exact ⟨x, y, hx, hy, hxy, scaleMap_bary T r α β x y⟩
  · rintro ⟨x, y, hx, hy, hxy, rfl⟩
    exact ⟨bary T x y, (mem_closedInterior_iff T _).2 ⟨x, y, hx, hy, hxy, rfl⟩,
      scaleMap_bary T r α β x y⟩

lemma mem_interior_tri (T : Triangle ℝ ℝ²) (r α β : ℝ) (hr : r ≠ 0) (p : ℝ²) :
    p ∈ (tri T r α β hr).interior ↔
      ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ x + y < 1 ∧ p = bary T (r * x + α) (r * y + β) := by
  have himg : (tri T r α β hr).interior = scaleMap r (cc T r α β) '' T.interior :=
    Simplex.setInterior_map _ T (scaleMap_injective hr _)
  rw [himg]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, y, hx, hy, hxy, rfl⟩ := (mem_interior_iff T q).1 hq
    exact ⟨x, y, hx, hy, hxy, scaleMap_bary T r α β x y⟩
  · rintro ⟨x, y, hx, hy, hxy, rfl⟩
    exact ⟨bary T x y, (mem_interior_iff T _).2 ⟨x, y, hx, hy, hxy, rfl⟩,
      scaleMap_bary T r α β x y⟩

lemma tri_congruent (T : Triangle ℝ ℝ²) {r r' : ℝ} (α β α' β' : ℝ) (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h : |r| = |r'|) : (tri T r α β hr).points ≅ (tri T r' α' β' hr').points := by
  intro i j
  simp only [tri, Simplex.map_points, Function.comp_apply, edist_dist, dist_scaleMap, h]

/-- The statement with the pieces indexed by pairs. -/
lemma cut_pairs {n : ℕ} (hn : n ≠ 0) (T : Triangle ℝ ℝ²) :
    ∃ Ts : Fin n × Fin n → Triangle ℝ ℝ²,
      (∀ i j, (Ts i).points ≅ (Ts j).points) ∧
        Pairwise (fun i j ↦ Disjoint (Ts i).interior (Ts j).interior) ∧
        ⋃ i, (Ts i).closedInterior = T.closedInterior := by
  refine ⟨fun k ↦ tri T (rr n k.1 k.2) (aa n k.1 k.2) (bb n k.1 k.2) (rr_ne_zero hn _ _),
    ?_, ?_, ?_⟩
  · intro k l
    exact tri_congruent T _ _ _ _ _ _ (by rw [abs_rr, abs_rr])
  · intro k l hkl
    rw [Set.disjoint_left]
    intro p hp hp'
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := (mem_interior_tri T _ _ _ _ p).1 hp
    obtain ⟨s', t', hs', ht', hst', hp''⟩ := (mem_interior_tri T _ _ _ _ _).1 hp'
    obtain ⟨e1, e2⟩ := bary_inj T hp''
    obtain ⟨d1, d2⟩ := disj hn hs ht hst hs' ht' hst' e1 e2
    exact hkl (Prod.ext (Fin.ext d1) (Fin.ext d2))
  · ext p
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := (mem_closedInterior_tri T _ _ _ _ p).1 hk
      obtain ⟨i1, i2, i3⟩ := inside hn k.1.isLt k.2.isLt hs ht hst
      exact (mem_closedInterior_iff T _).2 ⟨_, _, i1, i2, i3, rfl⟩
    · intro hp
      obtain ⟨x, y, hx, hy, hxy, rfl⟩ := (mem_closedInterior_iff T p).1 hp
      obtain ⟨a, b, ha, hb, s, t, hs, ht, hst, hx', hy'⟩ := cover hn hx hy hxy
      refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
      exact (mem_closedInterior_tri T _ _ _ _ _).2 ⟨s, t, hs, ht, hst, by rw [hx', hy']⟩

end Erdos633Sq

theorem OMA.solution : type_of% @Erdos633.IsCuttable.sq := by
  intro n T hn
  obtain ⟨Ts, h1, h2, h3⟩ := Erdos633Sq.cut_pairs hn T
  let e : Fin (n ^ 2) ≃ Fin n × Fin n := (finCongr (sq n)).trans finProdFinEquiv.symm
  refine ⟨fun k ↦ Ts (e k), fun i j ↦ h1 _ _, ?_, ?_⟩
  · intro i j hij
    exact h2 (fun h ↦ hij (e.injective h))
  · rw [← h3]
    exact e.surjective.iUnion_comp (fun k ↦ (Ts k).closedInterior)
