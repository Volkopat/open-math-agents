import OMAReductions.R_Erdos572_erdos_572_R1
import Mathlib

/-!
Step H2 of Erdős Problem 572: `ex(n; C₁₀) ≫ n ^ (6/5)` (Benson 1966; the graph used
here is the algebraic one of Wenger 1991, in five coordinates).

Points and lines are five-tuples over `ℤ/p`. A point `P` lies on a line `L` when
`P₂ + L₂ = P₁ L₁`, `P₃ + L₃ = P₁ L₂`, `P₄ + L₄ = P₁ L₃`, `P₅ + L₅ = P₁ L₄`.
If `L`, `M` pass through a point with first coordinate `a`, then
`L_{j+1} - M_{j+1} = a ^ j (L₁ - M₁)` for `j = 0, …, 4`. Around a ten-cycle
`A₁ L₁ A₂ L₂ … A₅ L₅` these differences telescope, so with `a_t` the first coordinate
of `A_t` and `y_t` the difference of the first coordinates of the two lines at `A_t`,
`∑ a_t ^ j y_t = 0` for `j = 0, …, 4`. Hence `∏_{t ≠ s} (a_s - a_t) · y_s = 0` for each
`s`. As `y_s ≠ 0` and cyclically consecutive `a`'s differ, each `a_s` equals `a_{s+2}`
or `a_{s-2}`, which is impossible on five indices. The graph has `2 p ^ 5` vertices and
`p ^ 6` edges; Bertrand's postulate and isolated vertices give every large `n`.
-/

open SimpleGraph

namespace OMA.Dec

section construction

variable (F : Type) [Field F]

/-- Five-tuples: the points, and the lines. -/
abbrev Tup : Type := F × F × F × F × F

/-- A point `P` lies on a line `L`. -/
def Inc (P L : Tup F) : Prop :=
  P.2.1 + L.2.1 = P.1 * L.1 ∧ P.2.2.1 + L.2.2.1 = P.1 * L.2.1 ∧
    P.2.2.2.1 + L.2.2.2.1 = P.1 * L.2.2.1 ∧ P.2.2.2.2 + L.2.2.2.2 = P.1 * L.2.2.2.1

/-- Adjacency on points, lines and `m` padding vertices. -/
def adj (m : ℕ) : (Tup F ⊕ Tup F) ⊕ Fin m → (Tup F ⊕ Tup F) ⊕ Fin m → Prop
  | Sum.inl (Sum.inl P), Sum.inl (Sum.inr L) => Inc F P L
  | Sum.inl (Sum.inr L), Sum.inl (Sum.inl P) => Inc F P L
  | _, _ => False

lemma adj_symm (m : ℕ) (u v : (Tup F ⊕ Tup F) ⊕ Fin m) (h : adj F m u v) :
    adj F m v u := by
  rcases u with (P | L) | i <;> rcases v with (P' | L') | j <;> simp_all [adj]

lemma adj_irrefl (m : ℕ) (u : (Tup F ⊕ Tup F) ⊕ Fin m) : ¬ adj F m u u := by
  rcases u with (P | L) | i <;> simp [adj]

/-- The incidence graph, padded with `m` isolated vertices. -/
def G (m : ℕ) : SimpleGraph ((Tup F ⊕ Tup F) ⊕ Fin m) :=
  SimpleGraph.fromRel (adj F m)

lemma G_adj (m : ℕ) (u v : (Tup F ⊕ Tup F) ⊕ Fin m) :
    (G F m).Adj u v ↔ adj F m u v := by
  unfold G
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact adj_symm F m _ _ h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    exact adj_irrefl F m _ h

lemma adj_point (m : ℕ) (P : Tup F) (v : (Tup F ⊕ Tup F) ⊕ Fin m)
    (h : (G F m).Adj (Sum.inl (Sum.inl P)) v) :
    ∃ L, v = Sum.inl (Sum.inr L) ∧ Inc F P L := by
  rw [G_adj] at h
  rcases v with (P' | L') | j
  · simp [adj] at h
  · exact ⟨L', rfl, by simpa [adj] using h⟩
  · simp [adj] at h

lemma adj_line (m : ℕ) (L : Tup F) (v : (Tup F ⊕ Tup F) ⊕ Fin m)
    (h : (G F m).Adj (Sum.inl (Sum.inr L)) v) :
    ∃ P, v = Sum.inl (Sum.inl P) ∧ Inc F P L := by
  rw [G_adj] at h
  rcases v with (P' | L') | j
  · exact ⟨P', rfl, by simpa [adj] using h⟩
  · simp [adj] at h
  · simp [adj] at h

/-- Two points on a common line with the same first coordinate coincide. -/
lemma point_eq (A B L : Tup F) (hA : Inc F A L) (hB : Inc F B L) (h : A.1 = B.1) :
    A = B := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := A
  obtain ⟨b1, b2, b3, b4, b5⟩ := B
  obtain ⟨l1, l2, l3, l4, l5⟩ := L
  simp only [Inc] at hA hB h
  subst h
  obtain ⟨hA1, hA2, hA3, hA4⟩ := hA
  obtain ⟨hB1, hB2, hB3, hB4⟩ := hB
  have h2 : a2 = b2 := by linear_combination hA1 - hB1
  have h3 : a3 = b3 := by linear_combination hA2 - hB2
  have h4 : a4 = b4 := by linear_combination hA3 - hB3
  have h5 : a5 = b5 := by linear_combination hA4 - hB4
  rw [h2, h3, h4, h5]

/-- For two lines through a point with first coordinate `a`, the differences of their
coordinates are `a ^ j` times the difference of their first coordinates. -/
lemma line_diff (A L M : Tup F) (hL : Inc F A L) (hM : Inc F A M) :
    L.2.1 - M.2.1 = A.1 * (L.1 - M.1) ∧ L.2.2.1 - M.2.2.1 = A.1 ^ 2 * (L.1 - M.1) ∧
      L.2.2.2.1 - M.2.2.2.1 = A.1 ^ 3 * (L.1 - M.1) ∧
      L.2.2.2.2 - M.2.2.2.2 = A.1 ^ 4 * (L.1 - M.1) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := A
  obtain ⟨l1, l2, l3, l4, l5⟩ := L
  obtain ⟨m1, m2, m3, m4, m5⟩ := M
  simp only [Inc] at hL hM ⊢
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hL
  obtain ⟨hM1, hM2, hM3, hM4⟩ := hM
  have h2 : l2 - m2 = a1 * (l1 - m1) := by linear_combination hL1 - hM1
  have h3 : l3 - m3 = a1 ^ 2 * (l1 - m1) := by linear_combination hL2 - hM2 + a1 * h2
  have h4 : l4 - m4 = a1 ^ 3 * (l1 - m1) := by linear_combination hL3 - hM3 + a1 * h3
  have h5 : l5 - m5 = a1 ^ 4 * (l1 - m1) := by linear_combination hL4 - hM4 + a1 * h4
  exact ⟨h2, h3, h4, h5⟩

/-- Two lines through a common point with the same first coordinate coincide. -/
lemma line_eq (A L M : Tup F) (hL : Inc F A L) (hM : Inc F A M) (h : L.1 = M.1) :
    L = M := by
  obtain ⟨h2, h3, h4, h5⟩ := line_diff F A L M hL hM
  obtain ⟨l1, l2, l3, l4, l5⟩ := L
  obtain ⟨m1, m2, m3, m4, m5⟩ := M
  simp only at h h2 h3 h4 h5
  subst h
  have e2 : l2 = m2 := by linear_combination h2
  have e3 : l3 = m3 := by linear_combination h3
  have e4 : l4 = m4 := by linear_combination h4
  have e5 : l5 = m5 := by linear_combination h5
  rw [e2, e3, e4, e5]

/-- The Vandermonde step: five weights `y_t`, none zero, at nodes `a_t` that differ
cyclically from their neighbours, cannot have vanishing power sums of degrees `0` to `4`. -/
lemma power_sums_false (a1 a2 a3 a4 a5 y1 y2 y3 y4 y5 : F)
    (S0 : y1 + y2 + y3 + y4 + y5 = 0)
    (S1 : a1 * y1 + a2 * y2 + a3 * y3 + a4 * y4 + a5 * y5 = 0)
    (S2 : a1 ^ 2 * y1 + a2 ^ 2 * y2 + a3 ^ 2 * y3 + a4 ^ 2 * y4 + a5 ^ 2 * y5 = 0)
    (S3 : a1 ^ 3 * y1 + a2 ^ 3 * y2 + a3 ^ 3 * y3 + a4 ^ 3 * y4 + a5 ^ 3 * y5 = 0)
    (S4 : a1 ^ 4 * y1 + a2 ^ 4 * y2 + a3 ^ 4 * y3 + a4 ^ 4 * y4 + a5 ^ 4 * y5 = 0)
    (h12 : a1 ≠ a2) (h23 : a2 ≠ a3) (h34 : a3 ≠ a4) (h45 : a4 ≠ a5) (h51 : a5 ≠ a1)
    (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0) (hy4 : y4 ≠ 0) (hy5 : y5 ≠ 0) : False := by
  have K1 : (a1 - a2) * (a1 - a5) * y1 * ((a1 - a3) * (a1 - a4)) = 0 := by
    linear_combination S4 - (a2 + a3 + a4 + a5) * S3
      + (a2 * a3 + a2 * a4 + a2 * a5 + a3 * a4 + a3 * a5 + a4 * a5) * S2
      - (a2 * a3 * a4 + a2 * a3 * a5 + a2 * a4 * a5 + a3 * a4 * a5) * S1
      + a2 * a3 * a4 * a5 * S0
  have K2 : (a2 - a3) * (a2 - a1) * y2 * ((a2 - a4) * (a2 - a5)) = 0 := by
    linear_combination S4 - (a1 + a3 + a4 + a5) * S3
      + (a1 * a3 + a1 * a4 + a1 * a5 + a3 * a4 + a3 * a5 + a4 * a5) * S2
      - (a1 * a3 * a4 + a1 * a3 * a5 + a1 * a4 * a5 + a3 * a4 * a5) * S1
      + a1 * a3 * a4 * a5 * S0
  have K3 : (a3 - a4) * (a3 - a2) * y3 * ((a3 - a5) * (a3 - a1)) = 0 := by
    linear_combination S4 - (a1 + a2 + a4 + a5) * S3
      + (a1 * a2 + a1 * a4 + a1 * a5 + a2 * a4 + a2 * a5 + a4 * a5) * S2
      - (a1 * a2 * a4 + a1 * a2 * a5 + a1 * a4 * a5 + a2 * a4 * a5) * S1
      + a1 * a2 * a4 * a5 * S0
  have K4 : (a4 - a5) * (a4 - a3) * y4 * ((a4 - a1) * (a4 - a2)) = 0 := by
    linear_combination S4 - (a1 + a2 + a3 + a5) * S3
      + (a1 * a2 + a1 * a3 + a1 * a5 + a2 * a3 + a2 * a5 + a3 * a5) * S2
      - (a1 * a2 * a3 + a1 * a2 * a5 + a1 * a3 * a5 + a2 * a3 * a5) * S1
      + a1 * a2 * a3 * a5 * S0
  have K5 : (a5 - a1) * (a5 - a4) * y5 * ((a5 - a2) * (a5 - a3)) = 0 := by
    linear_combination S4 - (a1 + a2 + a3 + a4) * S3
      + (a1 * a2 + a1 * a3 + a1 * a4 + a2 * a3 + a2 * a4 + a3 * a4) * S2
      - (a1 * a2 * a3 + a1 * a2 * a4 + a1 * a3 * a4 + a2 * a3 * a4) * S1
      + a1 * a2 * a3 * a4 * S0
  have n12 : a1 - a2 ≠ 0 := sub_ne_zero.mpr h12
  have n23 : a2 - a3 ≠ 0 := sub_ne_zero.mpr h23
  have n34 : a3 - a4 ≠ 0 := sub_ne_zero.mpr h34
  have n45 : a4 - a5 ≠ 0 := sub_ne_zero.mpr h45
  have n51 : a5 - a1 ≠ 0 := sub_ne_zero.mpr h51
  have n21 : a2 - a1 ≠ 0 := sub_ne_zero.mpr h12.symm
  have n32 : a3 - a2 ≠ 0 := sub_ne_zero.mpr h23.symm
  have n43 : a4 - a3 ≠ 0 := sub_ne_zero.mpr h34.symm
  have n54 : a5 - a4 ≠ 0 := sub_ne_zero.mpr h45.symm
  have n15 : a1 - a5 ≠ 0 := sub_ne_zero.mpr h51.symm
  have C1 : a1 = a3 ∨ a1 = a4 := by
    rcases mul_eq_zero.mp ((mul_eq_zero.mp K1).resolve_left
      (mul_ne_zero (mul_ne_zero n12 n15) hy1)) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have C2 : a2 = a4 ∨ a2 = a5 := by
    rcases mul_eq_zero.mp ((mul_eq_zero.mp K2).resolve_left
      (mul_ne_zero (mul_ne_zero n23 n21) hy2)) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have C3 : a3 = a5 ∨ a3 = a1 := by
    rcases mul_eq_zero.mp ((mul_eq_zero.mp K3).resolve_left
      (mul_ne_zero (mul_ne_zero n34 n32) hy3)) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have C4 : a4 = a1 ∨ a4 = a2 := by
    rcases mul_eq_zero.mp ((mul_eq_zero.mp K4).resolve_left
      (mul_ne_zero (mul_ne_zero n45 n43) hy4)) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  have C5 : a5 = a2 ∨ a5 = a3 := by
    rcases mul_eq_zero.mp ((mul_eq_zero.mp K5).resolve_left
      (mul_ne_zero (mul_ne_zero n51 n54) hy5)) with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  rcases C1 with c1 | c1 <;> rcases C2 with c2 | c2 <;> rcases C3 with c3 | c3 <;>
    rcases C4 with c4 | c4 <;> rcases C5 with c5 | c5 <;> subst_vars <;> simp_all

/-- There is no decagon `A₁ L₁ A₂ L₂ A₃ L₃ A₄ L₄ A₅ L₅` in the incidence structure. -/
lemma no_decagon (A1 A2 A3 A4 A5 L1 L2 L3 L4 L5 : Tup F)
    (hA12 : A1 ≠ A2) (hA23 : A2 ≠ A3) (hA34 : A3 ≠ A4) (hA45 : A4 ≠ A5) (hA51 : A5 ≠ A1)
    (hL12 : L1 ≠ L2) (hL23 : L2 ≠ L3) (hL34 : L3 ≠ L4) (hL45 : L4 ≠ L5) (hL51 : L5 ≠ L1)
    (i1 : Inc F A1 L1) (j1 : Inc F A2 L1) (i2 : Inc F A2 L2) (j2 : Inc F A3 L2)
    (i3 : Inc F A3 L3) (j3 : Inc F A4 L3) (i4 : Inc F A4 L4) (j4 : Inc F A5 L4)
    (i5 : Inc F A5 L5) (j5 : Inc F A1 L5) : False := by
  have a12 : A1.1 ≠ A2.1 := fun h => hA12 (point_eq F A1 A2 L1 i1 j1 h)
  have a23 : A2.1 ≠ A3.1 := fun h => hA23 (point_eq F A2 A3 L2 i2 j2 h)
  have a34 : A3.1 ≠ A4.1 := fun h => hA34 (point_eq F A3 A4 L3 i3 j3 h)
  have a45 : A4.1 ≠ A5.1 := fun h => hA45 (point_eq F A4 A5 L4 i4 j4 h)
  have a51 : A5.1 ≠ A1.1 := fun h => hA51 (point_eq F A5 A1 L5 i5 j5 h)
  have y1 : L1.1 - L5.1 ≠ 0 := fun h =>
    hL51 (line_eq F A1 L5 L1 j5 i1 (sub_eq_zero.mp h).symm)
  have y2 : L2.1 - L1.1 ≠ 0 := fun h =>
    hL12 (line_eq F A2 L1 L2 j1 i2 (sub_eq_zero.mp h).symm)
  have y3 : L3.1 - L2.1 ≠ 0 := fun h =>
    hL23 (line_eq F A3 L2 L3 j2 i3 (sub_eq_zero.mp h).symm)
  have y4 : L4.1 - L3.1 ≠ 0 := fun h =>
    hL34 (line_eq F A4 L3 L4 j3 i4 (sub_eq_zero.mp h).symm)
  have y5 : L5.1 - L4.1 ≠ 0 := fun h =>
    hL45 (line_eq F A5 L4 L5 j4 i5 (sub_eq_zero.mp h).symm)
  obtain ⟨d11, d12, d13, d14⟩ := line_diff F A1 L1 L5 i1 j5
  obtain ⟨d21, d22, d23, d24⟩ := line_diff F A2 L2 L1 i2 j1
  obtain ⟨d31, d32, d33, d34⟩ := line_diff F A3 L3 L2 i3 j2
  obtain ⟨d41, d42, d43, d44⟩ := line_diff F A4 L4 L3 i4 j3
  obtain ⟨d51, d52, d53, d54⟩ := line_diff F A5 L5 L4 i5 j4
  refine power_sums_false F A1.1 A2.1 A3.1 A4.1 A5.1 (L1.1 - L5.1) (L2.1 - L1.1)
    (L3.1 - L2.1) (L4.1 - L3.1) (L5.1 - L4.1) ?_ ?_ ?_ ?_ ?_ a12 a23 a34 a45 a51
    y1 y2 y3 y4 y5
  · ring
  · linear_combination -(d11 + d21 + d31 + d41 + d51)
  · linear_combination -(d12 + d22 + d32 + d42 + d52)
  · linear_combination -(d13 + d23 + d33 + d43 + d53)
  · linear_combination -(d14 + d24 + d34 + d44 + d54)

/-- No closed walk `u0 u1 … u9` of the graph starting at a point has consecutive points
distinct and consecutive lines distinct. -/
lemma no_cycle_from_point (m : ℕ) (A : Tup F)
    (u1 u2 u3 u4 u5 u6 u7 u8 u9 : (Tup F ⊕ Tup F) ⊕ Fin m)
    (h01 : (G F m).Adj (Sum.inl (Sum.inl A)) u1) (h12 : (G F m).Adj u1 u2)
    (h23 : (G F m).Adj u2 u3) (h34 : (G F m).Adj u3 u4) (h45 : (G F m).Adj u4 u5)
    (h56 : (G F m).Adj u5 u6) (h67 : (G F m).Adj u6 u7) (h78 : (G F m).Adj u7 u8)
    (h89 : (G F m).Adj u8 u9) (h90 : (G F m).Adj u9 (Sum.inl (Sum.inl A)))
    (n02 : Sum.inl (Sum.inl A) ≠ u2) (n24 : u2 ≠ u4) (n46 : u4 ≠ u6) (n68 : u6 ≠ u8)
    (n80 : u8 ≠ Sum.inl (Sum.inl A))
    (n13 : u1 ≠ u3) (n35 : u3 ≠ u5) (n57 : u5 ≠ u7) (n79 : u7 ≠ u9) (n91 : u9 ≠ u1) :
    False := by
  obtain ⟨L1, rfl, i1⟩ := adj_point F m A u1 h01
  obtain ⟨A2, rfl, j1⟩ := adj_line F m L1 u2 h12
  obtain ⟨L2, rfl, i2⟩ := adj_point F m A2 u3 h23
  obtain ⟨A3, rfl, j2⟩ := adj_line F m L2 u4 h34
  obtain ⟨L3, rfl, i3⟩ := adj_point F m A3 u5 h45
  obtain ⟨A4, rfl, j3⟩ := adj_line F m L3 u6 h56
  obtain ⟨L4, rfl, i4⟩ := adj_point F m A4 u7 h67
  obtain ⟨A5, rfl, j4⟩ := adj_line F m L4 u8 h78
  obtain ⟨L5, rfl, i5⟩ := adj_point F m A5 u9 h89
  obtain ⟨A', hA', j5⟩ := adj_line F m L5 _ h90
  have hAA : A = A' := Sum.inl_injective (Sum.inl_injective hA')
  subst hAA
  exact no_decagon F A A2 A3 A4 A5 L1 L2 L3 L4 L5
    (fun h => n02 (by rw [h])) (fun h => n24 (by rw [h])) (fun h => n46 (by rw [h]))
    (fun h => n68 (by rw [h])) (fun h => n80 (by rw [h]))
    (fun h => n13 (by rw [h])) (fun h => n35 (by rw [h])) (fun h => n57 (by rw [h]))
    (fun h => n79 (by rw [h])) (fun h => n91 (by rw [h]))
    i1 j1 i2 j2 i3 j3 i4 j4 i5 j5

/-- The padded incidence graph contains no ten-cycle. -/
lemma dec_free (m : ℕ) : (cycleGraph (2 * 5)).Free (G F m) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin (2 * 5), (cycleGraph (2 * 5)).Adj i j → (G F m).Adj (f i) (f j) :=
    fun i j h => f.toHom.map_adj h
  have hinj : ∀ i j : Fin (2 * 5), i ≠ j → f i ≠ f j := fun i j h h' => h (f.injective h')
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h23 := hadj 2 3 (by decide)
  have h34 := hadj 3 4 (by decide)
  have h45 := hadj 4 5 (by decide)
  have h56 := hadj 5 6 (by decide)
  have h67 := hadj 6 7 (by decide)
  have h78 := hadj 7 8 (by decide)
  have h89 := hadj 8 9 (by decide)
  have h90 := hadj 9 0 (by decide)
  rcases h0 : f 0 with (A | L) | i
  · rw [h0] at h01 h90
    exact no_cycle_from_point F m A (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)
      h01 h12 h23 h34 h45 h56 h67 h78 h89 h90
      (h0 ▸ hinj 0 2 (by decide)) (hinj 2 4 (by decide)) (hinj 4 6 (by decide))
      (hinj 6 8 (by decide)) (h0 ▸ hinj 8 0 (by decide))
      (hinj 1 3 (by decide)) (hinj 3 5 (by decide)) (hinj 5 7 (by decide))
      (hinj 7 9 (by decide)) (hinj 9 1 (by decide))
  · rw [h0] at h01 h90
    obtain ⟨A, h1, -⟩ := adj_line F m L (f 1) h01
    rw [h1] at h01 h12
    exact no_cycle_from_point F m A (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9)
      (Sum.inl (Sum.inr L)) h12 h23 h34 h45 h56 h67 h78 h89 h90 h01
      (h1 ▸ hinj 1 3 (by decide)) (hinj 3 5 (by decide)) (hinj 5 7 (by decide))
      (hinj 7 9 (by decide)) (h1 ▸ hinj 9 1 (by decide))
      (hinj 2 4 (by decide)) (hinj 4 6 (by decide)) (hinj 6 8 (by decide))
      (h0 ▸ hinj 8 0 (by decide)) (h0 ▸ hinj 0 2 (by decide))
  · rw [h0, G_adj] at h01
    simp [adj] at h01

/-- Every line carries one point for each first coordinate, so there are at least
`|F| ^ 6` edges. -/
lemma card_edges [Fintype F] (m : ℕ) [Fintype (G F m).edgeSet] :
    Fintype.card F ^ 6 ≤ (G F m).edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card]
  have hmem : ∀ tL : F × Tup F,
      s(Sum.inl (Sum.inl ((tL.1, tL.1 * tL.2.1 - tL.2.2.1, tL.1 * tL.2.2.1 - tL.2.2.2.1,
          tL.1 * tL.2.2.2.1 - tL.2.2.2.2.1, tL.1 * tL.2.2.2.2.1 - tL.2.2.2.2.2) : Tup F)),
        (Sum.inl (Sum.inr tL.2) : (Tup F ⊕ Tup F) ⊕ Fin m)) ∈ (G F m).edgeSet := by
    intro tL
    rw [SimpleGraph.mem_edgeSet, G_adj]
    show Inc F _ _
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  have hinj : Function.Injective (fun tL : F × Tup F =>
      (⟨_, hmem tL⟩ : (G F m).edgeSet)) := by
    intro tL tL' h
    have h' := congrArg Subtype.val h
    simp only [Sym2.eq_iff] at h'
    rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hL : tL.2 = tL'.2 := Sum.inr_injective (Sum.inl_injective h2)
      have hP := Sum.inl_injective (Sum.inl_injective h1)
      have ht : tL.1 = tL'.1 := (Prod.ext_iff.mp hP).1
      exact Prod.ext ht hL
    · exact absurd (Sum.inl_injective h1) (by simp)
  calc Fintype.card F ^ 6 = Fintype.card (F × Tup F) := by
        simp only [Fintype.card_prod]; ring
    _ ≤ Fintype.card (G F m).edgeSet := Fintype.card_le_of_injective _ hinj

end construction

/-- For a prime `p` and any `m`, a graph on `2 p ^ 5 + m` vertices without ten-cycles
can have `p ^ 6` edges. -/
lemma lower_bound (p m : ℕ) (hp : p.Prime) :
    p ^ 6 ≤ extremalNumber (2 * p ^ 5 + m) (cycleGraph (2 * 5)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h1 := card_edges (ZMod p) m
  rw [ZMod.card] at h1
  have h2 := card_edgeFinset_le_extremalNumber (dec_free (ZMod p) m)
  have hcard : Fintype.card ((Tup (ZMod p) ⊕ Tup (ZMod p)) ⊕ Fin m) = 2 * p ^ 5 + m := by
    simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card, Fintype.card_fin]; ring
  rw [hcard] at h2
  exact h1.trans h2

theorem main : ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in Filter.atTop,
    c * (n : ℝ) ^ (1 + 1 / (5 : ℝ)) ≤
      (extremalNumber n (cycleGraph (2 * 5)) : ℝ) := by
  refine ⟨(1 / 64 : ℝ) ^ (1 + 1 / (5 : ℝ)), by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 64] with n hn
  set r := Nat.findGreatest (fun r => 2 * r ^ 5 ≤ n) n with hr
  have hP2 : 2 * 2 ^ 5 ≤ n := by omega
  have hr2 : 2 ≤ r := Nat.le_findGreatest (by omega) hP2
  have hspec : 2 * r ^ 5 ≤ n :=
    Nat.findGreatest_spec (P := fun r => 2 * r ^ 5 ≤ n) (by omega : 2 ≤ n) hP2
  have hrn : r + 1 ≤ n := by
    have : r ^ 5 ≥ r := Nat.le_self_pow (by norm_num) r
    omega
  have hmax : n < 2 * (r + 1) ^ 5 := by
    have := Nat.findGreatest_is_greatest (P := fun r => 2 * r ^ 5 ≤ n)
      (Nat.lt_succ_self r) hrn
    exact not_le.mp this
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (r / 2) (by omega)
  have hpr : p ≤ r := by omega
  have hrp : r + 1 ≤ 2 * p := by omega
  have h2p : 2 * p ^ 5 ≤ n := (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpr 5)).trans hspec
  have h64 : n < 64 * p ^ 5 := by
    have h := Nat.pow_le_pow_left hrp 5
    have : (2 * p) ^ 5 = 32 * p ^ 5 := by ring
    omega
  have hlow := lower_bound p (n - 2 * p ^ 5) hp
  rw [Nat.add_sub_cancel' h2p] at hlow
  have hlowR : ((p : ℝ)) ^ 6 ≤ (extremalNumber n (cycleGraph (2 * 5)) : ℝ) := by
    exact_mod_cast hlow
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnp : (n : ℝ) / 64 ≤ (p : ℝ) ^ 5 := by
    have : (n : ℝ) < 64 * (p : ℝ) ^ 5 := by exact_mod_cast h64
    linarith
  have hpow : ((p : ℝ) ^ 5) ^ (1 + 1 / (5 : ℝ)) = (p : ℝ) ^ 6 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast]
    norm_num
  calc (1 / 64 : ℝ) ^ (1 + 1 / (5 : ℝ)) * (n : ℝ) ^ (1 + 1 / (5 : ℝ))
      = ((n : ℝ) / 64) ^ (1 + 1 / (5 : ℝ)) := by
        rw [← Real.mul_rpow (by norm_num) hn0]; congr 1; ring
    _ ≤ ((p : ℝ) ^ 5) ^ (1 + 1 / (5 : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hnp (by norm_num)
    _ = (p : ℝ) ^ 6 := hpow
    _ ≤ _ := hlowR

end OMA.Dec

theorem OMA.solution : OMA.R_Erdos572_erdos_572_R1.H2 := OMA.Dec.main
