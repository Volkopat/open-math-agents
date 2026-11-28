import OMAReductions.R_Erdos572_erdos_572_R1
import Mathlib

-- Step Erdos572.erdos_572.R1.H1: hypothesis H1 of reduction Erdos572.erdos_572.R1
-- Credit: @Mapika
-- H1 := ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in atTop,     c * (n : ℝ) ^ (1 + 1 / (3 : ℝ)) ≤       (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph (2 * 3)) : ℝ)

/-
ex(n; C_6) >> n^(4/3)  (Benson 1966; Singleton 1966).

Instead of generalized quadrangles this file uses the algebraic girth-eight graph in the form of
Wenger (1991) and Lazebnik-Ustimenko. Over F = ZMod p the points and the lines are the triples in
F^3, and a point P lies on a line L when
  P_2 + L_2 = P_1 * L_1   and   P_3 + L_3 = P_1 * L_2.
A line and a first coordinate determine the point, and a point and a first coordinate determine
the line. So in a hexagon A L B M C N the first coordinates a, b, c of A, B, C and x, y of L, M
satisfy a /= b, b /= c, x /= y, while eliminating the remaining coordinates from the twelve
incidence equations gives (a - b) (b - c) (x - y) = 0. Hence the incidence graph has no six-cycle.
It has 2 p^3 vertices and at least p^4 edges. For large n, Bertrand's postulate gives a prime p
with 2 p^3 <= n < 16 p^3; padding with isolated vertices gives a hexagon-free graph on n vertices
with p^4 >= (n / 16)^(4/3) edges.
-/

open SimpleGraph

namespace OMA.Hex

section construction

variable (F : Type) [Field F]

/-- A point `P` lies on a line `L`. -/
def Inc (P L : F × F × F) : Prop :=
  P.2.1 + L.2.1 = P.1 * L.1 ∧ P.2.2 + L.2.2 = P.1 * L.2.1

/-- Adjacency on points, lines and `m` padding vertices. -/
def adj (m : ℕ) : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m →
    ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m → Prop
  | Sum.inl (Sum.inl P), Sum.inl (Sum.inr L) => Inc F P L
  | Sum.inl (Sum.inr L), Sum.inl (Sum.inl P) => Inc F P L
  | _, _ => False

lemma adj_symm (m : ℕ) (u v : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m) (h : adj F m u v) :
    adj F m v u := by
  rcases u with (P | L) | i <;> rcases v with (P' | L') | j <;> simp_all [adj]

lemma adj_irrefl (m : ℕ) (u : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m) : ¬ adj F m u u := by
  rcases u with (P | L) | i <;> simp [adj]

/-- The incidence graph, padded with `m` isolated vertices. -/
def G (m : ℕ) : SimpleGraph (((F × F × F) ⊕ (F × F × F)) ⊕ Fin m) :=
  SimpleGraph.fromRel (adj F m)

lemma G_adj (m : ℕ) (u v : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m) :
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

lemma adj_point (m : ℕ) (P : F × F × F) (v : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m)
    (h : (G F m).Adj (Sum.inl (Sum.inl P)) v) :
    ∃ L, v = Sum.inl (Sum.inr L) ∧ Inc F P L := by
  rw [G_adj] at h
  rcases v with (P' | L') | j
  · simp [adj] at h
  · exact ⟨L', rfl, by simpa [adj] using h⟩
  · simp [adj] at h

lemma adj_line (m : ℕ) (L : F × F × F) (v : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m)
    (h : (G F m).Adj (Sum.inl (Sum.inr L)) v) :
    ∃ P, v = Sum.inl (Sum.inl P) ∧ Inc F P L := by
  rw [G_adj] at h
  rcases v with (P' | L') | j
  · exact ⟨P', rfl, by simpa [adj] using h⟩
  · simp [adj] at h
  · simp [adj] at h

/-- Two points on a common line with the same first coordinate coincide. -/
lemma point_eq (A B L : F × F × F) (hA : Inc F A L) (hB : Inc F B L) (h : A.1 = B.1) :
    A = B := by
  obtain ⟨a1, a2, a3⟩ := A
  obtain ⟨b1, b2, b3⟩ := B
  obtain ⟨l1, l2, l3⟩ := L
  simp only [Inc] at hA hB h
  subst h
  have h2 : a2 = b2 := by linear_combination hA.1 - hB.1
  have h3 : a3 = b3 := by linear_combination hA.2 - hB.2
  rw [h2, h3]

/-- Two lines through a common point with the same first coordinate coincide. -/
lemma line_eq (A L M : F × F × F) (hL : Inc F A L) (hM : Inc F A M) (h : L.1 = M.1) :
    L = M := by
  obtain ⟨a1, a2, a3⟩ := A
  obtain ⟨l1, l2, l3⟩ := L
  obtain ⟨m1, m2, m3⟩ := M
  simp only [Inc] at hL hM h
  subst h
  have h2 : l2 = m2 := by linear_combination hL.1 - hM.1
  have h3 : l3 = m3 := by linear_combination hL.2 - hM.2 + a1 * h2
  rw [h2, h3]

/-- There is no hexagon `A L B M C N` in the incidence structure. -/
lemma no_hexagon (A B C L M N : F × F × F) (hAB : A ≠ B) (hBC : B ≠ C) (hLM : L ≠ M)
    (hAL : Inc F A L) (hBL : Inc F B L) (hBM : Inc F B M) (hCM : Inc F C M)
    (hCN : Inc F C N) (hAN : Inc F A N) : False := by
  have hab : A.1 ≠ B.1 := fun h => hAB (point_eq F A B L hAL hBL h)
  have hbc : B.1 ≠ C.1 := fun h => hBC (point_eq F B C M hBM hCM h)
  have hxy : L.1 ≠ M.1 := fun h => hLM (line_eq F B L M hBL hBM h)
  obtain ⟨a, A2, A3⟩ := A
  obtain ⟨b, B2, B3⟩ := B
  obtain ⟨c, C2, C3⟩ := C
  obtain ⟨x, L2, L3⟩ := L
  obtain ⟨y, M2, M3⟩ := M
  obtain ⟨z, N2, N3⟩ := N
  simp only [Inc] at hAL hBL hBM hCM hCN hAN hab hbc hxy
  obtain ⟨e1, e2⟩ := hAL
  obtain ⟨e3, e4⟩ := hBL
  obtain ⟨e5, e6⟩ := hBM
  obtain ⟨e7, e8⟩ := hCM
  obtain ⟨e9, e10⟩ := hCN
  obtain ⟨e11, e12⟩ := hAN
  have E1 : (a - b) * x + (b - c) * y + (c - a) * z = 0 := by
    linear_combination -(e1 - e3 + e5 - e7 + e9 - e11)
  have T : (a - b) * L2 + (b - c) * M2 + (c - a) * N2 = 0 := by
    linear_combination -(e2 - e4 + e6 - e8 + e10 - e12)
  have key : (a - b) * (b - c) * (x - y) = 0 := by
    linear_combination T - (a - b) * e1 - (c - a) * e11 - (b - c) * (e5 - e3 + e1) - a * E1
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact hab (sub_eq_zero.mp h)
    · exact hbc (sub_eq_zero.mp h)
  · exact hxy (sub_eq_zero.mp h)

/-- No closed walk `u0 u1 u2 u3 u4 u5` of the graph starting at a point has
`u0 ≠ u2`, `u2 ≠ u4`, `u1 ≠ u3`. -/
lemma no_cycle_from_point (m : ℕ) (A : F × F × F)
    (u1 u2 u3 u4 u5 : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m)
    (h01 : (G F m).Adj (Sum.inl (Sum.inl A)) u1) (h12 : (G F m).Adj u1 u2)
    (h23 : (G F m).Adj u2 u3) (h34 : (G F m).Adj u3 u4) (h45 : (G F m).Adj u4 u5)
    (h50 : (G F m).Adj u5 (Sum.inl (Sum.inl A)))
    (n02 : Sum.inl (Sum.inl A) ≠ u2) (n24 : u2 ≠ u4) (n13 : u1 ≠ u3) : False := by
  obtain ⟨L, rfl, hAL⟩ := adj_point F m A u1 h01
  obtain ⟨B, rfl, hBL⟩ := adj_line F m L u2 h12
  obtain ⟨M, rfl, hBM⟩ := adj_point F m B u3 h23
  obtain ⟨C, rfl, hCM⟩ := adj_line F m M u4 h34
  obtain ⟨N, rfl, hCN⟩ := adj_point F m C u5 h45
  obtain ⟨A', hA', hAN⟩ := adj_line F m N _ h50
  have hAA : A = A' := Sum.inl_injective (Sum.inl_injective hA')
  subst hAA
  exact no_hexagon F A B C L M N (fun h => n02 (by rw [h])) (fun h => n24 (by rw [h]))
    (fun h => n13 (by rw [h])) hAL hBL hBM hCM hCN hAN

/-- The padded incidence graph contains no six-cycle. -/
lemma hex_free (m : ℕ) : (cycleGraph (2 * 3)).Free (G F m) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin (2 * 3), (cycleGraph (2 * 3)).Adj i j → (G F m).Adj (f i) (f j) :=
    fun i j h => f.toHom.map_adj h
  have hinj : ∀ i j : Fin (2 * 3), i ≠ j → f i ≠ f j := fun i j h h' => h (f.injective h')
  have h01 := hadj 0 1 (by decide)
  have h12 := hadj 1 2 (by decide)
  have h23 := hadj 2 3 (by decide)
  have h34 := hadj 3 4 (by decide)
  have h45 := hadj 4 5 (by decide)
  have h50 := hadj 5 0 (by decide)
  rcases h0 : f 0 with (A | L) | i
  · rw [h0] at h01 h50
    exact no_cycle_from_point F m A (f 1) (f 2) (f 3) (f 4) (f 5) h01 h12 h23 h34 h45 h50
      (h0 ▸ hinj 0 2 (by decide)) (hinj 2 4 (by decide)) (hinj 1 3 (by decide))
  · rw [h0] at h01 h50
    obtain ⟨A, h1, -⟩ := adj_line F m L (f 1) h01
    rw [h1] at h01 h12
    refine no_cycle_from_point F m A (f 2) (f 3) (f 4) (f 5) (Sum.inl (Sum.inr L))
      h12 h23 h34 h45 h50 h01
      (h1 ▸ hinj 1 3 (by decide)) (hinj 3 5 (by decide)) (hinj 2 4 (by decide))
  · rw [h0, G_adj] at h01
    simp [adj] at h01

/-- Every line carries one point for each first coordinate, so there are at least
`|F| ^ 4` edges. -/
lemma card_edges [Fintype F] (m : ℕ) [Fintype (G F m).edgeSet] :
    Fintype.card F ^ 4 ≤ (G F m).edgeFinset.card := by
  rw [SimpleGraph.edgeFinset_card]
  have hmem : ∀ tL : F × (F × F × F),
      s(Sum.inl (Sum.inl (tL.1, tL.1 * tL.2.1 - tL.2.2.1, tL.1 * tL.2.2.1 - tL.2.2.2)),
        (Sum.inl (Sum.inr tL.2) : ((F × F × F) ⊕ (F × F × F)) ⊕ Fin m)) ∈ (G F m).edgeSet := by
    intro tL
    rw [SimpleGraph.mem_edgeSet, G_adj]
    show Inc F _ _
    constructor <;> simp
  have hinj : Function.Injective (fun tL : F × (F × F × F) =>
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
  calc Fintype.card F ^ 4 = Fintype.card (F × (F × F × F)) := by
        simp only [Fintype.card_prod]; ring
    _ ≤ Fintype.card (G F m).edgeSet := Fintype.card_le_of_injective _ hinj

end construction

/-- For a prime `p` and any `m`, a hexagon-free graph on `2 p ^ 3 + m` vertices
has `p ^ 4` edges. -/
lemma lower_bound (p m : ℕ) (hp : p.Prime) :
    p ^ 4 ≤ extremalNumber (2 * p ^ 3 + m) (cycleGraph (2 * 3)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have h1 := card_edges (ZMod p) m
  rw [ZMod.card] at h1
  have h2 := card_edgeFinset_le_extremalNumber (hex_free (ZMod p) m)
  have hcard : Fintype.card (((ZMod p × ZMod p × ZMod p) ⊕ (ZMod p × ZMod p × ZMod p)) ⊕ Fin m)
      = 2 * p ^ 3 + m := by
    simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card, Fintype.card_fin]; ring
  rw [hcard] at h2
  exact h1.trans h2

theorem main : ∃ c > (0 : ℝ), ∀ᶠ (n : ℕ) in Filter.atTop,
    c * (n : ℝ) ^ (1 + 1 / (3 : ℝ)) ≤
      (extremalNumber n (cycleGraph (2 * 3)) : ℝ) := by
  refine ⟨(1 / 16 : ℝ) ^ (1 + 1 / (3 : ℝ)), by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 16] with n hn
  set r := Nat.findGreatest (fun r => 2 * r ^ 3 ≤ n) n with hr
  have hP2 : 2 * 2 ^ 3 ≤ n := by omega
  have hr2 : 2 ≤ r := Nat.le_findGreatest (by omega) hP2
  have hspec : 2 * r ^ 3 ≤ n :=
    Nat.findGreatest_spec (P := fun r => 2 * r ^ 3 ≤ n) (by omega : 2 ≤ n) hP2
  have hrn : r + 1 ≤ n := by
    have : r ^ 3 ≥ r := Nat.le_self_pow (by norm_num) r
    omega
  have hmax : n < 2 * (r + 1) ^ 3 := by
    have := Nat.findGreatest_is_greatest (P := fun r => 2 * r ^ 3 ≤ n)
      (Nat.lt_succ_self r) hrn
    exact not_le.mp this
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (r / 2) (by omega)
  have hpr : p ≤ r := by omega
  have hrp : r + 1 ≤ 2 * p := by omega
  have h2p : 2 * p ^ 3 ≤ n := (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpr 3)).trans hspec
  have h16 : n < 16 * p ^ 3 := by
    have h := Nat.pow_le_pow_left hrp 3
    have : (2 * p) ^ 3 = 8 * p ^ 3 := by ring
    omega
  have hlow := lower_bound p (n - 2 * p ^ 3) hp
  rw [Nat.add_sub_cancel' h2p] at hlow
  have hlowR : ((p : ℝ)) ^ 4 ≤ (extremalNumber n (cycleGraph (2 * 3)) : ℝ) := by
    exact_mod_cast hlow
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnp : (n : ℝ) / 16 ≤ (p : ℝ) ^ 3 := by
    have : (n : ℝ) < 16 * (p : ℝ) ^ 3 := by exact_mod_cast h16
    linarith
  have hpow : ((p : ℝ) ^ 3) ^ (1 + 1 / (3 : ℝ)) = (p : ℝ) ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0, ← Real.rpow_natCast]
    norm_num
  calc (1 / 16 : ℝ) ^ (1 + 1 / (3 : ℝ)) * (n : ℝ) ^ (1 + 1 / (3 : ℝ))
      = ((n : ℝ) / 16) ^ (1 + 1 / (3 : ℝ)) := by
        rw [← Real.mul_rpow (by norm_num) hn0]; congr 1; ring
    _ ≤ ((p : ℝ) ^ 3) ^ (1 + 1 / (3 : ℝ)) :=
        Real.rpow_le_rpow (by positivity) hnp (by norm_num)
    _ = (p : ℝ) ^ 4 := hpow
    _ ≤ _ := hlowR

end OMA.Hex

theorem OMA.solution : OMA.R_Erdos572_erdos_572_R1.H1 := by
  exact OMA.Hex.main
