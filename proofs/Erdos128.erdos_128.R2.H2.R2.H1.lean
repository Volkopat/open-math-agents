import OMAReductions.R_Erdos128_erdos_128_R2_H2_R2

-- Proof of Erdos128.erdos_128.R2.H2.R2.H1 (Luczak-Polcyn-Reiher 2024, arXiv:2406.10745,
-- Section 4: twin lemma 4.28 and attachment lemma 4.29 for maximal Vega subgraphs, then
-- Lemma 2.4), re-derived and formalized from scratch.
-- Builds on the reduction file of @therationalpie (prop_D, not_adj_both, Section 3 lemmas).

/-!
# E128H1 base: infrastructure for Luczak-Polcyn-Reiher Section 4 (Vega graphs)
Builds on the reduction file of @therationalpie (prop_D, not_adj_both).
-/

namespace E128H1

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2_H2_R2

/-- Simplified LPR Lemma 2.4: if every vertex q of a triangle-free G dominates the
image of the neighbourhood of some vertex of a target graph in which any two
non-adjacent vertices (also equal ones) have a common neighbour, then q maps to
such a vertex homomorphically. -/
theorem hom_of_dominate {V W : Type} {G : SimpleGraph V} (hcf : G.CliqueFree 3)
    (OA : W → W → Prop) (e : W → V)
    (hW : ∀ p p' : W, ¬ OA p p' → ∃ w, OA p w ∧ OA p' w)
    (φ : V → W) (hφ : ∀ q w, OA (φ q) w → G.Adj q (e w)) :
    ∀ x y, G.Adj x y → OA (φ x) (φ y) := by
  intro x y hxy
  by_contra h
  obtain ⟨w, h1, h2⟩ := hW _ _ h
  exact not_adj_both hcf hxy (hφ x w h1) (hφ y w h2)

def cnt12 (b : Fin 12 → Bool) : ℕ := (b 0).toNat + (b 1).toNat + (b 2).toNat + (b 3).toNat + (b 4).toNat + (b 5).toNat + (b 6).toNat + (b 7).toNat + (b 8).toNat + (b 9).toNat + (b 10).toNat + (b 11).toNat

theorem forall_fin12_bool {P : (Fin 12 → Bool) → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool, P ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11]) : ∀ b, P b := by
  intro b
  have hb : b = ![b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8, b 9, b 10, b 11] := by
    funext k; fin_cases k <;> rfl
  rw [hb]; exact h (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) (b 10) (b 11)

def beau_comb1_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 1) ||
    (b 5 && b 1) ||
    (b 5 && b 4) ||
    (b 9 && b 5) ||
    (b 1 && b 2) ||
    (b 6 && b 2) ||
    (b 6 && b 0) ||
    (b 9 && b 6) ||
    (b 2 && b 3) ||
    (b 7 && b 3) ||
    (b 7 && b 1) ||
    (b 9 && b 7) ||
    (b 3 && b 4) ||
    (b 8 && b 4) ||
    (b 8 && b 2) ||
    (b 9 && b 8) ||
    (b 4 && b 0) ||
    (b 10 && b 5) ||
    (b 10 && b 6) ||
    (b 11 && b 8) ||
    (b 11 && b 10) ||
    !(decide (5 ≤ cnt12 b)) || (b 0 && b 2 && b 5 && b 7 && b 11)

theorem beau_comb1_B_ok : ∀ b : Fin 12 → Bool, beau_comb1_B b = true :=
  forall_fin12_bool (by decide)

theorem beau_comb1 : ∀ b : Fin 12 → Bool,
    (b 0 && b 1) = false →
    (b 5 && b 1) = false →
    (b 5 && b 4) = false →
    (b 9 && b 5) = false →
    (b 1 && b 2) = false →
    (b 6 && b 2) = false →
    (b 6 && b 0) = false →
    (b 9 && b 6) = false →
    (b 2 && b 3) = false →
    (b 7 && b 3) = false →
    (b 7 && b 1) = false →
    (b 9 && b 7) = false →
    (b 3 && b 4) = false →
    (b 8 && b 4) = false →
    (b 8 && b 2) = false →
    (b 9 && b 8) = false →
    (b 4 && b 0) = false →
    (b 10 && b 5) = false →
    (b 10 && b 6) = false →
    (b 11 && b 8) = false →
    (b 11 && b 10) = false →
    5 ≤ cnt12 b → (b 0 && b 2 && b 5 && b 7 && b 11) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hc
  have h := beau_comb1_B_ok b
  simp only [beau_comb1_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def beau_comb2_B (b : Fin 12 → Bool) : Bool :=
    (b 4 && b 3) ||
    (b 8 && b 4) ||
    (b 5 && b 1) ||
    (b 5 && b 0) ||
    (b 8 && b 5) ||
    (b 1 && b 2) ||
    (b 2 && b 3) ||
    (b 6 && b 3) ||
    (b 6 && b 1) ||
    (b 8 && b 6) ||
    (b 3 && b 0) ||
    (b 7 && b 0) ||
    (b 7 && b 2) ||
    (b 8 && b 7) ||
    (b 9 && b 4) ||
    (b 9 && b 5) ||
    (b 10 && b 6) ||
    (b 10 && b 9) ||
    (b 11 && b 0) ||
    (b 11 && b 1) ||
    (b 11 && b 4) ||
    (b 11 && b 10) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem beau_comb2_B_ok : ∀ b : Fin 12 → Bool, beau_comb2_B b = true :=
  forall_fin12_bool (by decide)

theorem beau_comb2 : ∀ b : Fin 12 → Bool,
    (b 4 && b 3) = false →
    (b 8 && b 4) = false →
    (b 5 && b 1) = false →
    (b 5 && b 0) = false →
    (b 8 && b 5) = false →
    (b 1 && b 2) = false →
    (b 2 && b 3) = false →
    (b 6 && b 3) = false →
    (b 6 && b 1) = false →
    (b 8 && b 6) = false →
    (b 3 && b 0) = false →
    (b 7 && b 0) = false →
    (b 7 && b 2) = false →
    (b 8 && b 7) = false →
    (b 9 && b 4) = false →
    (b 9 && b 5) = false →
    (b 10 && b 6) = false →
    (b 10 && b 9) = false →
    (b 11 && b 0) = false →
    (b 11 && b 1) = false →
    (b 11 && b 4) = false →
    (b 11 && b 10) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 hc
  have h := beau_comb2_B_ok b
  simp only [beau_comb2_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

theorem D_bool12 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) (xs : Fin 12 → V) :
    ∃ y : V, 5 ≤ cnt12 (fun k => decide (G.Adj (xs k) y)) ∧
      ∀ i j : Fin 12, G.Adj (xs i) (xs j) →
        (decide (G.Adj (xs i) y) && decide (G.Adj (xs j) y)) = false := by
  obtain ⟨y, hy⟩ := prop_D G hmin 4 (by omega) xs
  refine ⟨y, ?_, ?_⟩
  · have hc : (Finset.univ.filter (fun i : Fin (3 * 4) => G.Adj (xs i) y)).card =
        cnt12 (fun k => decide (G.Adj (xs k) y)) := by
      rw [Finset.card_filter]
      simp only [cnt12, Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp only [Bool.toNat, decide_eq_true_eq, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Fin.reduceSucc, cond_eq_ite]
      omega
    omega
  · intro i j hij
    by_cases hi : G.Adj (xs i) y
    · have hj : ¬ G.Adj (xs j) y := fun hj => not_adj_both hcf hi.symm hj.symm hij
      simp [hi, hj]
    · simp [hi]

/-- LPR Lemma 4.4 (Beautiful lemma), in the Grötzsch labelling of H1:
outer 5-cycle v, shadows u (u k ~ v (k+1), v (k+4)), centre w.
If q is adjacent to u 0 and u 1 then q is adjacent to u 3. -/
theorem beautiful0 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3)
    (hmax : ∀ a b : V, a ≠ b → ¬ G.Adj a b → ∃ c : V, G.Adj a c ∧ G.Adj b c)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (v u : Fin 5 → V) (w : V)
    (hY : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
        G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i))
    (q : V) (hq0 : G.Adj q (u 0)) (hq1 : G.Adj q (u 1)) : G.Adj q (u 3) := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  by_contra hq3
  have hne : q ≠ u 3 := by
    rintro rfl
    exact not_adj_both hcf (gw 3) (gw 0) hq0
  obtain ⟨z, hqz, hz3'⟩ := hmax q (u 3) hne hq3
  have hzq : G.Adj z q := hqz.symm
  have hz3 : G.Adj z (u 3) := hz3'.symm
  obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(v 0), (v 1), (v 2), (v 3), (v 4), (u 0), (u 1), (u 2), (u 3), w, q, z]
  have h1 := beau_comb1 (fun k => decide (G.Adj (![(v 0), (v 1), (v 2), (v 3), (v 4), (u 0), (u 1), (u 2), (u 3), w, q, z] k) t)) (hp 0 1 (gv 0)) (hp 5 1 (gu1 0)) (hp 5 4 (gu4 0)) (hp 9 5 (gw 0)) (hp 1 2 (gv 1)) (hp 6 2 (gu1 1)) (hp 6 0 (gu4 1)) (hp 9 6 (gw 1)) (hp 2 3 (gv 2)) (hp 7 3 (gu1 2)) (hp 7 1 (gu4 2)) (hp 9 7 (gw 2)) (hp 3 4 (gv 3)) (hp 8 4 (gu1 3)) (hp 8 2 (gu4 3)) (hp 9 8 (gw 3)) (hp 4 0 (gv 4)) (hp 10 5 hq0) (hp 10 6 hq1) (hp 11 8 hz3) (hp 11 10 hzq) hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨⟨⟨⟨ht0, ht2⟩, htu0⟩, htu2⟩, htz⟩ := h1
  replace ht0 : G.Adj t (v 0) := ht0.symm
  replace ht2 : G.Adj t (v 2) := ht2.symm
  replace htu0 : G.Adj t (u 0) := htu0.symm
  replace htz : G.Adj t z := htz.symm
  obtain ⟨t2, hc, hp⟩ := D_bool12 G hcf hmin ![(v 0), (v 2), (v 3), (v 4), (u 0), (u 1), (u 3), (u 4), w, q, z, t]
  exact beau_comb2 (fun k => decide (G.Adj (![(v 0), (v 2), (v 3), (v 4), (u 0), (u 1), (u 3), (u 4), w, q, z, t] k) t2)) (hp 4 3 (gu4 0)) (hp 8 4 (gw 0)) (hp 5 1 (gu1 1)) (hp 5 0 (gu4 1)) (hp 8 5 (gw 1)) (hp 1 2 (gv 2)) (hp 2 3 (gv 3)) (hp 6 3 (gu1 3)) (hp 6 1 (gu4 3)) (hp 8 6 (gw 3)) (hp 3 0 (gv 4)) (hp 7 0 (gu1 4)) (hp 7 2 (gu4 4)) (hp 8 7 (gw 4)) (hp 9 4 hq0) (hp 9 5 hq1) (hp 10 6 hz3) (hp 10 9 hzq) (hp 11 0 ht0) (hp 11 1 ht2) (hp 11 4 htu0) (hp 11 10 htz) hc

def cnt9 (b : Fin 9 → Bool) : ℕ := (b 0).toNat + (b 1).toNat + (b 2).toNat + (b 3).toNat + (b 4).toNat + (b 5).toNat + (b 6).toNat + (b 7).toNat + (b 8).toNat

theorem forall_fin9_bool {P : (Fin 9 → Bool) → Prop}
    (h : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool, P ![b0, b1, b2, b3, b4, b5, b6, b7, b8]) : ∀ b, P b := by
  intro b
  have hb : b = ![b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8] := by
    funext k; fin_cases k <;> rfl
  rw [hb]; exact h (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8)

theorem D_bool9 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) (xs : Fin 9 → V) :
    ∃ y : V, 4 ≤ cnt9 (fun k => decide (G.Adj (xs k) y)) ∧
      ∀ i j : Fin 9, G.Adj (xs i) (xs j) →
        (decide (G.Adj (xs i) y) && decide (G.Adj (xs j) y)) = false := by
  obtain ⟨y, hy⟩ := prop_D G hmin 3 (by omega) xs
  refine ⟨y, ?_, ?_⟩
  · have hc : (Finset.univ.filter (fun i : Fin (3 * 3) => G.Adj (xs i) y)).card =
        cnt9 (fun k => decide (G.Adj (xs k) y)) := by
      rw [Finset.card_filter]
      simp only [cnt9, Fin.sum_univ_succ, Fin.sum_univ_zero]
      simp only [Bool.toNat, decide_eq_true_eq, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
        Fin.reduceSucc, cond_eq_ite]
      omega
    omega
  · intro i j hij
    by_cases hi : G.Adj (xs i) y
    · have hj : ¬ G.Adj (xs j) y := fun hj => not_adj_both hcf hi.symm hj.symm hij
      simp [hi, hj]
    · simp [hi]

def cube_c12_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 5) ||
    (b 0 && b 6) ||
    (b 0 && b 7) ||
    (b 1 && b 4) ||
    (b 1 && b 6) ||
    (b 1 && b 7) ||
    (b 2 && b 4) ||
    (b 2 && b 5) ||
    (b 2 && b 7) ||
    (b 3 && b 4) ||
    (b 3 && b 5) ||
    (b 3 && b 6) ||
    (b 8 && b 0) ||
    (b 9 && b 1) ||
    (b 10 && b 2) ||
    (b 11 && b 3) ||
    (b 8 && b 4) ||
    (b 9 && b 5) ||
    (b 10 && b 6) ||
    (b 11 && b 7) ||
    !(decide (5 ≤ cnt12 b)) || ((b 0 && b 4 && b 9 && b 10 && b 11) || (b 1 && b 5 && b 8 && b 10 && b 11) || (b 2 && b 6 && b 8 && b 9 && b 11) || (b 3 && b 7 && b 8 && b 9 && b 10))

theorem cube_c12_B_ok : ∀ b : Fin 12 → Bool, cube_c12_B b = true :=
  forall_fin12_bool (by decide)

theorem cube_c12 : ∀ b : Fin 12 → Bool,
    (b 0 && b 5) = false →
    (b 0 && b 6) = false →
    (b 0 && b 7) = false →
    (b 1 && b 4) = false →
    (b 1 && b 6) = false →
    (b 1 && b 7) = false →
    (b 2 && b 4) = false →
    (b 2 && b 5) = false →
    (b 2 && b 7) = false →
    (b 3 && b 4) = false →
    (b 3 && b 5) = false →
    (b 3 && b 6) = false →
    (b 8 && b 0) = false →
    (b 9 && b 1) = false →
    (b 10 && b 2) = false →
    (b 11 && b 3) = false →
    (b 8 && b 4) = false →
    (b 9 && b 5) = false →
    (b 10 && b 6) = false →
    (b 11 && b 7) = false →
    5 ≤ cnt12 b → ((b 0 && b 4 && b 9 && b 10 && b 11) || (b 1 && b 5 && b 8 && b 10 && b 11) || (b 2 && b 6 && b 8 && b 9 && b 11) || (b 3 && b 7 && b 8 && b 9 && b 10)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 hc
  have h := cube_c12_B_ok b
  simp only [cube_c12_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def cube_c9_B (b : Fin 9 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 0 && b 5) ||
    (b 1 && b 3) ||
    (b 1 && b 5) ||
    (b 2 && b 3) ||
    (b 2 && b 4) ||
    (b 6 && b 0) ||
    (b 7 && b 1) ||
    (b 8 && b 2) ||
    (b 6 && b 3) ||
    (b 7 && b 4) ||
    (b 8 && b 5) ||
    !(decide (4 ≤ cnt9 b)) || ((b 0 && b 3 && b 7 && b 8) || (b 1 && b 4 && b 6 && b 8) || (b 2 && b 5 && b 6 && b 7))

theorem cube_c9_B_ok : ∀ b : Fin 9 → Bool, cube_c9_B b = true :=
  forall_fin9_bool (by decide)

theorem cube_c9 : ∀ b : Fin 9 → Bool,
    (b 0 && b 4) = false →
    (b 0 && b 5) = false →
    (b 1 && b 3) = false →
    (b 1 && b 5) = false →
    (b 2 && b 3) = false →
    (b 2 && b 4) = false →
    (b 6 && b 0) = false →
    (b 7 && b 1) = false →
    (b 8 && b 2) = false →
    (b 6 && b 3) = false →
    (b 7 && b 4) = false →
    (b 8 && b 5) = false →
    4 ≤ cnt9 b → ((b 0 && b 3 && b 7 && b 8) || (b 1 && b 4 && b 6 && b 8) || (b 2 && b 5 && b 6 && b 7)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hc
  have h := cube_c9_B_ok b
  simp only [cube_c9_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def cube_cf_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 5) ||
    (b 0 && b 6) ||
    (b 0 && b 7) ||
    (b 1 && b 4) ||
    (b 1 && b 6) ||
    (b 1 && b 7) ||
    (b 2 && b 4) ||
    (b 2 && b 5) ||
    (b 2 && b 7) ||
    (b 3 && b 4) ||
    (b 3 && b 5) ||
    (b 3 && b 6) ||
    (b 8 && b 0) ||
    (b 8 && b 4) ||
    (b 9 && b 1) ||
    (b 9 && b 5) ||
    (b 10 && b 2) ||
    (b 10 && b 6) ||
    (b 11 && b 3) ||
    (b 11 && b 7) ||
    (b 10 && b 8) ||
    (b 10 && b 9) ||
    (b 11 && b 8) ||
    (b 11 && b 9) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem cube_cf_B_ok : ∀ b : Fin 12 → Bool, cube_cf_B b = true :=
  forall_fin12_bool (by decide)

theorem cube_cf : ∀ b : Fin 12 → Bool,
    (b 0 && b 5) = false →
    (b 0 && b 6) = false →
    (b 0 && b 7) = false →
    (b 1 && b 4) = false →
    (b 1 && b 6) = false →
    (b 1 && b 7) = false →
    (b 2 && b 4) = false →
    (b 2 && b 5) = false →
    (b 2 && b 7) = false →
    (b 3 && b 4) = false →
    (b 3 && b 5) = false →
    (b 3 && b 6) = false →
    (b 8 && b 0) = false →
    (b 8 && b 4) = false →
    (b 9 && b 1) = false →
    (b 9 && b 5) = false →
    (b 10 && b 2) = false →
    (b 10 && b 6) = false →
    (b 11 && b 3) = false →
    (b 11 && b 7) = false →
    (b 10 && b 8) = false →
    (b 10 && b 9) = false →
    (b 11 && b 8) = false →
    (b 11 && b 9) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 hc
  have h := cube_cf_B_ok b
  simp only [cube_cf_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

section Cube
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cube_final (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 4 → V) (s : V)
    (hab : ∀ i j : Fin 4, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i, G.Adj (c i) (a i)) (hbc : ∀ i, G.Adj (c i) (b i))
    (h30 : G.Adj (c 3) (c 0)) (h31 : G.Adj (c 3) (c 1))
    (hs0 : G.Adj s (c 0)) (hs1 : G.Adj s (c 1)) (hsa : G.Adj s (a 2)) (hsb : G.Adj s (b 2)) :
    False := by
  obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin
    ![a 0, a 1, a 2, a 3, b 0, b 1, b 2, b 3, c 0, c 1, s, c 3]
  exact cube_cf _ (hp 0 5 (hab 0 1 (by decide))) (hp 0 6 (hab 0 2 (by decide))) (hp 0 7 (hab 0 3 (by decide))) (hp 1 4 (hab 1 0 (by decide))) (hp 1 6 (hab 1 2 (by decide))) (hp 1 7 (hab 1 3 (by decide))) (hp 2 4 (hab 2 0 (by decide))) (hp 2 5 (hab 2 1 (by decide))) (hp 2 7 (hab 2 3 (by decide))) (hp 3 4 (hab 3 0 (by decide))) (hp 3 5 (hab 3 1 (by decide))) (hp 3 6 (hab 3 2 (by decide))) (hp 8 0 (hac 0)) (hp 8 4 (hbc 0)) (hp 9 1 (hac 1)) (hp 9 5 (hbc 1)) (hp 10 2 hsa) (hp 10 6 hsb) (hp 11 3 (hac 3)) (hp 11 7 (hbc 3)) (hp 10 8 hs0) (hp 10 9 hs1) (hp 11 8 h30) (hp 11 9 h31) hc

theorem cube_aux (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 4 → V)
    (hab : ∀ i j : Fin 4, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i, G.Adj (c i) (a i)) (hbc : ∀ i, G.Adj (c i) (b i))
    (h30 : G.Adj (c 3) (c 0)) (h31 : G.Adj (c 3) (c 1)) (h32 : G.Adj (c 3) (c 2)) : False := by
  obtain ⟨s, hc, hp⟩ := D_bool9 G hcf hmin ![a 0, a 1, a 2, b 0, b 1, b 2, c 0, c 1, c 2]
  have h := cube_c9 _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 6 0 (hac 0)) (hp 7 1 (hac 1)) (hp 8 2 (hac 2)) (hp 6 3 (hbc 0)) (hp 7 4 (hbc 1)) (hp 8 5 (hbc 2)) hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩)
  · -- s adj a0 b0 c1 c2 : swap 0 and 2
    let σ : Fin 4 → Fin 4 := ![2, 1, 0, 3]
    have hσ : Function.Injective σ := by decide
    exact cube_final G hcf hmin (fun i => a (σ i)) (fun i => b (σ i)) (fun i => c (σ i)) s
      (fun i j h => hab _ _ (hσ.ne h)) (fun i => hac (σ i)) (fun i => hbc (σ i))
      h32 h31 h4.symm h3.symm h1.symm h2.symm
  · -- s adj a1 b1 c0 c2 : swap 1 and 2
    let σ : Fin 4 → Fin 4 := ![0, 2, 1, 3]
    have hσ : Function.Injective σ := by decide
    exact cube_final G hcf hmin (fun i => a (σ i)) (fun i => b (σ i)) (fun i => c (σ i)) s
      (fun i j h => hab _ _ (hσ.ne h)) (fun i => hac (σ i)) (fun i => hbc (σ i))
      h30 h32 h3.symm h4.symm h1.symm h2.symm
  · exact cube_final G hcf hmin a b c s hab hac hbc h30 h31 h3.symm h4.symm h1.symm h2.symm

/-- LPR Lemma 4.2 (cube lemma): no induced cube Q_3 (as a_i b_j, i ≠ j) with a_i b_i non-edges. -/
theorem no_cube (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b : Fin 4 → V)
    (hab : ∀ i j : Fin 4, i ≠ j → G.Adj (a i) (b j)) (hn : ∀ i, ¬ G.Adj (a i) (b i)) : False := by
  have hne : ∀ i, a i ≠ b i := by
    intro i h
    have h1 := hab (i + 1) i (by fin_cases i <;> decide)
    have h2 := hab (i + 1) (i + 2) (by fin_cases i <;> decide)
    have h3 := hab i (i + 2) (by fin_cases i <;> decide)
    rw [← h] at h1
    exact not_adj_both hcf h1 h2 h3
  choose c hc using fun i => hmax (a i) (b i) (hne i) (hn i)
  have hac : ∀ i, G.Adj (c i) (a i) := fun i => (hc i).1.symm
  have hbc : ∀ i, G.Adj (c i) (b i) := fun i => (hc i).2.symm
  obtain ⟨t, hcnt, hp⟩ := D_bool12 G hcf hmin
    ![a 0, a 1, a 2, a 3, b 0, b 1, b 2, b 3, c 0, c 1, c 2, c 3]
  have h := cube_c12 _ (hp 0 5 (hab 0 1 (by decide))) (hp 0 6 (hab 0 2 (by decide))) (hp 0 7 (hab 0 3 (by decide))) (hp 1 4 (hab 1 0 (by decide))) (hp 1 6 (hab 1 2 (by decide))) (hp 1 7 (hab 1 3 (by decide))) (hp 2 4 (hab 2 0 (by decide))) (hp 2 5 (hab 2 1 (by decide))) (hp 2 7 (hab 2 3 (by decide))) (hp 3 4 (hab 3 0 (by decide))) (hp 3 5 (hab 3 1 (by decide))) (hp 3 6 (hab 3 2 (by decide))) (hp 8 0 (hac 0)) (hp 9 1 (hac 1)) (hp 10 2 (hac 2)) (hp 11 3 (hac 3)) (hp 8 4 (hbc 0)) (hp 9 5 (hbc 1)) (hp 10 6 (hbc 2)) (hp 11 7 (hbc 3)) hcnt
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with (((⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) |
    ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩)
  · -- t adj a0 b0 c1 c2 c3 ; sigma swaps 0 and 3
    let σ : Fin 4 → Fin 4 := ![3, 1, 2, 0]
    have hσ : Function.Injective σ := by decide
    refine cube_aux G hcf hmin (fun i => a (σ i)) (fun i => b (σ i)) ![c 3, c 1, c 2, t]
      (fun i j h => hab _ _ (hσ.ne h)) ?_ ?_ h5.symm h3.symm h4.symm
    · intro i; fin_cases i
      exacts [hac 3, hac 1, hac 2, h1.symm]
    · intro i; fin_cases i
      exacts [hbc 3, hbc 1, hbc 2, h2.symm]
  · let σ : Fin 4 → Fin 4 := ![0, 3, 2, 1]
    have hσ : Function.Injective σ := by decide
    refine cube_aux G hcf hmin (fun i => a (σ i)) (fun i => b (σ i)) ![c 0, c 3, c 2, t]
      (fun i j h => hab _ _ (hσ.ne h)) ?_ ?_ h3.symm h5.symm h4.symm
    · intro i; fin_cases i
      exacts [hac 0, hac 3, hac 2, h1.symm]
    · intro i; fin_cases i
      exacts [hbc 0, hbc 3, hbc 2, h2.symm]
  · let σ : Fin 4 → Fin 4 := ![0, 1, 3, 2]
    have hσ : Function.Injective σ := by decide
    refine cube_aux G hcf hmin (fun i => a (σ i)) (fun i => b (σ i)) ![c 0, c 1, c 3, t]
      (fun i j h => hab _ _ (hσ.ne h)) ?_ ?_ h3.symm h4.symm h5.symm
    · intro i; fin_cases i
      exacts [hac 0, hac 1, hac 3, h1.symm]
    · intro i; fin_cases i
      exacts [hbc 0, hbc 1, hbc 3, h2.symm]
  · refine cube_aux G hcf hmin a b ![c 0, c 1, c 2, t] hab ?_ ?_ h3.symm h4.symm h5.symm
    · intro i; fin_cases i
      exacts [hac 0, hac 1, hac 2, h1.symm]
    · intro i; fin_cases i
      exacts [hbc 0, hbc 1, hbc 2, h2.symm]

end Cube

def l43_cA_B (b : Fin 9 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 0 && b 5) ||
    (b 6 && b 0) ||
    (b 6 && b 3) ||
    (b 1 && b 3) ||
    (b 1 && b 5) ||
    (b 2 && b 3) ||
    (b 2 && b 4) ||
    (b 7 && b 2) ||
    (b 7 && b 5) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    !(decide (4 ≤ cnt9 b)) || ((b 0 && b 1 && b 2 && b 8) || (b 1 && b 4 && b 6 && b 7) || (b 3 && b 4 && b 5 && b 8))

theorem l43_cA_B_ok : ∀ b : Fin 9 → Bool, l43_cA_B b = true :=
  forall_fin9_bool (by decide)

theorem l43_cA : ∀ b : Fin 9 → Bool,
    (b 0 && b 4) = false →
    (b 0 && b 5) = false →
    (b 6 && b 0) = false →
    (b 6 && b 3) = false →
    (b 1 && b 3) = false →
    (b 1 && b 5) = false →
    (b 2 && b 3) = false →
    (b 2 && b 4) = false →
    (b 7 && b 2) = false →
    (b 7 && b 5) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    4 ≤ cnt9 b → ((b 0 && b 1 && b 2 && b 8) || (b 1 && b 4 && b 6 && b 7) || (b 3 && b 4 && b 5 && b 8)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hc
  have h := l43_cA_B_ok b
  simp only [l43_cA_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def l43_cB1_B (b : Fin 9 → Bool) : Bool :=
    (b 6 && b 2) ||
    (b 1 && b 2) ||
    (b 1 && b 0) ||
    (b 7 && b 1) ||
    (b 7 && b 8) ||
    (b 3 && b 2) ||
    (b 3 && b 8) ||
    (b 4 && b 3) ||
    (b 4 && b 0) ||
    (b 5 && b 6) ||
    (b 5 && b 4) ||
    !(decide (4 ≤ cnt9 b)) || ((b 0 && b 2 && b 5 && b 7) || (b 0 && b 2 && b 5 && b 8) || (b 0 && b 3 && b 5 && b 7) || (b 0 && b 3 && b 6 && b 7) || (b 1 && b 4 && b 6 && b 8))

theorem l43_cB1_B_ok : ∀ b : Fin 9 → Bool, l43_cB1_B b = true :=
  forall_fin9_bool (by decide)

theorem l43_cB1 : ∀ b : Fin 9 → Bool,
    (b 6 && b 2) = false →
    (b 1 && b 2) = false →
    (b 1 && b 0) = false →
    (b 7 && b 1) = false →
    (b 7 && b 8) = false →
    (b 3 && b 2) = false →
    (b 3 && b 8) = false →
    (b 4 && b 3) = false →
    (b 4 && b 0) = false →
    (b 5 && b 6) = false →
    (b 5 && b 4) = false →
    4 ≤ cnt9 b → ((b 0 && b 2 && b 5 && b 7) || (b 0 && b 2 && b 5 && b 8) || (b 0 && b 3 && b 5 && b 7) || (b 0 && b 3 && b 6 && b 7) || (b 1 && b 4 && b 6 && b 8)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hc
  have h := l43_cB1_B_ok b
  simp only [l43_cB1_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def l43_cF2_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 0 && b 5) ||
    (b 1 && b 3) ||
    (b 1 && b 5) ||
    (b 6 && b 1) ||
    (b 6 && b 4) ||
    (b 2 && b 3) ||
    (b 2 && b 4) ||
    (b 7 && b 2) ||
    (b 7 && b 5) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 7) ||
    (b 10 && b 0) ||
    (b 10 && b 1) ||
    (b 10 && b 2) ||
    (b 10 && b 9) ||
    (b 11 && b 5) ||
    (b 11 && b 3) ||
    (b 11 && b 9) ||
    (b 11 && b 6) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF2_B_ok : ∀ b : Fin 12 → Bool, l43_cF2_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF2 : ∀ b : Fin 12 → Bool,
    (b 0 && b 4) = false →
    (b 0 && b 5) = false →
    (b 1 && b 3) = false →
    (b 1 && b 5) = false →
    (b 6 && b 1) = false →
    (b 6 && b 4) = false →
    (b 2 && b 3) = false →
    (b 2 && b 4) = false →
    (b 7 && b 2) = false →
    (b 7 && b 5) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 7) = false →
    (b 10 && b 0) = false →
    (b 10 && b 1) = false →
    (b 10 && b 2) = false →
    (b 10 && b 9) = false →
    (b 11 && b 5) = false →
    (b 11 && b 3) = false →
    (b 11 && b 9) = false →
    (b 11 && b 6) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF2_B_ok b
  simp only [l43_cF2_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cF3_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 0 && b 5) ||
    (b 1 && b 3) ||
    (b 1 && b 5) ||
    (b 6 && b 1) ||
    (b 6 && b 4) ||
    (b 2 && b 3) ||
    (b 2 && b 4) ||
    (b 7 && b 2) ||
    (b 7 && b 5) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 7) ||
    (b 10 && b 0) ||
    (b 10 && b 1) ||
    (b 10 && b 2) ||
    (b 10 && b 9) ||
    (b 11 && b 5) ||
    (b 11 && b 3) ||
    (b 11 && b 9) ||
    (b 11 && b 4) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF3_B_ok : ∀ b : Fin 12 → Bool, l43_cF3_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF3 : ∀ b : Fin 12 → Bool,
    (b 0 && b 4) = false →
    (b 0 && b 5) = false →
    (b 1 && b 3) = false →
    (b 1 && b 5) = false →
    (b 6 && b 1) = false →
    (b 6 && b 4) = false →
    (b 2 && b 3) = false →
    (b 2 && b 4) = false →
    (b 7 && b 2) = false →
    (b 7 && b 5) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 7) = false →
    (b 10 && b 0) = false →
    (b 10 && b 1) = false →
    (b 10 && b 2) = false →
    (b 10 && b 9) = false →
    (b 11 && b 5) = false →
    (b 11 && b 3) = false →
    (b 11 && b 9) = false →
    (b 11 && b 4) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF3_B_ok b
  simp only [l43_cF3_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cF4_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 5 && b 0) ||
    (b 5 && b 3) ||
    (b 1 && b 3) ||
    (b 1 && b 4) ||
    (b 6 && b 1) ||
    (b 2 && b 3) ||
    (b 7 && b 2) ||
    (b 7 && b 4) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 5) ||
    (b 9 && b 7) ||
    (b 10 && b 0) ||
    (b 10 && b 1) ||
    (b 10 && b 2) ||
    (b 10 && b 9) ||
    (b 11 && b 4) ||
    (b 11 && b 2) ||
    (b 11 && b 9) ||
    (b 11 && b 6) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF4_B_ok : ∀ b : Fin 12 → Bool, l43_cF4_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF4 : ∀ b : Fin 12 → Bool,
    (b 0 && b 4) = false →
    (b 5 && b 0) = false →
    (b 5 && b 3) = false →
    (b 1 && b 3) = false →
    (b 1 && b 4) = false →
    (b 6 && b 1) = false →
    (b 2 && b 3) = false →
    (b 7 && b 2) = false →
    (b 7 && b 4) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 5) = false →
    (b 9 && b 7) = false →
    (b 10 && b 0) = false →
    (b 10 && b 1) = false →
    (b 10 && b 2) = false →
    (b 10 && b 9) = false →
    (b 11 && b 4) = false →
    (b 11 && b 2) = false →
    (b 11 && b 9) = false →
    (b 11 && b 6) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF4_B_ok b
  simp only [l43_cF4_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cF5_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 5 && b 0) ||
    (b 5 && b 3) ||
    (b 1 && b 3) ||
    (b 1 && b 4) ||
    (b 6 && b 1) ||
    (b 2 && b 3) ||
    (b 7 && b 2) ||
    (b 7 && b 4) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 5) ||
    (b 9 && b 7) ||
    (b 10 && b 0) ||
    (b 10 && b 1) ||
    (b 10 && b 2) ||
    (b 10 && b 9) ||
    (b 11 && b 4) ||
    (b 11 && b 2) ||
    (b 11 && b 5) ||
    (b 11 && b 6) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF5_B_ok : ∀ b : Fin 12 → Bool, l43_cF5_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF5 : ∀ b : Fin 12 → Bool,
    (b 0 && b 4) = false →
    (b 5 && b 0) = false →
    (b 5 && b 3) = false →
    (b 1 && b 3) = false →
    (b 1 && b 4) = false →
    (b 6 && b 1) = false →
    (b 2 && b 3) = false →
    (b 7 && b 2) = false →
    (b 7 && b 4) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 5) = false →
    (b 9 && b 7) = false →
    (b 10 && b 0) = false →
    (b 10 && b 1) = false →
    (b 10 && b 2) = false →
    (b 10 && b 9) = false →
    (b 11 && b 4) = false →
    (b 11 && b 2) = false →
    (b 11 && b 5) = false →
    (b 11 && b 6) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF5_B_ok b
  simp only [l43_cF5_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cB6_B (b : Fin 9 → Bool) : Bool :=
    (b 2 && b 1) ||
    (b 2 && b 3) ||
    (b 6 && b 2) ||
    (b 8 && b 3) ||
    (b 7 && b 8) ||
    (b 7 && b 1) ||
    (b 0 && b 1) ||
    (b 4 && b 0) ||
    (b 4 && b 3) ||
    (b 5 && b 6) ||
    (b 5 && b 4) ||
    !(decide (4 ≤ cnt9 b)) || ((b 0 && b 2 && b 5 && b 7) || (b 0 && b 2 && b 5 && b 8) || (b 0 && b 3 && b 5 && b 7) || (b 0 && b 3 && b 6 && b 7) || (b 1 && b 4 && b 6 && b 8))

theorem l43_cB6_B_ok : ∀ b : Fin 9 → Bool, l43_cB6_B b = true :=
  forall_fin9_bool (by decide)

theorem l43_cB6 : ∀ b : Fin 9 → Bool,
    (b 2 && b 1) = false →
    (b 2 && b 3) = false →
    (b 6 && b 2) = false →
    (b 8 && b 3) = false →
    (b 7 && b 8) = false →
    (b 7 && b 1) = false →
    (b 0 && b 1) = false →
    (b 4 && b 0) = false →
    (b 4 && b 3) = false →
    (b 5 && b 6) = false →
    (b 5 && b 4) = false →
    4 ≤ cnt9 b → ((b 0 && b 2 && b 5 && b 7) || (b 0 && b 2 && b 5 && b 8) || (b 0 && b 3 && b 5 && b 7) || (b 0 && b 3 && b 6 && b 7) || (b 1 && b 4 && b 6 && b 8)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hc
  have h := l43_cB6_B_ok b
  simp only [l43_cB6_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def l43_cF7_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 0 && b 5) ||
    (b 1 && b 3) ||
    (b 1 && b 5) ||
    (b 6 && b 1) ||
    (b 6 && b 4) ||
    (b 2 && b 3) ||
    (b 2 && b 4) ||
    (b 7 && b 2) ||
    (b 7 && b 5) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 7) ||
    (b 10 && b 3) ||
    (b 10 && b 4) ||
    (b 10 && b 5) ||
    (b 10 && b 9) ||
    (b 11 && b 2) ||
    (b 11 && b 0) ||
    (b 11 && b 9) ||
    (b 11 && b 6) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF7_B_ok : ∀ b : Fin 12 → Bool, l43_cF7_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF7 : ∀ b : Fin 12 → Bool,
    (b 0 && b 4) = false →
    (b 0 && b 5) = false →
    (b 1 && b 3) = false →
    (b 1 && b 5) = false →
    (b 6 && b 1) = false →
    (b 6 && b 4) = false →
    (b 2 && b 3) = false →
    (b 2 && b 4) = false →
    (b 7 && b 2) = false →
    (b 7 && b 5) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 7) = false →
    (b 10 && b 3) = false →
    (b 10 && b 4) = false →
    (b 10 && b 5) = false →
    (b 10 && b 9) = false →
    (b 11 && b 2) = false →
    (b 11 && b 0) = false →
    (b 11 && b 9) = false →
    (b 11 && b 6) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF7_B_ok b
  simp only [l43_cF7_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cF8_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 4) ||
    (b 0 && b 5) ||
    (b 1 && b 3) ||
    (b 1 && b 5) ||
    (b 6 && b 1) ||
    (b 6 && b 4) ||
    (b 2 && b 3) ||
    (b 2 && b 4) ||
    (b 7 && b 2) ||
    (b 7 && b 5) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 7) ||
    (b 10 && b 3) ||
    (b 10 && b 4) ||
    (b 10 && b 5) ||
    (b 10 && b 9) ||
    (b 11 && b 2) ||
    (b 11 && b 0) ||
    (b 11 && b 9) ||
    (b 11 && b 1) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF8_B_ok : ∀ b : Fin 12 → Bool, l43_cF8_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF8 : ∀ b : Fin 12 → Bool,
    (b 0 && b 4) = false →
    (b 0 && b 5) = false →
    (b 1 && b 3) = false →
    (b 1 && b 5) = false →
    (b 6 && b 1) = false →
    (b 6 && b 4) = false →
    (b 2 && b 3) = false →
    (b 2 && b 4) = false →
    (b 7 && b 2) = false →
    (b 7 && b 5) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 7) = false →
    (b 10 && b 3) = false →
    (b 10 && b 4) = false →
    (b 10 && b 5) = false →
    (b 10 && b 9) = false →
    (b 11 && b 2) = false →
    (b 11 && b 0) = false →
    (b 11 && b 9) = false →
    (b 11 && b 1) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF8_B_ok b
  simp only [l43_cF8_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cF9_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 3) ||
    (b 0 && b 4) ||
    (b 5 && b 0) ||
    (b 5 && b 2) ||
    (b 6 && b 3) ||
    (b 1 && b 2) ||
    (b 1 && b 3) ||
    (b 7 && b 1) ||
    (b 7 && b 4) ||
    (b 8 && b 0) ||
    (b 8 && b 2) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 5) ||
    (b 9 && b 7) ||
    (b 10 && b 2) ||
    (b 10 && b 3) ||
    (b 10 && b 4) ||
    (b 10 && b 9) ||
    (b 11 && b 1) ||
    (b 11 && b 4) ||
    (b 11 && b 9) ||
    (b 11 && b 6) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF9_B_ok : ∀ b : Fin 12 → Bool, l43_cF9_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF9 : ∀ b : Fin 12 → Bool,
    (b 0 && b 3) = false →
    (b 0 && b 4) = false →
    (b 5 && b 0) = false →
    (b 5 && b 2) = false →
    (b 6 && b 3) = false →
    (b 1 && b 2) = false →
    (b 1 && b 3) = false →
    (b 7 && b 1) = false →
    (b 7 && b 4) = false →
    (b 8 && b 0) = false →
    (b 8 && b 2) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 5) = false →
    (b 9 && b 7) = false →
    (b 10 && b 2) = false →
    (b 10 && b 3) = false →
    (b 10 && b 4) = false →
    (b 10 && b 9) = false →
    (b 11 && b 1) = false →
    (b 11 && b 4) = false →
    (b 11 && b 9) = false →
    (b 11 && b 6) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF9_B_ok b
  simp only [l43_cF9_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l43_cF10_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 3) ||
    (b 0 && b 4) ||
    (b 5 && b 0) ||
    (b 5 && b 2) ||
    (b 6 && b 3) ||
    (b 1 && b 2) ||
    (b 1 && b 3) ||
    (b 7 && b 1) ||
    (b 7 && b 4) ||
    (b 8 && b 0) ||
    (b 8 && b 2) ||
    (b 8 && b 6) ||
    (b 8 && b 7) ||
    (b 9 && b 5) ||
    (b 9 && b 7) ||
    (b 10 && b 2) ||
    (b 10 && b 3) ||
    (b 10 && b 4) ||
    (b 10 && b 9) ||
    (b 11 && b 1) ||
    (b 11 && b 4) ||
    (b 11 && b 5) ||
    (b 11 && b 6) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l43_cF10_B_ok : ∀ b : Fin 12 → Bool, l43_cF10_B b = true :=
  forall_fin12_bool (by decide)

theorem l43_cF10 : ∀ b : Fin 12 → Bool,
    (b 0 && b 3) = false →
    (b 0 && b 4) = false →
    (b 5 && b 0) = false →
    (b 5 && b 2) = false →
    (b 6 && b 3) = false →
    (b 1 && b 2) = false →
    (b 1 && b 3) = false →
    (b 7 && b 1) = false →
    (b 7 && b 4) = false →
    (b 8 && b 0) = false →
    (b 8 && b 2) = false →
    (b 8 && b 6) = false →
    (b 8 && b 7) = false →
    (b 9 && b 5) = false →
    (b 9 && b 7) = false →
    (b 10 && b 2) = false →
    (b 10 && b 3) = false →
    (b 10 && b 4) = false →
    (b 10 && b 9) = false →
    (b 11 && b 1) = false →
    (b 11 && b 4) = false →
    (b 11 && b 5) = false →
    (b 11 && b 6) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l43_cF10_B_ok b
  simp only [l43_cF10_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

section L43
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Core claim of LPR Lemma 4.3: configuration N (C6 a_i b_j plus c_i ~ a_i, b_i),
x0 common neighbour of a0 b0 c1 c2, c0 c2 non-adjacent: then a1 b1 c0 c2 have a
common neighbour. -/
theorem l43_claim0 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 3 → V)
    (hab : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i, G.Adj (c i) (a i)) (hbc : ∀ i, G.Adj (c i) (b i))
    (x0 : V) (hx_a0 : G.Adj x0 (a 0)) (hx_b0 : G.Adj x0 (b 0)) (hx_c1 : G.Adj x0 (c 1))
    (hx_c2 : G.Adj x0 (c 2)) (hn : ¬ G.Adj (c 0) (c 2)) :
    ∃ x, G.Adj x (a 1) ∧ G.Adj x (b 1) ∧ G.Adj x (c 0) ∧ G.Adj x (c 2) := by
  have hne : c 0 ≠ c 2 := by
    intro h
    have h1 := hbc 2
    rw [← h] at h1
    exact not_adj_both hcf (hac 0) h1 (hab 0 2 (by decide))
  obtain ⟨y, hy0', hy2'⟩ := hmax (c 0) (c 2) hne hn
  have hy0 : G.Adj y (c 0) := hy0'.symm
  have hy2 : G.Adj y (c 2) := hy2'.symm
  obtain ⟨z, hc, hp⟩ := D_bool9 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 1), (b 2), (c 0), (c 2), y]
  have h := l43_cA _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 6 0 (hac 0)) (hp 6 3 (hbc 0)) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 7 2 (hac 2)) (hp 7 5 (hbc 2)) (hp 8 6 hy0) (hp 8 7 hy2) hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩ | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩)
  · -- case a0 a1 a2 y
    have hz_a0 : G.Adj z (a 0) := hh1.symm
    have hz_a1 : G.Adj z (a 1) := hh2.symm
    have hz_a2 : G.Adj z (a 2) := hh3.symm
    have hz_y : G.Adj z y := hh4.symm
    obtain ⟨q, hc, hp⟩ := D_bool9 G hcf hmin ![(b 2), (a 1), (b 0), (a 2), (c 2), y, (c 0), (c 1), (b 1)]
    have h := l43_cB1 _ (hp 6 2 (hbc 0)) (hp 1 2 (hab 1 0 (by decide))) (hp 1 0 (hab 1 2 (by decide))) (hp 7 1 (hac 1)) (hp 7 8 (hbc 1)) (hp 3 2 (hab 2 0 (by decide))) (hp 3 8 (hab 2 1 (by decide))) (hp 4 3 (hac 2)) (hp 4 0 (hbc 2)) (hp 5 6 hy0) (hp 5 4 hy2) hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((((⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩ | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩)
    · -- case b2 b0 y c1
      have hq_b2 : G.Adj q (b 2) := hh1.symm
      have hq_b0 : G.Adj q (b 0) := hh2.symm
      have hq_y : G.Adj q y := hh3.symm
      have hq_c1 : G.Adj q (c 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 1), (b 2), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF2 _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 6 1 (hac 1)) (hp 6 4 (hbc 1)) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 7 2 (hac 2)) (hp 7 5 (hbc 2)) (hp 8 0 hx_a0) (hp 8 3 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 7 hy2) (hp 10 0 hz_a0) (hp 10 1 hz_a1) (hp 10 2 hz_a2) (hp 10 9 hz_y) (hp 11 5 hq_b2) (hp 11 3 hq_b0) (hp 11 9 hq_y) (hp 11 6 hq_c1) hc).elim
    · -- case b2 b0 y b1
      have hq_b2 : G.Adj q (b 2) := hh1.symm
      have hq_b0 : G.Adj q (b 0) := hh2.symm
      have hq_y : G.Adj q y := hh3.symm
      have hq_b1 : G.Adj q (b 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 1), (b 2), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF3 _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 6 1 (hac 1)) (hp 6 4 (hbc 1)) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 7 2 (hac 2)) (hp 7 5 (hbc 2)) (hp 8 0 hx_a0) (hp 8 3 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 7 hy2) (hp 10 0 hz_a0) (hp 10 1 hz_a1) (hp 10 2 hz_a2) (hp 10 9 hz_y) (hp 11 5 hq_b2) (hp 11 3 hq_b0) (hp 11 9 hq_y) (hp 11 4 hq_b1) hc).elim
    · -- case b2 a2 y c1
      have hq_b2 : G.Adj q (b 2) := hh1.symm
      have hq_a2 : G.Adj q (a 2) := hh2.symm
      have hq_y : G.Adj q y := hh3.symm
      have hq_c1 : G.Adj q (c 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 2), (c 0), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF4 _ (hp 0 4 (hab 0 2 (by decide))) (hp 5 0 (hac 0)) (hp 5 3 (hbc 0)) (hp 1 3 (hab 1 0 (by decide))) (hp 1 4 (hab 1 2 (by decide))) (hp 6 1 (hac 1)) (hp 2 3 (hab 2 0 (by decide))) (hp 7 2 (hac 2)) (hp 7 4 (hbc 2)) (hp 8 0 hx_a0) (hp 8 3 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 5 hy0) (hp 9 7 hy2) (hp 10 0 hz_a0) (hp 10 1 hz_a1) (hp 10 2 hz_a2) (hp 10 9 hz_y) (hp 11 4 hq_b2) (hp 11 2 hq_a2) (hp 11 9 hq_y) (hp 11 6 hq_c1) hc).elim
    · -- case b2 a2 c0 c1
      have hq_b2 : G.Adj q (b 2) := hh1.symm
      have hq_a2 : G.Adj q (a 2) := hh2.symm
      have hq_c0 : G.Adj q (c 0) := hh3.symm
      have hq_c1 : G.Adj q (c 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 2), (c 0), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF5 _ (hp 0 4 (hab 0 2 (by decide))) (hp 5 0 (hac 0)) (hp 5 3 (hbc 0)) (hp 1 3 (hab 1 0 (by decide))) (hp 1 4 (hab 1 2 (by decide))) (hp 6 1 (hac 1)) (hp 2 3 (hab 2 0 (by decide))) (hp 7 2 (hac 2)) (hp 7 4 (hbc 2)) (hp 8 0 hx_a0) (hp 8 3 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 5 hy0) (hp 9 7 hy2) (hp 10 0 hz_a0) (hp 10 1 hz_a1) (hp 10 2 hz_a2) (hp 10 9 hz_y) (hp 11 4 hq_b2) (hp 11 2 hq_a2) (hp 11 5 hq_c0) (hp 11 6 hq_c1) hc).elim
    · -- case a1 c2 c0 b1
      have hq_a1 : G.Adj q (a 1) := hh1.symm
      have hq_c2 : G.Adj q (c 2) := hh2.symm
      have hq_c0 : G.Adj q (c 0) := hh3.symm
      have hq_b1 : G.Adj q (b 1) := hh4.symm
      exact ⟨q, hq_a1, hq_b1, hq_c0, hq_c2⟩
  · -- case a1 b1 c0 c2
    have hz_a1 : G.Adj z (a 1) := hh1.symm
    have hz_b1 : G.Adj z (b 1) := hh2.symm
    have hz_c0 : G.Adj z (c 0) := hh3.symm
    have hz_c2 : G.Adj z (c 2) := hh4.symm
    exact ⟨z, hz_a1, hz_b1, hz_c0, hz_c2⟩
  · -- case b0 b1 b2 y
    have hz_b0 : G.Adj z (b 0) := hh1.symm
    have hz_b1 : G.Adj z (b 1) := hh2.symm
    have hz_b2 : G.Adj z (b 2) := hh3.symm
    have hz_y : G.Adj z y := hh4.symm
    obtain ⟨q, hc, hp⟩ := D_bool9 G hcf hmin ![(a 2), (b 1), (a 0), (b 2), (c 2), y, (c 0), (c 1), (a 1)]
    have h := l43_cB6 _ (hp 2 1 (hab 0 1 (by decide))) (hp 2 3 (hab 0 2 (by decide))) (hp 6 2 (hac 0)) (hp 8 3 (hab 1 2 (by decide))) (hp 7 8 (hac 1)) (hp 7 1 (hbc 1)) (hp 0 1 (hab 2 1 (by decide))) (hp 4 0 (hac 2)) (hp 4 3 (hbc 2)) (hp 5 6 hy0) (hp 5 4 hy2) hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((((⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩ | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩) | ⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩)
    · -- case a2 a0 y c1
      have hq_a2 : G.Adj q (a 2) := hh1.symm
      have hq_a0 : G.Adj q (a 0) := hh2.symm
      have hq_y : G.Adj q y := hh3.symm
      have hq_c1 : G.Adj q (c 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 1), (b 2), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF7 _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 6 1 (hac 1)) (hp 6 4 (hbc 1)) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 7 2 (hac 2)) (hp 7 5 (hbc 2)) (hp 8 0 hx_a0) (hp 8 3 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 7 hy2) (hp 10 3 hz_b0) (hp 10 4 hz_b1) (hp 10 5 hz_b2) (hp 10 9 hz_y) (hp 11 2 hq_a2) (hp 11 0 hq_a0) (hp 11 9 hq_y) (hp 11 6 hq_c1) hc).elim
    · -- case a2 a0 y a1
      have hq_a2 : G.Adj q (a 2) := hh1.symm
      have hq_a0 : G.Adj q (a 0) := hh2.symm
      have hq_y : G.Adj q y := hh3.symm
      have hq_a1 : G.Adj q (a 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 1), (a 2), (b 0), (b 1), (b 2), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF8 _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 6 1 (hac 1)) (hp 6 4 (hbc 1)) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 7 2 (hac 2)) (hp 7 5 (hbc 2)) (hp 8 0 hx_a0) (hp 8 3 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 7 hy2) (hp 10 3 hz_b0) (hp 10 4 hz_b1) (hp 10 5 hz_b2) (hp 10 9 hz_y) (hp 11 2 hq_a2) (hp 11 0 hq_a0) (hp 11 9 hq_y) (hp 11 1 hq_a1) hc).elim
    · -- case a2 b2 y c1
      have hq_a2 : G.Adj q (a 2) := hh1.symm
      have hq_b2 : G.Adj q (b 2) := hh2.symm
      have hq_y : G.Adj q y := hh3.symm
      have hq_c1 : G.Adj q (c 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 2), (b 0), (b 1), (b 2), (c 0), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF9 _ (hp 0 3 (hab 0 1 (by decide))) (hp 0 4 (hab 0 2 (by decide))) (hp 5 0 (hac 0)) (hp 5 2 (hbc 0)) (hp 6 3 (hbc 1)) (hp 1 2 (hab 2 0 (by decide))) (hp 1 3 (hab 2 1 (by decide))) (hp 7 1 (hac 2)) (hp 7 4 (hbc 2)) (hp 8 0 hx_a0) (hp 8 2 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 5 hy0) (hp 9 7 hy2) (hp 10 2 hz_b0) (hp 10 3 hz_b1) (hp 10 4 hz_b2) (hp 10 9 hz_y) (hp 11 1 hq_a2) (hp 11 4 hq_b2) (hp 11 9 hq_y) (hp 11 6 hq_c1) hc).elim
    · -- case a2 b2 c0 c1
      have hq_a2 : G.Adj q (a 2) := hh1.symm
      have hq_b2 : G.Adj q (b 2) := hh2.symm
      have hq_c0 : G.Adj q (c 0) := hh3.symm
      have hq_c1 : G.Adj q (c 1) := hh4.symm
      obtain ⟨t, hc, hp⟩ := D_bool12 G hcf hmin ![(a 0), (a 2), (b 0), (b 1), (b 2), (c 0), (c 1), (c 2), x0, y, z, q]
      exact (l43_cF10 _ (hp 0 3 (hab 0 1 (by decide))) (hp 0 4 (hab 0 2 (by decide))) (hp 5 0 (hac 0)) (hp 5 2 (hbc 0)) (hp 6 3 (hbc 1)) (hp 1 2 (hab 2 0 (by decide))) (hp 1 3 (hab 2 1 (by decide))) (hp 7 1 (hac 2)) (hp 7 4 (hbc 2)) (hp 8 0 hx_a0) (hp 8 2 hx_b0) (hp 8 6 hx_c1) (hp 8 7 hx_c2) (hp 9 5 hy0) (hp 9 7 hy2) (hp 10 2 hz_b0) (hp 10 3 hz_b1) (hp 10 4 hz_b2) (hp 10 9 hz_y) (hp 11 1 hq_a2) (hp 11 4 hq_b2) (hp 11 5 hq_c0) (hp 11 6 hq_c1) hc).elim
    · -- case b1 c2 c0 a1
      have hq_b1 : G.Adj q (b 1) := hh1.symm
      have hq_c2 : G.Adj q (c 2) := hh2.symm
      have hq_c0 : G.Adj q (c 0) := hh3.symm
      have hq_a1 : G.Adj q (a 1) := hh4.symm
      exact ⟨q, hq_a1, hq_b1, hq_c0, hq_c2⟩

end L43


section L43b
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem l43_D3 (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 3 → V)
    (hab : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i, G.Adj (c i) (a i)) (hbc : ∀ i, G.Adj (c i) (b i)) :
    ∃ k x, G.Adj x (a k) ∧ G.Adj x (b k) ∧ ∀ m, m ≠ k → G.Adj x (c m) := by
  obtain ⟨x, hc, hp⟩ := D_bool9 G hcf hmin ![a 0, a 1, a 2, b 0, b 1, b 2, c 0, c 1, c 2]
  have h := cube_c9 _ (hp 0 4 (hab 0 1 (by decide))) (hp 0 5 (hab 0 2 (by decide))) (hp 1 3 (hab 1 0 (by decide))) (hp 1 5 (hab 1 2 (by decide))) (hp 2 3 (hab 2 0 (by decide))) (hp 2 4 (hab 2 1 (by decide))) (hp 6 0 (hac 0)) (hp 7 1 (hac 1)) (hp 8 2 (hac 2)) (hp 6 3 (hbc 0)) (hp 7 4 (hbc 1)) (hp 8 5 (hbc 2)) hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ((⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩) | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩)
  · refine ⟨0, x, h1.symm, h2.symm, fun m hm => ?_⟩
    fin_cases m
    · exact absurd rfl hm
    · exact h3.symm
    · exact h4.symm
  · refine ⟨1, x, h1.symm, h2.symm, fun m hm => ?_⟩
    fin_cases m
    · exact h3.symm
    · exact absurd rfl hm
    · exact h4.symm
  · refine ⟨2, x, h1.symm, h2.symm, fun m hm => ?_⟩
    fin_cases m
    · exact h3.symm
    · exact h4.symm
    · exact absurd rfl hm

theorem l43_perm (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 3 → V)
    (hab : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i, G.Adj (c i) (a i)) (hbc : ∀ i, G.Adj (c i) (b i))
    (p r s : Fin 3) (hpr : p ≠ r) (hrs : r ≠ s) (hps : p ≠ s)
    (x0 : V) (h1 : G.Adj x0 (a p)) (h2 : G.Adj x0 (b p)) (h3 : G.Adj x0 (c r))
    (h4 : G.Adj x0 (c s)) (hn : ¬ G.Adj (c p) (c s)) :
    ∃ x, G.Adj x (a r) ∧ G.Adj x (b r) ∧ G.Adj x (c p) ∧ G.Adj x (c s) := by
  let σ : Fin 3 → Fin 3 := ![p, r, s]
  have hσ : ∀ i j : Fin 3, i ≠ j → σ i ≠ σ j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact hpr | exact hpr.symm | exact hrs | exact hrs.symm | exact hps | exact hps.symm
  exact l43_claim0 G hcf hmax hmin (fun i => a (σ i)) (fun i => b (σ i)) (fun i => c (σ i))
    (fun i j h => hab _ _ (hσ i j h)) (fun i => hac (σ i)) (fun i => hbc (σ i))
    x0 h1 h2 h3 h4 hn

/-- LPR Lemma 4.3. For the 9-vertex configuration N (a_i b_j for i ≠ j, c_i ~ a_i, b_i)
and distinct i j k: either c_j c_k is an edge or a_i, b_i, c_j, c_k have a common neighbour. -/
theorem lemma43 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (a b c : Fin 3 → V)
    (hab : ∀ i j : Fin 3, i ≠ j → G.Adj (a i) (b j))
    (hac : ∀ i, G.Adj (c i) (a i)) (hbc : ∀ i, G.Adj (c i) (b i))
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    G.Adj (c j) (c k) ∨
      ∃ x, G.Adj x (a i) ∧ G.Adj x (b i) ∧ G.Adj x (c j) ∧ G.Adj x (c k) := by
  obtain ⟨k0, x, h1, h2, h3⟩ := l43_D3 G hcf hmin a b c hab hac hbc
  by_cases hcc : G.Adj (c j) (c k)
  · exact Or.inl hcc
  right
  have hv : k0.val = i.val ∨ k0.val = j.val ∨ k0.val = k.val := by
    have := Fin.val_ne_of_ne hij; have := Fin.val_ne_of_ne hjk; have := Fin.val_ne_of_ne hik
    have := k0.isLt; have := i.isLt; have := j.isLt; have := k.isLt
    omega
  rcases hv with hv | hv | hv
  · have e : k0 = i := Fin.ext hv
    subst e
    exact ⟨x, h1, h2, h3 j (Ne.symm hij), h3 k (Ne.symm hik)⟩
  · have e : k0 = j := Fin.ext hv
    subst e
    exact l43_perm G hcf hmax hmin a b c hab hac hbc k0 i k (Ne.symm hij) hik hjk
      x h1 h2 (h3 i hij) (h3 k (Ne.symm hjk)) hcc
  · have e : k0 = k := Fin.ext hv
    subst e
    obtain ⟨y, g1, g2, g3, g4⟩ := l43_perm G hcf hmax hmin a b c hab hac hbc k0 i j
      (Ne.symm hik) hij (Ne.symm hjk) x h1 h2 (h3 i hik) (h3 j hjk) (fun h => hcc h.symm)
    exact ⟨y, g1, g2, g4, g3⟩

end L43b


section Rot
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A (not necessarily injective) Grötzsch configuration in the labelling of H1. -/
def IsGr (v u : Fin 5 → V) (w : V) : Prop :=
  ∀ i : Fin 5, G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
    G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i)

theorem IsGr.rot {v u : Fin 5 → V} {w : V} (h : IsGr G v u w) (k : Fin 5) :
    IsGr G (fun i => v (i + k)) (fun i => u (i + k)) w := by
  intro i
  have e1 : i + k + 1 = i + 1 + k := add_right_comm i k 1
  have e4 : i + k + 4 = i + 4 + k := add_right_comm i k 4
  obtain ⟨h1, h2, h3, h4⟩ := h (i + k)
  rw [e1] at h1 h2
  rw [e4] at h3
  exact ⟨h1, h2, h3, h4⟩

/-- Replacing a shadow vertex u k by a twin u' (adjacent to v (k+1), v (k+4), w) keeps a copy. -/
theorem IsGr.replace_u {v u : Fin 5 → V} {w : V} (h : IsGr G v u w) (k : Fin 5) (u' : V)
    (h1 : G.Adj u' (v (k + 1))) (h4 : G.Adj u' (v (k + 4))) (hw : G.Adj w u') :
    IsGr G v (Function.update u k u') w := by
  intro i
  by_cases hik : i = k
  · subst hik
    simp only [Function.update_self]
    exact ⟨(h i).1, h1, h4, hw⟩
  · simp only [Function.update_of_ne hik]
    exact h i

/-- LPR Lemma 4.4 (Beautiful lemma), general index. -/
theorem beautiful (hcf : G.CliqueFree 3)
    (hmax : ∀ a b : V, a ≠ b → ¬ G.Adj a b → ∃ c : V, G.Adj a c ∧ G.Adj b c)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (k : Fin 5)
    (q : V) (hq0 : G.Adj q (u k)) (hq1 : G.Adj q (u (k + 1))) : G.Adj q (u (k + 3)) := by
  have hR := hY.rot G k
  have e0 : (0 : Fin 5) + k = k := zero_add k
  have e1 : (1 : Fin 5) + k = k + 1 := add_comm 1 k
  have e3 : (3 : Fin 5) + k = k + 3 := add_comm 3 k
  have := beautiful0 G hcf hmax hmin (fun i => v (i + k)) (fun i => u (i + k)) w hR q
    (by simp only [e0]; exact hq0) (by simp only [e1]; exact hq1)
  simpa only [e3] using this

/-- LPR Lemma 4.5: (Υ, c a)-twin property. A twin u' of u k and a vertex c' adjacent to
u (k+2), u (k+3) are adjacent. -/
theorem twin_c_u (hcf : G.CliqueFree 3)
    (hmax : ∀ a b : V, a ≠ b → ¬ G.Adj a b → ∃ c : V, G.Adj a c ∧ G.Adj b c)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (k : Fin 5) (u' : V)
    (h1 : G.Adj u' (v (k + 1))) (h4 : G.Adj u' (v (k + 4))) (hw : G.Adj w u')
    (c' : V) (hc2 : G.Adj c' (u (k + 2))) (hc3 : G.Adj c' (u (k + 3))) : G.Adj c' u' := by
  have hR := hY.replace_u G k u' h1 h4 hw
  have n2 : k + 2 ≠ k := by
    intro h; have := add_left_cancel (h.trans (add_zero k).symm); exact absurd this (by decide)
  have n3 : k + 3 ≠ k := by
    intro h; have := add_left_cancel (h.trans (add_zero k).symm); exact absurd this (by decide)
  have := beautiful G hcf hmax hmin hR (k + 2) c'
    (by rw [Function.update_of_ne n2]; exact hc2)
    (by have e : k + 2 + 1 = k + 3 := by rw [add_assoc]; rfl
        rw [e, Function.update_of_ne n3]; exact hc3)
  have e : k + 2 + 3 = k := by
    rw [add_assoc, show (2 : Fin 5) + 3 = 0 from rfl, add_zero]
  rw [e, Function.update_self] at this
  exact this

end Rot


section L48
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- LPR Lemma 4.8 in H1 labels (b0 = v0, b1 = v3, b4 = v2, a1 = u3, a4 = u2): if Uq ~ u3, u2 and
Vq ~ Uq, v0, then Vq ~ v3, or Vq ~ v2, or Vq is adjacent to twins X of v3 and Y of v2. -/
theorem lemma48 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (Uq Vq : V)
    (hU3 : G.Adj Uq (u 3)) (hU2 : G.Adj Uq (u 2)) (hVU : G.Adj Vq Uq) (hV0 : G.Adj Vq (v 0)) :
    G.Adj Vq (v 3) ∨ G.Adj Vq (v 2) ∨
      ∃ X Y : V, G.Adj Vq X ∧ G.Adj Vq Y ∧
        (G.Adj X (v 2) ∧ G.Adj X (v 4) ∧ G.Adj X (u 2) ∧ G.Adj X (u 4)) ∧
        (G.Adj Y (v 1) ∧ G.Adj Y (v 3) ∧ G.Adj Y (u 1) ∧ G.Adj Y (u 3)) := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  have hU0 : G.Adj Uq (u 0) := beautiful G hcf hmax hmin hY 2 Uq hU2 hU3
  by_cases h3 : G.Adj Vq (v 3)
  · exact Or.inl h3
  by_cases h2 : G.Adj Vq (v 2)
  · exact Or.inr (Or.inl h2)
  right; right
  obtain hX | ⟨X, hX_u2, hX_v4, hX_v2, hX_Vq⟩ := lemma43 G hcf hmax hmin
      (a := ![(u 2), (u 3), (v 0)]) (b := ![(v 4), (v 1), Uq]) (c := ![(v 3), (v 2), Vq])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [(gu4 2), hU2.symm, (gu1 3), hU3.symm, (gv 4).symm, (gv 0)])
      (by intro p; fin_cases p
          exacts [(gu1 2).symm, (gu4 3).symm, hV0])
      (by intro p; fin_cases p
          exacts [(gv 3), (gv 1).symm, hVU])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hX.symm h2
  obtain hY' | ⟨Y, hY_u3, hY_v1, hY_v3, hY_Vq⟩ := lemma43 G hcf hmax hmin
      (a := ![(u 3), (u 2), (v 0)]) (b := ![(v 1), (v 4), Uq]) (c := ![(v 2), (v 3), Vq])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [(gu1 3), hU3.symm, (gu4 2), hU2.symm, (gv 0), (gv 4).symm])
      (by intro p; fin_cases p
          exacts [(gu4 3).symm, (gu1 2).symm, hV0])
      (by intro p; fin_cases p
          exacts [(gv 1).symm, (gv 3), hVU])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hY'.symm h3
  have hChXu4 : IsGr G ![Vq, Uq, (u 2), (v 1), Y] ![(u 3), X, (u 0), (v 3), (v 0)] (v 4) := by
    intro i; fin_cases i
    · exact ⟨hVU, hU3.symm, hY_u3.symm, (gu1 3).symm⟩
    · exact ⟨hU2, hX_u2, hX_Vq, hX_v4.symm⟩
    · exact ⟨(gu4 2), (gu1 0), hU0.symm, (gu4 0).symm⟩
    · exact ⟨hY_v1.symm, hY_v3.symm, (gu1 2).symm, (gv 3).symm⟩
    · exact ⟨hY_Vq, hV0.symm, (gv 0), (gv 4)⟩
  have hXu4 := beautiful G hcf hmax hmin hChXu4 3 (u 4) (gu4 4) (gu1 4)
  have hChYu1 : IsGr G ![Uq, Vq, X, (v 4), (u 3)] ![Y, (u 2), (v 0), (v 2), (u 0)] (v 1) := by
    intro i; fin_cases i
    · exact ⟨hVU.symm, hY_Vq, hY_u3, hY_v1.symm⟩
    · exact ⟨hX_Vq.symm, hX_u2.symm, hU2.symm, (gu4 2).symm⟩
    · exact ⟨hX_v4, (gv 4).symm, hV0.symm, (gv 0).symm⟩
    · exact ⟨(gu1 3).symm, (gu4 3).symm, hX_v2.symm, (gv 1)⟩
    · exact ⟨hU3.symm, hU0.symm, (gu4 0), (gu1 0).symm⟩
  have hYu1 := beautiful G hcf hmax hmin hChYu1 2 (u 1) (gu4 1) (gu1 1)
  exact ⟨X, Y, hX_Vq.symm, hY_Vq.symm, ⟨hX_v2, hX_v4, hX_u2, hXu4.symm⟩,
    ⟨hY_v1, hY_v3, hYu1.symm, hY_u3⟩⟩

end L48


section L410
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def l410_c_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 1) ||
    (b 5 && b 1) ||
    (b 5 && b 4) ||
    (b 9 && b 5) ||
    (b 1 && b 2) ||
    (b 2 && b 3) ||
    (b 6 && b 3) ||
    (b 6 && b 1) ||
    (b 9 && b 6) ||
    (b 3 && b 4) ||
    (b 7 && b 4) ||
    (b 7 && b 2) ||
    (b 9 && b 7) ||
    (b 4 && b 0) ||
    (b 8 && b 0) ||
    (b 8 && b 3) ||
    (b 9 && b 8) ||
    (b 10 && b 6) ||
    (b 10 && b 7) ||
    (b 10 && b 5) ||
    (b 11 && b 10) ||
    (b 11 && b 0) ||
    (b 11 && b 2) ||
    !(decide (5 ≤ cnt12 b)) || ((b 5 && b 6 && b 7 && b 8 && b 11))

theorem l410_c_B_ok : ∀ b : Fin 12 → Bool, l410_c_B b = true :=
  forall_fin12_bool (by decide)

theorem l410_c : ∀ b : Fin 12 → Bool,
    (b 0 && b 1) = false →
    (b 5 && b 1) = false →
    (b 5 && b 4) = false →
    (b 9 && b 5) = false →
    (b 1 && b 2) = false →
    (b 2 && b 3) = false →
    (b 6 && b 3) = false →
    (b 6 && b 1) = false →
    (b 9 && b 6) = false →
    (b 3 && b 4) = false →
    (b 7 && b 4) = false →
    (b 7 && b 2) = false →
    (b 9 && b 7) = false →
    (b 4 && b 0) = false →
    (b 8 && b 0) = false →
    (b 8 && b 3) = false →
    (b 9 && b 8) = false →
    (b 10 && b 6) = false →
    (b 10 && b 7) = false →
    (b 10 && b 5) = false →
    (b 11 && b 10) = false →
    (b 11 && b 0) = false →
    (b 11 && b 2) = false →
    5 ≤ cnt12 b → ((b 5 && b 6 && b 7 && b 8 && b 11)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l410_c_B_ok b
  simp only [l410_c_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h


theorem l410_core (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (q z : V)
    (hq3 : G.Adj q (u 3)) (hq2 : G.Adj q (u 2)) (hzq : G.Adj z q) (hz0 : G.Adj z (v 0))
    (hz2 : G.Adj z (v 2)) : ∀ k, G.Adj q (u k) := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  have hq0 : G.Adj q (u 0) := beautiful G hcf hmax hmin hY 2 q hq2 hq3
  obtain ⟨c1, hc, hp⟩ := D_bool12 G hcf hmin ![(v 0), (v 1), (v 2), (v 3), (v 4), (u 0), (u 2), (u 3), (u 4), w, q, z]
  have h := l410_c _ (hp 0 1 (gv 0)) (hp 5 1 (gu1 0)) (hp 5 4 (gu4 0)) (hp 9 5 (gw 0)) (hp 1 2 (gv 1)) (hp 2 3 (gv 2)) (hp 6 3 (gu1 2)) (hp 6 1 (gu4 2)) (hp 9 6 (gw 2)) (hp 3 4 (gv 3)) (hp 7 4 (gu1 3)) (hp 7 2 (gu4 3)) (hp 9 7 (gw 3)) (hp 4 0 (gv 4)) (hp 8 0 (gu1 4)) (hp 8 3 (gu4 4)) (hp 9 8 (gw 4)) (hp 10 6 hq2) (hp 10 7 hq3) (hp 10 5 hq0) (hp 11 10 hzq) (hp 11 0 hz0) (hp 11 2 hz2) hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩, hh5⟩
  have hc1_u0 : G.Adj c1 (u 0) := hh1.symm
  have hc1_u2 : G.Adj c1 (u 2) := hh2.symm
  have hc1_u3 : G.Adj c1 (u 3) := hh3.symm
  have hc1_u4 : G.Adj c1 (u 4) := hh4.symm
  have hc1_z : G.Adj c1 z := hh5.symm
  have hC : IsGr G ![(v 0), (v 1), (v 2), (v 3), (v 4)] ![(u 0), z, (u 2), (u 3), (u 4)] c1 := by
    intro i; fin_cases i
    · exact ⟨(gv 0), (gu1 0), (gu4 0), hc1_u0⟩
    · exact ⟨(gv 1), hz2, hz0, hc1_z⟩
    · exact ⟨(gv 2), (gu1 2), (gu4 2), hc1_u2⟩
    · exact ⟨(gv 3), (gu1 3), (gu4 3), hc1_u3⟩
    · exact ⟨(gv 4), (gu1 4), (gu4 4), hc1_u4⟩
  have hq4 : G.Adj q (u 4) := beautiful G hcf hmax hmin hC 1 q hzq.symm hq2
  have hq1 : G.Adj q (u 1) := beautiful G hcf hmax hmin hY 3 q hq3 hq4
  intro k; fin_cases k
  exacts [hq0, hq1, hq2, hq3, hq4]

theorem IsGr.refl {v u : Fin 5 → V} {w : V} (h : IsGr G v u w) :
    IsGr G (fun i => v (-i)) (fun i => u (-i)) w := by
  intro i
  have e1 : ∀ j : Fin 5, -(j + 1) + 1 = -j := by decide
  have e2 : ∀ j : Fin 5, -j + 4 = -(j + 1) := by decide
  have e3 : ∀ j : Fin 5, -j + 1 = -(j + 4) := by decide
  have a1 := (h (-(i + 1))).1
  rw [e1] at a1
  have a2 := (h (-i)).2.2.1
  rw [e2] at a2
  have a3 := (h (-i)).2.1
  rw [e3] at a3
  exact ⟨a1.symm, a2, a3, (h (-i)).2.2.2⟩

theorem IsGr.replace_v2 {v u : Fin 5 → V} {w : V} (h : IsGr G v u w) (Y : V)
    (h1 : G.Adj Y (v 1)) (h3 : G.Adj Y (v 3)) (hu1 : G.Adj Y (u 1)) (hu3 : G.Adj Y (u 3)) :
    IsGr G ![v 0, v 1, Y, v 3, v 4] u w := by
  intro i; fin_cases i
  · exact h 0
  · exact ⟨h1.symm, hu1.symm, (h 1).2.2.1, (h 1).2.2.2⟩
  · exact ⟨h3, (h 2).2.1, (h 2).2.2.1, (h 2).2.2.2⟩
  · exact ⟨(h 3).1, (h 3).2.1, hu3.symm, (h 3).2.2.2⟩
  · exact h 4

/-- LPR Lemma 4.10 in H1 labels (a1 = u3, a4 = u2, b0 = v0): if q ~ u3, u2 then q is adjacent
to all shadows u k (a twin of the centre) or q ~ v0 (q ∈ Ext(Υ, a0)). -/
theorem lemma410 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (q : V)
    (hq3 : G.Adj q (u 3)) (hq2 : G.Adj q (u 2)) :
    (∀ k, G.Adj q (u k)) ∨ G.Adj q (v 0) := by
  by_cases hb : G.Adj q (v 0)
  · exact Or.inr hb
  left
  have hne : q ≠ v 0 := by
    rintro rfl
    exact not_adj_both hcf hq2.symm (hY 2).2.2.1 (hY 0).1
  obtain ⟨z, hqz, hz0'⟩ := hmax q (v 0) hne hb
  rcases lemma48 G hcf hmax hmin hY q z hq3 hq2 hqz.symm hz0'.symm with
    h3 | h2 | ⟨X, Y, hzX, hzY, -, hYv1, hYv3, hYu1, hYu3⟩
  · have hR := hY.refl G
    have := l410_core G hcf hmax hmin hR q z hq2 hq3 hqz.symm hz0'.symm h3
    intro k
    have e : - -k = k := neg_neg k
    have hk := this (-k)
    simp only [e] at hk
    exact hk
  · exact l410_core G hcf hmax hmin hY q z hq3 hq2 hqz.symm hz0'.symm h2
  · exact l410_core G hcf hmax hmin (hY.replace_v2 G Y hYv1 hYv3 hYu1 hYu3) q z hq3 hq2
      hqz.symm hz0'.symm hzY

end L410


section L411
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- LPR Lemma 4.11 in H1 labels (a0 = u0, b1 = v3, a1 = u3, b0 = v0; Ext(Υ, a2) = common
neighbours of u3, u4, v1): if q ~ u0, v3 and q ≁ u3 then q ~ v0 and q has a neighbour in Ext(Υ, a2). -/
theorem lemma411 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (q : V)
    (hq0 : G.Adj q (u 0)) (hq3v : G.Adj q (v 3)) (hn : ¬ G.Adj q (u 3)) :
    G.Adj q (v 0) ∧ ∃ t, G.Adj t (u 3) ∧ G.Adj t (u 4) ∧ G.Adj t (v 1) ∧ G.Adj q t := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  have hne : q ≠ u 3 := by
    rintro rfl
    exact not_adj_both hcf (gw 3) (gw 0) hq0
  obtain ⟨z, hqz, hz3'⟩ := hmax q (u 3) hne hn
  have hzq : G.Adj z q := hqz.symm
  have hz3 : G.Adj z (u 3) := hz3'.symm
  obtain hc | ⟨t, ht_q, ht_u3, ht_v1, ht_u4⟩ := lemma43 G hcf hmax hmin
      (a := ![q, (v 2), w]) (b := ![(u 3), (u 0), (v 3)]) (c := ![z, (v 1), (u 4)])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [hq0, hq3v, (gu4 3).symm, (gv 2), (gw 3), (gw 0)])
      (by intro p; fin_cases p
          exacts [hzq, (gv 1), (gw 4).symm])
      (by intro p; fin_cases p
          exacts [hz3, (gu1 0).symm, (gu4 4)])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hc (not_adj_both hcf (gv 0) (gu1 4).symm)
  have hC : IsGr G ![(u 3), w, (u 4), (v 3), (v 4)] ![(u 0), t, (u 2), (v 0), (v 2)] (v 1) := by
    intro i; fin_cases i
    · exact ⟨(gw 3).symm, (gw 0).symm, (gu4 0), (gu1 0).symm⟩
    · exact ⟨(gw 4), ht_u4, ht_u3, ht_v1.symm⟩
    · exact ⟨(gu4 4), (gu1 2), (gw 2).symm, (gu4 2).symm⟩
    · exact ⟨(gv 3), (gv 4).symm, (gu1 4).symm, (gv 0).symm⟩
    · exact ⟨(gu1 3).symm, (gu4 3).symm, (gv 2), (gv 1)⟩
  have hb := beautiful G hcf hmax hmin hC 0 q hq0 ht_q.symm
  exact ⟨hb, t, ht_u3, ht_u4, ht_v1, ht_q.symm⟩

end L411


section L412
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- LPR Lemma 4.12 in H1 labels (a0 = u0, b1 = v3, a2 = u1, b0 = v0): if q ~ u0, v3 then
q ~ u1 (q ∈ Ext(Υ, a1)), or q ~ v0, or q is adjacent to a twin A2 of u1 and a twin B0 of v0. -/
theorem lemma412 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w) (q : V)
    (hq0 : G.Adj q (u 0)) (hq3v : G.Adj q (v 3)) :
    G.Adj q (u 1) ∨ G.Adj q (v 0) ∨
      ∃ A2 B0 : V, G.Adj q A2 ∧ G.Adj q B0 ∧
        (G.Adj A2 (v 0) ∧ G.Adj A2 (v 2) ∧ G.Adj A2 w) ∧
        (G.Adj B0 (v 1) ∧ G.Adj B0 (v 4) ∧ G.Adj B0 (u 1) ∧ G.Adj B0 (u 4)) := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  by_cases h1 : G.Adj q (u 1)
  · exact Or.inl h1
  by_cases h0 : G.Adj q (v 0)
  · exact Or.inr (Or.inl h0)
  right; right
  obtain hc | ⟨B0, hB_u4, hB_v1, hB_u1, hB_q⟩ := lemma43 G hcf hmax hmin
      (a := ![(u 4), (v 2), (u 0)]) (b := ![(v 1), w, (v 3)]) (c := ![(v 0), (u 1), q])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [(gw 4).symm, (gu4 4), (gv 1).symm, (gv 2), (gu1 0), (gw 0).symm])
      (by intro p; fin_cases p
          exacts [(gu1 4).symm, (gu1 1), hq0])
      (by intro p; fin_cases p
          exacts [(gv 0), (gw 1).symm, hq3v])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hc.symm h1
  obtain hc | ⟨A2, hA_v2, hA_w, hA_v0, hA_q⟩ := lemma43 G hcf hmax hmin
      (a := ![(v 2), (u 4), (u 0)]) (b := ![w, (v 1), (v 3)]) (c := ![(u 1), (v 0), q])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [(gv 1).symm, (gv 2), (gw 4).symm, (gu4 4), (gw 0).symm, (gu1 0)])
      (by intro p; fin_cases p
          exacts [(gu1 1), (gu1 4).symm, hq0])
      (by intro p; fin_cases p
          exacts [(gw 1).symm, (gv 0), hq3v])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hc.symm h0
  have hB_v4 : G.Adj B0 (v 4) := by
    by_contra hn
    refine no_cube G hcf hmax hmin ![v 4, q, u 4, v 1] ![B0, v 0, u 0, v 3] ?_ ?_
    · intro p r hpr; fin_cases p <;> fin_cases r
      all_goals first | exact absurd rfl hpr | skip
      exacts [(gv 4), (gu4 0).symm, (gv 3).symm, hB_q.symm, hq0, hq3v, hB_u4.symm, (gu1 4), (gu4 4), hB_v1.symm, (gv 0).symm, (gu1 0).symm]
    · intro p; fin_cases p
      · exact fun h => hn h.symm
      · exact h0
      · exact not_adj_both hcf (gw 4) (gw 0)
      · exact not_adj_both hcf (gu4 2) (gu1 2)
  exact ⟨A2, B0, hA_q.symm, hB_q.symm, ⟨hA_v0, hA_v2, hA_w⟩, ⟨hB_v1, hB_v4, hB_u1, hB_u4⟩⟩

end L412


section L467
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- LPR Lemma 4.6 (i = 0, eps = 1) in H1 labels: non-adjacent twins A of u0 and B of v1 have a common neighbour with u1 and v3. -/
theorem lemma46 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (A B : V) (hA_v1 : G.Adj A (v 1)) (hA_v4 : G.Adj A (v 4)) (hA_w : G.Adj A w)
    (hB_v0 : G.Adj B (v 0)) (hB_v2 : G.Adj B (v 2)) (hB_u0 : G.Adj B (u 0)) (hB_u2 : G.Adj B (u 2)) (hAB : ¬ G.Adj A B) :
    ∃ t, G.Adj t A ∧ G.Adj t (u 1) ∧ G.Adj t (v 3) ∧ G.Adj t B := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  by_cases hAB' : A = B
  · subst hAB'
    exact (not_adj_both hcf hA_v1 hB_v0 (gv 0).symm).elim
  obtain ⟨r, hAr, hBr⟩ := hmax A B hAB' hAB
  have hrA : G.Adj r A := hAr.symm
  have hrB : G.Adj r B := hBr.symm
  obtain hc | ⟨t, h1, h2, h3, h4⟩ := lemma43 G hcf hmax hmin
      (a := ![A, (v 0), (u 2)]) (b := ![B, w, (v 4)]) (c := ![r, (u 1), (v 3)])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [hA_w, hA_v4, hB_v0.symm, (gv 4).symm, hB_u2.symm, (gw 2).symm])
      (by intro p; fin_cases p
          exacts [hrA, (gu4 1), (gu1 2).symm])
      (by intro p; fin_cases p
          exacts [hrB, (gw 1).symm, (gv 3)])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hc (not_adj_both hcf (gu1 1).symm (gv 2))
  exact ⟨t, h1, h3, h4, h2⟩

/-- LPR Lemma 4.7 (i = 0) in H1 labels: non-adjacent twins A of v0 and B of v1 have a common neighbour with v3 and w. -/
theorem lemma47 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (A B : V) (hA_v1 : G.Adj A (v 1)) (hA_v4 : G.Adj A (v 4)) (hA_u1 : G.Adj A (u 1)) (hA_u4 : G.Adj A (u 4))
    (hB_v0 : G.Adj B (v 0)) (hB_v2 : G.Adj B (v 2)) (hB_u0 : G.Adj B (u 0)) (hB_u2 : G.Adj B (u 2)) (hAB : ¬ G.Adj A B) :
    ∃ t, G.Adj t A ∧ G.Adj t (v 3) ∧ G.Adj t w ∧ G.Adj t B := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  by_cases hAB' : A = B
  · subst hAB'
    exact (not_adj_both hcf hA_v1 hB_v0 (gv 0).symm).elim
  obtain ⟨r, hAr, hBr⟩ := hmax A B hAB' hAB
  have hrA : G.Adj r A := hAr.symm
  have hrB : G.Adj r B := hBr.symm
  obtain hc | ⟨t, h1, h2, h3, h4⟩ := lemma43 G hcf hmax hmin
      (a := ![A, (v 2), (u 0)]) (b := ![B, (v 4), (u 1)]) (c := ![r, (v 3), w])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [hA_v4, hA_u1, hB_v2.symm, (gu1 1).symm, hB_u0.symm, (gu4 0)])
      (by intro p; fin_cases p
          exacts [hrA, (gv 2).symm, (gw 0)])
      (by intro p; fin_cases p
          exacts [hrB, (gv 3), (gw 1)])
      0 1 2 (by decide) (by decide) (by decide)
  · exact absurd hc (not_adj_both hcf (gu1 2) (gw 2).symm)
  exact ⟨t, h1, h3, h4, h2⟩

end L467


section L41314
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def l413_c_B (b : Fin 12 → Bool) : Bool :=
    (b 4 && b 0) ||
    (b 4 && b 3) ||
    (b 8 && b 4) ||
    (b 0 && b 1) ||
    (b 5 && b 1) ||
    (b 8 && b 5) ||
    (b 1 && b 2) ||
    (b 6 && b 2) ||
    (b 6 && b 0) ||
    (b 8 && b 6) ||
    (b 2 && b 3) ||
    (b 7 && b 3) ||
    (b 7 && b 1) ||
    (b 8 && b 7) ||
    (b 10 && b 7) ||
    (b 10 && b 0) ||
    (b 10 && b 5) ||
    (b 11 && b 5) ||
    (b 11 && b 6) ||
    (b 11 && b 3) ||
    (b 9 && b 4) ||
    (b 9 && b 11) ||
    (b 9 && b 2) ||
    (b 9 && b 10) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l413_c_B_ok : ∀ b : Fin 12 → Bool, l413_c_B b = true :=
  forall_fin12_bool (by decide)

theorem l413_c : ∀ b : Fin 12 → Bool,
    (b 4 && b 0) = false →
    (b 4 && b 3) = false →
    (b 8 && b 4) = false →
    (b 0 && b 1) = false →
    (b 5 && b 1) = false →
    (b 8 && b 5) = false →
    (b 1 && b 2) = false →
    (b 6 && b 2) = false →
    (b 6 && b 0) = false →
    (b 8 && b 6) = false →
    (b 2 && b 3) = false →
    (b 7 && b 3) = false →
    (b 7 && b 1) = false →
    (b 8 && b 7) = false →
    (b 10 && b 7) = false →
    (b 10 && b 0) = false →
    (b 10 && b 5) = false →
    (b 11 && b 5) = false →
    (b 11 && b 6) = false →
    (b 11 && b 3) = false →
    (b 9 && b 4) = false →
    (b 9 && b 11) = false →
    (b 9 && b 2) = false →
    (b 9 && b 10) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 hc
  have h := l413_c_B_ok b
  simp only [l413_c_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

def l414_c1_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 1) ||
    (b 1 && b 2) ||
    (b 2 && b 3) ||
    (b 5 && b 3) ||
    (b 5 && b 1) ||
    (b 8 && b 5) ||
    (b 3 && b 4) ||
    (b 6 && b 4) ||
    (b 6 && b 2) ||
    (b 8 && b 6) ||
    (b 4 && b 0) ||
    (b 7 && b 0) ||
    (b 7 && b 3) ||
    (b 8 && b 7) ||
    (b 9 && b 4) ||
    (b 9 && b 2) ||
    (b 9 && b 8) ||
    (b 11 && b 9) ||
    (b 11 && b 7) ||
    (b 11 && b 1) ||
    (b 10 && b 5) ||
    (b 10 && b 6) ||
    (b 10 && b 0) ||
    !(decide (5 ≤ cnt12 b)) || ((b 2 && b 4 && b 8 && b 10 && b 11))

theorem l414_c1_B_ok : ∀ b : Fin 12 → Bool, l414_c1_B b = true :=
  forall_fin12_bool (by decide)

theorem l414_c1 : ∀ b : Fin 12 → Bool,
    (b 0 && b 1) = false →
    (b 1 && b 2) = false →
    (b 2 && b 3) = false →
    (b 5 && b 3) = false →
    (b 5 && b 1) = false →
    (b 8 && b 5) = false →
    (b 3 && b 4) = false →
    (b 6 && b 4) = false →
    (b 6 && b 2) = false →
    (b 8 && b 6) = false →
    (b 4 && b 0) = false →
    (b 7 && b 0) = false →
    (b 7 && b 3) = false →
    (b 8 && b 7) = false →
    (b 9 && b 4) = false →
    (b 9 && b 2) = false →
    (b 9 && b 8) = false →
    (b 11 && b 9) = false →
    (b 11 && b 7) = false →
    (b 11 && b 1) = false →
    (b 10 && b 5) = false →
    (b 10 && b 6) = false →
    (b 10 && b 0) = false →
    5 ≤ cnt12 b → ((b 2 && b 4 && b 8 && b 10 && b 11)) = true := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l414_c1_B_ok b
  simp only [l414_c1_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact h

def l414_c2_B (b : Fin 12 → Bool) : Bool :=
    (b 0 && b 1) ||
    (b 1 && b 2) ||
    (b 2 && b 3) ||
    (b 4 && b 3) ||
    (b 4 && b 1) ||
    (b 7 && b 4) ||
    (b 5 && b 2) ||
    (b 7 && b 5) ||
    (b 6 && b 0) ||
    (b 6 && b 3) ||
    (b 7 && b 6) ||
    (b 9 && b 6) ||
    (b 9 && b 1) ||
    (b 10 && b 5) ||
    (b 10 && b 3) ||
    (b 10 && b 9) ||
    (b 8 && b 4) ||
    (b 8 && b 5) ||
    (b 8 && b 0) ||
    (b 11 && b 2) ||
    (b 11 && b 7) ||
    (b 11 && b 8) ||
    (b 11 && b 9) ||
    !(decide (5 ≤ cnt12 b)) || false

theorem l414_c2_B_ok : ∀ b : Fin 12 → Bool, l414_c2_B b = true :=
  forall_fin12_bool (by decide)

theorem l414_c2 : ∀ b : Fin 12 → Bool,
    (b 0 && b 1) = false →
    (b 1 && b 2) = false →
    (b 2 && b 3) = false →
    (b 4 && b 3) = false →
    (b 4 && b 1) = false →
    (b 7 && b 4) = false →
    (b 5 && b 2) = false →
    (b 7 && b 5) = false →
    (b 6 && b 0) = false →
    (b 6 && b 3) = false →
    (b 7 && b 6) = false →
    (b 9 && b 6) = false →
    (b 9 && b 1) = false →
    (b 10 && b 5) = false →
    (b 10 && b 3) = false →
    (b 10 && b 9) = false →
    (b 8 && b 4) = false →
    (b 8 && b 5) = false →
    (b 8 && b 0) = false →
    (b 11 && b 2) = false →
    (b 11 && b 7) = false →
    (b 11 && b 8) = false →
    (b 11 && b 9) = false →
    5 ≤ cnt12 b → False := by
  intro b h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 hc
  have h := l414_c2_B_ok b
  simp only [l414_c2_B, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, Bool.false_or, decide_eq_true hc,
    Bool.not_true] at h
  exact Bool.false_ne_true h

/-- LPR Lemma 4.13 in H1 labels: Ext(a1) = N(u0) ∩ N(u1) ∩ N(v3), Ext(a2) = N(u3) ∩ N(u4) ∩ N(v1),
Ext(a3) = N(u1) ∩ N(u2) ∩ N(v4) are not all non-empty. -/
theorem lemma413 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (t1 t2 t3 : V) (h1a : G.Adj t1 (u 0)) (h1b : G.Adj t1 (u 1)) (h1c : G.Adj t1 (v 3))
    (h2a : G.Adj t2 (u 3)) (h2b : G.Adj t2 (u 4)) (h2c : G.Adj t2 (v 1))
    (h3a : G.Adj t3 (u 1)) (h3b : G.Adj t3 (u 2)) (h3c : G.Adj t3 (v 4)) : False := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  have h2d : G.Adj t2 (u 1) := beautiful G hcf hmax hmin hY 3 t2 h2a h2b
  obtain hc | ⟨q, hq_u0, hq_t3, hq_v3, hq_t2⟩ := lemma43 G hcf hmax hmin
      (a := ![(u 0), (u 2), (u 1)]) (b := ![t3, t1, (v 1)]) (c := ![(v 4), (v 3), t2])
      (by intro p q hpq; fin_cases p <;> fin_cases q
          all_goals first | exact absurd rfl hpq | skip
          exacts [h1a.symm, (gu1 0), h3b.symm, (gu4 2), h3a.symm, h1b.symm])
      (by intro p; fin_cases p
          exacts [(gu4 0).symm, (gu1 2).symm, h2d])
      (by intro p; fin_cases p
          exacts [h3c.symm, h1c.symm, h2c])
      0 1 2 (by decide) (by decide) (by decide)
  · exact not_adj_both hcf (gu4 4) h2b.symm hc
  obtain ⟨s, hc, hp⟩ := D_bool12 G hcf hmin ![(v 1), (v 2), (v 3), (v 4), (u 0), (u 1), (u 2), (u 3), w, q, t2, t3]
  exact (l413_c _ (hp 4 0 (gu1 0)) (hp 4 3 (gu4 0)) (hp 8 4 (gw 0)) (hp 0 1 (gv 1)) (hp 5 1 (gu1 1)) (hp 8 5 (gw 1)) (hp 1 2 (gv 2)) (hp 6 2 (gu1 2)) (hp 6 0 (gu4 2)) (hp 8 6 (gw 2)) (hp 2 3 (gv 3)) (hp 7 3 (gu1 3)) (hp 7 1 (gu4 3)) (hp 8 7 (gw 3)) (hp 10 7 h2a) (hp 10 0 h2c) (hp 10 5 h2d) (hp 11 5 h3a) (hp 11 6 h3b) (hp 11 3 h3c) (hp 9 4 hq_u0) (hp 9 11 hq_t3) (hp 9 2 hq_v3) (hp 9 10 hq_t2) hc).elim

/-- LPR Lemma 4.14 in H1 labels: A1 twin of a1 = u3 (A1 ~ v4, v2, w), T ∈ Ext(Υ(A1), a2)
(T ~ A1, u4, v1), q common neighbour of u3, v3, T. Then a0 = u0 is reliable:
no vertex t0 is adjacent to u2, u3, v0. -/
theorem lemma414 (hcf : G.CliqueFree 3)
    (hmax : ∀ x y : V, x ≠ y → ¬ G.Adj x y → ∃ z : V, G.Adj x z ∧ G.Adj y z)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (A1 : V) (hA_v4 : G.Adj A1 (v 4)) (hA_v2 : G.Adj A1 (v 2)) (hA_w : G.Adj A1 w)
    (T : V) (hT_A : G.Adj T A1) (hT_u4 : G.Adj T (u 4)) (hT_v1 : G.Adj T (v 1))
    (q : V) (hq_u3 : G.Adj q (u 3)) (hq_v3 : G.Adj q (v 3)) (hq_T : G.Adj q T)
    (t0 : V) (h0a : G.Adj t0 (u 2)) (h0b : G.Adj t0 (u 3)) (h0c : G.Adj t0 (v 0)) : False := by
  have gv : ∀ k : Fin 5, G.Adj (v k) (v (k + 1)) := fun k => (hY k).1
  have gu1 : ∀ k : Fin 5, G.Adj (u k) (v (k + 1)) := fun k => (hY k).2.1
  have gu4 : ∀ k : Fin 5, G.Adj (u k) (v (k + 4)) := fun k => (hY k).2.2.1
  have gw : ∀ k : Fin 5, G.Adj w (u k) := fun k => (hY k).2.2.2
  obtain ⟨z, hc, hp⟩ := D_bool12 G hcf hmin ![(v 0), (v 1), (v 2), (v 3), (v 4), (u 2), (u 3), (u 4), w, A1, t0, T]
  have h := l414_c1 _ (hp 0 1 (gv 0)) (hp 1 2 (gv 1)) (hp 2 3 (gv 2)) (hp 5 3 (gu1 2)) (hp 5 1 (gu4 2)) (hp 8 5 (gw 2)) (hp 3 4 (gv 3)) (hp 6 4 (gu1 3)) (hp 6 2 (gu4 3)) (hp 8 6 (gw 3)) (hp 4 0 (gv 4)) (hp 7 0 (gu1 4)) (hp 7 3 (gu4 4)) (hp 8 7 (gw 4)) (hp 9 4 hA_v4) (hp 9 2 hA_v2) (hp 9 8 hA_w) (hp 11 9 hT_A) (hp 11 7 hT_u4) (hp 11 1 hT_v1) (hp 10 5 h0a) (hp 10 6 h0b) (hp 10 0 h0c) hc
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨hh1, hh2⟩, hh3⟩, hh4⟩, hh5⟩
  have hz_v2 : G.Adj z (v 2) := hh1.symm
  have hz_v4 : G.Adj z (v 4) := hh2.symm
  have hz_w : G.Adj z w := hh3.symm
  have hz_t0 : G.Adj z t0 := hh4.symm
  have hz_T : G.Adj z T := hh5.symm
  obtain ⟨s, hc, hp⟩ := D_bool12 G hcf hmin ![(v 0), (v 1), (v 2), (v 3), (u 2), (u 3), (u 4), w, t0, T, q, z]
  exact (l414_c2 _ (hp 0 1 (gv 0)) (hp 1 2 (gv 1)) (hp 2 3 (gv 2)) (hp 4 3 (gu1 2)) (hp 4 1 (gu4 2)) (hp 7 4 (gw 2)) (hp 5 2 (gu4 3)) (hp 7 5 (gw 3)) (hp 6 0 (gu1 4)) (hp 6 3 (gu4 4)) (hp 7 6 (gw 4)) (hp 9 6 hT_u4) (hp 9 1 hT_v1) (hp 10 5 hq_u3) (hp 10 3 hq_v3) (hp 10 9 hq_T) (hp 8 4 h0a) (hp 8 5 h0b) (hp 8 0 h0c) (hp 11 2 hz_v2) (hp 11 7 hz_w) (hp 11 8 hz_t0) (hp 11 9 hz_T) hc).elim

end L41314

end E128H1


/-!
# E128H1 Vega part: parametric Vega copies in G (LPR §4.4)
Standalone for fast compilation: the cube lemma (proved in E128H1_base.lean as `no_cube`)
enters as the hypothesis `NoCube G`.
-/

namespace E128H1V

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2_H2_R2

section Vega
variable {V : Type} (G : SimpleGraph V)

/-- No induced cube: conclusion of LPR Lemma 4.2 (`no_cube`). -/
def NoCube : Prop :=
  ∀ a b : Fin 4 → V, (∀ i j : Fin 4, i ≠ j → G.Adj (a i) (b j)) → ¬ ∀ i, ¬ G.Adj (a i) (b i)

theorem cube_force (hcube : NoCube G) (a b : Fin 4 → V)
    (hab : ∀ i j : Fin 4, i ≠ j → G.Adj (a i) (b j))
    (h1 : ¬ G.Adj (a 1) (b 1)) (h2 : ¬ G.Adj (a 2) (b 2)) (h3 : ¬ G.Adj (a 3) (b 3)) :
    G.Adj (a 0) (b 0) := by
  by_contra h0
  refine hcube a b hab ?_
  intro i; fin_cases i
  exacts [h0, h1, h2, h3]

/-- A copy of the Vega graph Υ_i^{μν} in G (not required injective). Andrásfai vertex j < 3i-1
is `g j`; adjacency in Γ_i between j > k is i ≤ j - k ≤ 2i - 1. If ν then 2i-1 is absent;
if μ then y is absent. -/
structure Vega (i : ℕ) (μ ν : Bool) where
  g : ℕ → V
  a : V
  v : V
  c : V
  u : V
  b : V
  w : V
  x : V
  y : V
  hi : 2 ≤ i
  gg : ∀ j k, j < 3 * i - 1 → (ν = true → j ≠ 2 * i - 1) → (ν = true → k ≠ 2 * i - 1) →
    i ≤ j - k → j - k ≤ 2 * i - 1 → G.Adj (g j) (g k)
  red : ∀ j, j < i → G.Adj a (g j) ∧ G.Adj u (g j)
  green : ∀ j, i ≤ j → j < 2 * i → (ν = true → j ≠ 2 * i - 1) → G.Adj b (g j) ∧ G.Adj v (g j)
  blue : ∀ j, 2 * i ≤ j → j < 3 * i - 1 → G.Adj c (g j) ∧ G.Adj w (g j)
  av : G.Adj a v
  vc : G.Adj v c
  cu : G.Adj c u
  ub : G.Adj u b
  bw : G.Adj b w
  wa : G.Adj w a
  xa : G.Adj x a
  xb : G.Adj x b
  xc : G.Adj x c
  yu : μ = false → G.Adj y u
  yv : μ = false → G.Adj y v
  yw : μ = false → G.Adj y w
  yx : μ = false → G.Adj y x

variable {G}

/-- LPR Lemma 4.16(a): q ~ u, v, w ⟹ q ~ x. -/
theorem Vega.l416a (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (hu : G.Adj q Y.u) (hv : G.Adj q Y.v) (hw : G.Adj q Y.w) :
    G.Adj q Y.x := by
  have hi := Y.hi
  have r0 := Y.red 0 (by omega)
  have gi := Y.green i (by omega) (by omega) (by intro _; omega)
  have b2 := Y.blue (2 * i) (by omega) (by omega)
  have := cube_force G hcube ![q, Y.a, Y.b, Y.c] ![Y.x, Y.u, Y.v, Y.w] ?_
    (not_adj_both hcf r0.1.symm r0.2.symm)
    (not_adj_both hcf gi.1.symm gi.2.symm)
    (not_adj_both hcf b2.1.symm b2.2.symm)
  · exact this
  · intro p r hpr; fin_cases p <;> fin_cases r
    all_goals first | exact absurd rfl hpr | skip
    exacts [hu, hv, hw, Y.xa.symm, Y.av, Y.wa.symm, Y.xb.symm, Y.ub.symm, Y.bw,
      Y.xc.symm, Y.cu, Y.vc.symm]

/-- LPR Lemma 4.17(a): q ~ b, v and q ~ red j ⟹ q ~ every t ≤ j. -/
theorem Vega.l417a (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (hb : G.Adj q Y.b) (hv : G.Adj q Y.v) (j : ℕ) (hj : j < i)
    (hqj : G.Adj q (Y.g j)) : ∀ t, t ≤ j → G.Adj q (Y.g t) := by
  have hi := Y.hi
  intro t ht
  rcases Nat.eq_or_lt_of_le ht with h | ht
  · rw [h]; exact hqj
  have rt := Y.red t (by omega)
  have rj := Y.red j hj
  have gti := Y.green (t + i) (by omega) (by omega) (by intro _; omega)
  have e1 : G.Adj (Y.g (t + i)) (Y.g t) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g (t + 2 * i)) (Y.g (t + i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g (t + 2 * i)) (Y.g j) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.a, Y.u, Y.g (t + i)] ![Y.g t, Y.b, Y.v, Y.g j] ?_
    (not_adj_both hcf Y.wa Y.bw.symm) (not_adj_both hcf Y.cu Y.vc.symm)
    (not_adj_both hcf e2 e3)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hb, hv, hqj, rt.1, Y.av, rj.1, rt.2, Y.ub, rj.2, e1, gti.1.symm, gti.2.symm]

/-- LPR Lemma 4.17(b): q ~ b, v and q ~ blue j ⟹ q ~ every blue t ≥ j. -/
theorem Vega.l417b (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (hb : G.Adj q Y.b) (hv : G.Adj q Y.v) (j : ℕ) (hj1 : 2 * i ≤ j)
    (hqj : G.Adj q (Y.g j)) : ∀ t, j ≤ t → t < 3 * i - 1 → G.Adj q (Y.g t) := by
  have hi := Y.hi
  intro t ht ht2
  rcases Nat.eq_or_lt_of_le ht with h | ht
  · rw [← h]; exact hqj
  have bt := Y.blue t (by omega) ht2
  have bj := Y.blue j hj1 (by omega)
  have gti := Y.green (t - i) (by omega) (by omega) (by intro _; omega)
  have e1 : G.Adj (Y.g t) (Y.g (t - i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g (t - i)) (Y.g (t - 2 * i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g j) (Y.g (t - 2 * i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.c, Y.w, Y.g (t - i)] ![Y.g t, Y.b, Y.v, Y.g j] ?_
    (not_adj_both hcf Y.cu.symm Y.ub) (not_adj_both hcf Y.wa.symm Y.av)
    (not_adj_both hcf e2.symm e3.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hb, hv, hqj, bt.1, Y.vc.symm, bj.1, bt.2, Y.bw.symm, bj.2, e1.symm, gti.1.symm,
    gti.2.symm]

/-- LPR Lemma 4.19(a): q ~ c, w and q ~ red j ⟹ q ~ every red t ≥ j. -/
theorem Vega.l419a (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (hc : G.Adj q Y.c) (hw : G.Adj q Y.w) (j : ℕ)
    (hqj : G.Adj q (Y.g j)) : ∀ t, j ≤ t → t < i → G.Adj q (Y.g t) := by
  have hi := Y.hi
  intro t ht ht2
  rcases Nat.eq_or_lt_of_le ht with h | ht
  · rw [← h]; exact hqj
  have rt := Y.red t ht2
  have rj := Y.red j (by omega)
  have bt := Y.blue (t + 2 * i - 1) (by omega) (by omega)
  have e1 : G.Adj (Y.g (t + 2 * i - 1)) (Y.g t) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g (t + 2 * i - 1)) (Y.g (t + i - 1)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g (t + i - 1)) (Y.g j) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.a, Y.u, Y.g (t + 2 * i - 1)] ![Y.g t, Y.c, Y.w, Y.g j] ?_
    (not_adj_both hcf Y.av.symm Y.vc) (not_adj_both hcf Y.ub.symm Y.bw)
    (not_adj_both hcf e2.symm e3)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hc, hw, hqj, rt.1, Y.wa.symm, rj.1, rt.2, Y.cu.symm, rj.2, e1, bt.1.symm, bt.2.symm]

/-- LPR Lemma 4.19(b): q ~ c, w and q ~ green j ⟹ q ~ every green s ∈ [i, j]. -/
theorem Vega.l419b (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (hc : G.Adj q Y.c) (hw : G.Adj q Y.w) (j : ℕ)
    (hj2 : j < 2 * i) (hjn : ν = true → j ≠ 2 * i - 1)
    (hqj : G.Adj q (Y.g j)) : ∀ s, i ≤ s → s ≤ j → G.Adj q (Y.g s) := by
  have hi := Y.hi
  intro s hs1 hs
  rcases Nat.eq_or_lt_of_le hs with h | hs
  · rw [h]; exact hqj
  have gs := Y.green s hs1 (by omega) (by intro _; omega)
  have gj := Y.green j (by omega) hj2 hjn
  have bs := Y.blue (s + i) (by omega) (by omega)
  have e1 : G.Adj (Y.g (s + i)) (Y.g s) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g (s + i)) (Y.g (j - i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g j) (Y.g (j - i)) :=
    Y.gg _ _ (by omega) hjn (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.b, Y.v, Y.g (s + i)] ![Y.g s, Y.c, Y.w, Y.g j] ?_
    (not_adj_both hcf Y.ub Y.cu.symm) (not_adj_both hcf Y.av Y.wa.symm)
    (not_adj_both hcf e2.symm e3.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hc, hw, hqj, gs.1, Y.bw, gj.1, gs.2, Y.vc, gj.2, e1, bs.1.symm, bs.2.symm]

/-- LPR Lemma 4.20(a): q ~ a, u and q ~ green j ⟹ q ~ every green t ∈ [j, 2i-1-ν]. -/
theorem Vega.l420a (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (ha : G.Adj q Y.a) (hu : G.Adj q Y.u) (j : ℕ) (hj1 : i ≤ j)
    (hqj : G.Adj q (Y.g j)) :
    ∀ t, j ≤ t → t < 2 * i → (ν = true → t ≠ 2 * i - 1) → G.Adj q (Y.g t) := by
  have hi := Y.hi
  intro t ht ht2 htn
  rcases Nat.eq_or_lt_of_le ht with h | ht
  · rw [← h]; exact hqj
  have gt := Y.green t (by omega) ht2 htn
  have gj := Y.green j hj1 (by omega) (by intro _; omega)
  have rt := Y.red (t - i) (by omega)
  have e1 : G.Adj (Y.g t) (Y.g (t - i)) :=
    Y.gg _ _ (by omega) htn (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g (j + i)) (Y.g (t - i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g (j + i)) (Y.g j) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.b, Y.v, Y.g (t - i)] ![Y.g t, Y.a, Y.u, Y.g j] ?_
    (not_adj_both hcf Y.bw.symm Y.wa) (not_adj_both hcf Y.vc.symm Y.cu)
    (not_adj_both hcf e2 e3)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [ha, hu, hqj, gt.1, Y.ub.symm, gj.1, gt.2, Y.av.symm, gj.2, e1.symm, rt.1.symm,
    rt.2.symm]

/-- LPR Lemma 4.20(b): q ~ a, u and q ~ blue j ⟹ q ~ every blue s ∈ [2i, j]. -/
theorem Vega.l420b (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (ha : G.Adj q Y.a) (hu : G.Adj q Y.u) (j : ℕ)
    (hj2 : j < 3 * i - 1) (hqj : G.Adj q (Y.g j)) :
    ∀ s, 2 * i ≤ s → s ≤ j → G.Adj q (Y.g s) := by
  have hi := Y.hi
  intro s hs1 hs
  rcases Nat.eq_or_lt_of_le hs with h | hs
  · rw [h]; exact hqj
  have bs := Y.blue s hs1 (by omega)
  have bj := Y.blue j (by omega) hj2
  have rr := Y.red (s + 1 - 2 * i) (by omega)
  have e1 : G.Adj (Y.g s) (Y.g (s + 1 - 2 * i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g (s + 1 - i)) (Y.g (s + 1 - 2 * i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g j) (Y.g (s + 1 - i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.c, Y.w, Y.g (s + 1 - 2 * i)] ![Y.g s, Y.a, Y.u, Y.g j] ?_
    (not_adj_both hcf Y.vc Y.av.symm) (not_adj_both hcf Y.bw Y.ub.symm)
    (not_adj_both hcf e2 e3.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [ha, hu, hqj, bs.1, Y.cu, bj.1, bs.2, Y.wa, bj.2, e1.symm, rr.1.symm, rr.2.symm]

/-- LPR Lemma 4.16(b): μ = 0 and q ~ a, b, c ⟹ q ~ y. -/
theorem Vega.l416b (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {ν : Bool}
    (Y : Vega G i false ν) (q : V) (ha : G.Adj q Y.a) (hb : G.Adj q Y.b) (hc : G.Adj q Y.c) :
    G.Adj q Y.y := by
  have hi := Y.hi
  have r0 := Y.red 0 (by omega)
  have gi := Y.green i (by omega) (by omega) (by intro _; omega)
  have b2 := Y.blue (2 * i) (by omega) (by omega)
  refine cube_force G hcube ![q, Y.u, Y.v, Y.w] ![Y.y, Y.a, Y.b, Y.c] ?_
    (not_adj_both hcf r0.2.symm r0.1.symm)
    (not_adj_both hcf gi.2.symm gi.1.symm)
    (not_adj_both hcf b2.2.symm b2.1.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [ha, hb, hc, (Y.yu rfl).symm, Y.ub, Y.cu.symm, (Y.yv rfl).symm, Y.av.symm, Y.vc,
    (Y.yw rfl).symm, Y.wa, Y.bw.symm]

/-- LPR Lemma 4.26 (edge xy): x' ~ a, b, c and y' ~ u, v, w imply x' ~ y'. -/
theorem Vega.l426xy (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (x' y' : V) (ha : G.Adj x' Y.a) (hb : G.Adj x' Y.b) (hc : G.Adj x' Y.c)
    (hu : G.Adj y' Y.u) (hv : G.Adj y' Y.v) (hw : G.Adj y' Y.w) : G.Adj x' y' := by
  have hi := Y.hi
  have r0 := Y.red 0 (by omega)
  have gi := Y.green i (by omega) (by omega) (by intro _; omega)
  have b2 := Y.blue (2 * i) (by omega) (by omega)
  refine cube_force G hcube ![x', Y.u, Y.v, Y.w] ![y', Y.a, Y.b, Y.c] ?_
    (not_adj_both hcf r0.2.symm r0.1.symm)
    (not_adj_both hcf gi.2.symm gi.1.symm)
    (not_adj_both hcf b2.2.symm b2.1.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [ha, hb, hc, hu.symm, Y.ub, Y.cu.symm, hv.symm, Y.av.symm, Y.vc, hw.symm, Y.wa,
    Y.bw.symm]

/-- LPR Lemma 4.26, long red-green edge j m (j < i, i < m - j, m green): twins j' (j' ~ a, u,
g (j+i)) and m' (m' ~ b, v, g (m-i)) are adjacent. -/
theorem Vega.l426rg (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (j m : ℕ) (hj : j < i) (hm : m < 2 * i) (hjm : i < m - j)
    (j' m' : V) (hja : G.Adj j' Y.a) (hju : G.Adj j' Y.u) (hjg : G.Adj j' (Y.g (j + i)))
    (hmb : G.Adj m' Y.b) (hmv : G.Adj m' Y.v) (hmg : G.Adj m' (Y.g (m - i))) :
    G.Adj j' m' := by
  have hi := Y.hi
  have gji := Y.green (j + i) (by omega) (by omega) (by intro _; omega)
  have rmi := Y.red (m - i) (by omega)
  have e2 : G.Adj (Y.g (j + 2 * i)) (Y.g (j + i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g (j + 2 * i)) (Y.g (m - i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![j', Y.b, Y.v, Y.g (m - i)] ![m', Y.a, Y.u, Y.g (j + i)] ?_
    (not_adj_both hcf Y.bw.symm Y.wa) (not_adj_both hcf Y.vc.symm Y.cu)
    (not_adj_both hcf e3 e2)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hja, hju, hjg, hmb.symm, Y.ub.symm, gji.1, hmv.symm, Y.av.symm, gji.2, hmg.symm,
    rmi.1.symm, rmi.2.symm]

/-- LPR Lemma 4.26, long green-blue edge j m (i ≤ j, m blue, i < m - j): twins j'
(j' ~ b, v, g (j+i)) and m' (m' ~ c, w, g (m-i)) are adjacent. -/
theorem Vega.l426gb (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (j m : ℕ) (hj : i ≤ j) (hm : m < 3 * i - 1) (hjm : i < m - j)
    (hmj : m - j ≤ 2 * i - 1)
    (j' m' : V) (hjb : G.Adj j' Y.b) (hjv : G.Adj j' Y.v) (hjg : G.Adj j' (Y.g (j + i)))
    (hmc : G.Adj m' Y.c) (hmw : G.Adj m' Y.w) (hmg : G.Adj m' (Y.g (m - i))) :
    G.Adj j' m' := by
  have hi := Y.hi
  have bji := Y.blue (j + i) (by omega) (by omega)
  have gmi := Y.green (m - i) (by omega) (by omega) (by intro _; omega)
  have e2 : G.Adj (Y.g (m - i)) (Y.g (m - 2 * i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g (j + i)) (Y.g (m - 2 * i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![j', Y.c, Y.w, Y.g (m - i)] ![m', Y.b, Y.v, Y.g (j + i)] ?_
    (not_adj_both hcf Y.cu.symm Y.ub) (not_adj_both hcf Y.wa.symm Y.av)
    (not_adj_both hcf e2.symm e3.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hjb, hjv, hjg, hmc.symm, Y.vc.symm, bji.1, hmw.symm, Y.bw.symm, bji.2, hmg.symm,
    gmi.1.symm, gmi.2.symm]

/-- Adjacency in the Andrásfai part, either order. -/
def AA (i j k : ℕ) : Prop := (i ≤ j - k ∧ j - k ≤ 2 * i - 1) ∨ (i ≤ k - j ∧ k - j ≤ 2 * i - 1)

theorem Vega.adj {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) {j k : ℕ} (hj : j < 3 * i - 1)
    (hk : k < 3 * i - 1) (hjn : ν = true → j ≠ 2 * i - 1) (hkn : ν = true → k ≠ 2 * i - 1)
    (h : AA i j k) : G.Adj (Y.g j) (Y.g k) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Y.gg j k hj hjn hkn h1 h2
  · exact (Y.gg k j hk hkn hjn h1 h2).symm

/-- A (not necessarily injective) Grötzsch configuration (same as in E128H1_base). -/
def IsGr (H : SimpleGraph V) (v u : Fin 5 → V) (w : V) : Prop :=
  ∀ i : Fin 5, H.Adj (v i) (v (i + 1)) ∧ H.Adj (u i) (v (i + 1)) ∧
    H.Adj (u i) (v (i + 4)) ∧ H.Adj w (u i)

/-- Υ(π) for a red auxiliary path p0 (red) - p1 (green) - p2 (blue) - p3 (red). -/
theorem Vega.grRed {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (p0 p1 p2 p3 : ℕ)
    (h0 : p0 < i) (h1 : i ≤ p1) (h1' : p1 < 2 * i) (h1n : ν = true → p1 ≠ 2 * i - 1)
    (h2 : 2 * i ≤ p2) (h2' : p2 < 3 * i - 1) (h3 : p3 < i)
    (e01 : AA i p0 p1) (e12 : AA i p1 p2) (e23 : AA i p2 p3) :
    IsGr G ![Y.u, Y.b, Y.g p1, Y.g p2, Y.c] ![Y.x, Y.g p0, Y.w, Y.v, Y.g p3] Y.a := by
  have hi := Y.hi
  have r0 := Y.red p0 h0
  have r3 := Y.red p3 h3
  have g1 := Y.green p1 h1 h1' h1n
  have b2 := Y.blue p2 h2 h2'
  have a01 := Y.adj (by omega) (by omega) (by intro _; omega) h1n e01
  have a12 := Y.adj (by omega) (by omega) h1n (by intro _; omega) e12
  have a23 := Y.adj (by omega) (by omega) (by intro _; omega) (by intro _; omega) e23
  intro k; fin_cases k
  · exact ⟨Y.ub, Y.xb, Y.xc, Y.xa.symm⟩
  · exact ⟨g1.1, a01, r0.2.symm, r0.1⟩
  · exact ⟨a12, b2.2, Y.bw.symm, Y.wa.symm⟩
  · exact ⟨b2.1.symm, Y.vc, g1.2, Y.av⟩
  · exact ⟨Y.cu, r3.2.symm, a23.symm, r3.1⟩

/-- Υ(π) for a green auxiliary path p0 (green) - p1 (red) - p2 (blue) - p3 (green). -/
theorem Vega.grGreen {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (p0 p1 p2 p3 : ℕ)
    (h0 : i ≤ p0) (h0' : p0 < 2 * i) (h0n : ν = true → p0 ≠ 2 * i - 1) (h1 : p1 < i)
    (h2 : 2 * i ≤ p2) (h2' : p2 < 3 * i - 1)
    (h3 : i ≤ p3) (h3' : p3 < 2 * i) (h3n : ν = true → p3 ≠ 2 * i - 1)
    (e01 : AA i p0 p1) (e12 : AA i p1 p2) (e23 : AA i p2 p3) :
    IsGr G ![Y.a, Y.g p1, Y.g p2, Y.c, Y.v] ![Y.g p0, Y.w, Y.u, Y.g p3, Y.x] Y.b := by
  have hi := Y.hi
  have g0 := Y.green p0 h0 h0' h0n
  have g3 := Y.green p3 h3 h3' h3n
  have r1 := Y.red p1 h1
  have b2 := Y.blue p2 h2 h2'
  have a01 := Y.adj (by omega) (by omega) h0n (by intro _; omega) e01
  have a12 := Y.adj (by omega) (by omega) (by intro _; omega) (by intro _; omega) e12
  have a23 := Y.adj (by omega) (by omega) (by intro _; omega) h3n e23
  intro k; fin_cases k
  · exact ⟨r1.1, a01, g0.2.symm, g0.1⟩
  · exact ⟨a12, b2.2, Y.wa, Y.bw⟩
  · exact ⟨b2.1.symm, Y.cu.symm, r1.2, Y.ub.symm⟩
  · exact ⟨Y.vc.symm, g3.2.symm, a23.symm, g3.1⟩
  · exact ⟨Y.av.symm, Y.xa, Y.xc, Y.xb.symm⟩

/-- Υ(π) for a blue auxiliary path p0 (blue) - p1 (red) - p2 (green) - p3 (blue). -/
theorem Vega.grBlue {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (p0 p1 p2 p3 : ℕ)
    (h0 : 2 * i ≤ p0) (h0' : p0 < 3 * i - 1) (h1 : p1 < i)
    (h2 : i ≤ p2) (h2' : p2 < 2 * i) (h2n : ν = true → p2 ≠ 2 * i - 1)
    (h3 : 2 * i ≤ p3) (h3' : p3 < 3 * i - 1)
    (e01 : AA i p0 p1) (e12 : AA i p1 p2) (e23 : AA i p2 p3) :
    IsGr G ![Y.a, Y.g p1, Y.g p2, Y.b, Y.w] ![Y.g p0, Y.v, Y.u, Y.g p3, Y.x] Y.c := by
  have hi := Y.hi
  have b0 := Y.blue p0 h0 h0'
  have b3 := Y.blue p3 h3 h3'
  have r1 := Y.red p1 h1
  have g2 := Y.green p2 h2 h2' h2n
  have a01 := Y.adj (by omega) (by omega) (by intro _; omega) (by intro _; omega) e01
  have a12 := Y.adj (by omega) (by omega) (by intro _; omega) h2n e12
  have a23 := Y.adj (by omega) (by omega) h2n (by intro _; omega) e23
  intro k; fin_cases k
  · exact ⟨r1.1, a01, b0.2.symm, b0.1⟩
  · exact ⟨a12, g2.2, Y.av.symm, Y.vc.symm⟩
  · exact ⟨g2.1.symm, Y.ub, r1.2, Y.cu⟩
  · exact ⟨Y.bw, b3.2.symm, a23.symm, b3.1⟩
  · exact ⟨Y.wa, Y.xa, Y.xb, Y.xc.symm⟩

/-- The automorphism σ (x↔y, a↔u, b↔v, c↔w) of Υ_i^{0ν}. -/
def Vega.sigma {i : ℕ} {ν : Bool} (Y : Vega G i false ν) : Vega G i false ν where
  g := Y.g
  a := Y.u
  v := Y.b
  c := Y.w
  u := Y.a
  b := Y.v
  w := Y.c
  x := Y.y
  y := Y.x
  hi := Y.hi
  gg := Y.gg
  red j hj := (Y.red j hj).symm
  green j h1 h2 h3 := (Y.green j h1 h2 h3).symm
  blue j h1 h2 := (Y.blue j h1 h2).symm
  av := Y.ub
  vc := Y.bw
  cu := Y.wa
  ub := Y.av
  bw := Y.vc
  wa := Y.cu
  xa := Y.yu rfl
  xb := Y.yv rfl
  xc := Y.yw rfl
  yu _ := Y.xa
  yv _ := Y.xb
  yw _ := Y.xc
  yx _ := (Y.yx rfl).symm

/-- Reflection used by τ0: j ↦ 2i-1-j (mod 3i-1). -/
def rho0 (i j : ℕ) : ℕ := if j < 2 * i then 2 * i - 1 - j else 5 * i - 2 - j

/-- The automorphism τ0 (a↔b, u↔v, j ↦ 2i-1-j) of Υ_i^{μ0}. -/
def Vega.tau0 {i : ℕ} {μ : Bool} (Y : Vega G i μ false) : Vega G i μ false where
  g j := Y.g (rho0 i j)
  a := Y.b
  v := Y.u
  c := Y.c
  u := Y.v
  b := Y.a
  w := Y.w
  x := Y.x
  y := Y.y
  hi := Y.hi
  gg j k hj _ _ h1 h2 := by
    have hi := Y.hi
    apply Y.adj
    · unfold rho0; split_ifs <;> omega
    · unfold rho0; split_ifs <;> omega
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (by decide)
    · unfold AA rho0; split_ifs <;> omega
  red j hj := by
    have hi := Y.hi
    have e : rho0 i j = 2 * i - 1 - j := by unfold rho0; rw [if_pos (by omega)]
    rw [e]
    exact Y.green _ (by omega) (by omega) (fun h => absurd h (by decide))
  green j h1 h2 _ := by
    have hi := Y.hi
    have e : rho0 i j = 2 * i - 1 - j := by unfold rho0; rw [if_pos (by omega)]
    rw [e]
    exact Y.red _ (by omega)
  blue j h1 h2 := by
    have hi := Y.hi
    have e : rho0 i j = 5 * i - 2 - j := by unfold rho0; rw [if_neg (by omega)]
    rw [e]
    exact Y.blue _ (by omega) (by omega)
  av := Y.ub.symm
  vc := Y.cu.symm
  cu := Y.vc.symm
  ub := Y.av.symm
  bw := Y.wa.symm
  wa := Y.bw.symm
  xa := Y.xb
  xb := Y.xa
  xc := Y.xc
  yu h := Y.yv h
  yv h := Y.yu h
  yw h := Y.yw h
  yx h := Y.yx h

/-- Reflection used by τ1: j ↦ i-1-j (mod 3i-1) on Γ_i - (2i-1). -/
def rho1 (i j : ℕ) : ℕ := if j < i then i - 1 - j else if j = 2 * i - 1 then j else 4 * i - 2 - j

/-- The automorphism τ1 (b↔c, v↔w, j ↦ i-1-j) of Υ_i^{μ1}. -/
def Vega.tau1 {i : ℕ} {μ : Bool} (Y : Vega G i μ true) : Vega G i μ true where
  g j := Y.g (rho1 i j)
  a := Y.a
  v := Y.w
  c := Y.b
  u := Y.u
  b := Y.c
  w := Y.v
  x := Y.x
  y := Y.y
  hi := Y.hi
  gg j k hj hjn hkn h1 h2 := by
    have hi := Y.hi
    have hjn := hjn rfl
    have hkn := hkn rfl
    apply Y.adj
    · unfold rho1; split_ifs <;> omega
    · unfold rho1; split_ifs <;> omega
    · intro _; unfold rho1; split_ifs <;> omega
    · intro _; unfold rho1; split_ifs <;> omega
    · unfold AA rho1; split_ifs <;> omega
  red j hj := by
    have hi := Y.hi
    have e : rho1 i j = i - 1 - j := by unfold rho1; rw [if_pos hj]
    rw [e]
    exact Y.red _ (by omega)
  green j h1 h2 h3 := by
    have hi := Y.hi
    have h3 := h3 rfl
    have e : rho1 i j = 4 * i - 2 - j := by
      unfold rho1; rw [if_neg (by omega), if_neg h3]
    rw [e]
    exact Y.blue _ (by omega) (by omega)
  blue j h1 h2 := by
    have hi := Y.hi
    have e : rho1 i j = 4 * i - 2 - j := by
      unfold rho1; rw [if_neg (by omega), if_neg (by omega)]
    rw [e]
    exact Y.green _ (by omega) (by omega) (fun _ => by omega)
  av := Y.wa.symm
  vc := Y.bw.symm
  cu := Y.ub.symm
  ub := Y.cu.symm
  bw := Y.vc.symm
  wa := Y.av.symm
  xa := Y.xa
  xb := Y.xc
  xc := Y.xb
  yu h := Y.yu h
  yv h := Y.yw h
  yw h := Y.yv h
  yx h := Y.yx h

/-- Hexagon / x / y adjacency of the outer part (inr 0..7 = a v c u b w x y), as in H1. -/
def hexAdj (s t : Fin 8) : Prop :=
  (s.val < 6 ∧ t.val < 6 ∧ ((s.val + 1) % 6 = t.val ∨ (t.val + 1) % 6 = s.val)) ∨
  (s.val = 6 ∧ (t.val = 0 ∨ t.val = 4 ∨ t.val = 2 ∨ t.val = 7)) ∨
  (t.val = 6 ∧ (s.val = 0 ∨ s.val = 4 ∨ s.val = 2 ∨ s.val = 7)) ∨
  (s.val = 7 ∧ (t.val = 3 ∨ t.val = 1 ∨ t.val = 5 ∨ t.val = 6)) ∨
  (t.val = 7 ∧ (s.val = 3 ∨ s.val = 1 ∨ s.val = 5 ∨ s.val = 6))

/-- Adjacency between Andrásfai vertex j and outer vertex t, as in H1. -/
def colAdj (i j : ℕ) (t : Fin 8) : Prop :=
  ((t.val = 0 ∨ t.val = 3) ∧ j < i) ∨ ((t.val = 4 ∨ t.val = 1) ∧ i ≤ j ∧ j < 2 * i) ∨
  ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ j)

/-- The Vega graph Υ_i^{00} on ℕ ⊕ Fin 8 (Andrásfai indices j < 3i-1). -/
def vadj (i : ℕ) : ℕ ⊕ Fin 8 → ℕ ⊕ Fin 8 → Prop
  | Sum.inl j, Sum.inl k => AA i j k
  | Sum.inl j, Sum.inr t => colAdj i j t
  | Sum.inr t, Sum.inl j => colAdj i j t
  | Sum.inr s, Sum.inr t => hexAdj s t

/-- Vertices present in Υ_i^{μν}. -/
def pres (i : ℕ) (μ ν : Bool) : ℕ ⊕ Fin 8 → Prop
  | Sum.inl j => j < 3 * i - 1 ∧ (ν = true → j ≠ 2 * i - 1)
  | Sum.inr t => t.val < 7 ∨ μ = false

/-- The vertex map of a Vega copy. -/
def Vega.emb {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) : ℕ ⊕ Fin 8 → V
  | Sum.inl j => Y.g j
  | Sum.inr t => ![Y.a, Y.v, Y.c, Y.u, Y.b, Y.w, Y.x, Y.y] t

theorem Vega.outer_adj {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (s t : Fin 8)
    (hp : pres i μ ν (Sum.inr s)) (hs : pres i μ ν (Sum.inr t)) (h : hexAdj s t) :
    G.Adj (Y.emb (Sum.inr s)) (Y.emb (Sum.inr t)) := by
  obtain ⟨s, hs'⟩ := s
  obtain ⟨t, ht'⟩ := t
  have hy : ∀ r, pres i μ ν (Sum.inr r) → r.val = 7 → μ = false := by
    intro r hr h7; rcases hr with hr | hr
    · omega
    · exact hr
  have hyp := hy _ hp
  have hys := hy _ hs
  simp only [Vega.emb]
  unfold hexAdj at h
  simp only at h hyp hys
  rcases h with ⟨h1, h2, h3 | h3⟩ | ⟨h1, h2 | h2 | h2 | h2⟩ | ⟨h1, h2 | h2 | h2 | h2⟩ |
      ⟨h1, h2 | h2 | h2 | h2⟩ | ⟨h1, h2 | h2 | h2 | h2⟩
  · interval_cases s <;> subst h3
    exacts [Y.av, Y.vc, Y.cu, Y.ub, Y.bw, Y.wa.symm.symm]
  · interval_cases t <;> subst h3
    exacts [Y.av.symm, Y.vc.symm, Y.cu.symm, Y.ub.symm, Y.bw.symm, Y.wa.symm]
  all_goals subst h1; subst h2
  exacts [Y.xa, Y.xb, Y.xc, (Y.yx (hys rfl)).symm, Y.xa.symm, Y.xb.symm, Y.xc.symm,
    Y.yx (hyp rfl), (Y.yu (hyp rfl)), Y.yv (hyp rfl), Y.yw (hyp rfl), Y.yx (hyp rfl),
    (Y.yu (hys rfl)).symm, (Y.yv (hys rfl)).symm, (Y.yw (hys rfl)).symm, (Y.yx (hys rfl)).symm]

theorem Vega.emb_adj {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) :
    ∀ p s, pres i μ ν p → pres i μ ν s → vadj i p s → G.Adj (Y.emb p) (Y.emb s) := by
  have hi := Y.hi
  have col : ∀ j t, pres i μ ν (Sum.inl j) → colAdj i j t →
      G.Adj (Y.g j) (![Y.a, Y.v, Y.c, Y.u, Y.b, Y.w, Y.x, Y.y] t) := by
    intro j t ⟨hj, hjn⟩ h
    rcases h with ⟨ht, h1⟩ | ⟨ht, h1, h2⟩ | ⟨ht, h1⟩
    · rcases ht with ht | ht
      · have e : t = 0 := Fin.ext ht
        subst e; exact (Y.red j h1).1.symm
      · have e : t = 3 := Fin.ext ht
        subst e; exact (Y.red j h1).2.symm
    · rcases ht with ht | ht
      · have e : t = 4 := Fin.ext ht
        subst e; exact (Y.green j h1 h2 hjn).1.symm
      · have e : t = 1 := Fin.ext ht
        subst e; exact (Y.green j h1 h2 hjn).2.symm
    · rcases ht with ht | ht
      · have e : t = 2 := Fin.ext ht
        subst e; exact (Y.blue j h1 hj).1.symm
      · have e : t = 5 := Fin.ext ht
        subst e; exact (Y.blue j h1 hj).2.symm
  rintro (j | s) (k | t) hp hs h
  · exact Y.adj hp.1 hs.1 hp.2 hs.2 h
  · exact col j t hp h
  · exact (col k s hs h).symm
  · exact Y.outer_adj s t hp hs h

/-- Enlargement used in LPR Lemma 4.21, first case: q ~ c, w, all red; z ~ c, w, all green.
Then Υ_{i+1}^{μ1} sits in G (new red = q, old blue, z; new green = old red; new blue = old green;
new hexagon a' v' c' u' b' w' = c u b w a v). -/
def Vega.enlarge1 {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q z : V)
    (hqc : G.Adj q Y.c) (hqw : G.Adj q Y.w) (hq : ∀ j, j < i → G.Adj q (Y.g j))
    (hzc : G.Adj z Y.c) (hzw : G.Adj z Y.w)
    (hz : ∀ j, i ≤ j → j < 2 * i → G.Adj z (Y.g j)) : Vega G (i + 1) μ true where
  g J := if J = 0 then q else if J < i then Y.g (2 * i - 1 + J) else if J = i then z
    else if J ≤ 2 * i then Y.g (J - i - 1) else if J = 2 * i + 1 then q else Y.g (J - i - 2)
  a := Y.c
  v := Y.u
  c := Y.b
  u := Y.w
  b := Y.a
  w := Y.v
  x := Y.x
  y := Y.y
  hi := by have := Y.hi; omega
  gg J K hJ hJn hKn h1 h2 := by
    have hi := Y.hi
    have hJn := hJn rfl
    have hKn := hKn rfl
    have nf : (false = true → False) := fun h => Bool.false_ne_true h
    split_ifs <;> first
      | (exfalso; omega)
      | exact Y.adj (by omega) (by omega) (fun h => (nf h).elim) (fun h => (nf h).elim)
          (by unfold AA; omega)
      | exact hq _ (by omega) | exact (hq _ (by omega)).symm
      | exact hz _ (by omega) (by omega) | exact (hz _ (by omega) (by omega)).symm
  red J hJ := by
    have hi := Y.hi
    split_ifs
    · exact ⟨hqc.symm, hqw.symm⟩
    · exact Y.blue _ (by omega) (by omega)
    · exact ⟨hzc.symm, hzw.symm⟩
    all_goals exfalso; omega
  green J h1 h2 h3 := by
    have hi := Y.hi
    have h3 := h3 rfl
    split_ifs
    all_goals first | (exfalso; omega) | exact Y.red _ (by omega)
  blue J h1 h2 := by
    have hi := Y.hi
    split_ifs
    all_goals (first | (exfalso; omega) | exact Y.green _ (by omega) (by omega) (fun h => (Bool.false_ne_true h).elim))
  av := Y.cu
  vc := Y.ub
  cu := Y.bw
  ub := Y.wa
  bw := Y.av
  wa := Y.vc
  xa := Y.xc
  xb := Y.xa
  xc := Y.xb
  yu h := Y.yw h
  yv h := Y.yu h
  yw h := Y.yv h
  yx h := Y.yx h

/-- Enlargement used in LPR Lemma 4.21, second case: q ~ c, w, all red; z ~ b, v, q, all blue.
New red = z, old green; new green = q, old blue; new blue = old red;
new hexagon a' v' c' u' b' w' = b w a v c u. -/
def Vega.enlarge2 {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q z : V)
    (hqc : G.Adj q Y.c) (hqw : G.Adj q Y.w) (hq : ∀ j, j < i → G.Adj q (Y.g j))
    (hzb : G.Adj z Y.b) (hzv : G.Adj z Y.v) (hzq : G.Adj z q)
    (hz : ∀ j, 2 * i ≤ j → j < 3 * i - 1 → G.Adj z (Y.g j)) : Vega G (i + 1) μ true where
  g J := if J = 0 then z else if J ≤ i then Y.g (i + J - 1) else if J = i + 1 then q
    else if J ≤ 2 * i then Y.g (J + i - 2) else if J = 2 * i + 1 then q else Y.g (J - 2 * i - 2)
  a := Y.b
  v := Y.w
  c := Y.a
  u := Y.v
  b := Y.c
  w := Y.u
  x := Y.x
  y := Y.y
  hi := by have := Y.hi; omega
  gg J K hJ hJn hKn h1 h2 := by
    have hi := Y.hi
    have hJn := hJn rfl
    have hKn := hKn rfl
    have nf : (false = true → False) := fun h => Bool.false_ne_true h
    split_ifs <;> first
      | (exfalso; omega)
      | exact Y.adj (by omega) (by omega) (fun h => (nf h).elim) (fun h => (nf h).elim)
          (by unfold AA; omega)
      | exact hq _ (by omega) | exact (hq _ (by omega)).symm
      | exact hz _ (by omega) (by omega) | exact (hz _ (by omega) (by omega)).symm
      | exact hzq | exact hzq.symm
  red J hJ := by
    have hi := Y.hi
    split_ifs
    · exact ⟨hzb.symm, hzv.symm⟩
    · exact Y.green _ (by omega) (by omega) (fun h => (Bool.false_ne_true h).elim)
    all_goals exfalso; omega
  green J h1 h2 h3 := by
    have hi := Y.hi
    have h3 := h3 rfl
    split_ifs
    all_goals (first | (exfalso; omega) | exact ⟨hqc.symm, hqw.symm⟩ | exact Y.blue _ (by omega) (by omega))
  blue J h1 h2 := by
    have hi := Y.hi
    split_ifs
    all_goals first | (exfalso; omega) | exact Y.red _ (by omega)
  av := Y.bw
  vc := Y.wa
  cu := Y.av
  ub := Y.vc
  bw := Y.cu
  wa := Y.ub
  xa := Y.xb
  xb := Y.xc
  xc := Y.xa
  yu h := Y.yv h
  yv h := Y.yw h
  yw h := Y.yu h
  yx h := Y.yx h

/-- 𝒟_2 on a hexagon h0 - h1 - h2 - h3 - h4 - h5 - h0: some vertex is adjacent to h0, h2, h4 or
to h1, h3, h5. -/
theorem hex_D2 {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcf : H.CliqueFree 3)
    (hmin : ∀ v : W, Fintype.card W < 3 * (H.neighborSet v).ncard)
    (h0 h1 h2 h3 h4 h5 : W) (e01 : H.Adj h0 h1) (e12 : H.Adj h1 h2) (e23 : H.Adj h2 h3)
    (e34 : H.Adj h3 h4) (e45 : H.Adj h4 h5) (e50 : H.Adj h5 h0) :
    ∃ z, (H.Adj z h0 ∧ H.Adj z h2 ∧ H.Adj z h4) ∨ (H.Adj z h1 ∧ H.Adj z h3 ∧ H.Adj z h5) := by
  let xs6 : Fin 6 → W := fun k => match k.val with
    | 0 => h0 | 1 => h2 | 2 => h4 | 3 => h3 | 4 => h5 | _ => h1
  obtain ⟨z, hz⟩ := prop_D H hmin 2 (by omega) xs6
  rw [card_filter_fin6] at hz
  have hcls := c6_indep_ge_three
    (decide (H.Adj h0 z)) (decide (H.Adj h2 z)) (decide (H.Adj h4 z))
    (decide (H.Adj h3 z)) (decide (H.Adj h5 z)) (decide (H.Adj h1 z))
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e50.symm)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e01)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e23)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e12.symm)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e34.symm)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e45)
    hz
  rcases hcls with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩
  · exact ⟨z, Or.inl ⟨(of_decide_eq_true a1).symm, (of_decide_eq_true a2).symm,
      (of_decide_eq_true a3).symm⟩⟩
  · exact ⟨z, Or.inr ⟨(of_decide_eq_true b3).symm, (of_decide_eq_true b1).symm,
      (of_decide_eq_true b2).symm⟩⟩

/-- LPR Lemma 4.21 (case c, w, 0): a vertex adjacent to c, w, 0 of Υ_i^{μ0} yields Υ_{i+1}^{μ1}. -/
theorem Vega.l421 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q : V)
    (hqc : G.Adj q Y.c) (hqw : G.Adj q Y.w) (hq0 : G.Adj q (Y.g 0)) :
    Nonempty (Vega G (i + 1) μ true) := by
  have hi := Y.hi
  have nf : (false = true → 2 * i - 1 ≠ 2 * i - 1) := fun h => (Bool.false_ne_true h).elim
  have hq : ∀ j, j < i → G.Adj q (Y.g j) := fun j hj => Y.l419a hcf hcube q hqc hqw 0 hq0 j
    (by omega) hj
  have g2 := Y.green (2 * i - 1) (by omega) (by omega) nf
  obtain ⟨z, ⟨z1, z2, z3⟩ | ⟨z1, z2, z3⟩⟩ := hex_D2 G hcf hmin Y.v (Y.g (2 * i - 1)) Y.b Y.w q Y.c
    g2.2 g2.1.symm Y.bw hqw.symm hqc Y.vc.symm
  · -- z ~ v, b, q
    have hqi : ¬ G.Adj q (Y.g i) := fun h =>
      not_adj_both hcf hq0 h (Y.gg i 0 (by omega) (fun h => (Bool.false_ne_true h).elim)
        (fun h => (Bool.false_ne_true h).elim) (by omega) (by omega)).symm
    have gi := Y.green i (by omega) (by omega) (fun h => (Bool.false_ne_true h).elim)
    have b2i := Y.blue (2 * i) (by omega) (by omega)
    have e : G.Adj (Y.g (2 * i)) (Y.g i) := Y.gg _ _ (by omega)
      (fun h => (Bool.false_ne_true h).elim) (fun h => (Bool.false_ne_true h).elim)
      (by omega) (by omega)
    have hz2 : G.Adj z (Y.g (2 * i)) := by
      refine cube_force G hcube ![z, Y.c, Y.w, Y.g i] ![Y.g (2 * i), Y.b, Y.v, q] ?_
        (not_adj_both hcf Y.cu.symm Y.ub) (not_adj_both hcf Y.wa.symm Y.av)
        (fun h => hqi h.symm)
      intro p r hpr; fin_cases p <;> fin_cases r
      all_goals first | exact absurd rfl hpr | skip
      exacts [z2, z1, z3, b2i.1, Y.vc.symm, hqc.symm, b2i.2, Y.bw.symm, hqw.symm, e.symm,
        gi.1.symm, gi.2.symm]
    exact ⟨Y.enlarge2 q z hqc hqw hq z2 z1 z3
      (fun j h1 h2 => Y.l417b hcf hcube z z2 z1 (2 * i) le_rfl hz2 j h1 h2)⟩
  · -- z ~ 2i-1, w, c
    have hz : ∀ j, i ≤ j → j < 2 * i → G.Adj z (Y.g j) := fun j h1 h2 =>
      Y.l419b hcf hcube z z3 z2 (2 * i - 1) (by omega) nf z1 j h1 (by omega)
    exact ⟨Y.enlarge1 q z hqc hqw hq z3 z2 hz⟩

/-- LPR Lemma 4.21 (case c, w, 2i-1), via τ0. -/
theorem Vega.l421' [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q : V)
    (hqc : G.Adj q Y.c) (hqw : G.Adj q Y.w) (hq : G.Adj q (Y.g (2 * i - 1))) :
    Nonempty (Vega G (i + 1) μ true) := by
  have hi := Y.hi
  have e : rho0 i 0 = 2 * i - 1 := by unfold rho0; rw [if_pos (by omega)]; omega
  exact Y.tau0.l421 hcf hcube hmin q hqc hqw (by show G.Adj q (Y.g (rho0 i 0)); rw [e]; exact hq)

/-- Filling the missing vertex 2i-1 of Υ_i^{μ1} by a vertex adjacent to b, v and all red. -/
def Vega.fill {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (q : V)
    (hb : G.Adj q Y.b) (hv : G.Adj q Y.v) (hred : ∀ j, j < i → G.Adj q (Y.g j)) :
    Vega G i μ false where
  g j := if j = 2 * i - 1 then q else Y.g j
  a := Y.a
  v := Y.v
  c := Y.c
  u := Y.u
  b := Y.b
  w := Y.w
  x := Y.x
  y := Y.y
  hi := Y.hi
  gg j k hj _ _ h1 h2 := by
    have hi := Y.hi
    split_ifs with hjj hkk hkk
    · exfalso; omega
    · exact hred k (by omega)
    · exfalso; omega
    · exact Y.gg j k hj (fun _ => hjj) (fun _ => hkk) h1 h2
  red j hj := by
    have hi := Y.hi
    rw [if_neg (by omega)]
    exact Y.red j hj
  green j h1 h2 _ := by
    split_ifs with hjj
    · exact ⟨hb.symm, hv.symm⟩
    · exact Y.green j h1 h2 (fun _ => hjj)
  blue j h1 h2 := by
    have hi := Y.hi
    rw [if_neg (by omega)]
    exact Y.blue j h1 h2
  av := Y.av
  vc := Y.vc
  cu := Y.cu
  ub := Y.ub
  bw := Y.bw
  wa := Y.wa
  xa := Y.xa
  xb := Y.xb
  xc := Y.xc
  yu := Y.yu
  yv := Y.yv
  yw := Y.yw
  yx := Y.yx

/-- LPR Corollary 4.18 (case b, v, i-1). -/
theorem Vega.c418 (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ : Bool}
    (Y : Vega G i μ true) (q : V) (hb : G.Adj q Y.b) (hv : G.Adj q Y.v)
    (hq : G.Adj q (Y.g (i - 1))) : Nonempty (Vega G i μ false) := by
  have hi := Y.hi
  exact ⟨Y.fill q hb hv (fun j hj => Y.l417a hcf hcube q hb hv (i - 1) (by omega) hq j
    (by omega))⟩

/-- LPR Corollary 4.18 (case c, w, 0), via τ1. -/
theorem Vega.c418' (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ : Bool}
    (Y : Vega G i μ true) (q : V) (hc : G.Adj q Y.c) (hw : G.Adj q Y.w)
    (hq : G.Adj q (Y.g 0)) : Nonempty (Vega G i μ false) := by
  have hi := Y.hi
  have e : rho1 i (i - 1) = 0 := by unfold rho1; rw [if_pos (by omega)]; omega
  exact Y.tau1.c418 hcf hcube q hc hw (by show G.Adj q (Y.g (rho1 i (i - 1))); rw [e]; exact hq)

/-- Adding the missing vertex y to Υ_i^{1ν}. -/
def Vega.addY {i : ℕ} {ν : Bool} (Y : Vega G i true ν) (q : V) (hu : G.Adj q Y.u)
    (hv : G.Adj q Y.v) (hw : G.Adj q Y.w) (hx : G.Adj q Y.x) : Vega G i false ν where
  g := Y.g
  a := Y.a
  v := Y.v
  c := Y.c
  u := Y.u
  b := Y.b
  w := Y.w
  x := Y.x
  y := q
  hi := Y.hi
  gg := Y.gg
  red := Y.red
  green := Y.green
  blue := Y.blue
  av := Y.av
  vc := Y.vc
  cu := Y.cu
  ub := Y.ub
  bw := Y.bw
  wa := Y.wa
  xa := Y.xa
  xb := Y.xb
  xc := Y.xc
  yu _ := hu
  yv _ := hv
  yw _ := hw
  yx _ := hx

/-- LPR Lemma 4.16(a) consequence: in Υ_i^{1ν}, a vertex adjacent to u, v, w gives Υ_i^{0ν}. -/
theorem Vega.l416y (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {ν : Bool}
    (Y : Vega G i true ν) (q : V) (hu : G.Adj q Y.u) (hv : G.Adj q Y.v) (hw : G.Adj q Y.w) :
    Nonempty (Vega G i false ν) :=
  ⟨Y.addY q hu hv hw (Y.l416a hcf hcube q hu hv hw)⟩

/-- Number of vertices of Υ_i^{μν}. -/
def vsize (i : ℕ) (μ ν : Bool) : ℕ := 3 * i + 7 - (if μ then 1 else 0) - (if ν then 1 else 0)

/-- G contains no Vega graph with more vertices than Υ_i^{μν}. -/
def VegaMax (H : SimpleGraph V) (i : ℕ) (μ ν : Bool) : Prop :=
  ∀ i' μ' ν', vsize i μ ν < vsize i' μ' ν' → IsEmpty (Vega H i' μ' ν')

/-- The Grötzsch-level lemmas of LPR §4.3, proved in E128H1_base.lean (`beautiful`, `lemma410`,
`lemma411`, `lemma412`, `lemma413`, `lemma414`, `lemma46`, `lemma47`), bundled as a hypothesis. -/
structure GrFacts (H : SimpleGraph V) : Prop where
  beaut : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ (k : Fin 5) (q : V),
    H.Adj q (u k) → H.Adj q (u (k + 1)) → H.Adj q (u (k + 3))
  l410 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ q : V,
    H.Adj q (u 3) → H.Adj q (u 2) → (∀ k, H.Adj q (u k)) ∨ H.Adj q (v 0)
  l411 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ q : V,
    H.Adj q (u 0) → H.Adj q (v 3) → ¬ H.Adj q (u 3) →
    H.Adj q (v 0) ∧ ∃ t, H.Adj t (u 3) ∧ H.Adj t (u 4) ∧ H.Adj t (v 1) ∧ H.Adj q t
  l412 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ q : V,
    H.Adj q (u 0) → H.Adj q (v 3) →
    H.Adj q (u 1) ∨ H.Adj q (v 0) ∨
      ∃ A2 B0 : V, H.Adj q A2 ∧ H.Adj q B0 ∧
        (H.Adj A2 (v 0) ∧ H.Adj A2 (v 2) ∧ H.Adj A2 w) ∧
        (H.Adj B0 (v 1) ∧ H.Adj B0 (v 4) ∧ H.Adj B0 (u 1) ∧ H.Adj B0 (u 4))
  l413 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ t1 t2 t3 : V,
    H.Adj t1 (u 0) → H.Adj t1 (u 1) → H.Adj t1 (v 3) →
    H.Adj t2 (u 3) → H.Adj t2 (u 4) → H.Adj t2 (v 1) →
    H.Adj t3 (u 1) → H.Adj t3 (u 2) → H.Adj t3 (v 4) → False
  l414 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ A1 : V,
    H.Adj A1 (v 4) → H.Adj A1 (v 2) → H.Adj A1 w → ∀ T : V,
    H.Adj T A1 → H.Adj T (u 4) → H.Adj T (v 1) → ∀ q : V,
    H.Adj q (u 3) → H.Adj q (v 3) → H.Adj q T → ∀ t0 : V,
    H.Adj t0 (u 2) → H.Adj t0 (u 3) → H.Adj t0 (v 0) → False
  l46 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ A B : V,
    H.Adj A (v 1) → H.Adj A (v 4) → H.Adj A w →
    H.Adj B (v 0) → H.Adj B (v 2) → H.Adj B (u 0) → H.Adj B (u 2) → ¬ H.Adj A B →
    ∃ t, H.Adj t A ∧ H.Adj t (u 1) ∧ H.Adj t (v 3) ∧ H.Adj t B
  l47 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ A B : V,
    H.Adj A (v 1) → H.Adj A (v 4) → H.Adj A (u 1) → H.Adj A (u 4) →
    H.Adj B (v 0) → H.Adj B (v 2) → H.Adj B (u 0) → H.Adj B (u 2) → ¬ H.Adj A B →
    ∃ t, H.Adj t A ∧ H.Adj t (v 3) ∧ H.Adj t w ∧ H.Adj t B
  l45 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ (k : Fin 5) (u' : V),
    H.Adj u' (v (k + 1)) → H.Adj u' (v (k + 4)) → H.Adj w u' → ∀ c' : V,
    H.Adj c' (u (k + 2)) → H.Adj c' (u (k + 3)) → H.Adj c' u'
  l48 : ∀ {v u : Fin 5 → V} {w : V}, IsGr H v u w → ∀ Uq Vq : V,
    H.Adj Uq (u 3) → H.Adj Uq (u 2) → H.Adj Vq Uq → H.Adj Vq (v 0) →
    H.Adj Vq (v 3) ∨ H.Adj Vq (v 2) ∨
      ∃ X Y : V, H.Adj Vq X ∧ H.Adj Vq Y ∧
        (H.Adj X (v 2) ∧ H.Adj X (v 4) ∧ H.Adj X (u 2) ∧ H.Adj X (u 4)) ∧
        (H.Adj Y (v 1) ∧ H.Adj Y (v 3) ∧ H.Adj Y (u 1) ∧ H.Adj Y (u 3))

theorem IsGr.rotV {v u : Fin 5 → V} {w : V} (h : IsGr G v u w) (k : Fin 5) :
    IsGr G (fun i => v (i + k)) (fun i => u (i + k)) w := by
  intro i
  have e1 : i + k + 1 = i + 1 + k := add_right_comm i k 1
  have e4 : i + k + 4 = i + 4 + k := add_right_comm i k 4
  obtain ⟨h1, h2, h3, h4⟩ := h (i + k)
  rw [e1] at h1 h2
  rw [e4] at h3
  exact ⟨h1, h2, h3, h4⟩

/-- t ∈ Ext(Υ, u_m): t is adjacent to u (m+2), u (m+3), v m. -/
def InExt (H : SimpleGraph V) (v u : Fin 5 → V) (m : Fin 5) (t : V) : Prop :=
  H.Adj t (u (m + 2)) ∧ H.Adj t (u (m + 3)) ∧ H.Adj t (v m)

/-- Lemma 4.10 at any index: q ~ u (k+3), u (k+2) ⟹ q adjacent to all shadows or q ~ v k. -/
theorem GrFacts.l410r (F : GrFacts G) {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (k : Fin 5) (q : V) (h3 : G.Adj q (u (k + 3))) (h2 : G.Adj q (u (k + 2))) :
    (∀ j, G.Adj q (u j)) ∨ G.Adj q (v k) := by
  have e3 : (3 : Fin 5) + k = k + 3 := add_comm _ _
  have e2 : (2 : Fin 5) + k = k + 2 := add_comm _ _
  have e0 : (0 : Fin 5) + k = k := zero_add _
  rcases F.l410 (hY.rotV k) q (by simp only [e3]; exact h3) (by simp only [e2]; exact h2) with
    h | h
  · left; intro j
    have := h (j - k)
    simpa only [sub_add_cancel] using this
  · right; simpa only [e0] using h

/-- Lemma 4.13 at any index: Ext(u (k+3)), Ext(u (k+1)), Ext(u (k+4)) are not all non-empty. -/
theorem GrFacts.l413r (F : GrFacts G) {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (k : Fin 5) (t1 t2 t3 : V) (h1 : InExt G v u (k + 3) t1) (h2 : InExt G v u (k + 1) t2)
    (h3 : InExt G v u (k + 4) t3) : False := by
  obtain ⟨a1, a2, a3⟩ := h1
  obtain ⟨b1, b2, b3⟩ := h2
  obtain ⟨c1, c2, c3⟩ := h3
  have i1 : ∀ j : Fin 5, j + 3 + 2 = j := by decide
  have i2 : ∀ j : Fin 5, j + 3 + 3 = j + 1 := by decide
  have i3 : ∀ j : Fin 5, j + 1 + 2 = j + 3 := by decide
  have i4 : ∀ j : Fin 5, j + 1 + 3 = j + 4 := by decide
  have i5 : ∀ j : Fin 5, j + 4 + 2 = j + 1 := by decide
  have i6 : ∀ j : Fin 5, j + 4 + 3 = j + 2 := by decide
  rw [i1] at a1; rw [i2] at a2; rw [i3] at b1; rw [i4] at b2; rw [i5] at c1; rw [i6] at c2
  have c : ∀ j : Fin 5, j + k = k + j := fun j => add_comm j k
  exact F.l413 (hY.rotV k) t1 t2 t3
    (by simp only [c, add_zero]; exact a1) (by simp only [c]; exact a2) (by simp only [c]; exact a3)
    (by simp only [c]; exact b1) (by simp only [c]; exact b2) (by simp only [c]; exact b3)
    (by simp only [c]; exact c1) (by simp only [c]; exact c2) (by simp only [c]; exact c3)

/-- LPR Lemma 4.23, first case, i ≥ 3 part: if q ~ x and q ~ m or m+1 with i ≤ m, m+1 ≤ 2i-2,
then q ~ u and q ~ w (so q has no red and no blue neighbour). -/
theorem Vega.l423c1 (F : GrFacts G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (m : ℕ)
    (hm1 : i ≤ m) (hm2 : m + 1 ≤ 2 * i - 2) (q : V) (hx : G.Adj q Y.x)
    (hm : G.Adj q (Y.g m) ∨ G.Adj q (Y.g (m + 1))) : G.Adj q Y.u ∧ G.Adj q Y.w := by
  have hi := Y.hi
  have hC := Y.grGreen (m + 1) (m - i + 1) (m + i) m (by omega) (by omega) (by intro _; omega)
    (by omega) (by omega) (by omega) hm1 (by omega) (by intro _; omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have b1 := Y.blue (m + 1 + i) (by omega) (by omega)
  have r1 := Y.red (m - i) (by omega)
  have e1 : G.Adj (Y.g (m + 1 + i)) (Y.g (m + 1)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e2 : G.Adj (Y.g m) (Y.g (m - i)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have tU3 : InExt G ![Y.a, Y.g (m - i + 1), Y.g (m + i), Y.c, Y.v]
      ![Y.g (m + 1), Y.w, Y.u, Y.g m, Y.x] 3 (Y.g (m + 1 + i)) := ⟨e1, b1.2.symm, b1.1.symm⟩
  have tU0 : InExt G ![Y.a, Y.g (m - i + 1), Y.g (m + i), Y.c, Y.v]
      ![Y.g (m + 1), Y.w, Y.u, Y.g m, Y.x] 0 (Y.g (m - i)) := ⟨r1.2.symm, e2.symm, r1.1.symm⟩
  rcases hm with hm | hm
  · rcases F.l410r hC 1 q hx hm with h | h
    · exact ⟨h 2, h 1⟩
    · exact (F.l413r hC 2 _ _ q tU0 tU3 ⟨hm, hx, h⟩).elim
  · rcases F.l410r hC 2 q hm hx with h | h
    · exact ⟨h 2, h 1⟩
    · exact (F.l413r hC 4 q _ _ ⟨hx, hm, h⟩ tU0 tU3).elim

/-- The exceptional isomorphism ϱ : Υ_2^{μν} → Υ_2^{νμ} (c↔2, u↔b, 1↔w, x↔0, 3↔y). -/
def Vega.rho2 {μ ν : Bool} (Y : Vega G 2 μ ν) : Vega G 2 ν μ where
  g j := if j = 0 then Y.x else if j = 1 then Y.w else if j = 2 then Y.c else if j = 3 then Y.y
    else Y.g j
  a := Y.a
  v := Y.v
  c := Y.g 2
  u := Y.b
  b := Y.u
  w := Y.g 1
  x := Y.g 0
  y := Y.g 3
  hi := le_rfl
  gg j k hj hjn hkn h1 h2 := by
    have b4 := Y.blue 4 (by omega) (by omega)
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · have hj' : j = 2 ∨ j = 3 := by omega
      rcases hj' with rfl | rfl
      · exact Y.xc.symm
      · have hμ : μ = false := by
          cases μ
          · rfl
          · exact absurd rfl (hjn rfl)
        exact Y.yx hμ
    · have hj' : j = 3 ∨ j = 4 := by omega
      rcases hj' with rfl | rfl
      · have hμ : μ = false := by
          cases μ
          · rfl
          · exact absurd rfl (hjn rfl)
        exact Y.yw hμ
      · exact b4.2.symm
    · have hj' : j = 4 := by omega
      subst hj'
      exact b4.1.symm
  red j hj := by
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact ⟨Y.xa.symm, Y.xb.symm⟩
    · exact ⟨Y.wa.symm, Y.bw⟩
  green j h1 h2 h3 := by
    have hj' : j = 2 ∨ j = 3 := by omega
    rcases hj' with rfl | rfl
    · exact ⟨Y.cu.symm, Y.vc⟩
    · have hμ : μ = false := by
        cases μ
        · rfl
        · exact absurd rfl (h3 rfl)
      exact ⟨(Y.yu hμ).symm, (Y.yv hμ).symm⟩
  blue j h1 h2 := by
    have hj' : j = 4 := by omega
    subst hj'
    have e1 : G.Adj (Y.g 4) (Y.g 2) :=
      Y.gg 4 2 (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
    have e2 : G.Adj (Y.g 4) (Y.g 1) :=
      Y.gg 4 1 (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
    exact ⟨e1.symm, e2.symm⟩
  av := Y.av
  vc := (Y.green 2 (by omega) (by omega) (by intro _; omega)).2
  cu := (Y.green 2 (by omega) (by omega) (by intro _; omega)).1.symm
  ub := Y.ub.symm
  bw := (Y.red 1 (by omega)).2
  wa := (Y.red 1 (by omega)).1.symm
  xa := (Y.red 0 (by omega)).1.symm
  xb := (Y.red 0 (by omega)).2.symm
  xc := (Y.gg 2 0 (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)).symm
  yu hν := (Y.green 3 (by omega) (by omega)
    (by intro h; rw [hν] at h; exact absurd h (by decide))).1.symm
  yv hν := (Y.green 3 (by omega) (by omega)
    (by intro h; rw [hν] at h; exact absurd h (by decide))).2.symm
  yw hν := Y.gg 3 1 (by omega) (by intro h; rw [hν] at h; exact absurd h (by decide))
    (by intro _; omega) (by omega) (by omega)
  yx hν := Y.gg 3 0 (by omega) (by intro h; rw [hν] at h; exact absurd h (by decide))
    (by intro _; omega) (by omega) (by omega)

/-- LPR Lemma 4.22, blue case: in a maximal Υ_2^{μν}, no vertex is adjacent to x, 1 and 2. -/
theorem Vega.l422blue [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {μ ν : Bool} (Y : Vega G 2 μ ν) (hM : VegaMax G 2 μ ν) (q : V)
    (hx : G.Adj q Y.x) (h1 : G.Adj q (Y.g 1)) (h2 : G.Adj q (Y.g 2)) : False := by
  cases μ with
  | false =>
    obtain ⟨Z'⟩ := Y.rho2.l421 hcf hcube hmin q h2 h1 hx
    exact (hM 3 ν true (by unfold vsize; cases ν <;> simp)).false Z'
  | true =>
    obtain ⟨Z'⟩ := Y.rho2.c418' hcf hcube q h2 h1 hx
    exact (hM 2 ν false (by unfold vsize; cases ν <;> simp)).false Z'

/-- LPR Lemma 4.23, first case: q ~ x and q ~ a green m ∈ [i, 2i-2] ⟹ q has no red and no blue
neighbour in a maximal Vega copy. -/
theorem Vega.l423case1 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (F : GrFacts G) (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (hx : G.Adj q Y.x) (m : ℕ) (hm1 : i ≤ m) (hm2 : m ≤ 2 * i - 2) (hqm : G.Adj q (Y.g m)) :
    (∀ j, j < i → ¬ G.Adj q (Y.g j)) ∧ (∀ j, 2 * i ≤ j → j < 3 * i - 1 → ¬ G.Adj q (Y.g j)) := by
  have hi := Y.hi
  by_cases hi3 : 3 ≤ i
  · have huw : G.Adj q Y.u ∧ G.Adj q Y.w := by
      by_cases hm3 : m + 1 ≤ 2 * i - 2
      · exact Y.l423c1 F m hm1 hm3 q hx (Or.inl hqm)
      · exact Y.l423c1 F (m - 1) (by omega) (by omega) q hx
          (Or.inr (by rw [show m - 1 + 1 = m by omega]; exact hqm))
    refine ⟨fun j hj h => ?_, fun j h1 h2 h => ?_⟩
    · exact not_adj_both hcf huw.1 h (Y.red j hj).2
    · exact not_adj_both hcf huw.2 h (Y.blue j h1 h2).2
  · have hi2 : i = 2 := by omega
    subst hi2
    have hm' : m = 2 := by omega
    subst hm'
    refine ⟨fun j hj h => ?_, fun j h1 h2 h => ?_⟩
    · have hj' : j = 0 ∨ j = 1 := by omega
      rcases hj' with rfl | rfl
      · exact not_adj_both hcf hqm h
          (Y.gg 2 0 (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega))
      · exact Y.l422blue hcf hcube hmin hM q hx h hqm
    · have hj' : j = 4 := by omega
      subst hj'
      exact not_adj_both hcf hqm h
        (Y.gg 4 2 (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)).symm

/-- LPR Lemma 4.22, red case with μ = 1: in a maximal Υ_2^{10}, no vertex is adjacent to x, 3, 4
(reduced to the blue case by ϱ and σ∘τ1). -/
theorem Vega.l422red [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (Y : Vega G 2 true false) (hM : VegaMax G 2 true false) (q : V)
    (hx : G.Adj q Y.x) (h3 : G.Adj q (Y.g 3)) (h4 : G.Adj q (Y.g 4)) : False := by
  have hM' : VegaMax G 2 false true := fun i' μ' ν' h => hM i' μ' ν' (by
    unfold vsize at h ⊢; simpa using h)
  exact Y.rho2.sigma.tau1.l422blue hcf hcube hmin hM' q h3 hx h4

/-- LPR Lemma 4.23, second case: ν = 0, q ~ x and q ~ 2i-1 ⟹ q has no blue neighbour. -/
theorem Vega.l423case2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (F : GrFacts G) (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (hM : VegaMax G i μ false) (q : V)
    (hx : G.Adj q Y.x) (h2i : G.Adj q (Y.g (2 * i - 1))) :
    ∀ m, 2 * i ≤ m → m < 3 * i - 1 → ¬ G.Adj q (Y.g m) := by
  have hi := Y.hi
  have nf : ∀ j : ℕ, false = true → j ≠ 2 * i - 1 := fun _ h => (Bool.false_ne_true h).elim
  intro m hm1 hm2 hqm
  have hC := Y.grGreen (2 * i - 1) (i - 1) m i (by omega) (by omega) (nf _) (by omega) hm1 hm2
    le_rfl (by omega) (nf _) (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have r0 := Y.red 0 (by omega)
  have e0i : G.Adj (Y.g i) (Y.g 0) := Y.gg _ _ (by omega) (nf _) (nf _) (by omega) (by omega)
  have tU0 : InExt G ![Y.a, Y.g (i - 1), Y.g m, Y.c, Y.v]
      ![Y.g (2 * i - 1), Y.w, Y.u, Y.g i, Y.x] 0 (Y.g 0) := ⟨r0.2.symm, e0i.symm, r0.1.symm⟩
  have tU2 : InExt G ![Y.a, Y.g (i - 1), Y.g m, Y.c, Y.v]
      ![Y.g (2 * i - 1), Y.w, Y.u, Y.g i, Y.x] 2 q := ⟨hx, h2i, hqm⟩
  cases μ with
  | false =>
    have tU4 : InExt G ![Y.a, Y.g (i - 1), Y.g m, Y.c, Y.v]
        ![Y.g (2 * i - 1), Y.w, Y.u, Y.g i, Y.x] 4 Y.y := ⟨Y.yw rfl, Y.yu rfl, Y.yv rfl⟩
    exact F.l413r hC 1 _ _ _ tU4 tU2 tU0
  | true =>
    by_cases hi3 : 3 ≤ i
    · have hD := Y.grGreen (2 * i - 1) 1 (2 * i) i (by omega) (by omega) (nf _) (by omega)
        le_rfl (by omega) le_rfl (by omega) (nf _) (by unfold AA; omega) (by unfold AA; omega)
        (by unfold AA; omega)
      have gi1 := Y.green (i + 1) (by omega) (by omega) (nf _)
      have b2 := Y.blue (2 * i + 1) (by omega) (by omega)
      have r2 := Y.red 2 (by omega)
      have e1 : G.Adj (Y.g (i + 1)) (Y.g 1) :=
        Y.gg _ _ (by omega) (nf _) (nf _) (by omega) (by omega)
      have e2 : G.Adj (Y.g (2 * i + 1)) (Y.g (i + 1)) :=
        Y.gg _ _ (by omega) (nf _) (nf _) (by omega) (by omega)
      have e3 : G.Adj (Y.g (2 * i - 1)) (Y.g 2) :=
        Y.gg _ _ (by omega) (nf _) (nf _) (by omega) (by omega)
      have e4 : G.Adj (Y.g (2 * i + 1)) (Y.g 2) :=
        Y.gg _ _ (by omega) (nf _) (nf _) (by omega) (by omega)
      rcases F.l410r hD 2 q h2i hx with h | h
      · exact not_adj_both hcf (h 1) hqm (Y.blue m hm1 hm2).2
      · exact F.l414 (hD.rotV 2) (Y.g (i + 1)) e1 gi1.2.symm gi1.1.symm (Y.g (2 * i + 1)) e2
          b2.2.symm b2.1.symm (Y.g 2) e3.symm r2.1.symm e4.symm q hx h2i h
    · have hi2 : i = 2 := by omega
      subst hi2
      have hm4 : m = 4 := by omega
      subst hm4
      exact Y.l422red hcf hcube hmin hM q hx h2i hqm

section NoSmall
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem Vega.nsXRG (F : GrFacts G) (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V) (hx : G.Adj q Y.x)
    (r : ℕ) (hr : r < i) (hqr : G.Adj q (Y.g r))
    (m : ℕ) (hm1 : i ≤ m) (hm2 : m < 2 * i) (hmn : ν = true → m ≠ 2 * i - 1)
    (hqm : G.Adj q (Y.g m)) : False := by
  have hi := Y.hi
  by_cases h : m ≤ 2 * i - 2
  · exact (Y.l423case1 F hcf hcube hmin hM q hx m hm1 h hqm).1 r hr hqr
  · exact not_adj_both hcf hqm hqr
      (Y.gg m r (by omega) hmn (by intro _; omega) (by omega) (by omega))

theorem Vega.nsXGB (F : GrFacts G) (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V) (hx : G.Adj q Y.x)
    (m : ℕ) (hm1 : i ≤ m) (hm2 : m < 2 * i) (hmn : ν = true → m ≠ 2 * i - 1)
    (hqm : G.Adj q (Y.g m))
    (b : ℕ) (hb1 : 2 * i ≤ b) (hb2 : b < 3 * i - 1) (hqb : G.Adj q (Y.g b)) : False := by
  have hi := Y.hi
  by_cases h : m ≤ 2 * i - 2
  · exact (Y.l423case1 F hcf hcube hmin hM q hx m hm1 h hqm).2 b hb1 hb2 hqb
  · have hm : m = 2 * i - 1 := by omega
    subst hm
    cases ν with
    | true => exact hmn rfl rfl
    | false => exact Y.l423case2 F hcf hcube hmin hM q hx hqm b hb1 hb2 hqb

theorem Vega.nsXRB (F : GrFacts G) (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V) (hx : G.Adj q Y.x)
    (r : ℕ) (hr : r < i) (hqr : G.Adj q (Y.g r))
    (b : ℕ) (hb1 : 2 * i ≤ b) (hb2 : b < 3 * i - 1) (hqb : G.Adj q (Y.g b)) : False := by
  have hi := Y.hi
  cases ν with
  | false =>
    have e1 : Y.tau0.g (2 * i - 1 - r) = Y.g r := by
      show Y.g (rho0 i _) = _
      unfold rho0; rw [if_pos (by omega)]; congr 1; omega
    have e2 : Y.tau0.g (5 * i - 2 - b) = Y.g b := by
      show Y.g (rho0 i _) = _
      unfold rho0; rw [if_neg (by omega)]; congr 1; omega
    exact Y.tau0.nsXGB F hcf hcube hmin hM q hx (2 * i - 1 - r) (by omega) (by omega)
      (fun h => (Bool.false_ne_true h).elim) (by rw [e1]; exact hqr) (5 * i - 2 - b) (by omega)
      (by omega) (by rw [e2]; exact hqb)
  | true =>
    have e1 : Y.tau1.g (i - 1 - r) = Y.g r := by
      show Y.g (rho1 i _) = _
      unfold rho1; rw [if_pos (by omega)]; congr 1; omega
    have e2 : Y.tau1.g (4 * i - 2 - b) = Y.g b := by
      show Y.g (rho1 i _) = _
      unfold rho1; rw [if_neg (by omega), if_neg (by omega)]; congr 1; omega
    exact Y.tau1.nsXRG F hcf hcube hmin hM q hx (i - 1 - r) (by omega) (by rw [e1]; exact hqr)
      (4 * i - 2 - b) (by omega) (by omega) (fun _ => by omega) (by rw [e2]; exact hqb)

/-- LPR Lemma 4.23 (x-part): in a maximal Vega copy, a neighbour of x meets at most one colour
class of the Andrásfai part. -/
theorem Vega.noSmallX (F : GrFacts G) (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V) (hx : G.Adj q Y.x)
    (j k : ℕ) (hj : pres i μ ν (Sum.inl j)) (hk : pres i μ ν (Sum.inl k))
    (hqj : G.Adj q (Y.g j)) (hqk : G.Adj q (Y.g k))
    (hcol : (j < i ↔ k < i) → (j < 2 * i ↔ k < 2 * i) → False) : False := by
  obtain ⟨hj1, hjn⟩ := hj
  obtain ⟨hk1, hkn⟩ := hk
  have hi := Y.hi
  rcases Nat.lt_or_ge j i with h1 | h1 <;> rcases Nat.lt_or_ge k i with h2 | h2 <;>
    rcases Nat.lt_or_ge j (2 * i) with h3 | h3 <;> rcases Nat.lt_or_ge k (2 * i) with h4 | h4
  all_goals first
    | exact hcol (by omega) (by omega)
    | exact Y.nsXRG F hcf hcube hmin hM q hx j h1 hqj k h2 h4 hkn hqk
    | exact Y.nsXRG F hcf hcube hmin hM q hx k h2 hqk j h1 h3 hjn hqj
    | exact Y.nsXGB F hcf hcube hmin hM q hx j h1 h3 hjn hqj k h4 hk1 hqk
    | exact Y.nsXGB F hcf hcube hmin hM q hx k h2 h4 hkn hqk j h3 hj1 hqj
    | exact Y.nsXRB F hcf hcube hmin hM q hx j h1 hqj k h4 hk1 hqk
    | exact Y.nsXRB F hcf hcube hmin hM q hx k h2 hqk j h3 hj1 hqj
    | omega

end NoSmall

/-- The Grötzsch configuration of H1 (outer cycle v, shadows u, centre w) is a copy of Υ_2^{11}
(isomorphism found by Python, iso11.py): g 0 = u3, g 1 = u0, g 2 = v2, g 4 = v1,
a = w, v = u1, c = v0, u = v4, b = v3, w = u2, x = u4. -/
def Vega.ofGr (v u : Fin 5 → V) (w : V)
    (hY : ∀ i : Fin 5, G.Adj (v i) (v (i + 1)) ∧ G.Adj (u i) (v (i + 1)) ∧
      G.Adj (u i) (v (i + 4)) ∧ G.Adj w (u i)) : Vega G 2 true true where
  g j := if j = 0 then u 3 else if j = 1 then u 0 else if j = 2 then v 2 else v 1
  a := w
  v := u 1
  c := v 0
  u := v 4
  b := v 3
  w := u 2
  x := u 4
  y := w
  hi := le_rfl
  gg j k hj hjn hkn h1 h2 := by
    have hj3 := hjn rfl
    have hk3 := hkn rfl
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · have hj' : j = 2 := by omega
      subst hj'
      exact (hY 3).2.2.1.symm
    · have hj' : j = 4 := by omega
      subst hj'
      exact (hY 0).2.1.symm
    · have hj' : j = 4 := by omega
      subst hj'
      exact (hY 1).1
  red j hj := by
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact ⟨(hY 3).2.2.2, (hY 3).2.1.symm⟩
    · exact ⟨(hY 0).2.2.2, (hY 0).2.2.1.symm⟩
  green j h1 h2 h3 := by
    have hj3 := h3 rfl
    have hj' : j = 2 := by omega
    subst hj'
    exact ⟨(hY 2).1.symm, (hY 1).2.1⟩
  blue j h1 h2 := by
    have hj' : j = 4 := by omega
    subst hj'
    exact ⟨(hY 0).1, (hY 2).2.2.1⟩
  av := (hY 1).2.2.2
  vc := (hY 1).2.2.1
  cu := (hY 4).1.symm
  ub := (hY 3).1.symm
  bw := (hY 2).2.1.symm
  wa := (hY 2).2.2.2.symm
  xa := (hY 4).2.2.2.symm
  xb := (hY 4).2.2.1
  xc := (hY 4).2.1
  yu h := absurd h (by decide)
  yv h := absurd h (by decide)
  yw h := absurd h (by decide)
  yx h := absurd h (by decide)

/-- A Vega copy has i distinct red vertices, so i ≤ |V|. -/
theorem Vega.i_le_card [Fintype V] (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) : i ≤ Fintype.card V := by
  have hi := Y.hi
  have hinj : Function.Injective (fun j : Fin i => Y.g j.val) := by
    intro j k hjk
    by_contra hne
    have hne' : j.val ≠ k.val := fun h => hne (Fin.ext h)
    simp only at hjk
    -- wlog j < k
    have key : ∀ a b : ℕ, a < b → b < i → Y.g a = Y.g b → False := by
      intro a b hab hb he
      have e1 : G.Adj (Y.g (a + i)) (Y.g a) :=
        Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
      have e2 : G.Adj (Y.g (a + 2 * i)) (Y.g (a + i)) :=
        Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
      have e3 : G.Adj (Y.g (a + 2 * i)) (Y.g b) :=
        Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
      rw [he] at e1
      exact not_adj_both hcf e2 e3 e1
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact key _ _ h k.isLt hjk
    · exact key _ _ h j.isLt hjk.symm
  simpa using Fintype.card_le_of_injective _ hinj

/-- A maximal Vega copy exists once some Vega copy exists. -/
theorem exists_vegaMax [Fintype V] (hcf : G.CliqueFree 3) {i0 : ℕ} {μ0 ν0 : Bool}
    (Y0 : Vega G i0 μ0 ν0) : ∃ i μ ν, Nonempty (Vega G i μ ν) ∧ VegaMax G i μ ν := by
  classical
  let B := 3 * Fintype.card V + 7
  let P : ℕ → Prop := fun n => ∃ i μ ν, vsize i μ ν = n ∧ Nonempty (Vega G i μ ν)
  have hle : ∀ i μ ν, Nonempty (Vega G i μ ν) → vsize i μ ν ≤ B := by
    rintro i μ ν ⟨Y⟩
    have := Y.i_le_card hcf
    unfold vsize; split_ifs <;> omega
  have hP0 : P (vsize i0 μ0 ν0) := ⟨i0, μ0, ν0, rfl, ⟨Y0⟩⟩
  have hspec := Nat.findGreatest_spec (P := P) (hle i0 μ0 ν0 ⟨Y0⟩) hP0
  obtain ⟨i, μ, ν, hsz, hne⟩ := hspec
  refine ⟨i, μ, ν, hne, fun i' μ' ν' hlt => ⟨fun Y' => ?_⟩⟩
  have h1 := Nat.le_findGreatest (P := P) (hle i' μ' ν' ⟨Y'⟩) ⟨i', μ', ν', rfl, ⟨Y'⟩⟩
  omega

/-- Υ_i^{μν} has diameter two on its Andrásfai part: two present non-adjacent Andrásfai vertices
(possibly equal) have a present common neighbour. -/
theorem vadj_common_inl {i : ℕ} (hi : 2 ≤ i) (μ ν : Bool) (j k : ℕ)
    (hj : pres i μ ν (Sum.inl j)) (hk : pres i μ ν (Sum.inl k))
    (hn : ¬ vadj i (Sum.inl j) (Sum.inl k)) :
    ∃ r, pres i μ ν r ∧ vadj i (Sum.inl j) r ∧ vadj i r (Sum.inl k) := by
  obtain ⟨hj1, hjn⟩ := hj
  obtain ⟨hk1, hkn⟩ := hk
  simp only [vadj, AA] at hn
  by_cases hjr : j < i
  · by_cases hkr : k < i
    · exact ⟨Sum.inr 0, Or.inl (by decide), Or.inl ⟨Or.inl rfl, hjr⟩, Or.inl ⟨Or.inl rfl, hkr⟩⟩
    by_cases hkg : k < 2 * i
    · exact ⟨Sum.inl (k + i), ⟨by omega, fun _ => by omega⟩, by simp only [vadj, AA]; omega,
        by simp only [vadj, AA]; omega⟩
    · exact ⟨Sum.inl (j + i), ⟨by omega, fun _ => by omega⟩, by simp only [vadj, AA]; omega,
        by simp only [vadj, AA]; omega⟩
  by_cases hjg : j < 2 * i
  · by_cases hkr : k < i
    · exact ⟨Sum.inl (j + i), ⟨by omega, fun _ => by omega⟩, by simp only [vadj, AA]; omega,
        by simp only [vadj, AA]; omega⟩
    by_cases hkg : k < 2 * i
    · exact ⟨Sum.inr 4, Or.inl (by decide), Or.inr (Or.inl ⟨Or.inl rfl, by omega, hjg⟩),
        Or.inr (Or.inl ⟨Or.inl rfl, by omega, hkg⟩)⟩
    · exact ⟨Sum.inl (k + 1 - 2 * i), ⟨by omega, fun _ => by omega⟩,
        by simp only [vadj, AA]; omega, by simp only [vadj, AA]; omega⟩
  by_cases hkr : k < i
  · exact ⟨Sum.inl (k + i), ⟨by omega, fun _ => by omega⟩, by simp only [vadj, AA]; omega,
      by simp only [vadj, AA]; omega⟩
  by_cases hkg : k < 2 * i
  · exact ⟨Sum.inl (j + 1 - 2 * i), ⟨by omega, fun _ => by omega⟩,
      by simp only [vadj, AA]; omega, by simp only [vadj, AA]; omega⟩
  · exact ⟨Sum.inr 2, Or.inl (by decide), Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩),
      Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)⟩

/-- q is a Υ-twin of the vertex p of the copy Y (equal traces on the present vertices). -/
def Vega.Twin {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (q : V) (p : ℕ ⊕ Fin 8) : Prop :=
  ∀ s, pres i μ ν s → (G.Adj q (Y.emb s) ↔ vadj i p s)

theorem vadj_irrefl {i : ℕ} (hi : 2 ≤ i) (p : ℕ ⊕ Fin 8) : ¬ vadj i p p := by
  rcases p with j | t
  · simp only [vadj, AA]; omega
  · simp only [vadj, hexAdj]; omega

/-- Build a Vega copy from any adjacency-preserving map on the present vertices. -/
def Vega.ofEmb (i : ℕ) (μ ν : Bool) (hi : 2 ≤ i) (e : ℕ ⊕ Fin 8 → V)
    (h : ∀ p s, pres i μ ν p → pres i μ ν s → vadj i p s → G.Adj (e p) (e s)) :
    Vega G i μ ν where
  g j := e (Sum.inl j)
  a := e (Sum.inr 0)
  v := e (Sum.inr 1)
  c := e (Sum.inr 2)
  u := e (Sum.inr 3)
  b := e (Sum.inr 4)
  w := e (Sum.inr 5)
  x := e (Sum.inr 6)
  y := e (Sum.inr 7)
  hi := hi
  gg j k hj hjn hkn h1 h2 := h _ _ ⟨hj, hjn⟩ ⟨by omega, hkn⟩ (Or.inl ⟨h1, h2⟩)
  red j hj := ⟨h (Sum.inr 0) (Sum.inl j) (Or.inl (by decide)) ⟨by omega, fun _ => by omega⟩
      (Or.inl ⟨Or.inl rfl, hj⟩),
    h (Sum.inr 3) (Sum.inl j) (Or.inl (by decide)) ⟨by omega, fun _ => by omega⟩
      (Or.inl ⟨Or.inr rfl, hj⟩)⟩
  green j h1 h2 h3 := ⟨h (Sum.inr 4) (Sum.inl j) (Or.inl (by decide)) ⟨by omega, h3⟩
      (Or.inr (Or.inl ⟨Or.inl rfl, h1, h2⟩)),
    h (Sum.inr 1) (Sum.inl j) (Or.inl (by decide)) ⟨by omega, h3⟩
      (Or.inr (Or.inl ⟨Or.inr rfl, h1, h2⟩))⟩
  blue j h1 h2 := ⟨h (Sum.inr 2) (Sum.inl j) (Or.inl (by decide)) ⟨h2, fun _ => by omega⟩
      (Or.inr (Or.inr ⟨Or.inl rfl, h1⟩)),
    h (Sum.inr 5) (Sum.inl j) (Or.inl (by decide)) ⟨h2, fun _ => by omega⟩
      (Or.inr (Or.inr ⟨Or.inr rfl, h1⟩))⟩
  av := h (Sum.inr 0) (Sum.inr 1) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  vc := h (Sum.inr 1) (Sum.inr 2) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  cu := h (Sum.inr 2) (Sum.inr 3) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  ub := h (Sum.inr 3) (Sum.inr 4) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  bw := h (Sum.inr 4) (Sum.inr 5) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  wa := h (Sum.inr 5) (Sum.inr 0) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  xa := h (Sum.inr 6) (Sum.inr 0) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  xb := h (Sum.inr 6) (Sum.inr 4) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  xc := h (Sum.inr 6) (Sum.inr 2) (Or.inl (by decide)) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  yu hμ := h (Sum.inr 7) (Sum.inr 3) (Or.inr hμ) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  yv hμ := h (Sum.inr 7) (Sum.inr 1) (Or.inr hμ) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  yw hμ := h (Sum.inr 7) (Sum.inr 5) (Or.inr hμ) (Or.inl (by decide)) (by simp [vadj, hexAdj])
  yx hμ := h (Sum.inr 7) (Sum.inr 6) (Or.inr hμ) (Or.inl (by decide)) (by simp [vadj, hexAdj])

theorem Vega.ofEmb_emb (i : ℕ) (μ ν : Bool) (hi : 2 ≤ i) (e : ℕ ⊕ Fin 8 → V)
    (h : ∀ p s, pres i μ ν p → pres i μ ν s → vadj i p s → G.Adj (e p) (e s)) (s : ℕ ⊕ Fin 8) :
    (Vega.ofEmb i μ ν hi e h).emb s = e s := by
  rcases s with j | t
  · rfl
  · fin_cases t <;> rfl

theorem vadj_symm' {i : ℕ} {p s : ℕ ⊕ Fin 8} (h : vadj i p s) : vadj i s p := by
  rcases p with j | a <;> rcases s with k | b
  · simp only [vadj, AA] at h ⊢; omega
  · exact h
  · exact h
  · simp only [vadj, hexAdj] at h ⊢; omega

/-- Replace the vertex z of a Vega copy by a Υ-twin z' (LPR's Ω(z')). -/
def Vega.repl {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (z : ℕ ⊕ Fin 8) (z' : V)
    (htw : Y.Twin z' z) : Vega G i μ ν :=
  Vega.ofEmb i μ ν Y.hi (Function.update Y.emb z z') (by
    intro p s hp hs h
    by_cases hpz : p = z
    · subst hpz
      by_cases hsz : s = p
      · subst hsz; exact absurd h (vadj_irrefl Y.hi _)
      · rw [Function.update_self, Function.update_of_ne hsz]
        exact (htw s hs).mpr h
    · by_cases hsz : s = z
      · subst hsz
        rw [Function.update_self, Function.update_of_ne hpz]
        exact ((htw p hp).mpr (vadj_symm' h)).symm
      · rw [Function.update_of_ne hpz, Function.update_of_ne hsz]
        exact Y.emb_adj p s hp hs h)

theorem Vega.repl_emb {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (z : ℕ ⊕ Fin 8) (z' : V)
    (htw : Y.Twin z' z) (s : ℕ ⊕ Fin 8) :
    (Y.repl z z' htw).emb s = Function.update Y.emb z z' s :=
  Vega.ofEmb_emb i μ ν Y.hi _ _ s

end Vega

/-! ## Assembly skeleton
H1 follows from four statements. `NoCubeClaim` and `GrFactsClaim` are proved in
E128H1_base.lean (`no_cube`, `beautiful`, `lemma410`–`lemma414`, `lemma46`, `lemma47`).
`Diam2` is the diameter-two property of the Vega graphs (Andrásfai part done: `vadj_common_inl`).
`AttachClaim` is the attachment lemma (LPR 4.29, with twin lemma 4.28) — the remaining core. -/

section Skeleton

theorem vadj_symm {i : ℕ} {p s : ℕ ⊕ Fin 8} (h : vadj i p s) : vadj i s p := by
  rcases p with j | a <;> rcases s with k | b
  · simp only [vadj, AA] at h ⊢; omega
  · exact h
  · exact h
  · simp only [vadj, hexAdj] at h ⊢; omega

/-- Diameter two (with no isolated vertices) of every Vega graph Υ_i^{μν}, i ≥ 2. -/
def Diam2 : Prop :=
  ∀ i, 2 ≤ i → ∀ (μ ν : Bool) (p s : ℕ ⊕ Fin 8), pres i μ ν p → pres i μ ν s → ¬ vadj i p s →
    ∃ r, pres i μ ν r ∧ vadj i p r ∧ vadj i r s

/-- Diameter two between an Andrásfai vertex and an outer vertex. -/
theorem vadj_common_inl_inr {i : ℕ} (hi : 2 ≤ i) (μ ν : Bool) (j : ℕ) (t : Fin 8)
    (hj : pres i μ ν (Sum.inl j)) (ht : pres i μ ν (Sum.inr t))
    (hn : ¬ vadj i (Sum.inl j) (Sum.inr t)) :
    ∃ r, pres i μ ν r ∧ vadj i (Sum.inl j) r ∧ vadj i r (Sum.inr t) := by
  obtain ⟨hj1, hjn⟩ := hj
  have P : ∀ k : Fin 8, k.val < 7 → pres i μ ν (Sum.inr k) := fun k hk => Or.inl hk
  simp only [vadj, colAdj] at hn
  have hc : j < i ∨ (i ≤ j ∧ j < 2 * i) ∨ 2 * i ≤ j := by omega
  fin_cases t <;> simp at hn
  all_goals rcases hc with hc | hc | hc
  all_goals first
    | exact (hn (by omega)).elim
    | (exfalso; omega)
    | (refine ⟨Sum.inr 0, P 0 (by decide), ?_, ?_⟩ <;> simp [vadj, colAdj, hexAdj] <;> omega)
    | (refine ⟨Sum.inr 1, P 1 (by decide), ?_, ?_⟩ <;> simp [vadj, colAdj, hexAdj] <;> omega)
    | (refine ⟨Sum.inr 2, P 2 (by decide), ?_, ?_⟩ <;> simp [vadj, colAdj, hexAdj] <;> omega)
    | (refine ⟨Sum.inr 3, P 3 (by decide), ?_, ?_⟩ <;> simp [vadj, colAdj, hexAdj] <;> omega)
    | (refine ⟨Sum.inr 4, P 4 (by decide), ?_, ?_⟩ <;> simp [vadj, colAdj, hexAdj] <;> omega)
    | (refine ⟨Sum.inr 5, P 5 (by decide), ?_, ?_⟩ <;> simp [vadj, colAdj, hexAdj] <;> omega)

theorem diam2 : Diam2 := by
  intro i hi μ ν p s hp hs h
  rcases p with j | a <;> rcases s with k | b
  · exact vadj_common_inl hi μ ν j k hp hs h
  · exact vadj_common_inl_inr hi μ ν j b hp hs h
  · obtain ⟨r, hr, h1, h2⟩ :=
      vadj_common_inl_inr hi μ ν k a hs hp (fun h' => h (vadj_symm h'))
    exact ⟨r, hr, vadj_symm h2, vadj_symm h1⟩
  fin_cases a <;> fin_cases b
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inl (0), ⟨by omega, fun _ => by omega⟩, by simp [vadj, colAdj] <;> omega, by simp [vadj, colAdj] <;> omega⟩
  · exact ⟨Sum.inr 5, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 2, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inl (i), ⟨by omega, fun _ => by omega⟩, by simp [vadj, colAdj] <;> omega, by simp [vadj, colAdj] <;> omega⟩
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 3, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inl (2 * i), ⟨by omega, fun _ => by omega⟩, by simp [vadj, colAdj] <;> omega, by simp [vadj, colAdj] <;> omega⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inl (0), ⟨by omega, fun _ => by omega⟩, by simp [vadj, colAdj] <;> omega, by simp [vadj, colAdj] <;> omega⟩
  · exact ⟨Sum.inr 2, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 2, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 4, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inr 2, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 5, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inl (i), ⟨by omega, fun _ => by omega⟩, by simp [vadj, colAdj] <;> omega, by simp [vadj, colAdj] <;> omega⟩
  · exact ⟨Sum.inr 3, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 3, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 3, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inl (2 * i), ⟨by omega, fun _ => by omega⟩, by simp [vadj, colAdj] <;> omega, by simp [vadj, colAdj] <;> omega⟩
  · exact ⟨Sum.inr 4, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 2, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact ⟨Sum.inr 0, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 3, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩
  · exact absurd h (by simp [vadj, hexAdj])
  · exact absurd h (by simp [vadj, hexAdj])
  · exact ⟨Sum.inr 1, Or.inl (by decide), by simp [vadj, hexAdj], by simp [vadj, hexAdj]⟩

/-- Attachment (domination form) for a maximal Vega copy. -/
def AttachP {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ (i : ℕ) (μ ν : Bool) (Y : Vega G i μ ν), VegaMax G i μ ν → ∀ q : V,
    ∃ p, pres i μ ν p ∧ ∀ s, pres i μ ν s → vadj i p s → G.Adj q (Y.emb s)

/-- The remaining core: LPR Lemma 4.29 (attachment) in all relevant graphs. -/
def AttachClaim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) → NoCube G → GrFacts G → AttachP G

/-- Cube lemma in all relevant graphs (proved in the base file as `no_cube`). -/
def NoCubeClaim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) → NoCube G

/-- Grötzsch-level lemmas in all relevant graphs (proved in the base file). -/
def GrFactsClaim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) → GrFacts G

/-- Target relation of H1 (copied from the statement). -/
def H1rel (i : ℕ) (a b : Fin (3 * i - 1) ⊕ Fin 8) : Prop :=
  match a, b with
  | Sum.inl p, Sum.inl q =>
      i ≤ (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ∧
      (q.val + (3 * i - 1) - p.val) % (3 * i - 1) ≤ 2 * i - 1
  | Sum.inl p, Sum.inr t =>
      ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
      ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
      ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
  | Sum.inr t, Sum.inl p =>
      ((t.val = 0 ∨ t.val = 3) ∧ p.val < i) ∨
      ((t.val = 4 ∨ t.val = 1) ∧ i ≤ p.val ∧ p.val < 2 * i) ∨
      ((t.val = 2 ∨ t.val = 5) ∧ 2 * i ≤ p.val)
  | Sum.inr t₁, Sum.inr t₂ =>
      (t₁.val < 6 ∧ t₂.val < 6 ∧ ((t₁.val + 1) % 6 = t₂.val ∨ (t₂.val + 1) % 6 = t₁.val)) ∨
      (t₁.val = 6 ∧ (t₂.val = 0 ∨ t₂.val = 4 ∨ t₂.val = 2 ∨ t₂.val = 7)) ∨
      (t₂.val = 6 ∧ (t₁.val = 0 ∨ t₁.val = 4 ∨ t₁.val = 2 ∨ t₁.val = 7)) ∨
      (t₁.val = 7 ∧ (t₂.val = 3 ∨ t₂.val = 1 ∨ t₂.val = 5 ∨ t₂.val = 6)) ∨
      (t₂.val = 7 ∧ (t₁.val = 3 ∨ t₁.val = 1 ∨ t₁.val = 5 ∨ t₁.val = 6))

/-- From ℕ ⊕ Fin 8 to the vertex type of H1. -/
def toFin (i : ℕ) (hi : 2 ≤ i) : ℕ ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8
  | Sum.inl j => Sum.inl ⟨j % (3 * i - 1), Nat.mod_lt _ (by omega)⟩
  | Sum.inr t => Sum.inr t

theorem toFin_rel {i : ℕ} (hi : 2 ≤ i) {μ ν : Bool} (p s : ℕ ⊕ Fin 8)
    (hp : pres i μ ν p) (hs : pres i μ ν s) (h : vadj i p s) :
    H1rel i (toFin i hi p) (toFin i hi s) := by
  rcases p with j | a <;> rcases s with k | b
  · obtain ⟨hj, -⟩ := hp
    obtain ⟨hk, -⟩ := hs
    simp only [toFin, H1rel, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk]
    simp only [vadj, AA] at h
    rcases Nat.lt_or_ge k j with hkj | hkj
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have e : k + (3 * i - 1) - j = (k - j) + (3 * i - 1) := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · obtain ⟨hj, -⟩ := hp
    simp only [toFin, H1rel, Nat.mod_eq_of_lt hj]
    exact h
  · obtain ⟨hk, -⟩ := hs
    simp only [toFin, H1rel, Nat.mod_eq_of_lt hk]
    exact h
  · exact h

/-- Assembly: the four claims imply H1. -/
theorem h1_of_claims (hAtt : AttachClaim) (hD : Diam2) (hNC : NoCubeClaim)
    (hGF : GrFactsClaim) : OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 := by
  intro V _ G _ hcf hmax hmin _ hgr
  classical
  obtain ⟨v, u, w, hY⟩ := hgr
  obtain ⟨i, μ, ν, ⟨Y⟩, hM⟩ := exists_vegaMax hcf (Vega.ofGr v u w hY)
  have att := hAtt V G hcf hmax hmin (hNC V G hcf hmax hmin) (hGF V G hcf hmax hmin) i μ ν Y hM
  choose p hp hdom using att
  refine ⟨i, Y.hi, fun q => toFin i Y.hi (p q), ?_⟩
  intro x y hxy
  have hv : vadj i (p x) (p y) := by
    by_contra hn
    obtain ⟨r, hr, h1, h2⟩ := hD i Y.hi μ ν _ _ (hp x) (hp y) hn
    exact not_adj_both hcf hxy (hdom x r hr h1) (hdom y r hr (vadj_symm h2))
  exact toFin_rel Y.hi _ _ (hp x) (hp y) hv

end Skeleton

section Twins
variable {V : Type} {G : SimpleGraph V}

/-- Copies are induced: adjacency in G between copy vertices implies adjacency in Υ. -/
theorem Vega.induced (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (p s : ℕ ⊕ Fin 8) (hp : pres i μ ν p) (hs : pres i μ ν s)
    (h : G.Adj (Y.emb p) (Y.emb s)) : vadj i p s := by
  by_contra hn
  obtain ⟨r, hr, h1, h2⟩ := diam2 i Y.hi μ ν p s hp hs hn
  exact not_adj_both hcf (Y.emb_adj r p hr hp (vadj_symm h1)) (Y.emb_adj r s hr hs h2) h

/-- The (Υ_i^{μν})-twin property of a copy. -/
def Vega.TwinProp {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) : Prop :=
  ∀ p s, pres i μ ν p → pres i μ ν s → vadj i p s → ∀ p' s' : V, Y.Twin p' p → Y.Twin s' s →
    G.Adj p' s'

/-- LPR Lemma 2.3 for Vega copies: twins with respect to Y(z') are twins with respect to Y, when
Y(z') has the twin property. -/
theorem Vega.lemma23 (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (z : ℕ ⊕ Fin 8) (hz : pres i μ ν z) (z' : V) (htw : Y.Twin z' z)
    (hT : (Y.repl z z' htw).TwinProp) (q : ℕ ⊕ Fin 8) (hq : pres i μ ν q) (hqz : q ≠ z)
    (q' : V) (h' : (Y.repl z z' htw).Twin q' q) : Y.Twin q' q := by
  have E : ∀ s, (Y.repl z z' htw).emb s = Function.update Y.emb z z' s := Y.repl_emb z z' htw
  intro s hs
  by_cases hsz : s = z
  · subst hsz
    by_cases hv : vadj i q s
    · refine ⟨fun _ => hv, fun _ => ?_⟩
      have tw : (Y.repl s z' htw).Twin (Y.emb s) s := by
        intro r hr
        rw [E r]
        by_cases hrs : r = s
        · subst hrs
          rw [Function.update_self]
          obtain ⟨t, ht, h1, -⟩ := diam2 i Y.hi μ ν r r hr hr (vadj_irrefl Y.hi _)
          have a1 : G.Adj (Y.emb t) (Y.emb r) := Y.emb_adj t r ht hr (vadj_symm h1)
          have a2 : G.Adj (Y.emb t) z' := ((htw t ht).mpr h1).symm
          exact ⟨fun h => absurd h (not_adj_both hcf a1 a2),
            fun h => absurd h (vadj_irrefl Y.hi _)⟩
        · rw [Function.update_of_ne hrs]
          exact ⟨fun h => Y.induced hcf s r hs hr h, fun h => Y.emb_adj s r hs hr h⟩
      exact hT q s hq hs hv q' (Y.emb s) h' tw
    · refine ⟨fun h => ?_, fun h => absurd h hv⟩
      obtain ⟨r, hr, h1, h2⟩ := diam2 i Y.hi μ ν q s hq hs hv
      have hrs : r ≠ s := fun e => by subst e; exact vadj_irrefl Y.hi _ h2
      have a1 : G.Adj q' (Y.emb r) := by
        have := (h' r hr).mpr h1
        rwa [E r, Function.update_of_ne hrs] at this
      exact (not_adj_both hcf a1 h (Y.emb_adj r s hr hs h2)).elim
  · have := h' s hs
    rwa [E s, Function.update_of_ne hsz] at this

set_option maxHeartbeats 4000000 in
/-- Enlargement for LPR Lemma 4.27 (short red-green edge j, j+i): J (new red j+1), K (new green
i+j+1), q (new blue 2i+j+2) inserted into Υ_i^{μν} give Υ_{i+1}^{μν} (placement found by
l427s.py, unique). -/
def Vega.enlarge3 {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (j : ℕ) (hj : j + 2 ≤ i)
    (J K q : V)
    (hJ : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i j k → G.Adj J (Y.g k))
    (hK : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i (j + i) k → G.Adj K (Y.g k))
    (hJa : G.Adj J Y.a) (hJu : G.Adj J Y.u) (hKb : G.Adj K Y.b) (hKv : G.Adj K Y.v)
    (hqc : G.Adj q Y.c) (hqw : G.Adj q Y.w) (hqJ : G.Adj q J) (hqK : G.Adj q K)
    (hq : ∀ k, j + 1 ≤ k → k ≤ j + i - 1 → G.Adj q (Y.g k)) : Vega G (i + 1) μ ν where
  g J' := if J' ≤ j then Y.g J' else if J' = j + 1 then J else if J' ≤ i + j then Y.g (J' - 1)
    else if J' = i + j + 1 then K else if J' ≤ 2 * i + j + 1 then Y.g (J' - 2)
    else if J' = 2 * i + j + 2 then q else Y.g (J' - 3)
  a := Y.a
  v := Y.v
  c := Y.c
  u := Y.u
  b := Y.b
  w := Y.w
  x := Y.x
  y := Y.y
  hi := by have := Y.hi; omega
  gg A C hA hAn hCn h1 h2 := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact Y.adj (by omega) (by omega) (fun h => by have := hAn h; omega)
          (fun h => by have := hCn h; omega) (by unfold AA; omega)
      | exact hJ _ (by omega) (fun h => by have := hCn h; omega) (by unfold AA; omega)
      | exact (hJ _ (by omega) (fun h => by have := hAn h; omega) (by unfold AA; omega)).symm
      | exact hK _ (by omega) (fun h => by have := hCn h; omega) (by unfold AA; omega)
      | exact (hK _ (by omega) (fun h => by have := hAn h; omega) (by unfold AA; omega)).symm
      | exact hq _ (by omega) (by omega)
      | exact (hq _ (by omega) (by omega)).symm
      | exact hqJ
      | exact hqJ.symm
      | exact hqK
      | exact hqK.symm
  red J' hJ' := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact Y.red _ (by omega)
      | exact ⟨hJa.symm, hJu.symm⟩
  green J' h1 h2 h3 := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact ⟨hKb.symm, hKv.symm⟩
      | exact Y.green _ (by omega) (by omega) (fun h => by have := h3 h; omega)
  blue J' h1 h2 := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact ⟨hqc.symm, hqw.symm⟩
      | exact Y.blue _ (by omega) (by omega)
  av := Y.av
  vc := Y.vc
  cu := Y.cu
  ub := Y.ub
  bw := Y.bw
  wa := Y.wa
  xa := Y.xa
  xb := Y.xb
  xc := Y.xc
  yu := Y.yu
  yv := Y.yv
  yw := Y.yw
  yx := Y.yx

/-- LPR Lemma 4.27, short red-green edge j (j+i), j ≤ i-2: in a maximal copy, Υ-twins of j and
of j+i are adjacent. -/
theorem Vega.l427rg [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) (j : ℕ) (hj : j + 2 ≤ i) (J K : V)
    (hJ : Y.Twin J (Sum.inl j)) (hK : Y.Twin K (Sum.inl (j + i))) : G.Adj J K := by
  have hi := Y.hi
  by_contra hn
  have Jg : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i j k → G.Adj J (Y.g k) :=
    fun k h1 h2 h3 => (hJ (Sum.inl k) ⟨h1, h2⟩).mpr h3
  have Kg : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i (j + i) k →
      G.Adj K (Y.g k) := fun k h1 h2 h3 => (hK (Sum.inl k) ⟨h1, h2⟩).mpr h3
  have Ja : G.Adj J Y.a :=
    (hJ (Sum.inr 0) (Or.inl (by decide))).mpr (Or.inl ⟨Or.inl rfl, by omega⟩)
  have Ju : G.Adj J Y.u :=
    (hJ (Sum.inr 3) (Or.inl (by decide))).mpr (Or.inl ⟨Or.inr rfl, by omega⟩)
  have Kb : G.Adj K Y.b :=
    (hK (Sum.inr 4) (Or.inl (by decide))).mpr (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by omega⟩))
  have Kv : G.Adj K Y.v :=
    (hK (Sum.inr 1) (Or.inl (by decide))).mpr (Or.inr (Or.inl ⟨Or.inr rfl, by omega, by omega⟩))
  have hC := Y.grRed j (j + i) (j + 2 * i) (j + 1) (by omega) (by omega) (by omega)
    (by intro _; omega) (by omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  obtain ⟨q, hqJ, hqw, hqc, hqK⟩ := F.l46 (hC.rotV 1) J K
    (Jg _ (by omega) (by intro _; omega) (by unfold AA; omega)) Ju Ja
    Kb (Kg _ (by omega) (by intro _; omega) (by unfold AA; omega))
    (Kg _ (by omega) (by intro _; omega) (by unfold AA; omega)) Kv hn
  have hred : ∀ k, j + 1 ≤ k → k < i → G.Adj q (Y.g k) := by
    intro k hk1 hk2
    have h := (Y.repl (Sum.inl j) J hJ).l419a hcf hcube q
      (by show G.Adj q (Function.update Y.emb (Sum.inl j) J (Sum.inr 2))
          rw [Function.update_of_ne (by simp)]; exact hqc)
      (by show G.Adj q (Function.update Y.emb (Sum.inl j) J (Sum.inr 5))
          rw [Function.update_of_ne (by simp)]; exact hqw) j
      (by show G.Adj q (Function.update Y.emb (Sum.inl j) J (Sum.inl j))
          rw [Function.update_self]; exact hqJ) k (by omega) hk2
    have e : (Y.repl (Sum.inl j) J hJ).g k = Y.g k := by
      show Function.update Y.emb (Sum.inl j) J (Sum.inl k) = Y.g k
      rw [Function.update_of_ne (by simp; omega)]; rfl
    rwa [e] at h
  have hgreen : ∀ k, i ≤ k → k ≤ j + i - 1 → G.Adj q (Y.g k) := by
    intro k hk1 hk2
    have h := (Y.repl (Sum.inl (j + i)) K hK).l419b hcf hcube q
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + i)) K (Sum.inr 2))
          rw [Function.update_of_ne (by simp)]; exact hqc)
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + i)) K (Sum.inr 5))
          rw [Function.update_of_ne (by simp)]; exact hqw) (j + i) (by omega)
      (by intro _; omega)
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + i)) K (Sum.inl (j + i)))
          rw [Function.update_self]; exact hqK) k hk1 (by omega)
    have e : (Y.repl (Sum.inl (j + i)) K hK).g k = Y.g k := by
      show Function.update Y.emb (Sum.inl (j + i)) K (Sum.inl k) = Y.g k
      rw [Function.update_of_ne (by simp; omega)]; rfl
    rwa [e] at h
  have Z := Y.enlarge3 j hj J K q Jg Kg Ja Ju Kb Kv hqc hqw hqJ hqK
    (fun k h1 h2 => if h : k < i then hred k h1 h else hgreen k (by omega) h2)
  exact (hM (i + 1) μ ν (by unfold vsize; split_ifs <;> omega)).false Z

set_option maxHeartbeats 4000000 in
/-- Enlargement for LPR Lemma 4.27 (short green-blue edge j+i, j+2i): q (new red j+1),
K (new green i+j+2), L (new blue 2i+j+2) (placement found by l427gb.py, unique). -/
def Vega.enlarge4 {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (j : ℕ) (hj : j + 2 ≤ i)
    (K L q : V)
    (hK : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i (j + i) k → G.Adj K (Y.g k))
    (hL : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i (j + 2 * i) k →
      G.Adj L (Y.g k))
    (hKb : G.Adj K Y.b) (hKv : G.Adj K Y.v) (hLc : G.Adj L Y.c) (hLw : G.Adj L Y.w)
    (hqa : G.Adj q Y.a) (hqu : G.Adj q Y.u) (hqK : G.Adj q K) (hqL : G.Adj q L)
    (hq : ∀ k, j + i + 1 ≤ k → k ≤ j + 2 * i - 1 → (ν = true → k ≠ 2 * i - 1) →
      G.Adj q (Y.g k)) : Vega G (i + 1) μ ν where
  g J' := if J' ≤ j then Y.g J' else if J' = j + 1 then q else if J' ≤ i + j + 1 then Y.g (J' - 1)
    else if J' = i + j + 2 then K else if J' ≤ 2 * i + j + 1 then Y.g (J' - 2)
    else if J' = 2 * i + j + 2 then L else Y.g (J' - 3)
  a := Y.a
  v := Y.v
  c := Y.c
  u := Y.u
  b := Y.b
  w := Y.w
  x := Y.x
  y := Y.y
  hi := by have := Y.hi; omega
  gg A C hA hAn hCn h1 h2 := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact Y.adj (by omega) (by omega) (fun h => by have := hAn h; omega)
          (fun h => by have := hCn h; omega) (by unfold AA; omega)
      | exact hK _ (by omega) (fun h => by have := hCn h; omega) (by unfold AA; omega)
      | exact (hK _ (by omega) (fun h => by have := hAn h; omega) (by unfold AA; omega)).symm
      | exact hL _ (by omega) (fun h => by have := hCn h; omega) (by unfold AA; omega)
      | exact (hL _ (by omega) (fun h => by have := hAn h; omega) (by unfold AA; omega)).symm
      | exact hq _ (by omega) (by omega) (fun h => by have := hCn h; omega)
      | exact (hq _ (by omega) (by omega) (fun h => by have := hAn h; omega)).symm
      | exact hqK
      | exact hqK.symm
      | exact hqL
      | exact hqL.symm
  red J' hJ' := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact Y.red _ (by omega)
      | exact ⟨hqa.symm, hqu.symm⟩
  green J' h1 h2 h3 := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact ⟨hKb.symm, hKv.symm⟩
      | exact Y.green _ (by omega) (by omega) (fun h => by have := h3 h; omega)
  blue J' h1 h2 := by
    have hi := Y.hi
    split_ifs <;> first
      | (exfalso; omega)
      | exact ⟨hLc.symm, hLw.symm⟩
      | exact Y.blue _ (by omega) (by omega)
  av := Y.av
  vc := Y.vc
  cu := Y.cu
  ub := Y.ub
  bw := Y.bw
  wa := Y.wa
  xa := Y.xa
  xb := Y.xb
  xc := Y.xc
  yu := Y.yu
  yv := Y.yv
  yw := Y.yw
  yx := Y.yx

/-- LPR Lemma 4.27, short green-blue edge (j+i) (j+2i), j ≤ i-2: in a maximal copy, Υ-twins of
j+i and of j+2i are adjacent. -/
theorem Vega.l427gb [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) (j : ℕ) (hj : j + 2 ≤ i) (K L : V)
    (hK : Y.Twin K (Sum.inl (j + i))) (hL : Y.Twin L (Sum.inl (j + 2 * i))) : G.Adj K L := by
  have hi := Y.hi
  by_contra hn
  have Kg : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i (j + i) k →
      G.Adj K (Y.g k) := fun k h1 h2 h3 => (hK (Sum.inl k) ⟨h1, h2⟩).mpr h3
  have Lg : ∀ k, k < 3 * i - 1 → (ν = true → k ≠ 2 * i - 1) → AA i (j + 2 * i) k →
      G.Adj L (Y.g k) := fun k h1 h2 h3 => (hL (Sum.inl k) ⟨h1, h2⟩).mpr h3
  have Kb : G.Adj K Y.b :=
    (hK (Sum.inr 4) (Or.inl (by decide))).mpr (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by omega⟩))
  have Kv : G.Adj K Y.v :=
    (hK (Sum.inr 1) (Or.inl (by decide))).mpr (Or.inr (Or.inl ⟨Or.inr rfl, by omega, by omega⟩))
  have Lc : G.Adj L Y.c :=
    (hL (Sum.inr 2) (Or.inl (by decide))).mpr (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩))
  have Lw : G.Adj L Y.w :=
    (hL (Sum.inr 5) (Or.inl (by decide))).mpr (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))
  have hC := Y.grRed j (j + i) (j + 2 * i) (j + 1) (by omega) (by omega) (by omega)
    (by intro _; omega) (by omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  obtain ⟨q, hqK, hqu, hqa, hqL⟩ := F.l47 (hC.rotV 2) K L
    (Kg _ (by omega) (by intro _; omega) (by unfold AA; omega)) Kb Kv
    (Kg _ (by omega) (by intro _; omega) (by unfold AA; omega))
    (Lg _ (by omega) (by intro _; omega) (by unfold AA; omega)) Lc Lw
    (Lg _ (by omega) (by intro _; omega) (by unfold AA; omega)) hn
  have hgreen : ∀ k, j + i + 1 ≤ k → k < 2 * i → (ν = true → k ≠ 2 * i - 1) →
      G.Adj q (Y.g k) := by
    intro k hk1 hk2 hk3
    have h := (Y.repl (Sum.inl (j + i)) K hK).l420a hcf hcube q
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + i)) K (Sum.inr 0))
          rw [Function.update_of_ne (by simp)]; exact hqa)
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + i)) K (Sum.inr 3))
          rw [Function.update_of_ne (by simp)]; exact hqu) (j + i) (by omega)
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + i)) K (Sum.inl (j + i)))
          rw [Function.update_self]; exact hqK) k (by omega) hk2 hk3
    have e : (Y.repl (Sum.inl (j + i)) K hK).g k = Y.g k := by
      show Function.update Y.emb (Sum.inl (j + i)) K (Sum.inl k) = Y.g k
      rw [Function.update_of_ne (by simp; omega)]; rfl
    rwa [e] at h
  have hblue : ∀ k, 2 * i ≤ k → k ≤ j + 2 * i - 1 → G.Adj q (Y.g k) := by
    intro k hk1 hk2
    have h := (Y.repl (Sum.inl (j + 2 * i)) L hL).l420b hcf hcube q
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + 2 * i)) L (Sum.inr 0))
          rw [Function.update_of_ne (by simp)]; exact hqa)
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + 2 * i)) L (Sum.inr 3))
          rw [Function.update_of_ne (by simp)]; exact hqu) (j + 2 * i) (by omega)
      (by show G.Adj q (Function.update Y.emb (Sum.inl (j + 2 * i)) L (Sum.inl (j + 2 * i)))
          rw [Function.update_self]; exact hqL) k hk1 (by omega)
    have e : (Y.repl (Sum.inl (j + 2 * i)) L hL).g k = Y.g k := by
      show Function.update Y.emb (Sum.inl (j + 2 * i)) L (Sum.inl k) = Y.g k
      rw [Function.update_of_ne (by simp; omega)]; rfl
    rwa [e] at h
  have Z := Y.enlarge4 j hj K L q Kg Lg Kb Kv Lc Lw hqa hqu hqK hqL
    (fun k h1 h2 h3 => if h : k < 2 * i then hgreen k h1 h h3 else hblue k (by omega) h2)
  exact (hM (i + 1) μ ν (by unfold vsize; split_ifs <;> omega)).false Z

/-- LPR Lemma 4.26, long red-blue edge j m (j < i, m blue, i < m - j < 2i - 1): twins j'
(j' ~ a, u, g (j + 2i - 1)) and m' (m' ~ c, w, g (m - 2i + 1)) are adjacent (direct cube,
found by cube_search.py). -/
theorem Vega.l426rb (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (j m : ℕ) (hj : j < i) (hm1 : 2 * i ≤ m) (hm : m < 3 * i - 1)
    (hjm : i < m - j) (hmj : m - j < 2 * i - 1)
    (j' m' : V) (hja : G.Adj j' Y.a) (hju : G.Adj j' Y.u)
    (hjg : G.Adj j' (Y.g (j + 2 * i - 1)))
    (hmc : G.Adj m' Y.c) (hmw : G.Adj m' Y.w) (hmg : G.Adj m' (Y.g (m - 2 * i + 1))) :
    G.Adj j' m' := by
  have hi := Y.hi
  have rr := Y.red (m - 2 * i + 1) (by omega)
  have bb := Y.blue (j + 2 * i - 1) (by omega) (by omega)
  have e2 : G.Adj (Y.g (j + 2 * i - 1)) (Y.g (j + i - 1)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  have e3 : G.Adj (Y.g (j + i - 1)) (Y.g (m - 2 * i + 1)) :=
    Y.gg _ _ (by omega) (by intro _; omega) (by intro _; omega) (by omega) (by omega)
  refine cube_force G hcube ![j', Y.g (m - 2 * i + 1), Y.c, Y.w]
    ![m', Y.g (j + 2 * i - 1), Y.a, Y.u] ?_
    (not_adj_both hcf e3 e2.symm) (not_adj_both hcf Y.vc Y.av.symm)
    (not_adj_both hcf Y.bw Y.ub.symm)
  intro p r hpr; fin_cases p <;> fin_cases r
  all_goals first | exact absurd rfl hpr | skip
  exacts [hjg, hja, hju, hmg.symm, rr.1.symm, rr.2.symm, hmc.symm, bb.1, Y.cu, hmw.symm, bb.2,
    Y.wa]

/-- Twin property for all Andrásfai edges of a maximal copy, given the two short-edge cases not
yet proved: the edge (i-1)(2i-1) (ν = 0; LPR reduces it to 0 i by τ0) and the short red-blue edges
j (j+2i-1) (LPR: τν-symmetry). -/
theorem Vega.twinGamma [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν)
    (hRGlast : ν = false → ∀ J K : V, Y.Twin J (Sum.inl (i - 1)) →
      Y.Twin K (Sum.inl (2 * i - 1)) → G.Adj J K)
    (hRB : ∀ j, 1 ≤ j → j ≤ i - 1 → ∀ J K : V, Y.Twin J (Sum.inl j) →
      Y.Twin K (Sum.inl (j + 2 * i - 1)) → G.Adj J K) :
    ∀ j k, pres i μ ν (Sum.inl j) → pres i μ ν (Sum.inl k) → AA i j k →
      ∀ J K : V, Y.Twin J (Sum.inl j) → Y.Twin K (Sum.inl k) → G.Adj J K := by
  have hi := Y.hi
  suffices H : ∀ j k, j < k → pres i μ ν (Sum.inl j) → pres i μ ν (Sum.inl k) → AA i j k →
      ∀ J K : V, Y.Twin J (Sum.inl j) → Y.Twin K (Sum.inl k) → G.Adj J K by
    intro j k hj hk h J K hJ hK
    rcases Nat.lt_or_ge j k with hjk | hjk
    · exact H j k hjk hj hk h J K hJ hK
    · have hne : k < j := by unfold AA at h; omega
      exact (H k j hne hk hj (by unfold AA at h ⊢; omega) K J hK hJ).symm
  intro j k hjk hj hk h J K hJ hK
  obtain ⟨hj1, hjn⟩ := hj
  obtain ⟨hk1, hkn⟩ := hk
  unfold AA at h
  have Jx : ∀ s, pres i μ ν s → vadj i (Sum.inl j) s → G.Adj J (Y.emb s) :=
    fun s hs hv => (hJ s hs).mpr hv
  have Kx : ∀ s, pres i μ ν s → vadj i (Sum.inl k) s → G.Adj K (Y.emb s) :=
    fun s hs hv => (hK s hs).mpr hv
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  by_cases hjr : j < i
  · by_cases hkg : k < 2 * i
    · by_cases hd : k - j = i
      · by_cases hjl : j + 2 ≤ i
        · have e : k = j + i := by omega
          subst e
          exact Y.l427rg F hcf hcube hM j hjl J K hJ hK
        · have hj' : j = i - 1 := by omega
          have hk' : k = 2 * i - 1 := by omega
          subst hj' hk'
          cases ν with
          | true => exact absurd rfl (hkn rfl)
          | false => exact hRGlast rfl J K hJ hK
      · exact Y.l426rg hcf hcube j k hjr hkg (by omega)
          J K (Jx (Sum.inr 0) (P 0 (by decide)) (Or.inl ⟨Or.inl rfl, hjr⟩))
          (Jx (Sum.inr 3) (P 3 (by decide)) (Or.inl ⟨Or.inr rfl, hjr⟩))
          (Jx (Sum.inl (j + i)) (Pl _ (by omega) (by intro _; omega))
            (by simp only [vadj, AA]; omega))
          (Kx (Sum.inr 4) (P 4 (by decide)) (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hkg⟩)))
          (Kx (Sum.inr 1) (P 1 (by decide)) (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hkg⟩)))
          (Kx (Sum.inl (k - i)) (Pl _ (by omega) (by intro _; omega))
            (by simp only [vadj, AA]; omega))
    · by_cases hd : k - j = 2 * i - 1
      · have e : k = j + 2 * i - 1 := by omega
        subst e
        exact hRB j (by omega) (by omega) J K hJ hK
      · exact Y.l426rb hcf hcube j k hjr (by omega) hk1 (by omega) (by omega) J K
          (Jx (Sum.inr 0) (P 0 (by decide)) (Or.inl ⟨Or.inl rfl, hjr⟩))
          (Jx (Sum.inr 3) (P 3 (by decide)) (Or.inl ⟨Or.inr rfl, hjr⟩))
          (Jx (Sum.inl (j + 2 * i - 1)) (Pl _ (by omega) (by intro _; omega))
            (by simp only [vadj, AA]; omega))
          (Kx (Sum.inr 2) (P 2 (by decide)) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
          (Kx (Sum.inr 5) (P 5 (by decide)) (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)))
          (Kx (Sum.inl (k - 2 * i + 1)) (Pl _ (by omega) (by intro _; omega))
            (by simp only [vadj, AA]; omega))
  · have hjg : j < 2 * i := by omega
    by_cases hd : k - j = i
    · have e : k = (j - i) + 2 * i := by omega
      have e2 : j = (j - i) + i := by omega
      rw [e] at hK
      rw [e2] at hJ
      exact Y.l427gb F hcf hcube hM (j - i) (by omega) J K hJ hK
    · exact Y.l426gb hcf hcube j k (by omega) hk1 (by omega) (by omega) J K
        (Jx (Sum.inr 4) (P 4 (by decide)) (Or.inr (Or.inl ⟨Or.inl rfl, by omega, hjg⟩)))
        (Jx (Sum.inr 1) (P 1 (by decide)) (Or.inr (Or.inl ⟨Or.inr rfl, by omega, hjg⟩)))
        (Jx (Sum.inl (j + i)) (Pl _ (by omega) (by intro _; omega))
          (by simp only [vadj, AA]; omega))
        (Kx (Sum.inr 2) (P 2 (by decide)) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
        (Kx (Sum.inr 5) (P 5 (by decide)) (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩)))
        (Kx (Sum.inl (k - i)) (Pl _ (by omega) (by intro _; omega))
          (by simp only [vadj, AA]; omega))

/-- Outer-vertex permutations of τ0 (a↔b, v↔u) and τ1 (v↔w, c↔b). -/
def perm0 : Fin 8 → Fin 8 := ![4, 3, 2, 1, 0, 5, 6, 7]

/-- Outer-vertex permutation of τ1. -/
def perm1 : Fin 8 → Fin 8 := ![0, 5, 4, 3, 2, 1, 6, 7]

/-- Twins transported to τ0: a twin of rho0 j in Y is a twin of j in Y.tau0. -/
theorem Vega.tau0_twin {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q : V) (j : ℕ)
    (hj : j < 3 * i - 1) (h : Y.Twin q (Sum.inl (rho0 i j))) : Y.tau0.Twin q (Sum.inl j) := by
  have hi := Y.hi
  rintro (k | t) hs
  · obtain ⟨hk, -⟩ := hs
    have hr := h (Sum.inl (rho0 i k))
      ⟨by unfold rho0; split_ifs <;> omega, fun h => absurd h (by decide)⟩
    have h2 : AA i (rho0 i j) (rho0 i k) ↔ AA i j k := by
      unfold AA rho0; split_ifs <;> omega
    exact hr.trans h2
  · have ht : pres i μ false (Sum.inr (perm0 t)) := by
      rcases hs with hs | hs
      · left; fin_cases t <;> simp [perm0] at hs ⊢
      · right; exact hs
    have hr := h (Sum.inr (perm0 t)) ht
    have e : Y.tau0.emb (Sum.inr t) = Y.emb (Sum.inr (perm0 t)) := by
      fin_cases t <;> rfl
    rw [e, hr]
    show colAdj i (rho0 i j) (perm0 t) ↔ colAdj i j t
    fin_cases t <;> simp [colAdj, perm0] <;> unfold rho0 <;> split_ifs <;> omega

/-- Twins transported to τ1: a twin of rho1 j in Y is a twin of j in Y.tau1. -/
theorem Vega.tau1_twin {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (q : V) (j : ℕ)
    (hj : j < 3 * i - 1) (hjn : j ≠ 2 * i - 1) (h : Y.Twin q (Sum.inl (rho1 i j))) :
    Y.tau1.Twin q (Sum.inl j) := by
  have hi := Y.hi
  rintro (k | t) hs
  · obtain ⟨hk, hkn⟩ := hs
    have hkn := hkn rfl
    have hr := h (Sum.inl (rho1 i k))
      ⟨by unfold rho1; split_ifs <;> omega, fun _ => by unfold rho1; split_ifs <;> omega⟩
    have h2 : AA i (rho1 i j) (rho1 i k) ↔ AA i j k := by
      unfold AA rho1; split_ifs <;> omega
    exact hr.trans h2
  · have ht : pres i μ true (Sum.inr (perm1 t)) := by
      rcases hs with hs | hs
      · left; fin_cases t <;> simp [perm1] at hs ⊢
      · right; exact hs
    have hr := h (Sum.inr (perm1 t)) ht
    have e : Y.tau1.emb (Sum.inr t) = Y.emb (Sum.inr (perm1 t)) := by
      fin_cases t <;> rfl
    rw [e, hr]
    show colAdj i (rho1 i j) (perm1 t) ↔ colAdj i j t
    fin_cases t <;> simp [colAdj, perm1] <;> unfold rho1 <;> split_ifs <;> omega

/-- Twin property for all Andrásfai edges of a maximal copy (LPR Lemmas 4.26, 4.27). -/
theorem Vega.twinGammaFull [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) :
    ∀ j k, pres i μ ν (Sum.inl j) → pres i μ ν (Sum.inl k) → AA i j k →
      ∀ J K : V, Y.Twin J (Sum.inl j) → Y.Twin K (Sum.inl k) → G.Adj J K := by
  have hi := Y.hi
  refine Y.twinGamma F hcf hcube hM ?_ ?_
  · intro hν J K hJ hK
    subst hν
    have e1 : rho0 i i = i - 1 := by unfold rho0; rw [if_pos (by omega)]; omega
    have e2 : rho0 i 0 = 2 * i - 1 := by unfold rho0; rw [if_pos (by omega)]; omega
    have tJ := Y.tau0_twin J i (by omega) (by rw [e1]; exact hJ)
    have tK := Y.tau0_twin K 0 (by omega) (by rw [e2]; exact hK)
    exact (Y.tau0.l427rg F hcf hcube hM 0 (by omega) K J tK (by simpa using tJ)).symm
  · intro j hj1 hj2 J K hJ hK
    cases ν with
    | false =>
      have e1 : rho0 i (2 * i - 1 - j) = j := by unfold rho0; rw [if_pos (by omega)]; omega
      have e2 : rho0 i (3 * i - 1 - j) = j + 2 * i - 1 := by
        unfold rho0; rw [if_neg (by omega)]; omega
      have tJ := Y.tau0_twin J (2 * i - 1 - j) (by omega) (by rw [e1]; exact hJ)
      have tK := Y.tau0_twin K (3 * i - 1 - j) (by omega) (by rw [e2]; exact hK)
      have a1 : 2 * i - 1 - j = (i - 1 - j) + i := by omega
      have a2 : 3 * i - 1 - j = (i - 1 - j) + 2 * i := by omega
      rw [a1] at tJ
      rw [a2] at tK
      exact Y.tau0.l427gb F hcf hcube hM (i - 1 - j) (by omega) J K tJ tK
    | true =>
      have e1 : rho1 i (i - 1 - j) = j := by unfold rho1; rw [if_pos (by omega)]; omega
      have e2 : rho1 i (2 * i - 1 - j) = j + 2 * i - 1 := by
        unfold rho1; rw [if_neg (by omega), if_neg (by omega)]; omega
      have tJ := Y.tau1_twin J (i - 1 - j) (by omega) (by omega) (by rw [e1]; exact hJ)
      have tK := Y.tau1_twin K (2 * i - 1 - j) (by omega) (by omega) (by rw [e2]; exact hK)
      have a2 : 2 * i - 1 - j = (i - 1 - j) + i := by omega
      rw [a2] at tK
      exact Y.tau1.l427rg F hcf hcube hM (i - 1 - j) (by omega) J K tJ tK

/-- LPR Lemma 4.28, first case, edge u - red j with 1 ≤ j: twins are adjacent
(Lemma 4.6 on Υ(π_{j-1}) gives a vertex with a small neighbourhood in Υ(j')). -/
theorem Vega.twin_u_red [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (j : ℕ) (hj1 : 1 ≤ j)
    (hj : j < i) (J U' : V) (hJ : Y.Twin J (Sum.inl j)) (hU : Y.Twin U' (Sum.inr 3)) :
    G.Adj J U' := by
  have hi := Y.hi
  by_contra hn
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grRed (j - 1) (j + i - 1) (j + 2 * i - 1) j (by omega) (by omega) (by omega)
    (by intro _; omega) (by omega) (by omega) hj
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have Ju : G.Adj J Y.u := (hJ (Sum.inr 3) (P 3 (by decide))).mpr (Or.inl ⟨Or.inr rfl, hj⟩)
  have Ja : G.Adj J Y.a := (hJ (Sum.inr 0) (P 0 (by decide))).mpr (Or.inl ⟨Or.inl rfl, hj⟩)
  have Jb : G.Adj J (Y.g (j + 2 * i - 1)) :=
    (hJ (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr (by simp only [vadj, AA]; omega)
  have Uc : G.Adj U' Y.c := (hU (Sum.inr 2) (P 2 (by decide))).mpr (by simp [vadj, hexAdj])
  have Ub : G.Adj U' Y.b := (hU (Sum.inr 4) (P 4 (by decide))).mpr (by simp [vadj, hexAdj])
  have Uj : G.Adj U' (Y.g j) :=
    (hU (Sum.inl j) (Pl _ (by omega) (by intro _; omega))).mpr (Or.inl ⟨Or.inr rfl, hj⟩)
  have Uj1 : G.Adj U' (Y.g (j - 1)) :=
    (hU (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr (Or.inl ⟨Or.inr rfl, by omega⟩)
  obtain ⟨t, htJ, htx, htg, -⟩ := F.l46 (hC.rotV 4) J U' Ju Jb Ja Uc Ub Uj Uj1 hn
  refine (Y.repl (Sum.inl j) J hJ).noSmallX F hcf hcube hmin hM t
    (by show G.Adj t (Function.update Y.emb (Sum.inl j) J (Sum.inr 6))
        rw [Function.update_of_ne (by simp)]; exact htx)
    j (j + i - 1) (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega))
    (by show G.Adj t (Function.update Y.emb (Sum.inl j) J (Sum.inl j))
        rw [Function.update_self]; exact htJ)
    (by show G.Adj t (Function.update Y.emb (Sum.inl j) J (Sum.inl (j + i - 1)))
        rw [Function.update_of_ne (by simp; omega)]; exact htg)
    (fun h1 _ => by have := h1.mp hj; omega)

/-- LPR Lemma 4.28, second case, edges at a (via Lemma 4.5 in red path copies Υ(π), centre a):
a twin A' of a is adjacent to every twin of a neighbour of a. -/
theorem Vega.twin_a [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (A' S : V) (hA : Y.Twin A' (Sum.inr 0))
    (s : ℕ ⊕ Fin 8) (hs : pres i μ ν s) (hv : vadj i (Sum.inr 0) s) (hS : Y.Twin S s) :
    G.Adj A' S := by
  have hi := Y.hi
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have Sx : ∀ r, pres i μ ν r → vadj i s r → G.Adj S (Y.emb r) := fun r hr h => (hS r hr).mpr h
  have Ax : ∀ r, pres i μ ν r → vadj i (Sum.inr 0) r → G.Adj A' (Y.emb r) :=
    fun r hr h => (hA r hr).mpr h
  have hC0 := Y.grRed 0 i (2 * i) 1 (by omega) le_rfl (by omega) (by intro _; omega)
    le_rfl (by omega) (by omega) (by unfold AA; omega) (by unfold AA; omega)
    (by unfold AA; omega)
  have Sa : G.Adj Y.a S := ((hS (Sum.inr 0) (P 0 (by decide))).mpr (vadj_symm' hv)).symm
  rcases s with j | t
  · have hj : j < i := by simp [vadj, colAdj] at hv; omega
    by_cases hj2 : j + 2 ≤ i
    · have hC := Y.grRed j (j + i) (j + 2 * i) (j + 1) hj (by omega) (by omega)
        (by intro _; omega) (by omega) (by omega) (by omega)
        (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
      exact F.l45 hC 1 S
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (by simp only [vadj, AA]; omega))
        (Sx _ (P 3 (by decide)) (Or.inl ⟨Or.inr rfl, hj⟩)) Sa A'
        (Ax _ (P 1 (by decide)) (by simp [vadj, hexAdj]))
        (Ax _ (Pl _ (by omega) (by intro _; omega)) (Or.inl ⟨Or.inl rfl, by omega⟩))
    · have hC := Y.grRed (j - 1) (j + i - 1) (j + 2 * i - 1) j (by omega) (by omega)
        (by omega) (by intro _; omega) (by omega) (by omega) hj
        (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
      exact F.l45 hC 4 S
        (Sx _ (P 3 (by decide)) (Or.inl ⟨Or.inr rfl, hj⟩))
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (by simp only [vadj, AA]; omega)) Sa A'
        (Ax _ (Pl _ (by omega) (by intro _; omega)) (Or.inl ⟨Or.inl rfl, by omega⟩))
        (Ax _ (P 5 (by decide)) (by simp [vadj, hexAdj]))
  · fin_cases t
    all_goals simp [vadj, hexAdj] at hv
    · exact F.l45 hC0 3 S (Sx _ (P 2 (by decide)) (by simp [vadj, hexAdj]))
        (Sx _ (Pl _ (by omega) (by intro _; omega))
          (Or.inr (Or.inl ⟨Or.inr rfl, le_rfl, by omega⟩))) Sa A'
        (Ax _ (P 6 (by decide)) (by simp [vadj, hexAdj]))
        (Ax _ (Pl _ (by omega) (by intro _; omega)) (Or.inl ⟨Or.inl rfl, by omega⟩))
    · exact F.l45 hC0 2 S
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (Or.inr (Or.inr ⟨Or.inr rfl, le_rfl⟩)))
        (Sx _ (P 4 (by decide)) (by simp [vadj, hexAdj])) Sa A'
        (Ax _ (Pl _ (by omega) (by intro _; omega)) (Or.inl ⟨Or.inl rfl, by omega⟩))
        (Ax _ (P 6 (by decide)) (by simp [vadj, hexAdj]))
    · exact F.l45 hC0 0 S (Sx _ (P 4 (by decide)) (by simp [vadj, hexAdj]))
        (Sx _ (P 2 (by decide)) (by simp [vadj, hexAdj])) Sa A'
        (Ax _ (P 5 (by decide)) (by simp [vadj, hexAdj]))
        (Ax _ (P 1 (by decide)) (by simp [vadj, hexAdj]))

instance hexAdjDec (s t : Fin 8) : Decidable (hexAdj s t) := by
  unfold hexAdj; exact inferInstance

theorem hexAdj_perm0' : ∀ s t : Fin 8, hexAdj (perm0 s) (perm0 t) ↔ hexAdj s t := by decide

theorem hexAdj_perm1' : ∀ s t : Fin 8, hexAdj (perm1 s) (perm1 t) ↔ hexAdj s t := by decide

theorem hexAdj_perm0 (s t : Fin 8) : hexAdj (perm0 s) (perm0 t) ↔ hexAdj s t :=
  hexAdj_perm0' s t

theorem hexAdj_perm1 (s t : Fin 8) : hexAdj (perm1 s) (perm1 t) ↔ hexAdj s t :=
  hexAdj_perm1' s t

/-- Twins of outer vertices transported to τ0. -/
theorem Vega.tau0_twin_out {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q : V) (t : Fin 8)
    (h : Y.Twin q (Sum.inr (perm0 t))) : Y.tau0.Twin q (Sum.inr t) := by
  have hi := Y.hi
  rintro (k | s) hs
  · obtain ⟨hk, -⟩ := hs
    have hr := h (Sum.inl (rho0 i k))
      ⟨by unfold rho0; split_ifs <;> omega, fun h => absurd h (by decide)⟩
    have h2 : colAdj i (rho0 i k) (perm0 t) ↔ colAdj i k t := by
      fin_cases t <;> simp [colAdj, perm0] <;> unfold rho0 <;> split_ifs <;> omega
    exact hr.trans h2
  · have hs' : pres i μ false (Sum.inr (perm0 s)) := by
      rcases hs with hs | hs
      · left; fin_cases s <;> simp [perm0] at hs ⊢
      · right; exact hs
    have hr := h (Sum.inr (perm0 s)) hs'
    have e : Y.tau0.emb (Sum.inr s) = Y.emb (Sum.inr (perm0 s)) := by
      fin_cases s <;> rfl
    rw [e]
    exact hr.trans (hexAdj_perm0 t s)

/-- Twins of outer vertices transported to τ1. -/
theorem Vega.tau1_twin_out {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (q : V) (t : Fin 8)
    (h : Y.Twin q (Sum.inr (perm1 t))) : Y.tau1.Twin q (Sum.inr t) := by
  have hi := Y.hi
  rintro (k | s) hs
  · obtain ⟨hk, hkn⟩ := hs
    have hkn := hkn rfl
    have hr := h (Sum.inl (rho1 i k))
      ⟨by unfold rho1; split_ifs <;> omega, fun _ => by unfold rho1; split_ifs <;> omega⟩
    have h2 : colAdj i (rho1 i k) (perm1 t) ↔ colAdj i k t := by
      fin_cases t <;> simp [colAdj, perm1] <;> unfold rho1 <;> split_ifs <;> omega
    exact hr.trans h2
  · have hs' : pres i μ true (Sum.inr (perm1 s)) := by
      rcases hs with hs | hs
      · left; fin_cases s <;> simp [perm1] at hs ⊢
      · right; exact hs
    have hr := h (Sum.inr (perm1 s)) hs'
    have e : Y.tau1.emb (Sum.inr s) = Y.emb (Sum.inr (perm1 s)) := by
      fin_cases s <;> rfl
    rw [e]
    exact hr.trans (hexAdj_perm1 t s)

theorem rho0_rho0 {i : ℕ} (hi : 2 ≤ i) (k : ℕ) (hk : k < 3 * i - 1) :
    rho0 i (rho0 i k) = k := by
  unfold rho0; split_ifs <;> omega

theorem perm0_perm0 : ∀ t : Fin 8, perm0 (perm0 t) = t := by decide

theorem perm1_perm1 : ∀ t : Fin 8, perm1 (perm1 t) = t := by decide

/-- Edges at b for ν = 0, via τ0 (b ↔ a) and `twin_a`. -/
theorem Vega.twin_b0 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (B' S : V) (hB : Y.Twin B' (Sum.inr 4))
    (s : ℕ ⊕ Fin 8) (hs : pres i μ false s) (hv : vadj i (Sum.inr 4) s) (hS : Y.Twin S s) :
    G.Adj B' S := by
  have hi := Y.hi
  have tB : Y.tau0.Twin B' (Sum.inr 0) := Y.tau0_twin_out B' 0 hB
  rcases s with k | t
  · have hk := hs.1
    have tS := Y.tau0_twin S (rho0 i k) (by unfold rho0; split_ifs <;> omega)
      (by rw [rho0_rho0 hi k hk]; exact hS)
    refine Y.tau0.twin_a F B' S tB (Sum.inl (rho0 i k))
      ⟨by unfold rho0; split_ifs <;> omega, fun h => absurd h (by decide)⟩ ?_ tS
    simp only [vadj, colAdj] at hv ⊢
    unfold rho0; split_ifs <;> simp at hv ⊢ <;> omega
  · have tS := Y.tau0_twin_out S (perm0 t) (by rw [perm0_perm0]; exact hS)
    refine Y.tau0.twin_a F B' S tB (Sum.inr (perm0 t)) ?_ ?_ tS
    · rcases hs with hs | hs
      · left; fin_cases t <;> simp [perm0] at hs ⊢
      · right; exact hs
    · exact (hexAdj_perm0 4 t).mpr hv

/-- Edge v - green j (ν = 0, j ≤ 2i-2), via τ0 from `twin_u_red`. -/
theorem Vega.twin_v_green0 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (hM : VegaMax G i μ false) (j : ℕ)
    (hj1 : i ≤ j) (hj2 : j ≤ 2 * i - 2) (J V' : V) (hJ : Y.Twin J (Sum.inl j))
    (hV : Y.Twin V' (Sum.inr 1)) : G.Adj J V' := by
  have hi := Y.hi
  have e : rho0 i (2 * i - 1 - j) = j := by unfold rho0; rw [if_pos (by omega)]; omega
  have tJ := Y.tau0_twin J (2 * i - 1 - j) (by omega) (by rw [e]; exact hJ)
  have tV : Y.tau0.Twin V' (Sum.inr 3) := Y.tau0_twin_out V' 3 hV
  exact Y.tau0.twin_u_red F hcf hcube hmin hM (2 * i - 1 - j) (by omega) (by omega) J V' tJ tV

/-- LPR Lemma 4.28, edges at b for i ≥ 3 (Lemma 4.5 in green path copies, centre b). -/
theorem Vega.twin_b [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hi3 : 3 ≤ i) (B' S : V)
    (hB : Y.Twin B' (Sum.inr 4)) (s : ℕ ⊕ Fin 8) (hs : pres i μ ν s)
    (hv : vadj i (Sum.inr 4) s) (hS : Y.Twin S s) : G.Adj B' S := by
  have hi := Y.hi
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have Sx : ∀ r, pres i μ ν r → vadj i s r → G.Adj S (Y.emb r) := fun r hr h => (hS r hr).mpr h
  have Bx : ∀ r, pres i μ ν r → vadj i (Sum.inr 4) r → G.Adj B' (Y.emb r) :=
    fun r hr h => (hB r hr).mpr h
  have Sb : G.Adj Y.b S := ((hS (Sum.inr 4) (P 4 (by decide))).mpr (vadj_symm' hv)).symm
  have hC := Y.grGreen (i + 1) 1 (2 * i) i (by omega) (by omega) (by intro _; omega) (by omega)
    le_rfl (by omega) le_rfl (by omega) (by intro _; omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases s with j | t
  · have hj : i ≤ j ∧ j < 2 * i := by simp [vadj, colAdj] at hv; omega
    obtain ⟨hj1, hjn⟩ := hs
    by_cases hji : j = i
    · subst hji
      exact F.l45 hC 3 S
        (Sx _ (P 1 (by decide)) (Or.inr (Or.inl ⟨Or.inr rfl, le_rfl, by omega⟩)))
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (by simp only [vadj, AA]; omega)) Sb B'
        (Bx _ (Pl _ (by omega) (by intro _; omega))
          (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)))
        (Bx _ (P 5 (by decide)) (by simp [vadj, hexAdj]))
    · have hC' := Y.grGreen j (j - i) (j + i - 1) (j - 1) (by omega) (by omega) hjn (by omega)
        (by omega) (by omega) (by omega) (by omega) (by intro _; omega)
        (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
      exact F.l45 hC' 0 S
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (by simp only [vadj, AA]; omega))
        (Sx _ (P 1 (by decide)) (Or.inr (Or.inl ⟨Or.inr rfl, by omega, by omega⟩))) Sb B'
        (Bx _ (P 3 (by decide)) (by simp [vadj, hexAdj]))
        (Bx _ (Pl _ (by omega) (by intro _; omega))
          (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)))
  · fin_cases t
    all_goals simp [vadj, hexAdj] at hv
    · exact F.l45 hC 2 S (Sx _ (P 2 (by decide)) (by simp [vadj, hexAdj]))
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (Or.inl ⟨Or.inr rfl, by omega⟩)) Sb B'
        (Bx _ (P 6 (by decide)) (by simp [vadj, hexAdj]))
        (Bx _ (Pl _ (by omega) (by intro _; omega))
          (Or.inr (Or.inl ⟨Or.inl rfl, by omega, by omega⟩)))
    · exact F.l45 hC 1 S
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (Or.inr (Or.inr ⟨Or.inr rfl, le_rfl⟩)))
        (Sx _ (P 0 (by decide)) (by simp [vadj, hexAdj])) Sb B'
        (Bx _ (Pl _ (by omega) (by intro _; omega))
          (Or.inr (Or.inl ⟨Or.inl rfl, le_rfl, by omega⟩)))
        (Bx _ (P 6 (by decide)) (by simp [vadj, hexAdj]))
    · exact F.l45 hC 4 S (Sx _ (P 0 (by decide)) (by simp [vadj, hexAdj]))
        (Sx _ (P 2 (by decide)) (by simp [vadj, hexAdj])) Sb B'
        (Bx _ (P 5 (by decide)) (by simp [vadj, hexAdj]))
        (Bx _ (P 3 (by decide)) (by simp [vadj, hexAdj]))

/-- LPR Lemma 4.28, edges at c for i ≥ 3 (Lemma 4.5 in blue path copies, centre c). -/
theorem Vega.twin_c [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hi3 : 3 ≤ i) (C' S : V)
    (hC' : Y.Twin C' (Sum.inr 2)) (s : ℕ ⊕ Fin 8) (hs : pres i μ ν s)
    (hv : vadj i (Sum.inr 2) s) (hS : Y.Twin S s) : G.Adj C' S := by
  have hi := Y.hi
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have Sx : ∀ r, pres i μ ν r → vadj i s r → G.Adj S (Y.emb r) := fun r hr h => (hS r hr).mpr h
  have Cx : ∀ r, pres i μ ν r → vadj i (Sum.inr 2) r → G.Adj C' (Y.emb r) :=
    fun r hr h => (hC' r hr).mpr h
  have Sc : G.Adj Y.c S := ((hS (Sum.inr 2) (P 2 (by decide))).mpr (vadj_symm' hv)).symm
  have hC := Y.grBlue (2 * i) 1 (i + 1) (2 * i + 1) le_rfl (by omega) (by omega) (by omega)
    (by omega) (by intro _; omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases s with j | t
  · have hj : 2 * i ≤ j := by simp [vadj, colAdj] at hv; omega
    have hj1 := hs.1
    by_cases hji : j = 2 * i
    · subst hji
      exact F.l45 hC 0 S
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (by simp only [vadj, AA]; omega))
        (Sx _ (P 5 (by decide)) (Or.inr (Or.inr ⟨Or.inr rfl, le_rfl⟩))) Sc C'
        (Cx _ (P 3 (by decide)) (by simp [vadj, hexAdj]))
        (Cx _ (Pl _ (by omega) (by intro _; omega)) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
    · have hD := Y.grBlue (j - 1) (j - 2 * i) (j - i) j (by omega) (by omega) (by omega)
        (by omega) (by omega) (by intro _; omega) hj hj1
        (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
      exact F.l45 hD 3 S (Sx _ (P 5 (by decide)) (Or.inr (Or.inr ⟨Or.inr rfl, hj⟩)))
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (by simp only [vadj, AA]; omega)) Sc C'
        (Cx _ (Pl _ (by omega) (by intro _; omega)) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
        (Cx _ (P 1 (by decide)) (by simp [vadj, hexAdj]))
  · fin_cases t
    all_goals simp [vadj, hexAdj] at hv
    · exact F.l45 hC 1 S
        (Sx _ (Pl _ (by omega) (by intro _; omega))
          (Or.inr (Or.inl ⟨Or.inr rfl, by omega, by omega⟩)))
        (Sx _ (P 0 (by decide)) (by simp [vadj, hexAdj])) Sc C'
        (Cx _ (Pl _ (by omega) (by intro _; omega)) (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩)))
        (Cx _ (P 6 (by decide)) (by simp [vadj, hexAdj]))
    · exact F.l45 hC 2 S (Sx _ (P 4 (by decide)) (by simp [vadj, hexAdj]))
        (Sx _ (Pl _ (by omega) (by intro _; omega)) (Or.inl ⟨Or.inr rfl, by omega⟩)) Sc C'
        (Cx _ (P 6 (by decide)) (by simp [vadj, hexAdj]))
        (Cx _ (Pl _ (by omega) (by intro _; omega)) (Or.inr (Or.inr ⟨Or.inl rfl, le_rfl⟩)))
    · exact F.l45 hC 4 S (Sx _ (P 0 (by decide)) (by simp [vadj, hexAdj]))
        (Sx _ (P 4 (by decide)) (by simp [vadj, hexAdj])) Sc C'
        (Cx _ (P 1 (by decide)) (by simp [vadj, hexAdj]))
        (Cx _ (P 3 (by decide)) (by simp [vadj, hexAdj]))

theorem IsGr.reflV {v u : Fin 5 → V} {w : V} (h : IsGr G v u w) :
    IsGr G (fun i => v (-i)) (fun i => u (-i)) w := by
  intro i
  have e1 : ∀ j : Fin 5, -(j + 1) + 1 = -j := by decide
  have e2 : ∀ j : Fin 5, -j + 4 = -(j + 1) := by decide
  have e3 : ∀ j : Fin 5, -j + 1 = -(j + 4) := by decide
  have a1 := (h (-(i + 1))).1
  rw [e1] at a1
  have a2 := (h (-i)).2.2.1
  rw [e2] at a2
  have a3 := (h (-i)).2.1
  rw [e3] at a3
  exact ⟨a1.symm, a2, a3, (h (-i)).2.2.2⟩

/-- LPR Lemma 4.28, first case, edge u - red 0 (reflected Υ(π_0)). -/
theorem Vega.twin_u_red0 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν)
    (J U' : V) (hJ : Y.Twin J (Sum.inl 0)) (hU : Y.Twin U' (Sum.inr 3)) : G.Adj J U' := by
  have hi := Y.hi
  by_contra hn
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grRed 0 i (2 * i) 1 (by omega) le_rfl (by omega) (by intro _; omega)
    le_rfl (by omega) (by omega) (by unfold AA; omega) (by unfold AA; omega)
    (by unfold AA; omega)
  have Ju : G.Adj J Y.u :=
    (hJ (Sum.inr 3) (P 3 (by decide))).mpr (Or.inl ⟨Or.inr rfl, by omega⟩)
  have Ja : G.Adj J Y.a :=
    (hJ (Sum.inr 0) (P 0 (by decide))).mpr (Or.inl ⟨Or.inl rfl, by omega⟩)
  have Ji : G.Adj J (Y.g i) :=
    (hJ (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr (by simp only [vadj, AA]; omega)
  have Uc : G.Adj U' Y.c := (hU (Sum.inr 2) (P 2 (by decide))).mpr (by simp [vadj, hexAdj])
  have Ub : G.Adj U' Y.b := (hU (Sum.inr 4) (P 4 (by decide))).mpr (by simp [vadj, hexAdj])
  have U0 : G.Adj U' (Y.g 0) :=
    (hU (Sum.inl 0) (Pl _ (by omega) (by intro _; omega))).mpr (Or.inl ⟨Or.inr rfl, by omega⟩)
  have U1 : G.Adj U' (Y.g 1) :=
    (hU (Sum.inl 1) (Pl _ (by omega) (by intro _; omega))).mpr (Or.inl ⟨Or.inr rfl, by omega⟩)
  obtain ⟨t, htJ, htx, htb, -⟩ := F.l46 (hC.reflV.rotV 4) J U' Ju Ji Ja Ub Uc U0 U1 hn
  refine (Y.repl (Sum.inl 0) J hJ).noSmallX F hcf hcube hmin hM t
    (by show G.Adj t (Function.update Y.emb (Sum.inl 0) J (Sum.inr 6))
        rw [Function.update_of_ne (by simp)]; exact htx)
    0 (2 * i) (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega))
    (by show G.Adj t (Function.update Y.emb (Sum.inl 0) J (Sum.inl 0))
        rw [Function.update_self]; exact htJ)
    (by show G.Adj t (Function.update Y.emb (Sum.inl 0) J (Sum.inl (2 * i)))
        rw [Function.update_of_ne (by simp; omega)]; exact htb)
    (fun _ h2 => by have := h2.mp (by omega); omega)

/-- LPR Lemma 4.28, first case, edge w - blue j with j ≥ 2i+1 (Lemma 4.6 in a blue path copy,
then a small neighbourhood in Υ(j')). -/
theorem Vega.twin_w_blue [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (j : ℕ)
    (hj1 : 2 * i + 1 ≤ j) (hj : j < 3 * i - 1) (J W' : V) (hJ : Y.Twin J (Sum.inl j))
    (hW : Y.Twin W' (Sum.inr 5)) : G.Adj J W' := by
  have hi := Y.hi
  by_contra hn
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hD := Y.grBlue (j - 1) (j - 2 * i) (j - i) j (by omega) (by omega) (by omega)
    (by omega) (by omega) (by intro _; omega) (by omega) hj
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have Jw : G.Adj J Y.w :=
    (hJ (Sum.inr 5) (P 5 (by decide))).mpr (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))
  have Jc : G.Adj J Y.c :=
    (hJ (Sum.inr 2) (P 2 (by decide))).mpr (Or.inr (Or.inr ⟨Or.inl rfl, by omega⟩))
  have Jg : G.Adj J (Y.g (j - i)) :=
    (hJ (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr (by simp only [vadj, AA]; omega)
  have Wb : G.Adj W' Y.b := (hW (Sum.inr 4) (P 4 (by decide))).mpr (by simp [vadj, hexAdj])
  have Wa : G.Adj W' Y.a := (hW (Sum.inr 0) (P 0 (by decide))).mpr (by simp [vadj, hexAdj])
  have Wj : G.Adj W' (Y.g j) :=
    (hW (Sum.inl j) (Pl _ hj (by intro _; omega))).mpr (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))
  have Wj1 : G.Adj W' (Y.g (j - 1)) :=
    (hW (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr
      (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))
  obtain ⟨t, htJ, htx, htr, -⟩ := F.l46 (hD.rotV 3) J W' Jw Jg Jc Wb Wa Wj Wj1 hn
  refine (Y.repl (Sum.inl j) J hJ).noSmallX F hcf hcube hmin hM t
    (by show G.Adj t (Function.update Y.emb (Sum.inl j) J (Sum.inr 6))
        rw [Function.update_of_ne (by simp)]; exact htx)
    j (j - 2 * i) (Pl _ hj (by intro _; omega)) (Pl _ (by omega) (by intro _; omega))
    (by show G.Adj t (Function.update Y.emb (Sum.inl j) J (Sum.inl j))
        rw [Function.update_self]; exact htJ)
    (by show G.Adj t (Function.update Y.emb (Sum.inl j) J (Sum.inl (j - 2 * i)))
        rw [Function.update_of_ne (by simp; omega)]; exact htr)
    (fun h1 _ => by have := h1.mpr (by omega); omega)

/-- Edge w - blue 2i for i ≥ 3 (reflected blue path copy (2i, 1, i+1, 2i+1)). -/
theorem Vega.twin_w_blue0 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 3 ≤ i)
    (J W' : V) (hJ : Y.Twin J (Sum.inl (2 * i))) (hW : Y.Twin W' (Sum.inr 5)) :
    G.Adj J W' := by
  have hi := Y.hi
  by_contra hn
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grBlue (2 * i) 1 (i + 1) (2 * i + 1) le_rfl (by omega) (by omega) (by omega)
    (by omega) (by intro _; omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have Jw : G.Adj J Y.w :=
    (hJ (Sum.inr 5) (P 5 (by decide))).mpr (Or.inr (Or.inr ⟨Or.inr rfl, le_rfl⟩))
  have Jc : G.Adj J Y.c :=
    (hJ (Sum.inr 2) (P 2 (by decide))).mpr (Or.inr (Or.inr ⟨Or.inl rfl, le_rfl⟩))
  have J1 : G.Adj J (Y.g 1) :=
    (hJ (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr (by simp only [vadj, AA]; omega)
  have Wa : G.Adj W' Y.a := (hW (Sum.inr 0) (P 0 (by decide))).mpr (by simp [vadj, hexAdj])
  have Wb : G.Adj W' Y.b := (hW (Sum.inr 4) (P 4 (by decide))).mpr (by simp [vadj, hexAdj])
  have W0 : G.Adj W' (Y.g (2 * i)) :=
    (hW (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr
      (Or.inr (Or.inr ⟨Or.inr rfl, le_rfl⟩))
  have W1 : G.Adj W' (Y.g (2 * i + 1)) :=
    (hW (Sum.inl _) (Pl _ (by omega) (by intro _; omega))).mpr
      (Or.inr (Or.inr ⟨Or.inr rfl, by omega⟩))
  obtain ⟨t, htJ, htx, htg, -⟩ := F.l46 hC.reflV J W' Jw J1 Jc Wa Wb W0 W1 hn
  refine (Y.repl (Sum.inl (2 * i)) J hJ).noSmallX F hcf hcube hmin hM t
    (by show G.Adj t (Function.update Y.emb (Sum.inl (2 * i)) J (Sum.inr 6))
        rw [Function.update_of_ne (by simp)]; exact htx)
    (2 * i) (i + 1) (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega))
    (by show G.Adj t (Function.update Y.emb (Sum.inl (2 * i)) J (Sum.inl (2 * i)))
        rw [Function.update_self]; exact htJ)
    (by show G.Adj t (Function.update Y.emb (Sum.inl (2 * i)) J (Sum.inl (i + 1)))
        rw [Function.update_of_ne (by simp; omega)]; exact htg)
    (fun _ h2 => by have := h2.mpr (by omega); omega)

/-- Edge v - green 2i-1 (ν = 0), via τ0 from `twin_u_red0`. -/
theorem Vega.twin_v_green0' [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (hM : VegaMax G i μ false)
    (J V' : V) (hJ : Y.Twin J (Sum.inl (2 * i - 1))) (hV : Y.Twin V' (Sum.inr 1)) :
    G.Adj J V' := by
  have hi := Y.hi
  have e : rho0 i 0 = 2 * i - 1 := by unfold rho0; rw [if_pos (by omega)]; omega
  have tJ := Y.tau0_twin J 0 (by omega) (by rw [e]; exact hJ)
  have tV : Y.tau0.Twin V' (Sum.inr 3) := Y.tau0_twin_out V' 3 hV
  exact Y.tau0.twin_u_red0 F hcf hcube hmin hM J V' tJ tV

/-- Edge v - green j for ν = 1 and i ≥ 3, via τ1 (v ↔ w, green ↔ blue). -/
theorem Vega.twin_v_green1 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (hM : VegaMax G i μ true) (hi3 : 3 ≤ i) (j : ℕ)
    (hj1 : i ≤ j) (hj2 : j ≤ 2 * i - 2) (J V' : V) (hJ : Y.Twin J (Sum.inl j))
    (hV : Y.Twin V' (Sum.inr 1)) : G.Adj J V' := by
  have hi := Y.hi
  have e : rho1 i (4 * i - 2 - j) = j := by
    unfold rho1; rw [if_neg (by omega), if_neg (by omega)]; omega
  have tJ := Y.tau1_twin J (4 * i - 2 - j) (by omega) (by omega) (by rw [e]; exact hJ)
  have tV : Y.tau1.Twin V' (Sum.inr 5) := Y.tau1_twin_out V' 5 hV
  by_cases hj : j ≤ 2 * i - 3
  · exact Y.tau1.twin_w_blue F hcf hcube hmin hM (4 * i - 2 - j) (by omega) (by omega)
      J V' tJ tV
  · have e2 : 4 * i - 2 - j = 2 * i := by omega
    rw [e2] at tJ
    exact Y.tau1.twin_w_blue0 F hcf hcube hmin hM hi3 J V' tJ tV

/-- Outer-vertex permutation of σ (a↔u, b↔v, c↔w, x↔y). -/
def permS : Fin 8 → Fin 8 := ![3, 4, 5, 0, 1, 2, 7, 6]

theorem hexAdj_permS' : ∀ s t : Fin 8, hexAdj (permS s) (permS t) ↔ hexAdj s t := by decide

theorem permS_permS : ∀ t : Fin 8, permS (permS t) = t := by decide

/-- Twins transported to σ. -/
theorem Vega.sigma_twin {i : ℕ} {ν : Bool} (Y : Vega G i false ν) (q : V) (s : ℕ ⊕ Fin 8)
    (h : Y.Twin q (match s with | Sum.inl j => Sum.inl j | Sum.inr t => Sum.inr (permS t))) :
    Y.sigma.Twin q s := by
  have hi := Y.hi
  rcases s with j | t
  · rintro (k | r) hs
    · exact h (Sum.inl k) hs
    · have hr := h (Sum.inr (permS r)) (Or.inr rfl)
      have e : Y.sigma.emb (Sum.inr r) = Y.emb (Sum.inr (permS r)) := by fin_cases r <;> rfl
      rw [e]
      refine hr.trans ?_
      show colAdj i j (permS r) ↔ colAdj i j r
      fin_cases r <;> simp [colAdj, permS]
  · rintro (k | r) hs
    · have hr := h (Sum.inl k) hs
      refine hr.trans ?_
      show colAdj i k (permS t) ↔ colAdj i k t
      fin_cases t <;> simp [colAdj, permS]
    · have hr := h (Sum.inr (permS r)) (Or.inr rfl)
      have e : Y.sigma.emb (Sum.inr r) = Y.emb (Sum.inr (permS r)) := by fin_cases r <;> rfl
      rw [e]
      exact hr.trans (hexAdj_permS' t r)

/-- Twin property for edges between an Andrásfai vertex and an outer vertex (i ≥ 3). -/
theorem Vega.twin_Γout [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 3 ≤ i)
    (j : ℕ) (t : Fin 8) (hj : pres i μ ν (Sum.inl j)) (ht : pres i μ ν (Sum.inr t))
    (hv : vadj i (Sum.inl j) (Sum.inr t)) (J T : V) (hJ : Y.Twin J (Sum.inl j))
    (hT : Y.Twin T (Sum.inr t)) : G.Adj J T := by
  have hi := Y.hi
  obtain ⟨hj1, hjn⟩ := hj
  fin_cases t
  · exact (Y.twin_a F T J hT (Sum.inl j) ⟨hj1, hjn⟩ (vadj_symm' hv) hJ).symm
  · have hg : i ≤ j ∧ j < 2 * i := by simp [vadj, colAdj] at hv; omega
    cases ν with
    | false =>
      by_cases hj2 : j ≤ 2 * i - 2
      · exact Y.twin_v_green0 F hcf hcube hmin hM j hg.1 hj2 J T hJ hT
      · have e : j = 2 * i - 1 := by omega
        subst e
        exact Y.twin_v_green0' F hcf hcube hmin hM J T hJ hT
    | true =>
      have := hjn rfl
      exact Y.twin_v_green1 F hcf hcube hmin hM hi3 j hg.1 (by omega) J T hJ hT
  · exact (Y.twin_c F hi3 T J hT (Sum.inl j) ⟨hj1, hjn⟩ (vadj_symm' hv) hJ).symm
  · have hr : j < i := by simp [vadj, colAdj] at hv; omega
    by_cases h0 : j = 0
    · subst h0; exact Y.twin_u_red0 F hcf hcube hmin hM J T hJ hT
    · exact Y.twin_u_red F hcf hcube hmin hM j (by omega) hr J T hJ hT
  · exact (Y.twin_b F hi3 T J hT (Sum.inl j) ⟨hj1, hjn⟩ (vadj_symm' hv) hJ).symm
  · have hb : 2 * i ≤ j := by simp [vadj, colAdj] at hv; omega
    by_cases h0 : j = 2 * i
    · subst h0; exact Y.twin_w_blue0 F hcf hcube hmin hM hi3 J T hJ hT
    · exact Y.twin_w_blue F hcf hcube hmin hM j (by omega) hj1 J T hJ hT
  · exact absurd hv (by simp [vadj, colAdj])
  · exact absurd hv (by simp [vadj, colAdj])

/-- Twin property for edges between two outer vertices (i ≥ 3). -/
theorem Vega.twin_outout [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hi3 : 3 ≤ i) (s t : Fin 8) (hs : pres i μ ν (Sum.inr s)) (ht : pres i μ ν (Sum.inr t))
    (hv : vadj i (Sum.inr s) (Sum.inr t)) (S T : V) (hS : Y.Twin S (Sum.inr s))
    (hT : Y.Twin T (Sum.inr t)) : G.Adj S T := by
  have hy : ∀ r : Fin 8, pres i μ ν (Sum.inr r) → r.val = 7 → μ = false := by
    intro r hr h7; rcases hr with hr | hr
    · omega
    · exact hr
  have hyS := hy s hs
  have hyT := hy t ht
  have P : ∀ r : Fin 8, r.val < 7 → pres i μ ν (Sum.inr r) := fun r hr => Or.inl hr
  fin_cases s <;> fin_cases t
  all_goals first
    | (exfalso; revert hv; simp [vadj, hexAdj]; done)
    | exact Y.twin_a F S T hS _ ht hv hT
    | exact (Y.twin_a F T S hT _ hs (vadj_symm' hv) hS).symm
    | exact Y.twin_b F hi3 S T hS _ ht hv hT
    | exact (Y.twin_b F hi3 T S hT _ hs (vadj_symm' hv) hS).symm
    | exact Y.twin_c F hi3 S T hS _ ht hv hT
    | exact (Y.twin_c F hi3 T S hT _ hs (vadj_symm' hv) hS).symm
    | skip
  -- remaining: x - y and y - u, v, w (μ = 0)
  all_goals (obtain rfl : μ = false := by first | exact hyS rfl | exact hyT rfl)
  · -- v - y  (σ: v ↦ b, y ↦ x)
    exact Y.sigma.twin_b F hi3 S T (Y.sigma_twin S (Sum.inr 4) hS) (Sum.inr 6) (Or.inr rfl)
      (by simp [vadj, hexAdj]) (Y.sigma_twin T (Sum.inr 6) hT)
  · -- u - y
    exact Y.sigma.twin_a F S T (Y.sigma_twin S (Sum.inr 0) hS) (Sum.inr 6) (Or.inr rfl)
      (by simp [vadj, hexAdj]) (Y.sigma_twin T (Sum.inr 6) hT)
  · -- w - y
    exact Y.sigma.twin_c F hi3 S T (Y.sigma_twin S (Sum.inr 2) hS) (Sum.inr 6) (Or.inr rfl)
      (by simp [vadj, hexAdj]) (Y.sigma_twin T (Sum.inr 6) hT)
  · -- x - y
    exact Y.l426xy hcf hcube S T
      ((hS (Sum.inr 0) (P 0 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hS (Sum.inr 4) (P 4 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hS (Sum.inr 2) (P 2 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hT (Sum.inr 3) (P 3 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hT (Sum.inr 1) (P 1 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hT (Sum.inr 5) (P 5 (by decide))).mpr (by simp [vadj, hexAdj]))
  · exact (Y.sigma.twin_b F hi3 T S (Y.sigma_twin T (Sum.inr 4) hT) (Sum.inr 6) (Or.inr rfl)
      (by simp [vadj, hexAdj]) (Y.sigma_twin S (Sum.inr 6) hS)).symm
  · exact (Y.sigma.twin_a F T S (Y.sigma_twin T (Sum.inr 0) hT) (Sum.inr 6) (Or.inr rfl)
      (by simp [vadj, hexAdj]) (Y.sigma_twin S (Sum.inr 6) hS)).symm
  · exact (Y.sigma.twin_c F hi3 T S (Y.sigma_twin T (Sum.inr 2) hT) (Sum.inr 6) (Or.inr rfl)
      (by simp [vadj, hexAdj]) (Y.sigma_twin S (Sum.inr 6) hS)).symm
  · exact (Y.l426xy hcf hcube T S
      ((hT (Sum.inr 0) (P 0 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hT (Sum.inr 4) (P 4 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hT (Sum.inr 2) (P 2 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hS (Sum.inr 3) (P 3 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hS (Sum.inr 1) (P 1 (by decide))).mpr (by simp [vadj, hexAdj]))
      ((hS (Sum.inr 5) (P 5 (by decide))).mpr (by simp [vadj, hexAdj]))).symm

/-- The twin lemma (LPR 4.28) for maximal copies with i ≥ 3. -/
theorem Vega.twinProp_ge3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 3 ≤ i) :
    Y.TwinProp := by
  intro p s hp hs hv p' s' hp' hs'
  rcases p with j | t <;> rcases s with k | t'
  · exact Y.twinGammaFull F hcf hcube hM j k hp hs hv p' s' hp' hs'
  · exact Y.twin_Γout F hcf hcube hmin hM hi3 j t' hp hs hv p' s' hp' hs'
  · exact (Y.twin_Γout F hcf hcube hmin hM hi3 k t hs hp (vadj_symm' hv) s' p' hs' hp').symm
  · exact Y.twin_outout F hcf hcube hi3 t t' hp hs hv p' s' hp' hs'

/-- Bool version of colAdj. -/
def colB (i j : ℕ) (t : Fin 8) : Bool :=
  ((t.val == 0 || t.val == 3) && decide (j < i)) ||
  ((t.val == 4 || t.val == 1) && decide (i ≤ j) && decide (j < 2 * i)) ||
  ((t.val == 2 || t.val == 5) && decide (2 * i ≤ j))

/-- Bool version of vadj. -/
def vadjB (i : ℕ) : ℕ ⊕ Fin 8 → ℕ ⊕ Fin 8 → Bool
  | Sum.inl j, Sum.inl k =>
      (decide (i ≤ j - k) && decide (j - k ≤ 2 * i - 1)) ||
      (decide (i ≤ k - j) && decide (k - j ≤ 2 * i - 1))
  | Sum.inl j, Sum.inr t => colB i j t
  | Sum.inr t, Sum.inl j => colB i j t
  | Sum.inr s, Sum.inr t => decide (hexAdj s t)

theorem vadj_iff_B (i : ℕ) (p s : ℕ ⊕ Fin 8) : vadj i p s ↔ vadjB i p s = true := by
  rcases p with j | a <;> rcases s with k | b
  · simp [vadj, vadjB, AA]
  · simp [vadj, vadjB, colAdj, colB, and_assoc, or_assoc]
  · simp [vadj, vadjB, colAdj, colB, and_assoc, or_assoc]
  · simp [vadj, vadjB]

/-- ϱ on ℕ ⊕ Fin 8 (for i = 2): 0↔x, 1↔w, 2↔c, 3↔y, u↔b. -/
def rhoP : ℕ ⊕ Fin 8 → ℕ ⊕ Fin 8
  | Sum.inl j => if j = 0 then Sum.inr 6 else if j = 1 then Sum.inr 5 else if j = 2 then Sum.inr 2
      else if j = 3 then Sum.inr 7 else Sum.inl j
  | Sum.inr t => ![Sum.inr 0, Sum.inr 1, Sum.inl 2, Sum.inr 4, Sum.inr 3, Sum.inl 1, Sum.inl 0,
      Sum.inl 3] t

/-- Present vertices of Υ_2 as Fin 5 ⊕ Fin 8. -/
def e5 : Fin 5 ⊕ Fin 8 → ℕ ⊕ Fin 8
  | Sum.inl j => Sum.inl j.val
  | Sum.inr t => Sum.inr t

theorem rhoP_inv : ∀ a b : Fin 5 ⊕ Fin 8,
    vadjB 2 (rhoP (e5 a)) (rhoP (e5 b)) = vadjB 2 (e5 a) (e5 b) := by decide

theorem rhoP_rhoP : ∀ a : Fin 5 ⊕ Fin 8, rhoP (rhoP (e5 a)) = e5 a := by decide

/-- Bool version of pres. -/
def presB (i : ℕ) (μ ν : Bool) : ℕ ⊕ Fin 8 → Bool
  | Sum.inl j => decide (j < 3 * i - 1) && (!ν || decide (j ≠ 2 * i - 1))
  | Sum.inr t => decide (t.val < 7) || !μ

theorem pres_iff_B (i : ℕ) (μ ν : Bool) (p : ℕ ⊕ Fin 8) : pres i μ ν p ↔ presB i μ ν p = true := by
  rcases p with j | t
  · cases ν <;> simp [pres, presB]
  · cases μ <;> simp [pres, presB]

theorem rhoP_pres : ∀ (μ ν : Bool) (a : Fin 5 ⊕ Fin 8),
    presB 2 ν μ (e5 a) = presB 2 μ ν (rhoP (e5 a)) := by decide

theorem e5_surj (μ ν : Bool) (s : ℕ ⊕ Fin 8) (hs : pres 2 μ ν s) : ∃ a, e5 a = s := by
  rcases s with j | t
  · exact ⟨Sum.inl ⟨j, by have := hs.1; omega⟩, rfl⟩
  · exact ⟨Sum.inr t, rfl⟩

theorem Vega.rho2_emb {μ ν : Bool} (Y : Vega G 2 μ ν) (a : Fin 5 ⊕ Fin 8) :
    Y.rho2.emb (e5 a) = Y.emb (rhoP (e5 a)) := by
  rcases a with j | t
  · fin_cases j <;> rfl
  · fin_cases t <;> rfl

/-- Twins transported along ϱ (i = 2). -/
theorem Vega.rho2_twin {μ ν : Bool} (Y : Vega G 2 μ ν) (q : V) (a : Fin 5 ⊕ Fin 8)
    (h : Y.Twin q (rhoP (e5 a))) : Y.rho2.Twin q (e5 a) := by
  intro s hs
  obtain ⟨b, rfl⟩ := e5_surj ν μ s hs
  have hb : pres 2 μ ν (rhoP (e5 b)) := by
    rw [pres_iff_B, ← rhoP_pres]; exact (pres_iff_B _ _ _ _).mp hs
  rw [Y.rho2_emb b, h _ hb, vadj_iff_B, vadj_iff_B, rhoP_inv]

/-- Twin property for one edge. -/
def Vega.TwinE {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (p s : ℕ ⊕ Fin 8) : Prop :=
  ∀ p' s' : V, Y.Twin p' p → Y.Twin s' s → G.Adj p' s'

theorem Vega.TwinE.symm' {i : ℕ} {μ ν : Bool} {Y : Vega G i μ ν} {p s : ℕ ⊕ Fin 8}
    (h : Y.TwinE p s) : Y.TwinE s p := fun p' s' hp hs => (h s' p' hs hp).symm

/-- Outer/Andrásfai permutations as maps on ℕ ⊕ Fin 8. -/
def piS : ℕ ⊕ Fin 8 → ℕ ⊕ Fin 8
  | Sum.inl j => Sum.inl j
  | Sum.inr t => Sum.inr (permS t)

def pi0 (i : ℕ) : ℕ ⊕ Fin 8 → ℕ ⊕ Fin 8
  | Sum.inl j => Sum.inl (rho0 i j)
  | Sum.inr t => Sum.inr (perm0 t)

def pi1 (i : ℕ) : ℕ ⊕ Fin 8 → ℕ ⊕ Fin 8
  | Sum.inl j => Sum.inl (rho1 i j)
  | Sum.inr t => Sum.inr (perm1 t)

theorem Vega.sigmaE {i : ℕ} {ν : Bool} (Y : Vega G i false ν) (p s : ℕ ⊕ Fin 8)
    (h : Y.sigma.TwinE (piS p) (piS s)) : Y.TwinE p s := by
  intro p' s' hp hs
  have key : ∀ (r : ℕ ⊕ Fin 8) (q : V), Y.Twin q r → Y.sigma.Twin q (piS r) := by
    intro r q hq
    apply Y.sigma_twin
    rcases r with j | t
    · exact hq
    · simp only [piS]; rw [permS_permS]; exact hq
  exact h p' s' (key p p' hp) (key s s' hs)

theorem Vega.tau0E {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (p s : ℕ ⊕ Fin 8)
    (hp : pres i μ false p) (hs : pres i μ false s)
    (h : Y.tau0.TwinE (pi0 i p) (pi0 i s)) : Y.TwinE p s := by
  have hi := Y.hi
  intro p' s' hp' hs'
  have key : ∀ (r : ℕ ⊕ Fin 8), pres i μ false r → ∀ q : V, Y.Twin q r →
      Y.tau0.Twin q (pi0 i r) := by
    intro r hr q hq
    rcases r with j | t
    · exact Y.tau0_twin q (rho0 i j) (by have := hr.1; unfold rho0; split_ifs <;> omega)
        (by rw [rho0_rho0 hi j hr.1]; exact hq)
    · exact Y.tau0_twin_out q (perm0 t) (by rw [perm0_perm0]; exact hq)
  exact h p' s' (key p hp p' hp') (key s hs s' hs')

theorem Vega.tau1E {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (p s : ℕ ⊕ Fin 8)
    (hp : pres i μ true p) (hs : pres i μ true s)
    (h : Y.tau1.TwinE (pi1 i p) (pi1 i s)) : Y.TwinE p s := by
  have hi := Y.hi
  intro p' s' hp' hs'
  have key : ∀ (r : ℕ ⊕ Fin 8), pres i μ true r → ∀ q : V, Y.Twin q r →
      Y.tau1.Twin q (pi1 i r) := by
    intro r hr q hq
    rcases r with j | t
    · have h1 := hr.1
      have h2 := hr.2 rfl
      exact Y.tau1_twin q (rho1 i j) (by unfold rho1; split_ifs <;> omega)
        (by unfold rho1; split_ifs <;> omega)
        (by have e : rho1 i (rho1 i j) = j := by unfold rho1; split_ifs <;> omega
            rw [e]; exact hq)
    · exact Y.tau1_twin_out q (perm1 t) (by rw [perm1_perm1]; exact hq)
  exact h p' s' (key p hp p' hp') (key s hs s' hs')

theorem Vega.rhoE {μ ν : Bool} (Y : Vega G 2 μ ν) (a b : Fin 5 ⊕ Fin 8)
    (h : Y.rho2.TwinE (rhoP (e5 a)) (rhoP (e5 b))) : Y.TwinE (e5 a) (e5 b) := by
  intro p' s' hp hs
  have key : ∀ (c : Fin 5 ⊕ Fin 8) (q : V), Y.Twin q (e5 c) → Y.rho2.Twin q (rhoP (e5 c)) := by
    intro c q hq
    obtain ⟨d, hd⟩ : ∃ d, e5 d = rhoP (e5 c) := by
      rcases c with j | t
      · fin_cases j
        · exact ⟨Sum.inr 6, rfl⟩
        · exact ⟨Sum.inr 5, rfl⟩
        · exact ⟨Sum.inr 2, rfl⟩
        · exact ⟨Sum.inr 7, rfl⟩
        · exact ⟨Sum.inl 4, rfl⟩
      · fin_cases t
        · exact ⟨Sum.inr 0, rfl⟩
        · exact ⟨Sum.inr 1, rfl⟩
        · exact ⟨Sum.inl 2, rfl⟩
        · exact ⟨Sum.inr 4, rfl⟩
        · exact ⟨Sum.inr 3, rfl⟩
        · exact ⟨Sum.inl 1, rfl⟩
        · exact ⟨Sum.inl 0, rfl⟩
        · exact ⟨Sum.inl 3, rfl⟩
    rw [← hd]
    apply Y.rho2_twin
    rw [hd, rhoP_rhoP]; exact hq
  exact h p' s' (key a p' hp) (key b s' hs)

/-- LPR Lemma 4.28 (twin lemma) for maximal copies — remaining hypothesis. -/
def TwinClaim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) → NoCube G → GrFacts G →
    ∀ (i : ℕ) (μ ν : Bool) (Y : Vega G i μ ν), VegaMax G i μ ν → Y.TwinProp

/-- LPR Lemma 4.29 (attachment, twin form) given the twin lemma — remaining hypothesis. -/
def AttachTwinClaim : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) → NoCube G → GrFacts G →
    (∀ (i : ℕ) (μ ν : Bool) (Y : Vega G i μ ν), VegaMax G i μ ν → Y.TwinProp) →
    ∀ (i : ℕ) (μ ν : Bool) (Y : Vega G i μ ν), VegaMax G i μ ν → ∀ q : V,
      ∃ p, pres i μ ν p ∧ Y.Twin q p

/-- The twin lemma for i = 2 — the remaining part of TwinClaim. -/
def TwinClaim2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    G.CliqueFree 3 → (∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w) →
    (∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard) → NoCube G → GrFacts G →
    ∀ (μ ν : Bool) (Y : Vega G 2 μ ν), VegaMax G 2 μ ν → Y.TwinProp

theorem twinClaim_of_2 (h2 : TwinClaim2) : TwinClaim := by
  intro V _ _ G _ hcf hmax hmin hNC hGF i μ ν Y hM
  by_cases hi3 : 3 ≤ i
  · exact Y.twinProp_ge3 hGF hcf hNC hmin hM hi3
  · have hi := Y.hi
    have e : i = 2 := by omega
    subst e
    exact h2 V G hcf hmax hmin hNC hGF μ ν Y hM

theorem attachClaim_of (hT : TwinClaim) (hA : AttachTwinClaim) : AttachClaim := by
  intro V _ _ G _ hcf hmax hmin hNC hGF i μ ν Y hM q
  obtain ⟨p, hp, htw⟩ :=
    hA V G hcf hmax hmin hNC hGF (hT V G hcf hmax hmin hNC hGF) i μ ν Y hM q
  exact ⟨p, hp, fun s hs h => (htw s hs).mpr h⟩

/-! ## Bridges to the subgoals H1, H2 of reduction PR #21105 (therationalpie)
The definitions `PR_H1`, `PR_H2` are copied verbatim from
reductions/Erdos128.erdos_128.R2.H2.R2.H1.R1.lean (PR #21105). -/

def PR_H1 : Prop :=
  let va : ∀ i : ℕ, Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i a b =>
    match a, b with
    | Sum.inl p, Sum.inl q =>
      i ≤ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ∧ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ≤ 2 * i - 1
    | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
      ((t.1 = 0 ∨ t.1 = 3) ∧ p.1 < i) ∨ ((t.1 = 4 ∨ t.1 = 1) ∧ i ≤ p.1 ∧ p.1 < 2 * i) ∨ ((t.1 = 2 ∨ t.1 = 5) ∧ 2 * i ≤ p.1)
    | Sum.inr a, Sum.inr b =>
      (a.1 < 6 ∧ b.1 < 6 ∧ ((a.1 + 1) % 6 = b.1 ∨ (b.1 + 1) % 6 = a.1)) ∨
      (a.1 = 6 ∧ (b.1 = 0 ∨ b.1 = 4 ∨ b.1 = 2 ∨ b.1 = 7)) ∨ (b.1 = 6 ∧ (a.1 = 0 ∨ a.1 = 4 ∨ a.1 = 2 ∨ a.1 = 7)) ∨
      (a.1 = 7 ∧ (b.1 = 3 ∨ b.1 = 1 ∨ b.1 = 5 ∨ b.1 = 6)) ∨ (b.1 = 7 ∧ (a.1 = 3 ∨ a.1 = 1 ∨ a.1 = 5 ∨ a.1 = 6))
  let act : ∀ i : ℕ, Bool → Bool → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i μ ν x =>
    match x with | Sum.inl p => ν = true → p.1 ≠ 2 * i - 1 | Sum.inr t => μ = true → t.1 ≠ 7
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    (∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w) →
    (∀ v, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    ∀ (i : ℕ) (μ ν : Bool) (f : Fin (3 * i - 1) ⊕ Fin 8 → V), 2 ≤ i →
    (∀ p q, act i μ ν p → act i μ ν q → va i p q → G.Adj (f p) (f q)) →
    (∀ i' μ' ν' (f' : Fin (3 * i' - 1) ⊕ Fin 8 → V), 2 ≤ i' → (∀ p q, act i' μ' ν' p → act i' μ' ν' q → va i' p q → G.Adj (f' p) (f' q)) →
      3 * i' + 7 - μ'.toNat - ν'.toNat ≤ 3 * i + 7 - μ.toNat - ν.toNat) →
    ∀ p q u v, act i μ ν p → act i μ ν q → va i p q →
      (∀ r, act i μ ν r → va i p r → G.Adj u (f r)) →
      (∀ r, act i μ ν r → va i q r → G.Adj v (f r)) → G.Adj u v

def PR_H2 : Prop :=
  let va : ∀ i : ℕ, Fin (3 * i - 1) ⊕ Fin 8 → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i a b =>
    match a, b with
    | Sum.inl p, Sum.inl q =>
      i ≤ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ∧ (q.1 + (3 * i - 1) - p.1) % (3 * i - 1) ≤ 2 * i - 1
    | Sum.inl p, Sum.inr t | Sum.inr t, Sum.inl p =>
      ((t.1 = 0 ∨ t.1 = 3) ∧ p.1 < i) ∨ ((t.1 = 4 ∨ t.1 = 1) ∧ i ≤ p.1 ∧ p.1 < 2 * i) ∨ ((t.1 = 2 ∨ t.1 = 5) ∧ 2 * i ≤ p.1)
    | Sum.inr a, Sum.inr b =>
      (a.1 < 6 ∧ b.1 < 6 ∧ ((a.1 + 1) % 6 = b.1 ∨ (b.1 + 1) % 6 = a.1)) ∨
      (a.1 = 6 ∧ (b.1 = 0 ∨ b.1 = 4 ∨ b.1 = 2 ∨ b.1 = 7)) ∨ (b.1 = 6 ∧ (a.1 = 0 ∨ a.1 = 4 ∨ a.1 = 2 ∨ a.1 = 7)) ∨
      (a.1 = 7 ∧ (b.1 = 3 ∨ b.1 = 1 ∨ b.1 = 5 ∨ b.1 = 6)) ∨ (b.1 = 7 ∧ (a.1 = 3 ∨ a.1 = 1 ∨ a.1 = 5 ∨ a.1 = 6))
  let act : ∀ i : ℕ, Bool → Bool → Fin (3 * i - 1) ⊕ Fin 8 → Prop := fun i μ ν x =>
    match x with | Sum.inl p => ν = true → p.1 ≠ 2 * i - 1 | Sum.inr t => μ = true → t.1 ≠ 7
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.CliqueFree 3 →
    (∀ u v, u ≠ v → ¬ G.Adj u v → ∃ w, G.Adj u w ∧ G.Adj v w) →
    (∀ v, Fintype.card V < 3 * (G.neighborSet v).ncard) →
    ∀ (i : ℕ) (μ ν : Bool) (f : Fin (3 * i - 1) ⊕ Fin 8 → V), 2 ≤ i →
    (∀ p q, act i μ ν p → act i μ ν q → va i p q → G.Adj (f p) (f q)) →
    (∀ i' μ' ν' (f' : Fin (3 * i' - 1) ⊕ Fin 8 → V), 2 ≤ i' → (∀ p q, act i' μ' ν' p → act i' μ' ν' q → va i' p q → G.Adj (f' p) (f' q)) →
      3 * i' + 7 - μ'.toNat - ν'.toNat ≤ 3 * i + 7 - μ.toNat - ν.toNat) →
    (∀ p q u v, act i μ ν p → act i μ ν q → va i p q →
      (∀ r, act i μ ν r → va i p r → G.Adj u (f r)) →
      (∀ r, act i μ ν r → va i q r → G.Adj v (f r)) → G.Adj u v) →
    ∀ q : V, ∃ p, act i μ ν p ∧ ∀ r, act i μ ν r → va i p r → G.Adj q (f r)

/-- Their active predicate. -/
def PRact (i : ℕ) (μ ν : Bool) : Fin (3 * i - 1) ⊕ Fin 8 → Prop
  | Sum.inl p => ν = true → p.1 ≠ 2 * i - 1
  | Sum.inr t => μ = true → t.1 ≠ 7

/-- From their vertex type to ℕ ⊕ Fin 8. -/
def fromFin (i : ℕ) : Fin (3 * i - 1) ⊕ Fin 8 → ℕ ⊕ Fin 8
  | Sum.inl p => Sum.inl p.1
  | Sum.inr t => Sum.inr t

theorem act_pres {i : ℕ} {μ ν : Bool} (x : Fin (3 * i - 1) ⊕ Fin 8) :
    PRact i μ ν x ↔ pres i μ ν (fromFin i x) := by
  rcases x with p | t
  · simp only [PRact, fromFin, pres]
    exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
  · simp only [PRact, fromFin, pres]
    have := t.2
    cases μ <;> simp <;> omega

theorem H1rel_vadj {i : ℕ} (hi : 2 ≤ i) (x y : Fin (3 * i - 1) ⊕ Fin 8) :
    H1rel i x y ↔ vadj i (fromFin i x) (fromFin i y) := by
  rcases x with p | a <;> rcases y with q | b
  · simp only [H1rel, fromFin, vadj, AA]
    have hp := p.2
    have hq := q.2
    rcases Nat.lt_or_ge q.1 p.1 with h | h
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have e : q.1 + (3 * i - 1) - p.1 = (q.1 - p.1) + (3 * i - 1) := by omega
      rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

theorem fromFin_toFin {i : ℕ} (hi : 2 ≤ i) {μ ν : Bool} (s : ℕ ⊕ Fin 8) (hs : pres i μ ν s) :
    fromFin i (toFin i hi s) = s := by
  rcases s with k | t
  · simp only [toFin, fromFin, Nat.mod_eq_of_lt hs.1]
  · rfl

theorem toFin_fromFin {i : ℕ} (hi : 2 ≤ i) (x : Fin (3 * i - 1) ⊕ Fin 8) :
    toFin i hi (fromFin i x) = x := by
  rcases x with p | t
  · simp only [toFin, fromFin, Nat.mod_eq_of_lt p.2]
  · rfl

/-- Domination of N(p) implies being a twin of p (copies of maximal triangle-free graphs). -/
theorem Vega.twin_of_dom (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (q : V) (p : ℕ ⊕ Fin 8) (hp : pres i μ ν p)
    (hdom : ∀ s, pres i μ ν s → vadj i p s → G.Adj q (Y.emb s)) : Y.Twin q p := by
  intro s hs
  refine ⟨fun h => ?_, hdom s hs⟩
  by_contra hn
  obtain ⟨r, hr, h1, h2⟩ := diam2 i Y.hi μ ν p s hp hs hn
  exact not_adj_both hcf (hdom r hr h1) h (Y.emb_adj r s hr hs h2)

/-- Build a Vega copy from their map f. -/
def vegaOfPR {V : Type} {G : SimpleGraph V} (i : ℕ) (μ ν : Bool) (hi : 2 ≤ i)
    (f : Fin (3 * i - 1) ⊕ Fin 8 → V)
    (hf : ∀ p q, PRact i μ ν p → PRact i μ ν q → H1rel i p q → G.Adj (f p) (f q)) :
    Vega G i μ ν :=
  Vega.ofEmb i μ ν hi (fun s => f (toFin i hi s)) (by
    intro p s hp hs h
    refine hf _ _ ((act_pres _).mpr ?_) ((act_pres _).mpr ?_) ((H1rel_vadj hi _ _).mpr ?_)
    · rw [fromFin_toFin hi p hp]; exact hp
    · rw [fromFin_toFin hi s hs]; exact hs
    · rw [fromFin_toFin hi p hp, fromFin_toFin hi s hs]; exact h)

theorem vsize_eq (i : ℕ) (μ ν : Bool) :
    vsize i μ ν = 3 * i + 7 - μ.toNat - ν.toNat := by
  unfold vsize; cases μ <;> cases ν <;> rfl

/-- Their maximality implies ours. -/
theorem vegaMax_of_PR {V : Type} {G : SimpleGraph V} (i : ℕ) (μ ν : Bool)
    (hM : ∀ i' μ' ν' (f' : Fin (3 * i' - 1) ⊕ Fin 8 → V), 2 ≤ i' →
      (∀ p q, PRact i' μ' ν' p → PRact i' μ' ν' q → H1rel i' p q → G.Adj (f' p) (f' q)) →
      3 * i' + 7 - μ'.toNat - ν'.toNat ≤ 3 * i + 7 - μ.toNat - ν.toNat) :
    VegaMax G i μ ν := by
  intro i' μ' ν' hlt
  refine ⟨fun Y' => ?_⟩
  have h := hM i' μ' ν' (fun x => Y'.emb (fromFin i' x)) Y'.hi (by
    intro p q hp hq h
    exact Y'.emb_adj _ _ ((act_pres p).mp hp) ((act_pres q).mp hq) ((H1rel_vadj Y'.hi p q).mp h))
  rw [vsize_eq, vsize_eq] at hlt
  omega

/-- Bridge 1: our TwinClaim (with the proved cube / Grötzsch claims) gives their H1. -/
theorem prH1_of_twinClaim (hT : TwinClaim) (hNC : NoCubeClaim) (hGF : GrFactsClaim) :
    PR_H1 := by
  intro V _ G hcf hmax hmin i μ ν f hi hf hM p q u v hp hq hpq hu hv
  classical
  have hf' : ∀ p q, PRact i μ ν p → PRact i μ ν q → H1rel i p q → G.Adj (f p) (f q) := hf
  let Y := vegaOfPR i μ ν hi f hf'
  have hY : VegaMax G i μ ν := vegaMax_of_PR i μ ν hM
  have hTP := hT V G hcf hmax hmin (hNC V G hcf hmax hmin) (hGF V G hcf hmax hmin) i μ ν Y hY
  have E : ∀ s, Y.emb s = f (toFin i hi s) := fun s => Vega.ofEmb_emb i μ ν hi _ _ s
  have dom : ∀ (x : Fin (3 * i - 1) ⊕ Fin 8) (w : V),
      (∀ r, PRact i μ ν r → H1rel i x r → G.Adj w (f r)) →
      ∀ s, pres i μ ν s → vadj i (fromFin i x) s → G.Adj w (Y.emb s) := by
    intro x w hw s hs h
    rw [E s]
    refine hw _ ((act_pres _).mpr (by rw [fromFin_toFin hi s hs]; exact hs)) ?_
    show H1rel i x (toFin i hi s)
    rw [H1rel_vadj hi, fromFin_toFin hi s hs]; exact h
  have hp' := (act_pres (μ := μ) (ν := ν) p).mp hp
  have hq' := (act_pres (μ := μ) (ν := ν) q).mp hq
  exact hTP _ _ hp' hq' ((H1rel_vadj hi p q).mp hpq) u v
    (Y.twin_of_dom hcf u _ hp' (dom p u hu)) (Y.twin_of_dom hcf v _ hq' (dom q v hv))

/-- Bridge 2: our TwinClaim and AttachTwinClaim (with the proved claims) give their H2. Their
H2 assumes the twin property only for the given copy, while the attachment argument (via
Lemma 2.3) needs it for all maximal copies; TwinClaim supplies that. -/
theorem prH2_of_claims (hT : TwinClaim) (hA : AttachTwinClaim) (hNC : NoCubeClaim)
    (hGF : GrFactsClaim) : PR_H2 := by
  intro V _ G hcf hmax hmin i μ ν f hi hf hM _ q
  classical
  have hf' : ∀ p q, PRact i μ ν p → PRact i μ ν q → H1rel i p q → G.Adj (f p) (f q) := hf
  let Y := vegaOfPR i μ ν hi f hf'
  have hY : VegaMax G i μ ν := vegaMax_of_PR i μ ν hM
  have E : ∀ s, Y.emb s = f (toFin i hi s) := fun s => Vega.ofEmb_emb i μ ν hi _ _ s
  obtain ⟨p, hp, htw⟩ := hA V G hcf hmax hmin (hNC V G hcf hmax hmin) (hGF V G hcf hmax hmin)
    (hT V G hcf hmax hmin (hNC V G hcf hmax hmin) (hGF V G hcf hmax hmin)) i μ ν Y hY q
  refine ⟨toFin i hi p, (act_pres _).mpr (by rw [fromFin_toFin hi p hp]; exact hp), ?_⟩
  intro r hr h
  have hr' := (act_pres (μ := μ) (ν := ν) r).mp hr
  have h' : vadj i p (fromFin i r) := by
    have := (H1rel_vadj hi _ _).mp h
    rwa [fromFin_toFin hi p hp] at this
  have := (htw _ hr').mpr h'
  rwa [E, toFin_fromFin hi r] at this

end Twins

section Attach
variable {V : Type} {G : SimpleGraph V}

/-- Red vertices are reached by Lemma 4.10 from v, w: if q ~ v, w and q ≁ u then q ~ every red. -/
theorem Vega.red_of_vw (F : GrFacts G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (q : V)
    (hv : G.Adj q Y.v) (hw : G.Adj q Y.w) (hu : ¬ G.Adj q Y.u) :
    ∀ j, j < i → G.Adj q (Y.g j) := by
  have hi := Y.hi
  intro j hj
  by_cases hj2 : j + 2 ≤ i
  · have hC := Y.grRed j (j + i) (j + 2 * i) (j + 1) hj (by omega) (by omega)
      (by intro _; omega) (by omega) (by omega) (by omega)
      (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
    rcases F.l410r hC 0 q hv hw with h | h
    · exact h 1
    · exact absurd h hu
  · have hC := Y.grRed (j - 1) (j + i - 1) (j + 2 * i - 1) j (by omega) (by omega) (by omega)
      (by intro _; omega) (by omega) (by omega) hj
      (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
    rcases F.l410r hC 0 q hv hw with h | h
    · exact h 4
    · exact absurd h hu

/-- LPR Claim 4.30, case v, w ∈ N(q): q is a twin of y (μ = 0) or of a. -/
theorem Vega.c430vw [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) (q : V) (hv : G.Adj q Y.v) (hw : G.Adj q Y.w) :
    (μ = false ∧ Y.Twin q (Sum.inr 7)) ∨ Y.Twin q (Sum.inr 0) := by
  have hi := Y.hi
  have hC0 := Y.grRed 0 i (2 * i) 1 (by omega) le_rfl (by omega) (by intro _; omega)
    le_rfl (by omega) (by omega) (by unfold AA; omega) (by unfold AA; omega)
    (by unfold AA; omega)
  have hx : G.Adj q Y.x := F.beaut hC0 2 q hw hv
  by_cases hu : G.Adj q Y.u
  · cases μ with
    | true =>
      exact ((hM i false ν (by unfold vsize; cases ν <;> simp <;> omega)).false
        (Y.addY q hu hv hw hx)).elim
    | false =>
      refine Or.inl ⟨rfl, Y.twin_of_dom hcf q _ (Or.inr rfl) ?_⟩
      rintro (k | t) hs h
      · exact absurd h (by simp [vadj, colAdj])
      · fin_cases t <;> simp [vadj, hexAdj] at h
        exacts [hv, hu, hw, hx]
  · refine Or.inr (Y.twin_of_dom hcf q _ (Or.inl (by decide)) ?_)
    have hred := Y.red_of_vw F q hv hw hu
    rintro (k | t) hs h
    · exact hred k (by simp [vadj, colAdj] at h; omega)
    · fin_cases t <;> simp [vadj, hexAdj] at h
      exacts [hv, hw, hx]

/-- Blue analogue: if i ≥ 3, q ~ u, v and q ≁ w then q ~ every blue vertex. -/
theorem Vega.blue_of_uv (F : GrFacts G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hi3 : 3 ≤ i)
    (q : V) (hu : G.Adj q Y.u) (hv : G.Adj q Y.v) (hw : ¬ G.Adj q Y.w) :
    ∀ j, 2 * i ≤ j → j < 3 * i - 1 → G.Adj q (Y.g j) := by
  have hi := Y.hi
  intro j hj1 hj2
  by_cases hj : j = 2 * i
  · subst hj
    have hC := Y.grBlue (2 * i) 1 (i + 1) (2 * i + 1) le_rfl (by omega) (by omega) (by omega)
      (by omega) (by intro _; omega) (by omega) (by omega)
      (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
    rcases F.l410r hC 4 q hu hv with h | h
    · exact h 0
    · exact absurd h hw
  · have hD := Y.grBlue (j - 1) (j - 2 * i) (j - i) j (by omega) (by omega) (by omega)
      (by omega) (by omega) (by intro _; omega) hj1 hj2
      (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
    rcases F.l410r hD 4 q hu hv with h | h
    · exact h 3
    · exact absurd h hw

/-- LPR Claim 4.30, case u, v ∈ N(q), w ∉ N(q), i ≥ 3: q is a twin of c. -/
theorem Vega.c430uv [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hi3 : 3 ≤ i)
    (q : V) (hu : G.Adj q Y.u) (hv : G.Adj q Y.v) (hw : ¬ G.Adj q Y.w) :
    Y.Twin q (Sum.inr 2) := by
  have hi := Y.hi
  have hC := Y.grBlue (2 * i) 1 (i + 1) (2 * i + 1) le_rfl (by omega) (by omega) (by omega)
    (by omega) (by intro _; omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have hx : G.Adj q Y.x := F.beaut hC 1 q hv hu
  have hblue := Y.blue_of_uv F hi3 q hu hv hw
  refine Y.twin_of_dom hcf q _ (Or.inl (by decide)) ?_
  rintro (k | t) hs h
  · exact hblue k (by simp [vadj, colAdj] at h; omega) hs.1
  · fin_cases t <;> simp [vadj, hexAdj] at h
    exacts [hv, hu, hx]

theorem vadj_pi0 {i : ℕ} (hi : 2 ≤ i) (p s : ℕ ⊕ Fin 8) (hp : p.elim (· < 3 * i - 1) (fun _ => True))
    (hs : s.elim (· < 3 * i - 1) (fun _ => True)) :
    vadj i (pi0 i p) (pi0 i s) ↔ vadj i p s := by
  rcases p with j | a <;> rcases s with k | b
  · show AA i (rho0 i j) (rho0 i k) ↔ AA i j k
    simp only [Sum.elim_inl] at hp hs
    unfold AA rho0; split_ifs <;> omega
  · show colAdj i (rho0 i j) (perm0 b) ↔ colAdj i j b
    simp only [Sum.elim_inl] at hp
    fin_cases b <;> simp [colAdj, perm0] <;> unfold rho0 <;> split_ifs <;> omega
  · show colAdj i (rho0 i k) (perm0 a) ↔ colAdj i k a
    simp only [Sum.elim_inl] at hs
    fin_cases a <;> simp [colAdj, perm0] <;> unfold rho0 <;> split_ifs <;> omega
  · exact hexAdj_perm0 a b

theorem Vega.tau0_emb {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (s : ℕ ⊕ Fin 8) :
    Y.tau0.emb s = Y.emb (pi0 i s) := by
  rcases s with j | t
  · rfl
  · fin_cases t <;> rfl

theorem pi0_pi0 {i : ℕ} (hi : 2 ≤ i) (s : ℕ ⊕ Fin 8) (hs : s.elim (· < 3 * i - 1) (fun _ => True)) :
    pi0 i (pi0 i s) = s := by
  rcases s with j | t
  · simp only [Sum.elim_inl] at hs
    simp only [pi0, rho0_rho0 hi j hs]
  · simp only [pi0, perm0_perm0]

theorem pi0_pres {i : ℕ} {μ : Bool} (hi : 2 ≤ i) (s : ℕ ⊕ Fin 8) (hs : pres i μ false s) :
    pres i μ false (pi0 i s) := by
  rcases s with j | t
  · exact ⟨by have := hs.1; simp only [rho0]; split_ifs <;> omega, fun h => absurd h (by decide)⟩
  · rcases hs with hs | hs
    · left; fin_cases t <;> simp [pi0, perm0] at hs ⊢
    · right; exact hs

theorem pres_lt {i : ℕ} {μ ν : Bool} (s : ℕ ⊕ Fin 8) (hs : pres i μ ν s) :
    s.elim (· < 3 * i - 1) (fun _ => True) := by
  rcases s with j | t
  · exact hs.1
  · trivial

/-- Reverse twin transport along τ0. -/
theorem Vega.tau0_twin_rev {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (q : V) (p : ℕ ⊕ Fin 8)
    (hp : pres i μ false p) (h : Y.tau0.Twin q p) : Y.Twin q (pi0 i p) := by
  have hi := Y.hi
  intro s hs
  have hs' := pi0_pres hi s hs
  have e : Y.emb s = Y.tau0.emb (pi0 i s) := by rw [Y.tau0_emb, pi0_pi0 hi s (pres_lt s hs)]
  rw [e, h _ hs', ← vadj_pi0 hi p (pi0 i s) (pres_lt p hp) (pres_lt _ hs'),
    pi0_pi0 hi s (pres_lt s hs)]

theorem vadj_pi1 {i : ℕ} (hi : 2 ≤ i) (p s : ℕ ⊕ Fin 8)
    (hp : p.elim (fun j => j < 3 * i - 1 ∧ j ≠ 2 * i - 1) (fun _ => True))
    (hs : s.elim (fun j => j < 3 * i - 1 ∧ j ≠ 2 * i - 1) (fun _ => True)) :
    vadj i (pi1 i p) (pi1 i s) ↔ vadj i p s := by
  rcases p with j | a <;> rcases s with k | b
  · show AA i (rho1 i j) (rho1 i k) ↔ AA i j k
    simp only [Sum.elim_inl] at hp hs
    unfold AA rho1; split_ifs <;> omega
  · show colAdj i (rho1 i j) (perm1 b) ↔ colAdj i j b
    simp only [Sum.elim_inl] at hp
    fin_cases b <;> simp [colAdj, perm1] <;> unfold rho1 <;> split_ifs <;> omega
  · show colAdj i (rho1 i k) (perm1 a) ↔ colAdj i k a
    simp only [Sum.elim_inl] at hs
    fin_cases a <;> simp [colAdj, perm1] <;> unfold rho1 <;> split_ifs <;> omega
  · exact hexAdj_perm1 a b

theorem Vega.tau1_emb {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (s : ℕ ⊕ Fin 8) :
    Y.tau1.emb s = Y.emb (pi1 i s) := by
  rcases s with j | t
  · rfl
  · fin_cases t <;> rfl

theorem pres_lt1 {i : ℕ} {μ : Bool} (s : ℕ ⊕ Fin 8) (hs : pres i μ true s) :
    s.elim (fun j => j < 3 * i - 1 ∧ j ≠ 2 * i - 1) (fun _ => True) := by
  rcases s with j | t
  · exact ⟨hs.1, hs.2 rfl⟩
  · trivial

theorem pi1_pi1 {i : ℕ} (hi : 2 ≤ i) (s : ℕ ⊕ Fin 8)
    (hs : s.elim (fun j => j < 3 * i - 1 ∧ j ≠ 2 * i - 1) (fun _ => True)) :
    pi1 i (pi1 i s) = s := by
  rcases s with j | t
  · simp only [Sum.elim_inl] at hs
    simp only [pi1]
    congr 1
    unfold rho1; split_ifs <;> omega
  · simp only [pi1, perm1_perm1]

theorem pi1_pres {i : ℕ} {μ : Bool} (hi : 2 ≤ i) (s : ℕ ⊕ Fin 8) (hs : pres i μ true s) :
    pres i μ true (pi1 i s) := by
  rcases s with j | t
  · have h1 := hs.1
    have h2 := hs.2 rfl
    exact ⟨by simp only [rho1]; split_ifs <;> omega, fun _ => by simp only [rho1]; split_ifs <;> omega⟩
  · rcases hs with hs | hs
    · left; fin_cases t <;> simp [pi1, perm1] at hs ⊢
    · right; exact hs

/-- Reverse twin transport along τ1. -/
theorem Vega.tau1_twin_rev {i : ℕ} {μ : Bool} (Y : Vega G i μ true) (q : V) (p : ℕ ⊕ Fin 8)
    (hp : pres i μ true p) (h : Y.tau1.Twin q p) : Y.Twin q (pi1 i p) := by
  have hi := Y.hi
  intro s hs
  have hs' := pi1_pres hi s hs
  have e : Y.emb s = Y.tau1.emb (pi1 i s) := by rw [Y.tau1_emb, pi1_pi1 hi s (pres_lt1 s hs)]
  rw [e, h _ hs', ← vadj_pi1 hi p (pi1 i s) (pres_lt1 p hp) (pres_lt1 _ hs'),
    pi1_pi1 hi s (pres_lt1 s hs)]

/-- LPR Claim 4.30, case u, w ∈ N(q), v ∉ N(q) (i ≥ 3 when ν = 1): twin of b (or y). -/
theorem Vega.c430uw [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) (h3 : ν = true → 3 ≤ i) (q : V) (hu : G.Adj q Y.u)
    (hw : G.Adj q Y.w) (hv : ¬ G.Adj q Y.v) :
    (μ = false ∧ Y.Twin q (Sum.inr 7)) ∨ Y.Twin q (Sum.inr 4) := by
  have hi := Y.hi
  cases ν with
  | false =>
    rcases Y.tau0.c430vw F hcf hcube hM q hu hw with ⟨hμ, h⟩ | h
    · exact Or.inl ⟨hμ, Y.tau0_twin_rev q (Sum.inr 7) (Or.inr hμ) h⟩
    · exact Or.inr (Y.tau0_twin_rev q (Sum.inr 0) (Or.inl (by decide)) h)
  | true =>
    exact Or.inr (Y.tau1_twin_rev q (Sum.inr 2) (Or.inl (by decide))
      (Y.tau1.c430uv F hcf (h3 rfl) q hu hw hv))

theorem Vega.sigma_emb {i : ℕ} {ν : Bool} (Y : Vega G i false ν) (s : ℕ ⊕ Fin 8) :
    Y.sigma.emb s = Y.emb (piS s) := by
  rcases s with j | t
  · rfl
  · fin_cases t <;> rfl

theorem piS_piS (s : ℕ ⊕ Fin 8) : piS (piS s) = s := by
  rcases s with j | t
  · rfl
  · simp only [piS, permS_permS]

theorem vadj_piS {i : ℕ} (p s : ℕ ⊕ Fin 8) : vadj i (piS p) (piS s) ↔ vadj i p s := by
  rcases p with j | a <;> rcases s with k | b
  · exact Iff.rfl
  · show colAdj i j (permS b) ↔ colAdj i j b
    fin_cases b <;> simp [colAdj, permS]
  · show colAdj i k (permS a) ↔ colAdj i k a
    fin_cases a <;> simp [colAdj, permS]
  · exact hexAdj_permS' a b

theorem piS_pres {i : ℕ} {ν : Bool} (s : ℕ ⊕ Fin 8) (hs : pres i false ν s) :
    pres i false ν (piS s) := by
  rcases s with j | t
  · exact hs
  · exact Or.inr rfl

/-- Reverse twin transport along σ. -/
theorem Vega.sigma_twin_rev {i : ℕ} {ν : Bool} (Y : Vega G i false ν) (q : V)
    (p : ℕ ⊕ Fin 8) (h : Y.sigma.Twin q p) : Y.Twin q (piS p) := by
  intro s hs
  have e : Y.emb s = Y.sigma.emb (piS s) := by rw [Y.sigma_emb, piS_piS]
  rw [e, h _ (piS_pres s hs)]
  have := vadj_piS (i := i) p (piS s)
  rw [piS_piS] at this
  exact this.symm

/-- LPR Claim 4.30 (i ≥ 3): a vertex adjacent to two of u, v, w is a twin of a, b, c or y. -/
theorem Vega.c430 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) (hi3 : 3 ≤ i) (q : V)
    (h2 : (G.Adj q Y.u ∧ G.Adj q Y.v) ∨ (G.Adj q Y.v ∧ G.Adj q Y.w) ∨
      (G.Adj q Y.u ∧ G.Adj q Y.w)) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2 ∨ (μ = false ∧ p = Sum.inr 7)) ∧
      Y.Twin q p := by
  by_cases hvw : G.Adj q Y.v ∧ G.Adj q Y.w
  · rcases Y.c430vw F hcf hcube hM q hvw.1 hvw.2 with ⟨hμ, h⟩ | h
    · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨hμ, rfl⟩)), h⟩
    · exact ⟨_, Or.inl rfl, h⟩
  rcases h2 with ⟨hu, hv⟩ | h | ⟨hu, hw⟩
  · have hw : ¬ G.Adj q Y.w := fun hw => hvw ⟨hv, hw⟩
    exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), Y.c430uv F hcf hi3 q hu hv hw⟩
  · exact absurd h hvw
  · have hv : ¬ G.Adj q Y.v := fun hv => hvw ⟨hv, hw⟩
    rcases Y.c430uw F hcf hcube hM (fun _ => hi3) q hu hw hv with ⟨hμ, h⟩ | h
    · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨hμ, rfl⟩)), h⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h⟩


/-- Small-neighbourhood contradiction in a maximal copy: no vertex is adjacent to x and to two
Andrásfai vertices of different colours. -/
theorem Vega.noSmall2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (t : V)
    (hx : G.Adj t Y.x) (j k : ℕ) (hj : pres i μ ν (Sum.inl j)) (hk : pres i μ ν (Sum.inl k))
    (htj : G.Adj t (Y.g j)) (htk : G.Adj t (Y.g k))
    (hcol : ¬ ((j < i ↔ k < i) ∧ (j < 2 * i ↔ k < 2 * i))) : False :=
  Y.noSmallX F hcf hcube hmin hM t hx j k hj hk htj htk (fun h1 h2 => hcol ⟨h1, h2⟩)

/-- Lemma 4.11 at any index. -/
theorem GrFacts.l411r (F : GrFacts G) {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (k : Fin 5) (q : V) (h0 : G.Adj q (u k)) (h3 : G.Adj q (v (k + 3)))
    (hn : ¬ G.Adj q (u (k + 3))) :
    G.Adj q (v k) ∧ ∃ t, G.Adj t (u (k + 3)) ∧ G.Adj t (u (k + 4)) ∧ G.Adj t (v (k + 1)) ∧
      G.Adj q t := by
  have c : ∀ j : Fin 5, j + k = k + j := fun j => add_comm j k
  have r := F.l411 (hY.rotV k) q (by simp only [c, add_zero]; exact h0)
    (by simp only [c]; exact h3) (by simp only [c]; exact hn)
  simp only [c, add_zero] at r
  exact r

/-- Lemma 4.12 at any index. -/
theorem GrFacts.l412r (F : GrFacts G) {v u : Fin 5 → V} {w : V} (hY : IsGr G v u w)
    (k : Fin 5) (q : V) (h0 : G.Adj q (u k)) (h3 : G.Adj q (v (k + 3))) :
    G.Adj q (u (k + 1)) ∨ G.Adj q (v k) ∨
      ∃ A2 B0 : V, G.Adj q A2 ∧ G.Adj q B0 ∧
        (G.Adj A2 (v k) ∧ G.Adj A2 (v (k + 2)) ∧ G.Adj A2 w) ∧
        (G.Adj B0 (v (k + 1)) ∧ G.Adj B0 (v (k + 4)) ∧ G.Adj B0 (u (k + 1)) ∧
          G.Adj B0 (u (k + 4))) := by
  have c : ∀ j : Fin 5, j + k = k + j := fun j => add_comm j k
  have r := F.l412 (hY.rotV k) q (by simp only [c, add_zero]; exact h0)
    (by simp only [c]; exact h3)
  simp only [c, add_zero] at r
  exact r

/-- The twin property for every maximal Vega copy with index i (any μ, ν). -/
def TwAll (G : SimpleGraph V) (i : ℕ) : Prop :=
  ∀ (μ' ν' : Bool) (Y' : Vega G i μ' ν'), VegaMax G i μ' ν' → Y'.TwinProp

theorem vegaMax_swap {i : ℕ} {μ ν : Bool} (hM : VegaMax G i μ ν) : VegaMax G i ν μ := by
  intro i' μ' ν' h
  refine hM i' μ' ν' ?_
  unfold vsize at h ⊢
  cases μ <;> cases ν <;> simp at h ⊢ <;> omega

/-- Twins transported back along ϱ (i = 2). -/
theorem Vega.rho2_twin_rev {μ ν : Bool} (Y : Vega G 2 μ ν) (q : V) (a : Fin 5 ⊕ Fin 8)
    (h : Y.rho2.Twin q (e5 a)) : Y.Twin q (rhoP (e5 a)) := by
  intro s hs
  obtain ⟨b, rfl⟩ := e5_surj μ ν s hs
  have hb' : pres 2 ν μ (rhoP (e5 b)) := by
    rw [pres_iff_B, ← rhoP_pres]; exact (pres_iff_B _ _ _ _).mp hs
  obtain ⟨c, hc⟩ := e5_surj ν μ _ hb'
  have e : Y.emb (e5 b) = Y.rho2.emb (e5 c) := by rw [Y.rho2_emb c, hc, rhoP_rhoP]
  have hc' : pres 2 ν μ (e5 c) := by rw [hc]; exact hb'
  rw [e, h (e5 c) hc', vadj_iff_B, vadj_iff_B]
  have := rhoP_inv a c
  rw [hc, rhoP_rhoP] at this
  rw [this, hc]

/-- Hexagon form of 𝒟₂ (via `prop_D` with m = 2): for a closed walk h0 h1 h2 h3 h4 h5 some
vertex is adjacent to h0, h2, h4 or to h1, h3, h5. -/
theorem hexD [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hcf : G.CliqueFree 3)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (h0 h1 h2 h3 h4 h5 : V) (e01 : G.Adj h0 h1) (e12 : G.Adj h1 h2) (e23 : G.Adj h2 h3)
    (e34 : G.Adj h3 h4) (e45 : G.Adj h4 h5) (e50 : G.Adj h5 h0) :
    ∃ t, (G.Adj t h0 ∧ G.Adj t h2 ∧ G.Adj t h4) ∨ (G.Adj t h1 ∧ G.Adj t h3 ∧ G.Adj t h5) := by
  let xs6 : Fin 6 → V := fun i => match i.val with
    | 0 => h0 | 1 => h2 | 2 => h4 | 3 => h3 | 4 => h5 | _ => h1
  obtain ⟨x, hx⟩ := prop_D G hmin 2 (by omega) xs6
  rw [card_filter_fin6] at hx
  have hcls := c6_indep_ge_three
    (decide (G.Adj h0 x)) (decide (G.Adj h2 x)) (decide (G.Adj h4 x))
    (decide (G.Adj h3 x)) (decide (G.Adj h5 x)) (decide (G.Adj h1 x))
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e50.symm)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e01)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e23)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e12.symm)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e34.symm)
    (not_and_decide fun ha hb => not_adj_both hcf ha.symm hb.symm e45)
    hx
  rcases hcls with ⟨a1, a2, a3⟩ | ⟨b1, b2, b3⟩
  · exact ⟨x, Or.inl ⟨(of_decide_eq_true a1).symm, (of_decide_eq_true a2).symm,
      (of_decide_eq_true a3).symm⟩⟩
  · exact ⟨x, Or.inr ⟨(of_decide_eq_true b3).symm, (of_decide_eq_true b1).symm,
      (of_decide_eq_true b2).symm⟩⟩

/-- Lemma 2.3 including the replaced vertex itself. -/
theorem Vega.twin_back (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (z : ℕ ⊕ Fin 8) (hz : pres i μ ν z) (z' : V) (htw : Y.Twin z' z)
    (hT : (Y.repl z z' htw).TwinProp) (p : ℕ ⊕ Fin 8) (hp : pres i μ ν p) (q : V)
    (h : (Y.repl z z' htw).Twin q p) : Y.Twin q p := by
  by_cases hpz : p = z
  · subst hpz
    refine Y.twin_of_dom hcf q p hp ?_
    intro s hs hv
    have hsz : s ≠ p := by
      rintro rfl; exact vadj_irrefl Y.hi s hv
    have := (h s hs).mpr hv
    rwa [Y.repl_emb, Function.update_of_ne hsz] at this
  · exact Y.lemma23 hcf z hz z' htw hT p hp hpz q h

/-- `twin_back` with the replaced position inferred from the twin hypothesis. -/
theorem Vega.twin_back' (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    {z : ℕ ⊕ Fin 8} (z' : V) (htw : Y.Twin z' z) (hz : pres i μ ν z)
    (hT : (Y.repl z z' htw).TwinProp) (p : ℕ ⊕ Fin 8) (hp : pres i μ ν p) (q : V)
    (h : (Y.repl z z' htw).Twin q p) : Y.Twin q p :=
  Y.twin_back hcf z hz z' htw hT p hp q h

theorem pres_abc {i : ℕ} {μ ν : Bool} (p : ℕ ⊕ Fin 8)
    (hp : p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2) : pres i μ ν p := by
  rcases hp with rfl | rfl | rfl <;> exact Or.inl (by decide)

/-- For i = 2: a vertex adjacent to u, v, x and the blue vertex 4 is a twin of c. -/
theorem Vega.twin_c_dom2 (hcf : G.CliqueFree 3) {μ ν : Bool} (Y : Vega G 2 μ ν) (q : V)
    (hu : G.Adj q Y.u) (hv : G.Adj q Y.v) (hx : G.Adj q Y.x) (h4 : G.Adj q (Y.g 4)) :
    Y.Twin q (Sum.inr 2) := by
  refine Y.twin_of_dom hcf q _ (Or.inl (by decide)) ?_
  rintro (k | t) hs h
  · have hk := hs.1
    simp [vadj, colAdj] at h
    obtain rfl : k = 4 := by omega
    exact h4
  · fin_cases t <;> simp [vadj, hexAdj] at h <;> first | exact hu | exact hv | exact hx

/-- LPR Claim 4.30, case u, v ∈ N(q), w ∉ N(q), for i = 2 (red path 0-2-4-1, Lemmas 4.11 and
4.12, Lemma 2.3). -/
theorem Vega.c430uv2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {μ ν : Bool} (hTw : TwAll G 2) (Y : Vega G 2 μ ν) (hM : VegaMax G 2 μ ν) (q : V)
    (hu : G.Adj q Y.u) (hv : G.Adj q Y.v) (hw : ¬ G.Adj q Y.w) : Y.Twin q (Sum.inr 2) := by
  have hC0 := Y.grRed 0 2 4 1 (by omega) le_rfl (by omega) (by intro _; omega) le_rfl
    (by omega) (by omega) (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have hx : G.Adj q Y.x := by
    by_contra hnx
    obtain ⟨-, t, htx, ht1, ht2, -⟩ := F.l411r hC0.reflV 2 q hv hu hnx
    exact Y.noSmall2 F hcf hcube hmin hM t htx 1 2 ⟨by omega, fun _ => by omega⟩
      ⟨by omega, fun _ => by omega⟩ ht1 ht2 (fun h => absurd (h.1.mp (by omega)) (by omega))
  rcases F.l412r hC0.reflV 2 q hv hu with h | h | ⟨A2, B0, -, hqB, -, ⟨hB1, hB2, hB3, hB4⟩⟩
  · exact absurd h hw
  · exact Y.twin_c_dom2 hcf q hu hv hx h
  · have hB : Y.Twin B0 (Sum.inl 4) := by
      refine Y.twin_of_dom hcf B0 _ ⟨by omega, fun _ => by omega⟩ ?_
      rintro (k | t) hs h
      · have hk := hs.1
        simp only [vadj, AA] at h
        rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
        · exact hB4
        · exact hB1
      · simp only [vadj, colAdj] at h
        fin_cases t <;> simp at h <;> first | exact hB2 | exact hB3 | omega
    have h1 : (Y.repl (Sum.inl 4) B0 hB).Twin q (Sum.inr 2) := by
      refine (Y.repl (Sum.inl 4) B0 hB).twin_c_dom2 hcf q ?_ ?_ ?_ ?_
      · show G.Adj q (Function.update Y.emb (Sum.inl 4) B0 (Sum.inr 3))
        rw [Function.update_of_ne (by simp)]; exact hu
      · show G.Adj q (Function.update Y.emb (Sum.inl 4) B0 (Sum.inr 1))
        rw [Function.update_of_ne (by simp)]; exact hv
      · show G.Adj q (Function.update Y.emb (Sum.inl 4) B0 (Sum.inr 6))
        rw [Function.update_of_ne (by simp)]; exact hx
      · show G.Adj q (Function.update Y.emb (Sum.inl 4) B0 (Sum.inl 4))
        rw [Function.update_self]; exact hqB
    exact Y.twin_back' hcf B0 hB ⟨by omega, fun _ => by omega⟩ (hTw _ _ _ hM) (Sum.inr 2)
      (Or.inl (by decide)) q h1

/-- LPR Claim 4.30 for all i ≥ 2. -/
theorem Vega.c430A [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i) (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (h2 : (G.Adj q Y.u ∧ G.Adj q Y.v) ∨ (G.Adj q Y.v ∧ G.Adj q Y.w) ∨
      (G.Adj q Y.u ∧ G.Adj q Y.w)) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2 ∨ (μ = false ∧ p = Sum.inr 7)) ∧
      Y.Twin q p := by
  have hi := Y.hi
  rcases Nat.lt_or_ge i 3 with hi2 | hi3
  · obtain rfl : i = 2 := by omega
    by_cases hvw : G.Adj q Y.v ∧ G.Adj q Y.w
    · rcases Y.c430vw F hcf hcube hM q hvw.1 hvw.2 with ⟨hμ, h⟩ | h
      · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨hμ, rfl⟩)), h⟩
      · exact ⟨_, Or.inl rfl, h⟩
    rcases h2 with ⟨hu, hv⟩ | h | ⟨hu, hw⟩
    · have hw : ¬ G.Adj q Y.w := fun hw => hvw ⟨hv, hw⟩
      exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), Y.c430uv2 F hcf hcube hmin hTw hM q hu hv hw⟩
    · exact absurd h hvw
    · have hv : ¬ G.Adj q Y.v := fun hv => hvw ⟨hv, hw⟩
      cases ν with
      | false =>
        rcases Y.c430uw F hcf hcube hM (fun h => absurd h (by decide)) q hu hw hv with
          ⟨hμ, h⟩ | h
        · exact ⟨_, Or.inr (Or.inr (Or.inr ⟨hμ, rfl⟩)), h⟩
        · exact ⟨_, Or.inr (Or.inl rfl), h⟩
      | true =>
        exact ⟨_, Or.inr (Or.inl rfl), Y.tau1_twin_rev q (Sum.inr 2) (Or.inl (by decide))
          (Y.tau1.c430uv2 F hcf hcube hmin hTw hM q hu hw hv)⟩
  · exact Y.c430 F hcf hcube hM hi3 q h2

/-- LPR Claim 4.31 (i ≥ 3, μ = 0): a vertex adjacent to two of a, b, c is a twin of u, v, w or x. -/
theorem Vega.c431 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {ν : Bool} (hTw : TwAll G i) (Y : Vega G i false ν)
    (hM : VegaMax G i false ν) (hi3 : 2 ≤ i) (q : V)
    (h2 : (G.Adj q Y.a ∧ G.Adj q Y.b) ∨ (G.Adj q Y.b ∧ G.Adj q Y.c) ∨
      (G.Adj q Y.a ∧ G.Adj q Y.c)) :
    ∃ p, (p = Sum.inr 3 ∨ p = Sum.inr 1 ∨ p = Sum.inr 5 ∨ p = Sum.inr 6) ∧ Y.Twin q p := by
  obtain ⟨p, hp, h⟩ := Y.sigma.c430A F hcf hcube hmin hTw hM q h2
  refine ⟨piS p, ?_, Y.sigma_twin_rev q p h⟩
  rcases hp with rfl | rfl | rfl | ⟨-, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

/-- Claim 4.32 core, red colour: q ~ b, c cannot see exactly one of two consecutive reds. -/
theorem Vega.c432red [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (hb : G.Adj q Y.b) (hc : G.Adj q Y.c) (j : ℕ) (hj : j + 1 < i)
    (hxor : (G.Adj q (Y.g j) ∧ ¬ G.Adj q (Y.g (j + 1))) ∨
      (¬ G.Adj q (Y.g j) ∧ G.Adj q (Y.g (j + 1)))) : False := by
  have hi := Y.hi
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grRed j (j + i) (j + 2 * i) (j + 1) (by omega) (by omega) (by omega)
    (by intro _; omega) (by omega) (by omega) hj
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨-, t, ht4, ht0, htv, -⟩ := F.l411r hC 1 q h1 hc h2
    exact Y.noSmall2 F hcf hcube hmin hM t ht0 (j + 1) (j + i)
      (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega)) ht4 htv
      (fun h => by have := h.1.mp (by omega); omega)
  · obtain ⟨-, t, ht4, ht0, htv, -⟩ := F.l411r hC.reflV 1 q h2 hb h1
    exact Y.noSmall2 F hcf hcube hmin hM t ht0 j (j + 2 * i)
      (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega)) ht4 htv
      (fun h => by have := h.2.mp (by omega); omega)

/-- Claim 4.32 core, green colour: q ~ a, c cannot see exactly one of two consecutive greens. -/
theorem Vega.c432green [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (ha : G.Adj q Y.a) (hc : G.Adj q Y.c) (j : ℕ) (hj1 : i ≤ j) (hj : j + 1 < 2 * i)
    (hjn : ν = true → j + 1 ≠ 2 * i - 1)
    (hxor : (G.Adj q (Y.g j) ∧ ¬ G.Adj q (Y.g (j + 1))) ∨
      (¬ G.Adj q (Y.g j) ∧ G.Adj q (Y.g (j + 1)))) : False := by
  have hi := Y.hi
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grGreen (j + 1) (j + 1 - i) (j + i) j (by omega) hj hjn (by omega)
    (by omega) (by omega) hj1 (by omega) (by intro _; omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨-, t, ht0, ht4, htb, -⟩ := F.l411r hC.reflV 2 q h1 ha h2
    exact Y.noSmall2 F hcf hcube hmin hM t ht4 (j + 1) (j + i)
      (Pl _ (by omega) hjn) (Pl _ (by omega) (by intro _; omega)) ht0 htb
      (fun h => by have := h.2.mp (by omega); omega)
  · obtain ⟨-, t, ht3, ht4, htr, -⟩ := F.l411r hC 0 q h2 hc h1
    exact Y.noSmall2 F hcf hcube hmin hM t ht4 j (j + 1 - i)
      (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega)) ht3 htr
      (fun h => by have := h.1.mpr (by omega); omega)

/-- Claim 4.32 core, blue colour: q ~ a, b cannot see exactly one of two consecutive blues. -/
theorem Vega.c432blue [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (ha : G.Adj q Y.a) (hb : G.Adj q Y.b) (j : ℕ) (hj1 : 2 * i ≤ j) (hj : j + 1 < 3 * i - 1)
    (hxor : (G.Adj q (Y.g j) ∧ ¬ G.Adj q (Y.g (j + 1))) ∨
      (¬ G.Adj q (Y.g j) ∧ G.Adj q (Y.g (j + 1)))) : False := by
  have hi := Y.hi
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grBlue j (j + 1 - 2 * i) (j + 1 - i) (j + 1) hj1 (by omega) (by omega)
    (by omega) (by omega) (by intro _; omega) (by omega) hj
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases hxor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨-, t, ht3, ht4, htr, -⟩ := F.l411r hC 0 q h1 hb h2
    exact Y.noSmall2 F hcf hcube hmin hM t ht4 (j + 1) (j + 1 - 2 * i)
      (Pl _ hj (by intro _; omega)) (Pl _ (by omega) (by intro _; omega)) ht3 htr
      (fun h => by have := h.1.mpr (by omega); omega)
  · obtain ⟨-, t, ht0, ht4, htg, -⟩ := F.l411r hC.reflV 2 q h2 ha h1
    exact Y.noSmall2 F hcf hcube hmin hM t ht4 j (j + 1 - i)
      (Pl _ (by omega) (by intro _; omega)) (Pl _ (by omega) (by intro _; omega)) ht0 htg
      (fun h => by have := h.2.mpr (by omega); omega)

/-- A predicate true at j and false at k (both in [lo, hi]) changes between consecutive points. -/
theorem boundary (f : ℕ → Prop) (lo hi j k : ℕ) (hj1 : lo ≤ j) (hj2 : j ≤ hi) (hk1 : lo ≤ k)
    (hk2 : k ≤ hi) (hfj : f j) (hfk : ¬ f k) :
    ∃ m, lo ≤ m ∧ m + 1 ≤ hi ∧ ((f m ∧ ¬ f (m + 1)) ∨ (¬ f m ∧ f (m + 1))) := by
  by_contra h
  have h' : ∀ m, lo ≤ m → m + 1 ≤ hi → (f m ↔ f (m + 1)) := by
    intro m h1 h2
    by_contra hc
    apply h
    refine ⟨m, h1, h2, ?_⟩
    by_cases hm : f m
    · exact Or.inl ⟨hm, fun h3 => hc ⟨fun _ => h3, fun _ => hm⟩⟩
    · exact Or.inr ⟨hm, by by_contra h3; exact hc ⟨fun h4 => absurd h4 hm, fun h4 => absurd h4 h3⟩⟩
  have key : ∀ d, lo ≤ d → d ≤ hi → (f d ↔ f lo) := by
    intro d hd
    induction d, hd using Nat.le_induction with
    | base => intro _; exact Iff.rfl
    | succ n hn ih => intro h2; exact (h' n hn h2).symm.trans (ih (by omega))
  exact hfk ((key k hk1 hk2).mpr ((key j hj1 hj2).mp hfj))

/-- LPR Claim 4.32 (i ≥ 3): a vertex adjacent to two of a, b, c and to an Andrásfai vertex is a
twin of u, v or w. -/
theorem Vega.c432 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i) (Y : Vega G i μ ν) (hM : VegaMax G i μ ν)
    (hi3 : 2 ≤ i) (q : V)
    (h2 : (G.Adj q Y.a ∧ G.Adj q Y.b) ∨ (G.Adj q Y.b ∧ G.Adj q Y.c) ∨
      (G.Adj q Y.a ∧ G.Adj q Y.c))
    (j : ℕ) (hj : pres i μ ν (Sum.inl j)) (hqj : G.Adj q (Y.g j)) :
    ∃ p, (p = Sum.inr 3 ∨ p = Sum.inr 1 ∨ p = Sum.inr 5) ∧ Y.Twin q p := by
  have hi := Y.hi
  obtain ⟨hj1, hjn⟩ := hj
  have P : ∀ t : Fin 8, t.val < 7 → pres i μ ν (Sum.inr t) := fun t ht => Or.inl ht
  -- the case μ = 0 is Claim 4.31 (a twin of x has no Andrásfai neighbour)
  have via431 : μ = false → ∃ p, (p = Sum.inr 3 ∨ p = Sum.inr 1 ∨ p = Sum.inr 5) ∧ Y.Twin q p := by
    intro hμ
    subst hμ
    obtain ⟨p, hp, h⟩ := Y.c431 F hcf hcube hmin hTw hM hi3 q h2
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨_, Or.inl rfl, h⟩
    · exact ⟨_, Or.inr (Or.inl rfl), h⟩
    · exact ⟨_, Or.inr (Or.inr rfl), h⟩
    · exact absurd ((h (Sum.inl j) ⟨hj1, hjn⟩).mp hqj) (by simp [vadj, colAdj])
  cases μ
  · exact via431 rfl
  by_cases hjr : j < i
  · -- red: q ≁ a, so q ~ b, c
    have hna : ¬ G.Adj q Y.a := fun ha => not_adj_both hcf ha hqj (Y.red j hjr).1
    have hb : G.Adj q Y.b := by tauto
    have hc : G.Adj q Y.c := by tauto
    by_cases hall : ∀ k, k < i → G.Adj q (Y.g k)
    · refine ⟨Sum.inr 3, Or.inl rfl, Y.twin_of_dom hcf q _ (P 3 (by decide)) ?_⟩
      rintro (k | t) hs h
      · exact hall k (by simp [vadj, colAdj] at h; omega)
      · fin_cases t <;> simp [vadj, hexAdj] at h
        · exact hc
        · exact hb
        · exact absurd hs (by simp [pres])
    · push_neg at hall
      obtain ⟨k, hk, hqk⟩ := hall
      obtain ⟨m, hm1, hm2, hm⟩ := boundary (fun m => G.Adj q (Y.g m)) 0 (i - 1) j k
        (by omega) (by omega) (by omega) (by omega) hqj hqk
      exact (Y.c432red F hcf hcube hmin hM q hb hc m (by omega) hm).elim
  by_cases hjg : j < 2 * i
  · have hnb : ¬ G.Adj q Y.b := fun hb =>
      not_adj_both hcf hb hqj (Y.green j (by omega) hjg hjn).1
    have ha : G.Adj q Y.a := by tauto
    have hc : G.Adj q Y.c := by tauto
    by_cases hall : ∀ k, i ≤ k → k < 2 * i → (ν = true → k ≠ 2 * i - 1) → G.Adj q (Y.g k)
    · refine ⟨Sum.inr 1, Or.inr (Or.inl rfl), Y.twin_of_dom hcf q _ (P 1 (by decide)) ?_⟩
      rintro (k | t) hs h
      · exact hall k (by simp [vadj, colAdj] at h; omega) (by simp [vadj, colAdj] at h; omega)
          hs.2
      · fin_cases t <;> simp [vadj, hexAdj] at h
        · exact ha
        · exact hc
        · exact absurd hs (by simp [pres])
    · push_neg at hall
      obtain ⟨k, hk1, hk2, hkn, hqk⟩ := hall
      have hhi : ∀ m, (ν = true → m ≠ 2 * i - 1) → m < 2 * i → m ≤ 2 * i - 1 - ν.toNat := by
        intro m hm1 hm2; cases ν <;> simp at hm1 ⊢ <;> omega
      obtain ⟨m, hm1, hm2, hm⟩ := boundary (fun m => G.Adj q (Y.g m)) i (2 * i - 1 - ν.toNat)
        j k (by omega) (hhi j hjn hjg) hk1 (hhi k hkn hk2) hqj hqk
      exact (Y.c432green F hcf hcube hmin hM q ha hc m hm1 (by cases ν <;> simp at hm2 <;> omega)
        (fun h => by cases ν <;> simp at hm2 h ⊢ <;> omega) hm).elim
  · have hnc : ¬ G.Adj q Y.c := fun hc =>
      not_adj_both hcf hc hqj (Y.blue j (by omega) hj1).1
    have ha : G.Adj q Y.a := by tauto
    have hb : G.Adj q Y.b := by tauto
    by_cases hall : ∀ k, 2 * i ≤ k → k < 3 * i - 1 → G.Adj q (Y.g k)
    · refine ⟨Sum.inr 5, Or.inr (Or.inr rfl), Y.twin_of_dom hcf q _ (P 5 (by decide)) ?_⟩
      rintro (k | t) hs h
      · exact hall k (by simp [vadj, colAdj] at h; omega) hs.1
      · fin_cases t <;> simp [vadj, hexAdj] at h
        · exact ha
        · exact hb
        · exact absurd hs (by simp [pres])
    · push_neg at hall
      obtain ⟨k, hk1, hk2, hqk⟩ := hall
      obtain ⟨m, hm1, hm2, hm⟩ := boundary (fun m => G.Adj q (Y.g m)) (2 * i) (3 * i - 2) j k
        (by omega) (by omega) hk1 (by omega) hqj hqk
      exact (Y.c432blue F hcf hcube hmin hM q ha hb m hm1 (by omega) hm).elim

/-- No vertex is adjacent to y and to two Andrásfai vertices of different colours (μ = 0),
via σ. -/
theorem Vega.noSmallY [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {ν : Bool} (Y : Vega G i false ν) (hM : VegaMax G i false ν) (t : V)
    (hy : G.Adj t Y.y) (j k : ℕ) (hj : pres i false ν (Sum.inl j))
    (hk : pres i false ν (Sum.inl k)) (htj : G.Adj t (Y.g j)) (htk : G.Adj t (Y.g k))
    (hcol : ¬ ((j < i ↔ k < i) ∧ (j < 2 * i ↔ k < 2 * i))) : False :=
  Y.sigma.noSmall2 F hcf hcube hmin hM t hy j k hj hk htj htk hcol

/-- Domination of the neighbourhood of the blue vertex j+2i-1 (1 ≤ j < i): c, w and [j, j+i-1]. -/
theorem Vega.twin_blue_of_dom (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j < i) (q : V) (hc : G.Adj q Y.c) (hw : G.Adj q Y.w)
    (hint : ∀ k, j ≤ k → k ≤ j + i - 1 → G.Adj q (Y.g k)) :
    Y.Twin q (Sum.inl (j + 2 * i - 1)) := by
  have hi := Y.hi
  refine Y.twin_of_dom hcf q _ ⟨by omega, fun _ => by omega⟩ ?_
  rintro (k | t) hs h
  · have hk := hs.1
    simp only [vadj, AA] at h
    exact hint k (by omega) (by omega)
  · simp only [vadj, colAdj] at h
    fin_cases t <;> simp at h <;> first | exact hc | exact hw | omega

/-- LPR Claim 4.33, red case (i ≥ 3): if q ~ j (red, j ≥ 1) and q ~ j+i-1, then q is a twin of
j+2i-1 (= j - i mod 3i-1). Uses the twin property of all copies (Lemma 2.3). -/
theorem Vega.c433red [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (j : ℕ) (hj1 : 1 ≤ j) (hj : j < i)
    (q : V) (hqj : G.Adj q (Y.g j)) (hqk : G.Adj q (Y.g (j + i - 1))) :
    Y.Twin q (Sum.inl (j + 2 * i - 1)) := by
  have hi := Y.hi
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grRed (j - 1) (j + i - 1) (j + 2 * i - 1) j (by omega) (by omega) (by omega)
    (by intro _; omega) (by omega) (by omega) hj
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have hpj := Pl j (by omega) (by intro _; omega)
  have hpk := Pl (j + i - 1) (by omega) (by intro _; omega)
  have hcol : ¬ ((j < i ↔ j + i - 1 < i) ∧ (j < 2 * i ↔ j + i - 1 < 2 * i)) :=
    fun h => by have := h.1.mp hj; omega
  have hnx : ¬ G.Adj q Y.x := fun hx =>
    Y.noSmall2 F hcf hcube hmin hM q hx j (j + i - 1) hpj hpk hqj hqk hcol
  have hw : G.Adj q Y.w := by
    by_contra hnw
    obtain ⟨-, t, htw, htv, htu, hqt⟩ := F.l411r hC 4 q hqj hqk hnw
    have htx := Y.l416a hcf hcube t htu htv htw
    cases μ with
    | true =>
      exact (hM i false ν (by unfold vsize; cases ν <;> simp <;> omega)).false
        (Y.addY t htu htv htw htx)
    | false =>
      have htw' : Y.Twin t (Sum.inr 7) := by
        refine Y.twin_of_dom hcf t _ (Or.inr rfl) ?_
        rintro (k | s) hs h
        · exact absurd h (by simp [vadj, colAdj])
        · fin_cases s <;> simp [vadj, hexAdj] at h
          exacts [htv, htu, htw, htx]
      refine (Y.repl (Sum.inr 7) t htw').noSmallY F hcf hcube hmin hM q
        (by show G.Adj q (Function.update Y.emb (Sum.inr 7) t (Sum.inr 7))
            rw [Function.update_self]; exact hqt)
        j (j + i - 1) hpj hpk
        (by show G.Adj q (Function.update Y.emb (Sum.inr 7) t (Sum.inl j))
            rw [Function.update_of_ne (by simp)]; exact hqj)
        (by show G.Adj q (Function.update Y.emb (Sum.inr 7) t (Sum.inl (j + i - 1)))
            rw [Function.update_of_ne (by simp)]; exact hqk) hcol
  have hint : ∀ (Y' : Vega G i μ ν), G.Adj q Y'.c → G.Adj q Y'.w → G.Adj q (Y'.g j) →
      G.Adj q (Y'.g (j + i - 1)) → ∀ k, j ≤ k → k ≤ j + i - 1 → G.Adj q (Y'.g k) := by
    intro Y' hc hw' h1 h2 k hk1 hk2
    by_cases hk : k < i
    · exact Y'.l419a hcf hcube q hc hw' j h1 k hk1 hk
    · exact Y'.l419b hcf hcube q hc hw' (j + i - 1) (by omega) (by intro _; omega) h2 k
        (by omega) hk2
  rcases F.l412r hC 4 q hqj hqk with hx | hc | ⟨A2, B0, -, hqB, -, hBu, hBg, hBx, hBv⟩
  · exact absurd hx hnx
  · exact Y.twin_blue_of_dom hcf j hj1 hj q hc hw (hint Y hc hw hqj hqk)
  · -- B0 is a real twin of c (Claim 4.30), replace c by B0 and use Lemma 2.3
    obtain ⟨p, hp, hBp⟩ := Y.c430A F hcf hcube hmin hTw hM B0 (Or.inl ⟨hBu, hBv⟩)
    have hBc : Y.Twin B0 (Sum.inr 2) := by
      rcases hp with rfl | rfl | rfl | ⟨-, rfl⟩
      · exact absurd ((hBp (Sum.inr 3) (Or.inl (by decide))).mp hBu) (by simp [vadj, hexAdj])
      · exact absurd ((hBp (Sum.inr 1) (Or.inl (by decide))).mp hBv) (by simp [vadj, hexAdj])
      · exact hBp
      · exact absurd ((hBp (Sum.inl _) (Pl (j + 2 * i - 1) (by omega) (by intro _; omega))).mp hBg)
          (by simp [vadj, colAdj])
    have E : ∀ s, (Y.repl (Sum.inr 2) B0 hBc).emb s = Function.update Y.emb (Sum.inr 2) B0 s :=
      Y.repl_emb _ _ hBc
    have h1 : (Y.repl (Sum.inr 2) B0 hBc).Twin q (Sum.inl (j + 2 * i - 1)) := by
      have gq : ∀ k, (Y.repl (Sum.inr 2) B0 hBc).g k = Y.g k := fun k => by
        show Function.update Y.emb (Sum.inr 2) B0 (Sum.inl k) = Y.g k
        rw [Function.update_of_ne (by simp)]; rfl
      have hc' : G.Adj q (Y.repl (Sum.inr 2) B0 hBc).c := by
        show G.Adj q (Function.update Y.emb (Sum.inr 2) B0 (Sum.inr 2))
        rw [Function.update_self]; exact hqB
      have hw' : G.Adj q (Y.repl (Sum.inr 2) B0 hBc).w := by
        show G.Adj q (Function.update Y.emb (Sum.inr 2) B0 (Sum.inr 5))
        rw [Function.update_of_ne (by decide)]; exact hw
      exact (Y.repl (Sum.inr 2) B0 hBc).twin_blue_of_dom hcf j hj1 hj q hc' hw'
        (hint _ hc' hw' (by rw [gq]; exact hqj) (by rw [gq]; exact hqk))
    exact Y.lemma23 hcf (Sum.inr 2) (Or.inl (by decide)) B0 hBc (hTw _ _ _ hM) _
      (show pres i μ ν (Sum.inl (j + 2 * i - 1)) from ⟨by omega, fun _ => by omega⟩)
      (by simp) q h1

/-- Domination of the neighbourhood of the red vertex j-i (i < j < 2i): a, u and [j, j+i-1]. -/
theorem Vega.twin_red_of_dom (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν)
    (j : ℕ) (hj1 : i ≤ j) (hj : j < 2 * i) (q : V) (ha : G.Adj q Y.a) (hu : G.Adj q Y.u)
    (hint : ∀ k, j ≤ k → k ≤ j + i - 1 → (ν = true → k ≠ 2 * i - 1) → G.Adj q (Y.g k)) :
    Y.Twin q (Sum.inl (j - i)) := by
  have hi := Y.hi
  refine Y.twin_of_dom hcf q _ ⟨by omega, fun _ => by omega⟩ ?_
  rintro (k | t) hs h
  · have hk := hs.1
    simp only [vadj, AA] at h
    exact hint k (by omega) (by omega) hs.2
  · simp only [vadj, colAdj] at h
    fin_cases t <;> simp at h <;> first | exact ha | exact hu | omega

/-- LPR Claim 4.33, green case (i ≥ 3): if q ~ j (green, j ≥ i+1) and q ~ j+i-1 (blue), then q is
a twin of the red vertex j-i. -/
theorem Vega.c433green [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (j : ℕ) (hj1 : i + 1 ≤ j)
    (hj : j < 2 * i) (hjn : ν = true → j ≠ 2 * i - 1)
    (q : V) (hqj : G.Adj q (Y.g j)) (hqk : G.Adj q (Y.g (j + i - 1))) :
    Y.Twin q (Sum.inl (j - i)) := by
  have hi := Y.hi
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have hC := Y.grGreen j (j - i) (j + i - 1) (j - 1) (by omega) hj hjn (by omega)
    (by omega) (by omega) (by omega) (by omega) (by intro _; omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have hpj := Pl j (by omega) hjn
  have hpk := Pl (j + i - 1) (by omega) (by intro _; omega)
  have hcol : ¬ ((j < i ↔ j + i - 1 < i) ∧ (j < 2 * i ↔ j + i - 1 < 2 * i)) :=
    fun h => by have := h.2.mp hj; omega
  have hnx : ¬ G.Adj q Y.x := fun hx =>
    Y.noSmall2 F hcf hcube hmin hM q hx j (j + i - 1) hpj hpk hqj hqk hcol
  have hu : G.Adj q Y.u := by
    by_contra hnu
    obtain ⟨-, t, htu, htw, htv, hqt⟩ := F.l411r hC.reflV 0 q hqj hqk hnu
    have htx := Y.l416a hcf hcube t htu htv htw
    cases μ with
    | true =>
      exact (hM i false ν (by unfold vsize; cases ν <;> simp <;> omega)).false
        (Y.addY t htu htv htw htx)
    | false =>
      have htw' : Y.Twin t (Sum.inr 7) := by
        refine Y.twin_of_dom hcf t _ (Or.inr rfl) ?_
        rintro (k | s) hs h
        · exact absurd h (by simp [vadj, colAdj])
        · fin_cases s <;> simp [vadj, hexAdj] at h
          exacts [htv, htu, htw, htx]
      refine (Y.repl (Sum.inr 7) t htw').noSmallY F hcf hcube hmin hM q
        (by show G.Adj q (Function.update Y.emb (Sum.inr 7) t (Sum.inr 7))
            rw [Function.update_self]; exact hqt)
        j (j + i - 1) hpj hpk
        (by show G.Adj q (Function.update Y.emb (Sum.inr 7) t (Sum.inl j))
            rw [Function.update_of_ne (by simp)]; exact hqj)
        (by show G.Adj q (Function.update Y.emb (Sum.inr 7) t (Sum.inl (j + i - 1)))
            rw [Function.update_of_ne (by simp)]; exact hqk) hcol
  have hint : ∀ (Y' : Vega G i μ ν), G.Adj q Y'.a → G.Adj q Y'.u → G.Adj q (Y'.g j) →
      G.Adj q (Y'.g (j + i - 1)) →
      ∀ k, j ≤ k → k ≤ j + i - 1 → (ν = true → k ≠ 2 * i - 1) → G.Adj q (Y'.g k) := by
    intro Y' ha hu' h1 h2 k hk1 hk2 hkn
    by_cases hk : k < 2 * i
    · exact Y'.l420a hcf hcube q ha hu' j (by omega) h1 k hk1 hk hkn
    · exact Y'.l420b hcf hcube q ha hu' (j + i - 1) (by omega) h2 k (by omega) hk2
  rcases F.l412r hC.reflV 0 q hqj hqk with hx | ha | ⟨A2, B0, -, hqB, -, hBv, hBr, hBx, hBw⟩
  · exact absurd hx hnx
  · exact Y.twin_red_of_dom hcf j (by omega) hj q ha hu (hint Y ha hu hqj hqk)
  · obtain ⟨p, hp, hBp⟩ := Y.c430A F hcf hcube hmin hTw hM B0 (Or.inr (Or.inl ⟨hBv, hBw⟩))
    have hBa : Y.Twin B0 (Sum.inr 0) := by
      rcases hp with rfl | rfl | rfl | ⟨-, rfl⟩
      · exact hBp
      · exact absurd ((hBp (Sum.inr 1) (Or.inl (by decide))).mp hBv) (by simp [vadj, hexAdj])
      · exact absurd ((hBp (Sum.inr 5) (Or.inl (by decide))).mp hBw) (by simp [vadj, hexAdj])
      · exact absurd ((hBp (Sum.inl _) (Pl (j - i) (by omega) (by intro _; omega))).mp hBr)
          (by simp [vadj, colAdj])
    have h1 : (Y.repl (Sum.inr 0) B0 hBa).Twin q (Sum.inl (j - i)) := by
      have gq : ∀ k, (Y.repl (Sum.inr 0) B0 hBa).g k = Y.g k := fun k => by
        show Function.update Y.emb (Sum.inr 0) B0 (Sum.inl k) = Y.g k
        rw [Function.update_of_ne (by simp)]; rfl
      have ha' : G.Adj q (Y.repl (Sum.inr 0) B0 hBa).a := by
        show G.Adj q (Function.update Y.emb (Sum.inr 0) B0 (Sum.inr 0))
        rw [Function.update_self]; exact hqB
      have hu' : G.Adj q (Y.repl (Sum.inr 0) B0 hBa).u := by
        show G.Adj q (Function.update Y.emb (Sum.inr 0) B0 (Sum.inr 3))
        rw [Function.update_of_ne (by decide)]; exact hu
      exact (Y.repl (Sum.inr 0) B0 hBa).twin_red_of_dom hcf j (by omega) hj q ha' hu'
        (hint _ ha' hu' (by rw [gq]; exact hqj) (by rw [gq]; exact hqk))
    exact Y.lemma23 hcf (Sum.inr 0) (Or.inl (by decide)) B0 hBa (hTw _ _ _ hM) _
      (show pres i μ ν (Sum.inl (j - i)) from ⟨by omega, fun _ => by omega⟩)
      (by simp) q h1

/-- LPR Claim 4.33, blue case (i ≥ 3): if q ~ j (blue) and q ~ j-2i (red, = j+i-1 mod 3i-1),
then q is a twin of the green vertex j-i. Via τ0 (ν = 0, green case) or τ1 (ν = 1, red case). -/
theorem Vega.c433blue [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (j : ℕ) (hj1 : 2 * i ≤ j)
    (hj : j < 3 * i - 1)
    (q : V) (hqj : G.Adj q (Y.g j)) (hqk : G.Adj q (Y.g (j - 2 * i))) :
    Y.Twin q (Sum.inl (j - i)) := by
  have hi := Y.hi
  cases ν with
  | false =>
    have e1 : rho0 i (4 * i - 1 - j) = j - 2 * i := by
      unfold rho0; rw [if_pos (by omega)]; omega
    have e2 : rho0 i (4 * i - 1 - j + i - 1) = j := by
      unfold rho0; rw [if_neg (by omega)]; omega
    have e3 : rho0 i (4 * i - 1 - j - i) = j - i := by
      unfold rho0; rw [if_pos (by omega)]; omega
    have h := Y.tau0.c433green F hcf hcube hmin hTw hM hi3 (4 * i - 1 - j) (by omega) (by omega)
      (fun h => absurd h (by decide)) q
      (by show G.Adj q (Y.g (rho0 i _)); rw [e1]; exact hqk)
      (by show G.Adj q (Y.g (rho0 i _)); rw [e2]; exact hqj)
    have h2 := Y.tau0_twin_rev q (Sum.inl (4 * i - 1 - j - i)) ⟨by omega, fun h => absurd h (by decide)⟩ h
    simpa only [pi0, e3] using h2
  | true =>
    have e1 : rho1 i (3 * i - 1 - j) = j - 2 * i := by
      unfold rho1; rw [if_pos (by omega)]; omega
    have e2 : rho1 i (3 * i - 1 - j + i - 1) = j := by
      unfold rho1; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : rho1 i (3 * i - 1 - j + 2 * i - 1) = j - i := by
      unfold rho1; rw [if_neg (by omega), if_neg (by omega)]; omega
    have h := Y.tau1.c433red F hcf hcube hmin hTw hM hi3 (3 * i - 1 - j) (by omega) (by omega) q
      (by show G.Adj q (Y.g (rho1 i _)); rw [e1]; exact hqk)
      (by show G.Adj q (Y.g (rho1 i _)); rw [e2]; exact hqj)
    have h2 := Y.tau1_twin_rev q (Sum.inl (3 * i - 1 - j + 2 * i - 1)) ⟨by omega, fun _ => by omega⟩ h
    simpa only [pi1, e3] using h2

/-- LPR Claim 4.34 (1) (i ≥ 3): if a, u ∈ N(q) and j ≤ i-2, then j+i or j+2i is in N(q).
Corollary 4.9 (Lemma 4.8) in Υ(π_j), Claim 4.33 and the twin property. -/
theorem Vega.c434one [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (ha : G.Adj q Y.a) (hu : G.Adj q Y.u) (j : ℕ) (hj : j + 2 ≤ i) :
    G.Adj q (Y.g (j + i)) ∨ G.Adj q (Y.g (j + 2 * i)) := by
  have hi := Y.hi
  have hC := Y.grRed j (j + i) (j + 2 * i) (j + 1) (by omega) (by omega) (by omega)
    (by intro _; omega) (by omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases F.l48 hC Y.a q (hC 3).2.2.2 (hC 2).2.2.2 ha hu with
    h | h | ⟨X, Z, hqX, hqZ, ⟨hX2, -, -, hX4⟩, ⟨-, hZ3, hZ1, -⟩⟩
  · exact Or.inr h
  · exact Or.inl h
  · exfalso
    have hXt := Y.c433red F hcf hcube hmin hTw hM hi3 (j + 1) (by omega) (by omega) X hX4
      (by rw [show j + 1 + i - 1 = j + i by omega]; exact hX2)
    have hZt := Y.c433blue F hcf hcube hmin hTw hM hi3 (j + 2 * i) (by omega) (by omega) Z hZ3
      (by rw [show j + 2 * i - 2 * i = j by omega]; exact hZ1)
    rw [show j + 1 + 2 * i - 1 = j + 2 * i by omega] at hXt
    rw [show j + 2 * i - i = j + i by omega] at hZt
    have hZX := hTw _ _ Y hM (Sum.inl (j + i)) (Sum.inl (j + 2 * i)) ⟨by omega, fun _ => by omega⟩
      ⟨by omega, fun _ => by omega⟩ (by simp only [vadj, AA]; omega) Z X hZt hXt
    exact not_adj_both hcf hqZ hqX hZX

/-- LPR Claim 4.34 (2): if ν = 0 and a, u ∈ N(q), then 2i-1 ∈ N(q) (Lemma 4.11 in Υ(ω) and
Lemma 4.21'). -/
theorem Vega.c434two [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ : Bool} (Y : Vega G i μ false) (hM : VegaMax G i μ false) (q : V)
    (ha : G.Adj q Y.a) (hu : G.Adj q Y.u) : G.Adj q (Y.g (2 * i - 1)) := by
  have hi := Y.hi
  by_contra hn
  have hC := Y.grGreen (2 * i - 1) (i - 1) (2 * i) i (by omega) (by omega)
    (fun h => absurd h (by decide)) (by omega) le_rfl (by omega) le_rfl (by omega)
    (fun h => absurd h (by decide))
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  obtain ⟨-, t, ht0, ht1, ht3, -⟩ := F.l411r hC 2 q hu ha hn
  exact (Y.l421' hcf hcube hmin t ht3 ht1 ht0).elim
    (hM (i + 1) μ true (by unfold vsize; cases μ <;> simp <;> omega)).false

/-- LPR Claim 4.34 (i ≥ 3): if a, u ∈ N(q), then q is a twin of a red vertex. -/
theorem Vega.c434 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (ha : G.Adj q Y.a) (hu : G.Adj q Y.u) : ∃ k, k < i ∧ Y.Twin q (Sum.inl k) := by
  have hi := Y.hi
  classical
  have hex : ∃ k, k < i ∧ (k = i - 1 ∨ G.Adj q (Y.g (k + i))) := ⟨i - 1, by omega, Or.inl rfl⟩
  have hk0 := Nat.find_spec hex
  have hmin0 : ∀ m, m < Nat.find hex → ¬ (m < i ∧ (m = i - 1 ∨ G.Adj q (Y.g (m + i)))) :=
    fun m hm => Nat.find_min hex hm
  refine ⟨Nat.find hex, hk0.1, ?_⟩
  have e : Nat.find hex + i - i = Nat.find hex := by omega
  have H := Y.twin_red_of_dom hcf (Nat.find hex + i) (by omega) (by omega) q ha hu ?_
  · rwa [e] at H
  intro m hm1 hm2 hmn
  by_cases hm : m < 2 * i
  · by_cases h2 : m = 2 * i - 1
    · cases ν with
      | true => exact absurd h2 (hmn rfl)
      | false => rw [h2]; exact Y.c434two F hcf hcube hmin hM q ha hu
    · rcases hk0.2 with h | h
      · omega
      · exact Y.l420a hcf hcube q ha hu (Nat.find hex + i) (by omega) h m hm1 hm hmn
  · have hn := hmin0 (m - 2 * i) (by omega)
    rcases Y.c434one F hcf hcube hmin hTw hM hi3 q ha hu (m - 2 * i) (by omega) with h | h
    · exact absurd ⟨by omega, Or.inr h⟩ hn
    · rwa [show m - 2 * i + 2 * i = m by omega] at h

/-- LPR Claim 4.35 (1) (i ≥ 3): if c, w ∈ N(q) and 1 ≤ j ≤ i-2, then j or j+i is in N(q).
Corollary 4.9 (Lemma 4.8) in Υ(π_{2i+j-1}), Claim 4.33 and the twin property. -/
theorem Vega.c435one [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hc : G.Adj q Y.c) (hw : G.Adj q Y.w) (j : ℕ) (hj1 : 1 ≤ j) (hj : j + 2 ≤ i) :
    G.Adj q (Y.g j) ∨ G.Adj q (Y.g (j + i)) := by
  have hi := Y.hi
  have hC := Y.grBlue (2 * i + j - 1) j (i + j) (2 * i + j) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by intro _; omega) (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have hR := hC.rotV 4
  rcases F.l48 hR Y.c q (hR 3).2.2.2 (hR 2).2.2.2 hc hw with
    h | h | ⟨X, Z, hqX, hqZ, ⟨hX2, -, -, hX4⟩, ⟨-, hZ3, hZ1, -⟩⟩
  · right; rw [show j + i = i + j by omega]; exact h
  · exact Or.inl h
  · exfalso
    have hXt := Y.c433blue F hcf hcube hmin hTw hM hi3 (2 * i + j) (by omega) (by omega) X hX4
      (by rw [show 2 * i + j - 2 * i = j by omega]; exact hX2)
    have hZt := Y.c433green F hcf hcube hmin hTw hM hi3 (i + j) (by omega) (by omega)
      (by intro _; omega) Z hZ3 (by rw [show i + j + i - 1 = 2 * i + j - 1 by omega]; exact hZ1)
    rw [show 2 * i + j - i = i + j by omega] at hXt
    rw [show i + j - i = j by omega] at hZt
    have hZX := hTw _ _ Y hM (Sum.inl j) (Sum.inl (i + j)) ⟨by omega, fun _ => by omega⟩
      ⟨by omega, fun _ => by omega⟩ (by simp only [vadj, AA]; omega) Z X hZt hXt
    exact not_adj_both hcf hqZ hqX hZX

/-- LPR Claim 4.35 (2): if c, w ∈ N(q), then i-1 ∈ N(q) (Lemma 4.11 in Υ(η), Corollary 4.18,
Lemma 4.21'). -/
theorem Vega.c435two [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (hc : G.Adj q Y.c) (hw : G.Adj q Y.w) : G.Adj q (Y.g (i - 1)) := by
  have hi := Y.hi
  by_contra hn
  have hC := Y.grRed 0 i (2 * i) (i - 1) (by omega) le_rfl (by omega) (by intro _; omega)
    le_rfl (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  obtain ⟨-, z, hz4, hz3, hz1, hqz⟩ := F.l411r hC.reflV 3 q hw hc hn
  cases ν with
  | true =>
    exact (Y.c418 hcf hcube z hz1 hz3 hz4).elim
      (hM i μ false (by unfold vsize; cases μ <;> simp <;> omega)).false
  | false =>
    have htw : Y.Twin z (Sum.inl (2 * i - 1)) := by
      refine Y.twin_of_dom hcf z _ ⟨by omega, fun h => absurd h (by decide)⟩ ?_
      rintro (k | t) hs h
      · have hk := hs.1
        simp only [vadj, AA] at h
        exact Y.l417a hcf hcube z hz1 hz3 (i - 1) (by omega) hz4 k (by omega)
      · simp only [vadj, colAdj] at h
        fin_cases t <;> simp at h <;> first | exact hz1 | exact hz3 | omega
    have hc' : G.Adj q (Y.repl (Sum.inl (2 * i - 1)) z htw).c := by
      show G.Adj q (Function.update Y.emb (Sum.inl (2 * i - 1)) z (Sum.inr 2))
      rw [Function.update_of_ne (by simp)]; exact hc
    have hw' : G.Adj q (Y.repl (Sum.inl (2 * i - 1)) z htw).w := by
      show G.Adj q (Function.update Y.emb (Sum.inl (2 * i - 1)) z (Sum.inr 5))
      rw [Function.update_of_ne (by simp)]; exact hw
    have hz' : G.Adj q ((Y.repl (Sum.inl (2 * i - 1)) z htw).g (2 * i - 1)) := by
      show G.Adj q (Function.update Y.emb (Sum.inl (2 * i - 1)) z (Sum.inl (2 * i - 1)))
      rw [Function.update_self]; exact hqz
    exact ((Y.repl (Sum.inl (2 * i - 1)) z htw).l421' hcf hcube hmin q hc' hw' hz').elim
      (hM (i + 1) μ true (by unfold vsize; cases μ <;> simp <;> omega)).false

/-- LPR Claim 4.35 (3) (i ≥ 3): if c, w ∈ N(q), then i ∈ N(q) (Lemma 4.12 in Υ(η), Claims 4.34,
4.33 and the twin property). -/
theorem Vega.c435three [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hc : G.Adj q Y.c) (hw : G.Adj q Y.w) : G.Adj q (Y.g i) := by
  have hi := Y.hi
  by_contra hn
  have hC := Y.grRed 0 i (2 * i) (i - 1) (by omega) le_rfl (by omega) (by intro _; omega)
    le_rfl (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  rcases F.l412r hC.reflV 3 q hw hc with
    h0 | h1 | ⟨A2, B0, hqA, hqB, ⟨hA1, hA2, hA3⟩, ⟨-, hB2, hB3, -⟩⟩
  · cases ν with
    | true =>
      exact (Y.c418' hcf hcube q hc hw h0).elim
        (hM i μ false (by unfold vsize; cases μ <;> simp <;> omega)).false
    | false =>
      exact (Y.l421 hcf hcube hmin q hc hw h0).elim
        (hM (i + 1) μ true (by unfold vsize; cases μ <;> simp <;> omega)).false
  · exact hn h1
  · obtain ⟨k, hk, hAk⟩ := Y.c434 F hcf hcube hmin hTw hM hi3 A2 hA3 hA2
    have hk0 : k = 0 := by
      have := (hAk (Sum.inl i) ⟨by omega, fun _ => by omega⟩).mp hA1
      simp only [vadj, AA] at this; omega
    subst hk0
    have hBt := Y.c433blue F hcf hcube hmin hTw hM hi3 (2 * i) le_rfl (by omega) B0 hB2
      (by rw [show 2 * i - 2 * i = 0 by omega]; exact hB3)
    rw [show 2 * i - i = i by omega] at hBt
    have hAB := hTw _ _ Y hM (Sum.inl 0) (Sum.inl i) ⟨by omega, fun _ => by omega⟩
      ⟨by omega, fun _ => by omega⟩ (by simp only [vadj, AA]; omega) A2 B0 hAk hBt
    exact not_adj_both hcf hqA hqB hAB

/-- LPR Claim 4.35 (i ≥ 3): if c, w ∈ N(q), then q is a twin of a blue vertex k+2i-1. -/
theorem Vega.c435 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hc : G.Adj q Y.c) (hw : G.Adj q Y.w) :
    ∃ k, 1 ≤ k ∧ k < i ∧ Y.Twin q (Sum.inl (k + 2 * i - 1)) := by
  have hi := Y.hi
  classical
  have h2 := Y.c435two F hcf hcube hmin hM q hc hw
  have hex : ∃ k, 1 ≤ k ∧ G.Adj q (Y.g k) := ⟨i - 1, by omega, h2⟩
  have hk0 := Nat.find_spec hex
  have hle : Nat.find hex ≤ i - 1 := Nat.find_min' hex ⟨by omega, h2⟩
  have hmin0 : ∀ m, m < Nat.find hex → ¬ (1 ≤ m ∧ G.Adj q (Y.g m)) :=
    fun m hm => Nat.find_min hex hm
  refine ⟨Nat.find hex, hk0.1, by omega, ?_⟩
  refine Y.twin_blue_of_dom hcf (Nat.find hex) hk0.1 (by omega) q hc hw ?_
  intro m hm1 hm2
  by_cases hm : m < i
  · exact Y.l419a hcf hcube q hc hw (Nat.find hex) hk0.2 m hm1 hm
  · by_cases hmi : m = i
    · rw [hmi]; exact Y.c435three F hcf hcube hmin hTw hM hi3 q hc hw
    · have hn := hmin0 (m - i) (by omega)
      rcases Y.c435one F hcf hcube hmin hTw hM hi3 q hc hw (m - i) (by omega) (by omega) with
        h | h
      · exact absurd ⟨by omega, h⟩ hn
      · rwa [show m - i + i = m by omega] at h

/-- LPR Claim 4.36 (i ≥ 3): if b, v ∈ N(q), then q is a twin of a green vertex (τν-symmetry). -/
theorem Vega.c436 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hb : G.Adj q Y.b) (hv : G.Adj q Y.v) :
    ∃ m, i ≤ m ∧ m < 2 * i ∧ (ν = true → m ≠ 2 * i - 1) ∧ Y.Twin q (Sum.inl m) := by
  have hi := Y.hi
  cases ν with
  | false =>
    obtain ⟨k, hk, h⟩ := Y.tau0.c434 F hcf hcube hmin hTw hM hi3 q hb hv
    have h2 := Y.tau0_twin_rev q (Sum.inl k) ⟨by omega, fun h => absurd h (by decide)⟩ h
    have e : rho0 i k = 2 * i - 1 - k := by unfold rho0; rw [if_pos (by omega)]
    refine ⟨2 * i - 1 - k, by omega, by omega, fun h => absurd h (by decide), ?_⟩
    rw [← e]; exact h2
  | true =>
    obtain ⟨k, hk1, hk, h⟩ := Y.tau1.c435 F hcf hcube hmin hTw hM hi3 q hb hv
    have h2 := Y.tau1_twin_rev q (Sum.inl (k + 2 * i - 1)) ⟨by omega, fun _ => by omega⟩ h
    have e : rho1 i (k + 2 * i - 1) = 2 * i - 1 - k := by
      unfold rho1; rw [if_neg (by omega), if_neg (by omega)]; omega
    refine ⟨2 * i - 1 - k, by omega, by omega, fun _ => by omega, ?_⟩
    rw [← e]; exact h2

/-- Final step of LPR Claim 4.37: a neighbour of x and of some Andrásfai vertex that is adjacent
to two of u, v, w is a twin of a, b or c (Claim 4.30; y is excluded since y has no Andrásfai
neighbour). -/
theorem Vega.c437fin [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i) (Y : Vega G i μ ν)
    (hM : VegaMax G i μ ν) (q : V) (j : ℕ) (hj : pres i μ ν (Sum.inl j))
    (hqj : G.Adj q (Y.g j))
    (h2 : (G.Adj q Y.u ∧ G.Adj q Y.v) ∨ (G.Adj q Y.v ∧ G.Adj q Y.w) ∨
      (G.Adj q Y.u ∧ G.Adj q Y.w)) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2) ∧ Y.Twin q p := by
  obtain ⟨p, hp, h⟩ := Y.c430A F hcf hcube hmin hTw hM q h2
  refine ⟨p, ?_, h⟩
  rcases hp with h1 | h1 | h1 | ⟨-, rfl⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)
  · exact absurd ((h (Sum.inl j) hj).mp hqj) (by simp [vadj, colAdj])

/-- LPR Claim 4.37 (i ≥ 3): if q is adjacent to x and to some Andrásfai vertex, then q is a
twin of a, b or c (Lemma 4.10 in an auxiliary path copy ending in that vertex). -/
theorem Vega.c437g [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i) (Y : Vega G i μ ν) (hM : VegaMax G i μ ν)
    (hi3 : 2 ≤ i) (q : V)
    (hx : G.Adj q Y.x) (j : ℕ) (hj : pres i μ ν (Sum.inl j)) (hqj : G.Adj q (Y.g j))
    (hex : 3 ≤ i ∨ (j ≠ 3 * i - 2 ∧ (ν = true → j ≠ i))) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2) ∧ Y.Twin q p := by
  have hi := Y.hi
  obtain ⟨hj1, hjn⟩ := hj
  have Pl : ∀ m, m < 3 * i - 1 → (ν = true → m ≠ 2 * i - 1) → pres i μ ν (Sum.inl m) :=
    fun m h1 h2 => ⟨h1, h2⟩
  have fin := Y.c437fin F hcf hcube hmin hTw hM q j ⟨hj1, hjn⟩ hqj
  have ns := Y.noSmall2 F hcf hcube hmin hM q hx j
  by_cases hr : j < i
  · by_cases h0 : j = 0
    · subst h0
      have hC := Y.grRed 0 i (2 * i) 1 (by omega) le_rfl (by omega) (by intro _; omega)
        le_rfl (by omega) (by omega)
        (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
      rcases F.l410r hC 3 q hqj hx with h | h
      · exact fin (Or.inr (Or.inl ⟨h 3, h 2⟩))
      · exact (ns (2 * i) ⟨hj1, hjn⟩ (Pl _ (by omega) (by intro _; omega)) hqj h
          (fun h' => absurd (h'.2.mp (by omega)) (by omega))).elim
    · have hC := Y.grRed (j - 1) (j + i - 1) (j + 2 * i - 1) j (by omega) (by omega) (by omega)
        (by intro _; omega) (by omega) (by omega) hr
        (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
      rcases F.l410r hC 2 q hx hqj with h | h
      · exact fin (Or.inr (Or.inl ⟨h 3, h 2⟩))
      · exact (ns (j + i - 1) ⟨hj1, hjn⟩ (Pl _ (by omega) (by intro _; omega)) hqj h
          (fun h' => absurd (h'.1.mp (by omega)) (by omega))).elim
  · by_cases hg : j < 2 * i
    · by_cases hji : j = i
      · have hqi : G.Adj q (Y.g i) := hji ▸ hqj
        have hC := Y.grGreen (i + 1) 1 (2 * i) i (by omega) (by omega)
          (fun hν => by rcases hex with h | ⟨-, h⟩; omega; exact absurd hji (h hν))
          (by omega) le_rfl (by omega) le_rfl (by omega) (by intro _; omega)
          (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
        rcases F.l410r hC 1 q hx hqi with h | h
        · exact fin (Or.inr (Or.inr ⟨h 2, h 1⟩))
        · exact (ns 1 ⟨hj1, hjn⟩ (Pl _ (by omega) (by intro _; omega)) hqj h
            (fun h' => absurd (h'.1.mpr (by omega)) (by omega))).elim
      · have hC := Y.grGreen j (j - i) (j + i - 1) (j - 1) (by omega) hg hjn (by omega)
          (by omega) (by omega) (by omega) (by omega) (by intro _; omega)
          (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
        rcases F.l410r hC 2 q hqj hx with h | h
        · exact fin (Or.inr (Or.inr ⟨h 2, h 1⟩))
        · exact (ns (j + i - 1) ⟨hj1, hjn⟩ (Pl _ (by omega) (by intro _; omega)) hqj h
            (fun h' => absurd (h'.2.mp (by omega)) (by omega))).elim
    · by_cases hb : j + 2 < 3 * i
      · have hC := Y.grBlue j (j - 2 * i + 1) (j - i + 1) (j + 1) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by intro _; omega) (by omega) (by omega)
          (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
        rcases F.l410r hC 2 q hqj hx with h | h
        · exact fin (Or.inl ⟨h 2, h 1⟩)
        · exact (ns (j - i + 1) ⟨hj1, hjn⟩ (Pl _ (by omega) (by intro _; omega)) hqj h
            (fun h' => absurd (h'.2.mpr (by omega)) (by omega))).elim
      · have hi3' : 3 ≤ i := by rcases hex with h | ⟨h, -⟩; exact h; omega
        have hj' : j = 3 * i - 2 := by omega
        subst hj'
        have hC := Y.grBlue (3 * i - 3) (i - 2) (2 * i - 2) (3 * i - 2) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by intro _; omega) (by omega) (by omega)
          (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
        rcases F.l410r hC 1 q hx hqj with h | h
        · exact fin (Or.inl ⟨h 2, h 1⟩)
        · exact (ns (i - 2) ⟨hj1, hjn⟩ (Pl _ (by omega) (by intro _; omega)) hqj h
            (fun h' => absurd (h'.2.mpr (by omega)) (by omega))).elim

/-- LPR Claim 4.37, i = 2, blue vertex 4: via ϱ (ϱ(4) = 4, ϱ(x) = 0) and Claim 4.33. -/
theorem Vega.c437blue2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {μ ν : Bool} (hTw : TwAll G 2) (Y : Vega G 2 μ ν) (hM : VegaMax G 2 μ ν) (q : V)
    (hx : G.Adj q Y.x) (h4 : G.Adj q (Y.g 4)) : Y.Twin q (Sum.inr 2) := by
  have h := Y.rho2.c433blue F hcf hcube hmin hTw (vegaMax_swap hM) le_rfl 4 (by omega)
    (by omega) q (by simpa [Vega.rho2] using h4) (by simpa [Vega.rho2] using hx)
  have h' := Y.rho2_twin_rev q (Sum.inl ⟨2, by decide⟩) (by simpa [e5] using h)
  simpa [rhoP, e5] using h'

/-- LPR Claim 4.37 for all i ≥ 2. -/
theorem Vega.c437A [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i) (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (q : V)
    (hx : G.Adj q Y.x) (j : ℕ) (hj : pres i μ ν (Sum.inl j)) (hqj : G.Adj q (Y.g j)) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2) ∧ Y.Twin q p := by
  have hi := Y.hi
  rcases Nat.lt_or_ge i 3 with hi2 | hi3
  · obtain rfl : i = 2 := by omega
    by_cases h4 : j = 4
    · subst h4
      exact ⟨_, Or.inr (Or.inr rfl), Y.c437blue2 F hcf hcube hmin hTw hM q hx hqj⟩
    by_cases h2 : j = 2 ∧ ν = true
    · obtain ⟨rfl, rfl⟩ := h2
      have e : rho1 2 4 = 2 := by decide
      have := Y.tau1.c437blue2 F hcf hcube hmin hTw hM q hx
        (by show G.Adj q (Y.g (rho1 2 4)); rw [e]; exact hqj)
      exact ⟨_, Or.inr (Or.inl rfl), Y.tau1_twin_rev q (Sum.inr 2) (Or.inl (by decide)) this⟩
    · refine Y.c437g F hcf hcube hmin hTw hM le_rfl q hx j hj hqj (Or.inr ⟨by omega, ?_⟩)
      intro hν hj2; exact h2 ⟨hj2, hν⟩
  · exact Y.c437g F hcf hcube hmin hTw hM (by omega) q hx j hj hqj (Or.inl hi3)

/-- LPR Claim 4.38, first part (i ≥ 3): if x ∈ N(q) and u ∉ N(q), then q is a twin of a, b or c
(hexagon q z u 0 a x, 𝒟₂, Claims 4.34 and 4.37). -/
theorem Vega.c438u [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hx : G.Adj q Y.x) (hnu : ¬ G.Adj q Y.u) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2) ∧ Y.Twin q p := by
  have hi := Y.hi
  have r0 := Y.red 0 (by omega)
  have hne : q ≠ Y.u := by
    rintro rfl; exact not_adj_both hcf Y.cu Y.xc.symm hx
  obtain ⟨z, hqz, huz⟩ := hmax q Y.u hne hnu
  obtain ⟨t, ⟨htq, htu, hta⟩ | ⟨htz, ht0, htx⟩⟩ :=
    hexD hcf hmin q z Y.u (Y.g 0) Y.a Y.x hqz huz.symm r0.2 r0.1.symm Y.xa.symm hx.symm
  · obtain ⟨j, hj, htj⟩ := Y.c434 F hcf hcube hmin hTw hM hi3 t hta htu
    have hx' : G.Adj q (Y.repl (Sum.inl j) t htj).x := by
      show G.Adj q (Function.update Y.emb (Sum.inl j) t (Sum.inr 6))
      rw [Function.update_of_ne (by simp)]; exact hx
    have hj' : G.Adj q ((Y.repl (Sum.inl j) t htj).g j) := by
      show G.Adj q (Function.update Y.emb (Sum.inl j) t (Sum.inl j))
      rw [Function.update_self]; exact htq.symm
    obtain ⟨p, hp, hqp⟩ := (Y.repl (Sum.inl j) t htj).c437A F hcf hcube hmin hTw hM q hx' j
      ⟨by omega, fun _ => by omega⟩ hj'
    exact ⟨p, hp, Y.twin_back hcf (Sum.inl j) ⟨by omega, fun _ => by omega⟩ t htj (hTw _ _ _ hM) p
      (pres_abc p hp) q hqp⟩
  · obtain ⟨p, hp, htp⟩ := Y.c437A F hcf hcube hmin hTw hM t htx 0
      ⟨by omega, fun _ => by omega⟩ ht0
    have hta : Y.Twin t (Sum.inr 0) := by
      rcases hp with rfl | rfl | rfl
      · exact htp
      · have := (htp (Sum.inl 0) ⟨by omega, fun _ => by omega⟩).mp ht0
        simp only [vadj, colAdj] at this; omega
      · have := (htp (Sum.inl 0) ⟨by omega, fun _ => by omega⟩).mp ht0
        simp only [vadj, colAdj] at this; omega
    have hza : G.Adj z (Y.repl (Sum.inr 0) t hta).a := by
      show G.Adj z (Function.update Y.emb (Sum.inr 0) t (Sum.inr 0))
      rw [Function.update_self]; exact htz.symm
    have hzu : G.Adj z (Y.repl (Sum.inr 0) t hta).u := by
      show G.Adj z (Function.update Y.emb (Sum.inr 0) t (Sum.inr 3))
      rw [Function.update_of_ne (by decide)]; exact huz.symm
    obtain ⟨j, hj, hzj⟩ := (Y.repl (Sum.inr 0) t hta).c434 F hcf hcube hmin hTw hM hi3 z hza hzu
    have hx' : G.Adj q ((Y.repl (Sum.inr 0) t hta).repl (Sum.inl j) z hzj).x := by
      show G.Adj q (Function.update (Y.repl (Sum.inr 0) t hta).emb (Sum.inl j) z (Sum.inr 6))
      rw [Function.update_of_ne (by simp)]
      show G.Adj q (Function.update Y.emb (Sum.inr 0) t (Sum.inr 6))
      rw [Function.update_of_ne (by decide)]; exact hx
    have hj' : G.Adj q (((Y.repl (Sum.inr 0) t hta).repl (Sum.inl j) z hzj).g j) := by
      show G.Adj q (Function.update (Y.repl (Sum.inr 0) t hta).emb (Sum.inl j) z (Sum.inl j))
      rw [Function.update_self]; exact hqz
    obtain ⟨p, hp, hqp⟩ := ((Y.repl (Sum.inr 0) t hta).repl (Sum.inl j) z hzj).c437A F hcf hcube
      hmin hTw hM q hx' j ⟨by omega, fun _ => by omega⟩ hj'
    have h1 := (Y.repl (Sum.inr 0) t hta).twin_back hcf (Sum.inl j) ⟨by omega, fun _ => by omega⟩
      z hzj (hTw _ _ _ hM) p (pres_abc p hp) q hqp
    exact ⟨p, hp, Y.twin_back hcf (Sum.inr 0) (Or.inl (by decide)) t hta (hTw _ _ _ hM) p
      (pres_abc p hp) q h1⟩

/-- LPR Claim 4.38, second part (i ≥ 3): if x ∈ N(q) and w ∉ N(q), then q is a twin of a, b or c
(hexagon q z w 2i c x, 𝒟₂, Claims 4.35 and 4.37). -/
theorem Vega.c438w [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hx : G.Adj q Y.x) (hnw : ¬ G.Adj q Y.w) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2) ∧ Y.Twin q p := by
  have hi := Y.hi
  have b2 := Y.blue (2 * i) le_rfl (by omega)
  have hne : q ≠ Y.w := by
    rintro rfl; exact not_adj_both hcf Y.wa.symm Y.xa.symm hx
  obtain ⟨z, hqz, hwz⟩ := hmax q Y.w hne hnw
  obtain ⟨t, ⟨htq, htw, htc⟩ | ⟨htz, ht0, htx⟩⟩ :=
    hexD hcf hmin q z Y.w (Y.g (2 * i)) Y.c Y.x hqz hwz.symm b2.2 b2.1.symm Y.xc.symm hx.symm
  · obtain ⟨k, hk1, hk, htk⟩ := Y.c435 F hcf hcube hmin hTw hM hi3 t htc htw
    have hx' : G.Adj q (Y.repl (Sum.inl (k + 2 * i - 1)) t htk).x := by
      show G.Adj q (Function.update Y.emb (Sum.inl (k + 2 * i - 1)) t (Sum.inr 6))
      rw [Function.update_of_ne (by simp)]; exact hx
    have hj' : G.Adj q ((Y.repl (Sum.inl (k + 2 * i - 1)) t htk).g (k + 2 * i - 1)) := by
      show G.Adj q (Function.update Y.emb (Sum.inl (k + 2 * i - 1)) t (Sum.inl (k + 2 * i - 1)))
      rw [Function.update_self]; exact htq.symm
    obtain ⟨p, hp, hqp⟩ := (Y.repl (Sum.inl (k + 2 * i - 1)) t htk).c437A F hcf hcube hmin hTw hM
      q hx' (k + 2 * i - 1) ⟨by omega, fun _ => by omega⟩ hj'
    exact ⟨p, hp, Y.twin_back hcf (Sum.inl (k + 2 * i - 1)) ⟨by omega, fun _ => by omega⟩ t htk (hTw _ _ _ hM) p
      (pres_abc p hp) q hqp⟩
  · obtain ⟨p, hp, htp⟩ := Y.c437A F hcf hcube hmin hTw hM t htx (2 * i)
      ⟨by omega, fun _ => by omega⟩ ht0
    have htc : Y.Twin t (Sum.inr 2) := by
      rcases hp with rfl | rfl | rfl
      · have := (htp (Sum.inl (2 * i)) ⟨by omega, fun _ => by omega⟩).mp ht0
        simp only [vadj, colAdj] at this; omega
      · have := (htp (Sum.inl (2 * i)) ⟨by omega, fun _ => by omega⟩).mp ht0
        simp only [vadj, colAdj] at this; omega
      · exact htp
    have hzc : G.Adj z (Y.repl (Sum.inr 2) t htc).c := by
      show G.Adj z (Function.update Y.emb (Sum.inr 2) t (Sum.inr 2))
      rw [Function.update_self]; exact htz.symm
    have hzw : G.Adj z (Y.repl (Sum.inr 2) t htc).w := by
      show G.Adj z (Function.update Y.emb (Sum.inr 2) t (Sum.inr 5))
      rw [Function.update_of_ne (by decide)]; exact hwz.symm
    obtain ⟨k, hk1, hk, hzk⟩ :=
      (Y.repl (Sum.inr 2) t htc).c435 F hcf hcube hmin hTw hM hi3 z hzc hzw
    have hx' : G.Adj q ((Y.repl (Sum.inr 2) t htc).repl (Sum.inl (k + 2 * i - 1)) z hzk).x := by
      show G.Adj q (Function.update (Y.repl (Sum.inr 2) t htc).emb (Sum.inl (k + 2 * i - 1)) z
        (Sum.inr 6))
      rw [Function.update_of_ne (by simp)]
      show G.Adj q (Function.update Y.emb (Sum.inr 2) t (Sum.inr 6))
      rw [Function.update_of_ne (by decide)]; exact hx
    have hj' : G.Adj q (((Y.repl (Sum.inr 2) t htc).repl (Sum.inl (k + 2 * i - 1)) z hzk).g
        (k + 2 * i - 1)) := by
      show G.Adj q (Function.update (Y.repl (Sum.inr 2) t htc).emb (Sum.inl (k + 2 * i - 1)) z
        (Sum.inl (k + 2 * i - 1)))
      rw [Function.update_self]; exact hqz
    obtain ⟨p, hp, hqp⟩ := ((Y.repl (Sum.inr 2) t htc).repl (Sum.inl (k + 2 * i - 1)) z
      hzk).c437A F hcf hcube hmin hTw hM q hx' (k + 2 * i - 1) ⟨by omega, fun _ => by omega⟩ hj'
    have h1 := (Y.repl (Sum.inr 2) t htc).twin_back hcf (Sum.inl (k + 2 * i - 1))
      ⟨by omega, fun _ => by omega⟩ z hzk (hTw _ _ _ hM) p (pres_abc p hp) q hqp
    exact ⟨p, hp, Y.twin_back hcf (Sum.inr 2) (Or.inl (by decide)) t htc (hTw _ _ _ hM) p
      (pres_abc p hp) q h1⟩

/-- LPR Claim 4.38 (i ≥ 3): if x ∈ N(q), then q is a twin of a, b, c or y. -/
theorem Vega.c438 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V) (hx : G.Adj q Y.x) :
    ∃ p, (p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2 ∨ (μ = false ∧ p = Sum.inr 7)) ∧
      Y.Twin q p := by
  by_cases hu : G.Adj q Y.u
  · by_cases hw : G.Adj q Y.w
    · exact Y.c430A F hcf hcube hmin hTw hM q (Or.inr (Or.inr ⟨hu, hw⟩))
    · obtain ⟨p, hp, h⟩ := Y.c438w F hcf hcube hmin hmax hTw hM hi3 q hx hw
      exact ⟨p, by rcases hp with h | h | h <;> simp [h], h⟩
  · obtain ⟨p, hp, h⟩ := Y.c438u F hcf hcube hmin hmax hTw hM hi3 q hx hu
    exact ⟨p, by rcases hp with h | h | h <;> simp [h], h⟩

/-- LPR Lemma 4.16(b) in twin form: a common neighbour of a, b, c is a twin of x. -/
theorem Vega.twin_x_of_abc (hcf : G.CliqueFree 3) (hcube : NoCube G) {i : ℕ} {μ ν : Bool}
    (Y : Vega G i μ ν) (q : V) (ha : G.Adj q Y.a) (hb : G.Adj q Y.b) (hc : G.Adj q Y.c) :
    Y.Twin q (Sum.inr 6) := by
  refine Y.twin_of_dom hcf q _ (Or.inl (by decide)) ?_
  rintro (k | t) hs h
  · exact absurd h (by simp [vadj, colAdj])
  · fin_cases t <;> simp [vadj, hexAdj] at h <;> first | exact ha | exact hb | exact hc | skip
    cases μ with
    | false => exact Y.l416b hcf hcube q ha hb hc
    | true => exact absurd hs (by simp [pres])

/-- x is a twin of itself. -/
theorem Vega.twin_x_self (hcf : G.CliqueFree 3) {i : ℕ} {μ ν : Bool} (Y : Vega G i μ ν) :
    Y.Twin Y.x (Sum.inr 6) := by
  refine Y.twin_of_dom hcf Y.x _ (Or.inl (by decide)) ?_
  rintro (k | t) hs h
  · exact absurd h (by simp [vadj, colAdj])
  · fin_cases t <;> simp [vadj, hexAdj] at h <;>
      first | exact Y.xa | exact Y.xb | exact Y.xc | skip
    cases μ with
    | false => exact (Y.yx rfl).symm
    | true => exact absurd hs (by simp [pres])

/-- LPR Claim 4.39 (i ≥ 3): if μ = 0 and q is adjacent to a twin of y, then q is a twin of
u, v, w or x (σ applied to Claim 4.38, Lemma 2.3). -/
theorem Vega.c439 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i false ν) (hM : VegaMax G i false ν) (hi3 : 2 ≤ i) (y' : V)
    (hy : Y.Twin y' (Sum.inr 7)) (q : V) (hq : G.Adj q y') :
    ∃ p, (p = Sum.inr 3 ∨ p = Sum.inr 1 ∨ p = Sum.inr 5 ∨ p = Sum.inr 6) ∧ Y.Twin q p := by
  have key : ∀ Z : Vega G i false ν, G.Adj q Z.y →
      ∃ p, (p = Sum.inr 3 ∨ p = Sum.inr 1 ∨ p = Sum.inr 5 ∨ p = Sum.inr 6) ∧ Z.Twin q p := by
    intro Z hqy
    obtain ⟨p, hp, h⟩ := Z.sigma.c438 F hcf hcube hmin hmax hTw hM hi3 q hqy
    refine ⟨piS p, ?_, Z.sigma_twin_rev q p h⟩
    rcases hp with rfl | rfl | rfl | ⟨-, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hqy : G.Adj q (Y.repl (Sum.inr 7) y' hy).y := by
    show G.Adj q (Function.update Y.emb (Sum.inr 7) y' (Sum.inr 7))
    rw [Function.update_self]; exact hq
  obtain ⟨p, hp, h⟩ := key _ hqy
  refine ⟨p, hp, Y.twin_back hcf (Sum.inr 7) (Or.inr rfl) y' hy (hTw _ _ _ hM) p ?_ q h⟩
  rcases hp with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)

/-- LPR Claim 4.40 (i ≥ 3): if a ∈ N(q) and b or c ∈ N(q), then q is a twin of v, w, u or x
(Corollary 4.9 in Υ(π_0), Claims 4.30 and 4.32, Lemma 4.16(b), Lemma 2.3). -/
theorem Vega.c440 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (ha : G.Adj q Y.a) (hbc : G.Adj q Y.b ∨ G.Adj q Y.c) :
    ∃ p, (p = Sum.inr 1 ∨ p = Sum.inr 5 ∨ p = Sum.inr 3 ∨ p = Sum.inr 6) ∧ Y.Twin q p := by
  have hi := Y.hi
  have hC := Y.grRed 0 i (2 * i) 1 (by omega) le_rfl (by omega) (by intro _; omega)
    le_rfl (by omega) (by omega)
    (by unfold AA; omega) (by unfold AA; omega) (by unfold AA; omega)
  have from432 : ∀ j, pres i μ ν (Sum.inl j) → G.Adj q (Y.g j) →
      ((G.Adj q Y.a ∧ G.Adj q Y.b) ∨ (G.Adj q Y.b ∧ G.Adj q Y.c) ∨
        (G.Adj q Y.a ∧ G.Adj q Y.c)) →
      ∃ p, (p = Sum.inr 1 ∨ p = Sum.inr 5 ∨ p = Sum.inr 3 ∨ p = Sum.inr 6) ∧ Y.Twin q p := by
    intro j hj hqj h2
    obtain ⟨p, hp, h⟩ := Y.c432 F hcf hcube hmin hTw hM hi3 q h2 j hj hqj
    refine ⟨p, ?_, h⟩
    rcases hp with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  rcases hbc with hb | hc
  · have hR := hC.rotV 1
    rcases F.l48 hR Y.a q (hR 3).2.2.2 (hR 2).2.2.2 ha hb with
      h | h | ⟨X, -, hqX, -, ⟨hX2, hX4, hXu2, -⟩, -⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), Y.twin_x_of_abc hcf hcube q ha hb h⟩
    · exact from432 (2 * i) ⟨by omega, fun _ => by omega⟩ h (Or.inl ⟨ha, hb⟩)
    · obtain ⟨p, hp, hXp⟩ := Y.c430A F hcf hcube hmin hTw hM X (Or.inl ⟨hX4, hXu2⟩)
      have hXc : Y.Twin X (Sum.inr 2) := by
        rcases hp with rfl | rfl | rfl | ⟨-, rfl⟩
        · have := (hXp (Sum.inl (2 * i)) ⟨by omega, fun _ => by omega⟩).mp hX2
          simp [vadj, colAdj] at this <;> omega
        · have := (hXp (Sum.inl (2 * i)) ⟨by omega, fun _ => by omega⟩).mp hX2
          simp [vadj, colAdj] at this <;> omega
        · exact hXp
        · have := (hXp (Sum.inl (2 * i)) ⟨by omega, fun _ => by omega⟩).mp hX2
          simp [vadj, colAdj] at this
      have h1 : (Y.repl (Sum.inr 2) X hXc).Twin q (Sum.inr 6) := by
        refine (Y.repl (Sum.inr 2) X hXc).twin_x_of_abc hcf hcube q ?_ ?_ ?_
        · show G.Adj q (Function.update Y.emb (Sum.inr 2) X (Sum.inr 0))
          rw [Function.update_of_ne (by decide)]; exact ha
        · show G.Adj q (Function.update Y.emb (Sum.inr 2) X (Sum.inr 4))
          rw [Function.update_of_ne (by decide)]; exact hb
        · show G.Adj q (Function.update Y.emb (Sum.inr 2) X (Sum.inr 2))
          rw [Function.update_self]; exact hqX
      exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), Y.twin_back hcf (Sum.inr 2) (Or.inl (by decide))
        X hXc (hTw _ _ _ hM) (Sum.inr 6) (Or.inl (by decide)) q h1⟩
  · have hR := hC.rotV 4
    rcases F.l48 hR Y.a q (hR 3).2.2.2 (hR 2).2.2.2 ha hc with
      h | h | ⟨-, Z, -, hqZ, -, ⟨hZ1, hZ3, -, hZu3⟩⟩
    · exact from432 i ⟨by omega, fun _ => by omega⟩ h (Or.inr (Or.inr ⟨ha, hc⟩))
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), Y.twin_x_of_abc hcf hcube q ha h hc⟩
    · obtain ⟨p, hp, hZp⟩ := Y.c430A F hcf hcube hmin hTw hM Z (Or.inr (Or.inr ⟨hZ1, hZu3⟩))
      have hZb : Y.Twin Z (Sum.inr 4) := by
        rcases hp with rfl | rfl | rfl | ⟨-, rfl⟩
        · have := (hZp (Sum.inl i) ⟨by omega, fun _ => by omega⟩).mp hZ3
          simp [vadj, colAdj] at this <;> omega
        · exact hZp
        · have := (hZp (Sum.inl i) ⟨by omega, fun _ => by omega⟩).mp hZ3
          simp [vadj, colAdj] at this <;> omega
        · have := (hZp (Sum.inl i) ⟨by omega, fun _ => by omega⟩).mp hZ3
          simp [vadj, colAdj] at this
      have h1 : (Y.repl (Sum.inr 4) Z hZb).Twin q (Sum.inr 6) := by
        refine (Y.repl (Sum.inr 4) Z hZb).twin_x_of_abc hcf hcube q ?_ ?_ ?_
        · show G.Adj q (Function.update Y.emb (Sum.inr 4) Z (Sum.inr 0))
          rw [Function.update_of_ne (by decide)]; exact ha
        · show G.Adj q (Function.update Y.emb (Sum.inr 4) Z (Sum.inr 4))
          rw [Function.update_self]; exact hqZ
        · show G.Adj q (Function.update Y.emb (Sum.inr 4) Z (Sum.inr 2))
          rw [Function.update_of_ne (by decide)]; exact hc
      exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), Y.twin_back hcf (Sum.inr 4) (Or.inl (by decide))
        Z hZb (hTw _ _ _ hM) (Sum.inr 6) (Or.inl (by decide)) q h1⟩

/-- Finishing step shared by Claims 4.41 and 4.38-type hexagons: q ~ a, q ~ z, z ~ u, and z a
twin of a, b, c or y. -/
theorem Vega.fin441 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q z : V)
    (hqa : G.Adj q Y.a) (hqz : G.Adj q z) (hzu : G.Adj z Y.u) (p : ℕ ⊕ Fin 8)
    (hp : p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2 ∨ (μ = false ∧ p = Sum.inr 7))
    (hz : Y.Twin z p) : ∃ p', pres i μ ν p' ∧ Y.Twin q p' := by
  rcases hp with rfl | rfl | rfl | ⟨hμ, rfl⟩
  · exact absurd ((hz (Sum.inr 3) (Or.inl (by decide))).mp hzu) (by simp [vadj, hexAdj])
  · have hb : G.Adj q (Y.repl (Sum.inr 4) z hz).b := by
      show G.Adj q (Function.update Y.emb (Sum.inr 4) z (Sum.inr 4))
      rw [Function.update_self]; exact hqz
    have ha : G.Adj q (Y.repl (Sum.inr 4) z hz).a := by
      show G.Adj q (Function.update Y.emb (Sum.inr 4) z (Sum.inr 0))
      rw [Function.update_of_ne (by decide)]; exact hqa
    obtain ⟨p', hp', h⟩ := (Y.repl (Sum.inr 4) z hz).c440 F hcf hcube hmin hTw hM hi3 q ha
      (Or.inl hb)
    have hpp : pres i μ ν p' := by rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · have hc : G.Adj q (Y.repl (Sum.inr 2) z hz).c := by
      show G.Adj q (Function.update Y.emb (Sum.inr 2) z (Sum.inr 2))
      rw [Function.update_self]; exact hqz
    have ha : G.Adj q (Y.repl (Sum.inr 2) z hz).a := by
      show G.Adj q (Function.update Y.emb (Sum.inr 2) z (Sum.inr 0))
      rw [Function.update_of_ne (by decide)]; exact hqa
    obtain ⟨p', hp', h⟩ := (Y.repl (Sum.inr 2) z hz).c440 F hcf hcube hmin hTw hM hi3 q ha
      (Or.inr hc)
    have hpp : pres i μ ν p' := by rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · subst hμ
    obtain ⟨p', hp', h⟩ := Y.c439 F hcf hcube hmin hmax hTw hM hi3 z hz q hqz
    refine ⟨p', ?_, h⟩
    rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)

/-- LPR Claim 4.41 (i ≥ 3): every neighbour of a is a twin of some vertex of Υ (hexagon
q z u b w a). -/
theorem Vega.c441 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V) (ha : G.Adj q Y.a) :
    ∃ p, pres i μ ν p ∧ Y.Twin q p := by
  have hi := Y.hi
  by_cases hu : G.Adj q Y.u
  · obtain ⟨k, hk, h⟩ := Y.c434 F hcf hcube hmin hTw hM hi3 q ha hu
    exact ⟨Sum.inl k, ⟨by omega, fun _ => by omega⟩, h⟩
  have r0 := Y.red 0 (by omega)
  have hne : q ≠ Y.u := by
    rintro rfl; exact not_adj_both hcf r0.1.symm r0.2.symm ha.symm
  obtain ⟨z, hqz, huz⟩ := hmax q Y.u hne hu
  obtain ⟨t, ⟨htq, htu, htw⟩ | ⟨htz, htb, hta⟩⟩ :=
    hexD hcf hmin q z Y.u Y.b Y.w Y.a hqz huz.symm Y.ub Y.bw Y.wa ha.symm
  · obtain ⟨p, hp, htp⟩ := Y.c430A F hcf hcube hmin hTw hM t (Or.inr (Or.inr ⟨htu, htw⟩))
    exact Y.fin441 F hcf hcube hmin hmax hTw hM hi3 q t ha htq.symm htu p hp htp
  · obtain ⟨p, hp, htp⟩ := Y.c440 F hcf hcube hmin hTw hM hi3 t hta (Or.inl htb)
    rcases hp with rfl | rfl | rfl | rfl
    · exact absurd ((htp (Sum.inr 4) (Or.inl (by decide))).mp htb) (by simp [vadj, hexAdj])
    · have hzu : G.Adj z (Y.repl (Sum.inr 5) t htp).u := by
        show G.Adj z (Function.update Y.emb (Sum.inr 5) t (Sum.inr 3))
        rw [Function.update_of_ne (by decide)]; exact huz.symm
      have hzw : G.Adj z (Y.repl (Sum.inr 5) t htp).w := by
        show G.Adj z (Function.update Y.emb (Sum.inr 5) t (Sum.inr 5))
        rw [Function.update_self]; exact htz.symm
      have hqa : G.Adj q (Y.repl (Sum.inr 5) t htp).a := by
        show G.Adj q (Function.update Y.emb (Sum.inr 5) t (Sum.inr 0))
        rw [Function.update_of_ne (by decide)]; exact ha
      obtain ⟨p2, hp2, hz2⟩ := (Y.repl (Sum.inr 5) t htp).c430A F hcf hcube hmin hTw hM z
        (Or.inr (Or.inr ⟨hzu, hzw⟩))
      obtain ⟨p, hp, h⟩ := (Y.repl (Sum.inr 5) t htp).fin441 F hcf hcube hmin hmax hTw hM hi3
        q z hqa hqz hzu p2 hp2 hz2
      exact ⟨p, hp, Y.twin_back' hcf t htp (Or.inl (by decide)) (hTw _ _ _ hM) p hp q h⟩
    · exact absurd ((htp (Sum.inr 0) (Or.inl (by decide))).mp hta) (by simp [vadj, hexAdj])
    · have hzu : G.Adj z (Y.repl (Sum.inr 6) t htp).u := by
        show G.Adj z (Function.update Y.emb (Sum.inr 6) t (Sum.inr 3))
        rw [Function.update_of_ne (by decide)]; exact huz.symm
      have hzx : G.Adj z (Y.repl (Sum.inr 6) t htp).x := by
        show G.Adj z (Function.update Y.emb (Sum.inr 6) t (Sum.inr 6))
        rw [Function.update_self]; exact htz.symm
      have hqa : G.Adj q (Y.repl (Sum.inr 6) t htp).a := by
        show G.Adj q (Function.update Y.emb (Sum.inr 6) t (Sum.inr 0))
        rw [Function.update_of_ne (by decide)]; exact ha
      obtain ⟨p2, hp2, hz2⟩ := (Y.repl (Sum.inr 6) t htp).c438 F hcf hcube hmin hmax hTw hM hi3
        z hzx
      obtain ⟨p, hp, h⟩ := (Y.repl (Sum.inr 6) t htp).fin441 F hcf hcube hmin hmax hTw hM hi3
        q z hqa hqz hzu p2 hp2 hz2
      exact ⟨p, hp, Y.twin_back' hcf t htp (Or.inl (by decide)) (hTw _ _ _ hM) p hp q h⟩

/-- LPR Claim 4.42 (i ≥ 3): a common neighbour of b and c is a twin of some vertex. -/
theorem Vega.c442 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hb : G.Adj q Y.b) (hc : G.Adj q Y.c) : ∃ p, pres i μ ν p ∧ Y.Twin q p := by
  have hi := Y.hi
  by_cases ha : G.Adj q Y.a
  · exact ⟨Sum.inr 6, Or.inl (by decide), Y.twin_x_of_abc hcf hcube q ha hb hc⟩
  have hne : q ≠ Y.a := by
    rintro rfl; exact not_adj_both hcf Y.xa Y.xb hb
  obtain ⟨z, hqz, haz⟩ := hmax q Y.a hne ha
  obtain ⟨p, hp, hzp⟩ := Y.c441 F hcf hcube hmin hmax hTw hM hi3 z haz.symm
  have hzb : ¬ G.Adj z Y.b := not_adj_both hcf hqz hb
  have hzc : ¬ G.Adj z Y.c := not_adj_both hcf hqz hc
  rcases p with j | t
  · have hj := (hzp (Sum.inr 0) (Or.inl (by decide))).mp haz.symm
    simp only [vadj, colAdj] at hj
    have hji : j < i := by
      rcases hj with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> first | exact h | (exfalso; revert h; decide)
    have hb' : G.Adj q (Y.repl (Sum.inl j) z hzp).b := by
      show G.Adj q (Function.update Y.emb (Sum.inl j) z (Sum.inr 4))
      rw [Function.update_of_ne (by simp)]; exact hb
    have hc' : G.Adj q (Y.repl (Sum.inl j) z hzp).c := by
      show G.Adj q (Function.update Y.emb (Sum.inl j) z (Sum.inr 2))
      rw [Function.update_of_ne (by simp)]; exact hc
    have hj' : G.Adj q ((Y.repl (Sum.inl j) z hzp).g j) := by
      show G.Adj q (Function.update Y.emb (Sum.inl j) z (Sum.inl j))
      rw [Function.update_self]; exact hqz
    obtain ⟨p', hp', h⟩ := (Y.repl (Sum.inl j) z hzp).c432 F hcf hcube hmin hTw hM hi3 q
      (Or.inr (Or.inl ⟨hb', hc'⟩)) j hp hj'
    have hpp : pres i μ ν p' := by rcases hp' with rfl | rfl | rfl <;> exact Or.inl (by decide)
    exact ⟨p', hpp, Y.twin_back' hcf z hzp hp (hTw _ _ _ hM) p' hpp q h⟩
  · exfalso
    have key : ∀ s : Fin 8, hexAdj s 0 → hexAdj s 4 ∨ hexAdj s 2 := by decide
    rcases key t ((hzp (Sum.inr 0) (Or.inl (by decide))).mp haz.symm) with h | h
    · exact hzb ((hzp (Sum.inr 4) (Or.inl (by decide))).mpr h)
    · exact hzc ((hzp (Sum.inr 2) (Or.inl (by decide))).mpr h)

/-- Finishing step of Claim 4.43, b-version: q ~ b, q ~ z, z ~ v, z twin of a, b, c or y. -/
theorem Vega.fin443b [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q z : V)
    (hqb : G.Adj q Y.b) (hqz : G.Adj q z) (hzv : G.Adj z Y.v) (p : ℕ ⊕ Fin 8)
    (hp : p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2 ∨ (μ = false ∧ p = Sum.inr 7))
    (hz : Y.Twin z p) : ∃ p', pres i μ ν p' ∧ Y.Twin q p' := by
  rcases hp with rfl | rfl | rfl | ⟨hμ, rfl⟩
  · have ha : G.Adj q (Y.repl (Sum.inr 0) z hz).a := by
      show G.Adj q (Function.update Y.emb (Sum.inr 0) z (Sum.inr 0))
      rw [Function.update_self]; exact hqz
    have hb : G.Adj q (Y.repl (Sum.inr 0) z hz).b := by
      show G.Adj q (Function.update Y.emb (Sum.inr 0) z (Sum.inr 4))
      rw [Function.update_of_ne (by decide)]; exact hqb
    obtain ⟨p', hp', h⟩ := (Y.repl (Sum.inr 0) z hz).c440 F hcf hcube hmin hTw hM hi3 q ha
      (Or.inl hb)
    have hpp : pres i μ ν p' := by rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · exact absurd ((hz (Sum.inr 1) (Or.inl (by decide))).mp hzv) (by simp [vadj, hexAdj])
  · have hc : G.Adj q (Y.repl (Sum.inr 2) z hz).c := by
      show G.Adj q (Function.update Y.emb (Sum.inr 2) z (Sum.inr 2))
      rw [Function.update_self]; exact hqz
    have hb : G.Adj q (Y.repl (Sum.inr 2) z hz).b := by
      show G.Adj q (Function.update Y.emb (Sum.inr 2) z (Sum.inr 4))
      rw [Function.update_of_ne (by decide)]; exact hqb
    obtain ⟨p', hpp, h⟩ := (Y.repl (Sum.inr 2) z hz).c442 F hcf hcube hmin hmax hTw hM hi3 q hb hc
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · subst hμ
    obtain ⟨p', hp', h⟩ := Y.c439 F hcf hcube hmin hmax hTw hM hi3 z hz q hqz
    refine ⟨p', ?_, h⟩
    rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)

/-- Finishing step of Claim 4.43, c-version: q ~ c, q ~ z, z ~ w, z twin of a, b, c or y. -/
theorem Vega.fin443c [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q z : V)
    (hqc : G.Adj q Y.c) (hqz : G.Adj q z) (hzw : G.Adj z Y.w) (p : ℕ ⊕ Fin 8)
    (hp : p = Sum.inr 0 ∨ p = Sum.inr 4 ∨ p = Sum.inr 2 ∨ (μ = false ∧ p = Sum.inr 7))
    (hz : Y.Twin z p) : ∃ p', pres i μ ν p' ∧ Y.Twin q p' := by
  rcases hp with rfl | rfl | rfl | ⟨hμ, rfl⟩
  · have ha : G.Adj q (Y.repl (Sum.inr 0) z hz).a := by
      show G.Adj q (Function.update Y.emb (Sum.inr 0) z (Sum.inr 0))
      rw [Function.update_self]; exact hqz
    have hc : G.Adj q (Y.repl (Sum.inr 0) z hz).c := by
      show G.Adj q (Function.update Y.emb (Sum.inr 0) z (Sum.inr 2))
      rw [Function.update_of_ne (by decide)]; exact hqc
    obtain ⟨p', hp', h⟩ := (Y.repl (Sum.inr 0) z hz).c440 F hcf hcube hmin hTw hM hi3 q ha
      (Or.inr hc)
    have hpp : pres i μ ν p' := by rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · have hb : G.Adj q (Y.repl (Sum.inr 4) z hz).b := by
      show G.Adj q (Function.update Y.emb (Sum.inr 4) z (Sum.inr 4))
      rw [Function.update_self]; exact hqz
    have hc : G.Adj q (Y.repl (Sum.inr 4) z hz).c := by
      show G.Adj q (Function.update Y.emb (Sum.inr 4) z (Sum.inr 2))
      rw [Function.update_of_ne (by decide)]; exact hqc
    obtain ⟨p', hpp, h⟩ := (Y.repl (Sum.inr 4) z hz).c442 F hcf hcube hmin hmax hTw hM hi3 q hb hc
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · exact absurd ((hz (Sum.inr 5) (Or.inl (by decide))).mp hzw) (by simp [vadj, hexAdj])
  · subst hμ
    obtain ⟨p', hp', h⟩ := Y.c439 F hcf hcube hmin hmax hTw hM hi3 z hz q hqz
    refine ⟨p', ?_, h⟩
    rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)

/-- LPR Claim 4.43 (i ≥ 3): every neighbour of b or c is a twin of some vertex of Υ (hexagons
q z v a w b and q z w a v c). -/
theorem Vega.c443 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V)
    (hbc : G.Adj q Y.b ∨ G.Adj q Y.c) : ∃ p, pres i μ ν p ∧ Y.Twin q p := by
  have hi := Y.hi
  rcases hbc with hb | hc
  · by_cases hv : G.Adj q Y.v
    · obtain ⟨m, hm1, hm2, hmn, h⟩ := Y.c436 F hcf hcube hmin hTw hM hi3 q hb hv
      exact ⟨Sum.inl m, ⟨by omega, hmn⟩, h⟩
    have gi := Y.green i le_rfl (by omega) (by intro _; omega)
    have hne : q ≠ Y.v := by
      rintro rfl; exact not_adj_both hcf gi.1.symm gi.2.symm hb.symm
    obtain ⟨z, hqz, hvz⟩ := hmax q Y.v hne hv
    obtain ⟨t, ⟨htq, htv, htw⟩ | ⟨htz, hta, htb⟩⟩ :=
      hexD hcf hmin q z Y.v Y.a Y.w Y.b hqz hvz.symm Y.av.symm Y.wa.symm Y.bw.symm hb.symm
    · obtain ⟨p, hp, htp⟩ := Y.c430A F hcf hcube hmin hTw hM t (Or.inr (Or.inl ⟨htv, htw⟩))
      exact Y.fin443b F hcf hcube hmin hmax hTw hM hi3 q t hb htq.symm htv p hp htp
    · obtain ⟨p, hp, htp⟩ := Y.c440 F hcf hcube hmin hTw hM hi3 t hta (Or.inl htb)
      rcases hp with rfl | rfl | rfl | rfl
      · exact absurd ((htp (Sum.inr 4) (Or.inl (by decide))).mp htb) (by simp [vadj, hexAdj])
      · have hzv : G.Adj z (Y.repl (Sum.inr 5) t htp).v := by
          show G.Adj z (Function.update Y.emb (Sum.inr 5) t (Sum.inr 1))
          rw [Function.update_of_ne (by decide)]; exact hvz.symm
        have hzw : G.Adj z (Y.repl (Sum.inr 5) t htp).w := by
          show G.Adj z (Function.update Y.emb (Sum.inr 5) t (Sum.inr 5))
          rw [Function.update_self]; exact htz.symm
        have hqb : G.Adj q (Y.repl (Sum.inr 5) t htp).b := by
          show G.Adj q (Function.update Y.emb (Sum.inr 5) t (Sum.inr 4))
          rw [Function.update_of_ne (by decide)]; exact hb
        obtain ⟨p2, hp2, hz2⟩ := (Y.repl (Sum.inr 5) t htp).c430A F hcf hcube hmin hTw hM z
          (Or.inr (Or.inl ⟨hzv, hzw⟩))
        obtain ⟨p, hp, h⟩ := (Y.repl (Sum.inr 5) t htp).fin443b F hcf hcube hmin hmax hTw hM hi3
          q z hqb hqz hzv p2 hp2 hz2
        exact ⟨p, hp, Y.twin_back' hcf t htp (Or.inl (by decide)) (hTw _ _ _ hM) p hp q h⟩
      · exact absurd ((htp (Sum.inr 0) (Or.inl (by decide))).mp hta) (by simp [vadj, hexAdj])
      · have hzv : G.Adj z (Y.repl (Sum.inr 6) t htp).v := by
          show G.Adj z (Function.update Y.emb (Sum.inr 6) t (Sum.inr 1))
          rw [Function.update_of_ne (by decide)]; exact hvz.symm
        have hzx : G.Adj z (Y.repl (Sum.inr 6) t htp).x := by
          show G.Adj z (Function.update Y.emb (Sum.inr 6) t (Sum.inr 6))
          rw [Function.update_self]; exact htz.symm
        have hqb : G.Adj q (Y.repl (Sum.inr 6) t htp).b := by
          show G.Adj q (Function.update Y.emb (Sum.inr 6) t (Sum.inr 4))
          rw [Function.update_of_ne (by decide)]; exact hb
        obtain ⟨p2, hp2, hz2⟩ := (Y.repl (Sum.inr 6) t htp).c438 F hcf hcube hmin hmax hTw hM hi3
          z hzx
        obtain ⟨p, hp, h⟩ := (Y.repl (Sum.inr 6) t htp).fin443b F hcf hcube hmin hmax hTw hM hi3
          q z hqb hqz hzv p2 hp2 hz2
        exact ⟨p, hp, Y.twin_back' hcf t htp (Or.inl (by decide)) (hTw _ _ _ hM) p hp q h⟩
  · by_cases hw : G.Adj q Y.w
    · obtain ⟨k, hk1, hk, h⟩ := Y.c435 F hcf hcube hmin hTw hM hi3 q hc hw
      exact ⟨Sum.inl (k + 2 * i - 1), ⟨by omega, fun _ => by omega⟩, h⟩
    have b2 := Y.blue (2 * i) le_rfl (by omega)
    have hne : q ≠ Y.w := by
      rintro rfl; exact not_adj_both hcf b2.1.symm b2.2.symm hc.symm
    obtain ⟨z, hqz, hwz⟩ := hmax q Y.w hne hw
    obtain ⟨t, ⟨htq, htw, htv⟩ | ⟨htz, hta, htc⟩⟩ :=
      hexD hcf hmin q z Y.w Y.a Y.v Y.c hqz hwz.symm Y.wa Y.av Y.vc hc.symm
    · obtain ⟨p, hp, htp⟩ := Y.c430A F hcf hcube hmin hTw hM t (Or.inr (Or.inl ⟨htv, htw⟩))
      exact Y.fin443c F hcf hcube hmin hmax hTw hM hi3 q t hc htq.symm htw p hp htp
    · obtain ⟨p, hp, htp⟩ := Y.c440 F hcf hcube hmin hTw hM hi3 t hta (Or.inr htc)
      rcases hp with rfl | rfl | rfl | rfl
      · have hzw : G.Adj z (Y.repl (Sum.inr 1) t htp).w := by
          show G.Adj z (Function.update Y.emb (Sum.inr 1) t (Sum.inr 5))
          rw [Function.update_of_ne (by decide)]; exact hwz.symm
        have hzv : G.Adj z (Y.repl (Sum.inr 1) t htp).v := by
          show G.Adj z (Function.update Y.emb (Sum.inr 1) t (Sum.inr 1))
          rw [Function.update_self]; exact htz.symm
        have hqc : G.Adj q (Y.repl (Sum.inr 1) t htp).c := by
          show G.Adj q (Function.update Y.emb (Sum.inr 1) t (Sum.inr 2))
          rw [Function.update_of_ne (by decide)]; exact hc
        obtain ⟨p2, hp2, hz2⟩ := (Y.repl (Sum.inr 1) t htp).c430A F hcf hcube hmin hTw hM z
          (Or.inr (Or.inl ⟨hzv, hzw⟩))
        obtain ⟨p, hp, h⟩ := (Y.repl (Sum.inr 1) t htp).fin443c F hcf hcube hmin hmax hTw hM hi3
          q z hqc hqz hzw p2 hp2 hz2
        exact ⟨p, hp, Y.twin_back' hcf t htp (Or.inl (by decide)) (hTw _ _ _ hM) p hp q h⟩
      · exact absurd ((htp (Sum.inr 2) (Or.inl (by decide))).mp htc) (by simp [vadj, hexAdj])
      · exact absurd ((htp (Sum.inr 0) (Or.inl (by decide))).mp hta) (by simp [vadj, hexAdj])
      · have hzw : G.Adj z (Y.repl (Sum.inr 6) t htp).w := by
          show G.Adj z (Function.update Y.emb (Sum.inr 6) t (Sum.inr 5))
          rw [Function.update_of_ne (by decide)]; exact hwz.symm
        have hzx : G.Adj z (Y.repl (Sum.inr 6) t htp).x := by
          show G.Adj z (Function.update Y.emb (Sum.inr 6) t (Sum.inr 6))
          rw [Function.update_self]; exact htz.symm
        have hqc : G.Adj q (Y.repl (Sum.inr 6) t htp).c := by
          show G.Adj q (Function.update Y.emb (Sum.inr 6) t (Sum.inr 2))
          rw [Function.update_of_ne (by decide)]; exact hc
        obtain ⟨p2, hp2, hz2⟩ := (Y.repl (Sum.inr 6) t htp).c438 F hcf hcube hmin hmax hTw hM hi3
          z hzx
        obtain ⟨p, hp, h⟩ := (Y.repl (Sum.inr 6) t htp).fin443c F hcf hcube hmin hmax hTw hM hi3
          q z hqc hqz hzw p2 hp2 hz2
        exact ⟨p, hp, Y.twin_back' hcf t htp (Or.inl (by decide)) (hTw _ _ _ hM) p hp q h⟩

/-- LPR Lemma 4.29 (attachment lemma) for i ≥ 3. -/
theorem Vega.attach3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    (hmax : ∀ u v : V, u ≠ v → ¬ G.Adj u v → ∃ w : V, G.Adj u w ∧ G.Adj v w)
    {i : ℕ} {μ ν : Bool} (hTw : TwAll G i)
    (Y : Vega G i μ ν) (hM : VegaMax G i μ ν) (hi3 : 2 ≤ i) (q : V) :
    ∃ p, pres i μ ν p ∧ Y.Twin q p := by
  by_cases hx : G.Adj q Y.x
  · obtain ⟨p, hp, h⟩ := Y.c438 F hcf hcube hmin hmax hTw hM hi3 q hx
    refine ⟨p, ?_, h⟩
    rcases hp with rfl | rfl | rfl | ⟨hμ, rfl⟩
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inl (by decide)
    · exact Or.inr hμ
  by_cases hqx : q = Y.x
  · subst hqx; exact ⟨Sum.inr 6, Or.inl (by decide), Y.twin_x_self hcf⟩
  obtain ⟨z, hqz, hxz⟩ := hmax q Y.x hqx hx
  obtain ⟨p, hp, hz⟩ := Y.c438 F hcf hcube hmin hmax hTw hM hi3 z hxz.symm
  rcases hp with rfl | rfl | rfl | ⟨hμ, rfl⟩
  · have ha : G.Adj q (Y.repl (Sum.inr 0) z hz).a := by
      show G.Adj q (Function.update Y.emb (Sum.inr 0) z (Sum.inr 0))
      rw [Function.update_self]; exact hqz
    obtain ⟨p', hpp, h⟩ := (Y.repl (Sum.inr 0) z hz).c441 F hcf hcube hmin hmax hTw hM hi3 q ha
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · have hb : G.Adj q (Y.repl (Sum.inr 4) z hz).b := by
      show G.Adj q (Function.update Y.emb (Sum.inr 4) z (Sum.inr 4))
      rw [Function.update_self]; exact hqz
    obtain ⟨p', hpp, h⟩ := (Y.repl (Sum.inr 4) z hz).c443 F hcf hcube hmin hmax hTw hM hi3 q
      (Or.inl hb)
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · have hc : G.Adj q (Y.repl (Sum.inr 2) z hz).c := by
      show G.Adj q (Function.update Y.emb (Sum.inr 2) z (Sum.inr 2))
      rw [Function.update_self]; exact hqz
    obtain ⟨p', hpp, h⟩ := (Y.repl (Sum.inr 2) z hz).c443 F hcf hcube hmin hmax hTw hM hi3 q
      (Or.inr hc)
    exact ⟨p', hpp, Y.twin_back' hcf z hz (Or.inl (by decide)) (hTw _ _ _ hM) p' hpp q h⟩
  · subst hμ
    obtain ⟨p', hp', h⟩ := Y.c439 F hcf hcube hmin hmax hTw hM hi3 z hz q hqz
    refine ⟨p', ?_, h⟩
    rcases hp' with rfl | rfl | rfl | rfl <;> exact Or.inl (by decide)

/-- LPR Lemma 4.29 (attachment lemma, twin form) for all i ≥ 2, given the twin lemma. -/
theorem attachTwinClaim_proof : AttachTwinClaim := by
  intro V _ _ G _ hcf hmax hmin hcube F hTw i μ ν Y hM q
  exact Y.attach3 F hcf hcube hmin hmax (fun μ' ν' Y' hM' => hTw i μ' ν' Y' hM') hM Y.hi q

end Attach


section Twin2
variable {V : Type} {G : SimpleGraph V}

theorem VegaMax.swap2 {μ ν : Bool} (h : VegaMax G 2 μ ν) : VegaMax G 2 ν μ := by
  intro i' μ' ν' hlt
  apply h
  unfold vsize at hlt ⊢
  cases μ <;> cases ν <;> simp_all

/-- The twin lemma (LPR 4.28) for i = 2, by transports σ, τ0, τ1, ϱ to the base lemmas
(derivations generated by E128H1_gen/twin_i2_search.py and gen_twin2.py). -/
theorem Vega.twinProp2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (F : GrFacts G)
    (hcf : G.CliqueFree 3) (hcube : NoCube G)
    (hmin : ∀ v : V, Fintype.card V < 3 * (G.neighborSet v).ncard)
    {μ ν : Bool} (Y : Vega G 2 μ ν) (hM : VegaMax G 2 μ ν) : Y.TwinProp := by
  have key : ∀ a b : Fin 5 ⊕ Fin 8, pres 2 μ ν (e5 a) → pres 2 μ ν (e5 b) →
      vadj 2 (e5 a) (e5 b) → Y.TwinE (e5 a) (e5 b) := by
    cases μ <;> cases ν <;> intro a b ha hb hv <;> rw [pres_iff_B] at ha hb <;>
      rw [vadj_iff_B] at hv <;> fin_cases a <;> fin_cases b
    all_goals first | (exfalso; revert ha hb hv; decide) | skip
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 0 2 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 0 3 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 1 3 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 1 4 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 0 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 4 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twin_v_green0 F hcf hcube hmin hM 2 (by omega) (by omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 2)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 2))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 3 0 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 3 1 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twin_v_green0' F hcf hcube hmin hM P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 3)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 3))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 1 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 2 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Y.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inl 4)) (e5 (Sum.inr 5)) (Y.sigma.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_v_green0 F hcf hcube hmin hM 2 (by omega) (by omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_v_green0' F hcf hcube hmin hM P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 1)) (e5 (Sum.inr 2)) (fun P S hP hS => Y.sigma.twin_b0 F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 1)) (e5 (Sum.inr 7)) (fun P S hP hS => Y.sigma.twin_b0 F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inr 2)) (e5 (Sum.inr 1)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_b0 F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 5))).mpr (by decide)) hS)))
    · exact (Y.sigmaE (e5 (Sum.inr 2)) (e5 (Sum.inr 3)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS)))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inr 3)) (e5 (Sum.inr 2)) (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 3)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 3))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 3)) (e5 (Sum.inr 7)) (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 2)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 2))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 3)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 3))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 3)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 3))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 5))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 6))).mpr (by decide)) hS)
    · exact (Y.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inl 4)) (Y.sigma.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inr 7)) (Y.sigma.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.l426xy hcf hcube P S ((hP (Sum.inr 0) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 0))).mpr (by decide))) ((hP (Sum.inr 4) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 4))).mpr (by decide))) ((hP (Sum.inr 2) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 2))).mpr (by decide))) ((hS (Sum.inr 3) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 3))).mpr (by decide))) ((hS (Sum.inr 1) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 1))).mpr (by decide))) ((hS (Sum.inr 5) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 5))).mpr (by decide))))
    · exact (Y.sigmaE (e5 (Sum.inr 7)) (e5 (Sum.inr 1)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_b0 F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 6))).mpr (by decide)) hS)))
    · exact (Y.sigmaE (e5 (Sum.inr 7)) (e5 (Sum.inr 3)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS)))
    · exact (Y.sigmaE (e5 (Sum.inr 7)) (e5 (Sum.inr 5)) (Y.sigma.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 false false _).mpr (by decide)) ((pres_iff_B 2 false false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.l426xy hcf hcube P S ((hP (Sum.inr 0) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 0))).mpr (by decide))) ((hP (Sum.inr 4) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 4))).mpr (by decide))) ((hP (Sum.inr 2) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 2))).mpr (by decide))) ((hS (Sum.inr 3) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 3))).mpr (by decide))) ((hS (Sum.inr 1) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 1))).mpr (by decide))) ((hS (Sum.inr 5) ((pres_iff_B 2 false false _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 5))).mpr (by decide)))))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 0 2 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 1 4 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 0 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 4 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Y.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.tau1.sigmaE (e5 (Sum.inl 4)) (e5 (Sum.inr 5)) (Y.tau1.sigma.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))
    · exact (Y.sigmaE (e5 (Sum.inl 2)) (e5 (Sum.inr 4)) (Y.sigma.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.sigma.tau1.sigmaE (e5 (Sum.inl 4)) (e5 (Sum.inr 5)) (Y.sigma.tau1.sigma.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.sigma.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 1 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 2 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Y.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inl 4)) (e5 (Sum.inr 5)) (Y.sigma.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS)
    · exact (Y.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.tau1.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inl 4)) (Y.tau1.sigma.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 1) (Sum.inr 2) (Vega.TwinE.symm' (fun P S hP hS => Y.rho2.twin_v_green0 F hcf hcube hmin hM.swap2 2 (by omega) (by omega) P S hP hS)))
    · exact (Y.rhoE (Sum.inr 1) (Sum.inr 7) (Vega.TwinE.symm' (fun P S hP hS => Y.rho2.twin_v_green0' F hcf hcube hmin hM.swap2 P S hP hS)))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 1) (fun P S hP hS => Y.rho2.twin_v_green0 F hcf hcube hmin hM.swap2 2 (by omega) (by omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inr 2)) (e5 (Sum.inr 3)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS)))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inr 3)) (e5 (Sum.inr 2)) (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 3)) (e5 (Sum.inr 4)) (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 3)) (e5 (Sum.inr 7)) (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 4)) (e5 (Sum.inl 2)) (Y.sigma.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.sigma.tau1.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inl 4)) (Y.sigma.tau1.sigma.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.sigma.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Y.sigmaE (e5 (Sum.inr 4)) (e5 (Sum.inr 3)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS)))
    · exact (Y.sigmaE (e5 (Sum.inr 4)) (e5 (Sum.inr 5)) (Y.sigma.rhoE (Sum.inr 1) (Sum.inr 2) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.rho2.twin_v_green0 F hcf hcube hmin hM.swap2 2 (by omega) (by omega) P S hP hS))))
    · exact (Y.sigmaE (e5 (Sum.inr 4)) (e5 (Sum.inr 6)) (Y.sigma.rhoE (Sum.inr 1) (Sum.inr 7) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.rho2.twin_v_green0' F hcf hcube hmin hM.swap2 P S hP hS))))
    · exact (Y.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inl 4)) (Y.sigma.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Y.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inr 4)) (Y.sigma.rhoE (Sum.inr 2) (Sum.inr 1) (fun P S hP hS => Y.sigma.rho2.twin_v_green0 F hcf hcube hmin hM.swap2 2 (by omega) (by omega) P S hP hS)))
    · exact (Y.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inr 7)) (Y.sigma.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inr 6)) (e5 (Sum.inr 4)) (Y.sigma.rhoE (Sum.inr 7) (Sum.inr 1) (fun P S hP hS => Y.sigma.rho2.twin_v_green0' F hcf hcube hmin hM.swap2 P S hP hS)))
    · exact (fun P S hP hS => Y.l426xy hcf hcube P S ((hP (Sum.inr 0) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 0))).mpr (by decide))) ((hP (Sum.inr 4) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 4))).mpr (by decide))) ((hP (Sum.inr 2) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 2))).mpr (by decide))) ((hS (Sum.inr 3) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 3))).mpr (by decide))) ((hS (Sum.inr 1) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 1))).mpr (by decide))) ((hS (Sum.inr 5) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 5))).mpr (by decide))))
    · exact (Y.rhoE (Sum.inr 7) (Sum.inr 1) (fun P S hP hS => Y.rho2.twin_v_green0' F hcf hcube hmin hM.swap2 P S hP hS))
    · exact (Y.sigmaE (e5 (Sum.inr 7)) (e5 (Sum.inr 3)) (Vega.TwinE.symm' (fun P S hP hS => Y.sigma.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 false true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS)))
    · exact (Y.sigmaE (e5 (Sum.inr 7)) (e5 (Sum.inr 5)) (Y.sigma.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.sigma.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.l426xy hcf hcube P S ((hP (Sum.inr 0) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 0))).mpr (by decide))) ((hP (Sum.inr 4) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 4))).mpr (by decide))) ((hP (Sum.inr 2) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 6)) (e5 (Sum.inr 2))).mpr (by decide))) ((hS (Sum.inr 3) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 3))).mpr (by decide))) ((hS (Sum.inr 1) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 1))).mpr (by decide))) ((hS (Sum.inr 5) ((pres_iff_B 2 false true _).mpr (by decide))).mpr ((vadj_iff_B 2 (e5 (Sum.inr 7)) (e5 (Sum.inr 5))).mpr (by decide)))))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 0 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 0 3 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 1 3 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 1 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 0 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twin_v_green0 F hcf hcube hmin hM 2 (by omega) (by omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 2)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 2))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 3 0 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 3 1 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twin_v_green0' F hcf hcube hmin hM P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 3)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 3))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 1 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Y.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.rhoE (Sum.inl 4) (Sum.inr 5) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 4 1 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_v_green0 F hcf hcube hmin hM 2 (by omega) (by omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_v_green0' F hcf hcube hmin hM P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 1) (Sum.inr 2) (Y.rho2.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.rho2.tau1.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inl 4)) (Y.rho2.tau1.sigma.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.rho2.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 1) (Y.rho2.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.rho2.tau1.sigmaE (e5 (Sum.inl 4)) (e5 (Sum.inr 5)) (Y.rho2.tau1.sigma.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.rho2.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Y.tau0E (e5 (Sum.inr 2)) (e5 (Sum.inr 3)) ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (Y.tau0.rhoE (Sum.inr 2) (Sum.inr 1) (Y.tau0.rho2.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.tau0.rho2.tau1.sigmaE (e5 (Sum.inl 4)) (e5 (Sum.inr 5)) (Y.tau0.rho2.tau1.sigma.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.tau0.rho2.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 4 2 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS))
    · exact (Y.tau0E (e5 (Sum.inr 3)) (e5 (Sum.inr 2)) ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (Y.tau0.rhoE (Sum.inr 1) (Sum.inr 2) (Y.tau0.rho2.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (Y.tau0.rho2.tau1.sigmaE (e5 (Sum.inr 5)) (e5 (Sum.inl 4)) (Y.tau0.rho2.tau1.sigma.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.tau0.rho2.tau1.sigma.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 2 4 ((pres_iff_B 2 true false _).mpr (by decide)) ((pres_iff_B 2 true false _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 3)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 3))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 2)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 2))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inl 3)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inl 3))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 3)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 3))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 5))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 6))).mpr (by decide)) hS)
    · exact (Y.rhoE (Sum.inr 5) (Sum.inl 4) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 1 4 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 false true _).mpr (by decide)) ((pres_iff_B 2 false true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_b0 F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 true false _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 4)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 0 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 1 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS))
    · exact (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 0 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 2 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Y.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inl 4) (Sum.inr 5) (fun P S hP hS => Y.tau1.rho2.twinGammaFull F hcf hcube hM.swap2 4 1 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Y.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 4)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.tau1.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 1 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (fun P S hP hS => Y.twinGammaFull F hcf hcube hM 4 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)
    · exact (Y.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 4 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.rhoE (Sum.inl 4) (Sum.inr 5) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 4 1 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 0)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 0))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inl 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inl 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS)
    · exact (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS)
    · exact (Y.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 5) (Sum.inl 4) (fun P S hP hS => Y.tau1.rho2.twinGammaFull F hcf hcube hM.swap2 1 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 1))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 1) (Sum.inr 2) (Y.rho2.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.rho2.tau1.rhoE (Sum.inr 5) (Sum.inl 4) (fun P S hP hS => Y.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 1 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 1) (Y.rho2.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.rho2.tau1.rhoE (Sum.inl 4) (Sum.inr 5) (fun P S hP hS => Y.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 4 1 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 3) (Y.rho2.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 4)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.rho2.tau1.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 4 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))
    · exact (Y.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red0 F hcf hcube hmin hM P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_u_red F hcf hcube hmin hM 1 (by omega) (by omega) P S hP hS))
    · exact (Y.rhoE (Sum.inr 3) (Sum.inr 2) (Y.rho2.tau1E (e5 (Sum.inr 4)) (e5 (Sum.inl 2)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.rho2.tau1.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 2 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))))
    · exact (Y.tau1E (e5 (Sum.inr 3)) (e5 (Sum.inr 4)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 3) (Sum.inr 2) (Y.tau1.rho2.tau1E (e5 (Sum.inr 4)) (e5 (Sum.inl 2)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rho2.tau1.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.tau1.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 2 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Y.tau1E (e5 (Sum.inr 4)) (e5 (Sum.inl 2)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 2) (Sum.inl 4) (fun P S hP hS => Y.tau1.rho2.twinGammaFull F hcf hcube hM.swap2 2 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Y.tau1E (e5 (Sum.inr 4)) (e5 (Sum.inr 3)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 2) (Sum.inr 3) (Y.tau1.rho2.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 4)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rho2.tau1.rhoE (Sum.inl 4) (Sum.inr 2) (fun P S hP hS => Y.tau1.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 4 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Y.tau1E (e5 (Sum.inr 4)) (e5 (Sum.inr 5)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 2) (Sum.inr 1) (Y.tau1.rho2.tau1E (e5 (Sum.inl 2)) (e5 (Sum.inr 1)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rho2.tau1.rhoE (Sum.inl 4) (Sum.inr 5) (fun P S hP hS => Y.tau1.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 4 1 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Y.tau1E (e5 (Sum.inr 4)) (e5 (Sum.inr 6)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 2) (Sum.inr 6) (fun P S hP hS => Y.tau1.rho2.twinGammaFull F hcf hcube hM.swap2 2 0 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))
    · exact (Y.rhoE (Sum.inr 5) (Sum.inl 4) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 1 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 5)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 5))).mpr (by decide)) hS))
    · exact (Y.tau1E (e5 (Sum.inr 5)) (e5 (Sum.inr 4)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 1) (Sum.inr 2) (Y.tau1.rho2.tau1E (e5 (Sum.inr 1)) (e5 (Sum.inl 2)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rho2.tau1.rhoE (Sum.inr 5) (Sum.inl 4) (fun P S hP hS => Y.tau1.rho2.tau1.rho2.twinGammaFull F hcf hcube hM.swap2.swap2 1 4 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))))
    · exact (Vega.TwinE.symm' (fun P S hP hS => Y.twin_a F P S hP (e5 (Sum.inr 6)) ((pres_iff_B 2 true true _).mpr (by decide)) ((vadj_iff_B 2 (e5 (Sum.inr 0)) (e5 (Sum.inr 6))).mpr (by decide)) hS))
    · exact (Y.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS))
    · exact (Y.tau1E (e5 (Sum.inr 6)) (e5 (Sum.inr 4)) ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (Y.tau1.rhoE (Sum.inr 6) (Sum.inr 2) (fun P S hP hS => Y.tau1.rho2.twinGammaFull F hcf hcube hM.swap2 0 2 ((pres_iff_B 2 true true _).mpr (by decide)) ((pres_iff_B 2 true true _).mpr (by decide)) (by unfold AA; omega) P S hP hS)))

  intro p s hp hs hv
  obtain ⟨a, rfl⟩ := e5_surj μ ν p hp
  obtain ⟨b, rfl⟩ := e5_surj μ ν s hs
  exact key a b hp hs hv

theorem twinClaim2_proof : TwinClaim2 := by
  intro V _ _ G _ hcf hmax hmin hNC hGF μ ν Y hM
  exact Y.twinProp2 hGF hcf hNC hmin hM

end Twin2

end E128H1V


/-! ## Final assembly: H1 from the attachment claim (the only remaining hypothesis). -/

theorem E128H1_noCubeClaim : E128H1V.NoCubeClaim := by
  intro V _ _ G _ hcf hmax hmin a b hab hn
  exact E128H1.no_cube G hcf hmax hmin a b hab hn

theorem E128H1_grFactsClaim : E128H1V.GrFactsClaim := by
  intro V _ _ G _ hcf hmax hmin
  exact
    { beaut := fun hY k q h0 h1 => E128H1.beautiful G hcf hmax hmin hY k q h0 h1
      l410 := fun hY q h3 h2 => E128H1.lemma410 G hcf hmax hmin hY q h3 h2
      l411 := fun hY q h0 h3 hn => E128H1.lemma411 G hcf hmax hmin hY q h0 h3 hn
      l412 := fun hY q h0 h3 => E128H1.lemma412 G hcf hmax hmin hY q h0 h3
      l413 := fun hY t1 t2 t3 a1 a2 a3 b1 b2 b3 c1 c2 c3 =>
        E128H1.lemma413 G hcf hmax hmin hY t1 t2 t3 a1 a2 a3 b1 b2 b3 c1 c2 c3
      l414 := fun hY A1 a1 a2 a3 T b1 b2 b3 q c1 c2 c3 t0 d1 d2 d3 =>
        E128H1.lemma414 G hcf hmax hmin hY A1 a1 a2 a3 T b1 b2 b3 q c1 c2 c3 t0 d1 d2 d3
      l46 := fun hY A B a1 a2 a3 b1 b2 b3 b4 hn =>
        E128H1.lemma46 G hcf hmax hmin hY A B a1 a2 a3 b1 b2 b3 b4 hn
      l47 := fun hY A B a1 a2 a3 a4 b1 b2 b3 b4 hn =>
        E128H1.lemma47 G hcf hmax hmin hY A B a1 a2 a3 a4 b1 b2 b3 b4 hn
      l45 := fun hY k u' h1 h4 hw c' hc2 hc3 =>
        E128H1.twin_c_u G hcf hmax hmin hY k u' h1 h4 hw c' hc2 hc3
      l48 := fun hY Uq Vq h3 h2 hVU hV0 =>
        E128H1.lemma48 G hcf hmax hmin hY Uq Vq h3 h2 hVU hV0 }

theorem E128H1_h1_of_attach (hAtt : E128H1V.AttachClaim) :
    OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 :=
  E128H1V.h1_of_claims hAtt E128H1V.diam2 E128H1_noCubeClaim E128H1_grFactsClaim

/-- H1 from the two remaining hypotheses: LPR Lemma 4.28 (twin) and 4.29 (attachment). -/
theorem E128H1_h1_of_twin_attach (hT : E128H1V.TwinClaim) (hA : E128H1V.AttachTwinClaim) :
    OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 :=
  E128H1_h1_of_attach (E128H1V.attachClaim_of hT hA)

/-- Bridge to PR #21105's H1 (Lemma 4.28). -/
theorem E128H1_prH1 (hT : E128H1V.TwinClaim) : E128H1V.PR_H1 :=
  E128H1V.prH1_of_twinClaim hT E128H1_noCubeClaim E128H1_grFactsClaim

/-- Bridge to PR #21105's H2 (Lemma 4.29). -/
theorem E128H1_prH2 (hT : E128H1V.TwinClaim) (hA : E128H1V.AttachTwinClaim) : E128H1V.PR_H2 :=
  E128H1V.prH2_of_claims hT hA E128H1_noCubeClaim E128H1_grFactsClaim

/-- H1 from the i = 2 twin lemma and the attachment lemma (i ≥ 3 twin lemma is proved). -/
theorem E128H1_h1_of_twin2_attach (h2 : E128H1V.TwinClaim2) (hA : E128H1V.AttachTwinClaim) :
    OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 :=
  E128H1_h1_of_twin_attach (E128H1V.twinClaim_of_2 h2) hA

/-- PR #21105's H1 from the i = 2 twin lemma. -/
theorem E128H1_prH1' (h2 : E128H1V.TwinClaim2) : E128H1V.PR_H1 :=
  E128H1_prH1 (E128H1V.twinClaim_of_2 h2)

/-- H1 from the attachment lemma alone (the twin lemma is now proved for all i). -/
theorem E128H1_h1_of_attach_only (hA : E128H1V.AttachTwinClaim) :
    OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 :=
  E128H1_h1_of_twin2_attach E128H1V.twinClaim2_proof hA

/-- PR #21105's H1, proved outright. -/
theorem E128H1_prH1_proof : E128H1V.PR_H1 := E128H1_prH1' E128H1V.twinClaim2_proof


/-- The step H1 itself: twin lemma (all i) and attachment lemma (all i), then Lemma 2.4. -/
theorem E128H1_h1_proof : OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 :=
  E128H1_h1_of_attach_only E128H1V.attachTwinClaim_proof

/-- PR #21105's H2 (Lemma 4.29), proved outright. -/
theorem E128H1_prH2_proof : E128H1V.PR_H2 :=
  E128H1_prH2 (E128H1V.twinClaim_of_2 E128H1V.twinClaim2_proof) E128H1V.attachTwinClaim_proof

/-- Proof of the step Erdos128.erdos_128.R2.H2.R2.H1: every graph in the class maps
homomorphically to the Vega graph (LPR Theorem 1.3(b) via Lemmas 4.28, 4.29, 2.4). -/
theorem OMA.solution : OMA.R_Erdos128_erdos_128_R2_H2_R2.H1 := E128H1_h1_proof

