import OMAReductions.R_Erdos128_erdos_128_R2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Reduction Erdos128.erdos_128.R2.H3.R1 of Erdos Problem 128 (R2.H3)

Elementary all-finite-n reduction of `OMA.R_Erdos128_erdos_128_R2.H3`
(zero flag algebras, zero regularity, zero blowup reductions):
1. Theorem 1 (`induce_edgeSet_gt_twoPiece`, `six_hundred_twenty_five_mul_edges_gt`):
   Two-piece quadratic potential `F(N) = min(Q1(u), Q2(u))` proving `58 * n^2 < 625 * e(G)`
   (e/n^2 > 0.0928, strictly improving `73/800 = 0.09125`).
2. Theorem 2 (`bipartite_del_gt`):
   Sharp elementary bipartite-deletion lower bound `37 * n^2 < 1250 * (e(G[A]) + e(G[A^c]))`
   for every `A : Set V` (D_2(G) > 0.0296 n^2, 98.7% of Petersen's 3/100).
3. Theorem 3 (`main`):
   Chromatic dichotomy splitting `R2.H3` into:
   - `H1`: minimal-order 3-colorable open core (`Even n`, `G.Connected`, `3*n^2 < 25*e(G)`,
     `n <= 25*d(v)`, `4*n <= 25*(d(u)+d(v)) + 3` for all `u != v`, `37*n^2 < 1250*D_2(G)`,
     and every color class satisfies `37*n < 250*|C_i|`).
   - `H2`: 4+-chromatic open core (`¬ G.Colorable 3`, `58*n^2 < 625*e(G)`, `37*n^2 < 1250*D_2(G)`).
-/

-- Reduction Erdos128.erdos_128.R2.H3.R1 of Erdos128.erdos_128.R2.H3
-- Credit: @iskamag

namespace OMA.R_Erdos128_erdos_128_R2_H3_R1

def H1 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    Even (Fintype.card V) →
    G.Colorable 3 →
    G.Connected →
    3 * Fintype.card V ^ 2 < 25 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    (∀ v : V, Fintype.card V ≤ 25 * (G.neighborSet v).ncard) →
    (∀ u v : V, u ≠ v →
      4 * Fintype.card V ≤ 25 * ((G.neighborSet u).ncard + (G.neighborSet v).ncard) + 3) →
    (∃ v : V, 3 * (G.neighborSet v).ncard ≤ Fintype.card V) →
    (∀ A : Set V, 37 * Fintype.card V ^ 2 <
      1250 * ((G.induce A).edgeSet.ncard + (G.induce Aᶜ).edgeSet.ncard)) →
    (∀ (c : G.Coloring (Fin 3)) (i : Fin 3),
      37 * Fintype.card V < 250 * {v : V | c v = i}.ncard) →
    (∃ a b c d : V, a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

def H2 : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    12 ≤ Fintype.card V →
    58 * Fintype.card V ^ 2 < 625 * G.edgeSet.ncard →
    500000 * G.edgeSet.ncard < 99999 * Fintype.card V ^ 2 →
    (∀ I : Set V, G.IsIndepSet I → 5 * I.ncard < 2 * Fintype.card V) →
    (∃ a b c d : V, a ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) →
    (∃ a b c d e : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d e ∧ G.Adj e a) →
    (∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ G.Adj a b ∧ G.Adj c d ∧
      ¬ G.Adj a c ∧ ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) →
    ¬ G.Colorable 3 →
    (∃ v : V, 3 * (G.neighborSet v).ncard ≤ Fintype.card V) →
    (∀ A : Set V, 37 * Fintype.card V ^ 2 <
      1250 * ((G.induce A).edgeSet.ncard + (G.induce Aᶜ).edgeSet.ncard)) →
    (∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) →
    ¬ G.CliqueFree 3

open Finset SimpleGraph OMA.R_Erdos128_erdos_128_R2

section TwoPiecePotential

/-- Pure rational linear separator for Piece 1 Subcase 1B2 (`10*u <= n`, `dbar <= u`, `p1 < 58/25 * dbar`). -/
lemma piece1_sep_B2
    {nq kq N u Mq : ℚ}
    (hnq_ge12 : 12 ≤ nq) (hkq_lo : 2 * kq ≤ nq) (hkq_hi : nq ≤ 2 * kq + 1)
    (hu_eq : u = N - kq) (hu_pos : 0 < u) (hu_le10 : 10 * u ≤ nq) (hN_pos : 0 < N)
    (hMQ1 : Mq ≤ nq ^ 2 / 50 + 2 * nq * u / 25 + 4 * u ^ 2 / 25)
    (hdu : 2 * Mq / N ≤ u)
    (hB1 : 2 * nq / 25 + 8 * u / 25 < 58 * (2 * Mq / N) / 25) :
    ∃ lam : ℚ, lam ≤ 0 ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ u →
        Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 ≤
          lam * (x - 2 * Mq / N)) ∧
      (∀ x : ℚ, u ≤ x →
        ((Mq - nq ^ 2 / 50) / u) * x - x ^ 2 ≤ lam * (x - 2 * Mq / N)) := by
  set Q1 : ℚ := nq ^ 2 / 50 + 2 * nq * u / 25 + 4 * u ^ 2 / 25
  set dbar : ℚ := 2 * Mq / N
  set p1 : ℚ := 2 * nq / 25 + 8 * u / 25
  set p2 : ℚ := (Mq - nq ^ 2 / 50) / u
  set lam : ℚ := p1 - 58 * dbar / 25
  set gM : ℚ := (Mq - Q1) + dbar * (p1 - 29 * dbar / 25)
  set dbarQ : ℚ := 2 * Q1 / N
  set gQ : ℚ := dbarQ * (p1 - 29 * dbarQ / 25)
  have hQ1_pos : 0 < Q1 := by dsimp only [Q1]; nlinarith only [hnq_ge12, hu_pos]
  have hdbarQ_pos : 0 < dbarQ := div_pos (by linarith only [hQ1_pos]) hN_pos
  have hg_mono : gM ≤ gQ := by
    have hdiff : gQ - gM = (Q1 - Mq) / N ^ 2 * (N ^ 2 + 2 * N * p1 - 116 * (Q1 + Mq) / 25) := by
      dsimp only [gM, gQ, dbar, dbarQ]; field_simp [hN_pos.ne']; ring
    set rq : ℚ := nq - 2 * kq
    have hrq1 : rq ≤ 1 := by dsimp only [rq]; linarith only [hkq_hi]
    have hN_r : N = (nq - rq) / 2 + u := by dsimp only [rq]; linarith only [hu_eq]
    have hexp : N ^ 2 + 2 * N * p1 - 232 * Q1 / 25 =
        361 * nq ^ 2 / 2500 + 461 * nq * u / 625 + 97 * u ^ 2 / 625 -
          rq * (29 * nq / 50 + 33 * u / 25) + rq ^ 2 / 4 := by
      rw [hN_r]; dsimp only [p1, Q1]; ring
    have hpos1 : 0 < N ^ 2 + 2 * N * p1 - 232 * Q1 / 25 := by
      have h1 : rq * (29 * nq / 50 + 33 * u / 25) ≤ 29 * nq / 50 + 33 * u / 25 := by
        nlinarith only [hrq1, hnq_ge12, hu_pos]
      have h2 : 0 < 361 * nq ^ 2 / 2500 - 29 * nq / 50 := by nlinarith only [hnq_ge12]
      have h3 : 0 < 461 * nq * u / 625 - 33 * u / 25 := by nlinarith only [hnq_ge12, hu_pos]
      have h4 : 0 ≤ 97 * u ^ 2 / 625 + rq ^ 2 / 4 :=
        add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
          (div_nonneg (sq_nonneg _) (by norm_num))
      linarith only [hexp, h1, h2, h3, h4]
    have hpos2 : 0 ≤ N ^ 2 + 2 * N * p1 - 116 * (Q1 + Mq) / 25 := by linarith only [hpos1, hMQ1]
    have hfac : 0 ≤ (Q1 - Mq) / N ^ 2 := div_nonneg (by linarith only [hMQ1]) (sq_nonneg N)
    have hge0 : 0 ≤ gQ - gM := by rw [hdiff]; exact mul_nonneg hfac hpos2
    linarith only [hge0]
  have hN_le : N ≤ 3 * nq / 5 := by linarith only [hu_eq, hkq_lo, hu_le10]
  have hgQ_le : gQ ≤ -(23 * dbarQ / (15625 * N)) * nq ^ 2 := by
    have h1 : N * p1 - 58 * Q1 / 25 =
        -(46 * nq ^ 2 + (nq - 10 * u) * (154 * nq - 160 * u)) / 31250 -
          (nq - 2 * kq) * p1 / 2 := by
      have hNku : N = kq + u := by linarith only [hu_eq]
      rw [hNku]; dsimp only [p1, Q1]; ring
    have hrem1 : 0 ≤ (nq - 10 * u) * (154 * nq - 160 * u) := by
      nlinarith only [hu_le10, hu_pos, hnq_ge12]
    have hrem2 : 0 ≤ (nq - 2 * kq) * p1 / 2 := by
      dsimp only [p1]; nlinarith only [hkq_lo, hnq_ge12, hu_pos]
    have hle_in : N * p1 - 58 * Q1 / 25 ≤ -23 * nq ^ 2 / 15625 := by
      linarith only [h1, hrem1, hrem2]
    have h2 : gQ = (dbarQ / N) * (N * p1 - 58 * Q1 / 25) := by
      dsimp only [gQ, dbarQ]; field_simp [hN_pos.ne']; ring
    have hfac : 0 ≤ dbarQ / N := div_nonneg hdbarQ_pos.le hN_pos.le
    have hmul := mul_le_mul_of_nonneg_left hle_in hfac
    have hR : (dbarQ / N) * (-23 * nq ^ 2 / 15625) = -(23 * dbarQ / (15625 * N)) * nq ^ 2 := by
      field_simp [hN_pos.ne']
    linarith only [h2, hmul, hR]
  have hgQ_neg : gQ < 0 := by
    have hpos : 0 < (23 * dbarQ / (15625 * N)) * nq ^ 2 :=
      mul_pos (div_pos (by linarith only [hdbarQ_pos]) (by linarith only [hN_pos])) (by nlinarith only [hnq_ge12])
    linarith only [hgQ_le, hpos]
  refine ⟨lam, by dsimp only [lam]; linarith only [hB1], ?_, ?_⟩
  · intro x _ _
    have hP1 : Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 -
        lam * (x - dbar) = -29 / 25 * (x - dbar) ^ 2 + gM := by
      dsimp only [Q1, p1, lam, gM]; ring
    have hsq0 : 0 ≤ 29 / 25 * (x - dbar) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith only [hP1, hsq0, hg_mono, hgQ_neg]
  · intro x hux
    set s : ℚ := p2 - 2 * u - lam
    have hP12_u : Mq - nq ^ 2 / 50 - u ^ 2 = p2 * u - u ^ 2 := by
      dsimp only [p2]; field_simp [hu_pos.ne']
    have hhu : p2 * u - u ^ 2 - lam * (u - dbar) = -29 / 25 * (u - dbar) ^ 2 + gM := by
      rw [← hP12_u]; dsimp only [Q1, p1, lam, gM]; ring
    have hhu_le : p2 * u - u ^ 2 - lam * (u - dbar) ≤ gQ := by
      have : 0 ≤ 29 / 25 * (u - dbar) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
      linarith only [hhu, this, hg_mono]
    have hh_eq : p2 * x - x ^ 2 - lam * (x - dbar) =
        (p2 * u - u ^ 2 - lam * (u - dbar)) + s * (x - u) - (x - u) ^ 2 := by
      dsimp only [s]; ring
    by_cases hs0 : s ≤ 0
    · have h1 : s * (x - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs0 (by linarith only [hux])
      have h2 : 0 ≤ (x - u) ^ 2 := sq_nonneg _
      linarith only [hh_eq, hhu_le, hgQ_neg, h1, h2]
    · push Not at hs0
      have hp2_le : p2 ≤ p1 - 4 * u / 25 := by
        have h1 : (Mq - nq ^ 2 / 50) / u ≤ (Q1 - nq ^ 2 / 50) / u :=
          div_le_div_of_nonneg_right (by linarith only [hMQ1]) hu_pos.le
        have h2 : (Q1 - nq ^ 2 / 50) / u = p1 - 4 * u / 25 := by
          dsimp only [Q1, p1]; field_simp [hu_pos.ne']; ring
        linarith only [h1, h2]
      have hs_le : s ≤ 4 * u / 25 := by dsimp only [s, lam]; linarith only [hp2_le, hdu]
      have hdbar_gt : 27 * u / 29 < dbar := by dsimp only [s, lam] at hs0; linarith only [hs0, hp2_le]
      have hdbar_le_Q : dbar ≤ dbarQ := div_le_div_of_nonneg_right (by linarith only [hMQ1]) hN_pos.le
      have hdQ_gt : 27 * u / 29 < dbarQ := lt_of_lt_of_le hdbar_gt hdbar_le_Q
      have hfrac_gt : 23 * (27 * u / 29) / (15625 * (3 * nq / 5)) < 23 * dbarQ / (15625 * N) := by
        have h1 : 23 * (27 * u / 29) / (15625 * (3 * nq / 5)) ≤ 23 * (27 * u / 29) / (15625 * N) :=
          div_le_div_of_nonneg_left (by linarith only [hu_pos]) (by linarith only [hN_pos]) (by linarith only [hN_le])
        have h2 : 23 * (27 * u / 29) / (15625 * N) < 23 * dbarQ / (15625 * N) :=
          div_lt_div_of_pos_right (by linarith only [hdQ_gt]) (by linarith only [hN_pos])
        linarith only [h1, h2]
      have hprod : 23 * (27 * u / 29) / (15625 * (3 * nq / 5)) * nq ^ 2 <
          23 * dbarQ / (15625 * N) * nq ^ 2 :=
        mul_lt_mul_of_pos_right hfrac_gt (by nlinarith only [hnq_ge12])
      have hsimp : 23 * (27 * u / 29) / (15625 * (3 * nq / 5)) * nq ^ 2 = 1035 * nq * u / 453125 := by
        field_simp [show nq ≠ 0 by linarith only [hnq_ge12]]; ring
      have hs2 : s ^ 2 / 4 ≤ 4 * u ^ 2 / 625 := by nlinarith only [hs0, hs_le]
      have hcomp : 4 * u ^ 2 / 625 < 1035 * nq * u / 453125 := by
        nlinarith only [hu_le10, hu_pos]
      have hquad : p2 * x - x ^ 2 - lam * (x - dbar) =
          (p2 * u - u ^ 2 - lam * (u - dbar)) + s ^ 2 / 4 - (x - u - s / 2) ^ 2 := by
        rw [hh_eq]; ring
      have hsq0 : 0 ≤ (x - u - s / 2) ^ 2 := sq_nonneg _
      linarith only [hquad, hhu_le, hgQ_le, hprod, hsimp, hs2, hcomp, hsq0]

/-- Pure rational SOS helper for Piece 2 Subcase 2B2 cross-piece bound (`P_{1,Q1}(x) <= lam*(x - dbar)` for ALL `x : ℚ`). -/
lemma piece2_cross_neg
    {nq kq N u Mq : ℚ}
    (hnq_ge12 : 12 ≤ nq) (hkq_lo : 2 * kq ≤ nq) (hkq_hi : nq ≤ 2 * kq + 1)
    (hu_eq : u = N - kq) (hu_gt10 : nq < 10 * u) (hN_pos : 0 < N)
    (hMQ2 : Mq ≤ 401 * nq ^ 2 / 20000 + 83 * nq * u / 1000 + u ^ 2 / 8) :
    ∀ x : ℚ,
      Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 ≤
        (83 * nq / 1000 + u / 4 - 9 * (2 * Mq / N) / 4) * (x - 2 * Mq / N) := by
  set Q1 : ℚ := nq ^ 2 / 50 + 2 * nq * u / 25 + 4 * u ^ 2 / 25
  set Q2 : ℚ := 401 * nq ^ 2 / 20000 + 83 * nq * u / 1000 + u ^ 2 / 8
  set p1 : ℚ := 83 * nq / 1000 + u / 4
  set b0 : ℚ := -3 * nq / 1000 + 7 * u / 100
  set dbar : ℚ := 2 * Mq / N
  set lam : ℚ := p1 - 9 * dbar / 4
  set Bc : ℚ := b0 + 9 * Mq / (2 * N)
  set Cc : ℚ := Mq - Q1 + 2 * p1 * Mq / N - 9 * Mq ^ 2 / N ^ 2
  have hu_pos : 0 < u := by linarith only [hnq_ge12, hu_gt10]
  have hH_mono : 116 * Cc / 25 + Bc ^ 2 ≤
      116 * (Q2 - Q1 + 2 * p1 * Q2 / N - 9 * Q2 ^ 2 / N ^ 2) / 25 + (b0 + 9 * Q2 / (2 * N)) ^ 2 := by
    set HM : ℚ := 116 * Cc / 25 + Bc ^ 2
    set HQ : ℚ := 116 * (Q2 - Q1 + 2 * p1 * Q2 / N - 9 * Q2 ^ 2 / N ^ 2) / 25 + (b0 + 9 * Q2 / (2 * N)) ^ 2
    have hdiff : HQ - HM = (Q2 - Mq) / N ^ 2 *
        (116 * N ^ 2 / 25 + 232 * N * p1 / 25 + 9 * N * b0 - 2151 * (Q2 + Mq) / 100) := by
      dsimp only [HQ, HM, Cc, Bc]; field_simp [hN_pos.ne']; ring
    set rq : ℚ := nq - 2 * kq
    have hrq1 : rq ≤ 1 := by dsimp only [rq]; linarith only [hkq_hi]
    have hN_r : N = (nq - rq) / 2 + u := by dsimp only [rq]; linarith only [hu_eq]
    have hexp : 116 * N ^ 2 / 25 + 232 * N * p1 / 25 + 9 * N * b0 - 4302 * Q2 / 100 =
        669069 * nq ^ 2 / 1000000 + 164379 * nq * u / 50000 + 177 * u ^ 2 / 80 -
          rq * (134581 * nq / 50000 + 1223 * u / 200) + 29 * rq ^ 2 / 25 := by
      rw [hN_r]; dsimp only [p1, b0, Q2]; ring
    have hpos1 : 0 < 116 * N ^ 2 / 25 + 232 * N * p1 / 25 + 9 * N * b0 - 4302 * Q2 / 100 := by
      have h1 : rq * (134581 * nq / 50000 + 1223 * u / 200) ≤ 134581 * nq / 50000 + 1223 * u / 200 := by
        nlinarith only [hrq1, hnq_ge12, hu_pos]
      have h2 : 0 < 669069 * nq ^ 2 / 1000000 - 134581 * nq / 50000 := by nlinarith only [hnq_ge12]
      have h3 : 0 < 164379 * nq * u / 50000 - 1223 * u / 200 := by nlinarith only [hnq_ge12, hu_pos]
      have h4 : 0 ≤ 177 * u ^ 2 / 80 + 29 * rq ^ 2 / 25 :=
        add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
          (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
      linarith only [hexp, h1, h2, h3, h4]
    have hpos2 : 0 ≤ 116 * N ^ 2 / 25 + 232 * N * p1 / 25 + 9 * N * b0 - 2151 * (Q2 + Mq) / 100 := by
      linarith only [hpos1, hMQ2]
    have hge0 : 0 ≤ HQ - HM := by
      rw [hdiff]; exact mul_nonneg (div_nonneg (by linarith only [hMQ2]) (sq_nonneg N)) hpos2
    linarith only [hge0]
  have hHQ_neg : 116 * (Q2 - Q1 + 2 * p1 * Q2 / N - 9 * Q2 ^ 2 / N ^ 2) / 25 +
      (b0 + 9 * Q2 / (2 * N)) ^ 2 < 0 := by
    set rq : ℚ := nq - 2 * kq
    set T : ℚ := 10 * u - nq
    have hrq0 : 0 ≤ rq := by dsimp only [rq]; linarith only [hkq_lo]
    have hrq1 : rq ≤ 1 := by dsimp only [rq]; linarith only [hkq_hi]
    have hT0 : 0 < T := by dsimp only [T]; linarith only [hu_gt10]
    have hN_r : N = (nq - rq) / 2 + (nq + T) / 10 := by dsimp only [rq, T]; linarith only [hu_eq]
    have hu_T : u = (nq + T) / 10 := by dsimp only [T]; ring
    set P0 : ℚ := 16051968 * nq ^ 4 - 25658880 * nq ^ 3 * T + 7949088 * nq ^ 2 * T ^ 2 +
        4725600 * nq * T ^ 3 + 499375 * T ^ 4
    set R1 : ℚ := (615022080 * nq ^ 3 - 160000 * rq * nq ^ 2) +
        (355763840 * nq ^ 2 + 18000000 * rq * nq) * T +
        (44676000 * nq + 15750000 * rq) * T ^ 2 + 1075000 * T ^ 3
    have hexp_sos : -(40000000000 * N ^ 2 *
        (116 * (Q2 - Q1 + 2 * p1 * Q2 / N - 9 * Q2 ^ 2 / N ^ 2) / 25 + (b0 + 9 * Q2 / (2 * N)) ^ 2)) =
        P0 + rq * R1 := by
      have hclear : N ^ 2 *
          (116 * (Q2 - Q1 + 2 * p1 * Q2 / N - 9 * Q2 ^ 2 / N ^ 2) / 25 + (b0 + 9 * Q2 / (2 * N)) ^ 2) =
          116 * (N ^ 2 * (Q2 - Q1) + 2 * N * p1 * Q2 - 9 * Q2 ^ 2) / 25 + (N * b0 + 9 * Q2 / 2) ^ 2 := by
        field_simp [hN_pos.ne']
      rw [mul_assoc, hclear]; dsimp only [Q1, Q2, p1, b0, P0, R1]; rw [hN_r, hu_T]; ring
    have hP0_pos : 0 < P0 := by
      have h4P0 : 4 * P0 =
          499375 * (2 * T ^ 2 + 9 * nq * T - 11 * nq ^ 2) ^ 2 +
          nq ^ 2 * (1900 * nq - 990 * T) ^ 2 +
          173497 * nq ^ 4 + 2730 * nq ^ 3 * T + 12339377 * nq ^ 2 * T ^ 2 + 924900 * nq * T ^ 3 := by
        dsimp only [P0]; ring
      have hsq1 : 0 ≤ 499375 * (2 * T ^ 2 + 9 * nq * T - 11 * nq ^ 2) ^ 2 := by positivity
      have hsq2 : 0 ≤ nq ^ 2 * (1900 * nq - 990 * T) ^ 2 := by positivity
      have hpos_t : 0 < 173497 * nq ^ 4 + 2730 * nq ^ 3 * T + 12339377 * nq ^ 2 * T ^ 2 + 924900 * nq * T ^ 3 := by
        positivity
      linarith only [h4P0, hsq1, hsq2, hpos_t]
    have hR1_nonneg : 0 ≤ R1 := by
      dsimp only [R1]
      have h0 : 0 ≤ 615022080 * nq ^ 3 - 160000 * rq * nq ^ 2 := by
        have : 160000 * rq * nq ^ 2 ≤ 160000 * nq ^ 2 := by nlinarith only [hrq1, hnq_ge12]
        nlinarith only [this, hnq_ge12]
      have h1 : 0 ≤ (355763840 * nq ^ 2 + 18000000 * rq * nq) * T := by positivity
      have h2 : 0 ≤ (44676000 * nq + 15750000 * rq) * T ^ 2 := by positivity
      have h3 : 0 ≤ 1075000 * T ^ 3 := by positivity
      linarith only [h0, h1, h2, h3]
    have hprod_neg : 40000000000 * N ^ 2 *
        (116 * (Q2 - Q1 + 2 * p1 * Q2 / N - 9 * Q2 ^ 2 / N ^ 2) / 25 + (b0 + 9 * Q2 / (2 * N)) ^ 2) < 0 := by
      have : 0 ≤ rq * R1 := mul_nonneg hrq0 hR1_nonneg
      linarith only [hexp_sos, hP0_pos, this]
    have hN2_pos : 0 < 40000000000 * N ^ 2 := by positivity
    nlinarith only [hprod_neg, hN2_pos]
  intro x
  have hcomp : Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 -
      lam * (x - dbar) = -29 / 25 * (x - 25 * Bc / 58) ^ 2 + 25 / 116 * (116 * Cc / 25 + Bc ^ 2) := by
    dsimp only [Q1, p1, b0, dbar, lam, Bc, Cc]; field_simp [hN_pos.ne']; ring
  have hsq0 : 0 ≤ 29 / 25 * (x - 25 * Bc / 58) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  linarith only [hcomp, hsq0, hH_mono, hHQ_neg]

/-- Pure rational linear separator for Piece 2 Subcase 2B2 (`10*u > n`, `p1_2 < 9/4 * dbar`). -/
lemma piece2_sep_B2
    {nq kq N u Mq : ℚ}
    (hnq_ge12 : 12 ≤ nq) (hkq_lo : 2 * kq ≤ nq) (hkq_hi : nq ≤ 2 * kq + 1)
    (hu_eq : u = N - kq) (hu_gt10 : nq < 10 * u) (hN_pos : 0 < N)
    (hMQ2 : Mq ≤ 401 * nq ^ 2 / 20000 + 83 * nq * u / 1000 + u ^ 2 / 8)
    (hdu : 2 * Mq / N ≤ u)
    (hB1 : 83 * nq / 1000 + u / 4 < 9 * (2 * Mq / N) / 4) :
    ∃ lam : ℚ, lam ≤ 0 ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ u →
        (10 * (u - x) ≤ nq →
          Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 ≤
            lam * (x - 2 * Mq / N)) ∧
        (nq < 10 * (u - x) →
          Mq - (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) - x ^ 2 ≤
            lam * (x - 2 * Mq / N))) ∧
      (∀ x : ℚ, u ≤ x →
        ((Mq - nq ^ 2 / 50) / u) * x - x ^ 2 ≤ lam * (x - 2 * Mq / N)) := by
  set Q2 : ℚ := 401 * nq ^ 2 / 20000 + 83 * nq * u / 1000 + u ^ 2 / 8
  set dbar : ℚ := 2 * Mq / N
  set p1 : ℚ := 83 * nq / 1000 + u / 4
  set p2 : ℚ := (Mq - nq ^ 2 / 50) / u
  set lam : ℚ := p1 - 9 * dbar / 4
  set gM : ℚ := (Mq - Q2) + dbar * (p1 - 9 * dbar / 8)
  set dbarQ : ℚ := 2 * Q2 / N
  set gQ : ℚ := dbarQ * (p1 - 9 * dbarQ / 8)
  have hu_pos : 0 < u := by linarith only [hnq_ge12, hu_gt10]
  have hQ2_pos : 0 < Q2 := by dsimp only [Q2]; nlinarith only [hnq_ge12, hu_pos]
  have hdbarQ_pos : 0 < dbarQ := div_pos (by linarith only [hQ2_pos]) hN_pos
  have hg_mono : gM ≤ gQ := by
    have hdiff : gQ - gM = (Q2 - Mq) / N ^ 2 * (N ^ 2 + 2 * N * p1 - 9 * (Q2 + Mq) / 2) := by
      dsimp only [gM, gQ, dbar, dbarQ]; field_simp [hN_pos.ne']; ring
    set rq : ℚ := nq - 2 * kq
    have hrq1 : rq ≤ 1 := by dsimp only [rq]; linarith only [hkq_hi]
    have hN_r : N = (nq - rq) / 2 + u := by dsimp only [rq]; linarith only [hu_eq]
    have hexp : N ^ 2 + 2 * N * p1 - 9 * Q2 =
        3051 * nq ^ 2 / 20000 + 13380 * nq * u / 20000 + 7500 * u ^ 2 / 20000 -
          rq * (583 * nq / 1000 + 1250 * u / 1000) + rq ^ 2 / 4 := by
      rw [hN_r]; dsimp only [p1, Q2]; ring
    have hpos1 : 0 < N ^ 2 + 2 * N * p1 - 9 * Q2 := by
      have h1 : rq * (583 * nq / 1000 + 1250 * u / 1000) ≤ 583 * nq / 1000 + 1250 * u / 1000 := by
        nlinarith only [hrq1, hnq_ge12, hu_pos]
      have h2 : 0 < 3051 * nq ^ 2 / 20000 - 583 * nq / 1000 := by nlinarith only [hnq_ge12]
      have h3 : 0 < 13380 * nq * u / 20000 - 1250 * u / 1000 := by nlinarith only [hnq_ge12, hu_pos]
      have h4 : 0 ≤ 7500 * u ^ 2 / 20000 + rq ^ 2 / 4 :=
        add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
          (div_nonneg (sq_nonneg _) (by norm_num))
      linarith only [hexp, h1, h2, h3, h4]
    have hpos2 : 0 ≤ N ^ 2 + 2 * N * p1 - 9 * (Q2 + Mq) / 2 := by linarith only [hpos1, hMQ2]
    have hge0 : 0 ≤ gQ - gM := by
      rw [hdiff]; exact mul_nonneg (div_nonneg (by linarith only [hMQ2]) (sq_nonneg N)) hpos2
    linarith only [hge0]
  have hgQ_le : gQ ≤ -(dbarQ / (32 * N)) * (u - 17 * nq / 50) ^ 2 := by
    have h1 : N * p1 - 9 * Q2 / 4 = -(u - 17 * nq / 50) ^ 2 / 32 - (nq - 2 * kq) * p1 / 2 := by
      have hNku : N = kq + u := by linarith only [hu_eq]
      rw [hNku]; dsimp only [p1, Q2]; ring
    have hrem : 0 ≤ (nq - 2 * kq) * p1 / 2 := by dsimp only [p1]; nlinarith only [hkq_lo, hnq_ge12, hu_pos]
    have h2 : gQ = (dbarQ / N) * (N * p1 - 9 * Q2 / 4) := by
      dsimp only [gQ, dbarQ]; field_simp [hN_pos.ne']; ring
    have hmul := mul_le_mul_of_nonneg_left (show N * p1 - 9 * Q2 / 4 ≤ -(u - 17 * nq / 50) ^ 2 / 32 by
      linarith only [h1, hrem]) (div_nonneg hdbarQ_pos.le hN_pos.le)
    have hR : (dbarQ / N) * (-(u - 17 * nq / 50) ^ 2 / 32) = -(dbarQ / (32 * N)) * (u - 17 * nq / 50) ^ 2 := by
      field_simp [hN_pos.ne']
    linarith only [h2, hmul, hR]
  have hgQ_nonpos : gQ ≤ 0 := by
    have : 0 ≤ dbarQ / (32 * N) * (u - 17 * nq / 50) ^ 2 :=
      mul_nonneg (div_nonneg hdbarQ_pos.le (by linarith only [hN_pos])) (sq_nonneg _)
    linarith only [hgQ_le, this]
  have hcross := piece2_cross_neg hnq_ge12 hkq_lo hkq_hi hu_eq hu_gt10 hN_pos hMQ2
  refine ⟨lam, by dsimp only [lam]; linarith only [hB1], ?_, ?_⟩
  · intro x _ _
    refine ⟨fun _ => hcross x, fun _ => ?_⟩
    have hP2 : Mq - (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) - x ^ 2 -
        lam * (x - dbar) = -9 / 8 * (x - dbar) ^ 2 + gM := by
      dsimp only [Q2, p1, lam, gM]; ring
    have hsq0 : 0 ≤ 9 / 8 * (x - dbar) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
    linarith only [hP2, hsq0, hg_mono, hgQ_nonpos]
  · intro x hux
    set s : ℚ := p2 - 2 * u - lam
    have hP2_u_eq : p2 * u - u ^ 2 = Mq - nq ^ 2 / 50 - u ^ 2 := by
      dsimp only [p2]; field_simp [hu_pos.ne']
    have hhu_nonpos : p2 * u - u ^ 2 - lam * (u - dbar) ≤ 0 := by
      have hc := hcross u
      have hsimp : Mq - (nq ^ 2 / 50 + 2 * nq * (u - u) / 25 + 4 * (u - u) ^ 2 / 25) - u ^ 2 =
          p2 * u - u ^ 2 := by rw [hP2_u_eq]; ring
      dsimp only [lam, p1, dbar]
      linarith only [hc, hsimp]
    have hhu_gQ : p2 * u - u ^ 2 - lam * (u - dbar) ≤ gQ + nq ^ 2 / 20000 := by
      have hid : p2 * u - u ^ 2 - lam * (u - dbar) =
          -9 / 8 * (u - dbar) ^ 2 + gM + nq ^ 2 / 20000 := by
        rw [hP2_u_eq]; dsimp only [Q2, p1, lam, gM]; ring
      have hsq0 : 0 ≤ 9 / 8 * (u - dbar) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
      linarith only [hid, hsq0, hg_mono]
    have hh_eq : p2 * x - x ^ 2 - lam * (x - dbar) =
        (p2 * u - u ^ 2 - lam * (u - dbar)) + s * (x - u) - (x - u) ^ 2 := by
      dsimp only [s]; ring
    by_cases hs0 : s ≤ 0
    · have h1 : s * (x - u) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs0 (by linarith only [hux])
      have h2 : 0 ≤ (x - u) ^ 2 := sq_nonneg _
      linarith only [hh_eq, hhu_nonpos, h1, h2]
    · push Not at hs0
      have hp2_lt : p2 < p1 - 3 * u / 25 := by
        have h1 : (Mq - nq ^ 2 / 50) / u ≤ (Q2 - nq ^ 2 / 50) / u :=
          div_le_div_of_nonneg_right (by linarith only [hMQ2]) hu_pos.le
        have h2 : (Q2 - nq ^ 2 / 50) / u = nq ^ 2 / (20000 * u) + 83 * nq / 1000 + u / 8 := by
          dsimp only [Q2]; field_simp [hu_pos.ne']; ring
        have h3 : nq ^ 2 / (20000 * u) < u / 200 := by
          have hmul : nq ^ 2 < 100 * u ^ 2 := by nlinarith only [hu_gt10, hnq_ge12]
          have hdiv := div_lt_div_of_pos_right hmul (show (0 : ℚ) < 20000 * u by linarith only [hu_pos])
          have hR : 100 * u ^ 2 / (20000 * u) = u / 200 := by field_simp [hu_pos.ne']; ring
          linarith only [hdiv, hR]
        dsimp only [p1]; linarith only [h1, h2, h3]
      have hs_lt : s < 13 * u / 100 := by dsimp only [s, lam]; linarith only [hp2_lt, hdu]
      have hdbar_gt : 212 * u < 225 * dbar := by dsimp only [s, lam] at hs0; linarith only [hs0, hp2_lt]
      have hdbar_le_Q : dbar ≤ dbarQ := div_le_div_of_nonneg_right (by linarith only [hMQ2]) hN_pos.le
      have h212_lt : 212 * N * u < 450 * Q2 := by
        have h1 : 212 * u < 225 * (2 * Q2 / N) := by linarith only [hdbar_gt, hdbar_le_Q]
        have h2 := mul_lt_mul_of_pos_left h1 hN_pos
        have hR : N * (225 * (2 * Q2 / N)) = 450 * Q2 := by field_simp [hN_pos.ne']; ring
        linarith only [h2, hR]
      have hu_lt_325 : 25 * u < 3 * nq := by
        by_contra hge
        push Not at hge
        set t : ℚ := u - 3 * nq / 25
        have ht0 : 0 ≤ t := by dsimp only [t]; linarith only [hge]
        have h24k : 11 * nq ≤ 24 * kq := by linarith only [hnq_ge12, hkq_hi]
        have hN_lo : 11 * nq / 24 + u ≤ N := by linarith only [hu_eq, h24k]
        have hge1 : 212 * (11 * nq / 24 + u) * u - 450 * Q2 ≤ 212 * N * u - 450 * Q2 := by
          nlinarith only [hN_lo, hu_pos]
        have hexp : 212 * (11 * nq / 24 + u) * u - 450 * Q2 =
            3983 * nq ^ 2 / 10000 + 29159 * nq * t / 300 + 623 * t ^ 2 / 4 := by
          have hu_t : u = 3 * nq / 25 + t := by dsimp only [t]; ring
          dsimp only [Q2]; rw [hu_t]; ring
        have hpos : 0 < 3983 * nq ^ 2 / 10000 + 29159 * nq * t / 300 + 623 * t ^ 2 / 4 := by
          nlinarith only [hnq_ge12, ht0]
        linarith only [h212_lt, hge1, hexp, hpos]
      have hN_lt : N < 31 * nq / 50 := by linarith only [hu_eq, hkq_lo, hu_lt_325]
      have hdiff_gt : 11 * nq / 50 < 17 * nq / 50 - u := by linarith only [hu_lt_325]
      have hsq_gt : (11 * nq / 50) ^ 2 < (u - 17 * nq / 50) ^ 2 := by
        nlinarith only [hdiff_gt, hnq_ge12]
      have hdQ_gt : 212 * u / 225 < dbarQ := by linarith only [hdbar_gt, hdbar_le_Q]
      have hfrac_gt : 212 * u / (225 * 32 * (31 * nq / 50)) < dbarQ / (32 * N) := by
        have h1 : 212 * u / (225 * 32 * (31 * nq / 50)) < 212 * u / (225 * 32 * N) :=
          div_lt_div_of_pos_left (by linarith only [hu_pos]) (by linarith only [hN_pos]) (by linarith only [hN_lt])
        have h2 : 212 * u / (225 * 32 * N) < dbarQ / (32 * N) := by
          have hL : 212 * u / (225 * 32 * N) = (212 * u / 225) / (32 * N) := by ring
          rw [hL]; exact div_lt_div_of_pos_right hdQ_gt (by linarith only [hN_pos])
        linarith only [h1, h2]
      have hprod : 212 * u / (225 * 32 * (31 * nq / 50)) * (11 * nq / 50) ^ 2 <
          dbarQ / (32 * N) * (u - 17 * nq / 50) ^ 2 := by
        have hA : 0 < 212 * u / (225 * 32 * (31 * nq / 50)) :=
          div_pos (by linarith only [hu_pos]) (by linarith only [hnq_ge12])
        have hB : 0 < (11 * nq / 50) ^ 2 := sq_pos_of_pos (by linarith only [hnq_ge12])
        nlinarith only [hfrac_gt, hsq_gt, hA, hB]
      have hsimp : 212 * u / (225 * 32 * (31 * nq / 50)) * (11 * nq / 50) ^ 2 = 6413 * nq * u / 2790000 := by
        field_simp [show nq ≠ 0 by linarith only [hnq_ge12]]; ring
      have htail : nq ^ 2 / 20000 + s ^ 2 / 4 < 6413 * nq * u / 2790000 := by
        have h1 : nq ^ 2 / 20000 < nq * u / 2000 := by nlinarith only [hu_gt10, hnq_ge12]
        have h2 : s ^ 2 / 4 < 169 * u ^ 2 / 40000 := by nlinarith only [hs0, hs_lt]
        have h3 : 169 * u ^ 2 / 40000 < 507 * nq * u / 1000000 := by nlinarith only [hu_lt_325, hu_pos]
        have h4 : nq * u / 2000 + 507 * nq * u / 1000000 < 6413 * nq * u / 2790000 := by
          nlinarith only [hnq_ge12, hu_pos]
        linarith only [h1, h2, h3, h4]
      have hquad : p2 * x - x ^ 2 - lam * (x - dbar) =
          (p2 * u - u ^ 2 - lam * (u - dbar)) + s ^ 2 / 4 - (x - u - s / 2) ^ 2 := by
        rw [hh_eq]; ring
      have hsq0 : 0 ≤ (x - u - s / 2) ^ 2 := sq_nonneg _
      linarith only [hquad, hhu_gQ, hgQ_le, hprod, hsimp, htail, hsq0]

/-- Pure rational step contradiction for the 2-piece quadratic potential `F(N) = min(Q1(u), Q2(u))`. -/
lemma two_piece_step_contra
    {W : Type} [DecidableEq W] (S : Finset W)
    {n k M : ℕ} (hn12 : 12 ≤ n) (hk_lo : 2 * k ≤ n) (hk_hi : n ≤ 2 * k + 1)
    (hN_gt : k < #S) (hN_le : #S ≤ n)
    (hM_gt : n ^ 2 < 50 * M)
    (hM_le : (M : ℚ) ≤ if 10 * (#S - k) ≤ n
      then (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((#S - k : ℕ) : ℚ) / 25 + 4 * (((#S - k : ℕ) : ℚ) ^ 2) / 25
      else 401 * (n : ℚ) ^ 2 / 20000 + 83 * (n : ℚ) * ((#S - k : ℕ) : ℚ) / 1000 + (((#S - k : ℕ) : ℚ) ^ 2) / 8)
    (d Sv : W → ℕ)
    (hsum_d : ∑ v ∈ S, d v = 2 * M)
    (hsum_Sv : ∑ v ∈ S, Sv v = ∑ v ∈ S, (d v) ^ 2)
    (hd0 : ∀ v ∈ S, d v = 0 → Sv v = 0)
    (hb1 : ∀ v ∈ S, 1 ≤ d v → d v ≤ #S - k →
      ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
        (M : ℚ) - (if 10 * (#S - d v - k) ≤ n
          then (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((#S - d v - k : ℕ) : ℚ) / 25 +
            4 * (((#S - d v - k : ℕ) : ℚ) ^ 2) / 25
          else 401 * (n : ℚ) ^ 2 / 20000 + 83 * (n : ℚ) * ((#S - d v - k : ℕ) : ℚ) / 1000 +
            (((#S - d v - k : ℕ) : ℚ) ^ 2) / 8) - (d v : ℚ) ^ 2)
    (hb2 : ∀ v ∈ S, #S - k < d v →
      ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
        (((M : ℚ) - (n : ℚ) ^ 2 / 50) / ((#S - k : ℕ) : ℚ)) * (d v : ℚ) - (d v : ℚ) ^ 2) :
    False := by
  set N : ℚ := (#S : ℚ)
  set nq : ℚ := (n : ℚ)
  set kq : ℚ := (k : ℚ)
  set u : ℚ := ((#S - k : ℕ) : ℚ)
  set Mq : ℚ := (M : ℚ)
  have hu_eq : u = N - kq := by
    have h : (#S - k : ℕ) + k = #S := Nat.sub_add_cancel (by omega)
    have hz : ((#S - k : ℕ) : ℚ) + (k : ℚ) = (#S : ℚ) := by exact_mod_cast h
    linarith
  have hu_pos : (0 : ℚ) < u := by dsimp only [u]; exact Nat.cast_pos.mpr (by omega)
  have hN_pos : (0 : ℚ) < N := by dsimp only [N]; exact Nat.cast_pos.mpr (by omega)
  have hnq_ge12 : (12 : ℚ) ≤ nq := by dsimp only [nq]; exact_mod_cast hn12
  have hkq_lo : 2 * kq ≤ nq := by dsimp only [kq, nq]; exact_mod_cast hk_lo
  have hkq_hi : nq ≤ 2 * kq + 1 := by dsimp only [kq, nq]; exact_mod_cast hk_hi
  have hM_gt_q : nq ^ 2 / 50 < Mq := by
    have h1 : nq ^ 2 < 50 * Mq := by dsimp only [nq, Mq]; exact_mod_cast hM_gt
    linarith
  have hM_pos : (0 : ℚ) < Mq := by nlinarith only [hM_gt_q, hnq_ge12]
  set dbar : ℚ := 2 * Mq / N
  set p2 : ℚ := (Mq - nq ^ 2 / 50) / u
  have hdbar_pos : 0 < dbar := div_pos (by linarith) hN_pos
  -- Exhibit linear separator lam <= 0 for both pieces
  have hsep : ∃ lam : ℚ, lam ≤ 0 ∧
      (∀ x : ℚ, 0 ≤ x → x ≤ u →
        (10 * (u - x) ≤ nq →
          Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 ≤
            lam * (x - dbar)) ∧
        (nq < 10 * (u - x) →
          Mq - (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) - x ^ 2 ≤
            lam * (x - dbar))) ∧
      (∀ x : ℚ, u ≤ x → p2 * x - x ^ 2 ≤ lam * (x - dbar)) := by
    by_cases hpiece : 10 * (#S - k) ≤ n
    · -- Branch 1: Piece 1 (10 * u <= n)
      rw [if_pos hpiece] at hM_le
      have hu_le10 : 10 * u ≤ nq := by dsimp only [u, nq]; exact_mod_cast hpiece
      set Q1 : ℚ := nq ^ 2 / 50 + 2 * nq * u / 25 + 4 * u ^ 2 / 25
      set p1 : ℚ := 2 * nq / 25 + 8 * u / 25
      have hu_lt_k : u < kq := by linarith only [hu_le10, hkq_hi, hnq_ge12]
      have hslack : 4 * u ^ 2 / (25 * N) ≤ dbar - p2 := by
        have hNu : N * u * (dbar - p2) = N * (nq ^ 2 / 50) - (kq - u) * Mq := by
          dsimp only [dbar, p2]
          have hNku : N = kq + u := by linarith
          field_simp [hN_pos.ne', hu_pos.ne']; rw [hNku]; ring
        have hgeF : N * (nq ^ 2 / 50) - (kq - u) * Q1 ≤ N * (nq ^ 2 / 50) - (kq - u) * Mq := by
          have : 0 ≤ kq - u := by linarith
          nlinarith only [this, hM_le]
        have hexp : N * (nq ^ 2 / 50) - (kq - u) * Q1 =
            4 * u ^ 3 / 25 + (nq - 2 * kq) * (2 * nq * u / 25 + 4 * u ^ 2 / 25) / 2 := by
          have hNku : N = kq + u := by linarith
          dsimp only [Q1]; rw [hNku]; ring
        have hrem : 0 ≤ (nq - 2 * kq) * (2 * nq * u / 25 + 4 * u ^ 2 / 25) / 2 :=
          div_nonneg (mul_nonneg (by linarith only [hkq_lo]) (by nlinarith only [hnq_ge12, hu_pos])) (by norm_num)
        have hNu_ge : 4 * u ^ 3 / 25 ≤ N * u * (dbar - p2) := by linarith only [hNu, hgeF, hexp, hrem]
        have hL : (N * u) * (4 * u ^ 2 / (25 * N)) = 4 * u ^ 3 / 25 := by field_simp [hN_pos.ne']
        have hNu_pos : 0 < N * u := mul_pos hN_pos hu_pos
        exact le_of_mul_le_mul_left (by linarith only [hNu_ge, hL]) hNu_pos
      have hp2_lt_dbar : p2 < dbar := by
        have hpos : 0 < 4 * u ^ 2 / (25 * N) := div_pos (by nlinarith only [hu_pos]) (by linarith only [hN_pos])
        linarith only [hslack, hpos]
      by_cases hdu : u < dbar
      · -- Subcase 1A: dbar > u
        refine ⟨p2 - 2 * dbar, by linarith only [hp2_lt_dbar, hdbar_pos], ?_, ?_⟩
        · intro x hx0 hxu
          refine ⟨fun _ => ?_, fun hbad => by linarith only [hx0, hu_le10, hbad]⟩
          have hP12 : (Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2) -
              (p2 * x - x ^ 2) = (u - x) * (4 * x / 25 - (Q1 - Mq) / u) := by
            dsimp only [Q1, p2]; field_simp [hu_pos.ne']; ring
          have hP12_le : (Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2) -
              (p2 * x - x ^ 2) ≤ 4 * x * (u - x) / 25 := by
            have h1 : 0 ≤ (u - x) * ((Q1 - Mq) / u) :=
              mul_nonneg (by linarith only [hxu]) (div_nonneg (by linarith only [hM_le]) hu_pos.le)
            nlinarith only [hP12, h1]
          have hP2_eq : p2 * x - x ^ 2 - (p2 - 2 * dbar) * (x - dbar) = -(x - dbar) ^ 2 - dbar * (dbar - p2) := by ring
          have hsq : -(x - dbar) ^ 2 + 4 * x * (u - x) / 25 =
              -29 / 25 * (x - (25 * dbar + 2 * u) / 29) ^ 2 + (4 * u ^ 2 - 100 * dbar * (dbar - u)) / 725 := by ring
          have hsq_le : -(x - dbar) ^ 2 + 4 * x * (u - x) / 25 ≤ 4 * u ^ 2 / 725 := by
            have h1 : 0 ≤ 29 / 25 * (x - (25 * dbar + 2 * u) / 29) ^ 2 := by positivity
            have h2 : 0 ≤ 100 * dbar * (dbar - u) := by nlinarith only [hdbar_pos, hdu]
            linarith only [hsq, h1, h2]
          have hN_le35 : N ≤ 3 * nq / 5 := by linarith only [hu_eq, hkq_lo, hu_le10]
          have hdbar_lb : nq ^ 2 / (25 * N) < dbar := by
            dsimp only [dbar]
            have hdiv := div_lt_div_of_pos_right (show nq ^ 2 / 25 < 2 * Mq by linarith only [hM_gt_q]) hN_pos
            have hL : (nq ^ 2 / 25) / N = nq ^ 2 / (25 * N) := by ring
            linarith only [hdiv, hL]
          have hprod : 4 * nq ^ 2 * u ^ 2 / (625 * N ^ 2) < dbar * (dbar - p2) := by
            have hA : 0 < nq ^ 2 / (25 * N) := div_pos (by nlinarith only [hnq_ge12]) (by linarith only [hN_pos])
            have hB : 0 < 4 * u ^ 2 / (25 * N) := div_pos (by nlinarith only [hu_pos]) (by linarith only [hN_pos])
            have h1 : (nq ^ 2 / (25 * N)) * (4 * u ^ 2 / (25 * N)) < dbar * (dbar - p2) := by
              nlinarith only [hdbar_lb, hslack, hA, hB]
            have hL : (nq ^ 2 / (25 * N)) * (4 * u ^ 2 / (25 * N)) = 4 * nq ^ 2 * u ^ 2 / (625 * N ^ 2) := by ring
            linarith only [h1, hL]
          have hcomp : 4 * u ^ 2 / 725 ≤ 4 * nq ^ 2 * u ^ 2 / (625 * N ^ 2) := by
            have hN2 : 25 * N ^ 2 ≤ 9 * nq ^ 2 := by nlinarith only [hN_le35, hN_pos, hnq_ge12]
            have hnum : 4 * u ^ 2 * (625 * N ^ 2) ≤ 725 * (4 * nq ^ 2 * u ^ 2) := by
              nlinarith only [hN2, hu_pos]
            have hden : (0 : ℚ) < 625 * N ^ 2 := by positivity
            have hdiv := div_le_div_of_nonneg_right hnum (show (0 : ℚ) ≤ 725 * (625 * N ^ 2) by positivity)
            have hL : 4 * u ^ 2 * (625 * N ^ 2) / (725 * (625 * N ^ 2)) = 4 * u ^ 2 / 725 := by
              field_simp [hN_pos.ne']
            have hR : 725 * (4 * nq ^ 2 * u ^ 2) / (725 * (625 * N ^ 2)) = 4 * nq ^ 2 * u ^ 2 / (625 * N ^ 2) := by
              field_simp [hN_pos.ne']
            linarith only [hdiv, hL, hR]
          linarith only [hP12_le, hP2_eq, hsq_le, hprod, hcomp]
        · intro x _
          have hP2_eq : p2 * x - x ^ 2 - (p2 - 2 * dbar) * (x - dbar) = -(x - dbar) ^ 2 - dbar * (dbar - p2) := by ring
          have h1 : 0 ≤ (x - dbar) ^ 2 := sq_nonneg _
          have h2 : 0 ≤ dbar * (dbar - p2) := by nlinarith only [hdbar_pos, hp2_lt_dbar]
          linarith only [hP2_eq, h1, h2]
      · push Not at hdu
        by_cases hB1 : 58 * dbar / 25 ≤ p1
        · -- Subcase 1B1: lam = 0
          refine ⟨0, le_refl 0, ?_, ?_⟩
          · intro x hx0 _
            refine ⟨fun _ => ?_, fun hbad => by linarith only [hx0, hu_le10, hbad]⟩
            have hM_b : Mq ≤ 25 * N * p1 / 116 := by
              dsimp only [dbar] at hB1
              have h1 := mul_le_mul_of_nonneg_left hB1 hN_pos.le
              have hL : N * (58 * (2 * Mq / N) / 25) = 116 * Mq / 25 := by field_simp [hN_pos.ne']; ring
              linarith only [h1, hL]
            have hN_half : N ≤ nq / 2 + u := by linarith only [hu_eq, hkq_lo]
            have hp1_pos : 0 < p1 := by dsimp only [p1]; linarith only [hnq_ge12, hu_pos]
            have hsq : Mq - (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) - x ^ 2 =
                -29 / 25 * (x - 25 * p1 / 58) ^ 2 + (Mq - Q1) + 25 * p1 ^ 2 / 116 := by
              dsimp only [Q1, p1]; ring
            have hsq0 : 0 ≤ 29 / 25 * (x - 25 * p1 / 58) ^ 2 := by positivity
            have hcomp : 25 * p1 * (nq / 2 + u + p1) / 116 - Q1 =
                -(58 * nq ^ 2 + 100 * nq * u + 400 * u ^ 2) / 5800 := by
              dsimp only [p1, Q1]; ring
            have hneg : 25 * p1 * (nq / 2 + u + p1) / 116 - Q1 ≤ 0 := by
              have : 0 ≤ (58 * nq ^ 2 + 100 * nq * u + 400 * u ^ 2) / 5800 := by positivity
              linarith only [hcomp, this]
            have hstep : Mq - Q1 + 25 * p1 ^ 2 / 116 ≤ 25 * p1 * (nq / 2 + u + p1) / 116 - Q1 := by
              have : 25 * N * p1 / 116 ≤ 25 * (nq / 2 + u) * p1 / 116 := by nlinarith only [hN_half, hp1_pos]
              linarith only [hM_b, this]
            simp only [zero_mul]
            linarith only [hsq, hsq0, hneg, hstep]
          · intro x hux
            simp only [zero_mul]
            have h1 : p2 * x - x ^ 2 = x * (p2 - x) := by ring
            have h2 : p2 - x ≤ 0 := by linarith only [hp2_lt_dbar, hdu, hux]
            have h3 : 0 ≤ x := by linarith only [hu_pos, hux]
            nlinarith only [h1, h2, h3]
        · push Not at hB1
          obtain ⟨lam, hlam, h1, h2⟩ := piece1_sep_B2 hnq_ge12 hkq_lo hkq_hi hu_eq hu_pos hu_le10 hN_pos hM_le hdu hB1
          exact ⟨lam, hlam, fun x hx0 hxu => ⟨fun _ => h1 x hx0 hxu, fun hbad => by linarith only [hx0, hu_le10, hbad]⟩, h2⟩
    · -- Branch 2: Piece 2 (10 * u > n)
      rw [if_neg hpiece] at hM_le
      have hu_gt10 : nq < 10 * u := by dsimp only [u, nq]; exact_mod_cast (show n < 10 * (#S - k) by omega)
      have hu_ge10p1 : nq + 1 ≤ 10 * u := by dsimp only [u, nq]; exact_mod_cast (show n + 1 ≤ 10 * (#S - k) by omega)
      set Q2 : ℚ := 401 * nq ^ 2 / 20000 + 83 * nq * u / 1000 + u ^ 2 / 8
      set p1 : ℚ := 83 * nq / 1000 + u / 4
      -- Step 2.0: dbar <= u unconditionally in Piece 2
      have hdu : dbar ≤ u := by
        set rq : ℚ := nq - 2 * kq
        set T : ℚ := 10 * u - nq
        have hrq1 : rq ≤ 1 := by dsimp only [rq]; linarith only [hkq_hi]
        have hT1 : 1 ≤ T := by dsimp only [T]; linarith only [hu_ge10p1]
        have hN_r : N = (nq - rq) / 2 + (nq + T) / 10 := by dsimp only [rq, T]; linarith only [hu_eq]
        have hu_T : u = (nq + T) / 10 := by dsimp only [T]; ring
        have hexp : 20000 * (u * N - 2 * Q2) = 16 * nq ^ 2 + 968 * nq * T + 150 * T ^ 2 - 1000 * rq * (nq + T) := by
          dsimp only [Q2]; rw [hN_r, hu_T]; ring
        have hpos : 0 < 20000 * (u * N - 2 * Q2) := by
          have hr_b : 1000 * rq * (nq + T) ≤ 1000 * (nq + T) := by nlinarith only [hrq1, hnq_ge12, hT1]
          have h1 : 16 * nq ^ 2 + 968 * nq * T + 150 * T ^ 2 - 1000 * (nq + T) =
              16 * nq * (nq - 12) + (968 * T - 808) * (nq - 12) + 150 * T ^ 2 + 10616 * T - 9696 := by ring
          have h2 : 0 ≤ 16 * nq * (nq - 12) := by nlinarith only [hnq_ge12]
          have h3 : 0 ≤ (968 * T - 808) * (nq - 12) := by nlinarith only [hT1, hnq_ge12]
          have h4 : 0 < 150 * T ^ 2 + 10616 * T - 9696 := by nlinarith only [hT1]
          linarith only [hexp, hr_b, h1, h2, h3, h4]
        have h2M : 2 * Mq ≤ u * N := by linarith only [hM_le, hpos]
        dsimp only [dbar]
        exact (div_le_iff₀ hN_pos).mpr h2M
      -- Positivity of dbar - p2 in Piece 2
      have hp2_lt_dbar : p2 < dbar := by
        have hNu : N * u * (dbar - p2) = N * (nq ^ 2 / 50) - (kq - u) * Mq := by
          dsimp only [dbar, p2]
          have hNku : N = kq + u := by linarith
          field_simp [hN_pos.ne', hu_pos.ne']; rw [hNku]; ring
        have hNu_pos : 0 < N * u := mul_pos hN_pos hu_pos
        have hrhs_pos : 0 < N * (nq ^ 2 / 50) - (kq - u) * Mq := by
          by_cases huk : u < kq
          · have hgeF : N * (nq ^ 2 / 50) - (kq - u) * Q2 ≤ N * (nq ^ 2 / 50) - (kq - u) * Mq := by
              have : 0 ≤ kq - u := by linarith
              nlinarith only [this, hM_le]
            set t : ℚ := u - nq / 10
            have ht_pos : 0 < t := by dsimp only [t]; linarith only [hu_gt10]
            have hexp : N * (nq ^ 2 / 50) - (kq - u) * Q2 =
                nq ^ 3 / 6250 + 4 * nq ^ 2 * t / 625 + 29 * nq * t ^ 2 / 500 + t ^ 3 / 8 +
                  (nq - 2 * kq) * (Q2 - nq ^ 2 / 50) / 2 := by
              have hNku : N = kq + u := by linarith
              have hu_t : u = nq / 10 + t := by dsimp only [t]; ring
              rw [hNku]; dsimp only [Q2]; rw [hu_t]; ring
            have hrem : 0 ≤ (nq - 2 * kq) * (Q2 - nq ^ 2 / 50) / 2 := by
              have hQ2_gt : nq ^ 2 / 50 ≤ Q2 := by dsimp only [Q2]; nlinarith only [hnq_ge12, hu_pos]
              nlinarith only [hkq_lo, hQ2_gt]
            have hmain : 0 < nq ^ 3 / 6250 + 4 * nq ^ 2 * t / 625 + 29 * nq * t ^ 2 / 500 + t ^ 3 / 8 := by
              positivity
            linarith only [hgeF, hexp, hrem, hmain]
          · push Not at huk
            have h1 : 0 ≤ (u - kq) * Mq := mul_nonneg (by linarith only [huk]) hM_pos.le
            have h2 : 0 < N * (nq ^ 2 / 50) := mul_pos hN_pos (by nlinarith only [hnq_ge12])
            linarith only [h1, h2]
        nlinarith only [hNu, hNu_pos, hrhs_pos]
      by_cases hB1 : 9 * dbar / 4 ≤ p1
      · -- Subcase 2B1: lam = 0
        refine ⟨0, le_refl 0, ?_, ?_⟩
        · intro x _ _
          have hM_b : Mq ≤ 2 * N * p1 / 9 := by
            dsimp only [dbar] at hB1
            have h1 := mul_le_mul_of_nonneg_left hB1 hN_pos.le
            have hL : N * (9 * (2 * Mq / N) / 4) = 9 * Mq / 2 := by field_simp [hN_pos.ne']; ring
            linarith only [h1, hL]
          have hN_half : N ≤ nq / 2 + u := by linarith only [hu_eq, hkq_lo]
          have hp1_pos : 0 < p1 := by dsimp only [p1]; linarith only [hnq_ge12, hu_pos]
          have hQ2_ub : Mq - (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) - x ^ 2 ≤
              -nq ^ 2 / 108 := by
            have hsq : Mq - (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) - x ^ 2 =
                -9 / 8 * (x - 4 * p1 / 9) ^ 2 + (Mq - Q2) + 2 * p1 ^ 2 / 9 := by
              dsimp only [Q2, p1]; ring
            have hsq0 : 0 ≤ 9 / 8 * (x - 4 * p1 / 9) ^ 2 := by positivity
            have hcomp : 2 * p1 * (nq / 2 + u + p1) / 9 - Q2 =
                -(83672 * nq ^ 2 + 248000 * nq * u + 500000 * u ^ 2) / 9000000 := by
              dsimp only [p1, Q2]; ring
            have hstep : Mq - Q2 + 2 * p1 ^ 2 / 9 ≤ 2 * p1 * (nq / 2 + u + p1) / 9 - Q2 := by
              have : 2 * N * p1 / 9 ≤ 2 * (nq / 2 + u) * p1 / 9 := by nlinarith only [hN_half, hp1_pos]
              linarith only [hM_b, this]
            have hbd : -(83672 * nq ^ 2 + 248000 * nq * u + 500000 * u ^ 2) / 9000000 ≤ -nq ^ 2 / 108 := by
              nlinarith only [hnq_ge12, hu_pos]
            linarith only [hsq, hsq0, hcomp, hstep, hbd]
          refine ⟨fun h10 => ?_, fun _ => by simp only [zero_mul]; nlinarith only [hQ2_ub, hnq_ge12]⟩
          simp only [zero_mul]
          have hdiff : (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) -
              (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) =
              (16 * nq ^ 2 - (70 * (u - x) - 3 * nq) ^ 2) / 140000 := by ring
          have hsq0 : 0 ≤ (70 * (u - x) - 3 * nq) ^ 2 := sq_nonneg _
          have hgap : (401 * nq ^ 2 / 20000 + 83 * nq * (u - x) / 1000 + (u - x) ^ 2 / 8) -
              (nq ^ 2 / 50 + 2 * nq * (u - x) / 25 + 4 * (u - x) ^ 2 / 25) ≤ nq ^ 2 / 8750 := by
            linarith only [hdiff, hsq0]
          nlinarith only [hQ2_ub, hgap, hnq_ge12]
        · intro x hux
          simp only [zero_mul]
          have h1 : p2 * x - x ^ 2 = x * (p2 - x) := by ring
          have h2 : p2 - x ≤ 0 := by linarith only [hp2_lt_dbar, hdu, hux]
          have h3 : 0 ≤ x := by linarith only [hu_pos, hux]
          nlinarith only [h1, h2, h3]
      · push Not at hB1
        exact piece2_sep_B2 hnq_ge12 hkq_lo hkq_hi hu_eq hu_gt10 hN_pos hM_le hdu hB1
  -- Sum over v ∈ S to derive contradiction (strict at some v0 with d v0 >= 1)
  obtain ⟨lam, hlam0, hP1_le, hP2_le⟩ := hsep
  have hex_pos : ∃ v0 ∈ S, 1 ≤ d v0 := by
    by_contra hall0
    push Not at hall0
    have hzero : ∑ v ∈ S, d v = 0 := Finset.sum_eq_zero (fun v hv => by have := hall0 v hv; omega)
    have hM0 : M = 0 := by omega
    rw [hM0] at hM_gt; omega
  obtain ⟨v0, hv0S, hv0_pos⟩ := hex_pos
  have hsub_cast : ∀ x : ℕ, x ≤ #S - k → ((#S - x - k : ℕ) : ℚ) = u - (x : ℚ) := by
    intro x hx
    have hnat : (#S - x - k) + x = #S - k := by omega
    have hq : ((#S - x - k : ℕ) : ℚ) + (x : ℚ) = u := by dsimp only [u]; exact_mod_cast hnat
    linarith
  have hbound_pos : ∀ v ∈ S, 1 ≤ d v → ((Sv v : ℚ) - (d v : ℚ) ^ 2) < lam * ((d v : ℚ) - dbar) := by
    intro v hv hdv1
    by_cases hdv_u : d v ≤ #S - k
    · have h1 := hb1 v hv hdv1 hdv_u
      have hsc := hsub_cast (d v) hdv_u
      have hsepv := hP1_le (d v : ℚ) (Nat.cast_nonneg _) (by dsimp only [u]; exact_mod_cast hdv_u)
      by_cases hp : 10 * (#S - d v - k) ≤ n
      · rw [if_pos hp] at h1
        rw [hsc] at h1
        have hpq : 10 * (u - (d v : ℚ)) ≤ nq := by
          rw [← hsc]; dsimp only [nq]; exact_mod_cast hp
        linarith only [h1, hsepv.1 hpq]
      · rw [if_neg hp] at h1
        rw [hsc] at h1
        have hpq : nq < 10 * (u - (d v : ℚ)) := by
          rw [← hsc]; dsimp only [nq]; exact_mod_cast (show n < 10 * (#S - d v - k) by omega)
        linarith only [h1, hsepv.2 hpq]
    · have h1 := hb2 v hv (by omega)
      have h2 := hP2_le (d v : ℚ) (by dsimp only [u]; exact_mod_cast (show #S - k ≤ d v by omega))
      dsimp only [p2] at h2; linarith only [h1, h2]
  have hle_all : ∀ v ∈ S, ((Sv v : ℚ) - (d v : ℚ) ^ 2) ≤ lam * ((d v : ℚ) - dbar) := by
    intro v hv
    by_cases hdv0 : d v = 0
    · rw [hd0 v hv hdv0, hdv0]; simp
      exact mul_nonpos_of_nonpos_of_nonneg hlam0 hdbar_pos.le
    · exact (hbound_pos v hv (by omega)).le
  have hsum_lt : ∑ v ∈ S, ((Sv v : ℚ) - (d v : ℚ) ^ 2) < ∑ v ∈ S, lam * ((d v : ℚ) - dbar) :=
    Finset.sum_lt_sum hle_all ⟨v0, hv0S, hbound_pos v0 hv0S hv0_pos⟩
  have hLHS0 : ∑ v ∈ S, ((Sv v : ℚ) - (d v : ℚ) ^ 2) = 0 := by
    rw [Finset.sum_sub_distrib]
    have h1 : (∑ v ∈ S, (Sv v : ℚ)) = ((∑ v ∈ S, Sv v : ℕ) : ℚ) := by simp
    have h2 : (∑ v ∈ S, (d v : ℚ) ^ 2) = ((∑ v ∈ S, (d v) ^ 2 : ℕ) : ℚ) := by simp
    rw [h1, h2, hsum_Sv]; ring
  have hRHS0 : ∑ v ∈ S, lam * ((d v : ℚ) - dbar) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h1 : (∑ v ∈ S, (d v : ℚ)) = ((∑ v ∈ S, d v : ℕ) : ℚ) := by simp
    rw [h1, hsum_d]
    have h2 : ((2 * M : ℕ) : ℚ) = 2 * Mq := by push_cast; rfl
    have h3 : ((#S : ℕ) : ℚ) = N := rfl
    rw [h2, h3]; dsimp only [dbar]; field_simp [hN_pos.ne']; ring
  linarith

/-- Theorem 1 (Master 2-piece potential lower bound on all induced subgraphs of size `N in [k, n]`). -/
theorem induce_edgeSet_gt_twoPiece {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (S : Finset V) (hSk : Fintype.card V / 2 ≤ #S) :
    (if 10 * (#S - Fintype.card V / 2) ≤ Fintype.card V
      then (Fintype.card V : ℚ) ^ 2 / 50 +
        2 * (Fintype.card V : ℚ) * ((#S - Fintype.card V / 2 : ℕ) : ℚ) / 25 +
        4 * (((#S - Fintype.card V / 2 : ℕ) : ℚ) ^ 2) / 25
      else 401 * (Fintype.card V : ℚ) ^ 2 / 20000 +
        83 * (Fintype.card V : ℚ) * ((#S - Fintype.card V / 2 : ℕ) : ℚ) / 1000 +
        (((#S - Fintype.card V / 2 : ℕ) : ℚ) ^ 2) / 8) <
      ((G.induce (S : Set V)).edgeSet.ncard : ℚ) := by
  classical
  set n := Fintype.card V
  set k := n / 2
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  have hk_lo : 2 * k ≤ n := by omega
  have hk_hi : n ≤ 2 * k + 1 := by omega
  suffices hind : ∀ N : ℕ, k ≤ N → N ≤ n →
      ∀ S : Finset V, #S = N →
        (if 10 * (N - k) ≤ n
          then (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((N - k : ℕ) : ℚ) / 25 + 4 * (((N - k : ℕ) : ℚ) ^ 2) / 25
          else 401 * (n : ℚ) ^ 2 / 20000 + 83 * (n : ℚ) * ((N - k : ℕ) : ℚ) / 1000 + (((N - k : ℕ) : ℚ) ^ 2) / 8) <
          ((G.induce (S : Set V)).edgeSet.ncard : ℚ) by
    exact hind #S hSk (by simpa [n] using Finset.card_le_univ S) S rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hNk hNn S hSN
    by_cases hbase : N = k
    · subst hbase
      have h50 : 50 * (G.induce (S : Set V)).edgeSet.ncard > n ^ 2 := by
        apply hH (S : Set V); rw [Set.ncard_coe_finset, hSN]; omega
      have h50q : (n : ℚ) ^ 2 < 50 * ((G.induce (S : Set V)).edgeSet.ncard : ℚ) := by exact_mod_cast h50
      rw [if_pos (by omega)]
      simp only [Nat.sub_self, Nat.cast_zero, mul_zero, zero_div, add_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      linarith
    · by_contra hle
      push Not at hle
      set M := (G.induce (S : Set V)).edgeSet.ncard
      have hM_gt : n ^ 2 < 50 * M := by
        obtain ⟨S₀, hS₀S, hS₀k⟩ := Finset.exists_subset_card_eq (by omega : k ≤ #S)
        have h50 := hH (S₀ : Set V) (by rw [Set.ncard_coe_finset, hS₀k]; omega)
        have hmono : (G.induce (S₀ : Set V)).edgeSet.ncard ≤ M := by
          have h1 := two_mul_induce_edgeSet_ncard G S₀
          have h2 := two_mul_induce_edgeSet_ncard G S
          have hle2 : ∑ u ∈ S₀, #(S₀.filter (G.Adj u)) ≤ ∑ u ∈ S, #(S.filter (G.Adj u)) :=
            (Finset.sum_le_sum (fun u _ => Finset.card_le_card (Finset.filter_subset_filter _ hS₀S))).trans
              (Finset.sum_le_sum_of_subset hS₀S)
          omega
        omega
      let d : V → ℕ := fun v => #(S.filter (G.Adj v))
      let Sv : V → ℕ := fun v => ∑ w ∈ S.filter (G.Adj v), d w
      have hsum_d : ∑ v ∈ S, d v = 2 * M := (two_mul_induce_edgeSet_ncard G S).symm
      have hsum_Sv : ∑ v ∈ S, Sv v = ∑ v ∈ S, (d v) ^ 2 := by
        calc ∑ v ∈ S, ∑ w ∈ S.filter (G.Adj v), d w
            = ∑ v ∈ S, ∑ w ∈ S, if G.Adj v w then d w else 0 := by
              apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_filter]
          _ = ∑ w ∈ S, ∑ v ∈ S, if G.Adj v w then d w else 0 := Finset.sum_comm
          _ = ∑ w ∈ S, ∑ v ∈ S, if G.Adj w v then d w else 0 := by
              apply Finset.sum_congr rfl; intro w _
              apply Finset.sum_congr rfl; intro v _; simp [G.adj_comm]
          _ = ∑ w ∈ S, ∑ _v ∈ S.filter (G.Adj w), d w := by
              apply Finset.sum_congr rfl; intro w _; rw [← Finset.sum_filter]
          _ = ∑ w ∈ S, (d w) ^ 2 := by
              apply Finset.sum_congr rfl; intro w _; rw [Finset.sum_const, smul_eq_mul]; ring
      have hd0 : ∀ v ∈ S, d v = 0 → Sv v = 0 := by
        intro v _ hdv; dsimp only [Sv]; rw [Finset.card_eq_zero.mp hdv, Finset.sum_empty]
      have hNv_indep : ∀ v ∈ S, ∀ x ∈ S.filter (G.Adj v), ∀ y ∈ S.filter (G.Adj v), ¬ G.Adj x y := by
        intro v _ x hx y hy hxy
        exact not_adj_of_cliqueFree_three hTF (Finset.mem_filter.mp hx).2 hxy (Finset.mem_filter.mp hy).2
      have hb1 : ∀ v ∈ S, 1 ≤ d v → d v ≤ #S - k →
          ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
            (M : ℚ) - (if 10 * (#S - d v - k) ≤ n
              then (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * ((#S - d v - k : ℕ) : ℚ) / 25 +
                4 * (((#S - d v - k : ℕ) : ℚ) ^ 2) / 25
              else 401 * (n : ℚ) ^ 2 / 20000 + 83 * (n : ℚ) * ((#S - d v - k : ℕ) : ℚ) / 1000 +
                (((#S - d v - k : ℕ) : ℚ) ^ 2) / 8) - (d v : ℚ) ^ 2 := by
        intro v hv hdv1 hdv_u
        let J := S.filter (G.Adj v)
        have hJS : J ⊆ S := Finset.filter_subset _ _
        have hcard_sdiff : #(S \ J) = N - d v := by rw [Finset.card_sdiff_of_subset hJS, hSN]
        have hih := ih (N - d v) (by omega) (by omega) (by omega) (S \ J) hcard_sdiff
        have hedge := induce_edgeSet_ncard_sdiff_indep G hJS (hNv_indep v hv)
        have hedge_q : ((G.induce ((S \ J : Finset V) : Set V)).edgeSet.ncard : ℚ) + (Sv v : ℚ) = (M : ℚ) := by
          exact_mod_cast hedge
        rw [← hSN] at hih
        linarith
      have hb2 : ∀ v ∈ S, #S - k < d v →
          ((Sv v : ℚ) - (d v : ℚ) ^ 2) <
            (((M : ℚ) - (n : ℚ) ^ 2 / 50) / ((#S - k : ℕ) : ℚ)) * (d v : ℚ) - (d v : ℚ) ^ 2 := by
        intro v hv hdv_gt
        let Nv := S.filter (G.Adj v)
        set uN := #S - k
        have huN1 : 1 ≤ uN := by omega
        have huN_le : uN ≤ #Nv := by change #S - k ≤ d v; omega
        have hperJ : ∀ J ∈ Nv.powersetCard uN, n ^ 2 + 50 * ∑ w ∈ J, d w < 50 * M := by
          intro J hJ
          have hJsub : J ⊆ Nv := (Finset.mem_powersetCard.mp hJ).1
          have hJcard : #J = uN := (Finset.mem_powersetCard.mp hJ).2
          have hJS : J ⊆ S := hJsub.trans (Finset.filter_subset _ _)
          have hJindep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y :=
            fun x hx y hy => hNv_indep v hv x (hJsub hx) y (hJsub hy)
          have hcard_k : #(S \ J) = k := by rw [Finset.card_sdiff_of_subset hJS, hJcard]; omega
          have h50 := hH ((S \ J : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard_k]; omega)
          have hedge := induce_edgeSet_ncard_sdiff_indep G hJS hJindep
          change (G.induce ((S \ J : Finset V) : Set V)).edgeSet.ncard + ∑ w ∈ J, d w = M at hedge
          omega
        have hne_pow : (Nv.powersetCard uN).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hemp
          have h0 : (#Nv).choose uN = 0 := by rw [← Finset.card_powersetCard, hemp, Finset.card_empty]
          have hpos := Nat.choose_pos huN_le
          omega
        have hsum_lt := Finset.sum_lt_sum_of_nonempty hne_pow hperJ
        have hsum_J : ∑ J ∈ Nv.powersetCard uN, ∑ w ∈ J, d w = (#Nv - 1).choose (uN - 1) * Sv v := by
          calc ∑ J ∈ Nv.powersetCard uN, ∑ w ∈ J, d w
              = ∑ J ∈ Nv.powersetCard uN, ∑ w ∈ Nv, if w ∈ J then d w else 0 := by
                apply Finset.sum_congr rfl; intro J hJ
                rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                  Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hJ).1]
            _ = ∑ w ∈ Nv, ∑ J ∈ Nv.powersetCard uN, if w ∈ J then d w else 0 := Finset.sum_comm
            _ = ∑ w ∈ Nv, #((Nv.powersetCard uN).filter (w ∈ ·)) * d w := by
                apply Finset.sum_congr rfl; intro w _
                rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
            _ = ∑ w ∈ Nv, (#Nv - 1).choose (uN - 1) * d w := by
                apply Finset.sum_congr rfl; intro w hw; rw [card_powersetCard_mem Nv hw huN1]
            _ = (#Nv - 1).choose (uN - 1) * Sv v := (Finset.mul_sum _ _ _).symm
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_J, Finset.sum_const, Finset.sum_const,
          Finset.card_powersetCard, smul_eq_mul, smul_eq_mul] at hsum_lt
        have hchoose : (#Nv).choose uN * uN = #Nv * (#Nv - 1).choose (uN - 1) := by
          have := Nat.add_one_mul_choose_eq (#Nv - 1) (uN - 1)
          rw [show #Nv - 1 + 1 = #Nv by omega, show uN - 1 + 1 = uN by omega] at this
          linarith
        have hmul_lt := Nat.mul_lt_mul_of_pos_left hsum_lt (by omega : 0 < #Nv)
        have hnat_lt : (#Nv).choose uN * (uN * (50 * Sv v) + #Nv * n ^ 2) <
            (#Nv).choose uN * (#Nv * (50 * M)) := by
          have hL : #Nv * ((#Nv).choose uN * n ^ 2 + 50 * ((#Nv - 1).choose (uN - 1) * Sv v)) =
              (#Nv).choose uN * (uN * (50 * Sv v) + #Nv * n ^ 2) := by
            calc #Nv * ((#Nv).choose uN * n ^ 2 + 50 * ((#Nv - 1).choose (uN - 1) * Sv v))
                = (#Nv).choose uN * (#Nv * n ^ 2) + (#Nv * (#Nv - 1).choose (uN - 1)) * (50 * Sv v) := by ring
              _ = (#Nv).choose uN * (#Nv * n ^ 2) + ((#Nv).choose uN * uN) * (50 * Sv v) := by rw [← hchoose]
              _ = (#Nv).choose uN * (uN * (50 * Sv v) + #Nv * n ^ 2) := by ring
          have hR : #Nv * ((#Nv).choose uN * (50 * M)) = (#Nv).choose uN * (#Nv * (50 * M)) := by ring
          omega
        have hclean : uN * (50 * Sv v) + d v * n ^ 2 < d v * (50 * M) := Nat.lt_of_mul_lt_mul_left hnat_lt
        have hq : (uN : ℚ) * (50 * (Sv v : ℚ)) + (d v : ℚ) * (n : ℚ) ^ 2 < (d v : ℚ) * (50 * (M : ℚ)) := by
          exact_mod_cast hclean
        have huq_pos : (0 : ℚ) < (uN : ℚ) := by exact_mod_cast huN1
        have hSv_lt : (Sv v : ℚ) < (((M : ℚ) - (n : ℚ) ^ 2 / 50) / (uN : ℚ)) * (d v : ℚ) := by
          have h1 : (uN : ℚ) * (Sv v : ℚ) < (uN : ℚ) * ((((M : ℚ) - (n : ℚ) ^ 2 / 50) / (uN : ℚ)) * (d v : ℚ)) := by
            have hR : (uN : ℚ) * ((((M : ℚ) - (n : ℚ) ^ 2 / 50) / (uN : ℚ)) * (d v : ℚ)) =
                ((M : ℚ) - (n : ℚ) ^ 2 / 50) * (d v : ℚ) := by field_simp [huq_pos.ne']
            linarith
          exact lt_of_mul_lt_mul_left h1 huq_pos.le
        linarith
      exact two_piece_step_contra S hn12 hk_lo hk_hi (by omega) (by omega) hM_gt
        (by rw [hSN]; exact hle) d Sv hsum_d hsum_Sv hd0 hb1 hb2

/-- Corollary 1: Improved global edge lower bound `58 * n^2 < 625 * e(G)` (e/n^2 > 0.0928). -/
theorem six_hundred_twenty_five_mul_edges_gt {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    58 * Fintype.card V ^ 2 < 625 * G.edgeSet.ncard := by
  classical
  set n := Fintype.card V
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  have hfull := induce_edgeSet_gt_twoPiece G hTF hH Finset.univ (by simp; omega)
  have hedge_univ : (G.induce ((Finset.univ : Finset V) : Set V)).edgeSet.ncard = G.edgeSet.ncard := by
    have h1 := two_mul_induce_edgeSet_ncard G (Finset.univ : Finset V)
    have h2 : 2 * G.edgeSet.ncard = ∑ u : V, #((Finset.univ : Finset V).filter (G.Adj u)) := by
      have hcard : G.edgeSet.ncard = #G.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro u _
      rw [SimpleGraph.degree, SimpleGraph.neighborFinset]
      congr 1; ext v; simp
    omega
  rw [hedge_univ] at hfull
  have hcard_u : (#(Finset.univ : Finset V) - n / 2) = n - n / 2 := by simp [n]
  rw [hcard_u, if_neg (by omega)] at hfull
  have hu_ge_half : (n : ℚ) / 2 ≤ ((n - n / 2 : ℕ) : ℚ) := by
    have h1 : n ≤ 2 * (n - n / 2) := by omega
    have h2 : (n : ℚ) ≤ 2 * ((n - n / 2 : ℕ) : ℚ) := by exact_mod_cast h1
    linarith
  have hQ2_ge : 58 * (n : ℚ) ^ 2 / 625 ≤
      401 * (n : ℚ) ^ 2 / 20000 + 83 * (n : ℚ) * ((n - n / 2 : ℕ) : ℚ) / 1000 +
      (((n - n / 2 : ℕ) : ℚ) ^ 2) / 8 := by
    have hnq : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    nlinarith only [hu_ge_half, hnq]
  have hq : 58 * (n : ℚ) ^ 2 < 625 * (G.edgeSet.ncard : ℚ) := by linarith
  exact_mod_cast hq

end TwoPiecePotential

section BipartiteDeletion

/-- Exact averaging lemma for arbitrary disjoint Finsets `J, K` keeping `(#K - 1)` uncancelled. -/
lemma avg_union_gt {V : Type} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {J K : Finset V} {r T : ℕ}
    (hdisj : Disjoint J K) (hr2 : 2 ≤ r) (hrK : r ≤ #K) (hK2 : 2 ≤ #K)
    (hbound : ∀ S ∈ K.powersetCard r, T < 25 * (2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard)) :
    T * #K * (#K - 1) <
      25 * (#K * (#K - 1) * (∑ u ∈ J, #(J.filter (G.Adj u))) +
        2 * r * (#K - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
        r * (r - 1) * (∑ u ∈ K, #(K.filter (G.Adj u)))) := by
  have hpos : 0 < (#K).choose r := Nat.choose_pos hrK
  have hne : (K.powersetCard r).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have : (#K).choose r = 0 := by rw [← Finset.card_powersetCard, hemp, Finset.card_empty]
    omega
  have hsum_lt : (#K).choose r * T <
      25 * ∑ S ∈ K.powersetCard r, 2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard := by
    rw [Finset.mul_sum]
    calc (#K).choose r * T
        = ∑ _S ∈ K.powersetCard r, T := by rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
      _ < _ := Finset.sum_lt_sum_of_nonempty hne hbound
  have hsum_eq : ∑ S ∈ K.powersetCard r, 2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard =
      (#K).choose r * (∑ u ∈ J, #(J.filter (G.Adj u))) +
      2 * (#K - 1).choose (r - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
      (#K - 2).choose (r - 2) * (∑ u ∈ K, #(K.filter (G.Adj u))) := by
    have hstep : ∀ S ∈ K.powersetCard r,
        2 * (G.induce ((J ∪ S : Finset V) : Set V)).edgeSet.ncard =
        (∑ u ∈ J, #(J.filter (G.Adj u))) +
        2 * (∑ w ∈ S, #(J.filter (G.Adj w))) +
        (∑ u ∈ S, #(S.filter (G.Adj u))) := by
      intro S hS
      rw [two_mul_induce_edgeSet_ncard]
      exact sum_adj_union G (hdisj.mono_right (Finset.mem_powersetCard.mp hS).1)
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_powersetCard, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    · congr 1
      have h1 : ∑ S ∈ K.powersetCard r, ∑ w ∈ S, #(J.filter (G.Adj w)) =
          ∑ w ∈ K, #((K.powersetCard r).filter (w ∈ ·)) * #(J.filter (G.Adj w)) := by
        calc ∑ S ∈ K.powersetCard r, ∑ w ∈ S, #(J.filter (G.Adj w))
            = ∑ S ∈ K.powersetCard r, ∑ w ∈ K, if w ∈ S then #(J.filter (G.Adj w)) else 0 := by
              apply Finset.sum_congr rfl; intro S hS
              rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
                Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
          _ = ∑ w ∈ K, ∑ S ∈ K.powersetCard r, if w ∈ S then #(J.filter (G.Adj w)) else 0 := Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl; intro w _
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [h1, mul_assoc]; congr 1; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro w hw
      rw [card_powersetCard_mem K hw (by omega)]
    · have h2 : ∑ S ∈ K.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u)) =
          ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u), #((K.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) := by
        calc ∑ S ∈ K.powersetCard r, ∑ u ∈ S, #(S.filter (G.Adj u))
            = ∑ S ∈ K.powersetCard r, ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u),
                if u ∈ S ∧ v ∈ S then 1 else 0 := by
              apply Finset.sum_congr rfl; intro S hS
              have hSK := (Finset.mem_powersetCard.mp hS).1
              calc ∑ u ∈ S, #(S.filter (G.Adj u))
                  = ∑ u ∈ K, if u ∈ S then #(S.filter (G.Adj u)) else 0 := by
                    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hSK]
                _ = ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u), if u ∈ S ∧ v ∈ S then 1 else 0 := by
                    apply Finset.sum_congr rfl; intro u _
                    by_cases hu : u ∈ S
                    · simp only [hu, true_and, if_true, ← Finset.card_filter]
                      congr 1; ext v; simp only [Finset.mem_filter]
                      exact ⟨fun ⟨hv, hadj⟩ => ⟨⟨hSK hv, hadj⟩, hv⟩, fun ⟨⟨_, hadj⟩, hv⟩ => ⟨hv, hadj⟩⟩
                    · simp [hu]
          _ = ∑ u ∈ K, ∑ S ∈ K.powersetCard r, ∑ v ∈ K.filter (G.Adj u),
                if u ∈ S ∧ v ∈ S then 1 else 0 := Finset.sum_comm
          _ = ∑ u ∈ K, ∑ v ∈ K.filter (G.Adj u), ∑ S ∈ K.powersetCard r,
                if u ∈ S ∧ v ∈ S then 1 else 0 := by
              apply Finset.sum_congr rfl; intro u _; exact Finset.sum_comm
          _ = _ := by
              apply Finset.sum_congr rfl; intro u _
              apply Finset.sum_congr rfl; intro v _; rw [← Finset.card_filter]
      rw [h2, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro u hu
      have hinner : ∑ v ∈ K.filter (G.Adj u), #((K.powersetCard r).filter (fun S => u ∈ S ∧ v ∈ S)) =
          ∑ _v ∈ K.filter (G.Adj u), (#K - 2).choose (r - 2) := by
        apply Finset.sum_congr rfl; intro v hv
        have hv' := Finset.mem_filter.mp hv
        exact card_powersetCard_mem_pair K hu hv'.1 (G.ne_of_adj hv'.2) hr2
      rw [hinner, Finset.sum_const, smul_eq_mul, mul_comm]
  rw [hsum_eq] at hsum_lt
  have hc1 : (#K).choose r * r = #K * (#K - 1).choose (r - 1) := by
    have := Nat.add_one_mul_choose_eq (#K - 1) (r - 1)
    rw [show #K - 1 + 1 = #K by omega, show r - 1 + 1 = r by omega] at this
    linarith
  have hc2 : (#K).choose r * r * (r - 1) = #K * (#K - 1) * (#K - 2).choose (r - 2) := by
    have hstep1 : (#K - 1).choose (r - 1) * (r - 1) = (#K - 1) * (#K - 2).choose (r - 2) := by
      have := Nat.add_one_mul_choose_eq (#K - 2) (r - 2)
      rw [show #K - 2 + 1 = #K - 1 by omega, show r - 2 + 1 = r - 1 by omega] at this
      linarith
    calc (#K).choose r * r * (r - 1)
        = (#K * (#K - 1).choose (r - 1)) * (r - 1) := by rw [hc1]
      _ = #K * ((#K - 1).choose (r - 1) * (r - 1)) := by ring
      _ = #K * ((#K - 1) * (#K - 2).choose (r - 2)) := by rw [hstep1]
      _ = #K * (#K - 1) * (#K - 2).choose (r - 2) := by ring
  have hmul := Nat.mul_lt_mul_of_pos_left hsum_lt (Nat.mul_pos (by omega : 0 < #K) (by omega : 0 < #K - 1))
  have hkey : (#K).choose r * (T * #K * (#K - 1)) <
      (#K).choose r * (25 * (#K * (#K - 1) * (∑ u ∈ J, #(J.filter (G.Adj u))) +
        2 * r * (#K - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
        r * (r - 1) * (∑ u ∈ K, #(K.filter (G.Adj u))))) := by
    have hL : #K * (#K - 1) * ((#K).choose r * T) = (#K).choose r * (T * #K * (#K - 1)) := by ring
    have hR : #K * (#K - 1) * (25 * ((#K).choose r * (∑ u ∈ J, #(J.filter (G.Adj u))) +
        2 * (#K - 1).choose (r - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
        (#K - 2).choose (r - 2) * (∑ u ∈ K, #(K.filter (G.Adj u))))) =
        (#K).choose r * (25 * (#K * (#K - 1) * (∑ u ∈ J, #(J.filter (G.Adj u))) +
          2 * r * (#K - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
          r * (r - 1) * (∑ u ∈ K, #(K.filter (G.Adj u))))) := by
      calc #K * (#K - 1) * (25 * ((#K).choose r * (∑ u ∈ J, #(J.filter (G.Adj u))) +
            2 * (#K - 1).choose (r - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
            (#K - 2).choose (r - 2) * (∑ u ∈ K, #(K.filter (G.Adj u)))))
          = 25 * ((#K).choose r * (#K * (#K - 1) * (∑ u ∈ J, #(J.filter (G.Adj u)))) +
            2 * (#K * (#K - 1).choose (r - 1)) * (#K - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
            (#K * (#K - 1) * (#K - 2).choose (r - 2)) * (∑ u ∈ K, #(K.filter (G.Adj u)))) := by ring
        _ = 25 * ((#K).choose r * (#K * (#K - 1) * (∑ u ∈ J, #(J.filter (G.Adj u)))) +
            2 * ((#K).choose r * r) * (#K - 1) * (∑ w ∈ K, #(J.filter (G.Adj w))) +
            ((#K).choose r * r * (r - 1)) * (∑ u ∈ K, #(K.filter (G.Adj u)))) := by rw [← hc1, ← hc2]
        _ = _ := by ring
    linarith only [hmul, hL, hR]
  exact Nat.lt_of_mul_lt_mul_left hkey

/-- Helper for Theorem 2 assuming `|A| >= |B|` for disjoint `A, B` covering `Finset.univ`. -/
lemma bipartite_del_gt_ordered {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (A B : Finset V) (hdisj : Disjoint A B) (hcov : A ∪ B = Finset.univ) (hle : #B ≤ #A) :
    37 * Fintype.card V ^ 2 <
      1250 * ((G.induce (A : Set V)).edgeSet.ncard + (G.induce (B : Set V)).edgeSet.ncard) := by
  set n := Fintype.card V
  set k := n / 2
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  have hsum_ab : #A + #B = n := by
    rw [← Finset.card_union_of_disjoint hdisj, hcov, Finset.card_univ]
  set a := #A
  set b := #B
  have ha_ge_k : k ≤ a := by omega
  have hb_le_k : b ≤ k := by omega
  set u := a - k
  set r := k - b
  have hru : r ≤ u := by omega
  -- Case 0a: r = 0 (so b = k and a >= k)
  by_cases hr0 : r = 0
  · have hA50 := hH (A : Set V) (by rw [Set.ncard_coe_finset]; omega)
    have hB50 := hH (B : Set V) (by rw [Set.ncard_coe_finset]; omega)
    omega
  -- Case 0b: 10 * u > n
  by_cases hu10 : 10 * u ≤ n
  · -- Main regime: r >= 1 and 10 * u <= n
    have hFA := induce_edgeSet_gt_twoPiece G hTF hH A ha_ge_k
    rw [if_pos hu10] at hFA
    -- Partition A into A1 = {x ∈ A | 2*d_B(x) > b} (indep) and A0 = A \ A1
    let A1 : Finset V := A.filter (fun x => b < 2 * #(B.filter (G.Adj x)))
    let A0 : Finset V := A.filter (fun x => 2 * #(B.filter (G.Adj x)) ≤ b)
    have hA1_indep : ∀ x ∈ A1, ∀ y ∈ A1, ¬ G.Adj x y := by
      intro x hx y hy hxy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      have hd : Disjoint (B.filter (G.Adj x)) (B.filter (G.Adj y)) := by
        rw [Finset.disjoint_left]; intro w hwx hwy
        exact not_adj_of_cliqueFree_three hTF hxy (Finset.mem_filter.mp hwy).2 (Finset.mem_filter.mp hwx).2
      have hu : #(B.filter (G.Adj x)) + #(B.filter (G.Adj y)) ≤ #B := by
        rw [← Finset.card_union_of_disjoint hd]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      omega
    have h5a1 : 5 * #A1 < 2 * n := by
      have h := five_mul_indep_lt_two_mul_card G hTF hH (A1 : Set V) (by
        intro x hx y hy _ hxy; exact hA1_indep x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy)
      rwa [Set.ncard_coe_finset] at h
    have hdisj_10 : Disjoint A1 A0 := by
      rw [Finset.disjoint_left]; intro x hx1 hx0
      have h1 := (Finset.mem_filter.mp hx1).2; have h0 := (Finset.mem_filter.mp hx0).2; omega
    have hunion_10 : A1 ∪ A0 = A := by
      ext x; simp only [A1, A0, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx; by_cases h : b < 2 * #(B.filter (G.Adj x))
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    have hcard_10 : #A1 + #A0 = a := by rw [← Finset.card_union_of_disjoint hdisj_10, hunion_10]
    set a1 := #A1
    set a0 := #A0
    set r1 := k - a1
    have hr1_ge1 : 1 ≤ r1 := by omega
    have ha0_ge2 : 2 ≤ a0 := by omega
    have hdisj_BA0 : Disjoint B A0 := hdisj.symm.mono_right (Finset.filter_subset _ _)
    -- Max independent subset J ⊆ A0
    let indepA0 : Finset (Finset V) := A0.powerset.filter (fun S => ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
    obtain ⟨J, hJ_mem, hJ_max⟩ := Finset.exists_max_image indepA0 Finset.card ⟨∅, by simp [indepA0]⟩
    have hJ_sub : J ⊆ A0 := Finset.mem_powerset.mp (Finset.mem_filter.mp hJ_mem).1
    have hJ_indep : ∀ x ∈ J, ∀ y ∈ J, ¬ G.Adj x y := (Finset.mem_filter.mp hJ_mem).2
    by_cases hbeta : r ≤ #J
    · -- Case 1: alpha(A0) >= r
      obtain ⟨S, hSJ, hScard⟩ := Finset.exists_subset_card_eq hbeta
      have hSA0 : S ⊆ A0 := hSJ.trans hJ_sub
      have hS_indep : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y := fun x hx y hy => hJ_indep x (hSJ hx) y (hSJ hy)
      have hdisj_BS : Disjoint B S := hdisj_BA0.mono_right hSA0
      have hcard_BS : #(B ∪ S) = k := by rw [Finset.card_union_of_disjoint hdisj_BS, hScard]; omega
      have h50 := hH ((B ∪ S : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard_BS]; omega)
      have h2BS := two_mul_induce_edgeSet_ncard G (B ∪ S)
      have h2B := two_mul_induce_edgeSet_ncard G B
      have hsum_BS := sum_adj_union G hdisj_BS
      have hSS0 : ∑ x ∈ S, #(S.filter (G.Adj x)) = 0 := by
        apply Finset.sum_eq_zero; intro x hx
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun y hy => hS_indep x hx y hy
      have hBS_le : 2 * ∑ x ∈ S, #(B.filter (G.Adj x)) ≤ r * b := by
        calc 2 * ∑ x ∈ S, #(B.filter (G.Adj x))
            = ∑ x ∈ S, 2 * #(B.filter (G.Adj x)) := Finset.mul_sum _ _ _
          _ ≤ ∑ _x ∈ S, b := Finset.sum_le_sum (fun x hx => (Finset.mem_filter.mp (hSA0 hx)).2)
          _ = r * b := by rw [Finset.sum_const, hScard, smul_eq_mul]
      have heB_gt : n ^ 2 < 50 * (G.induce (B : Set V)).edgeSet.ncard + 25 * r * b := by
        have hle2 : 2 * (G.induce ((B ∪ S : Finset V) : Set V)).edgeSet.ncard ≤
            2 * (G.induce (B : Set V)).edgeSet.ncard + r * b := by omega
        have h25 : 25 * r * b = 25 * (r * b) := by ring
        omega
      have h2rb_nat : 2 * r * b + 2 * u * u ≤ u * n := by
        by_cases heven : 2 * k = n
        · have hr : r = u := by omega
          have hbn : 2 * b + 2 * u = n := by omega
          nlinarith only [hr, hbn]
        · have hru1 : r + 1 = u := by omega
          have hbn : 2 * b + 2 * u = n + 1 := by omega
          have hub : u ≤ 2 * b := by omega
          nlinarith only [hru1, hbn, hub]
      have heBq : (n : ℚ) ^ 2 / 50 - (u : ℚ) * ((n : ℚ) - 2 * (u : ℚ)) / 4 <
          ((G.induce (B : Set V)).edgeSet.ncard : ℚ) := by
        have h1 : (n : ℚ) ^ 2 < 50 * ((G.induce (B : Set V)).edgeSet.ncard : ℚ) + 25 * (r : ℚ) * (b : ℚ) := by
          exact_mod_cast heB_gt
        have h2 : 2 * (r : ℚ) * (b : ℚ) ≤ (u : ℚ) * ((n : ℚ) - 2 * (u : ℚ)) := by
          have hq : 2 * (r : ℚ) * (b : ℚ) + 2 * (u : ℚ) * (u : ℚ) ≤ (u : ℚ) * (n : ℚ) := by exact_mod_cast h2rb_nat
          linarith only [hq]
        linarith only [h1, h2]
      have hfac : ((n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * (u : ℚ) / 25 + 4 * (u : ℚ) ^ 2 / 25) +
          ((n : ℚ) ^ 2 / 50 - (u : ℚ) * ((n : ℚ) - 2 * (u : ℚ)) / 4) - 37 * (n : ℚ) ^ 2 / 1250 =
          ((n : ℚ) - 10 * (u : ℚ)) * (26 * (n : ℚ) - 165 * (u : ℚ)) / 2500 := by ring
      have hnn : (0 : ℚ) ≤ ((n : ℚ) - 10 * (u : ℚ)) * (26 * (n : ℚ) - 165 * (u : ℚ)) / 2500 := by
        have hu10q : 10 * (u : ℚ) ≤ (n : ℚ) := by exact_mod_cast hu10
        have hu0q : (0 : ℚ) ≤ (u : ℚ) := Nat.cast_nonneg u
        nlinarith only [hu10q, hu0q]
      have hfin : 37 * (n : ℚ) ^ 2 / 1250 <
          ((G.induce (A : Set V)).edgeSet.ncard : ℚ) + ((G.induce (B : Set V)).edgeSet.ncard : ℚ) := by
        linarith only [hFA, heBq, hfac, hnn]
      have hfin2 : 37 * (n : ℚ) ^ 2 <
          1250 * (((G.induce (A : Set V)).edgeSet.ncard : ℚ) + ((G.induce (B : Set V)).edgeSet.ncard : ℚ)) := by
        linarith only [hfin]
      exact_mod_cast hfin2
    · -- Case 2: alpha(A0) < r
      push Not at hbeta
      have hJ_pos : 1 ≤ #J := by
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < #A0)
        have hw_mem : ({w} : Finset V) ∈ indepA0 := by
          simp only [indepA0, Finset.mem_filter, Finset.mem_powerset, Finset.singleton_subset_iff,
            Finset.mem_singleton]
          refine ⟨hw, ?_⟩; rintro _ rfl _ rfl; exact G.loopless.irrefl _
        simpa using hJ_max {w} hw_mem
      have hr2 : 2 ≤ r := by omega
      -- Step 2.1: A1 union S' averaging => 50 * r1 * e(A) > a0 * n^2
      have h50eA : a0 * n ^ 2 < 50 * r1 * (G.induce (A : Set V)).edgeSet.ncard := by
        have hsc := avg_union_ge_scaled G hdisj_10 hr1_ge1 (by omega) ha0_ge2 (T := n ^ 2 + 1) (fun S hS => by
          have hcard : #(A1 ∪ S) = k := by
            rw [Finset.card_union_of_disjoint (hdisj_10.mono_right (Finset.mem_powersetCard.mp hS).1),
              (Finset.mem_powersetCard.mp hS).2]; omega
          have h50 := hH ((A1 ∪ S : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard]; omega)
          omega)
        have hA1_0 : ∑ x ∈ A1, #(A1.filter (G.Adj x)) = 0 := by
          apply Finset.sum_eq_zero; intro x hx
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun y hy => hA1_indep x hx y hy
        rw [hA1_0, mul_zero, zero_add] at hsc
        have h2A := two_mul_induce_edgeSet_ncard G A
        have hsumA := sum_adj_union_indep G hdisj_10 hA1_indep
        rw [hunion_10] at hsumA
        have : 2 * r1 * (∑ w ∈ A0, #(A1.filter (G.Adj w))) + r1 * (∑ u ∈ A0, #(A0.filter (G.Adj u))) =
            r1 * (2 * (G.induce (A : Set V)).edgeSet.ncard) := by rw [h2A, hsumA]; ring
        have ha0_pos : 0 < a0 := by omega
        nlinarith only [hsc, this, ha0_pos]
      by_cases hsub2a : 37 * r1 ≤ 25 * a0
      · -- Subcase 2a: 37 * r1 <= 25 * a0
        have h1 : 37 * r1 * n ^ 2 ≤ 25 * (a0 * n ^ 2) := by
          have := Nat.mul_le_mul_right (n ^ 2) hsub2a; linarith
        have h2 : 25 * (a0 * n ^ 2) < 25 * (50 * r1 * (G.induce (A : Set V)).edgeSet.ncard) :=
          Nat.mul_lt_mul_of_pos_left h50eA (by norm_num)
        have h3 : r1 * (37 * n ^ 2) < r1 * (1250 * (G.induce (A : Set V)).edgeSet.ncard) := by linarith
        have h4 := Nat.lt_of_mul_lt_mul_left h3
        omega
      · -- Subcase 2b: 25 * a0 < 37 * r1
        have ha0_gt : 37 * r < 12 * a0 := by omega
        have ha0m1_gt : 37 * (r - 1) < 12 * (a0 - 1) := by omega
        have hdeg_A0 : ∀ v : V, #(A0.filter (G.Adj v)) ≤ r - 1 := by
          intro v
          have hmem : A0.filter (G.Adj v) ∈ indepA0 :=
            Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
              filter_adj_indep hTF A0 v⟩
          have := hJ_max _ hmem
          omega
        have heA0B : ∑ w ∈ A0, #(B.filter (G.Adj w)) ≤ b * (r - 1) := by
          have hswap : ∑ w ∈ A0, #(B.filter (G.Adj w)) = ∑ v ∈ B, #(A0.filter (G.Adj v)) := by
            simp_rw [Finset.card_filter]; rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro v _
            apply Finset.sum_congr rfl; intro w _; simp [G.adj_comm]
          rw [hswap]
          calc ∑ v ∈ B, #(A0.filter (G.Adj v))
              ≤ ∑ _v ∈ B, (r - 1) := Finset.sum_le_sum (fun v _ => hdeg_A0 v)
            _ = b * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
        have hdA0 : ∑ w ∈ A0, #(A0.filter (G.Adj w)) ≤ a0 * (r - 1) := by
          calc ∑ w ∈ A0, #(A0.filter (G.Adj w))
              ≤ ∑ _w ∈ A0, (r - 1) := Finset.sum_le_sum (fun w _ => hdeg_A0 w)
            _ = a0 * (r - 1) := by rw [Finset.sum_const, smul_eq_mul]
        have hBavg := avg_union_gt G hdisj_BA0 hr2 (by omega) ha0_ge2 (T := n ^ 2) (fun S hS => by
          have hcard : #(B ∪ S) = k := by
            rw [Finset.card_union_of_disjoint (hdisj_BA0.mono_right (Finset.mem_powersetCard.mp hS).1),
              (Finset.mem_powersetCard.mp hS).2]; omega
          have h50 := hH ((B ∪ S : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard]; omega)
          omega)
        have h2B := two_mul_induce_edgeSet_ncard G B
        rw [← h2B] at hBavg
        -- Convert to ℚ cleanly
        have hBavg_q : (n : ℚ) ^ 2 * (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) <
            50 * (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((G.induce (B : Set V)).edgeSet.ncard : ℚ) +
            50 * (r : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((b : ℚ) * ((r - 1 : ℕ) : ℚ)) +
            25 * (r : ℚ) * ((r - 1 : ℕ) : ℚ) * ((a0 : ℚ) * ((r - 1 : ℕ) : ℚ)) := by
          have h1 : n ^ 2 * a0 * (a0 - 1) <
              25 * (a0 * (a0 - 1) * (2 * (G.induce (B : Set V)).edgeSet.ncard) +
                2 * r * (a0 - 1) * (b * (r - 1)) +
                r * (r - 1) * (a0 * (r - 1))) := by
            have hm1 : 2 * r * (a0 - 1) * (∑ w ∈ A0, #(B.filter (G.Adj w))) ≤
                2 * r * (a0 - 1) * (b * (r - 1)) := Nat.mul_le_mul_left _ heA0B
            have hm2 : r * (r - 1) * (∑ w ∈ A0, #(A0.filter (G.Adj w))) ≤
                r * (r - 1) * (a0 * (r - 1)) := Nat.mul_le_mul_left _ hdA0
            change n ^ 2 * a0 * (a0 - 1) <
              25 * (a0 * (a0 - 1) * (2 * (G.induce (B : Set V)).edgeSet.ncard) +
                2 * r * (a0 - 1) * (∑ w ∈ A0, #(B.filter (G.Adj w))) +
                r * (r - 1) * (∑ u ∈ A0, #(A0.filter (G.Adj u)))) at hBavg
            omega
          have h1_exp : n ^ 2 * a0 * (a0 - 1) <
              50 * a0 * (a0 - 1) * (G.induce (B : Set V)).edgeSet.ncard +
              50 * r * (a0 - 1) * (b * (r - 1)) +
              25 * r * (r - 1) * (a0 * (r - 1)) := by
            have hring_nat : 25 * (a0 * (a0 - 1) * (2 * (G.induce (B : Set V)).edgeSet.ncard) +
                2 * r * (a0 - 1) * (b * (r - 1)) +
                r * (r - 1) * (a0 * (r - 1))) =
                50 * a0 * (a0 - 1) * (G.induce (B : Set V)).edgeSet.ncard +
                50 * r * (a0 - 1) * (b * (r - 1)) +
                25 * r * (r - 1) * (a0 * (r - 1)) := by ring
            rw [← hring_nat]; exact h1
          exact_mod_cast h1_exp
        have ha0_pos_q : (0 : ℚ) < (a0 : ℚ) := Nat.cast_pos.mpr (by omega)
        have ha0m1_pos_q : (0 : ℚ) < ((a0 - 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
        have ha0_gt_q : 37 * (r : ℚ) < 12 * (a0 : ℚ) := by exact_mod_cast ha0_gt
        have ha0m1_gt_q : 37 * ((r - 1 : ℕ) : ℚ) < 12 * ((a0 - 1 : ℕ) : ℚ) := by exact_mod_cast ha0m1_gt
        have hrm1_le : ((r - 1 : ℕ) : ℚ) ≤ (r : ℚ) := by exact_mod_cast (show r - 1 ≤ r by omega)
        have hterm1 : 50 * (r : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((b : ℚ) * ((r - 1 : ℕ) : ℚ)) ≤
            (600 / 37) * (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((r : ℚ) * (b : ℚ)) := by
          have hb0 : (0 : ℚ) ≤ (b : ℚ) := Nat.cast_nonneg b
          have hr0q : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
          have hrm1_0 : (0 : ℚ) ≤ ((r - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
          have h1 : 37 * ((r - 1 : ℕ) : ℚ) ≤ 12 * (a0 : ℚ) := by linarith only [ha0_gt_q, hrm1_le]
          have h2 : 50 * (r : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((b : ℚ) * (37 * ((r - 1 : ℕ) : ℚ))) ≤
              50 * (r : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((b : ℚ) * (12 * (a0 : ℚ))) := by
            have hfac : 0 ≤ 50 * (r : ℚ) * ((a0 - 1 : ℕ) : ℚ) * (b : ℚ) := by positivity
            nlinarith only [h1, hfac]
          linarith only [h2]
        have hterm2 : 25 * (r : ℚ) * ((r - 1 : ℕ) : ℚ) * ((a0 : ℚ) * ((r - 1 : ℕ) : ℚ)) ≤
            (300 / 37) * (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((r : ℚ) ^ 2) := by
          have hr0q : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
          have hrm1_0 : (0 : ℚ) ≤ ((r - 1 : ℕ) : ℚ) := Nat.cast_nonneg _
          have h2 : 25 * (r : ℚ) * (a0 : ℚ) * ((r - 1 : ℕ) : ℚ) * (37 * ((r - 1 : ℕ) : ℚ)) ≤
              25 * (r : ℚ) * (a0 : ℚ) * (r : ℚ) * (12 * ((a0 - 1 : ℕ) : ℚ)) := by
            have h1 : ((r - 1 : ℕ) : ℚ) * (37 * ((r - 1 : ℕ) : ℚ)) ≤ (r : ℚ) * (12 * ((a0 - 1 : ℕ) : ℚ)) := by
              nlinarith only [hrm1_le, ha0m1_gt_q, hrm1_0, hr0q, ha0m1_pos_q]
            have hfac : 0 ≤ 25 * (r : ℚ) * (a0 : ℚ) := by positivity
            nlinarith only [h1, hfac]
          linarith only [h2]
        have h2br : 2 * (b : ℚ) + (r : ℚ) ≤ (n : ℚ) := by
          have : 2 * b + r ≤ n := by omega
          exact_mod_cast this
        have hprod_pos : (0 : ℚ) < (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) := mul_pos ha0_pos_q ha0m1_pos_q
        have heB_q : (n : ℚ) ^ 2 / 50 - 6 * (r : ℚ) * (n : ℚ) / 37 <
            ((G.induce (B : Set V)).edgeSet.ncard : ℚ) := by
          have h1 : (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) * ((n : ℚ) ^ 2 - 300 * (r : ℚ) * (n : ℚ) / 37) <
              (a0 : ℚ) * ((a0 - 1 : ℕ) : ℚ) * (50 * ((G.induce (B : Set V)).edgeSet.ncard : ℚ)) := by
            have h2 : (600 / 37) * ((r : ℚ) * (b : ℚ)) + (300 / 37) * ((r : ℚ) ^ 2) ≤
                (300 / 37) * ((r : ℚ) * (n : ℚ)) := by
              have hr0q : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
              nlinarith only [h2br, hr0q]
            have h3 := mul_le_mul_of_nonneg_left h2 hprod_pos.le
            linarith only [hBavg_q, hterm1, hterm2, h3]
          have h4 := lt_of_mul_lt_mul_left h1 hprod_pos.le
          linarith only [h4]
        have heA_q : (n : ℚ) ^ 2 / 50 + 2 * (n : ℚ) * (r : ℚ) / 25 <
            ((G.induce (A : Set V)).edgeSet.ncard : ℚ) := by
          have hruq : (r : ℚ) ≤ (u : ℚ) := by exact_mod_cast hru
          have hnq0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
          have hu2 : (0 : ℚ) ≤ 4 * (u : ℚ) ^ 2 / 25 := by positivity
          nlinarith only [hFA, hruq, hnq0, hu2]
        have h10r : 10 * (r : ℚ) ≤ (n : ℚ) := by
          have : 10 * r ≤ n := by omega
          exact_mod_cast this
        have hnq0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
        have hfin : 37 * (n : ℚ) ^ 2 <
            1250 * (((G.induce (A : Set V)).edgeSet.ncard : ℚ) + ((G.induce (B : Set V)).edgeSet.ncard : ℚ)) := by
          nlinarith only [heA_q, heB_q, h10r, hnq0]
        exact_mod_cast hfin
  · -- Case 0b: 10 * u > n
    have hFA := induce_edgeSet_gt_twoPiece G hTF hH A ha_ge_k
    rw [if_neg hu10] at hFA
    have hu_gt10 : (n : ℚ) < 10 * (u : ℚ) := by exact_mod_cast (show n < 10 * u by omega)
    have hnq0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
    have hQ2_gt : 37 * (n : ℚ) ^ 2 / 1250 ≤
        401 * (n : ℚ) ^ 2 / 20000 + 83 * (n : ℚ) * (u : ℚ) / 1000 + (u : ℚ) ^ 2 / 8 := by
      nlinarith only [hu_gt10, hnq0]
    have hfin : 37 * (n : ℚ) ^ 2 < 1250 * ((G.induce (A : Set V)).edgeSet.ncard : ℚ) := by
      linarith only [hFA, hQ2_gt]
    have hnat : 37 * n ^ 2 < 1250 * (G.induce (A : Set V)).edgeSet.ncard := by exact_mod_cast hfin
    omega

/-- Theorem 2 (Sharp Bipartite Deletion Lower Bound): `37 * n^2 < 1250 * (e(G[A]) + e(G[A^c]))`. -/
theorem bipartite_del_gt {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (A : Set V) :
    37 * Fintype.card V ^ 2 <
      1250 * ((G.induce A).edgeSet.ncard + (G.induce Aᶜ).edgeSet.ncard) := by
  classical
  let Af : Finset V := A.toFinset
  let Bf : Finset V := Aᶜ.toFinset
  have hAf_coe : (Af : Set V) = A := Set.coe_toFinset A
  have hBf_coe : (Bf : Set V) = Aᶜ := Set.coe_toFinset Aᶜ
  have hdisj : Disjoint Af Bf := by
    rw [Finset.disjoint_left]; intro x hxA hxB
    exact (Set.mem_toFinset.mp hxB) (Set.mem_toFinset.mp hxA)
  have hcov : Af ∪ Bf = Finset.univ := by
    ext x; simp only [Af, Bf, Finset.mem_union, Set.mem_toFinset, Set.mem_compl_iff, Finset.mem_univ, iff_true]
    exact em (x ∈ A)
  rw [← hBf_coe, ← hAf_coe]
  by_cases hle : #Bf ≤ #Af
  · exact bipartite_del_gt_ordered G hTF hH Af Bf hdisj hcov hle
  · rw [add_comm]
    exact bipartite_del_gt_ordered G hTF hH Bf Af hdisj.symm (by rw [Finset.union_comm]; exact hcov) (by omega)

end BipartiteDeletion

section ThreeColorableCore

/-- Helper: edge count between two disjoint independent Finsets `X, Y` satisfies `50 * (k - #X) * e(X, Y) > #Y * n^2`. -/
lemma cross_edges_gt_of_indep {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    {X Y : Finset V} (hdisj : Disjoint X Y)
    (hX : ∀ u ∈ X, ∀ v ∈ X, ¬ G.Adj u v) (hY : ∀ u ∈ Y, ∀ v ∈ Y, ¬ G.Adj u v)
    (hXk : #X < Fintype.card V / 2) (hXY : Fintype.card V / 2 ≤ #X + #Y) :
    #Y * Fintype.card V ^ 2 < 50 * (Fintype.card V / 2 - #X) * (∑ w ∈ Y, #(X.filter (G.Adj w))) := by
  set n := Fintype.card V
  set k := n / 2
  set r := k - #X
  have hr1 : 1 ≤ r := by omega
  have hrY : r ≤ #Y := by omega
  have hne : (Y.powersetCard r).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have : (#Y).choose r = 0 := by rw [← Finset.card_powersetCard, hemp, Finset.card_empty]
    have := Nat.choose_pos hrY; omega
  have hper : ∀ S ∈ Y.powersetCard r, n ^ 2 < 50 * ∑ w ∈ S, #(X.filter (G.Adj w)) := by
    intro S hS
    have hSY := (Finset.mem_powersetCard.mp hS).1
    have hScard := (Finset.mem_powersetCard.mp hS).2
    have hcard : #(X ∪ S) = k := by rw [Finset.card_union_of_disjoint (hdisj.mono_right hSY), hScard]; omega
    have h50 := hH ((X ∪ S : Finset V) : Set V) (by rw [Set.ncard_coe_finset, hcard]; omega)
    have h2 := two_mul_induce_edgeSet_ncard G (X ∪ S)
    have hsum := sum_adj_union_indep G (hdisj.mono_right hSY) hX
    have hSS0 : ∑ u ∈ S, #(S.filter (G.Adj u)) = 0 := by
      apply Finset.sum_eq_zero; intro u hu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hY u (hSY hu) v (hSY hv)
    omega
  have hsum_lt := Finset.sum_lt_sum_of_nonempty hne hper
  have hsum_eq : ∑ S ∈ Y.powersetCard r, ∑ w ∈ S, #(X.filter (G.Adj w)) =
      (#Y - 1).choose (r - 1) * ∑ w ∈ Y, #(X.filter (G.Adj w)) := by
    calc ∑ S ∈ Y.powersetCard r, ∑ w ∈ S, #(X.filter (G.Adj w))
        = ∑ S ∈ Y.powersetCard r, ∑ w ∈ Y, if w ∈ S then #(X.filter (G.Adj w)) else 0 := by
          apply Finset.sum_congr rfl; intro S hS
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.mpr (Finset.mem_powersetCard.mp hS).1]
      _ = ∑ w ∈ Y, ∑ S ∈ Y.powersetCard r, if w ∈ S then #(X.filter (G.Adj w)) else 0 := Finset.sum_comm
      _ = ∑ w ∈ Y, #((Y.powersetCard r).filter (w ∈ ·)) * #(X.filter (G.Adj w)) := by
          apply Finset.sum_congr rfl; intro w _; rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      _ = ∑ w ∈ Y, (#Y - 1).choose (r - 1) * #(X.filter (G.Adj w)) := by
          apply Finset.sum_congr rfl; intro w hw; rw [card_powersetCard_mem Y hw hr1]
      _ = (#Y - 1).choose (r - 1) * ∑ w ∈ Y, #(X.filter (G.Adj w)) := (Finset.mul_sum _ _ _).symm
  rw [← Finset.mul_sum, hsum_eq, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul] at hsum_lt
  have hc1 : (#Y).choose r * r = #Y * (#Y - 1).choose (r - 1) := by
    have := Nat.add_one_mul_choose_eq (#Y - 1) (r - 1)
    rw [show #Y - 1 + 1 = #Y by omega, show r - 1 + 1 = r by omega] at this
    linarith
  have hmul := Nat.mul_lt_mul_of_pos_left hsum_lt (by omega : 0 < #Y)
  have hkey : (#Y).choose r * (#Y * n ^ 2) <
      (#Y).choose r * (50 * r * ∑ w ∈ Y, #(X.filter (G.Adj w))) := by
    have hL : #Y * ((#Y).choose r * n ^ 2) = (#Y).choose r * (#Y * n ^ 2) := by ring
    have hR : #Y * (50 * ((#Y - 1).choose (r - 1) * ∑ w ∈ Y, #(X.filter (G.Adj w)))) =
        (#Y).choose r * (50 * r * ∑ w ∈ Y, #(X.filter (G.Adj w))) := by
      calc #Y * (50 * ((#Y - 1).choose (r - 1) * ∑ w ∈ Y, #(X.filter (G.Adj w))))
          = 50 * (#Y * (#Y - 1).choose (r - 1)) * ∑ w ∈ Y, #(X.filter (G.Adj w)) := by ring
        _ = 50 * ((#Y).choose r * r) * ∑ w ∈ Y, #(X.filter (G.Adj w)) := by rw [← hc1]
        _ = _ := by ring
    linarith only [hmul, hL, hR]
  exact Nat.lt_of_mul_lt_mul_left hkey

/-- Lemma 3.1: Every 3-colorable triangle-free counterexample satisfies `3 * n^2 < 25 * e(G)`. -/
theorem three_col_edges_gt {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3) (h3 : G.Colorable 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2) :
    3 * Fintype.card V ^ 2 < 25 * G.edgeSet.ncard := by
  classical
  set n := Fintype.card V
  set k := n / 2
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  obtain ⟨c⟩ := h3
  let C : Fin 3 → Finset V := fun i => Finset.univ.filter (fun v => c v = i)
  have hC_indep : ∀ i : Fin 3, ∀ u ∈ C i, ∀ v ∈ C i, ¬ G.Adj u v := by
    intro i u hu v hv hadj
    exact c.valid hadj (by rw [(Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hv).2])
  have hC_lt : ∀ i : Fin 3, 5 * #(C i) < 2 * n := by
    intro i
    have h := five_mul_indep_lt_two_mul_card G hTF hH (C i : Set V) (by
      intro u hu v hv _ hadj; exact hC_indep i u (Finset.mem_coe.mp hu) v (Finset.mem_coe.mp hv) hadj)
    rwa [Set.ncard_coe_finset] at h
  have hC_disj : ∀ i j : Fin 3, i ≠ j → Disjoint (C i) (C j) := by
    intro i j hij; rw [Finset.disjoint_left]; intro v hvi hvj
    exact hij ((Finset.mem_filter.mp hvi).2.symm.trans (Finset.mem_filter.mp hvj).2)
  have hC_sum : #(C 0) + #(C 1) + #(C 2) = n := by
    have hu : C 0 ∪ C 1 ∪ C 2 = Finset.univ := by
      ext v; simp only [C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      generalize c v = x; fin_cases x <;> simp
    have hd01 : Disjoint (C 0) (C 1) := hC_disj 0 1 (by decide)
    have hd012 : Disjoint (C 0 ∪ C 1) (C 2) :=
      Finset.disjoint_union_left.mpr ⟨hC_disj 0 2 (by decide), hC_disj 1 2 (by decide)⟩
    rw [← Finset.card_union_of_disjoint hd01, ← Finset.card_union_of_disjoint hd012, hu, Finset.card_univ]
  -- Sort the 3 indices so #(C i0) >= #(C i1) >= #(C i2)
  have hex_ord : ∃ i0 i1 i2 : Fin 3, i0 ≠ i1 ∧ i0 ≠ i2 ∧ i1 ≠ i2 ∧
      #(C i2) ≤ #(C i1) ∧ #(C i1) ≤ #(C i0) ∧ #(C i0) + #(C i1) + #(C i2) = n := by
    by_cases h01 : #(C 1) ≤ #(C 0)
    · by_cases h12 : #(C 2) ≤ #(C 1)
      · exact ⟨0, 1, 2, by decide, by decide, by decide, h12, h01, hC_sum⟩
      · by_cases h02 : #(C 2) ≤ #(C 0)
        · exact ⟨0, 2, 1, by decide, by decide, by decide, by omega, h02, by omega⟩
        · exact ⟨2, 0, 1, by decide, by decide, by decide, h01, by omega, by omega⟩
    · by_cases h02 : #(C 2) ≤ #(C 0)
      · exact ⟨1, 0, 2, by decide, by decide, by decide, h02, by omega, by omega⟩
      · by_cases h12 : #(C 2) ≤ #(C 1)
        · exact ⟨1, 2, 0, by decide, by decide, by decide, by omega, h12, by omega⟩
        · exact ⟨2, 1, 0, by decide, by decide, by decide, by omega, by omega, by omega⟩
  obtain ⟨i0, i1, i2, h01, h02, h12, hcb, hba, habc⟩ := hex_ord
  set A := C i0; set B := C i1; set D := C i2
  set a := #A; set b := #B; set d := #D
  have ha5 : 5 * a < 2 * n := hC_lt i0
  have hb5 : 5 * b < 2 * n := hC_lt i1
  have hd5 : 5 * d < 2 * n := hC_lt i2
  have hcb' : d ≤ b := hcb
  have hba' : b ≤ a := hba
  have habc' : a + b + d = n := habc
  have hk_lo : 2 * k ≤ n := by omega
  have hk_hi : n ≤ 2 * k + 1 := by omega
  have heAB := cross_edges_gt_of_indep G hH (hC_disj i0 i1 h01) (hC_indep i0) (hC_indep i1)
    (by change a < k; omega) (by change k ≤ a + b; omega)
  have heAD := cross_edges_gt_of_indep G hH (hC_disj i0 i2 h02) (hC_indep i0) (hC_indep i2)
    (by change a < k; omega) (by change k ≤ a + d; omega)
  have heBD := cross_edges_gt_of_indep G hH (hC_disj i1 i2 h12) (hC_indep i1) (hC_indep i2)
    (by change b < k; omega) (by change k ≤ b + d; omega)
  -- Show e(G) = e(A, B) + e(A, D) + e(B, D)
  set eAB := ∑ w ∈ B, #(A.filter (G.Adj w))
  set eAD := ∑ w ∈ D, #(A.filter (G.Adj w))
  set eBD := ∑ w ∈ D, #(B.filter (G.Adj w))
  have hedge_sum : G.edgeSet.ncard = eAB + eAD + eBD := by
    have hcov : A ∪ B ∪ D = Finset.univ := by
      ext v; simp only [A, B, D, C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      have hall : ∀ x : Fin 3, x = i0 ∨ x = i1 ∨ x = i2 := by
        fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> first | contradiction | (intro x; fin_cases x <;> simp)
      rcases hall (c v) with h | h | h <;> simp [h]
    have hdAB : Disjoint A B := hC_disj i0 i1 h01
    have hdABD : Disjoint (A ∪ B) D := Finset.disjoint_union_left.mpr ⟨hC_disj i0 i2 h02, hC_disj i1 i2 h12⟩
    have h2G : 2 * G.edgeSet.ncard = ∑ u ∈ A ∪ B ∪ D, #((A ∪ B ∪ D).filter (G.Adj u)) := by
      rw [hcov]
      have h1 := two_mul_induce_edgeSet_ncard G (Finset.univ : Finset V)
      have h2 : (G.induce ((Finset.univ : Finset V) : Set V)).edgeSet.ncard = G.edgeSet.ncard := by
        have hcard : G.edgeSet.ncard = #G.edgeFinset := by rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
        rw [← Nat.mul_left_cancel_iff (show 0 < 2 by norm_num), h1, hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
        apply Finset.sum_congr rfl; intro u _
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset]; congr 1; ext v; simp
      omega
    have hstep1 := sum_adj_union G hdABD
    have hstep2 := sum_adj_union_indep G hdAB (hC_indep i0)
    have hBB0 : ∑ u ∈ B, #(B.filter (G.Adj u)) = 0 := by
      apply Finset.sum_eq_zero; intro u hu; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun v hv => hC_indep i1 u hu v hv
    have hDD0 : ∑ u ∈ D, #(D.filter (G.Adj u)) = 0 := by
      apply Finset.sum_eq_zero; intro u hu; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun v hv => hC_indep i2 u hu v hv
    have hcross : ∑ w ∈ D, #((A ∪ B).filter (G.Adj w)) = eAD + eBD := by
      have h1 : ∀ w, #((A ∪ B).filter (G.Adj w)) = #(A.filter (G.Adj w)) + #(B.filter (G.Adj w)) := fun w => by
        rw [Finset.filter_union, Finset.card_union_of_disjoint
          (hdAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      simp_rw [h1, Finset.sum_add_distrib]; rfl
    omega
  -- Pure rational 4-line proof: 50*(eAB + eAD + eBD)/n^2 > (b+d)/(k-a) + d/(k-b) >= 6
  have haq : (n : ℚ) ≤ 3 * (a : ℚ) := by exact_mod_cast (show n ≤ 3 * a by omega)
  have hka_pos : (0 : ℚ) < ((k - a : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
  have hkb_pos : (0 : ℚ) < ((k - b : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
  have hka_le : ((k - a : ℕ) : ℚ) ≤ (n : ℚ) / 2 - (a : ℚ) := by
    have : 2 * (k - a) + 2 * a ≤ n := by omega
    have hq : 2 * ((k - a : ℕ) : ℚ) + 2 * (a : ℚ) ≤ (n : ℚ) := by exact_mod_cast this
    linarith
  have hkb_le : ((k - b : ℕ) : ℚ) ≤ (n : ℚ) / 2 - (b : ℚ) := by
    have : 2 * (k - b) + 2 * b ≤ n := by omega
    have hq : 2 * ((k - b : ℕ) : ℚ) + 2 * (b : ℚ) ≤ (n : ℚ) := by exact_mod_cast this
    linarith
  have h1q : ((b : ℚ) + (d : ℚ)) * (n : ℚ) ^ 2 < 50 * ((k - a : ℕ) : ℚ) * ((eAB : ℚ) + (eAD : ℚ)) := by
    have : (b + d) * n ^ 2 < 50 * (k - a) * (eAB + eAD) := by nlinarith only [heAB, heAD]
    exact_mod_cast this
  have h2q : (d : ℚ) * (n : ℚ) ^ 2 < 50 * ((k - b : ℕ) : ℚ) * (eBD : ℚ) := by exact_mod_cast heBD
  have hbd_eq : (b : ℚ) + (d : ℚ) = (n : ℚ) - (a : ℚ) := by
    have hq : (a : ℚ) + (b : ℚ) + (d : ℚ) = (n : ℚ) := by exact_mod_cast habc'
    linarith only [hq]
  have hna_pos : (0 : ℚ) < (n : ℚ) / 2 - (a : ℚ) := by linarith only [hka_pos, hka_le]
  have hnb_pos : (0 : ℚ) < (n : ℚ) / 2 - (b : ℚ) := by linarith only [hkb_pos, hkb_le]
  have ha_pos : (0 : ℚ) < (a : ℚ) := by linarith only [haq, show (0 : ℚ) < (n : ℚ) by exact_mod_cast (by omega : 0 < n)]
  have hterm1 : ((n : ℚ) - (a : ℚ)) / ((n : ℚ) / 2 - (a : ℚ)) * (n : ℚ) ^ 2 < 50 * ((eAB : ℚ) + (eAD : ℚ)) := by
    have hdiv1 : ((n : ℚ) - (a : ℚ)) * (n : ℚ) ^ 2 / ((k - a : ℕ) : ℚ) < 50 * ((eAB : ℚ) + (eAD : ℚ)) := by
      rw [div_lt_iff₀ hka_pos]; rw [← hbd_eq]; linarith only [h1q]
    have hdiv2 : ((n : ℚ) - (a : ℚ)) * (n : ℚ) ^ 2 / ((n : ℚ) / 2 - (a : ℚ)) ≤
        ((n : ℚ) - (a : ℚ)) * (n : ℚ) ^ 2 / ((k - a : ℕ) : ℚ) :=
      div_le_div_of_nonneg_left (mul_nonneg (by linarith only [hna_pos, ha_pos]) (sq_nonneg _))
        hka_pos hka_le
    have hL : ((n : ℚ) - (a : ℚ)) / ((n : ℚ) / 2 - (a : ℚ)) * (n : ℚ) ^ 2 =
        ((n : ℚ) - (a : ℚ)) * (n : ℚ) ^ 2 / ((n : ℚ) / 2 - (a : ℚ)) := by ring
    linarith only [hdiv1, hdiv2, hL]
  have hterm2 : ((n : ℚ) - (a : ℚ)) / (a : ℚ) * (n : ℚ) ^ 2 < 50 * (eBD : ℚ) := by
    have hdiv1 : (d : ℚ) * (n : ℚ) ^ 2 / ((k - b : ℕ) : ℚ) < 50 * (eBD : ℚ) := by
      rw [div_lt_iff₀ hkb_pos]; linarith only [h2q]
    have hdiv2 : (d : ℚ) * (n : ℚ) ^ 2 / ((n : ℚ) / 2 - (b : ℚ)) ≤ (d : ℚ) * (n : ℚ) ^ 2 / ((k - b : ℕ) : ℚ) :=
      div_le_div_of_nonneg_left (by positivity) hkb_pos hkb_le
    have hb_ge : ((n : ℚ) - (a : ℚ)) / 2 ≤ (b : ℚ) := by
      have : n - a ≤ 2 * b := by omega
      have hq : (n : ℚ) - (a : ℚ) ≤ 2 * (b : ℚ) := by linarith only [hbd_eq, show (d : ℚ) ≤ (b : ℚ) by exact_mod_cast hcb]
      linarith
    have hfrac : ((n : ℚ) - (a : ℚ)) / (a : ℚ) ≤ (d : ℚ) / ((n : ℚ) / 2 - (b : ℚ)) := by
      rw [div_le_div_iff₀ ha_pos hnb_pos]
      have hd_eq : (d : ℚ) = (n : ℚ) - (a : ℚ) - (b : ℚ) := by linarith only [hbd_eq]
      rw [hd_eq]; nlinarith only [hb_ge, hna_pos]
    have hmul := mul_le_mul_of_nonneg_right hfrac (sq_nonneg (n : ℚ))
    have hR : (d : ℚ) / ((n : ℚ) / 2 - (b : ℚ)) * (n : ℚ) ^ 2 = (d : ℚ) * (n : ℚ) ^ 2 / ((n : ℚ) / 2 - (b : ℚ)) := by ring
    linarith only [hdiv1, hdiv2, hmul, hR]
  have hsum_ge6 : (6 : ℚ) ≤ ((n : ℚ) - (a : ℚ)) / ((n : ℚ) / 2 - (a : ℚ)) + ((n : ℚ) - (a : ℚ)) / (a : ℚ) := by
    have hcomb : ((n : ℚ) - (a : ℚ)) / ((n : ℚ) / 2 - (a : ℚ)) + ((n : ℚ) - (a : ℚ)) / (a : ℚ) - 6 =
        (3 * (a : ℚ) - (n : ℚ)) * (4 * (a : ℚ) - (n : ℚ)) / ((a : ℚ) * ((n : ℚ) - 2 * (a : ℚ))) := by
      have h1 : (n : ℚ) / 2 - (a : ℚ) ≠ 0 := by linarith only [hna_pos]
      have h2 : (n : ℚ) - 2 * (a : ℚ) ≠ 0 := by linarith only [hna_pos]
      have h3 : (a : ℚ) * ((n : ℚ) - 2 * (a : ℚ)) ≠ 0 := mul_ne_zero ha_pos.ne' h2
      rw [eq_div_iff h3]
      have hmul1 : ((n : ℚ) - (a : ℚ)) / ((n : ℚ) / 2 - (a : ℚ)) * ((a : ℚ) * ((n : ℚ) - 2 * (a : ℚ))) =
          2 * (a : ℚ) * ((n : ℚ) - (a : ℚ)) := by
        rw [show (n : ℚ) - 2 * (a : ℚ) = 2 * ((n : ℚ) / 2 - (a : ℚ)) by ring]
        have := div_mul_cancel₀ ((n : ℚ) - (a : ℚ)) h1
        linear_combination 2 * (a : ℚ) * this
      have hmul2 : ((n : ℚ) - (a : ℚ)) / (a : ℚ) * ((a : ℚ) * ((n : ℚ) - 2 * (a : ℚ))) =
          ((n : ℚ) - (a : ℚ)) * ((n : ℚ) - 2 * (a : ℚ)) := by
        have := div_mul_cancel₀ ((n : ℚ) - (a : ℚ)) ha_pos.ne'
        linear_combination ((n : ℚ) - 2 * (a : ℚ)) * this
      linear_combination hmul1 + hmul2
    have hnn : (0 : ℚ) ≤ (3 * (a : ℚ) - (n : ℚ)) * (4 * (a : ℚ) - (n : ℚ)) / ((a : ℚ) * ((n : ℚ) - 2 * (a : ℚ))) :=
      div_nonneg (mul_nonneg (by linarith only [haq]) (by linarith only [haq, ha_pos]))
        (mul_nonneg ha_pos.le (by linarith only [hna_pos]))
    linarith only [hcomb, hnn]
  have hfin : 6 * (n : ℚ) ^ 2 < 50 * ((eAB : ℚ) + (eAD : ℚ) + (eBD : ℚ)) := by
    have := mul_le_mul_of_nonneg_right hsum_ge6 (sq_nonneg (n : ℚ))
    linarith only [hterm1, hterm2, this]
  have hfin_nat : 6 * n ^ 2 < 50 * (eAB + eAD + eBD) := by exact_mod_cast hfin
  rw [hedge_sum]; omega

/-- Lemma 3.2: Every color class of any 3-coloring of a counterexample satisfies `37 * n < 250 * |C_i|`. -/
theorem three_col_class_gt {V : Type} [Fintype V] (G : SimpleGraph V)
    (hTF : G.CliqueFree 3)
    (hH : ∀ V' : Set V, 2 * V'.ncard + 1 ≥ Fintype.card V →
      50 * (G.induce V').edgeSet.ncard > Fintype.card V ^ 2)
    (c : G.Coloring (Fin 3)) (i : Fin 3) :
    37 * Fintype.card V < 250 * {v : V | c v = i}.ncard := by
  classical
  set n := Fintype.card V
  have hn12 : 12 ≤ n := twelve_le_card G hTF hH
  -- Pick the two other colors j1, j2 ≠ i
  have hex : ∃ j1 j2 : Fin 3, j1 ≠ i ∧ j2 ≠ i ∧ j1 ≠ j2 ∧ ∀ x : Fin 3, x = i ∨ x = j1 ∨ x = j2 := by
    fin_cases i
    · exact ⟨1, 2, by decide, by decide, by decide, fun x => by fin_cases x <;> simp⟩
    · exact ⟨0, 2, by decide, by decide, by decide, fun x => by fin_cases x <;> simp⟩
    · exact ⟨0, 1, by decide, by decide, by decide, fun x => by fin_cases x <;> simp⟩
  obtain ⟨j1, j2, hj1i, hj2i, hj12, hall⟩ := hex
  let Ci : Finset V := Finset.univ.filter (fun v => c v = i)
  let C1 : Finset V := Finset.univ.filter (fun v => c v = j1)
  let C2 : Finset V := Finset.univ.filter (fun v => c v = j2)
  have hCi_ind : ∀ u ∈ Ci, ∀ v ∈ Ci, ¬ G.Adj u v := fun u hu v hv h =>
    c.valid h ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  have hC1_ind : ∀ u ∈ C1, ∀ v ∈ C1, ¬ G.Adj u v := fun u hu v hv h =>
    c.valid h ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  have hC2_ind : ∀ u ∈ C2, ∀ v ∈ C2, ¬ G.Adj u v := fun u hu v hv h =>
    c.valid h ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
  have hd_i1 : Disjoint Ci C1 := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact hj1i ((Finset.mem_filter.mp h2).2.symm.trans (Finset.mem_filter.mp h1).2)
  have hd_i2 : Disjoint Ci C2 := by
    rw [Finset.disjoint_left]; intro v h1 h2
    exact hj2i ((Finset.mem_filter.mp h2).2.symm.trans (Finset.mem_filter.mp h1).2)
  have h1_compl : ((Ci ∪ C1 : Finset V) : Set V)ᶜ = (C2 : Set V) := by
    ext v; simp only [Ci, C1, C2, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rcases hall (c v) with h0 | h0 | h0 <;> first | exact h0 | exact (h (Or.inl h0)).elim | exact (h (Or.inr h0)).elim
    · rintro h (h0 | h0)
      · exact hj2i (h.symm.trans h0)
      · exact hj12 (h0.symm.trans h)
  have h2_compl : ((Ci ∪ C2 : Finset V) : Set V)ᶜ = (C1 : Set V) := by
    ext v; simp only [Ci, C1, C2, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; rcases hall (c v) with h0 | h0 | h0 <;> first | exact h0 | exact (h (Or.inl h0)).elim | exact (h (Or.inr h0)).elim
    · rintro h (h0 | h0)
      · exact hj1i (h.symm.trans h0)
      · exact hj12 (h.symm.trans h0)
  have hD1 := bipartite_del_gt G hTF hH ((Ci ∪ C1 : Finset V) : Set V)
  have hD2 := bipartite_del_gt G hTF hH ((Ci ∪ C2 : Finset V) : Set V)
  rw [h1_compl] at hD1; rw [h2_compl] at hD2
  have heC2_0 : (G.induce (C2 : Set V)).edgeSet.ncard = 0 := by
    have h := two_mul_induce_edgeSet_ncard G C2
    have h0 : ∑ u ∈ C2, #(C2.filter (G.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hC2_ind u hu v hv)
    omega
  have heC1_0 : (G.induce (C1 : Set V)).edgeSet.ncard = 0 := by
    have h := two_mul_induce_edgeSet_ncard G C1
    have h0 : ∑ u ∈ C1, #(C1.filter (G.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hC1_ind u hu v hv)
    omega
  rw [heC2_0, add_zero] at hD1
  rw [heC1_0, add_zero] at hD2
  have he_i1 : (G.induce ((Ci ∪ C1 : Finset V) : Set V)).edgeSet.ncard = ∑ u ∈ Ci, #(C1.filter (G.Adj u)) := by
    have h := two_mul_induce_edgeSet_ncard G (Ci ∪ C1)
    have hs := sum_adj_union_indep G hd_i1.symm hC1_ind
    rw [Finset.union_comm] at hs
    have h0 : ∑ u ∈ Ci, #(Ci.filter (G.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hCi_ind u hu v hv)
    omega
  have he_i2 : (G.induce ((Ci ∪ C2 : Finset V) : Set V)).edgeSet.ncard = ∑ u ∈ Ci, #(C2.filter (G.Adj u)) := by
    have h := two_mul_induce_edgeSet_ncard G (Ci ∪ C2)
    have hs := sum_adj_union_indep G hd_i2.symm hC2_ind
    rw [Finset.union_comm] at hs
    have h0 : ∑ u ∈ Ci, #(Ci.filter (G.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hCi_ind u hu v hv)
    omega
  rw [he_i1] at hD1; rw [he_i2] at hD2
  have hCi_ne : Ci.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty] at hD1
    nlinarith only [hD1, hn12]
  have hdeg_lt : ∀ u ∈ Ci, 5 * (#(C1.filter (G.Adj u)) + #(C2.filter (G.Adj u))) < 2 * n := by
    intro u hu
    have h5d := five_mul_deg_lt_two_mul_card G hTF hH u
    have hd12 : Disjoint (C1.filter (G.Adj u)) (C2.filter (G.Adj u)) := by
      rw [Finset.disjoint_left]; intro v h1 h2
      exact hj12 ((Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2)
    have hsub : C1.filter (G.Adj u) ∪ C2.filter (G.Adj u) ⊆ (G.neighborSet u).toFinset := by
      intro v hv
      simp only [Finset.mem_union, Finset.mem_filter, Set.mem_toFinset, SimpleGraph.mem_neighborSet] at hv ⊢
      rcases hv with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    have hle := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd12, ← Set.ncard_eq_toFinset_card'] at hle
    omega
  have hsum_lt := Finset.sum_lt_sum_of_nonempty hCi_ne hdeg_lt
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hsum_lt
  have hcard_eq : {v : V | c v = i}.ncard = #Ci := by
    rw [Set.ncard_eq_toFinset_card']; congr 1; ext v; simp [Ci]
  rw [hcard_eq]
  nlinarith only [hD1, hD2, hsum_lt, hn12]

/-- Lemma 3.3: Every 3-colorable triangle-free graph on `m >= 1` vertices has `18 * D_2(H) <= m^2`. -/
lemma three_col_bipartite_del_le {W : Type} [Fintype W] (H : SimpleGraph W)
    (hTF : H.CliqueFree 3) (h3 : H.Colorable 3) (hm : 1 ≤ Fintype.card W) :
    ∃ A : Set W, 18 * ((H.induce A).edgeSet.ncard + (H.induce Aᶜ).edgeSet.ncard) ≤ Fintype.card W ^ 2 := by
  classical
  set m := Fintype.card W
  let cutVal : Finset W → ℕ := fun A =>
    (H.induce (A : Set W)).edgeSet.ncard + (H.induce ((A : Set W)ᶜ)).edgeSet.ncard
  obtain ⟨A₀, -, hA₀_min⟩ := Finset.exists_min_image (Finset.univ : Finset (Finset W)) cutVal
    ⟨∅, Finset.mem_univ _⟩
  set D := cutVal A₀
  have hD_le : ∀ A : Finset W, D ≤ cutVal A := fun A => hA₀_min A (Finset.mem_univ A)
  refine ⟨(A₀ : Set W), ?_⟩
  change 18 * D ≤ m ^ 2
  set e := H.edgeSet.ncard
  -- Bound 1: 3 * D <= e (from a 3-coloring)
  have h3D_le_e : 3 * D ≤ e := by
    obtain ⟨c⟩ := h3
    let C : Fin 3 → Finset W := fun i => Finset.univ.filter (fun v => c v = i)
    have hC_ind : ∀ i u, u ∈ C i → ∀ v ∈ C i, ¬ H.Adj u v := fun i u hu v hv h =>
      c.valid h ((Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm)
    have hC_disj : ∀ i j : Fin 3, i ≠ j → Disjoint (C i) (C j) := fun i j hij => by
      rw [Finset.disjoint_left]; intro v h1 h2
      exact hij ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
    have hcut_pair : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        cutVal (C i ∪ C j) = ∑ w ∈ C j, #((C i).filter (H.Adj w)) := by
      intro i j k hij hik hjk
      have hcompl : ((C i ∪ C j : Finset W) : Set W)ᶜ = (C k : Set W) := by
        ext v; simp only [C, Set.mem_compl_iff, Finset.mem_coe, Finset.mem_union, Finset.mem_filter,
          Finset.mem_univ, true_and]
        have hall : ∀ x : Fin 3, x = i ∨ x = j ∨ x = k := by
          fin_cases i <;> fin_cases j <;> fin_cases k <;> first | contradiction | (intro x; fin_cases x <;> simp)
        constructor
        · intro h; rcases hall (c v) with h0 | h0 | h0 <;> first | exact h0 | exact (h (Or.inl h0)).elim | exact (h (Or.inr h0)).elim
        · rintro h (h0 | h0)
          · exact hik (h0.symm.trans h)
          · exact hjk (h0.symm.trans h)
      dsimp only [cutVal]; rw [hcompl]
      have hek : (H.induce (C k : Set W)).edgeSet.ncard = 0 := by
        have h := two_mul_induce_edgeSet_ncard H (C k)
        have h0 : ∑ u ∈ C k, #((C k).filter (H.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hC_ind k u hu v hv)
        omega
      have heij : 2 * (H.induce ((C i ∪ C j : Finset W) : Set W)).edgeSet.ncard =
          2 * ∑ w ∈ C j, #((C i).filter (H.Adj w)) := by
        rw [two_mul_induce_edgeSet_ncard, sum_adj_union_indep H (hC_disj i j hij) (hC_ind i)]
        have h0 : ∑ u ∈ C j, #((C j).filter (H.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hC_ind j u hu v hv)
        omega
      omega
    have hD01 := hD_le (C 0 ∪ C 1); rw [hcut_pair 0 1 2 (by decide) (by decide) (by decide)] at hD01
    have hD02 := hD_le (C 0 ∪ C 2); rw [hcut_pair 0 2 1 (by decide) (by decide) (by decide)] at hD02
    have hD12 := hD_le (C 1 ∪ C 2); rw [hcut_pair 1 2 0 (by decide) (by decide) (by decide)] at hD12
    have he_eq : e = (∑ w ∈ C 1, #((C 0).filter (H.Adj w))) +
        (∑ w ∈ C 2, #((C 0).filter (H.Adj w))) + (∑ w ∈ C 2, #((C 1).filter (H.Adj w))) := by
      have hcov : C 0 ∪ C 1 ∪ C 2 = Finset.univ := by
        ext v; simp only [C, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        generalize c v = x; fin_cases x <;> simp
      have hd01 : Disjoint (C 0) (C 1) := hC_disj 0 1 (by decide)
      have hd012 : Disjoint (C 0 ∪ C 1) (C 2) :=
        Finset.disjoint_union_left.mpr ⟨hC_disj 0 2 (by decide), hC_disj 1 2 (by decide)⟩
      have h2H : 2 * e = ∑ u ∈ C 0 ∪ C 1 ∪ C 2, #((C 0 ∪ C 1 ∪ C 2).filter (H.Adj u)) := by
        rw [hcov]
        have hcard : e = #H.edgeFinset := by dsimp only [e]; rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
        rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
        apply Finset.sum_congr rfl; intro u _
        rw [SimpleGraph.degree, SimpleGraph.neighborFinset]; congr 1; ext v; simp
      have hstep1 := sum_adj_union H hd012
      have hstep2 := sum_adj_union_indep H hd01 (hC_ind 0)
      have h10 : ∑ u ∈ C 1, #((C 1).filter (H.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hC_ind 1 u hu v hv)
      have h20 : ∑ u ∈ C 2, #((C 2).filter (H.Adj u)) = 0 := Finset.sum_eq_zero (fun u hu => by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun v hv => hC_ind 2 u hu v hv)
      have hcross : ∑ w ∈ C 2, #((C 0 ∪ C 1).filter (H.Adj w)) =
          (∑ w ∈ C 2, #((C 0).filter (H.Adj w))) + ∑ w ∈ C 2, #((C 1).filter (H.Adj w)) := by
        simp_rw [Finset.filter_union, Finset.card_union_of_disjoint
          (hd01.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)), Finset.sum_add_distrib]
      omega
    omega
  -- Case split on 6 * e <= m^2
  by_cases h6e : 6 * e ≤ m ^ 2
  · omega
  · -- Bound 2: m^2 * D <= m^2 * e - 4 * e^2 via V \ N(v) + Cauchy-Schwarz
    let d : W → ℕ := fun v => #(Finset.univ.filter (H.Adj v))
    have hsum_d : ∑ v : W, d v = 2 * e := by
      have hcard : e = #H.edgeFinset := by dsimp only [e]; rw [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
      rw [hcard, ← SimpleGraph.sum_degrees_eq_twice_card_edges]
      apply Finset.sum_congr rfl; intro u _
      dsimp only [d]; rw [SimpleGraph.degree, SimpleGraph.neighborFinset]; congr 1; ext v; simp
    have hper_v : ∀ v : W, D + ∑ w ∈ Finset.univ.filter (H.Adj v), d w ≤ e := by
      intro v
      let Nv := Finset.univ.filter (H.Adj v)
      have hNv_ind : ∀ x ∈ Nv, ∀ y ∈ Nv, ¬ H.Adj x y := filter_adj_indep hTF Finset.univ v
      have hDv := hD_le (Finset.univ \ Nv)
      have hcompl : ((Finset.univ \ Nv : Finset W) : Set W)ᶜ = (Nv : Set W) := by
        ext x; simp [Nv]
      dsimp only [cutVal] at hDv; rw [hcompl] at hDv
      have heNv0 : (H.induce (Nv : Set W)).edgeSet.ncard = 0 := by
        have h := two_mul_induce_edgeSet_ncard H Nv
        have h0 : ∑ x ∈ Nv, #(Nv.filter (H.Adj x)) = 0 := Finset.sum_eq_zero (fun x hx => by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun y hy => hNv_ind x hx y hy)
        omega
      have hsdiff := induce_edgeSet_ncard_sdiff_indep H (Finset.subset_univ Nv) hNv_ind
      have huniv_e : (H.induce ((Finset.univ : Finset W) : Set W)).edgeSet.ncard = e := by
        have h1 := two_mul_induce_edgeSet_ncard H (Finset.univ : Finset W)
        have h2 : ∑ u ∈ (Finset.univ : Finset W), #(Finset.univ.filter (H.Adj u)) = 2 * e := hsum_d
        omega
      have h3 : (H.induce ((Finset.univ \ Nv : Finset W) : Set W)).edgeSet.ncard + ∑ w ∈ Nv, d w = e := by
        rw [← huniv_e]; exact hsdiff
      change D + ∑ w ∈ Nv, d w ≤ e
      omega
    have hsum_v : m * D + ∑ v : W, (d v) ^ 2 ≤ m * e := by
      have h1 := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset W)) => hper_v v)
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, Finset.card_univ, smul_eq_mul, smul_eq_mul] at h1
      have hswap : ∑ v : W, ∑ w ∈ Finset.univ.filter (H.Adj v), d w = ∑ v : W, (d v) ^ 2 := by
        calc ∑ v : W, ∑ w ∈ Finset.univ.filter (H.Adj v), d w
            = ∑ v : W, ∑ w : W, if H.Adj v w then d w else 0 := by
              apply Finset.sum_congr rfl; intro v _; rw [Finset.sum_filter]
          _ = ∑ w : W, ∑ v : W, if H.Adj v w then d w else 0 := Finset.sum_comm
          _ = ∑ w : W, ∑ v : W, if H.Adj w v then d w else 0 := by
              apply Finset.sum_congr rfl; intro w _
              apply Finset.sum_congr rfl; intro v _; simp [H.adj_comm]
          _ = ∑ w : W, ∑ _v ∈ Finset.univ.filter (H.Adj w), d w := by
              apply Finset.sum_congr rfl; intro w _; rw [← Finset.sum_filter]
          _ = ∑ w : W, (d w) ^ 2 := by
              apply Finset.sum_congr rfl; intro w _; rw [Finset.sum_const, smul_eq_mul]; ring
      rw [hswap] at h1; exact h1
    have hCS : (2 * e) ^ 2 ≤ m * ∑ v : W, (d v) ^ 2 := by
      let eqv := (Fintype.equivFin W).symm
      have hcs := sq_sum_le_card_mul_sum_sq_int (fun i : Fin m => (d (eqv i) : ℤ))
      have hsum1 : ∑ i : Fin m, (d (eqv i) : ℤ) = (2 * e : ℤ) := by
        have hnat : ∑ i : Fin m, d (eqv i) = 2 * e := by rw [Fintype.sum_equiv eqv _ d (fun _ => rfl), hsum_d]
        exact_mod_cast hnat
      have hsum2 : ∑ i : Fin m, ((d (eqv i) : ℤ) ^ 2) = ((∑ v : W, (d v) ^ 2 : ℕ) : ℤ) := by
        have hnat : ∑ i : Fin m, (d (eqv i)) ^ 2 = ∑ v : W, (d v) ^ 2 :=
          Fintype.sum_equiv eqv _ (fun v => (d v) ^ 2) (fun _ => rfl)
        push_cast [← hnat]; rfl
      rw [hsum1, hsum2] at hcs
      exact_mod_cast hcs
    have hD_quad : m ^ 2 * D + 4 * e ^ 2 ≤ m ^ 2 * e := by
      have hm1 := Nat.mul_le_mul_left m hsum_v
      nlinarith only [hm1, hCS]
    have hfac : (m : ℤ) ^ 4 - 18 * ((m : ℤ) ^ 2 * (e : ℤ) - 4 * (e : ℤ) ^ 2) =
        (6 * (e : ℤ) - (m : ℤ) ^ 2) * (12 * (e : ℤ) - (m : ℤ) ^ 2) := by ring
    have hge0 : (0 : ℤ) ≤ (6 * (e : ℤ) - (m : ℤ) ^ 2) * (12 * (e : ℤ) - (m : ℤ) ^ 2) := by
      have h6 : (m : ℤ) ^ 2 < 6 * (e : ℤ) := by exact_mod_cast (show m ^ 2 < 6 * e by omega)
      nlinarith only [h6]
    have hD_z : (m : ℤ) ^ 2 * (D : ℤ) ≤ (m : ℤ) ^ 2 * (e : ℤ) - 4 * (e : ℤ) ^ 2 := by
      have : ((m ^ 2 * D + 4 * e ^ 2 : ℕ) : ℤ) ≤ ((m ^ 2 * e : ℕ) : ℤ) := by exact_mod_cast hD_quad
      push_cast at this; linarith
    have hm2_pos : (0 : ℤ) < (m : ℤ) ^ 2 := by
      have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      nlinarith only [this]
    have hfin_z : (m : ℤ) ^ 2 * (18 * (D : ℤ)) ≤ (m : ℤ) ^ 2 * (m : ℤ) ^ 2 := by
      nlinarith only [hD_z, hfac, hge0]
    have hfin_z2 := le_of_mul_le_mul_left hfin_z hm2_pos
    exact_mod_cast hfin_z2

/-- Helper: induced edge count is invariant under injective adjacency-preserving maps. -/
lemma induce_ncard_map {W V : Type} [DecidableEq W] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : W ↪ V) (hf : ∀ x y : W, H.Adj x y ↔ G.Adj (f x) (f y)) (S : Finset W) :
    (H.induce (S : Set W)).edgeSet.ncard = (G.induce ((S.map f : Finset V) : Set V)).edgeSet.ncard := by
  have h1 := two_mul_induce_edgeSet_ncard H S
  have h2 := two_mul_induce_edgeSet_ncard G (S.map f)
  rw [Finset.sum_map] at h2
  have hsum : ∑ u ∈ S, #(S.filter (H.Adj u)) = ∑ u ∈ S, #((S.map f).filter (G.Adj (f u))) := by
    apply Finset.sum_congr rfl; intro u _
    have hmap : (S.filter (H.Adj u)).map f = (S.map f).filter (G.Adj (f u)) := by
      ext v; simp only [Finset.mem_map, Finset.mem_filter]
      constructor
      · rintro ⟨w, ⟨hw, hadj⟩, rfl⟩; exact ⟨⟨w, hw, rfl⟩, (hf u w).mp hadj⟩
      · rintro ⟨⟨w, hw, rfl⟩, hadj⟩; exact ⟨w, ⟨hw, (hf u w).mpr hadj⟩, rfl⟩
    rw [← Finset.card_map f, hmap]
  omega

/-- Helper: given a minimum-order 3-colorable TF counterexample `G₀` on `Fin n₀`, every proper induced
    subgraph `U` (`#U < n₀`) contains a subset `W ⊆ U` of exact size `#U / 2` with `50 * e(W) <= (#U)^2`. -/
lemma exists_sparse_half_of_min {n₀ : ℕ} (G₀ : SimpleGraph (Fin n₀))
    (hTF : G₀.CliqueFree 3) (h3 : G₀.Colorable 3)
    (hmin : ∀ m < n₀, ¬ ∃ H : SimpleGraph (Fin m), H.CliqueFree 3 ∧ H.Colorable 3 ∧
      ∀ V' : Set (Fin m), 2 * V'.ncard + 1 ≥ m → 50 * (H.induce V').edgeSet.ncard > m ^ 2)
    (U : Finset (Fin n₀)) (hU_lt : #U < n₀) :
    ∃ W : Finset (Fin n₀), W ⊆ U ∧ #W = #U / 2 ∧
      50 * (G₀.induce (W : Set (Fin n₀))).edgeSet.ncard ≤ (#U) ^ 2 := by
  classical
  set m := #U
  let eqv : Fin m ≃ {x : Fin n₀ // x ∈ U} := (Fintype.equivFinOfCardEq (by simp [m])).symm
  let f : Fin m ↪ Fin n₀ := ⟨fun i => (eqv i).val, fun i j hij => eqv.injective (Subtype.ext hij)⟩
  let H : SimpleGraph (Fin m) := G₀.comap f
  have hHTF : H.CliqueFree 3 := by
    intro s hs
    apply hTF (s.map f)
    refine ⟨?_, by rw [Finset.card_map]; exact hs.2⟩
    intro x hx y hy hxy
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨b, hb, rfl⟩
    exact hs.1 ha hb (fun hab => hxy (congrArg f hab))
  have hH3 : H.Colorable 3 := by
    obtain ⟨c⟩ := h3
    exact ⟨SimpleGraph.Coloring.mk (fun i => c (f i)) (fun hadj => c.valid hadj)⟩
  have hnot := hmin m hU_lt
  have hfail : ¬ ∀ V' : Set (Fin m), 2 * V'.ncard + 1 ≥ m → 50 * (H.induce V').edgeSet.ncard > m ^ 2 :=
    fun h => hnot ⟨H, hHTF, hH3, h⟩
  push Not at hfail
  obtain ⟨V', hV'sz, hV'e⟩ := hfail
  let S' : Finset (Fin m) := V'.toFinset
  have hS'card : m / 2 ≤ #S' := by
    have : V'.ncard = #S' := Set.ncard_eq_toFinset_card' V'
    omega
  obtain ⟨S, hSS', hScard⟩ := Finset.exists_subset_card_eq hS'card
  have hS_le : (H.induce (S : Set (Fin m))).edgeSet.ncard ≤ (H.induce V').edgeSet.ncard := by
    have h1 := two_mul_induce_edgeSet_ncard H S
    have h2 := two_mul_induce_edgeSet_ncard H S'
    have hcoe : (S' : Set (Fin m)) = V' := Set.coe_toFinset V'
    rw [hcoe] at h2
    have hle2 : ∑ u ∈ S, #(S.filter (H.Adj u)) ≤ ∑ u ∈ S', #(S'.filter (H.Adj u)) :=
      (Finset.sum_le_sum (fun u _ => Finset.card_le_card (Finset.filter_subset_filter _ hSS'))).trans
        (Finset.sum_le_sum_of_subset hSS')
    omega
  refine ⟨S.map f, ?_, by rw [Finset.card_map]; exact hScard, ?_⟩
  · intro x hx; rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩; exact (eqv i).property
  · rw [← induce_ncard_map H G₀ f (fun _ _ => Iff.rfl) S]; omega

/-- Theorem 3: `H1 → H2 → OMA.R_Erdos128_erdos_128_R2.H3`. -/
theorem main : H1 → H2 → OMA.R_Erdos128_erdos_128_R2.H3 := by
  intro hH1 hH2 V _ G hn12 h800 h500k h5a hC4 hC5 h2K2 h3d hH hTF
  classical
  by_cases h3col : G.Colorable 3
  · -- Branch 1: 3-colorable -> pass to minimum-order 3-colorable TF counterexample on Fin n₀
    have hex : ∃ n : ℕ, ∃ G' : SimpleGraph (Fin n), G'.CliqueFree 3 ∧ G'.Colorable 3 ∧
        ∀ V' : Set (Fin n), 2 * V'.ncard + 1 ≥ n → 50 * (G'.induce V').edgeSet.ncard > n ^ 2 := by
      let eqv : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
      let f : Fin (Fintype.card V) ↪ V := eqv.toEmbedding
      let G' : SimpleGraph (Fin (Fintype.card V)) := G.comap f
      refine ⟨Fintype.card V, G', ?_, ?_, ?_⟩
      · intro s hs; apply hTF (s.map f); refine ⟨?_, by rw [Finset.card_map]; exact hs.2⟩
        intro x hx y hy hxy
        rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨a, ha, rfl⟩
        rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨b, hb, rfl⟩
        exact hs.1 ha hb (fun hab => hxy (congrArg f hab))
      · obtain ⟨c⟩ := h3col
        exact ⟨SimpleGraph.Coloring.mk (fun i => c (f i)) (fun hadj => c.valid hadj)⟩
      · intro V' hV'
        let S : Finset (Fin (Fintype.card V)) := V'.toFinset
        have hScoe : (S : Set (Fin (Fintype.card V))) = V' := Set.coe_toFinset V'
        have hnc : (S.map f : Set V).ncard = V'.ncard := by
          rw [Set.ncard_coe_finset, Finset.card_map, ← Set.ncard_eq_toFinset_card']
        have h50 := hH (S.map f : Set V) (by rw [hnc]; exact hV')
        rw [← hScoe, induce_ncard_map G' G f (fun _ _ => Iff.rfl) S]
        exact h50
    set n₀ := Nat.find hex
    obtain ⟨G₀, h0TF, h03col, h0H_raw⟩ := Nat.find_spec hex
    have h0min : ∀ m < n₀, ¬ ∃ H : SimpleGraph (Fin m), H.CliqueFree 3 ∧ H.Colorable 3 ∧
        ∀ V' : Set (Fin m), 2 * V'.ncard + 1 ≥ m → 50 * (H.induce V').edgeSet.ncard > m ^ 2 :=
      fun m hm => Nat.find_min hex hm
    have h0H : ∀ V' : Set (Fin n₀), 2 * V'.ncard + 1 ≥ Fintype.card (Fin n₀) →
        50 * (G₀.induce V').edgeSet.ncard > Fintype.card (Fin n₀) ^ 2 := by
      simpa only [Fintype.card_fin] using h0H_raw
    have h0n12 : 12 ≤ Fintype.card (Fin n₀) := twelve_le_card G₀ h0TF h0H
    have h0n12' : 12 ≤ n₀ := by simpa using h0n12
    -- 1. Even n₀
    have h0even : Even (Fintype.card (Fin n₀)) := by
      rw [Fintype.card_fin]
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      obtain ⟨m, hm⟩ := hodd
      let v₀ : Fin n₀ := ⟨0, by omega⟩
      let U : Finset (Fin n₀) := Finset.univ.erase v₀
      have hUcard : #U = 2 * m := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]; omega
      obtain ⟨W, -, hWcard, hWe⟩ := exists_sparse_half_of_min G₀ h0TF h03col h0min U (by omega)
      have h50 := h0H (W : Set (Fin n₀)) (by rw [Set.ncard_coe_finset, Fintype.card_fin, hWcard, hUcard]; omega)
      rw [Fintype.card_fin] at h50
      nlinarith only [h50, hWe, hUcard, hm]
    -- 2. Minimum degree: n₀ <= 25 * d(v)
    have h0deg_ge : ∀ v : Fin n₀, Fintype.card (Fin n₀) ≤ 25 * (G₀.neighborSet v).ncard := by
      intro v
      rw [Fintype.card_fin]
      obtain ⟨m, hm⟩ := h0even
      rw [Fintype.card_fin] at hm
      let U : Finset (Fin n₀) := Finset.univ.erase v
      have hUcard : #U = n₀ - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      obtain ⟨W, hWU, hWcard, hWe⟩ := exists_sparse_half_of_min G₀ h0TF h03col h0min U (by omega)
      have hvW : v ∉ W := fun h => (Finset.mem_erase.mp (hWU h)).1 rfl
      have h50 := h0H ((insert v W : Finset (Fin n₀)) : Set (Fin n₀)) (by
        rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hvW, Fintype.card_fin, hWcard, hUcard]; omega)
      rw [Fintype.card_fin] at h50
      have hadd : (G₀.induce ((insert v W : Finset (Fin n₀)) : Set (Fin n₀))).edgeSet.ncard ≤
          (G₀.induce (W : Set (Fin n₀))).edgeSet.ncard + (G₀.neighborSet v).ncard := by
        have hdisj : Disjoint ({v} : Finset (Fin n₀)) W := Finset.disjoint_singleton_left.mpr hvW
        have h2ins := two_mul_induce_edgeSet_ncard G₀ (insert v W)
        have h2W := two_mul_induce_edgeSet_ncard G₀ W
        have hsum := sum_adj_union_indep G₀ hdisj (by rintro _ h1 _ h2; rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]; exact G₀.loopless.irrefl _)
        rw [Finset.singleton_union] at hsum
        have hcross : ∑ w ∈ W, #(({v} : Finset (Fin n₀)).filter (G₀.Adj w)) ≤ (G₀.neighborSet v).ncard := by
          have h1 : ∑ w ∈ W, #(({v} : Finset (Fin n₀)).filter (G₀.Adj w)) = #(W.filter (G₀.Adj v)) := by
            rw [Finset.card_filter]; apply Finset.sum_congr rfl; intro w _
            by_cases hadj : G₀.Adj v w
            · have : ({v} : Finset (Fin n₀)).filter (G₀.Adj w) = {v} := by
                ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
                exact ⟨fun h => h.1, fun h => ⟨h, h.symm ▸ hadj.symm⟩⟩
              rw [this]; simp [hadj]
            · have : ({v} : Finset (Fin n₀)).filter (G₀.Adj w) = ∅ := by
                rw [Finset.filter_eq_empty_iff]; intro x hx; rw [Finset.mem_singleton.mp hx]; exact fun h => hadj h.symm
              rw [this]; simp [hadj]
          rw [h1, Set.ncard_eq_toFinset_card']
          exact Finset.card_le_card (fun w hw => Set.mem_toFinset.mpr (Finset.mem_filter.mp hw).2)
        omega
      have hsq : (n₀ - 1) ^ 2 + 2 * n₀ = n₀ ^ 2 + 1 := by zify [show 1 ≤ n₀ by omega]; ring
      rw [hUcard] at hWe
      omega
    -- 3. Pair degree sum: 4 * n₀ <= 25 * (d(u) + d(v)) + 3 for ALL u != v
    have h0pair : ∀ u v : Fin n₀, u ≠ v →
        4 * Fintype.card (Fin n₀) ≤ 25 * ((G₀.neighborSet u).ncard + (G₀.neighborSet v).ncard) + 3 := by
      intro u v huv
      rw [Fintype.card_fin]
      obtain ⟨m, hm⟩ := h0even
      rw [Fintype.card_fin] at hm
      let U : Finset (Fin n₀) := (Finset.univ.erase u).erase v
      have hUcard : #U = n₀ - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ _⟩),
          Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨W, hWU, hWcard, hWe⟩ := exists_sparse_half_of_min G₀ h0TF h03col h0min U (by omega)
      have huW : u ∉ W := fun h => (Finset.mem_erase.mp (Finset.mem_erase.mp (hWU h)).2).1 rfl
      have hvW : v ∉ W := fun h => (Finset.mem_erase.mp (hWU h)).1 rfl
      have hstep_ins : ∀ x : Fin n₀, x ∉ W →
          n₀ ^ 2 < 50 * (G₀.induce (W : Set (Fin n₀))).edgeSet.ncard + 50 * (G₀.neighborSet x).ncard := by
        intro x hxW
        have h50 := h0H ((insert x W : Finset (Fin n₀)) : Set (Fin n₀)) (by
          rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem hxW, Fintype.card_fin, hWcard, hUcard]; omega)
        rw [Fintype.card_fin] at h50
        have hdisj : Disjoint ({x} : Finset (Fin n₀)) W := Finset.disjoint_singleton_left.mpr hxW
        have h2ins := two_mul_induce_edgeSet_ncard G₀ (insert x W)
        have h2W := two_mul_induce_edgeSet_ncard G₀ W
        have hsum := sum_adj_union_indep G₀ hdisj (by rintro _ h1 _ h2; rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]; exact G₀.loopless.irrefl _)
        rw [Finset.singleton_union] at hsum
        have hcross : ∑ w ∈ W, #(({x} : Finset (Fin n₀)).filter (G₀.Adj w)) ≤ (G₀.neighborSet x).ncard := by
          have h1 : ∑ w ∈ W, #(({x} : Finset (Fin n₀)).filter (G₀.Adj w)) = #(W.filter (G₀.Adj x)) := by
            rw [Finset.card_filter]; apply Finset.sum_congr rfl; intro w _
            by_cases hadj : G₀.Adj x w
            · have : ({x} : Finset (Fin n₀)).filter (G₀.Adj w) = {x} := by
                ext y; simp only [Finset.mem_filter, Finset.mem_singleton]
                exact ⟨fun h => h.1, fun h => ⟨h, h.symm ▸ hadj.symm⟩⟩
              rw [this]; simp [hadj]
            · have : ({x} : Finset (Fin n₀)).filter (G₀.Adj w) = ∅ := by
                rw [Finset.filter_eq_empty_iff]; intro y hy; rw [Finset.mem_singleton.mp hy]; exact fun h => hadj h.symm
              rw [this]; simp [hadj]
          rw [h1, Set.ncard_eq_toFinset_card']
          exact Finset.card_le_card (fun w hw => Set.mem_toFinset.mpr (Finset.mem_filter.mp hw).2)
        omega
      have hu50 := hstep_ins u huW
      have hv50 := hstep_ins v hvW
      have hsq : (n₀ - 2) ^ 2 + 4 * n₀ = n₀ ^ 2 + 4 := by zify [show 2 ≤ n₀ by omega]; ring
      nlinarith only [hu50, hv50, hWe, hUcard, hsq]
    -- 4. Connectedness of G₀
    have h0conn : G₀.Connected := by
      refine { preconnected := ?_, nonempty := ⟨⟨0, by omega⟩⟩ }
      by_contra hnotpre
      -- Pick u0 = 0, split Fin n₀ into V1 = reachable from u0 and V2 = univ \ V1
      let u₀ : Fin n₀ := ⟨0, by omega⟩
      let V1 : Finset (Fin n₀) := Finset.univ.filter (fun v => G₀.Reachable u₀ v)
      let V2 : Finset (Fin n₀) := Finset.univ \ V1
      have hV1_ne : V1.Nonempty := ⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, SimpleGraph.Reachable.refl u₀⟩⟩
      have hV2_ne : V2.Nonempty := by
        rw [SimpleGraph.Preconnected] at hnotpre; push Not at hnotpre
        obtain ⟨x, y, hxy⟩ := hnotpre
        by_cases hx : G₀.Reachable u₀ x
        · refine ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hy => hxy (hx.symm.trans (Finset.mem_filter.mp hy).2)⟩⟩
        · exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hx' => hx (Finset.mem_filter.mp hx').2⟩⟩
      have hno_cross : ∀ x ∈ V1, ∀ y ∈ V2, ¬ G₀.Adj x y := by
        intro x hx y hy hadj
        exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hx).2.trans hadj.reachable⟩)
      -- WLOG #V1 <= #V2 (swap if needed)
      have hsplit : ∃ U1 U2 : Finset (Fin n₀), Disjoint U1 U2 ∧ U1 ∪ U2 = Finset.univ ∧
          1 ≤ #U1 ∧ #U1 ≤ #U2 ∧ ∀ x ∈ U1, ∀ y ∈ U2, ¬ G₀.Adj x y := by
        have hd : Disjoint V1 V2 := Finset.disjoint_sdiff
        have hc : V1 ∪ V2 = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ V1)
        by_cases hle : #V1 ≤ #V2
        · exact ⟨V1, V2, hd, hc, Finset.card_pos.mpr hV1_ne, hle, hno_cross⟩
        · exact ⟨V2, V1, hd.symm, by rw [Finset.union_comm]; exact hc, Finset.card_pos.mpr hV2_ne, by omega,
            fun x hx y hy hadj => hno_cross y hy x hx hadj.symm⟩
      obtain ⟨U1, U2, hd12, hc12, hn1_pos, hn1_le_n2, hnc⟩ := hsplit
      set n1 := #U1; set n2 := #U2
      have hsum12 : n1 + n2 = n₀ := by
        rw [← Finset.card_union_of_disjoint hd12, hc12, Finset.card_univ, Fintype.card_fin]
      obtain ⟨m, hm⟩ := h0even; rw [Fintype.card_fin] at hm
      obtain ⟨W1, hW1U, hW1c, hW1e⟩ := exists_sparse_half_of_min G₀ h0TF h03col h0min U1 (by omega)
      obtain ⟨W2, hW2U, hW2c, hW2e⟩ := exists_sparse_half_of_min G₀ h0TF h03col h0min U2 (by omega)
      have hedge_disj : ∀ S1 S2 : Finset (Fin n₀), S1 ⊆ U1 → S2 ⊆ U2 →
          (G₀.induce ((S1 ∪ S2 : Finset (Fin n₀)) : Set (Fin n₀))).edgeSet.ncard =
          (G₀.induce (S1 : Set (Fin n₀))).edgeSet.ncard + (G₀.induce (S2 : Set (Fin n₀))).edgeSet.ncard := by
        intro S1 S2 hS1 hS2
        have hdS := hd12.mono hS1 hS2
        have h2u := two_mul_induce_edgeSet_ncard G₀ (S1 ∪ S2)
        have h21 := two_mul_induce_edgeSet_ncard G₀ S1
        have h22 := two_mul_induce_edgeSet_ncard G₀ S2
        have hsu := sum_adj_union G₀ hdS
        have h0 : ∑ w ∈ S2, #(S1.filter (G₀.Adj w)) = 0 := Finset.sum_eq_zero (fun w hw => by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; exact fun x hx hadj => hnc x (hS1 hx) w (hS2 hw) hadj.symm)
        rw [hsu, h0, mul_zero, add_zero, ← h21, ← h22] at h2u
        omega
      by_cases hpar : n1 % 2 = 0
      · -- Both n1, n2 even
        have hcard : #(W1 ∪ W2) = m := by
          rw [Finset.card_union_of_disjoint (hd12.mono hW1U hW2U), hW1c, hW2c]; omega
        have h50 := h0H ((W1 ∪ W2 : Finset (Fin n₀)) : Set (Fin n₀)) (by
          rw [Set.ncard_coe_finset, Fintype.card_fin, hcard]; omega)
        rw [Fintype.card_fin, hedge_disj W1 W2 hW1U hW2U] at h50
        nlinarith only [h50, hW1e, hW2e, hsum12, hn1_pos, hn1_le_n2]
      · -- Both n1, n2 odd
        have hn1_odd : n1 % 2 = 1 := by omega
        have hn2_odd : n2 % 2 = 1 := by omega
        have hne_sdiff : (U1 \ W1).Nonempty := Finset.card_pos.mp (by rw [Finset.card_sdiff_of_subset hW1U, hW1c]; omega)
        obtain ⟨v, hv⟩ := hne_sdiff
        have hvU1 : v ∈ U1 := (Finset.mem_sdiff.mp hv).1
        have hvW1 : v ∉ W1 := (Finset.mem_sdiff.mp hv).2
        have hcard : #(insert v W1 ∪ W2) = m := by
          have hsub : insert v W1 ⊆ U1 := Finset.insert_subset hvU1 hW1U
          rw [Finset.card_union_of_disjoint (hd12.mono hsub hW2U), Finset.card_insert_of_notMem hvW1, hW1c, hW2c]
          omega
        have h50 := h0H ((insert v W1 ∪ W2 : Finset (Fin n₀)) : Set (Fin n₀)) (by
          rw [Set.ncard_coe_finset, Fintype.card_fin, hcard]; omega)
        rw [Fintype.card_fin, hedge_disj (insert v W1) W2 (Finset.insert_subset hvU1 hW1U) hW2U] at h50
        have hins_le : (G₀.induce ((insert v W1 : Finset (Fin n₀)) : Set (Fin n₀))).edgeSet.ncard ≤
            (G₀.induce (W1 : Set (Fin n₀))).edgeSet.ncard + #W1 := by
          have hdisj : Disjoint ({v} : Finset (Fin n₀)) W1 := Finset.disjoint_singleton_left.mpr hvW1
          have h2ins := two_mul_induce_edgeSet_ncard G₀ (insert v W1)
          have h2W := two_mul_induce_edgeSet_ncard G₀ W1
          have hsum := sum_adj_union_indep G₀ hdisj (by rintro _ h1 _ h2; rw [Finset.mem_singleton.mp h1, Finset.mem_singleton.mp h2]; exact G₀.loopless.irrefl _)
          rw [Finset.singleton_union] at hsum
          have hcross : ∑ w ∈ W1, #(({v} : Finset (Fin n₀)).filter (G₀.Adj w)) ≤ #W1 := by
            calc ∑ w ∈ W1, #(({v} : Finset (Fin n₀)).filter (G₀.Adj w))
                ≤ ∑ _w ∈ W1, 1 := Finset.sum_le_sum (fun w _ => (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp))
              _ = #W1 := by simp
          omega
        have h2n1n2 : 2 * n1 * n2 < 25 * (n1 - 1) := by
          have h2W1 : 2 * #W1 = n1 - 1 := by rw [hW1c]; omega
          nlinarith only [h50, hW1e, hW2e, hins_le, h2W1, hsum12]
        -- Only 7 odd pairs (n1, n2) satisfy 2*n1*n2 < 25*(n1 - 1) and n1 <= n2 and n1 + n2 >= 12,
        -- and ALL have n1 <= n2 <= 11! Apply Lemma 3.3 (18 * D_2 <= m^2) to U1 and U2!
        have hsub1 : n1 - 1 + 1 = n1 := by omega
        have hn2_le12 : n2 ≤ 12 := by nlinarith only [h2n1n2, hn1_pos, hsub1]
        have hn2_le11 : n2 ≤ 11 := by omega
        have hn1_ge5 : 5 ≤ n1 := by
          by_contra hlt; push Not at hlt
          have : n1 = 1 ∨ n1 = 3 := by omega
          rcases this with h1 | h1
          · rw [h1] at h2n1n2; norm_num at h2n1n2
          · rw [h1] at h2n1n2 hsum12; norm_num at h2n1n2; omega
        -- Induce G₀ on U1 and U2 and apply Lemma 3.3 to both
        have hD_comp : ∀ U : Finset (Fin n₀), 1 ≤ #U →
            ∃ S : Finset (Fin n₀), S ⊆ U ∧
              18 * ((G₀.induce (S : Set (Fin n₀))).edgeSet.ncard +
                (G₀.induce ((U \ S : Finset (Fin n₀)) : Set (Fin n₀))).edgeSet.ncard) ≤ (#U) ^ 2 := by
          intro U hUpos
          let eqv : Fin #U ≃ {x : Fin n₀ // x ∈ U} := (Fintype.equivFinOfCardEq (by simp)).symm
          let f : Fin #U ↪ Fin n₀ := ⟨fun i => (eqv i).val, fun i j hij => eqv.injective (Subtype.ext hij)⟩
          let H : SimpleGraph (Fin #U) := G₀.comap f
          have hHTF : H.CliqueFree 3 := by
            intro s hs; apply h0TF (s.map f); refine ⟨?_, by rw [Finset.card_map]; exact hs.2⟩
            intro x hx y hy hxy
            rcases Finset.mem_map.mp (Finset.mem_coe.mp hx) with ⟨a, ha, rfl⟩
            rcases Finset.mem_map.mp (Finset.mem_coe.mp hy) with ⟨b, hb, rfl⟩
            exact hs.1 ha hb (fun hab => hxy (congrArg f hab))
          have hH3 : H.Colorable 3 := by
            obtain ⟨c⟩ := h03col
            exact ⟨SimpleGraph.Coloring.mk (fun i => c (f i)) (fun hadj => c.valid hadj)⟩
          obtain ⟨A, hA⟩ := three_col_bipartite_del_le H hHTF hH3 (by simpa using hUpos)
          rw [Fintype.card_fin] at hA
          let Af : Finset (Fin #U) := A.toFinset
          let Bf : Finset (Fin #U) := Aᶜ.toFinset
          have hAf_coe : (Af : Set (Fin #U)) = A := Set.coe_toFinset A
          have hBf_coe : (Bf : Set (Fin #U)) = Aᶜ := Set.coe_toFinset Aᶜ
          have hS_sub : Af.map f ⊆ U := by
            intro x hx; rcases Finset.mem_map.mp hx with ⟨i, _, rfl⟩; exact (eqv i).property
          have hcompl_eq : U \ Af.map f = Bf.map f := by
            ext x; simp only [Finset.mem_sdiff, Finset.mem_map, Af, Bf, Set.mem_toFinset, Set.mem_compl_iff]
            constructor
            · rintro ⟨hxU, hnot⟩
              have hfeqv : f (eqv.symm ⟨x, hxU⟩) = x := congrArg Subtype.val (eqv.apply_symm_apply ⟨x, hxU⟩)
              exact ⟨eqv.symm ⟨x, hxU⟩, fun hmem => hnot ⟨eqv.symm ⟨x, hxU⟩, hmem, hfeqv⟩, hfeqv⟩
            · rintro ⟨i, hi, rfl⟩
              refine ⟨(eqv i).property, ?_⟩
              rintro ⟨j, hj, hfeq⟩
              have hij : j = i := f.injective hfeq
              exact hi (hij ▸ hj)
          refine ⟨Af.map f, hS_sub, ?_⟩
          rw [hcompl_eq, ← induce_ncard_map H G₀ f (fun _ _ => Iff.rfl) Af,
            ← induce_ncard_map H G₀ f (fun _ _ => Iff.rfl) Bf, hAf_coe, hBf_coe]
          exact hA
        obtain ⟨S1, hS1U, hD1⟩ := hD_comp U1 hn1_pos
        obtain ⟨S2, hS2U, hD2⟩ := hD_comp U2 (by omega)
        have hG0_D := bipartite_del_gt G₀ h0TF h0H ((S1 ∪ S2 : Finset (Fin n₀)) : Set (Fin n₀))
        rw [Fintype.card_fin] at hG0_D
        have hcompl_tot : ((S1 ∪ S2 : Finset (Fin n₀)) : Set (Fin n₀))ᶜ =
            (((U1 \ S1) ∪ (U2 \ S2) : Finset (Fin n₀)) : Set (Fin n₀)) := by
          ext x
          have hxU : x ∈ U1 ∨ x ∈ U2 := by
            have : x ∈ U1 ∪ U2 := by rw [hc12]; exact Finset.mem_univ x
            exact Finset.mem_union.mp this
          simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_union, Finset.mem_sdiff]
          constructor
          · intro h; rcases hxU with h1 | h2
            · exact Or.inl ⟨h1, fun hs => h (Or.inl hs)⟩
            · exact Or.inr ⟨h2, fun hs => h (Or.inr hs)⟩
          · rintro (⟨h1, hns1⟩ | ⟨h2, hns2⟩) (hs1 | hs2)
            · exact hns1 hs1
            · exact (Finset.disjoint_left.mp hd12 h1 (hS2U hs2))
            · exact (Finset.disjoint_left.mp hd12 (hS1U hs1) h2)
            · exact hns2 hs2
        rw [hcompl_tot, hedge_disj S1 S2 hS1U hS2U,
          hedge_disj (U1 \ S1) (U2 \ S2) Finset.sdiff_subset Finset.sdiff_subset] at hG0_D
        set D1 := (G₀.induce (S1 : Set (Fin n₀))).edgeSet.ncard +
            (G₀.induce ((U1 \ S1 : Finset (Fin n₀)) : Set (Fin n₀))).edgeSet.ncard
        set D2 := (G₀.induce (S2 : Set (Fin n₀))).edgeSet.ncard +
            (G₀.induce ((U2 \ S2 : Finset (Fin n₀)) : Set (Fin n₀))).edgeSet.ncard
        have hD1_le : D1 ≤ n1 ^ 2 / 18 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by linarith only [hD1])
        have hD2_le : D2 ≤ n2 ^ 2 / 18 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by linarith only [hD2])
        have hcontra : 1250 * (n1 ^ 2 / 18 + n2 ^ 2 / 18) < 37 * (n1 + n2) ^ 2 := by
          have hcases : (n1 = 5 ∨ n1 = 7 ∨ n1 = 9 ∨ n1 = 11) ∧ (n2 = 7 ∨ n2 = 9 ∨ n2 = 11) := by omega
          rcases hcases with ⟨h1 | h1 | h1 | h1, h2 | h2 | h2⟩ <;> rw [h1, h2] <;> norm_num
        rw [hsum12] at hcontra
        dsimp only [D1, D2] at hD1_le hD2_le
        change 37 * n₀ ^ 2 < _ at hG0_D
        omega
    -- 5. Assemble remaining hypotheses of H1 for G₀
    have h0_3d : ∃ v : Fin n₀, 3 * (G₀.neighborSet v).ncard ≤ Fintype.card (Fin n₀) := by
      by_contra hall
      push Not at hall
      exact not_colorable_three_of_gt_third G₀ h0TF h0H hall h03col
    exact hH1 (Fin n₀) G₀ h0n12 h0even h03col h0conn
      (three_col_edges_gt G₀ h0TF h03col h0H)
      (five_hundred_thousand_mul_edges_lt G₀ h0TF h0H)
      (five_mul_indep_lt_two_mul_card G₀ h0TF h0H)
      h0deg_ge h0pair h0_3d
      (bipartite_del_gt G₀ h0TF h0H)
      (three_col_class_gt G₀ h0TF h0H)
      (exists_fourCycle G₀ h0TF h0H)
      (exists_fiveCycle G₀ h0TF h0H)
      (exists_induced_twoK2 G₀ h0TF h0H)
      h0H h0TF
  · -- Branch 2: non-3-colorable -> apply H2 directly to G
    exact hH2 V G hn12
      (six_hundred_twenty_five_mul_edges_gt G hTF hH)
      h500k h5a hC4 hC5 h2K2 h3col h3d
      (bipartite_del_gt G hTF hH)
      hH hTF

end ThreeColorableCore

end OMA.R_Erdos128_erdos_128_R2_H3_R1
