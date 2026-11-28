import OMAStatements.S_oeis_a058211
import Mathlib.Tactic

namespace OMA.D_oeis_a058211

open OMA.S_oeis_a058211

private lemma collinear3_eq_of_collinear {p q q' : ℝ × ℝ}
    (hpq : p ≠ q) (hpq' : p ≠ q') (h : collinear3 p q q') (r : ℝ × ℝ) :
    collinear3 p q r ↔ collinear3 p q' r := by
  unfold collinear3 at h ⊢
  have hne : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
    by_contra h0
    push Not at h0
    apply hpq
    exact Prod.ext (by linarith) (by linarith)
  have hne' : q'.1 - p.1 ≠ 0 ∨ q'.2 - p.2 ≠ 0 := by
    by_contra h0
    push Not at h0
    apply hpq'
    exact Prod.ext (by linarith) (by linarith)
  constructor
  · intro hr
    have hmul1 : (q.1 - p.1) * ((q'.1 - p.1) * (r.2 - p.2) - (q'.2 - p.2) * (r.1 - p.1)) = 0 := by
      calc (q.1 - p.1) * ((q'.1 - p.1) * (r.2 - p.2) - (q'.2 - p.2) * (r.1 - p.1))
          = (q'.1 - p.1) * ((q.1 - p.1) * (r.2 - p.2)) - ((q.1 - p.1) * (q'.2 - p.2)) * (r.1 - p.1) := by ring
        _ = (q'.1 - p.1) * ((q.2 - p.2) * (r.1 - p.1)) - ((q.2 - p.2) * (q'.1 - p.1)) * (r.1 - p.1) := by rw [hr, h]
        _ = 0 := by ring
    have hmul2 : (q.2 - p.2) * ((q'.1 - p.1) * (r.2 - p.2) - (q'.2 - p.2) * (r.1 - p.1)) = 0 := by
      calc (q.2 - p.2) * ((q'.1 - p.1) * (r.2 - p.2) - (q'.2 - p.2) * (r.1 - p.1))
          = ((q.2 - p.2) * (q'.1 - p.1)) * (r.2 - p.2) - (q'.2 - p.2) * ((q.2 - p.2) * (r.1 - p.1)) := by ring
        _ = ((q.1 - p.1) * (q'.2 - p.2)) * (r.2 - p.2) - (q'.2 - p.2) * ((q.1 - p.1) * (r.2 - p.2)) := by rw [← h, ← hr]
        _ = 0 := by ring
    have hzero : (q'.1 - p.1) * (r.2 - p.2) - (q'.2 - p.2) * (r.1 - p.1) = 0 := by
      rcases hne with h1 | h2
      · exact (mul_eq_zero.mp hmul1).resolve_left h1
      · exact (mul_eq_zero.mp hmul2).resolve_left h2
    linarith
  · intro hr
    have hmul1 : (q'.1 - p.1) * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) = 0 := by
      calc (q'.1 - p.1) * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1))
          = (q.1 - p.1) * ((q'.1 - p.1) * (r.2 - p.2)) - ((q.2 - p.2) * (q'.1 - p.1)) * (r.1 - p.1) := by ring
        _ = (q.1 - p.1) * ((q'.2 - p.2) * (r.1 - p.1)) - ((q.1 - p.1) * (q'.2 - p.2)) * (r.1 - p.1) := by rw [hr, ← h]
        _ = 0 := by ring
    have hmul2 : (q'.2 - p.2) * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)) = 0 := by
      calc (q'.2 - p.2) * ((q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1))
          = ((q.1 - p.1) * (q'.2 - p.2)) * (r.2 - p.2) - (q.2 - p.2) * ((q'.2 - p.2) * (r.1 - p.1)) := by ring
        _ = ((q.2 - p.2) * (q'.1 - p.1)) * (r.2 - p.2) - (q.2 - p.2) * ((q'.1 - p.1) * (r.2 - p.2)) := by rw [h, ← hr]
        _ = 0 := by ring
    have hzero : (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1) = 0 := by
      rcases hne' with h1 | h2
      · exact (mul_eq_zero.mp hmul1).resolve_left h1
      · exact (mul_eq_zero.mp hmul2).resolve_left h2
    linarith

private lemma numLinesThrough_le_four (S : Finset (ℝ × ℝ)) (p q1 q2 q3 q4 : ℝ × ℝ)
    (h1 : p ≠ q1) (h2 : p ≠ q2) (h3 : p ≠ q3) (h4 : p ≠ q4)
    (hcov : ∀ q ∈ S, q ≠ p →
      collinear3 p q1 q ∨ collinear3 p q2 q ∨ collinear3 p q3 q ∨ collinear3 p q4 q) :
    numLinesThrough S p ≤ 4 := by
  classical
  unfold numLinesThrough
  let L : ℝ × ℝ → Finset (ℝ × ℝ) := fun q => S.filter (fun r => collinear3 p q r)
  have hsub : (S.erase p).image L ⊆ ({L q1, L q2, L q3, L q4} : Finset (Finset (ℝ × ℝ))) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨q, hq, rfl⟩ := hA
    rw [Finset.mem_erase] at hq
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcov q hq.2 hq.1 with hc | hc | hc | hc
    · left; ext r; simp only [L, Finset.mem_filter]; exact and_congr_right (fun _ => (collinear3_eq_of_collinear h1 hq.1.symm hc r).symm)
    · right; left; ext r; simp only [L, Finset.mem_filter]; exact and_congr_right (fun _ => (collinear3_eq_of_collinear h2 hq.1.symm hc r).symm)
    · right; right; left; ext r; simp only [L, Finset.mem_filter]; exact and_congr_right (fun _ => (collinear3_eq_of_collinear h3 hq.1.symm hc r).symm)
    · right; right; right; ext r; simp only [L, Finset.mem_filter]; exact and_congr_right (fun _ => (collinear3_eq_of_collinear h4 hq.1.symm hc r).symm)
  calc ((S.erase p).image L).card
      ≤ ({L q1, L q2, L q3, L q4} : Finset (Finset (ℝ × ℝ))).card := Finset.card_le_card hsub
    _ ≤ 4 := by
      have c1 := Finset.card_insert_le (L q1) ({L q2, L q3, L q4} : Finset (Finset (ℝ × ℝ)))
      have c2 := Finset.card_insert_le (L q2) ({L q3, L q4} : Finset (Finset (ℝ × ℝ)))
      have c3 := Finset.card_insert_le (L q3) ({L q4} : Finset (Finset (ℝ × ℝ)))
      rw [Finset.card_singleton] at c3
      omega

private def p0 : ℝ × ℝ := (10, 10)
private def p1 : ℝ × ℝ := (20, -20)
private def p2 : ℝ × ℝ := (-15, 15)
private def p3 : ℝ × ℝ := (-60, -60)
private def p4 : ℝ × ℝ := (0, 0)
private def p5 : ℝ × ℝ := (60, 0)
private def p6 : ℝ × ℝ := (0, 40)
private def p7 : ℝ × ℝ := (24, 24)
private def p8 : ℝ × ℝ := (-120, 120)

open Classical in
private noncomputable def S9 : Finset (ℝ × ℝ) :=
  {p0, p1, p2, p3, p4, p5, p6, p7, p8}

private lemma S9_card : S9.card = 9 := by
  classical
  unfold S9
  repeat rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, p0, p1, p2, p3, p4, p5, p6, p7, p8]
    norm_num)]
  rw [Finset.card_singleton]

private lemma S9_not_collinear : ∃ p ∈ S9, ∃ q ∈ S9, ∃ r ∈ S9, ¬ collinear3 p q r := by
  refine ⟨p4, by simp [S9], p5, by simp [S9], p6, by simp [S9], ?_⟩
  norm_num [collinear3, p4, p5, p6]

private theorem disprove_main : ¬ (type_of% @OMA.S_oeis_a058211.main) := by
  intro h
  obtain ⟨p, hp, hcard⟩ := h S9 S9_not_collinear
  rw [S9_card] at hcard
  have hle4 : numLinesThrough S9 p ≤ 4 := by
    simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · apply numLinesThrough_le_four S9 p0 p1 p2 p3 p8
      · intro heq; have := congrArg Prod.fst heq; norm_num [p0, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p0, p2] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p0, p3] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p0, p8] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hne
        · left; norm_num [collinear3, p0, p1, p1]
        · right; left; norm_num [collinear3, p0, p2, p2]
        · right; right; left; norm_num [collinear3, p0, p3, p3]
        · right; right; left; norm_num [collinear3, p0, p3, p4]
        · right; left; norm_num [collinear3, p0, p2, p5]
        · left; norm_num [collinear3, p0, p1, p6]
        · right; right; left; norm_num [collinear3, p0, p3, p7]
        · right; right; right; norm_num [collinear3, p0, p8, p8]
    · apply numLinesThrough_le_four S9 p1 p0 p2 p3 p7
      · intro heq; have := congrArg Prod.fst heq; norm_num [p1, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p1, p2] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p1, p3] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p1, p7] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p1, p0, p0]
        · exact absurd rfl hne
        · right; left; norm_num [collinear3, p1, p2, p2]
        · right; right; left; norm_num [collinear3, p1, p3, p3]
        · right; left; norm_num [collinear3, p1, p2, p4]
        · right; right; left; norm_num [collinear3, p1, p3, p5]
        · left; norm_num [collinear3, p1, p0, p6]
        · right; right; right; norm_num [collinear3, p1, p7, p7]
        · right; left; norm_num [collinear3, p1, p2, p8]
    · apply numLinesThrough_le_four S9 p2 p0 p1 p3 p7
      · intro heq; have := congrArg Prod.fst heq; norm_num [p2, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p2, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p2, p3] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p2, p7] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p2, p0, p0]
        · right; left; norm_num [collinear3, p2, p1, p1]
        · exact absurd rfl hne
        · right; right; left; norm_num [collinear3, p2, p3, p3]
        · right; left; norm_num [collinear3, p2, p1, p4]
        · left; norm_num [collinear3, p2, p0, p5]
        · right; right; left; norm_num [collinear3, p2, p3, p6]
        · right; right; right; norm_num [collinear3, p2, p7, p7]
        · right; left; norm_num [collinear3, p2, p1, p8]
    · apply numLinesThrough_le_four S9 p3 p0 p1 p2 p8
      · intro heq; have := congrArg Prod.fst heq; norm_num [p3, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p3, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p3, p2] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p3, p8] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p3, p0, p0]
        · right; left; norm_num [collinear3, p3, p1, p1]
        · right; right; left; norm_num [collinear3, p3, p2, p2]
        · exact absurd rfl hne
        · left; norm_num [collinear3, p3, p0, p4]
        · right; left; norm_num [collinear3, p3, p1, p5]
        · right; right; left; norm_num [collinear3, p3, p2, p6]
        · left; norm_num [collinear3, p3, p0, p7]
        · right; right; right; norm_num [collinear3, p3, p8, p8]
    · apply numLinesThrough_le_four S9 p4 p0 p1 p5 p6
      · intro heq; have := congrArg Prod.fst heq; norm_num [p4, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p4, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p4, p5] at this
      · intro heq; have := congrArg Prod.snd heq; norm_num [p4, p6] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p4, p0, p0]
        · right; left; norm_num [collinear3, p4, p1, p1]
        · right; left; norm_num [collinear3, p4, p1, p2]
        · left; norm_num [collinear3, p4, p0, p3]
        · exact absurd rfl hne
        · right; right; left; norm_num [collinear3, p4, p5, p5]
        · right; right; right; norm_num [collinear3, p4, p6, p6]
        · left; norm_num [collinear3, p4, p0, p7]
        · right; left; norm_num [collinear3, p4, p1, p8]
    · apply numLinesThrough_le_four S9 p5 p0 p1 p4 p6
      · intro heq; have := congrArg Prod.fst heq; norm_num [p5, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p5, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p5, p4] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p5, p6] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p5, p0, p0]
        · right; left; norm_num [collinear3, p5, p1, p1]
        · left; norm_num [collinear3, p5, p0, p2]
        · right; left; norm_num [collinear3, p5, p1, p3]
        · right; right; left; norm_num [collinear3, p5, p4, p4]
        · exact absurd rfl hne
        · right; right; right; norm_num [collinear3, p5, p6, p6]
        · right; right; right; norm_num [collinear3, p5, p6, p7]
        · right; right; right; norm_num [collinear3, p5, p6, p8]
    · apply numLinesThrough_le_four S9 p6 p0 p2 p4 p5
      · intro heq; have := congrArg Prod.fst heq; norm_num [p6, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p6, p2] at this
      · intro heq; have := congrArg Prod.snd heq; norm_num [p6, p4] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p6, p5] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p6, p0, p0]
        · left; norm_num [collinear3, p6, p0, p1]
        · right; left; norm_num [collinear3, p6, p2, p2]
        · right; left; norm_num [collinear3, p6, p2, p3]
        · right; right; left; norm_num [collinear3, p6, p4, p4]
        · right; right; right; norm_num [collinear3, p6, p5, p5]
        · exact absurd rfl hne
        · right; right; right; norm_num [collinear3, p6, p5, p7]
        · right; right; right; norm_num [collinear3, p6, p5, p8]
    · apply numLinesThrough_le_four S9 p7 p0 p1 p2 p5
      · intro heq; have := congrArg Prod.fst heq; norm_num [p7, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p7, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p7, p2] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p7, p5] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p7, p0, p0]
        · right; left; norm_num [collinear3, p7, p1, p1]
        · right; right; left; norm_num [collinear3, p7, p2, p2]
        · left; norm_num [collinear3, p7, p0, p3]
        · left; norm_num [collinear3, p7, p0, p4]
        · right; right; right; norm_num [collinear3, p7, p5, p5]
        · right; right; right; norm_num [collinear3, p7, p5, p6]
        · exact absurd rfl hne
        · right; right; right; norm_num [collinear3, p7, p5, p8]
    · apply numLinesThrough_le_four S9 p8 p0 p1 p3 p5
      · intro heq; have := congrArg Prod.fst heq; norm_num [p8, p0] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p8, p1] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p8, p3] at this
      · intro heq; have := congrArg Prod.fst heq; norm_num [p8, p5] at this
      · intro q hq hne
        simp only [S9, Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · left; norm_num [collinear3, p8, p0, p0]
        · right; left; norm_num [collinear3, p8, p1, p1]
        · right; left; norm_num [collinear3, p8, p1, p2]
        · right; right; left; norm_num [collinear3, p8, p3, p3]
        · right; left; norm_num [collinear3, p8, p1, p4]
        · right; right; right; norm_num [collinear3, p8, p5, p5]
        · right; right; right; norm_num [collinear3, p8, p5, p6]
        · right; right; right; norm_num [collinear3, p8, p5, p7]
        · exact absurd rfl hne
  omega

end OMA.D_oeis_a058211

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a058211.main) :=
  OMA.D_oeis_a058211.disprove_main
