import OMAStatements.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl

-- Problem: Is the line graph of a non-word-representable graph always non-word-representable?
-- Credit: @sobrien032

/-!
The Grötzsch graph gives a counterexample to the line-graph question.
Khyodeno Mozhui, Tithi Dwary and K. V. Krishna prove the line-graph result
in Theorem 3 of arXiv:2509.03339, and cite Sergey Kitaev and Artem Pyatkin
for non-representability of the original graph. We certify both sides for
the Mycielski graph of the pentagon.
-/

open OMA.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl

namespace WordExample

/-- The endpoint pairs of the twenty edges of the Mycielski graph of the pentagon. -/
def ends : Fin 20 → Fin 11 × Fin 11 :=
  ![(0,1), (0,4), (0,6), (0,9), (1,2), (1,5), (1,7), (2,3), (2,6), (2,8), (3,4), (3,7), (3,9), (4,5), (4,8), (5,10), (6,10), (7,10), (8,10), (9,10)]

abbrev G : SimpleGraph (Fin 11) :=
  SimpleGraph.fromRel (fun a b : Fin 11 => ∃ i : Fin 20, ends i = (a,b))

def share (i j : Fin 20) : Prop :=
  (ends i).1 = (ends j).1 ∨ (ends i).1 = (ends j).2 ∨
  (ends i).2 = (ends j).1 ∨ (ends i).2 = (ends j).2

instance (i j : Fin 20) : Decidable (share i j) := by
  unfold share
  infer_instance

end WordExample

namespace WordSquare
variable {V : Type} [DecidableEq V]

private def keep (w : List V) (a b : V) : List V :=
  w.filter fun x => decide (x = a ∨ x = b)

private lemma keep_flip (w : List V) (a b : V) : keep w b a = keep w a b := by
  simp only [keep, or_comm]

private lemma keep_left (w : List V) (a b : V) : keep (a::w) a b = a :: keep w a b := by
  simp [keep]

private lemma keep_right (w : List V) (a b : V) : keep (b::w) a b = b :: keep w a b := by
  simp [keep]

private lemma keep_other {w : List V} {x a b : V} (ha : x ≠ a) (hb : x ≠ b) :
    keep (x::w) a b = keep w a b := by simp [keep, ha, hb]

-- Prepending a dummy b prescribes that the next letter of the pair is a.
private def expect (w : List V) (a b : V) := List.IsChain (· ≠ ·) (b :: keep w a b)

private lemma expect_left {w : List V} {a b : V} (h : a ≠ b) :
    expect (a::w) a b ↔ expect w b a := by
  simp only [expect, keep_left, List.isChain_cons_cons, keep_flip w a b]
  exact and_iff_right h.symm

private lemma expect_bad {w : List V} {a b : V} : ¬ expect (b::w) a b := by
  simp [expect, keep_right, List.isChain_cons_cons]

private lemma expect_other {w : List V} {x a b : V} (ha : x ≠ a) (hb : x ≠ b) :
    expect (x::w) a b ↔ expect w a b := by rw [expect, expect, keep_other ha hb]

private lemma expect_of_first {w : List V} {a b : V} (rank : w.idxOf a < w.idxOf b)
    (alt : Alternate w a b) : expect w a b := by
  have hab : a ≠ b := by rintro rfl; omega
  induction w with
  | nil => simp at rank
  | cons x w ih =>
    change List.IsChain (· ≠ ·) (keep (x::w) a b) at alt
    by_cases hx : x=a
    · subst x
      rw [keep_left] at alt
      unfold expect
      rw [keep_left, List.isChain_cons_cons]
      exact ⟨hab.symm, alt⟩
    · by_cases hy : x=b
      · subst x; simp at rank
      · apply (expect_other hx hy).2
        rw [keep_other hx hy] at alt
        apply ih _ alt
        simpa [List.idxOf_cons, hx, hy] using rank

-- Only a can be read next. Reading it rotates the four constraints.
private lemma chords (w : List V) {a b c d : V}
    (ab : a ≠ b) (bc : b ≠ c) (cd : c ≠ d) (da : d ≠ a) (ac : a ≠ c) (bd : b ≠ d)
    (eab : expect w a b) (ebc : expect w b c) (ecd : expect w c d) (ead : expect w a d) :
    expect w a c ∧ expect w b d := by
  induction w generalizing a b c d with
  | nil => simp [expect, keep]
  | cons x w ih =>
    by_cases hx : x = a
    · subst x
      have h := ih bc cd da ab bd ac.symm ((expect_other ab ac).1 ebc)
        ((expect_other ac da.symm).1 ecd) ((expect_left da.symm).1 ead) ((expect_left ab).1 eab)
      exact ⟨(expect_left ac).2 h.2, (expect_other ab da.symm).2 h.1⟩
    · by_cases hy : x = b
      · subst x; exact (expect_bad eab).elim
      · by_cases hz : x = c
        · subst x; exact (expect_bad ebc).elim
        · by_cases ht : x = d
          · subst x; exact (expect_bad ecd).elim
          · have h := ih ab bc cd da ac bd ((expect_other hx hy).1 eab)
              ((expect_other hy hz).1 ebc) ((expect_other hz ht).1 ecd) ((expect_other hx ht).1 ead)
            exact ⟨(expect_other hx hz).2 h.1, (expect_other hy ht).2 h.2⟩

theorem noShortcut {w : List V} {a b c d : V}
    (rab : w.idxOf a < w.idxOf b) (rbc : w.idxOf b < w.idxOf c) (rcd : w.idxOf c < w.idxOf d)
    (ab : Alternate w a b) (bc : Alternate w b c) (cd : Alternate w c d) (ad : Alternate w a d) :
    Alternate w a c := by
  have ne {x y : V} (h : w.idxOf x < w.idxOf y) : x ≠ y := by rintro rfl; omega
  have h := chords w (ne rab) (ne rbc) (ne rcd) (ne (rab.trans (rbc.trans rcd))).symm
    (ne (rab.trans rbc)) (ne (rbc.trans rcd)) (expect_of_first rab ab) (expect_of_first rbc bc)
    (expect_of_first rcd cd) (expect_of_first (rab.trans (rbc.trans rcd)) ad)
  exact (List.isChain_cons.1 h.1).2

def sgn (w : List V) (a b : V) : ℤ := if w.idxOf a < w.idxOf b then 1 else -1

theorem sgn_neg {w : List V} (cover : ∀ v, v ∈ w) {x y : V} (hxy : x≠y) :
    sgn w y x = -sgn w x y := by
  have h := (List.idxOf_inj (cover x)).not.mpr hxy
  unfold sgn
  split_ifs <;> omega

theorem square_balance {G : SimpleGraph V} {w : List V}
    (rep : ∀ a b, a ≠ b → (G.Adj a b ↔ Alternate w a b)) (cover : ∀ v, v ∈ w)
    {a b c d : V} (eab : G.Adj a b) (ebc : G.Adj b c) (ecd : G.Adj c d) (eda : G.Adj d a)
    (nac : ¬ G.Adj a c) (nbd : ¬ G.Adj b d) (hac : a ≠ c) (hbd : b ≠ d) :
    sgn w a b + sgn w b c + sgn w c d + sgn w d a = 0 := by
  have bad {x y z t : V} (e1 : G.Adj x y) (e2 : G.Adj y z) (e3 : G.Adj z t)
      (e4 : G.Adj t x) (n : ¬ G.Adj x z) (h : x ≠ z) :
      ¬ (w.idxOf x < w.idxOf y ∧ w.idxOf y < w.idxOf z ∧ w.idxOf z < w.idxOf t) := by
    rintro ⟨r,s,u⟩
    apply n
    apply (rep x z h).2
    exact noShortcut r s u ((rep x y e1.ne).1 e1) ((rep y z e2.ne).1 e2)
      ((rep z t e3.ne).1 e3) ((rep x t e4.ne.symm).1 e4.symm)
  have h1 := bad eab ebc ecd eda nac hac
  have h2 := bad ebc ecd eda eab nbd hbd
  have h3 := bad ecd eda eab ebc (fun h => nac h.symm) hac.symm
  have h4 := bad eda eab ebc ecd (fun h => nbd h.symm) hbd.symm
  have h5 := bad eda.symm ecd.symm ebc.symm eab.symm nac hac
  have h6 := bad ecd.symm ebc.symm eab.symm eda.symm (fun h => nbd h.symm) hbd.symm
  have h7 := bad ebc.symm eab.symm eda.symm ecd.symm (fun h => nac h.symm) hac.symm
  have h8 := bad eab.symm eda.symm ecd.symm ebc.symm nbd hbd
  have r1 := (List.idxOf_inj (cover a)).not.mpr eab.ne
  have r2 := (List.idxOf_inj (cover b)).not.mpr ebc.ne
  have r3 := (List.idxOf_inj (cover c)).not.mpr ecd.ne
  have r4 := (List.idxOf_inj (cover d)).not.mpr eda.ne
  unfold sgn
  split_ifs <;> omega
end WordSquare

namespace WordExample

/-- The ten induced squares of the Grötzsch graph cannot all have balanced signs. -/
private theorem noBalancedSigns (s : Fin 11 → Fin 11 → ℤ)
    (reverse : ∀ a b, a ≠ b → s b a = -s a b)
    (unitSign : ∀ a b, s a b = 1 ∨ s a b = -1)
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      ¬ G.Adj a c → ¬ G.Adj b d → a ≠ c → b ≠ d →
      s a b + s b c + s c d + s d a = 0) : False := by
  have q0 := square 0 1 2 6
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 0 6 (by decide)] at q0
  have q1 := square 0 1 5 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 4 5 (by decide), reverse 0 4 (by decide)] at q1
  have q2 := square 0 4 3 9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 3 4 (by decide), reverse 0 9 (by decide)] at q2
  have q3 := square 0 6 10 9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 9 10 (by decide), reverse 0 9 (by decide)] at q3
  have q4 := square 1 2 3 7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 1 7 (by decide)] at q4
  have q5 := square 1 5 10 7
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 7 10 (by decide), reverse 1 7 (by decide)] at q5
  have q6 := square 2 3 4 8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 2 8 (by decide)] at q6
  have q7 := square 2 6 10 8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 8 10 (by decide), reverse 2 8 (by decide)] at q7
  have q8 := square 3 7 10 9
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 9 10 (by decide), reverse 3 9 (by decide)] at q8
  have q9 := square 4 5 10 8
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [reverse 8 10 (by decide), reverse 4 8 (by decide)] at q9
  have twice : 2 * (s 0 1 + s 1 2 + s 2 3 + s 3 4 - s 0 4) = 0 := by
    linear_combination q0 + q1 - q2 + q3 + q4 - q5 + q6 - q7 - q8 + q9
  have h01 := unitSign 0 1
  have h12 := unitSign 1 2
  have h23 := unitSign 2 3
  have h34 := unitSign 3 4
  have h04 := unitSign 0 4
  clear q0 q1 q2 q3 q4 q5 q6 q7 q8 q9
  omega

end WordExample

namespace WordExample

/-- A five-uniform word for the line graph in the orientation of
Khyodeno Mozhui, Tithi Dwary and K. V. Krishna (Theorem 3). -/
def word : List (Fin 20) :=
  [
    11, 13, 8, 5, 14, 12, 2, 3, 9, 10, 7, 6, 4, 1, 0, 15,
    13, 5, 16, 17, 11, 6, 18, 19, 12, 15, 8, 2, 16, 17, 14, 3,
    10, 9, 1, 18, 19, 13, 14, 7, 11, 12, 10, 4, 8, 9, 7, 0,
    5, 6, 15, 4, 2, 16, 17, 8, 11, 3, 18, 19, 12, 1, 0, 2,
    3, 13, 14, 10, 1, 5, 15, 13, 9, 6, 7, 4, 16, 8, 0, 5,
    2, 17, 18, 14, 9, 19, 15, 16, 11, 6, 17, 18, 12, 3, 19, 10,
    1, 7, 4, 0]

theorem wordCovers : ∀ i : Fin 20, i ∈ word := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 12000 in
theorem wordPairs : ∀ i j : Fin 20, i ≠ j → (share i j ↔ Alternate word i j) := by
  unfold share Alternate
  decide

end WordExample

namespace WordExample

private theorem distinctEnds : ∀ i : Fin 20, (ends i).1 ≠ (ends i).2 := by decide

private def edgeLetter (i : Fin 20) : G.edgeSet :=
  ⟨s((ends i).1, (ends i).2), ⟨distinctEnds i, Or.inl ⟨i, rfl⟩⟩⟩

private theorem edgeLetter_injective : Function.Injective edgeLetter := by
  have h : ∀ i j : Fin 20,
      (((ends i).1 = (ends j).1 ∧ (ends i).2 = (ends j).2) ∨
       ((ends i).1 = (ends j).2 ∧ (ends i).2 = (ends j).1)) → i = j := by decide
  intro i j he
  exact h i j (Sym2.eq_iff.mp (congrArg Subtype.val he))

private theorem edgeLetter_surjective : Function.Surjective edgeLetter := by
  rintro ⟨e,he⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    change a ≠ b ∧ ((∃ i, ends i = (a,b)) ∨ ∃ i, ends i = (b,a)) at he
    rcases he.2 with ⟨i,hi⟩ | ⟨i,hi⟩
    · refine ⟨i, Subtype.ext ?_⟩
      change s((ends i).1, (ends i).2) = s(a,b)
      rw [hi]
    · refine ⟨i, Subtype.ext ?_⟩
      change s((ends i).1, (ends i).2) = s(a,b)
      rw [hi]
      exact Sym2.eq_swap

private theorem edgeLetter_adj {i j : Fin 20} (hij : i ≠ j) :
    G.lineGraph.Adj (edgeLetter i) (edgeLetter j) ↔ share i j := by
  rw [SimpleGraph.lineGraph_adj_iff_exists, and_iff_right (fun h => hij (edgeLetter_injective h))]
  change (∃ x : Fin 11, x ∈ s((ends i).1, (ends i).2) ∧ x ∈ s((ends j).1, (ends j).2)) ↔ _
  simp [Sym2.mem_iff, or_and_right, exists_or, share, or_assoc]

private theorem edgeLetter_alternate (word : List (Fin 20)) (i j : Fin 20) :
    Alternate (word.map edgeLetter) (edgeLetter i) (edgeLetter j) ↔ Alternate word i j := by
  simp [Alternate, List.filter_map, List.isChain_map, Function.comp_def, edgeLetter_injective.eq_iff]

theorem lineGraphRep (word : List (Fin 20)) (covers : ∀ i, i ∈ word)
    (pairs : ∀ i j, i ≠ j → (share i j ↔ Alternate word i j)) :
    IsWordRepresentable G.lineGraph := by
  refine ⟨word.map edgeLetter, ?_, ?_⟩
  · intro e
    obtain ⟨i,rfl⟩ := edgeLetter_surjective e
    exact List.mem_map.mpr ⟨i, covers i, rfl⟩
  · intro a b hab
    obtain ⟨i,rfl⟩ := edgeLetter_surjective a
    obtain ⟨j,rfl⟩ := edgeLetter_surjective b
    have hij : i ≠ j := fun h => hab (congrArg edgeLetter h)
    exact (edgeLetter_adj hij).trans ((pairs i j hij).trans (edgeLetter_alternate word i j).symm)

end WordExample

namespace WordExample

private theorem notRepresentable : ¬ IsWordRepresentable G := by
  rintro ⟨w, cover, rep⟩
  apply noBalancedSigns (WordSquare.sgn w)
  · intro a b hab
    exact WordSquare.sgn_neg cover hab
  · intro a b
    unfold WordSquare.sgn
    split <;> simp
  · intro a b c d eab ebc ecd eda nac nbd hac hbd
    exact WordSquare.square_balance rep cover eab ebc ecd eda nac nbd hac hbd

end WordExample

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_is_the_line_graph_of_a_non_word_representable_graph_always_non_word_representabl.main) := by
  intro claim
  exact claim (Fin 11) WordExample.G WordExample.notRepresentable
    (WordExample.lineGraphRep WordExample.word WordExample.wordCovers WordExample.wordPairs)
