import OMAStatements.S_oeis_a307554
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
An anchored spanning path on an n-by-n board extends to side n+8. First
attach an 8-by-n strip at the right edge and then an (n+8)-by-8 strip at
the top. Two types of width-eight paths supply the necessary endpoints.
Each extends by prefixing an 8-by-8 path. Thus only widths 8 through 15
require explicit witnesses. The finite certificates at the end of the
file are lists of squares checked by the kernel.
-/

/-!
Credit: @wtho704. This is the complete proof linked by statement PR #22118,
ported from commit 958e6d75f0a526cad5a8ee6adb624e25a352dd73 without mathematical changes.
Source: https://github.com/wtho704/open-math-agents/blob/958e6d75f0a526cad5a8ee6adb624e25a352dd73/proofs/oeis-a307554.lean
Port and current-checker validation: @rodolfoquint.
-/

open OMA.S_oeis_a307554 Finset

namespace OMA.Fiveleaper

/-- A simple path in a specified region, with fixed endpoints and vertex count. -/
def Route (area : Square → Prop) (a b : Square) (k : ℕ) : Prop :=
  ∃ l : List Square, pathOn area l ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.length = k

private theorem mapRoute {P Q : Square → Prop} {a b : Square} {k : ℕ} (f : Square → Square)
    (inj : Function.Injective f) (moves : ∀ p q, jump p q → jump (f p) (f q))
    (inside : ∀ p, P p → Q (f p)) (h : Route P a b k) : Route Q (f a) (f b) k := by
  obtain ⟨l, ⟨hn, hc, hb⟩, ha, he, hk⟩ := h
  refine ⟨l.map f, ⟨hn.map inj, (List.isChain_map f).2 (hc.imp moves), ?_⟩, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact inside p (hb p hp)
  · simp [ha]
  · simp [he]
  · simpa using hk

private theorem reverseRoute {P : Square → Prop} {a b : Square} {k : ℕ}
    (h : Route P a b k) : Route P b a k := by
  obtain ⟨l, ⟨hn, hc, hb⟩, ha, he, hk⟩ := h
  refine ⟨l.reverse, ⟨by simpa using hn, List.isChain_reverse.mpr (hc.imp ?_), ?_⟩, ?_, ?_, ?_⟩
  · intro p q hp
    unfold jump at hp ⊢
    rw [← hp]
    ring
  · intro p hp
    exact hb p (List.mem_reverse.mp hp)
  · simpa using he
  · simpa using ha
  · simpa using hk

private theorem splice {P Q R : Square → Prop} {a b c d : Square} {s t : ℕ}
    (h : Route P a b s) (k : Route Q c d t) (edge : jump b c)
    (left : ∀ p, P p → R p) (right : ∀ p, Q p → R p)
    (apart : ∀ p, P p → Q p → False) : Route R a d (s + t) := by
  obtain ⟨l, ⟨hl, cl, bl⟩, fl, el, nl⟩ := h
  obtain ⟨r, ⟨hr, cr, br⟩, fr, er, nr⟩ := k
  refine ⟨l ++ r, ⟨hl.append hr ?_, List.isChain_append.mpr ⟨cl, cr, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · intro p hp hq
    exact apart p (bl p hp) (br p hq)
  · simpa [el, fr] using edge
  · intro p hp
    rcases List.mem_append.mp hp with hpl | hpr
    · exact left p (bl p hpl)
    · exact right p (br p hpr)
  · simp [fl]
  · simp [er]
  · simp [nl, nr]

private def portA (w : ℕ) : Square :=
  ((w : ℤ) - 3, if w % 2 = 0 then 2 else 5)

private def portB (w : ℕ) : Square :=
  ((w : ℤ) - (if w % 2 = 0 then 6 else 3), 5)

private def stripA (w : ℕ) : Prop := Route (box 0 w 0 8) (2,2) (portA w) (w * 8)
private def stripB (w : ℕ) : Prop := Route (box 0 w 0 8) (2,2) (portB w) (w * 8)
private def anchored (n : ℕ) : Prop :=
  ∃ a : Square, Route (box 0 n 0 n) a ((n : ℤ) - 3, 2) (n * n)

private abbrev StripBases := ∀ w, 8 ≤ w → w ≤ 15 → stripA w ∧ stripB w
private abbrev SquareBases := ∀ w, 8 ≤ w → w ≤ 15 → anchored w

private def east (p : Square) : Square := (p.1 + 8, p.2)

private theorem extendStrip (tile : stripA 8) {w : ℕ} {b : Square}
    (h : Route (box 0 w 0 8) (2,2) b (w * 8)) :
    Route (box 0 (w + 8 : ℕ) 0 8) (2,2) (east b) ((w + 8) * 8) := by
  have shifted := mapRoute (Q := box 8 ((w : ℤ) + 8) 0 8) east
    (by intro p q e; simpa [east, Prod.ext_iff] using e)
    (by intro p q e; simpa [east, jump] using e)
    (by intro p hp; unfold east box at *; dsimp at *; omega) h
  have bridge : jump (portA 8) (east (2,2)) := by decide
  have both := splice (R := box 0 ((w : ℤ) + 8) 0 8) tile shifted bridge
    (by intro p hp; unfold box at *; omega)
    (by intro p hp; unfold box at *; omega)
    (by intro p hp hq; unfold box at *; omega)
  have size_eq : (w + 8) * 8 = 8 * 8 + w * 8 := by omega
  rw [size_eq]
  simpa using both

private theorem allStrips (base : StripBases) : ∀ w, 8 ≤ w → stripA w ∧ stripB w := by
  intro w
  induction w using Nat.strong_induction_on with
  | h w ih =>
    intro hw
    by_cases hsmall : w ≤ 15
    · exact base w hw hsmall
    · obtain ⟨v, rfl⟩ : ∃ v, w = v + 8 := ⟨w - 8, by omega⟩
      have hv := ih v (by omega) (by omega)
      have tile := (base 8 (by decide) (by decide)).1
      have ha := extendStrip tile hv.1
      have hb := extendStrip tile hv.2
      have hmod : (v + 8) % 2 = v % 2 := by omega
      have ea : east (portA v) = portA (v + 8) := by
        simp [east, portA, hmod]; omega
      have eb : east (portB v) = portB (v + 8) := by
        simp [east, portB, hmod]; omega
      rw [ea] at ha
      rw [eb] at hb
      exact ⟨ha, hb⟩

private def toRight (n : ℕ) (p : Square) : Square := ((n : ℤ) + p.2, p.1)
private def toTop (n : ℕ) (p : Square) : Square := (p.1, (n : ℤ) + 7 - p.2)

private theorem growSquare (base : StripBases) {n : ℕ} (hn : 8 ≤ n) (old : anchored n) :
    anchored (n + 8) := by
  obtain ⟨a, old⟩ := old
  have vertical := mapRoute (Q := box n ((n : ℤ) + 8) 0 n) (toRight n)
    (by intro p q e; ext <;> simp [toRight, Prod.ext_iff] at e <;> omega)
    (by intro p q h; unfold jump toRight at *; dsimp; rw [← h]; ring)
    (by intro p hp; unfold box toRight at *; dsimp; omega) (allStrips base n hn).1
  have horizontal := mapRoute (Q := box 0 ((n : ℤ) + 8) n ((n : ℤ) + 8)) (toTop n)
    (by intro p q e; ext <;> simp [toTop, Prod.ext_iff] at e <;> omega)
    (by intro p q h; unfold jump toTop at *; dsimp; rw [← h]; ring)
    (by intro p hp; unfold box toTop at *; dsimp; push_cast at hp; omega)
    (reverseRoute (allStrips base (n+8) (by omega)).2)
  have first : jump ((n : ℤ) - 3, 2) (toRight n (2,2)) := by
    unfold jump toRight
    dsimp
    ring
  have hmod : (n+8) % 2 = n % 2 := by omega
  have second : jump (toRight n (portA n)) (toTop n (portB (n+8))) := by
    by_cases he : n % 2 = 0 <;> simp [jump, toRight, toTop, portA, portB, hmod, he] <;> ring
  have bottom := splice (R := box 0 ((n : ℤ) + 8) 0 n) old vertical first
    (by intro p hp; unfold box at *; omega)
    (by intro p hp; unfold box at *; omega)
    (by intro p hp hq; unfold box at *; omega)
  have big := splice (R := box 0 ((n : ℤ) + 8) 0 ((n : ℤ) + 8)) bottom horizontal second
    (by intro p hp; unfold box at *; omega)
    (by intro p hp; unfold box at *; omega)
    (by intro p hp hq; unfold box at *; omega)
  have turned := mapRoute (Q := box 0 ((n : ℤ) + 8) 0 ((n : ℤ) + 8)) Prod.swap
    Prod.swap_injective (by intro p q h; unfold jump at *; simpa [add_comm] using h)
    (by intro p hp; unfold box at *; dsimp; omega) big
  refine ⟨a.swap, ?_⟩
  have hsize : n * n + n * 8 + (n + 8) * 8 = (n + 8) * (n + 8) := by ring
  have hend : (toTop n (2,2)).swap = (((n+8 : ℕ) : ℤ) - 3, 2) := by
    apply Prod.ext
    · simp [toTop]
      omega
    · rfl
  rw [hsize, hend] at turned
  simpa using turned

private theorem allSquares (strips : StripBases) (squares : SquareBases) :
    ∀ n, 8 ≤ n → anchored n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n ≤ 15
    · exact squares n hn hsmall
    · obtain ⟨v, rfl⟩ : ∃ v, n = v + 8 := ⟨n - 8, by omega⟩
      exact growSquare strips (by omega) (ih v (by omega) (by omega))

private def cells (n : ℕ) : Finset Square :=
  (Ico (0 : ℤ) n) ×ˢ (Ico (0 : ℤ) n)

private theorem mem_cells {n : ℕ} {p : Square} : p ∈ cells n ↔ box 0 n 0 n p := by
  simp [cells, box, and_assoc]

private theorem length_bound {n : ℕ} {l : List Square} (hl : pathOn (box 0 n 0 n) l) :
    l.length ≤ n * n := by
  have hsub : l.toFinset ⊆ cells n := fun p hp => mem_cells.mpr (hl.2.2 p (List.mem_toFinset.mp hp))
  simpa [cells, card_product, Int.card_Ico, List.toFinset_card_of_nodup hl.1] using card_le_card hsub

private theorem maximum_of_route {n k : ℕ} {u v : Square} (h : Route (box 0 n 0 n) u v k)
    (bound : ∀ l, pathOn (box 0 n 0 n) l → l.length ≤ k) : a n = k - 1 := by
  apply IsGreatest.csSup_eq
  obtain ⟨l, hl, _, _, hk⟩ := h
  refine ⟨⟨l, hl, by rw [hk]⟩, ?_⟩
  rintro j ⟨r, hr, rfl⟩
  exact Nat.sub_le_sub_right (bound r hr) 1

private theorem largeValue (strips : StripBases) (squares : SquareBases) {n : ℕ} (hn : 8 ≤ n) :
    a n = n ^ 2 - 1 := by
  obtain ⟨u, h⟩ := allSquares strips squares n hn
  simpa [pow_two] using maximum_of_route h (fun _ hl => length_bound hl)

private theorem oneLabel {f : Square → ℕ} (u : Square) (l : List Square)
    (h : (u :: l).IsChain fun p q => f p = f q) : ∀ p ∈ u :: l, f p = f u := by
  induction l generalizing u with
  | nil => simp
  | cons b t ih =>
    obtain ⟨he, ht⟩ := List.isChain_cons_cons.mp h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hr
    · rfl
    · exact (ih b ht p hr).trans he.symm

/-- A path stays in one component. A finite label certificate only needs
to check that edges preserve their label and each label class is small. -/
private def ComponentBound (n k : ℕ) (f : Square → ℕ) : Prop :=
  (∀ p ∈ cells n, ∀ q ∈ cells n, jump p q → f p = f q) ∧
  ∀ p ∈ cells n, ((cells n).filter fun q => f q = f p).card ≤ k

private instance (n k : ℕ) (f : Square → ℕ) : Decidable (ComponentBound n k f) := by
  unfold ComponentBound
  infer_instance

private theorem bound_from_labels {n k : ℕ} {f : Square → ℕ} (cert : ComponentBound n k f)
    (l : List Square) (h : pathOn (box 0 n 0 n) l) : l.length ≤ k := by
  cases l with
  | nil => simp
  | cons u t =>
    have hmem : ∀ p ∈ u :: t, p ∈ cells n := fun p hp => mem_cells.mpr (h.2.2 p hp)
    have chain : (u :: t).IsChain fun p q => f p = f q :=
      h.2.1.imp_of_mem_imp fun p q hp hq => cert.1 p (hmem p hp) q (hmem q hq)
    have sub : (u :: t).toFinset ⊆ (cells n).filter fun q => f q = f u := by
      intro p hp
      have hm := List.mem_toFinset.mp hp
      exact mem_filter.mpr ⟨hmem p hm, oneLabel u t chain p hm⟩
    rw [← List.toFinset_card_of_nodup h.1]
    exact (card_le_card sub).trans (cert.2 u (hmem u (List.mem_cons_self ..)))

private def smallVertices : ℕ → ℕ
  | 5 => 3
  | 6 => 20
  | 7 => 48
  | _ => 1

private abbrev SmallRoutes := ∀ n : ℕ, 1 ≤ n → n ≤ 7 →
  ∃ u v, Route (box 0 n 0 n) u v (smallVertices n)
private abbrev SmallBounds := ∀ n : ℕ, 1 ≤ n → n ≤ 7 →
  ∃ f, ComponentBound n (smallVertices n) f

private theorem smallValue (paths : SmallRoutes) (bounds : SmallBounds) {n : ℕ}
    (hn : 1 ≤ n) (hs : n ≤ 7) : a n = smallVertices n - 1 := by
  obtain ⟨u,v,h⟩ := paths n hn hs
  obtain ⟨f,cert⟩ := bounds n hn hs
  exact maximum_of_route h (bound_from_labels cert)

private def model (j : ℤ) : ℤ :=
  if j ≤ 4 then 0 else if j = 5 then 2 else if j = 6 then 19 else if j = 7 then 47 else j ^ 2 - 1

private theorem model_large {j : ℤ} (h : 7 < j) : model j = j ^ 2 - 1 := by
  simp [model, show ¬ j ≤ 4 by omega, show j ≠ 5 by omega, show j ≠ 6 by omega,
    show j ≠ 7 by omega]

private theorem fromCertificates (strips : StripBases) (squares : SquareBases)
    (paths : SmallRoutes) (bounds : SmallBounds) : type_of% @OMA.S_oeis_a307554.main := by
  refine ⟨fun n hn => largeValue strips squares hn, ?_⟩
  have values (n : ℕ) (hn : 0 < n) : (a n : ℤ) = model n := by
    by_cases hs : n ≤ 7
    · rw [smallValue paths bounds hn hs]
      interval_cases n <;> decide
    · rw [largeValue strips squares (by omega), model_large (by omega),
        Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow]
      rfl
  have coefficients (j : ℤ) : coeff j = model j := by
    by_cases h : 0 < j
    · rw [coeff, if_pos h, values j.toNat (by omega), Int.toNat_of_nonneg (by omega)]
    · simp [coeff, h, model, show j ≤ 4 by omega]
  intro n
  simp only [coefficients]
  by_cases hs : n ≤ 10
  · interval_cases n <;> decide
  · have hnum : numerator n = 0 := by
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 11 := ⟨n - 11, by omega⟩
      rfl
    rw [model_large (by omega), model_large (by omega), model_large (by omega),
      model_large (by omega), hnum]
    ring

/-- Witnesses are encoded as x+16y, with both coordinates between 0 and 15. -/
private def unpack (v : ℕ) : Square := (v % 16, v / 16)

private def Certified (w h : ℕ) (u v : Square) (k : ℕ) (data : List ℕ) : Prop :=
  let l := data.map unpack
  pathOn (box 0 w 0 h) l ∧ l.head? = some u ∧ l.getLast? = some v ∧ l.length = k

private instance (w h : ℕ) (u v : Square) (k : ℕ) (s : List ℕ) :
    Decidable (Certified w h u v k s) := by
  unfold Certified pathOn
  dsimp only
  infer_instance

private theorem readPath {w h k : ℕ} {u v : Square} (s : List ℕ) (ok : Certified w h u v k s) :
    Route (box 0 w 0 h) u v k := ⟨s.map unpack, ok⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA8 : stripA 8 := by
  apply readPath
    [34, 101, 49, 5, 0, 67, 23, 18, 85, 80, 36, 97, 17, 69, 113, 33, 38, 99, 32, 84, 4, 65,
    70, 114, 53, 48, 100, 20, 81, 1, 6, 86, 19, 71, 115, 35, 96, 52, 119, 39, 83, 3, 64, 116,
    55, 50, 102, 22, 66, 118, 51, 103, 98, 54, 2, 7, 87, 82, 21, 16, 68, 112, 117, 37]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedB8 : stripB 8 := by
  apply readPath
    [34, 86, 19, 71, 66, 22, 83, 39, 119, 52, 113, 118, 38, 99, 32, 37, 98, 54, 115, 48, 100,
    33, 85, 18, 23, 67, 6, 50, 117, 112, 68, 16, 96, 101, 21, 65, 4, 84, 17, 97, 102, 35, 87,
    7, 51, 103, 36, 80, 0, 5, 49, 116, 55, 3, 70, 114, 53, 1, 81, 20, 64, 69, 2, 82]
  decide

private theorem seedS8 : anchored 8 := ⟨(2, 2), seedA8⟩

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA9 : stripA 9 := by
  apply readPath
    [34, 39, 119, 114, 70, 18, 85, 5, 72, 20, 81, 1, 53, 48, 115, 120, 40, 84, 4, 71, 66, 22,
    83, 3, 55, 99, 19, 24, 104, 37, 32, 112, 51, 7, 68, 16, 21, 65, 117, 56, 100, 33, 38,
    118, 113, 52, 8, 88, 36, 80, 0, 67, 23, 103, 98, 54, 2, 82, 87, 35, 96, 101, 49, 116, 64,
    69, 17, 97, 102, 50, 6, 86]
  decide

private theorem seedB9 : stripB 9 := seedA9

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS9 : anchored 9 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 101, 96, 16, 83, 135, 130, 50, 102, 35, 40, 84, 32, 99, 104, 52, 8, 88, 36, 80, 132,
    71, 4, 65, 21, 82, 134, 129, 49, 116, 55, 3, 64, 69, 2, 7, 87, 20, 72, 133, 128, 48, 100,
    39, 119, 114, 70, 131, 136, 56, 51, 112, 117, 37, 81, 1, 53, 97, 17, 22, 66, 5, 0, 67, 6,
    86, 19, 24, 68, 120, 115, 54, 98, 103, 23, 18, 85, 33, 113, 118, 38]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA10 : stripA 10 := by
  apply readPath
    [34, 114, 119, 67, 0, 5, 72, 20, 64, 116, 49, 54, 98, 37, 89, 9, 70, 18, 23, 103, 36, 97,
    17, 22, 102, 41, 121, 69, 2, 7, 68, 16, 96, 101, 57, 52, 104, 24, 19, 80, 85, 33, 113,
    118, 66, 71, 115, 120, 40, 35, 87, 82, 21, 73, 6, 50, 117, 65, 4, 84, 32, 112, 51, 56,
    100, 48, 53, 1, 81, 86, 25, 105, 38, 99, 55, 3, 8, 88, 83, 39]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedB10 : stripB 10 := by
  apply readPath
    [34, 114, 119, 39, 100, 105, 25, 86, 19, 71, 66, 118, 113, 33, 38, 82, 2, 7, 87, 20, 72,
    67, 0, 80, 36, 103, 23, 18, 85, 41, 121, 54, 98, 37, 81, 1, 6, 50, 55, 116, 49, 5, 57,
    52, 8, 69, 64, 3, 70, 65, 117, 73, 68, 24, 104, 99, 32, 112, 51, 56, 4, 48, 115, 120, 53,
    9, 89, 22, 17, 97, 102, 35, 96, 16, 83, 88, 21, 101, 40, 84]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS10 : anchored 10 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 86, 153, 148, 87, 131, 136, 56, 4, 9, 89, 22, 17, 69, 113, 33, 38, 82, 134, 73, 117,
    37, 104, 24, 19, 71, 115, 48, 128, 84, 23, 18, 70, 137, 132, 88, 149, 97, 36, 116, 64,
    144, 83, 150, 98, 103, 147, 80, 0, 67, 6, 1, 81, 133, 72, 20, 25, 105, 53, 114, 119, 52,
    8, 3, 55, 135, 130, 50, 102, 41, 121, 54, 2, 7, 51, 112, 32, 99, 151, 146, 66, 118, 57,
    101, 145, 65, 21, 16, 96, 35, 40, 120, 68, 129, 49, 5, 85, 152, 100, 39]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA11 : stripA 11 := by
  apply readPath
    [34, 114, 53, 58, 119, 39, 106, 26, 87, 82, 2, 54, 121, 41, 36, 97, 102, 50, 117, 122,
    70, 9, 89, 84, 17, 69, 8, 52, 96, 35, 40, 120, 115, 48, 4, 65, 21, 73, 6, 1, 81, 86, 42,
    103, 98, 37, 104, 24, 19, 80, 0, 5, 72, 67, 23, 18, 85, 33, 113, 118, 57, 101, 49, 116,
    55, 3, 64, 20, 25, 105, 100, 56, 51, 112, 32, 99, 38, 90, 10, 71, 66, 22, 74, 7, 68, 16,
    83, 88]
  decide

private theorem seedB11 : stripB 11 := seedA11

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS11 : anchored 11 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 114, 166, 122, 42, 37, 89, 169, 164, 84, 151, 146, 66, 5, 49, 129, 134, 82, 21, 16,
    96, 163, 168, 116, 160, 80, 19, 24, 104, 165, 113, 52, 0, 67, 23, 18, 85, 33, 38, 105,
    53, 48, 128, 133, 72, 152, 147, 103, 98, 150, 145, 101, 162, 167, 100, 144, 149, 154, 87,
    26, 106, 39, 119, 58, 138, 71, 10, 90, 170, 118, 57, 137, 132, 65, 70, 9, 4, 56, 136,
    131, 51, 7, 2, 54, 121, 41, 36, 88, 8, 69, 130, 50, 55, 99, 32, 112, 68, 148, 153, 73,
    117, 161, 81, 1, 6, 86, 25, 20, 64, 3, 83, 135, 74, 22, 17, 97, 102, 35, 115, 120, 40]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA12 : stripA 12 := by
  apply readPath
    [34, 114, 70, 65, 4, 9, 53, 58, 119, 75, 8, 69, 64, 116, 72, 11, 91, 24, 19, 99, 38, 105,
    100, 48, 115, 120, 68, 73, 6, 1, 81, 20, 25, 86, 42, 122, 117, 50, 102, 22, 74, 7, 59,
    103, 98, 18, 23, 67, 0, 80, 36, 97, 17, 84, 89, 37, 32, 112, 51, 56, 123, 43, 104, 52,
    113, 33, 85, 90, 10, 5, 49, 101, 57, 118, 66, 71, 27, 88, 21, 16, 96, 35, 40, 107, 55, 3,
    83, 39, 106, 26, 87, 82, 2, 54, 121, 41]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedB12 : stripB 12 := by
  apply readPath
    [34, 114, 53, 105, 25, 69, 74, 118, 57, 101, 96, 16, 83, 22, 89, 9, 4, 84, 17, 97, 36,
    41, 121, 54, 49, 116, 72, 5, 66, 71, 10, 90, 38, 43, 123, 56, 117, 65, 21, 73, 68, 120,
    59, 7, 2, 82, 87, 26, 106, 39, 119, 58, 102, 50, 55, 11, 91, 24, 19, 99, 32, 112, 51,
    103, 98, 37, 104, 52, 113, 33, 100, 48, 115, 35, 40, 107, 27, 88, 8, 3, 64, 20, 81, 1, 6,
    67, 0, 80, 85, 18, 23, 75, 70, 122, 42, 86]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS12 : anchored 12 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 39, 106, 26, 87, 139, 134, 186, 181, 137, 57, 5, 0, 80, 147, 103, 36, 88, 27, 107,
    151, 71, 138, 58, 119, 171, 166, 161, 81, 37, 42, 122, 70, 114, 53, 9, 89, 22, 17, 97,
    149, 154, 74, 118, 51, 7, 2, 69, 113, 52, 8, 75, 155, 150, 145, 65, 4, 48, 128, 67, 23,
    18, 98, 178, 183, 131, 136, 180, 185, 105, 25, 20, 72, 152, 100, 167, 162, 82, 38, 33,
    85, 24, 19, 99, 55, 3, 64, 144, 83, 16, 21, 73, 153, 148, 96, 163, 168, 101, 49, 129, 68,
    1, 6, 11, 91, 86, 130, 50, 117, 56, 123, 43, 104, 184, 132, 176, 115, 35, 40, 120, 59,
    54, 10, 90, 170, 165, 160, 116, 177, 133, 66, 146, 102, 169, 164, 84, 32, 112, 179, 135,
    187, 182, 121, 41]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA13 : stripA 13 := by
  apply readPath
    [34, 114, 53, 105, 25, 92, 40, 107, 27, 88, 36, 97, 17, 22, 83, 16, 96, 52, 57, 124, 44,
    39, 91, 86, 6, 1, 81, 37, 89, 84, 32, 112, 51, 56, 12, 73, 68, 24, 76, 9, 70, 3, 64, 20,
    87, 35, 115, 120, 59, 7, 74, 118, 66, 71, 123, 43, 38, 82, 21, 26, 106, 101, 49, 116,
    121, 41, 108, 28, 72, 11, 55, 122, 42, 103, 98, 18, 85, 5, 10, 54, 2, 69, 113, 33, 100,
    48, 4, 65, 117, 50, 102, 58, 119, 75, 8, 60, 104, 99, 19, 80, 0, 67, 23, 90]
  decide

private theorem seedB13 : stripB 13 := seedA13

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS13 : anchored 13 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 114, 70, 26, 87, 43, 38, 33, 113, 69, 2, 82, 21, 16, 83, 144, 64, 3, 8, 75, 23, 18,
    98, 178, 134, 186, 106, 54, 49, 129, 68, 148, 200, 195, 115, 176, 181, 137, 76, 9, 53,
    48, 4, 65, 132, 193, 149, 154, 198, 203, 123, 167, 162, 101, 153, 73, 12, 92, 172, 105,
    185, 124, 204, 199, 155, 103, 108, 28, 89, 156, 151, 146, 66, 71, 10, 90, 170, 165, 160,
    80, 147, 86, 25, 20, 81, 1, 6, 58, 138, 182, 187, 107, 27, 22, 17, 84, 145, 150, 194,
    133, 177, 97, 36, 88, 44, 39, 100, 161, 166, 171, 119, 163, 168, 116, 72, 139, 183, 188,
    136, 180, 128, 67, 0, 5, 57, 52, 96, 35, 40, 120, 59, 7, 74, 118, 179, 135, 130, 50, 102,
    169, 164, 112, 32, 99, 19, 24, 85, 41, 121, 201, 196, 152, 91, 11, 55, 122, 202, 197,
    192, 131, 51, 56, 117, 184, 140, 60, 104, 37, 42]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA14 : stripA 14 := by
  apply readPath
    [34, 114, 119, 75, 23, 18, 85, 41, 36, 80, 19, 99, 32, 112, 51, 103, 98, 37, 42, 109, 29,
    73, 68, 16, 96, 52, 113, 33, 38, 90, 10, 54, 49, 5, 0, 67, 72, 77, 121, 116, 64, 20, 81,
    1, 53, 97, 102, 50, 117, 65, 70, 122, 61, 105, 25, 86, 91, 11, 6, 58, 125, 45, 106, 26,
    93, 13, 8, 60, 104, 24, 76, 120, 59, 7, 2, 82, 87, 92, 12, 56, 108, 28, 89, 9, 4, 48,
    100, 39, 44, 124, 57, 101, 21, 88, 83, 3, 55, 107, 27, 22, 66, 118, 74, 69, 17, 84, 40,
    35, 115, 71, 123, 43]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedB14 : stripB 14 := by
  apply readPath
    [34, 114, 70, 75, 23, 18, 85, 80, 19, 24, 76, 9, 61, 122, 117, 73, 68, 112, 51, 56, 123,
    43, 104, 60, 8, 52, 0, 67, 119, 124, 72, 11, 91, 39, 44, 105, 38, 82, 2, 54, 121, 116,
    49, 5, 66, 118, 113, 33, 100, 48, 4, 65, 21, 16, 96, 35, 115, 71, 27, 107, 40, 45, 89,
    28, 108, 103, 98, 37, 81, 1, 53, 58, 125, 120, 59, 7, 12, 92, 87, 20, 25, 77, 10, 90, 29,
    109, 42, 86, 6, 50, 102, 97, 36, 41, 93, 26, 106, 101, 57, 13, 74, 69, 64, 3, 55, 99, 32,
    84, 17, 22, 83, 88]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS14 : anchored 14 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 114, 181, 129, 68, 112, 51, 118, 170, 109, 189, 184, 179, 99, 32, 37, 42, 122, 183,
    178, 98, 18, 85, 41, 102, 146, 66, 22, 74, 154, 198, 193, 113, 180, 185, 141, 61, 9, 70,
    131, 192, 197, 202, 135, 196, 152, 72, 28, 23, 84, 17, 97, 36, 80, 0, 5, 49, 54, 2, 7,
    12, 56, 108, 188, 121, 165, 209, 214, 162, 82, 134, 139, 219, 167, 123, 203, 151, 195,
    128, 67, 147, 199, 194, 150, 211, 144, 64, 3, 55, 11, 6, 1, 53, 58, 138, 182, 177, 133,
    89, 45, 40, 101, 145, 212, 160, 116, 168, 220, 140, 201, 157, 218, 213, 208, 164, 169,
    221, 216, 172, 92, 136, 69, 149, 210, 130, 50, 117, 65, 4, 48, 100, 33, 38, 105, 166,
    161, 81, 20, 25, 77, 10, 90, 29, 24, 19, 86, 153, 73, 21, 16, 83, 163, 215, 171, 91, 39,
    44, 88, 27, 107, 187, 120, 59, 103, 155, 75, 119, 124, 204, 137, 93, 173, 217, 156, 76,
    71, 132, 176, 115, 35, 87, 26, 106, 186, 125, 205, 200, 148, 96, 52, 57, 13, 8, 60, 104,
    43]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedA15 : stripA 15 := by
  apply readPath
    [34, 39, 91, 11, 78, 26, 106, 101, 40, 45, 89, 28, 23, 18, 98, 54, 2, 82, 38, 90, 85, 33,
    100, 48, 53, 97, 36, 116, 49, 5, 72, 20, 64, 3, 83, 16, 21, 88, 8, 60, 104, 24, 29, 109,
    42, 86, 6, 67, 0, 80, 19, 99, 55, 107, 27, 94, 14, 75, 119, 114, 70, 122, 61, 9, 76, 120,
    59, 103, 108, 56, 51, 112, 32, 37, 81, 1, 68, 73, 125, 58, 102, 50, 117, 65, 4, 84, 17,
    22, 66, 71, 115, 35, 96, 52, 113, 69, 121, 126, 46, 41, 93, 13, 57, 124, 44, 105, 25, 77,
    10, 62, 123, 118, 74, 30, 110, 43, 87, 7, 12, 92]
  decide

private theorem seedB15 : stripB 15 := seedA15

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedS15 : anchored 15 := by
  refine ⟨(2, 2), ?_⟩
  apply readPath
    [34, 39, 83, 22, 17, 84, 145, 225, 181, 176, 228, 161, 166, 233, 172, 105, 53, 114, 194,
    199, 132, 212, 151, 146, 213, 208, 128, 195, 200, 156, 104, 52, 119, 75, 23, 67, 0, 80,
    147, 227, 160, 165, 226, 231, 236, 184, 140, 220, 168, 101, 57, 5, 49, 129, 209, 148,
    192, 112, 32, 37, 42, 94, 14, 58, 6, 11, 55, 60, 8, 3, 64, 131, 51, 7, 12, 92, 136, 203,
    198, 193, 113, 33, 85, 18, 70, 65, 4, 48, 115, 120, 40, 35, 96, 16, 68, 1, 81, 86, 19,
    71, 10, 62, 123, 56, 117, 197, 202, 135, 179, 99, 38, 43, 87, 26, 78, 158, 91, 30, 25,
    20, 100, 152, 196, 116, 72, 28, 89, 45, 125, 73, 21, 82, 134, 214, 162, 229, 185, 237,
    232, 180, 224, 163, 215, 210, 149, 144, 211, 216, 164, 97, 177, 133, 66, 118, 170, 103,
    155, 235, 174, 218, 157, 77, 121, 201, 206, 154, 221, 141, 74, 13, 93, 41, 36, 88, 27,
    107, 187, 182, 102, 50, 130, 69, 2, 54, 59, 126, 46, 90, 142, 222, 217, 150, 98, 178,
    230, 169, 108, 188, 183, 139, 219, 167, 234, 173, 106, 186, 238, 171, 110, 190, 138, 205,
    153, 109, 29, 24, 76, 9, 61, 122, 189, 137, 204, 124, 44]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL1 : ∃ u v, Route (box 0 1 0 1) u v (smallVertices 1) := by
  refine ⟨(0, 0), (0, 0), ?_⟩
  apply readPath
    [0]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL2 : ∃ u v, Route (box 0 2 0 2) u v (smallVertices 2) := by
  refine ⟨(0, 1), (0, 1), ?_⟩
  apply readPath
    [16]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL3 : ∃ u v, Route (box 0 3 0 3) u v (smallVertices 3) := by
  refine ⟨(0, 1), (0, 1), ?_⟩
  apply readPath
    [16]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL4 : ∃ u v, Route (box 0 4 0 4) u v (smallVertices 4) := by
  refine ⟨(0, 1), (0, 1), ?_⟩
  apply readPath
    [16]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL5 : ∃ u v, Route (box 0 5 0 5) u v (smallVertices 5) := by
  refine ⟨(0, 1), (1, 0), ?_⟩
  apply readPath
    [16, 68, 1]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL6 : ∃ u v, Route (box 0 6 0 6) u v (smallVertices 6) := by
  refine ⟨(4, 1), (5, 3), ?_⟩
  apply readPath
    [20, 64, 3, 83, 16, 68, 1, 81, 37, 32, 84, 17, 69, 2, 82, 21, 65, 4, 48, 53]
  decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem seedL7 : ∃ u v, Route (box 0 7 0 7) u v (smallVertices 7) := by
  refine ⟨(2, 3), (3, 1), ?_⟩
  apply readPath
    [50, 6, 67, 0, 52, 96, 35, 102, 97, 36, 80, 85, 33, 100, 48, 53, 1, 68, 16, 21, 65, 4,
    84, 17, 69, 64, 20, 81, 37, 32, 99, 38, 82, 2, 54, 98, 18, 70, 3, 83, 22, 66, 5, 49, 101,
    34, 86, 19]
  decide

private theorem stripBases : StripBases := by
  intro w h₁ h₂
  interval_cases w
  · exact ⟨seedA8, seedB8⟩
  · exact ⟨seedA9, seedB9⟩
  · exact ⟨seedA10, seedB10⟩
  · exact ⟨seedA11, seedB11⟩
  · exact ⟨seedA12, seedB12⟩
  · exact ⟨seedA13, seedB13⟩
  · exact ⟨seedA14, seedB14⟩
  · exact ⟨seedA15, seedB15⟩

private theorem squareBases : SquareBases := by
  intro w h₁ h₂
  interval_cases w
  · exact seedS8
  · exact seedS9
  · exact seedS10
  · exact seedS11
  · exact seedS12
  · exact seedS13
  · exact seedS14
  · exact seedS15

private theorem smallRoutes : SmallRoutes := by
  intro n h₁ h₂
  interval_cases n
  · exact seedL1
  · exact seedL2
  · exact seedL3
  · exact seedL4
  · exact seedL5
  · exact seedL6
  · exact seedL7

/-- The tables give the connected component of each square in row-major order. -/
private def index (n : ℕ) (p : Square) : ℕ := p.1.toNat + n * p.2.toNat

private def label5 (p : Square) : ℕ :=
  ([0, 1, 8, 4, 3, 1, 5, 9, 13, 4, 2, 6, 10, 14, 16, 3, 7, 11, 15, 0, 4, 3, 12, 0, 1] : List ℕ).getD (index 5 p) 0

private def label6 (p : Square) : ℕ :=
  ([0, 1, 1, 1, 1, 0, 1, 1, 0, 0, 1, 1, 1, 0, 2, 4, 0, 1, 1, 0, 3, 5, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0] : List ℕ).getD (index 6 p) 0

private def label7 (p : Square) : ℕ := if p = (3,3) then 1 else 0

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound1 : ComponentBound 1 (smallVertices 1) (index 1) := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound2 : ComponentBound 2 (smallVertices 2) (index 2) := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound3 : ComponentBound 3 (smallVertices 3) (index 3) := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound4 : ComponentBound 4 (smallVertices 4) (index 4) := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound5 : ComponentBound 5 (smallVertices 5) label5 := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound6 : ComponentBound 6 (smallVertices 6) label6 := by decide

set_option maxRecDepth 50000 in
set_option maxHeartbeats 600000 in
private theorem bound7 : ComponentBound 7 (smallVertices 7) label7 := by decide

private theorem smallBounds : SmallBounds := by
  intro n h₁ h₂
  interval_cases n
  · exact ⟨_, bound1⟩
  · exact ⟨_, bound2⟩
  · exact ⟨_, bound3⟩
  · exact ⟨_, bound4⟩
  · exact ⟨_, bound5⟩
  · exact ⟨_, bound6⟩
  · exact ⟨_, bound7⟩

end OMA.Fiveleaper

open OMA.Fiveleaper

theorem OMA.solution : type_of% @OMA.S_oeis_a307554.main := by
  exact fromCertificates stripBases squareBases smallRoutes smallBounds

