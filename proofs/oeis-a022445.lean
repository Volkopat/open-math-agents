import OMAStatements.S_oeis_a022445
import Mathlib

/-!
# Self-avoiding closed walks based at the edge of a three-line strip

Credit: @jacklarmer

This proof uses the layer encoding and root marking proposed in project desk note #162978.
At each horizontal cut through a cycle, exactly two of the three vertical edges are used.
From bottom to top, these pairs form a word over three letters. Degree two determines the
horizontal edges, and the boundary walk of every admissible word reconstructs a cycle.
A marked vertex on the left boundary fixes its vertical translation. The two orientations
then account for every positive rooted walk. The empty walk contributes the constant term.

The word recurrences count shapes by semiperimeter and count their possible root heights.
Eliminating the four resulting power series gives the claimed generating function.
-/

namespace StripWords

inductive Layer where
  | L | R | B
  deriving DecidableEq

open Layer

def compatible : Layer → Layer → Prop
  | L, R | R, L => False
  | _, _ => True

def valid : List Layer → Prop
  | [] => False
  | [_] => True
  | x :: y :: t => compatible x y ∧ valid (y :: t)

def firstCost : Layer → ℕ
  | L | R => 2
  | B => 3

/-- The first argument is the newly added top layer. -/
def stepCost : Layer → Layer → ℕ
  | B, L | B, R => 2
  | _, _ => 1

def cost : List Layer → ℕ
  | [] => 0
  | [x] => firstCost x
  | x :: y :: t => cost (y :: t) + stepCost x y

def firstMarks : Layer → ℕ
  | L | B => 2
  | R => 0

/-- Number of new vertices on the left line when adding the first argument. -/
def stepMarks : Layer → Layer → ℕ
  | R, _ => 0
  | L, R | B, R => 2
  | _, _ => 1

def marks : List Layer → ℕ
  | [] => 0
  | [x] => firstMarks x
  | x :: y :: t => marks (y :: t) + stepMarks x y

/-- All words of cost n ending at the top in s, with the top layer at the head. -/
def words (s : Layer) : ℕ → List (List Layer)
  | 0 | 1 => []
  | n+2 => match s with
    | L => (if n = 0 then [[L]] else []) ++
        ((words L (n+1) ++ words B (n+1)).map (L :: ·))
    | R => (if n = 0 then [[R]] else []) ++
        ((words R (n+1) ++ words B (n+1)).map (R :: ·))
    | B => (if n = 1 then [[B]] else []) ++
        ((words L n ++ words R n ++ words B (n+1)).map (B :: ·))
termination_by n => n

def C (n : ℕ) := (words L n).length
def BCount (n : ℕ) := (words B n).length
def weight (s : Layer) (n : ℕ) := ((words s n).map marks).sum
def W (n : ℕ) := weight L n + weight R n
def Z (n : ℕ) := weight B n

end StripWords

namespace StripWords

open Layer

private theorem min_cost : ∀ (x : Layer) (t : List Layer), 2 ≤ cost (x :: t)
  | x, [] => by cases x <;> decide
  | x, y :: t => Nat.le_trans (min_cost y t) (Nat.le_add_right _ _)

theorem mem_words (s : Layer) (n : ℕ) (l : List Layer) :
    l ∈ words s n ↔ valid l ∧ l.head? = some s ∧ cost l = n := by
  induction n using Nat.strongRecOn generalizing s l with
  | ind n ih =>
    cases n with
    | zero =>
      rw [words]
      cases l with
      | nil => simp [valid]
      | cons x t => have h := min_cost x t; simp; omega
    | succ n =>
      cases n with
      | zero =>
        rw [words]
        cases l with
        | nil => simp [valid]
        | cons x t => have h := min_cost x t; simp; omega
      | succ k =>
        have ih₀ := ih k (by omega)
        have ih₁ := ih (k+1) (by omega)
        cases s <;> rw [words] <;> cases l with
        | nil => simp [List.mem_map, valid]
        | cons x t =>
          cases t with
          | nil =>
            cases x <;>
              simp [List.mem_map, ih₀, ih₁, valid, cost, firstCost]
          | cons y t =>
            cases x <;> cases y <;>
              simp [List.mem_map, ih₀, ih₁, valid, cost, compatible, stepCost, and_comm]

private theorem words_disjoint {s t : Layer} (hst : s ≠ t) (n m : ℕ) :
    (words s n).Disjoint (words t m) := by
  intro l hs ht
  exact hst (Option.some.inj ((mem_words _ _ _).1 hs |>.2.1.symm.trans
    ((mem_words _ _ _).1 ht).2.1))

private theorem no_empty_word (s : Layer) (n : ℕ) : [] ∉ words s n := by
  simp [mem_words, valid]

private theorem combine_nodup (s : Layer) (p : Prop) [Decidable p] (v : List (List Layer))
    (hv : v.Nodup) (h₀ : [] ∉ v) :
    ((if p then [[s]] else []) ++ v.map (s :: ·)).Nodup := by
  have hm := hv.map (f := (s :: ·)) (fun _ _ h => (List.cons.inj h).2)
  split <;> simp_all

theorem words_nodup (s : Layer) (n : ℕ) : (words s n).Nodup := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    cases n with
    | zero => rw [words]; simp
    | succ n =>
      cases n with
      | zero => rw [words]; simp
      | succ k =>
        have ih₀ := ih k (by omega)
        have ih₁ := ih (k+1) (by omega)
        cases s <;> rw [words] <;> apply combine_nodup
        · exact (ih₁ L).append (ih₁ B) (words_disjoint (by decide) _ _)
        · simp [no_empty_word]
        · exact (ih₁ R).append (ih₁ B) (words_disjoint (by decide) _ _)
        · simp [no_empty_word]
        · apply ((ih₀ L).append (ih₀ R) (words_disjoint (by decide) _ _)).append (ih₁ B)
          intro l hl hb
          rcases List.mem_append.mp hl with hL | hR
          · exact words_disjoint (s := L) (t := B) (by decide) _ _ hL hb
          · exact words_disjoint (s := R) (t := B) (by decide) _ _ hR hb
        · simp [no_empty_word]

end StripWords

namespace StripWords

open Layer

/-- Every word in an endpoint class has the indicated top row. -/
theorem words_top {s : Layer} {n : ℕ} {v : List Layer} (hv : v ∈ words s n) :
    ∃ t, v = s :: t := by
  cases n with
  | zero => simp [words] at hv
  | succ n =>
    cases n with
    | zero => simp [words] at hv
    | succ n =>
      cases s <;> rw [words] at hv <;> split at hv <;>
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_map, false_or] at hv <;> grind

private theorem sum_map_incr (l : List (List Layer)) (k : ℕ) :
    (l.map (fun v => marks v + k)).sum = (l.map marks).sum + l.length * k := by
  induction l with
  | nil => simp
  | cons v t ih => simp [ih, Nat.add_mul]; omega

private theorem sum_add_row (s t : Layer) (n : ℕ) :
    (((words t n).map (s :: ·)).map marks).sum =
      weight t n + (words t n).length * stepMarks s t := by
  rw [List.map_map]
  have hh : (words t n).map (marks ∘ (s :: ·)) =
      (words t n).map (fun v => marks v + stepMarks s t) := by
    apply List.map_congr_left
    intro v hv
    obtain ⟨tl, rfl⟩ := words_top hv
    rfl
  rw [hh, sum_map_incr]
  rfl

theorem length_right (n : ℕ) : (words R n).length = C n := by
  unfold C
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => simp only [words]
    | succ k =>
      cases k with
      | zero =>
        change (words R 1).length = (words L 1).length
        simp only [words]
      | succ k =>
        change (words R (k+2)).length = (words L (k+2)).length
        conv_lhs => rw [words]
        conv_rhs => rw [words]
        simp only [List.length_append, List.length_map, ih (k+1) (by omega)]
        split <;> rfl

theorem base_zero : (C 0, BCount 0, W 0, Z 0) = (0,0,0,0) := by
  simp [C, BCount, W, Z, weight, words]

theorem base_one : (C 1, BCount 1, W 1, Z 1) = (0,0,0,0) := by
  simp [C, BCount, W, Z, weight, words]

theorem base_two : (C 2, BCount 2, W 2, Z 2) = (1,0,2,0) := by
  simp [C, BCount, W, Z, weight, words, marks, firstMarks]

theorem words_rec (n : ℕ) :
    (C (n+3), BCount (n+3), W (n+3), Z (n+3)) =
    (C (n+2) + BCount (n+2),
     (if n = 0 then 1 else 0) + 2*C (n+1) + BCount (n+2),
     W (n+2) + 2*Z (n+2) + C (n+2) + BCount (n+2),
     (if n = 0 then 2 else 0) + W (n+1) + 3*C (n+1) + Z (n+2) + BCount (n+2)) := by
  have l : words L (n+3) = (words L (n+2)).map (L :: ·) ++
      (words B (n+2)).map (L :: ·) := by
    rw [words]; simp [List.map_append]
  have r : words R (n+3) = (words R (n+2)).map (R :: ·) ++
      (words B (n+2)).map (R :: ·) := by
    rw [words]; simp [List.map_append]
  have b : words B (n+3) = (if n = 0 then [[B]] else []) ++
      ((words L (n+1)).map (B :: ·) ++ (words R (n+1)).map (B :: ·) ++
        (words B (n+2)).map (B :: ·)) := by
    rw [words]; simp only [List.map_append, Nat.add_eq_right]
  simp only [Prod.mk.injEq, C, BCount, W, Z, weight] at *
  simp only [l, r, b, List.map_append, List.length_append, List.length_map, List.sum_append,
    sum_add_row, stepMarks, Nat.mul_zero, Nat.mul_one, Nat.add_zero]
  have h1 := length_right (n+1)
  have h2 := length_right (n+2)
  unfold C at h1 h2
  unfold weight
  split <;> simp [marks, firstMarks] <;> omega

end StripWords

namespace StripTransfer

/-- Heights on the left boundary of a word of layers, with the bottom at height
zero and the top layer at the head of the list. -/
def leftLevels {α : Type*} (touches : α → Bool) : List α → Finset ℕ
  | [] => ∅
  | t :: w =>
    if touches t then insert (w.length + 1) (insert w.length (leftLevels touches w))
    else leftLevels touches w

theorem level_le_length {α : Type*} (touches : α → Bool) {w : List α} {j : ℕ}
    (hj : j ∈ leftLevels touches w) : j ≤ w.length := by
  induction w with
  | nil => simp [leftLevels] at hj
  | cons t w ih =>
    simp only [List.length_cons]
    by_cases ht : touches t
    · simp only [leftLevels, ht, ↓reduceIte, Finset.mem_insert] at hj
      rcases hj with rfl | rfl | hj
      · rfl
      · omega
      · exact (ih hj).trans (by omega)
    · simp [leftLevels, ht] at hj
      exact (ih hj).trans (by omega)

theorem top_mem_levels_iff {α : Type*} (touches : α → Bool) (w : List α) :
    w.length ∈ leftLevels touches w ↔ (w.head?.map touches) = some true := by
  cases w with
  | nil => simp [leftLevels]
  | cons t w =>
    have h : w.length + 1 ∉ leftLevels touches w := fun hj => by
      have := level_le_length touches hj
      omega
    cases ht : touches t <;> simp [leftLevels, ht, h]

theorem card_leftLevels_cons {α : Type*} (touches : α → Bool) (t : α) (w : List α) :
    (leftLevels touches (t :: w)).card = (leftLevels touches w).card +
      if touches t then (if w.head?.map touches = some true then 1 else 2) else 0 := by
  have h : w.length + 1 ∉ leftLevels touches w := fun hj => by
    have := level_le_length touches hj
    omega
  have hi : w.length + 1 ∉ insert w.length (leftLevels touches w) := by simp [h]
  cases ht : touches t
  · simp [leftLevels, ht]
  · simp only [leftLevels, ht, ↓reduceIte, Finset.card_insert_of_notMem hi]
    by_cases htop : w.head?.map touches = some true
    · have hm := (top_mem_levels_iff touches w).2 htop
      simp [htop, Finset.insert_eq_of_mem hm]
    · have hm := (top_mem_levels_iff touches w).not.mpr htop
      simp [htop, Finset.card_insert_of_notMem hm, Nat.add_assoc]

theorem mem_leftLevels_iff {α : Type*} (touches : α → Bool) (w : List α) (j : ℕ) :
    j ∈ leftLevels touches w ↔ ∃ above t below, w = above ++ t :: below ∧
      touches t = true ∧ (j = below.length ∨ j = below.length + 1) := by
  induction w with
  | nil => simp [leftLevels]
  | cons a w ih =>
    constructor
    · intro hj
      by_cases ha : touches a
      · simp only [leftLevels, ha, ↓reduceIte, Finset.mem_insert] at hj
        rcases hj with h | h | hj
        · exact ⟨[], a, w, rfl, ha, Or.inr h⟩
        · exact ⟨[], a, w, rfl, ha, Or.inl h⟩
        · obtain ⟨above, t, below, eq, ht, hh⟩ := ih.mp hj
          exact ⟨a :: above, t, below, congrArg (List.cons a) eq, ht, hh⟩
      · simp [leftLevels, ha] at hj
        obtain ⟨above, t, below, eq, ht, hh⟩ := ih.mp hj
        exact ⟨a :: above, t, below, congrArg (List.cons a) eq, ht, hh⟩
    · rintro ⟨above, t, below, eq, ht, hh⟩
      cases above with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at eq
        obtain ⟨rfl, rfl⟩ := eq
        rcases hh with rfl | rfl <;> simp [leftLevels, ht]
      | cons b above =>
        simp only [List.cons_append, List.cons.injEq] at eq
        have hj := ih.mpr ⟨above, t, below, eq.2, ht, hh⟩
        cases ha : touches a <;> simp [leftLevels, ha, hj]

end StripTransfer

namespace StripWords

def touchesLeft : Layer → Bool
  | .L | .B => true
  | .R => false

/-- Heights of vertices on the left edge of the bottom-normalized layer word. -/
def rootLevels (w : List Layer) : Finset ℕ := StripTransfer.leftLevels touchesLeft w

theorem card_rootLevels_eq_marks (w : List Layer) : (rootLevels w).card = marks w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    change (StripTransfer.leftLevels touchesLeft (t :: w)).card = _
    rw [StripTransfer.card_leftLevels_cons]
    change (StripTransfer.leftLevels touchesLeft w).card = marks w at ih
    rw [ih]
    cases w with
    | nil => cases t <;> rfl
    | cons u w => cases t <;> cases u <;> rfl

theorem mem_rootLevels_iff (w : List Layer) (j : ℕ) :
    j ∈ rootLevels w ↔ ∃ above t below, w = above ++ t :: below ∧
      t ≠ .R ∧ (j = below.length ∨ j = below.length + 1) := by
  have touch (t : Layer) : touchesLeft t = true ↔ t ≠ .R := by
    cases t <;> decide
  simp only [rootLevels, StripTransfer.mem_leftLevels_iff, touch]

end StripWords

namespace StripWords

open Layer

/-- A layer word of half-perimeter `n` with a chosen vertex on its left edge. -/
abbrev RootedWord (n : ℕ) :=
  (v : ↑((words L n ++ words R n ++ words B n).toFinset)) × ↑(rootLevels v.val)

private theorem sum_marks_toFinset (v : List (List Layer)) (hv : v.Nodup) :
    ∑ w ∈ v.toFinset, marks w = (v.map marks).sum := by
  induction v with
  | nil => simp
  | cons w v ih =>
    obtain ⟨hw, hv⟩ := List.nodup_cons.mp hv
    simp [hw, ih hv]

theorem card_rootedWord (n : ℕ) : Nat.card (RootedWord n) = W n + Z n := by
  have hd {s t : Layer} (hst : s ≠ t) : (words s n).Disjoint (words t n) := by
    intro v hs ht
    exact hst (Option.some.inj (((mem_words _ _ _).1 hs).2.1.symm.trans
      ((mem_words _ _ _).1 ht).2.1))
  have nodup : (words L n ++ words R n ++ words B n).Nodup := by
    apply ((words_nodup L n).append (words_nodup R n) (hd (by decide))).append (words_nodup B n)
    intro v hv hb
    rcases List.mem_append.mp hv with hl | hr
    · exact hd (s := L) (t := B) (by decide) hl hb
    · exact hd (s := R) (t := B) (by decide) hr hb
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_coe, card_rootLevels_eq_marks]
  rw [Finset.sum_coe_sort, sum_marks_toFinset _ nodup]
  simp [W, Z, weight, Nat.add_assoc]

end StripWords

namespace StripWords

open Layer

theorem mem_all_words (n : ℕ) (w : List Layer) :
    w ∈ (words L n ++ words R n ++ words B n).toFinset ↔ valid w ∧ cost w = n := by
  cases w with
  | nil => simp [mem_words, valid]
  | cons x t => cases x <;> simp [mem_words]

/-- The geometric representation records the reversed layer list and root height. -/
abbrev Marked (n : ℕ) :=
  (w : {w : List Layer // valid w ∧ cost w = n}) × ↑(rootLevels w.val)

def markedEquivRooted (n : ℕ) : Marked n ≃ RootedWord n where
  toFun p := ⟨⟨p.1.val, (mem_all_words n _).2 p.1.property⟩, p.2⟩
  invFun p := ⟨⟨p.1.val, (mem_all_words n _).1 p.1.property⟩, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_marked (n : ℕ) : Nat.card (Marked n) = W n + Z n :=
  (Nat.card_congr (markedEquivRooted n)).trans (card_rootedWord n)

end StripWords

namespace StripTransfer

open PowerSeries

/-- The ordinary generating function of a natural-valued count. -/
noncomputable def stripSeries (f : ℕ → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => (f n : ℤ)

private theorem coeff_twice (n : ℕ) (p : PowerSeries ℤ) :
    coeff n (2 * p) = 2 * coeff n p := by simp only [two_mul, map_add]

private theorem coeff_thrice (n : ℕ) (p : PowerSeries ℤ) :
    coeff n (3 * p) = 3 * coeff n p := by
  rw [show 3 * p = p + p + p by ring, map_add, map_add]
  ring

private theorem coeff_two (n : ℕ) : coeff (R := ℤ) n 2 = if n = 0 then 2 else 0 := by
  rw [show (2 : PowerSeries ℤ) = 1 + 1 by ring, map_add, coeff_one]
  split <;> rfl

private theorem shift_twice (p : PowerSeries ℤ) :
    X ^ 2 * p = X * (X * p) := by rw [sq, mul_assoc]

/-- The four recurrences obtained by appending a layer, expressed as identities of series. -/
theorem strip_series_eqs (c b w z : ℕ → ℕ)
    (h₀ : (c 0, b 0, w 0, z 0) = (0, 0, 0, 0))
    (h₁ : (c 1, b 1, w 1, z 1) = (0, 0, 0, 0))
    (h₂ : (c 2, b 2, w 2, z 2) = (1, 0, 2, 0))
    (hrec : ∀ n, (c (n+3), b (n+3), w (n+3), z (n+3)) =
      (c (n+2) + b (n+2),
       (if n = 0 then 1 else 0) + 2*c (n+1) + b (n+2),
       w (n+2) + 2*z (n+2) + c (n+2) + b (n+2),
       (if n = 0 then 2 else 0) + w (n+1) + 3*c (n+1) + z (n+2) + b (n+2))) :
    stripSeries c = X ^ 2 + X * (stripSeries c + stripSeries b) ∧
    stripSeries b = X ^ 3 + 2 * X ^ 2 * stripSeries c + X * stripSeries b ∧
    stripSeries w = 2 * X ^ 2 + X * (stripSeries w + 2 * stripSeries z +
      stripSeries c + stripSeries b) ∧
    stripSeries z = 2 * X ^ 3 + X ^ 2 * (stripSeries w + 3 * stripSeries c) +
      X * (stripSeries z + stripSeries b) := by
  simp only [Prod.mk.injEq] at h₀ h₁ h₂ hrec
  obtain ⟨c₀, b₀, w₀, z₀⟩ := h₀
  obtain ⟨c₁, b₁, w₁, z₁⟩ := h₁
  obtain ⟨c₂, b₂, w₂, z₂⟩ := h₂
  refine ⟨PowerSeries.ext ?_, PowerSeries.ext ?_, PowerSeries.ext ?_, PowerSeries.ext ?_⟩
  all_goals
    rintro (_ | _ | _ | n)
    case' succ.succ.succ => obtain ⟨cn, bn, wn, zn⟩ := hrec n
    all_goals
      simp +arith [stripSeries, mul_assoc, shift_twice, coeff_X_pow, coeff_twice, coeff_thrice,
        coeff_two, *]

/-- Positive walks are obtained by orienting a shape with a marked boundary vertex. -/
theorem strip_series_total (a w z : ℕ → ℕ) (a₀ : a 0 = 1) (w₀ : w 0 = 0) (z₀ : z 0 = 0)
    (ha : ∀ n, a (n+1) = 2 * (w (n+1) + z (n+1))) :
    stripSeries a = 1 + 2 * (stripSeries w + stripSeries z) := by
  apply PowerSeries.ext
  rintro (_ | n) <;>
    simp [stripSeries, coeff_one, coeff_twice, a₀, w₀, z₀, ha]

end StripTransfer

namespace StripTransfer

/-- Elimination of the four layer-count generating functions. Here `c` counts shapes
ending in the left singleton (or, by reflection, in the right singleton), and `b`
counts shapes ending in the double layer. The series `w` and `z` count the same
shapes with a marked left-boundary vertex, according as the last layer is a
singleton or a double layer. -/
theorem transfer_identity {R : Type*} [CommRing R] (x a c b w z : R)
    (hc : c = x ^ 2 + x * (c + b))
    (hb : b = x ^ 3 + 2 * x ^ 2 * c + x * b)
    (hw : w = 2 * x ^ 2 + x * (w + 2 * z + c + b))
    (hz : z = 2 * x ^ 3 + x ^ 2 * (w + 3 * c) + x * (z + b))
    (ha : a = 1 + 2 * (w + z)) :
    a * ((1 + x ^ 2) ^ 2 * (1 - 2 * x) ^ 2) =
      1 - 4 * x + 10 * x ^ 2 - 14 * x ^ 3 + 27 * x ^ 4 -
        18 * x ^ 5 + 10 * x ^ 6 - 6 * x ^ 7 := by
  rw [ha]
  linear_combination
    (2*x + 2*x^2 + 12*x^3 - 8*x^4 + 4*x^5) * hc +
    (4*x - 2*x^2 + 6*x^3 + 6*x^4) * hb +
    (2 * (1 + x^2) * (1 - 2*x) * (1 - x + x^2)) * hw +
    (2 * (1 + x^2) * (1 - 2*x) * (1 + x)) * hz

end StripTransfer

open PowerSeries
open OMA.S_oeis_a022445

namespace StripWords

private theorem gf_of_count_eq (f : ℕ → ℕ)
    (h : ∀ n, f n = (if n = 0 then 1 else 0) + 2 * Nat.card (RootedWord n)) :
    (PowerSeries.mk fun n => (f n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 10 * X ^ 2 - 14 * X ^ 3 + 27 * X ^ 4 - 18 * X ^ 5 +
        10 * X ^ 6 - 6 * X ^ 7 := by
  obtain ⟨hc, hb, hw, hz⟩ := StripTransfer.strip_series_eqs C BCount W Z
    base_zero base_one base_two words_rec
  have hzero := base_zero
  simp only [Prod.mk.injEq] at hzero
  have h' (n : ℕ) : f n = (if n = 0 then 1 else 0) + 2 * (W n + Z n) := by
    rw [← card_rootedWord]
    exact h n
  have ha := StripTransfer.strip_series_total f W Z
    (by simpa [hzero.2.2.1, hzero.2.2.2] using h' 0)
    hzero.2.2.1 hzero.2.2.2
    (fun n => by simpa using h' (n + 1))
  exact StripTransfer.transfer_identity X _ _ _ _ _ hc hb hw hz ha

/-- The generating function of the oriented, rooted layer words. -/
theorem rooted_word_gf :
    (PowerSeries.mk fun n => (((if n = 0 then 1 else 0) + 2 * Nat.card (RootedWord n) : ℕ) : ℤ)) *
        ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 10 * X ^ 2 - 14 * X ^ 3 + 27 * X ^ 4 - 18 * X ^ 5 +
        10 * X ^ 6 - 6 * X ^ 7 :=
  gf_of_count_eq _ (fun _ => rfl)

/-- A positive directed cycle is counted by its vertically normalized layer word,
the height to translate to the origin, and one of its two orientations. -/
theorem gf_of_rooted_count
    (h : ∀ n, a n = (if n = 0 then 1 else 0) + 2 * Nat.card (RootedWord n)) :
    (PowerSeries.mk fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 10 * X ^ 2 - 14 * X ^ 3 + 27 * X ^ 4 - 18 * X ^ 5 +
        10 * X ^ 6 - 6 * X ^ 7 :=
  gf_of_count_eq a h

abbrev PositiveCycle (n : ℕ) :=
  {p : strip.Walk origin origin // p.length = 2 * n ∧ p.IsCycle}

/-- Decoding and encoding may be proved independently: injections in both
directions give the required count, without a choice of compatible inverses. -/
theorem gf_of_geometric_embeddings
    (encode : ∀ n, 0 < n → Nonempty (PositiveCycle n ↪ Bool × Marked n))
    (decode : ∀ n, 0 < n → Nonempty ((Bool × Marked n) ↪ PositiveCycle n)) :
    (PowerSeries.mk fun n => (a n : ℤ)) * ((1 + X ^ 2) ^ 2 * (1 - 2 * X) ^ 2) =
      1 - 4 * X + 10 * X ^ 2 - 14 * X ^ 3 + 27 * X ^ 4 - 18 * X ^ 5 +
        10 * X ^ 6 - 6 * X ^ 7 := by
  apply gf_of_rooted_count
  intro n
  by_cases hn : n = 0
  · subst n
    have hbase := base_zero
    simp only [Prod.mk.injEq] at hbase
    have empty_walk : a 0 = 1 := by
      rw [a]
      have single : {w : strip.Walk origin origin | w.length = 2 * 0 ∧ (0 = 0 ∨ w.IsCycle)} =
          {SimpleGraph.Walk.nil} := by
        rw [← SimpleGraph.Walk.setOfPred_length_eq_zero]
        ext w
        simp
      rw [single, Set.ncard_singleton]
    rw [card_rootedWord]
    simp [empty_walk, hbase.2.2.1, hbase.2.2.2]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨e⟩ := Function.Embedding.antisymm (encode n hn').some (decode n hn').some
    have hcard : a n = Nat.card (PositiveCycle n) := by
      simp only [a, hn, false_or]
      rfl
    rw [hcard, Nat.card_congr e, Nat.card_prod, card_marked, card_rootedWord]
    simp [hn]

end StripWords

namespace StripParity

/-- Whether the endpoints of an undirected edge have different colors. -/
def crosses {V : Type*} (c : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun u v => decide (c u ≠ c v), fun u v => by simp only [ne_comm]⟩

theorem count_crossings_mod_two {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (c : V → Bool) :
    w.edges.countP (crosses c) % 2 = if c a = c b then 0 else 1 := by
  induction w with
  | nil => simp
  | @cons a b d _ w ih =>
    rw [SimpleGraph.Walk.edges_cons, List.countP_cons]
    change (_ + (if decide (c a ≠ c b) then 1 else 0)) % 2 = _
    cases ha : c a <;> cases hb : c b <;> cases hd : c d <;>
      simp [hb, hd] at ih ⊢ <;> omega

theorem even_count_crossings {V : Type*} {G : SimpleGraph V} {a : V}
    (w : G.Walk a a) (c : V → Bool) : Even (w.edges.countP (crosses c)) := by
  have h : w.edges.countP (crosses c) % 2 = 0 := by simpa using count_crossings_mod_two w c
  exact ⟨w.edges.countP (crosses c) / 2, by omega⟩

theorem no_crossing_iff_constant {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (c : V → Bool) :
    (∀ e ∈ w.edges, crosses c e = false) ↔ (∀ u ∈ w.support, c u = c a) := by
  induction w with
  | nil => simp
  | @cons a b d h w ih =>
    have first : crosses c s(a,b) = false ↔ c a = c b := by
      change decide (c a ≠ c b) = false ↔ _
      simp
    rw [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.support_cons]
    simp only [List.forall_mem_cons, first, ih, true_and, eq_self]
    have hb := w.start_mem_support
    grind

theorem crossing_iff_support {V : Type*} {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (c : V → Bool) :
    (∃ e ∈ w.edges, crosses c e = true) ↔
      ∃ u ∈ w.support, ∃ v ∈ w.support, c u ≠ c v := by
  constructor
  · rintro ⟨e, he, hce⟩
    by_contra! hall
    have hconst : ∀ u ∈ w.support, c u = c a := fun u hu => hall u hu a w.start_mem_support
    have hfalse := (no_crossing_iff_constant w c).mpr hconst e he
    simp_all
  · rintro ⟨u, hu, v, hv, huv⟩
    by_contra! h
    have hfalse : ∀ e ∈ w.edges, crosses c e = false := by
      intro e he
      simpa using h e he
    have hconst := (no_crossing_iff_constant w c).mp hfalse
    exact huv ((hconst u hu).trans (hconst v hv).symm)

end StripParity

namespace StripLayers

open OMA.S_oeis_a022445

def pt (i : Fin 3) (h : ℤ) : stripSet :=
  ⟨((i.val : ℤ), h), by change 0 ≤ (i.val : ℤ) ∧ (i.val : ℤ) ≤ 2; omega⟩

def upEdge (i : Fin 3) (h : ℤ) : Sym2 stripSet := s(pt i h, pt i (h+1))

def cutMask (E : Finset (Sym2 stripSet)) (h : ℤ) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => upEdge i h ∈ E)

def below (h : ℤ) (v : stripSet) : Bool := decide (v.1.2 ≤ h)

theorem upEdge_injective (h : ℤ) : Function.Injective (fun i => upEdge i h) := by
  intro i j he
  apply Fin.ext
  simp only [upEdge, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk] at he
  rcases he with ⟨v, -⟩ | ⟨v, -⟩ <;>
    have hcol := congrArg (fun p : stripSet => p.1.1) v <;>
    simp only [pt] at hcol <;> exact_mod_cast hcol

theorem crossing_endpoints {h : ℤ} {u v : stripSet} (hadj : strip.Adj u v)
    (hu : u.1.2 ≤ h) (hv : h < v.1.2) :
    ∃ i : Fin 3, u = pt i h ∧ v = pt i (h+1) := by
  rcases u with ⟨⟨x,y⟩,hx⟩
  rcases v with ⟨⟨z,t⟩,hz⟩
  change |x-z| + |y-t| = 1 at hadj
  change 0 ≤ x ∧ x ≤ 2 at hx
  change y ≤ h at hu
  change h < t at hv
  rw [abs_of_nonpos (by omega : y-t ≤ 0)] at hadj
  have hnon := abs_nonneg (x-z)
  have hxz : x-z = 0 := abs_eq_zero.mp (by omega)
  let i : Fin 3 := ⟨x.toNat, by omega⟩
  refine ⟨i, Subtype.ext (Prod.ext ?_ ?_), Subtype.ext (Prod.ext ?_ ?_)⟩ <;>
    dsimp [pt,i] <;> omega

theorem vertical_of_crossing {a b : stripSet} (w : strip.Walk a b) (h : ℤ)
    (e : Sym2 stripSet) (he : e ∈ w.edges) (hc : StripParity.crosses (below h) e = true) :
    ∃ i : Fin 3, upEdge i h = e := by
  revert he hc
  refine Sym2.inductionOn e ?_
  intro u v he hc
  have hadj := w.adj_of_mem_edges he
  change decide (below h u ≠ below h v) = true at hc
  by_cases hu : u.1.2 ≤ h
  · have hv : h < v.1.2 := by by_contra! hh; simp [below, hu, hh] at hc
    obtain ⟨i, rfl, rfl⟩ := crossing_endpoints hadj hu hv
    exact ⟨i, rfl⟩
  · have hv : v.1.2 ≤ h := by by_contra hh; simp [below, hu, hh] at hc
    obtain ⟨i, rfl, rfl⟩ := crossing_endpoints hadj.symm hv (lt_of_not_ge hu)
    exact ⟨i, Sym2.eq_swap⟩

theorem crossing_image {a b : stripSet} (w : strip.Walk a b) (h : ℤ) :
    (cutMask w.edges.toFinset h).image (fun i => upEdge i h) =
      w.edges.toFinset.filter (fun e => StripParity.crosses (below h) e = true) := by
  ext e
  constructor
  · rintro he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hm := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨hm, ?_⟩
    change decide (below h (pt i h) ≠ below h (pt i (h+1))) = true
    simp [below, pt]
  · intro he
    obtain ⟨hm,hc⟩ := Finset.mem_filter.mp he
    obtain ⟨i,rfl⟩ := vertical_of_crossing w h e (List.mem_toFinset.mp hm) hc
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hm⟩, rfl⟩

theorem cut_card_zero_or_two {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle) (h : ℤ) :
    (cutMask w.edges.toFinset h).card = 0 ∨ (cutMask w.edges.toFinset h).card = 2 := by
  have hc := congrArg Finset.card (crossing_image w h)
  rw [Finset.card_image_of_injective _ (upEdge_injective h), hw.edges_nodup.card_eq_countP] at hc
  have hev := StripParity.even_count_crossings w (below h)
  have hcard : (cutMask w.edges.toFinset h).card ≤ 3 := by
    simpa using (cutMask w.edges.toFinset h).card_le_univ
  simp only [Bool.decide_eq_true] at hc
  obtain ⟨k,hk⟩ := hev
  have hsum := hc.trans hk
  omega

theorem cut_nonempty_iff {a b : stripSet} (w : strip.Walk a b) (h : ℤ) :
    (cutMask w.edges.toFinset h).Nonempty ↔
      (∃ u ∈ w.support, u.1.2 ≤ h) ∧ ∃ v ∈ w.support, h < v.1.2 := by
  have hc : (cutMask w.edges.toFinset h).Nonempty ↔
      ∃ e ∈ w.edges, StripParity.crosses (below h) e = true := by
    constructor
    · rintro ⟨i,hi⟩
      refine ⟨upEdge i h, List.mem_toFinset.mp (Finset.mem_filter.mp hi).2, ?_⟩
      change decide (below h (pt i h) ≠ below h (pt i (h+1))) = true
      simp [below,pt]
    · rintro ⟨e,he,hc⟩
      obtain ⟨i,rfl⟩ := vertical_of_crossing w h e he hc
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,List.mem_toFinset.mpr he⟩⟩
  rw [hc, StripParity.crossing_iff_support]
  constructor
  · rintro ⟨u,hu,v,hv,hne⟩
    by_cases ha : u.1.2 ≤ h <;> by_cases hb : v.1.2 ≤ h
    · simp [below,ha,hb] at hne
    · exact ⟨⟨u,hu,ha⟩,⟨v,hv,lt_of_not_ge hb⟩⟩
    · exact ⟨⟨v,hv,hb⟩,⟨u,hu,lt_of_not_ge ha⟩⟩
    · simp [below,ha,hb] at hne
  · rintro ⟨⟨u,hu,ha⟩,⟨v,hv,hb⟩⟩
    exact ⟨u,hu,v,hv,by simp [below,ha,not_le_of_gt hb]⟩

theorem cut_between {a b : stripSet} (w : strip.Walk a b) {h j k : ℤ}
    (hj : h ≤ j) (jk : j ≤ k) (hh : (cutMask w.edges.toFinset h).Nonempty)
    (hk : (cutMask w.edges.toFinset k).Nonempty) : (cutMask w.edges.toFinset j).Nonempty := by
  obtain ⟨⟨u,hu,ha⟩,-⟩ := (cut_nonempty_iff w h).mp hh
  obtain ⟨-,⟨v,hv,hb⟩⟩ := (cut_nonempty_iff w k).mp hk
  exact (cut_nonempty_iff w j).mpr ⟨⟨u,hu,ha.trans hj⟩,⟨v,hv,lt_of_le_of_lt jk hb⟩⟩

/-- The visited integer heights, including both extreme levels. -/
def heights {a b : stripSet} (w : strip.Walk a b) : Finset ℤ :=
  w.support.toFinset.image (fun v => v.1.2)

theorem mem_heights {a b : stripSet} (w : strip.Walk a b) (v : stripSet)
    (hv : v ∈ w.support) : v.1.2 ∈ heights w :=
  Finset.mem_image.mpr ⟨v, List.mem_toFinset.mpr hv, rfl⟩

theorem heights_nonempty {a b : stripSet} (w : strip.Walk a b) : (heights w).Nonempty :=
  ⟨_, mem_heights w a w.start_mem_support⟩

def bottom {a b : stripSet} (w : strip.Walk a b) : ℤ := (heights w).min' (heights_nonempty w)

def top {a b : stripSet} (w : strip.Walk a b) : ℤ := (heights w).max' (heights_nonempty w)

theorem height_bounds {a b : stripSet} {w : strip.Walk a b} {v : stripSet} (hv : v ∈ w.support) :
    bottom w ≤ v.1.2 ∧ v.1.2 ≤ top w :=
  ⟨(heights w).min'_le _ (mem_heights w v hv), (heights w).le_max' _ (mem_heights w v hv)⟩

theorem cut_bounds_iff {a b : stripSet} (w : strip.Walk a b) (h : ℤ) :
    (cutMask w.edges.toFinset h).Nonempty ↔ bottom w ≤ h ∧ h < top w := by
  rw [cut_nonempty_iff]
  constructor
  · rintro ⟨⟨u,hu,hu'⟩,⟨v,hv,hv'⟩⟩
    exact ⟨(height_bounds hu).1.trans hu', lt_of_lt_of_le hv' (height_bounds hv).2⟩
  · rintro ⟨hl,ht⟩
    obtain ⟨u,hu,hu'⟩ := Finset.mem_image.mp ((heights w).min'_mem (heights_nonempty w))
    obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp ((heights w).max'_mem (heights_nonempty w))
    exact ⟨⟨u,List.mem_toFinset.mp hu,hu'.le.trans hl⟩,⟨v,List.mem_toFinset.mp hv,lt_of_lt_of_eq ht hv'.symm⟩⟩

/-- A cycle cannot fit in one row: a leftmost visited vertex on that row would have at most one neighbor. -/
theorem bottom_lt_top {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle) : bottom w < top w := by
  by_contra! hflat
  obtain ⟨p,hp,hm⟩ := w.support.toFinset.exists_min_image (fun v : stripSet => v.1.1)
    ⟨a,List.mem_toFinset.mpr w.start_mem_support⟩
  have hd := hw.ncard_neighborSet_toSubgraph_eq_two (List.mem_toFinset.mp hp)
  obtain ⟨u,v,huv,hs⟩ := Set.ncard_eq_two.mp hd
  have hrow (z : stripSet) (hz : z ∈ w.support) : z.1.2 = bottom w := by
    have hh := height_bounds hz
    omega
  have hn (z : stripSet) (hz : w.toSubgraph.Adj p z) : z.1.1 = p.1.1+1 ∧ z.1.2 = bottom w := by
    have hv := SimpleGraph.Walk.mem_support_of_adj_toSubgraph hz.symm
    have hle := hm z (List.mem_toFinset.mpr hv)
    have ha := w.toSubgraph.adj_sub hz
    change |p.1.1-z.1.1| + |p.1.2-z.1.2| = 1 at ha
    rw [hrow p (List.mem_toFinset.mp hp), hrow z hv, sub_self, abs_zero, add_zero,
      abs_of_nonpos (sub_nonpos.mpr hle)] at ha
    exact ⟨by omega,hrow z hv⟩
  have hu := hn u (by change u ∈ w.toSubgraph.neighborSet p; simp [hs])
  have hv := hn v (by change v ∈ w.toSubgraph.neighborSet p; simp [hs])
  exact huv (Subtype.ext (Prod.ext (hu.1.trans hv.1.symm) (hu.2.trans hv.2.symm)))

end StripLayers

namespace StripLayers

open OMA.S_oeis_a022445 SimpleGraph

private theorem at_left {h : ℤ} {v : stripSet} (hv : strip.Adj (pt 0 (h+1)) v) :
    v = pt 0 h ∨ v = pt 0 (h+1+1) ∨ v = pt 1 (h+1) := by
  rcases v with ⟨⟨i,j⟩, hv'⟩
  change 0 ≤ i ∧ i ≤ 2 at hv'
  change |0-i| + |h+1-j| = 1 at hv
  simp only [zero_sub, abs_neg, abs_of_nonneg hv'.1] at hv
  by_cases hj : 0 ≤ h+1-j
  · rw [abs_of_nonneg hj] at hv
    by_cases hi : i = 0
    · left
      apply Subtype.ext
      change (i,j) = (0,h)
      congr 1
      omega
    · right; right; apply Subtype.ext; change (i,j) = (1,h+1); congr 1 <;> omega
  · rw [abs_of_neg (by omega : h+1-j < 0)] at hv
    right; left; apply Subtype.ext; change (i,j) = (0,h+1+1); congr 1 <;> omega

private theorem adj_only_two {V : Type*} {G : SimpleGraph V} {a v x y z : V}
    {w : G.Walk a a} (hw : w.IsCycle) (hx : w.toSubgraph.Adj v x)
    (hy : w.toSubgraph.Adj v y) (hxy : x ≠ y) (hz : w.toSubgraph.Adj v z) :
    z = x ∨ z = y := by
  have hn := hw.ncard_neighborSet_toSubgraph_eq_two (Walk.mem_support_of_adj_toSubgraph hx)
  obtain ⟨b,c,_,hs⟩ := Set.ncard_eq_two.mp hn
  have ez (t) (ht : w.toSubgraph.Adj v t) : t = b ∨ t = c := by
    change t ∈ w.toSubgraph.neighborSet v at ht
    simpa [hs] using ht
  grind [ez x hx, ez y hy, ez z hz]

private theorem other_neighbor {V : Type*} {G : SimpleGraph V} {a v x : V}
    {w : G.Walk a a} (hw : w.IsCycle) (hx : w.toSubgraph.Adj v x) :
    ∃ z, w.toSubgraph.Adj v z ∧ z ≠ x := by
  have hn := hw.ncard_neighborSet_toSubgraph_eq_two (Walk.mem_support_of_adj_toSubgraph hx)
  obtain ⟨b,c,hbc,hs⟩ := Set.ncard_eq_two.mp hn
  by_cases hbx : b = x
  · refine ⟨c, ?_, fun e => hbc (hbx.trans e.symm)⟩
    change c ∈ w.toSubgraph.neighborSet v; simp [hs]
  · refine ⟨b, ?_, hbx⟩
    change b ∈ w.toSubgraph.neighborSet v; simp [hs]

private theorem mask_adj {a : stripSet} {w : strip.Walk a a} (i : Fin 3) (h : ℤ) :
    i ∈ cutMask w.edges.toFinset h ↔ w.toSubgraph.Adj (pt i h) (pt i (h+1)) := by
  classical
  simp [cutMask, upEdge, Walk.adj_toSubgraph_iff_mem_edges]

theorem left_persists {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle) (h : ℤ)
    (h1 : 1 ∈ cutMask w.edges.toFinset h) (h2 : 1 ∈ cutMask w.edges.toFinset (h+1)) :
    0 ∈ cutMask w.edges.toFinset h ↔ 0 ∈ cutMask w.edges.toFinset (h+1) := by
  have hd := (mask_adj 1 h).mp h1
  have hu := (mask_adj 1 (h+1)).mp h2
  have hdu : pt 1 h ≠ pt 1 (h+1+1) := by
    intro he; have := congrArg (fun v : stripSet => v.val.2) he
    change h = h+1+1 at this; omega
  have nh : ¬ w.toSubgraph.Adj (pt 0 (h+1)) (pt 1 (h+1)) := by
    intro hh
    have ht := adj_only_two hw hd.symm hu hdu hh.symm
    rcases ht with he | he <;>
      exact (by decide : (0 : ℤ) ≠ 1) (congrArg (fun v : stripSet => v.val.1) he)
  rw [mask_adj, mask_adj]
  constructor
  · intro hl
    obtain ⟨z,hz,hz'⟩ := other_neighbor hw hl.symm
    rcases at_left (w.toSubgraph.adj_sub hz) with he | he | he
    · exact (hz' he).elim
    · exact he ▸ hz
    · exact (nh (he ▸ hz)).elim
  · intro hu0
    obtain ⟨z,hz,hz'⟩ := other_neighbor hw hu0
    rcases at_left (w.toSubgraph.adj_sub hz) with he | he | he
    · exact (he ▸ hz : w.toSubgraph.Adj _ _).symm
    · exact (hz' he).elim
    · exact (nh (he ▸ hz)).elim

theorem no_mixed {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle) (h : ℤ) :
    ¬ (cutMask w.edges.toFinset h = {0,1} ∧ cutMask w.edges.toFinset (h+1) = {1,2}) ∧
    ¬ (cutMask w.edges.toFinset h = {1,2} ∧ cutMask w.edges.toFinset (h+1) = {0,1}) := by
  constructor <;> rintro ⟨hl,hu⟩ <;>
    have hp := left_persists hw h (by rw [hl]; decide) (by rw [hu]; decide) <;>
    rw [hl,hu] at hp
  · exact (by decide : (0 : Fin 3) ∉ ({1,2} : Finset (Fin 3))) (hp.mp (by decide))
  · exact (by decide : (0 : Fin 3) ∉ ({1,2} : Finset (Fin 3))) (hp.mpr (by decide))

private theorem at_right {h : ℤ} {v : stripSet} (hv : strip.Adj (pt 2 (h+1)) v) :
    v = pt 2 h ∨ v = pt 2 (h+1+1) ∨ v = pt 1 (h+1) := by
  rcases v with ⟨⟨i,j⟩, hv'⟩
  change 0 ≤ i ∧ i ≤ 2 at hv'
  change |2-i| + |h+1-j| = 1 at hv
  rw [abs_of_nonneg (by omega : 0 ≤ 2-i)] at hv
  by_cases hj : 0 ≤ h+1-j
  · rw [abs_of_nonneg hj] at hv
    by_cases hi : i = 2
    · left
      apply Subtype.ext
      change (i,j) = (2,h)
      congr 1
      omega
    · right; right; apply Subtype.ext; change (i,j) = (1,h+1); congr 1 <;> omega
  · rw [abs_of_neg (by omega : h+1-j < 0)] at hv
    right; left; apply Subtype.ext; change (i,j) = (2,h+1+1); congr 1 <;> omega

private theorem outer_neighbors (i : Fin 3) (hi : i ≠ 1) (h : ℤ) {v : stripSet}
    (hv : strip.Adj (pt i (h+1)) v) :
    v = pt i h ∨ v = pt i (h+1+1) ∨ v = pt 1 (h+1) := by
  have hpos : i = 0 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hpos with rfl | rfl
  · exact at_left hv
  · exact at_right hv

private theorem three_neighbors {V : Type*} {G : SimpleGraph V} {a v d u m : V}
    {w : G.Walk a a} (hw : w.IsCycle) (hdu : d ≠ u) (hdm : d ≠ m) (hum : u ≠ m)
    (cover : ∀ z, w.toSubgraph.Adj v z → z = d ∨ z = u ∨ z = m) :
    w.toSubgraph.Adj v m ↔ ¬ (w.toSubgraph.Adj v d ↔ w.toSubgraph.Adj v u) := by
  constructor
  · intro hm he
    obtain ⟨z,hz,hzm⟩ := other_neighbor hw hm
    have both : w.toSubgraph.Adj v d ∧ w.toSubgraph.Adj v u := by
      rcases cover z hz with rfl | rfl | heq
      · exact ⟨hz,he.mp hz⟩
      · exact ⟨he.mpr hz,hz⟩
      · exact (hzm heq).elim
    rcases adj_only_two hw both.1 both.2 hdu hm with h | h
    · exact hdm h.symm
    · exact hum h.symm
  · intro he
    by_contra hm
    apply he
    constructor
    · intro hd
      obtain ⟨z,hz,hzd⟩ := other_neighbor hw hd
      rcases cover z hz with h | rfl | rfl
      · exact (hzd h).elim
      · exact hz
      · exact (hm hz).elim
    · intro hu
      obtain ⟨z,hz,hzu⟩ := other_neighbor hw hu
      rcases cover z hz with rfl | h | rfl
      · exact hz
      · exact (hzu h).elim
      · exact (hm hz).elim

/-- Either horizontal edge is determined by the two neighboring cut masks. -/
theorem horizontal_iff {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle)
    (i : Fin 3) (hi : i ≠ 1) (h : ℤ) :
    w.toSubgraph.Adj (pt i (h+1)) (pt 1 (h+1)) ↔
      ¬ (i ∈ cutMask w.edges.toFinset h ↔ i ∈ cutMask w.edges.toFinset (h+1)) := by
  rw [mask_adj, mask_adj, w.toSubgraph.adj_comm (pt i h) (pt i (h+1))]
  apply three_neighbors hw
  · intro he
    have hy := congrArg (fun v : stripSet => v.val.2) he
    change h = h+1+1 at hy; omega
  · intro he
    have hy := congrArg (fun v : stripSet => v.val.2) he
    change h = h+1 at hy; omega
  · intro he
    have hy := congrArg (fun v : stripSet => v.val.2) he
    change h+1+1 = h+1 at hy; omega
  · intro v hv
    exact outer_neighbors i hi h (w.toSubgraph.adj_sub hv)

/-- A boundary point lies on the cycle exactly when one of its vertical edges is used. -/
theorem outer_visit_iff {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle)
    (i : Fin 3) (hi : i ≠ 1) (h : ℤ) :
    pt i (h+1) ∈ w.support ↔
      i ∈ cutMask w.edges.toFinset h ∨ i ∈ cutMask w.edges.toFinset (h+1) := by
  rw [mask_adj, mask_adj]
  constructor
  · intro hv
    obtain ⟨b,c,hbc,hs⟩ := Set.ncard_eq_two.mp (hw.ncard_neighborSet_toSubgraph_eq_two hv)
    obtain ⟨z,hz,hzm⟩ : ∃ z, w.toSubgraph.Adj (pt i (h+1)) z ∧ z ≠ pt 1 (h+1) := by
      by_cases hb : b = pt 1 (h+1)
      · refine ⟨c, ?_, fun he => hbc (hb.trans he.symm)⟩
        change c ∈ w.toSubgraph.neighborSet _; simp [hs]
      · refine ⟨b, ?_, hb⟩
        change b ∈ w.toSubgraph.neighborSet _; simp [hs]
    rcases outer_neighbors i hi h (w.toSubgraph.adj_sub hz) with rfl | rfl | he
    · exact Or.inl hz.symm
    · exact Or.inr hz
    · exact (hzm he).elim
  · rintro (hd | hu)
    · exact Walk.mem_support_of_adj_toSubgraph hd.symm
    · exact Walk.mem_support_of_adj_toSubgraph hu

end StripLayers

namespace StripLayers

open OMA.S_oeis_a022445 SimpleGraph

private theorem in_column (v : stripSet) : ∃ i : Fin 3, v = pt i v.1.2 := by
  obtain ⟨⟨x,y⟩, hx⟩ := v
  change 0 ≤ x ∧ x ≤ 2 at hx
  let i : Fin 3 := ⟨x.toNat, by omega⟩
  refine ⟨i, Subtype.ext (Prod.ext ?_ rfl)⟩
  change x = (x.toNat : ℤ)
  omega

/-- All vertical cuts determine a strip cycle's edge set, independently of the
choice of its root and orientation. -/
theorem edges_eq_of_masks_eq {a b : stripSet} {p : strip.Walk a a} {q : strip.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle)
    (hm : ∀ h, cutMask p.edges.toFinset h = cutMask q.edges.toFinset h) :
    p.edges.toFinset = q.edges.toFinset := by
  have vert (i : Fin 3) (h : ℤ) :
      p.toSubgraph.Adj (pt i h) (pt i (h+1)) ↔ q.toSubgraph.Adj (pt i h) (pt i (h+1)) := by
    have hh : i ∈ cutMask p.edges.toFinset h ↔ i ∈ cutMask q.edges.toFinset h := by rw [hm]
    simpa [cutMask, upEdge, Walk.adj_toSubgraph_iff_mem_edges] using hh
  have horiz (i : Fin 3) (hi : i ≠ 1) (h : ℤ) :
      p.toSubgraph.Adj (pt i h) (pt 1 h) ↔ q.toSubgraph.Adj (pt i h) (pt 1 h) := by
    have H := (horizontal_iff hp i hi (h-1)).trans
      (by simpa only [hm] using (horizontal_iff hq i hi (h-1)).symm)
    simpa using H
  have horiz' (i : Fin 3) (hi : i ≠ 1) (h : ℤ) :
      p.toSubgraph.Adj (pt 1 h) (pt i h) ↔ q.toSubgraph.Adj (pt 1 h) (pt i h) := by
    rw [p.toSubgraph.adj_comm (pt 1 h), q.toSubgraph.adj_comm (pt 1 h)]
    exact horiz i hi h
  ext e
  refine Sym2.inductionOn e ?_
  intro u v
  simp only [List.mem_toFinset, ← Walk.adj_toSubgraph_iff_mem_edges]
  by_cases huv : strip.Adj u v
  · rcases lt_trichotomy u.1.2 v.1.2 with hv | h | hv
    · obtain ⟨i, hu, hv'⟩ := crossing_endpoints huv (le_refl _) hv
      rw [hu, hv']
      exact vert _ _
    · obtain ⟨i, hi⟩ := in_column u
      obtain ⟨j, hj⟩ := in_column v
      let k := u.1.2
      have hu' : u = pt i k := hi
      have hv' : v = pt j k := hj.trans (congrArg (pt j) h.symm)
      rw [hu', hv'] at huv ⊢
      change |(i.val : ℤ) - j.val| + |k-k| = 1 at huv
      fin_cases i <;> fin_cases j <;> first
        | exact horiz 0 (by decide) k
        | exact horiz 2 (by decide) k
        | exact horiz' 0 (by decide) k
        | exact horiz' 2 (by decide) k
        | norm_num at huv
    · obtain ⟨i, hv', hu⟩ := crossing_endpoints huv.symm (le_refl _) hv
      rw [p.toSubgraph.adj_comm, q.toSubgraph.adj_comm, hv', hu]
      exact vert _ _
  · exact ⟨fun h => (huv (p.toSubgraph.adj_sub h)).elim,
      fun h => (huv (q.toSubgraph.adj_sub h)).elim⟩

end StripLayers

namespace StripLayers

open OMA.S_oeis_a022445 StripWords

def layerMask : Layer → Finset (Fin 3)
  | .L => {0,1}
  | .R => {1,2}
  | .B => {0,2}

def label (s : Finset (Fin 3)) : Layer :=
  if s = {0,1} then .L else if s = {1,2} then .R else .B

theorem label_layerMask (l : Layer) : label (layerMask l) = l := by cases l <;> decide

theorem layerMask_label (s : Finset (Fin 3)) (hs : s.card = 2) : layerMask (label s) = s := by
  revert s; decide

theorem compatible_labels (s t : Finset (Fin 3)) (hs : s.card = 2) (ht : t.card = 2)
    (hLR : ¬(s = {0,1} ∧ t = {1,2})) (hRL : ¬(s = {1,2} ∧ t = {0,1})) :
    compatible (label t) (label s) := by
  let (u v : Layer) : Decidable (compatible u v) := by
    cases u <;> cases v <;> unfold compatible <;> infer_instance
  revert s t; decide

/-- Cut heights increase bottom-to-top; the word lists the top layer first. -/
def wordAt (E : Finset (Sym2 stripSet)) (base : ℤ) : ℕ → List Layer
  | 0 => []
  | k+1 => label (cutMask E (base + k)) :: wordAt E base k

theorem length_wordAt (E : Finset (Sym2 stripSet)) (base : ℤ) (k : ℕ) :
    (wordAt E base k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [wordAt,ih]

def span {a b : stripSet} (w : strip.Walk a b) : ℕ := (top w - bottom w).toNat

def word {a b : stripSet} (w : strip.Walk a b) : List Layer :=
  wordAt w.edges.toFinset (bottom w) (span w)

theorem length_word {a b : stripSet} (w : strip.Walk a b) : (word w).length = span w :=
  length_wordAt _ _ _

theorem active_at {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle)
    {i : ℕ} (hi : i < span w) : (cutMask w.edges.toFinset (bottom w+i)).card = 2 := by
  have hlt := bottom_lt_top hw
  change i < (top w - bottom w).toNat at hi
  have hn := (cut_bounds_iff w (bottom w+i)).mpr ⟨by omega,by omega⟩
  exact (cut_card_zero_or_two hw _).resolve_left (Finset.card_pos.mpr hn).ne'

theorem wordAt_valid {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle)
    (k : ℕ) (hk : 0 < k) (hb : k ≤ span w) : valid (wordAt w.edges.toFinset (bottom w) k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => trivial
    | succ j =>
      change compatible (label (cutMask _ (bottom w + ((j + 1 : ℕ) : ℤ))))
        (label (cutMask _ (bottom w+j))) ∧ valid (wordAt _ _ (j+1))
      constructor
      · have hno := no_mixed hw (bottom w+j)
        have hh : bottom w + ((j+1 : ℕ) : ℤ) = bottom w + j + 1 := by omega
        apply compatible_labels _ _ (active_at hw (by omega : j < span w))
          (active_at hw (by omega : j+1 < span w))
        · simpa only [hh] using hno.1
        · simpa only [hh] using hno.2
      · exact ih (by omega) (by omega)

theorem word_valid {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle) : valid (word w) := by
  apply wordAt_valid hw _ _ (le_refl _)
  have hlt := bottom_lt_top hw
  change 0 < (top w - bottom w).toNat
  omega

end StripLayers

namespace StripLayers

open StripWords OMA.S_oeis_a022445

private theorem wordAt_marks (E : Finset (Sym2 stripSet)) (b : ℤ) (k j : ℕ) :
    j ∈ rootLevels (wordAt E b k) ↔ ∃ i : ℕ, i < k ∧
      touchesLeft (label (cutMask E (b+i))) = true ∧ (j = i ∨ j = i+1) := by
  induction k with
  | zero => simp [wordAt, rootLevels, StripTransfer.leftLevels]
  | succ k ih =>
    let touch := touchesLeft (label (cutMask E (b + k)))
    change j ∈ (if touch then insert ((wordAt E b k).length + 1)
      (insert (wordAt E b k).length (rootLevels (wordAt E b k)))
      else rootLevels (wordAt E b k)) ↔ _
    rw [length_wordAt]
    cases ht : touch with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · rintro ⟨i,hi,hh,hj⟩; exact ⟨i,by omega,hh,hj⟩
      · rintro ⟨i,hi,hh,hj⟩
        have hik : i ≠ k := by rintro rfl; exact Bool.noConfusion (ht.symm.trans hh)
        exact ⟨i,by omega,hh,hj⟩
    | true =>
      simp only [↓reduceIte, Finset.mem_insert, ih]
      constructor
      · rintro (hj | hj | ⟨i,hi,hh,hj⟩)
        · exact ⟨k,by omega,ht,Or.inr hj⟩
        · exact ⟨k,by omega,ht,Or.inl hj⟩
        · exact ⟨i,by omega,hh,hj⟩
      · rintro ⟨i,hi,hh,hj⟩
        by_cases heq : i = k
        · subst i; rcases hj with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
        · exact Or.inr (Or.inr ⟨i,by omega,hh,hj⟩)

private theorem left_label_iff (s : Finset (Fin 3)) (hs : s.card = 2) :
    touchesLeft (label s) = true ↔ 0 ∈ s := by
  revert s
  decide

/-- The marks on the normalized word are precisely the visited heights at the left boundary. -/
theorem word_marks_iff {a : stripSet} {w : strip.Walk a a} (hw : w.IsCycle) (j : ℕ) :
    j ∈ rootLevels (word w) ↔ pt 0 (bottom w + j) ∈ w.support := by
  change j ∈ rootLevels (wordAt _ _ _) ↔ _
  rw [wordAt_marks]
  have hh := bottom_lt_top hw
  have hspan : (span w : ℤ) = top w - bottom w := Int.toNat_of_nonneg (by omega)
  let z : ℤ := bottom w + j
  have hz : z-1+1 = z := by omega
  have hvis := outer_visit_iff hw 0 (by decide) (z-1)
  rw [hz] at hvis
  change _ ↔ pt 0 z ∈ w.support
  rw [hvis]
  constructor
  · rintro ⟨i,hi,ht,hj⟩
    have h0 := (left_label_iff _ (active_at hw hi)).mp ht
    rcases hj with rfl | rfl
    · exact Or.inr h0
    · left
      convert h0 using 3
      dsimp [z]
      omega
  · rintro (h0 | h0)
    · have hm := (cut_bounds_iff w _).1 ⟨0,h0⟩
      change bottom w ≤ bottom w + (j : ℤ) - 1 ∧ _ at hm
      have hj : 0 < j := by omega
      have he : z-1 = bottom w + (j-1 : ℕ) := by dsimp [z]; omega
      have hi : j-1 < span w := by dsimp [z] at hm; omega
      rw [he] at h0
      exact ⟨j-1,hi,(left_label_iff _ (active_at hw hi)).mpr h0,Or.inr (by omega)⟩
    · have hm := (cut_bounds_iff w _).1 ⟨0,h0⟩
      have hi : j < span w := by dsimp [z] at hm; omega
      exact ⟨j,hi,(left_label_iff _ (active_at hw hi)).mpr h0,Or.inl rfl⟩

theorem origin_mark {w : strip.Walk origin origin} (hw : w.IsCycle) :
    (-bottom w).toNat ∈ rootLevels (word w) := by
  apply (word_marks_iff hw _).2
  have hb := (height_bounds w.start_mem_support).1
  change bottom w ≤ 0 at hb
  rw [Int.toNat_of_nonneg (by omega : 0 ≤ -bottom w), add_neg_cancel]
  exact w.start_mem_support

end StripLayers

namespace StripCycle

open SimpleGraph

theorem exists_cycle_of_list {V : Type*} {G : SimpleGraph V} (u : V) (l : List V)
    (h : (u :: l).Nodup) (hlen : 3 ≤ (u :: l).length)
    (hchain : (u :: (l ++ [u])).IsChain G.Adj) :
    ∃ p : G.Walk u u, p.IsCycle ∧ p.support = u :: (l ++ [u]) ∧ p.length = (u :: l).length := by
  let q := Walk.ofSupport (u :: (l ++ [u])) (by simp) hchain
  have he : (u :: (l ++ [u])).getLast (by simp) = u := by
    change ((u :: l) ++ [u]).getLast _ = u
    simp
  let p : G.Walk u u := q.copy rfl he
  have hs : p.support = u :: (l ++ [u]) :=
    (q.support_copy rfl he).trans (Walk.support_ofSupport _ hchain)
  have hl : p.length = (u :: l).length :=
    (q.length_copy rfl he).trans ((Walk.length_ofSupport _ hchain).trans (by simp))
  refine ⟨p, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, hl ▸ hlen⟩, hs, hl⟩
  have hpos : ¬p.Nil := fun hn => by have := hn.length_eq_zero; omega
  rw [Walk.isPath_def, Walk.support_tail_of_not_nil _ hpos, hs, List.tail_cons]
  exact (List.perm_append_comm.nodup_iff).mpr (show ([u] ++ l).Nodup from h)

theorem exists_rooted_cycle_of_list {V : Type*} {G : SimpleGraph V} (u : V) (l : List V)
    (h : (u :: l).Nodup) (hlen : 3 ≤ (u :: l).length)
    (hchain : (u :: (l ++ [u])).IsChain G.Adj) (x : V) (hx : x ∈ u :: l) :
    ∃ p : G.Walk x x, p.IsCycle ∧ p.length = (u :: l).length ∧
      p.edges.Perm (List.zipWith (s(·, ·)) (u :: (l ++ [u])) (l ++ [u])) ∧
      ∀ v, v ∈ p.support ↔ v ∈ u :: l := by
  classical
  obtain ⟨q, hq, hs, hl⟩ := exists_cycle_of_list u l h hlen hchain
  have hmem (v : V) : v ∈ q.support ↔ v ∈ u :: l := by rw [hs]; simp; tauto
  let p := q.rotate x ((hmem x).mpr hx)
  refine ⟨p, hq.rotate _, (Walk.length_rotate ..).trans hl, ?_, ?_⟩
  · have he : q.edges = List.zipWith (s(·, ·)) (u :: (l ++ [u])) (l ++ [u]) := by
      rw [Walk.edges_eq_zipWith_support, hs]; rfl
    exact he ▸ (q.rotate_edges x ((hmem x).mpr hx)).perm
  · intro v
    exact (q.mem_support_rotate_iff ..).trans (hmem v)

end StripCycle

namespace StripConstruct
open StripWords StripWords.Layer OMA.S_oeis_a022445 StripLayers

def left : Layer → Fin 3 | L | B => 0 | R => 1
def right : Layer → Fin 3 | L => 1 | R | B => 2
def baseCols : Layer → List (Fin 3) | L => [0,1] | R => [1,2] | B => [0,1,2]
def middleCols : Layer → List (Fin 3) | B => [1] | L | R => []
def leftTurn (s t : Layer) : List (Fin 3) :=
  if left s = left t then [left t] else [left s, left t]
def rightTurn (s t : Layer) : List (Fin 3) :=
  if right s = right t then [right t] else [right t, right s]
def row (h : ℤ) (xs : List (Fin 3)) : List stripSet := xs.map (fun i => pt i h)

/-- The part of the boundary below its top height, traversed from left to right. -/
def inside : List Layer → ℤ → Layer → List stripSet
  | [], h, s => row (h-1) (baseCols s)
  | t::w, h, s => row (h-1) (leftTurn s t) ++ inside w (h-1) t ++ row (h-1) (rightTurn s t)

def tail (w : List Layer) (h : ℤ) (s : Layer) : List stripSet :=
  inside w h s ++ row h (right s :: middleCols s)

def ringList (w : List Layer) (h : ℤ) (s : Layer) : List stripSet :=
  pt (left s) h :: tail w h s

end StripConstruct

namespace StripConstruct
open StripWords StripWords.Layer OMA.S_oeis_a022445 StripLayers

theorem row_height {h : ℤ} {l : List (Fin 3)} {v : stripSet} (hv : v ∈ row h l) : v.val.2 = h := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  rfl

theorem inside_below (w : List Layer) (h : ℤ) (s : Layer) :
    ∀ v ∈ inside w h s, v.val.2 < h := by
  induction w generalizing h s with
  | nil => intro v hv; have := row_height hv; omega
  | cons t w ih =>
    intro v hv
    simp only [inside, List.mem_append] at hv
    rcases hv with (ha | hb) | hc
    · have := row_height ha; omega
    · have := ih (h-1) t v hb; omega
    · have := row_height hc; omega

theorem row_inj (h : ℤ) : Function.Injective (fun i => pt i h) := by
  intro i j e
  have := congrArg (fun v : stripSet => v.val.1) e
  apply Fin.ext
  simpa [pt] using this

/-- Inserting an older, lower list between two disjoint pieces of the new top row
    preserves the absence of repeated vertices. -/
theorem nodup_around (a c : List (Fin 3)) (b : List stripSet) (h : ℤ)
    (hac : (a ++ c).Nodup) (hb : b.Nodup) (hlt : ∀ v ∈ b, v.val.2 < h) :
    (row h a ++ b ++ row h c).Nodup := by
  have hr : (row h a ++ row h c).Nodup := by
    simpa only [row, List.map_append] using hac.map (row_inj h)
  obtain ⟨ha, hc, hd⟩ := List.nodup_append.mp hr
  rw [List.append_assoc]
  apply List.nodup_append.mpr
  refine ⟨ha, List.nodup_append.mpr ⟨hb, hc, ?_⟩, ?_⟩
  · intro x hx y hy e; subst y
    have := hlt x hx; have := row_height hy; omega
  · intro x hx y hy e; subst y
    rcases List.mem_append.mp hy with hxb | hxc
    · have := hlt x hxb; have := row_height hx; omega
    · exact hd x hx x hxc rfl

theorem inside_nodup (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s::w)) :
    (inside w h s).Nodup := by
  induction w generalizing s h with
  | nil =>
    apply List.Nodup.map (row_inj h.pred)
    cases s <;> decide
  | cons t w ih =>
    obtain ⟨hc, ht⟩ := hv
    apply nodup_around _ _ _ _ _ (ih (h-1) t ht) (inside_below w (h-1) t)
    cases s <;> cases t <;> simp [compatible] at hc <;> decide

theorem ring_nodup (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s::w)) :
    (ringList w h s).Nodup := by
  change (row h [left s] ++ inside w h s ++ row h (right s :: middleCols s)).Nodup
  apply nodup_around _ _ _ _ _ (inside_nodup w h s hv) (inside_below w h s)
  cases s <;> decide

theorem inside_length (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s::w)) :
    (inside w h s).length + (middleCols s).length + 2 = 2 * cost (s::w) := by
  induction w generalizing s h with
  | nil => cases s <;> simp [inside, row, baseCols, middleCols, cost, firstCost]
  | cons t w ih =>
    obtain ⟨hc, ht⟩ := hv
    have prev := ih (h-1) t ht
    cases s <;> cases t <;> simp [compatible] at hc <;>
      simp [inside, row, leftTurn, rightTurn, left, right, middleCols, cost, stepCost] at prev ⊢ <;> omega

theorem ring_length (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s::w)) :
    (ringList w h s).length = 2 * cost (s::w) := by
  have := inside_length w h s hv
  simp only [ringList, tail, row, List.length_cons, List.length_append, List.length_map]
  omega

theorem ring_three_le (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s::w)) :
    3 ≤ (ringList w h s).length := by
  rw [ring_length w h s hv]
  suffices 2 ≤ cost (s::w) by omega
  induction w generalizing s with
  | nil => cases s <;> decide
  | cons t w ih =>
    have := ih t hv.2
    simp only [cost]
    omega

end StripConstruct

namespace StripConstruct

open StripWords StripWords.Layer OMA.S_oeis_a022445 StripLayers

theorem rim_down (i : Fin 3) (h : ℤ) : strip.Adj (pt i h) (pt i (h-1)) := by
  change |(i.val : ℤ) - i.val| + |h - (h-1)| = 1
  simp

theorem rim_up (i : Fin 3) (h : ℤ) : strip.Adj (pt i (h-1)) (pt i h) :=
  (rim_down i h).symm

theorem rim_horizontal (i j : Fin 3) (h : ℤ) (hij : |(i.val : ℤ) - j.val| = 1) :
    strip.Adj (pt i h) (pt j h) := by
  change |(i.val : ℤ) - j.val| + |h-h| = 1
  simpa using hij

theorem trace_chain_wrap {V : Type*} {R : V → V → Prop} {u a b v : V} {l m r : List V}
    (hl : (u :: (l ++ [a])).IsChain R) (hm : (a :: (m ++ [b])).IsChain R)
    (hr : (b :: (r ++ [v])).IsChain R) :
    (u :: (l ++ a :: (m ++ b :: (r ++ [v])))).IsChain R :=
  List.isChain_cons_split.mpr ⟨hl, List.isChain_cons_split.mpr ⟨hm, hr⟩⟩

theorem inside_chain (w : List Layer) (h : ℤ) (s : Layer) :
    (pt (left s) h :: (inside w h s ++ [pt (right s) h])).IsChain strip.Adj := by
  induction w generalizing s h with
  | nil =>
    cases s <;> simp [inside, row, baseCols, left, right, List.isChain_cons_cons, rim_down,
      rim_up, rim_horizontal 0 1 _ (by decide), rim_horizontal 1 2 _ (by decide)]
  | cons t w ih =>
    let l := if left s = left t then [] else [pt (left s) (h-1)]
    let r := if right s = right t then [] else [pt (right s) (h-1)]
    have hl : row (h-1) (leftTurn s t) = l ++ [pt (left t) (h-1)] := by
      by_cases hh : left s = left t <;> simp [row, leftTurn, l, hh]
    have hr : row (h-1) (rightTurn s t) = pt (right t) (h-1) :: r := by
      by_cases hh : right s = right t <;> simp [row, rightTurn, r, hh]
    have lchain : (pt (left s) h :: (l ++ [pt (left t) (h-1)])).IsChain strip.Adj := by
      cases s <;> cases t <;> norm_num [l, left, List.isChain_cons_cons, rim_down,
        rim_horizontal 0 1 _ (by decide), rim_horizontal 1 0 _ (by decide)]
    have rchain : (pt (right t) (h-1) :: (r ++ [pt (right s) h])).IsChain strip.Adj := by
      cases s <;> cases t <;> norm_num [r, right, List.isChain_cons_cons, rim_up,
        show (1 : Fin 3) ≠ 2 by decide, show (2 : Fin 3) ≠ 1 by decide,
        rim_horizontal 1 2 _ (by decide), rim_horizontal 2 1 _ (by decide)]
    simpa only [inside, hl, hr, List.append_assoc, List.cons_append, List.nil_append] using
      (trace_chain_wrap lchain (ih (h-1) t) rchain)

theorem rim_chain (w : List Layer) (h : ℤ) (s : Layer) :
    (pt (left s) h :: (tail w h s ++ [pt (left s) h])).IsChain strip.Adj := by
  have cap : (pt (right s) h :: (row h (middleCols s) ++ [pt (left s) h])).IsChain strip.Adj := by
    cases s <;> simp [row, middleCols, left, right, List.isChain_cons_cons,
      rim_horizontal 1 0 _ (by decide), rim_horizontal 2 1 _ (by decide)]
  simpa only [tail, row, List.map_cons, List.map_append, List.append_assoc, List.cons_append,
    List.nil_append] using
    (List.isChain_cons_split.mpr ⟨inside_chain w h s, cap⟩)

end StripConstruct

namespace StripConstruct

open OMA.S_oeis_a022445 StripWords StripLayers

/-- A simple cycle counts each of its unoriented edges exactly once. -/
theorem length_eq_of_edgeFinset_eq {a b : stripSet} {p : strip.Walk a a} {q : strip.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle) (he : p.edges.toFinset = q.edges.toFinset) :
    p.length = q.length := by
  rw [← p.length_edges, ← q.length_edges, ← List.toFinset_card_of_nodup hp.edges_nodup,
    ← List.toFinset_card_of_nodup hq.edges_nodup, he]

/-- The top-rooted boundary traverses the layer list in its stated order. -/
theorem ring_cycle_exists (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s :: w)) :
    ∃ p : strip.Walk (pt (left s) h) (pt (left s) h), p.IsCycle ∧
      p.support = (ringList w h s ++ [pt (left s) h]) ∧ p.length = 2 * cost (s :: w) := by
  obtain ⟨p, hp, hs, hl⟩ := StripCycle.exists_cycle_of_list (pt (left s) h) (tail w h s)
    (ring_nodup w h s hv) (ring_three_le w h s hv) (rim_chain w h s)
  exact ⟨p, hp, hs, hl.trans (ring_length w h s hv)⟩

/-- Rooting at any point on the boundary preserves its edges and semiperimeter. -/
theorem ring_cycle_exists_at (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s :: w))
    (x : stripSet) (hx : x ∈ ringList w h s) :
    ∃ p : strip.Walk x x, p.IsCycle ∧ p.length = 2 * cost (s :: w) ∧
      p.edges.Perm (List.zipWith (s(·, ·)) (pt (left s) h :: (tail w h s ++ [pt (left s) h]))
        (tail w h s ++ [pt (left s) h])) ∧ ∀ v, v ∈ p.support ↔ v ∈ ringList w h s := by
  obtain ⟨p, hp, hl, he, hm⟩ := StripCycle.exists_rooted_cycle_of_list (pt (left s) h)
    (tail w h s) (ring_nodup w h s hv) (ring_three_le w h s hv) (rim_chain w h s) x hx
  exact ⟨p, hp, hl.trans (ring_length w h s hv), he, hm⟩

end StripConstruct

namespace StripConstruct

open StripWords StripWords.Layer OMA.S_oeis_a022445 StripLayers

theorem bottom_left_mem_inside (s : Layer) (w : List Layer) (h : ℤ) :
    pt (left s) (h-1) ∈ inside w h s := by
  cases w with
  | nil => cases s <;> simp [inside, row, left, baseCols]
  | cons t w =>
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨left s, by by_cases he : left s = left t <;> simp [leftTurn, he], rfl⟩

theorem interior_left_mem_extend (s t : Layer) (w : List Layer) (h : ℤ) (v : stripSet)
    (hv : v ∈ pt (left t) (h-1) :: inside w (h-1) t) :
    v ∈ pt (left s) h :: inside (t::w) h s := by
  apply List.mem_cons_of_mem
  apply List.mem_append_left
  rcases List.mem_cons.mp hv with rfl | hm
  · apply List.mem_append_left
    apply List.mem_map.mpr
    exact ⟨left t, by unfold leftTurn; split <;> simp, rfl⟩
  · exact List.mem_append_right _ hm

theorem layer_left_ends (above below : List Layer) (t s : Layer) (w : List Layer)
    (he : s :: w = above ++ t :: below) (h : ℤ) :
    pt (left t) (h - (above.length : ℤ)) ∈ pt (left s) h :: inside w h s ∧
    pt (left t) (h - (above.length : ℤ) - 1) ∈ pt (left s) h :: inside w h s := by
  induction above generalizing s w h with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.length_nil, Nat.cast_zero, sub_zero]
    exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (bottom_left_mem_inside _ _ _)⟩
  | cons a above ih =>
    cases w with
    | nil => simp at he
    | cons b w =>
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨ht, hb⟩ := ih b w he.2 (h-1)
      have hy : h - ((a::above).length : ℤ) = (h-1) - above.length := by simp; ring
      rw [hy]
      exact ⟨interior_left_mem_extend s b w h _ ht, interior_left_mem_extend s b w h _ hb⟩

theorem origin_mem_ring (s : Layer) (w : List Layer) (j : ℕ) (hj : j ∈ rootLevels (s :: w)) :
    pt 0 0 ∈ ringList w (((w.length+1 : ℕ) : ℤ) - j) s := by
  obtain ⟨above, t, below, he, hl, hj⟩ := (mem_rootLevels_iff _ _).mp hj
  have ht : left t = 0 := by cases t <;> simp_all [left]
  have len := congrArg List.length he
  simp only [List.length_cons, List.length_append] at len
  have ⟨hu, hd⟩ := layer_left_ends above below t s w he (((w.length+1 : ℕ) : ℤ) - j)
  rw [ht] at hu hd
  have hz : pt 0 0 ∈ pt (left s) (((w.length+1 : ℕ) : ℤ) - j) :: inside w (((w.length+1 : ℕ) : ℤ) - j) s := by
    rcases hj with hj | hj
    · have hy : (((w.length+1 : ℕ) : ℤ) - j) - (above.length : ℤ) - 1 = 0 := by omega
      simpa only [hy] using hd
    · have hy : (((w.length+1 : ℕ) : ℤ) - j) - (above.length : ℤ) = 0 := by omega
      simpa only [hy] using hu
  rcases List.mem_cons.mp hz with hh | hh
  · exact List.mem_cons.mpr (Or.inl hh)
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hh)

end StripConstruct

namespace StripConstruct
open StripWords StripWords.Layer OMA.S_oeis_a022445 StripLayers

/-- The two columns crossed at each integer cut, reading layers downwards. -/
def cutProfile : List Layer → ℤ → Fin 3 → ℤ → Prop
  | [], _, _, _ => False
  | s :: w, h, i, k => (k = h-1 ∧ (i = left s ∨ i = right s)) ∨ cutProfile w (h-1) i k

end StripConstruct

namespace StripConstruct

open StripWords StripWords.Layer OMA.S_oeis_a022445 StripLayers

/-- Edges encountered on a vertex list, starting at its distinguished first vertex. -/
def traceEdges {V : Type*} (u : V) : List V → List (Sym2 V)
  | [] => []
  | v :: r => s(u,v) :: traceEdges v r

theorem traceEdges_eq_zipWith {V : Type*} (u : V) (r : List V) :
    traceEdges u r = List.zipWith (s(·,·)) (u::r) r := by
  induction r generalizing u with
  | nil => rfl
  | cons x xs ih => simp only [traceEdges, List.zipWith_cons_cons, ih]

theorem traceEdges_split {V : Type*} (u : V) (pre : List V) (v : V) (post : List V) :
    traceEdges u (pre ++ v :: post) = traceEdges u (pre ++ [v]) ++ traceEdges v post := by
  induction pre generalizing u with
  | nil => simp [traceEdges]
  | cons x xs ih => simp only [List.cons_append, traceEdges, ih]

theorem rim_pt_eq {i j : Fin 3} {k h : ℤ} : pt i k = pt j h ↔ i = j ∧ k = h := by
  constructor
  · intro he
    have hx : (i.val : ℤ) = j.val := congrArg (fun q : stripSet => q.1.1) he
    exact ⟨Fin.ext (by exact_mod_cast hx), congrArg (fun q : stripSet => q.1.2) he⟩
  · rintro ⟨rfl,rfl⟩; rfl

theorem rim_v_down (i j : Fin 3) (k h : ℤ) :
    s(pt i k,pt i (k+1)) = s(pt j h,pt j (h-1)) ↔ k = h-1 ∧ i = j := by
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, rim_pt_eq]
  omega

theorem rim_v_up (i j : Fin 3) (k h : ℤ) :
    s(pt i k,pt i (k+1)) = s(pt j (h-1),pt j h) ↔ k = h-1 ∧ i = j := by
  conv_lhs => rhs; rw [Sym2.eq_swap]
  exact rim_v_down i j k h

theorem rim_v_horizontal (i j l : Fin 3) (k h : ℤ) :
    s(pt i k,pt i (k+1)) ≠ s(pt j h,pt l h) := by
  intro he
  simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, rim_pt_eq] at he
  omega

theorem inside_cutProfile (w : List Layer) (h : ℤ) (s : Layer) (i : Fin 3) (k : ℤ) :
    s(pt i k,pt i (k+1)) ∈ traceEdges (pt (left s) h) (inside w h s ++ [pt (right s) h]) ↔
      cutProfile (s::w) h i k := by
  induction w generalizing h s with
  | nil =>
    cases s <;> simp only [inside, row, baseCols, left, right, traceEdges, cutProfile,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, rim_v_down, rim_v_up, rim_v_horizontal, false_or, or_false] <;> tauto
  | cons t w ih =>
    let l := if left s = left t then [] else [pt (left s) (h-1)]
    let r := if right s = right t then [] else [pt (right s) (h-1)]
    have hl : row (h-1) (leftTurn s t) = l ++ [pt (left t) (h-1)] := by
      by_cases hh : left s = left t <;> simp [row, leftTurn, l, hh]
    have hr : row (h-1) (rightTurn s t) = pt (right t) (h-1) :: r := by
      by_cases hh : right s = right t <;> simp [row, rightTurn, r, hh]
    have cutL : s(pt i k,pt i (k+1)) ∈ traceEdges (pt (left s) h) (l ++ [pt (left t) (h-1)])
        ↔ k = h-1 ∧ i = left s := by
      by_cases hh : left s = left t <;> simp only [l, hh, ↓reduceIte, traceEdges,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        rim_v_down, rim_v_horizontal, or_false]
    have cutR : s(pt i k,pt i (k+1)) ∈ traceEdges (pt (right t) (h-1)) (r ++ [pt (right s) h])
        ↔ k = h-1 ∧ i = right s := by
      by_cases hh : right s = right t <;> simp only [r, hh, ↓reduceIte, traceEdges,
        List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        rim_v_up, rim_v_horizontal, false_or, or_false]
    rw [inside, hl, hr]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [traceEdges_split _ l, traceEdges_split _ (inside w (h-1) t)]
    simp only [List.mem_append, cutL, cutR, ih]
    change _ ↔ (k = h-1 ∧ (i = left s ∨ i = right s)) ∨ cutProfile (t::w) (h-1) i k
    tauto

theorem ring_cutProfile (w : List Layer) (h : ℤ) (s : Layer) (i : Fin 3) (k : ℤ) :
    s(pt i k,pt i (k+1)) ∈ traceEdges (pt (left s) h) (tail w h s ++ [pt (left s) h]) ↔
      cutProfile (s::w) h i k := by
  have hcap : s(pt i k,pt i (k+1)) ∉ traceEdges (pt (right s) h)
      (row h (middleCols s) ++ [pt (left s) h]) := by
    cases s <;> simp only [row, middleCols, traceEdges, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, rim_v_horizontal,
      false_or, not_false_eq_true]
  simp only [tail, row, List.map_cons, List.append_assoc, List.cons_append]
  rw [traceEdges_split, List.mem_append, inside_cutProfile]
  exact or_iff_left hcap

theorem cutProfile_lt {w : List Layer} {h k : ℤ} {i : Fin 3} (hm : cutProfile w h i k) : k < h := by
  induction w generalizing h with
  | nil => exact False.elim hm
  | cons s w ih =>
    rcases hm with ⟨hh, _⟩ | hm
    · omega
    · have := ih hm; omega

theorem cutProfile_top (w : List Layer) (s : Layer) (h : ℤ) (i : Fin 3) :
    cutProfile (s::w) h i (h-1) ↔ i = left s ∨ i = right s := by
  have hn : ¬cutProfile w (h-1) i (h-1) := fun hm => (lt_irrefl _ (cutProfile_lt hm))
  simp [cutProfile, hn]

theorem cutProfile_word_injective (w v : List Layer) (h : ℤ)
    (he : ∀ i k, cutProfile w h i k ↔ cutProfile v h i k) : w = v := by
  induction w generalizing v h with
  | nil =>
    cases v with
    | nil => rfl
    | cons t v =>
      exact False.elim ((he (left t) (h-1)).2 ((cutProfile_top v t h (left t)).2 (Or.inl rfl)))
  | cons s w ih =>
    cases v with
    | nil =>
      exact False.elim ((he (left s) (h-1)).1 ((cutProfile_top w s h (left s)).2 (Or.inl rfl)))
    | cons t v =>
      have topEq (i : Fin 3) : (i = left s ∨ i = right s) ↔ (i = left t ∨ i = right t) := by
        simpa only [cutProfile_top] using he i (h-1)
      have hst : s = t := by
        have h0 := topEq 0; have h1 := topEq 1; have h2 := topEq 2
        cases s <;> cases t <;> first | rfl | (exfalso; revert h0 h1 h2; decide)
      subst t
      apply congrArg (List.cons s)
      apply ih v (h-1)
      intro i k
      by_cases hk : k = h-1
      · subst k
        constructor <;> intro hp <;> exact False.elim ((lt_irrefl _) (cutProfile_lt hp))
      · simpa [cutProfile, hk] using he i k

theorem cutProfile_injective {s t : Layer} {w v : List Layer} {h j : ℤ}
    (he : ∀ i k, cutProfile (s::w) h i k ↔ cutProfile (t::v) j i k) :
    h = j ∧ s::w = t::v := by
  have hh := cutProfile_lt ((he (left s) (h-1)).1 ((cutProfile_top w s h _).2 (Or.inl rfl)))
  have hj := cutProfile_lt ((he (left t) (j-1)).2 ((cutProfile_top v t j _).2 (Or.inl rfl)))
  have hhj : h = j := by omega
  subst j
  exact ⟨rfl, cutProfile_word_injective _ _ _ he⟩

end StripConstruct

namespace StripConstruct
open OMA.S_oeis_a022445 StripLayers StripWords

theorem cols_iff_mask (s : Layer) (i : Fin 3) :
    (i = left s ∨ i = right s) ↔ i ∈ layerMask s := by
  cases s <;> simp [left, right, layerMask]

theorem cutProfile_wordAt (E : Finset (Sym2 stripSet)) (base : ℤ) (k : ℕ)
    (ha : ∀ j : ℕ, j < k → (cutMask E (base+j)).card = 2) (i : Fin 3) (h : ℤ) :
    cutProfile (wordAt E base k) (base+k) i h ↔
      base ≤ h ∧ h < base+k ∧ i ∈ cutMask E h := by
  induction k with
  | zero => simp [wordAt, cutProfile]; omega
  | succ k ih =>
    have ht : base + ((k+1 : ℕ) : ℤ) - 1 = base + k := by omega
    rw [wordAt, cutProfile, ht, cols_iff_mask, layerMask_label _ (ha k (by omega)), ih (fun j hj => ha j (by omega))]
    constructor
    · rintro (⟨rfl, hm⟩ | ⟨hl, hu, hm⟩) <;> exact ⟨by omega, by omega, hm⟩
    · rintro ⟨hl, hu, hm⟩
      by_cases hh : h = base + k
      · exact Or.inl ⟨hh, hh ▸ hm⟩
      · exact Or.inr ⟨hl, by omega, hm⟩

theorem cutProfile_word {a : stripSet} {p : strip.Walk a a} (hp : p.IsCycle) (i : Fin 3) (h : ℤ) :
    cutProfile (word p) (top p) i h ↔ i ∈ cutMask p.edges.toFinset h := by
  have hp' := bottom_lt_top hp
  have ht : bottom p + (span p : ℤ) = top p := by unfold span; omega
  have hw := cutProfile_wordAt p.edges.toFinset (bottom p) (span p)
    (fun _ hj => active_at hp hj) i h
  change cutProfile (wordAt _ _ _) _ _ _ ↔ _
  rw [ht] at hw
  rw [hw]
  constructor
  · exact fun hs => hs.2.2
  · intro hm
    have hs := (cut_bounds_iff p h).mp ⟨i,hm⟩
    exact ⟨hs.1, hs.2, hm⟩

theorem cuts_of_word_eq {a b : stripSet} {p : strip.Walk a a} {q : strip.Walk b b}
    (hp : p.IsCycle) (hq : q.IsCycle) (hbottom : bottom p = bottom q) (hword : word p = word q)
    (h : ℤ) : cutMask p.edges.toFinset h = cutMask q.edges.toFinset h := by
  have hw := congrArg List.length hword
  rw [length_word, length_word] at hw
  have htp := bottom_lt_top hp
  have htq := bottom_lt_top hq
  unfold span at hw
  have htop : top p = top q := by omega
  ext i
  rw [← cutProfile_word hp, ← cutProfile_word hq, hword, htop]

end StripConstruct

namespace StripConstruct
open StripWords OMA.S_oeis_a022445 StripLayers

theorem ring_cycle_roundtrip (w : List Layer) (h : ℤ) (s : Layer) (hv : valid (s::w))
    (x : stripSet) (hx : x ∈ ringList w h s) :
    ∃ p : strip.Walk x x, p.IsCycle ∧ p.length = 2 * cost (s::w) ∧
      word p = s::w ∧ top p = h := by
  obtain ⟨p, hp, hl, he, _⟩ := ring_cycle_exists_at w h s hv x hx
  have hpro (i : Fin 3) (k : ℤ) : cutProfile (word p) (top p) i k ↔ cutProfile (s::w) h i k := by
    rw [cutProfile_word hp, ← ring_cutProfile, traceEdges_eq_zipWith]
    simp only [cutMask, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
    exact he.mem_iff
  cases hword : word p with
  | nil => have hv' := word_valid hp; rw [hword] at hv'; exact hv'.elim
  | cons t v =>
    simp only [hword] at hpro
    obtain ⟨hh,hw⟩ := cutProfile_injective hpro
    exact ⟨p,hp,hl,hword.trans hw,hh⟩

theorem realize_mark (s : Layer) (w : List Layer) (j : ℕ) (hv : valid (s::w))
    (hj : j ∈ rootLevels (s::w)) :
    ∃ p : strip.Walk origin origin, p.IsCycle ∧ p.length = 2 * cost (s::w) ∧
      word p = s::w ∧ bottom p = -(j:ℤ) := by
  let h : ℤ := ((w.length+1 : ℕ) : ℤ) - j
  have hx : origin ∈ ringList w h s := origin_mem_ring s w j hj
  obtain ⟨p, hp, hl, hw, ht⟩ := ring_cycle_roundtrip w h s hv origin hx
  have hlt := bottom_lt_top hp
  have hlen := congrArg List.length hw
  rw [length_word, List.length_cons] at hlen
  unfold span at hlen
  dsimp [h] at ht
  exact ⟨p,hp,hl,hw,by omega⟩

end StripConstruct

namespace StripConstruct

open OMA.S_oeis_a022445 StripWords StripLayers

/-- The encoded word has semiperimeter equal to half the original cycle length. -/
theorem forward_perimeter {a : stripSet} {p : strip.Walk a a} (hp : p.IsCycle) :
    p.length = 2 * cost (word p) := by
  have hv := word_valid hp
  cases hw : word p with
  | nil => rw [hw] at hv; exact False.elim hv
  | cons s w =>
    rw [hw] at hv
    obtain ⟨q, hq, len, pairs, _⟩ := ring_cycle_exists_at w (top p) s hv
      (pt (left s) (top p)) (by simp [ringList])
    have shared (k : ℤ) : cutMask p.edges.toFinset k = cutMask q.edges.toFinset k := by
      ext i
      rw [← cutProfile_word hp i k, hw]
      symm
      simp only [cutMask, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset,
        upEdge, pairs.mem_iff, ← traceEdges_eq_zipWith]
      exact ring_cutProfile w (top p) s i k
    exact (length_eq_of_edgeFinset_eq hp hq (edges_eq_of_masks_eq hp hq shared)).trans len

end StripConstruct

namespace StripCycle

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V} {u v : V}

private theorem tail_edge_subset {w : V} {h : G.Adj u v} {p q : G.Walk v w}
    (hp : s(u,v) ∉ p.edges) (hs : (cons h p).edgeSet ⊆ (cons h q).edgeSet) :
    p.edgeSet ⊆ q.edgeSet := by
  intro e he
  have hmem : e ∈ (cons h q).edgeSet := hs (by simp [he])
  rw [edgeSet_cons, Set.mem_insert_iff] at hmem
  exact hmem.resolve_left (fun heq => hp (heq ▸ he))

private theorem path_eq_of_edge_subset (p : G.Walk u v) :
    ∀ {q : G.Walk u v}, p.IsPath → q.IsPath → p.edgeSet ⊆ q.edgeSet → p = q := by
  induction p with
  | nil =>
    intro q _ hq _
    exact (isPath_iff_nil.mp hq).eq_nil.symm
  | @cons u v w h p ih =>
    intro q hp hq hs
    have hm : s(u,v) ∈ q.edgeSet := hs (by simp)
    cases q with
    | nil => simp at hm
    | @cons _ t _ ht q =>
      have hvt : v = t := by simpa [snd_cons] using hq.eq_snd_of_mem_edges hm
      subst t
      have hp' := (cons_isPath_iff _ _).mp hp
      have hq' := (cons_isPath_iff _ _).mp hq
      have he := ((isTrail_cons _ _).mp hp.isTrail).2
      exact congrArg (cons h) (ih hp'.1 hq'.1 (tail_edge_subset he hs))

private theorem cycle_eq_of_same_snd {p q : G.Walk u u} (hp : p.IsCycle)
    (hq : q.IsCycle) (hs : p.edgeSet ⊆ q.edgeSet) (h : p.snd = q.snd) : p = q := by
  cases p with
  | nil => simp at hp
  | @cons _ v _ hv p =>
    cases q with
    | nil => simp at hq
    | @cons _ w _ hw q =>
      simp only [snd_cons] at h
      subst w
      obtain ⟨hp', he⟩ := (cons_isCycle_iff _ _).mp hp
      have hq' := ((cons_isCycle_iff _ _).mp hq).1
      exact congrArg (cons hv) (path_eq_of_edge_subset p hp' hq' (tail_edge_subset he hs))

/-- Rooted cycles traversing the same edges differ at most by reversal. -/
theorem oriented_cycle_eq_or_reverse {p q : G.Walk u u} (hp : p.IsCycle)
    (hq : q.IsCycle) (hs : p.edgeSet = q.edgeSet) : p = q ∨ p = q.reverse := by
  have hm : s(u,p.snd) ∈ q.edgeSet := hs ▸ p.mk_start_snd_mem_edges hp.not_nil
  have hchoice : p.snd = q.snd ∨ p.snd = q.penultimate := by
    cases q with
    | nil => simp at hq
    | @cons _ w _ hw q =>
      rw [edgeSet_cons, Set.mem_insert_iff] at hm
      rcases hm with he | he
      · left
        simpa [snd_cons, hw.ne] using he
      · right
        rw [penultimate_cons_of_not_nil _ _ (not_nil_of_isCycle_cons hq)]
        exact ((cons_isCycle_iff _ _).mp hq).1.eq_penultimate_of_mem_edges he
  rcases hchoice with h | h
  · exact Or.inl (cycle_eq_of_same_snd hp hq hs.le h)
  · exact Or.inr (cycle_eq_of_same_snd hp hq.reverse (by simpa using hs.le) (by simpa using h))

theorem cycle_ne_reverse {p : G.Walk u u} (hp : p.IsCycle) : p ≠ p.reverse := by
  intro he
  have hs : p.snd = p.penultimate := by simpa using congrArg (fun w : G.Walk u u => w.snd) he
  have hl := hp.three_le_length
  change p.getVert 1 = p.getVert (p.length - 1) at hs
  have hi : 1 = p.length - 1 := hp.getVert_injOn
    (by change 1 ≤ 1 ∧ 1 ≤ p.length; omega)
    (by change 1 ≤ p.length - 1 ∧ p.length - 1 ≤ p.length; omega) hs
  omega

end StripCycle

namespace StripWords

open OMA.S_oeis_a022445

/-- Reverse a positive rooted cycle, keeping the length and the root. -/
def reversePositive {n : ℕ} (p : PositiveCycle n) : PositiveCycle n :=
  ⟨p.val.reverse, by simpa using p.property.1, p.property.2.reverse⟩

/-- A marked edge set with one realization has two oriented realizations.
The representative is chosen separately for each mark. -/
noncomputable def markedCycleEquiv {n : ℕ}
    (edge : Marked n → Set (Sym2 stripSet)) (edge_injective : Function.Injective edge)
    (cover : ∀ p : PositiveCycle n, ∃ m, p.val.edgeSet = edge m)
    (realize : ∀ m, ∃ p : PositiveCycle n, p.val.edgeSet = edge m) :
    Bool × Marked n ≃ PositiveCycle n := by
  classical
  let rep (m : Marked n) : PositiveCycle n := (realize m).choose
  have hrep (m : Marked n) : (rep m).val.edgeSet = edge m := (realize m).choose_spec
  let orient (v : Bool × Marked n) : PositiveCycle n :=
    if v.1 then reversePositive (rep v.2) else rep v.2
  have hside (v : Bool × Marked n) : (orient v).val.edgeSet = edge v.2 := by
    rcases v with ⟨b,m⟩
    cases b <;> simp [orient, reversePositive, hrep]
  refine Equiv.ofBijective orient ⟨?_, ?_⟩
  · rintro ⟨b,m⟩ ⟨c,k⟩ h
    have hmk : m = k :=
      edge_injective ((hside (b,m)).symm.trans
        ((congrArg (fun p : PositiveCycle n => p.val.edgeSet) h).trans (hside (c,k))))
    subst k
    have hd := StripCycle.cycle_ne_reverse (rep m).property.2
    cases b <;> cases c <;> first
      | rfl
      | exact False.elim (hd (congrArg Subtype.val h))
      | exact False.elim (hd (congrArg Subtype.val h).symm)
  · intro p
    obtain ⟨m,hm⟩ := cover p
    have hs := hm.trans (hrep m).symm
    rcases StripCycle.oriented_cycle_eq_or_reverse p.property.2 (rep m).property.2 hs with h | h
    · exact ⟨(false,m), Subtype.ext h.symm⟩
    · exact ⟨(true,m), Subtype.ext h.symm⟩

/-- An equivalent input for the classification is a surjective encoding whose
fibers are exactly the classes of equal undirected edge sets. -/
noncomputable def markedCycleEquivOfEncode {n : ℕ} (mark : PositiveCycle n → Marked n)
    (onto : Function.Surjective mark)
    (same : ∀ p q, mark p = mark q ↔ p.val.edgeSet = q.val.edgeSet) :
    Bool × Marked n ≃ PositiveCycle n := by
  classical
  let rep (m : Marked n) : PositiveCycle n := (onto m).choose
  have hrep (m : Marked n) : mark (rep m) = m := (onto m).choose_spec
  apply markedCycleEquiv (fun m => (rep m).val.edgeSet)
  · intro m k h
    exact (hrep m).symm.trans (((same _ _).mpr h).trans (hrep k))
  · intro p
    exact ⟨mark p, (same _ _).mp (hrep _).symm⟩
  · exact fun m => ⟨rep m, rfl⟩

/-- It suffices to classify equal marks in one direction and to check that
reversing a walk preserves its mark. -/
noncomputable def markedCycleEquivOfReversal {n : ℕ} (mark : PositiveCycle n → Marked n)
    (onto : Function.Surjective mark)
    (classify : ∀ p q, mark p = mark q → p.val.edgeSet = q.val.edgeSet)
    (reversal : ∀ p, mark (reversePositive p) = mark p) :
    Bool × Marked n ≃ PositiveCycle n := by
  apply markedCycleEquivOfEncode mark onto
  intro p q
  refine ⟨classify p q, fun h => ?_⟩
  rcases StripCycle.oriented_cycle_eq_or_reverse p.property.2 q.property.2 h with h | h
  · exact congrArg mark (Subtype.ext h)
  · have hp : p = reversePositive q := Subtype.ext h
    exact (congrArg mark hp).trans (reversal q)

end StripWords

namespace StripLayers

open OMA.S_oeis_a022445

theorem heights_reverse {u v : stripSet} (p : strip.Walk u v) :
    heights p.reverse = heights p := by simp [heights]

theorem bottom_reverse {u v : stripSet} (p : strip.Walk u v) :
    bottom p.reverse = bottom p := by simp [bottom, heights_reverse]

theorem top_reverse {u v : stripSet} (p : strip.Walk u v) :
    top p.reverse = top p := by simp [top, heights_reverse]

theorem word_reverse {u v : stripSet} (p : strip.Walk u v) :
    word p.reverse = word p := by simp [word, span, bottom_reverse, top_reverse]

end StripLayers

namespace StripWords

open OMA.S_oeis_a022445 StripLayers

theorem marked_ext {n : ℕ} {x y : Marked n} (hw : x.1.val = y.1.val)
    (hj : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨⟨w, hw'⟩, ⟨j, hj'⟩⟩
  rcases y with ⟨⟨z, hz'⟩, ⟨k, hk'⟩⟩
  change w = z at hw
  change j = k at hj
  subst z
  subst k
  rfl

/-- The cost identifies the semiperimeter. The two remaining geometric inputs
are edge-set uniqueness and realization of every marked layer word. -/
noncomputable def markedCycleEquivOfGeometry {n : ℕ}
    (length_cost : ∀ p : PositiveCycle n, cost (word p.val) = n)
    (classify : ∀ p q : PositiveCycle n, bottom p.val = bottom q.val →
      word p.val = word q.val → p.val.edgeSet = q.val.edgeSet)
    (realize : ∀ m : Marked n, ∃ p : PositiveCycle n,
      word p.val = m.1.val ∧ (-bottom p.val).toNat = m.2.val) :
    Bool × Marked n ≃ PositiveCycle n := by
  let mark (p : PositiveCycle n) : Marked n :=
    ⟨⟨word p.val, word_valid p.property.2, length_cost p⟩,
      ⟨(-bottom p.val).toNat, origin_mark p.property.2⟩⟩
  apply markedCycleEquivOfReversal mark
  · intro m
    obtain ⟨p, hw, hj⟩ := realize m
    exact ⟨p, marked_ext hw hj⟩
  · intro p q h
    have hj : (-bottom p.val).toNat = (-bottom q.val).toNat :=
      congrArg (fun m : Marked n => m.2.val) h
    have hp := (height_bounds p.val.start_mem_support).1
    have hq := (height_bounds q.val.start_mem_support).1
    change bottom p.val ≤ 0 at hp
    change bottom q.val ≤ 0 at hq
    exact classify p q (by omega) (congrArg (fun m : Marked n => m.1.val) h)
  · intro p
    apply marked_ext
    · exact word_reverse p.val
    · change (-bottom p.val.reverse).toNat = (-bottom p.val).toNat
      rw [bottom_reverse]

/-- The length formula, uniqueness of the edge set, and realization of each
marked word establish the generating function at the official root. -/
theorem gf_of_layer_geometry
    (length_cost : ∀ {p : strip.Walk origin origin}, p.IsCycle →
      p.length = 2 * cost (word p))
    (classify : ∀ {p q : strip.Walk origin origin}, p.IsCycle → q.IsCycle →
      bottom p = bottom q → word p = word q → p.edges.toFinset = q.edges.toFinset)
    (realize : ∀ (s : Layer) (w : List Layer) (j : ℕ), valid (s :: w) →
      j ∈ rootLevels (s :: w) → ∃ p : strip.Walk origin origin,
      p.IsCycle ∧ p.length = 2 * cost (s :: w) ∧ word p = s :: w ∧ bottom p = -(j : ℤ)) :
    type_of% @OMA.S_oeis_a022445.main := by
  have e (n : ℕ) : Bool × Marked n ≃ PositiveCycle n := by
    apply markedCycleEquivOfGeometry
    · intro p
      have h := length_cost p.property.2
      have hl := p.property.1
      omega
    · intro p q hb hw
      have he := classify p.property.2 q.property.2 hb hw
      ext x
      simpa only [SimpleGraph.Walk.mem_edgeSet, List.mem_toFinset] using
        (Finset.ext_iff.mp he x)
    · rintro ⟨⟨l, hv, hc⟩, ⟨j, hj⟩⟩
      cases l with
      | nil => exact False.elim hv
      | cons s w =>
        obtain ⟨p, hp, hl, hw, hb⟩ := realize s w j hv hj
        exact ⟨⟨p, hl.trans (congrArg (2 * ·) hc), hp⟩, hw, by
          change (-bottom p).toNat = j
          simp [hb]⟩
  apply gf_of_geometric_embeddings
  · exact fun n _ => ⟨(e n).symm.toEmbedding⟩
  · exact fun n _ => ⟨(e n).toEmbedding⟩

end StripWords

theorem OMA.solution : type_of% @OMA.S_oeis_a022445.main := by
  apply StripWords.gf_of_layer_geometry
  · exact fun hp => StripConstruct.forward_perimeter hp
  · exact fun hp hq hb hw =>
      StripLayers.edges_eq_of_masks_eq hp hq (StripConstruct.cuts_of_word_eq hp hq hb hw)
  · exact StripConstruct.realize_mark
