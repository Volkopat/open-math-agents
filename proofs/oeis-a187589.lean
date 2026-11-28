import OMAStatements.S_oeis_a187589

/-!
# OEIS A187589

Source: https://oeis.org/A187589 (OEIS Foundation, CC BY-SA 4.0).
Sequence and empirical quadratic: R. H. Hardin.
Generating function and recurrence conjectures: Colin Barker.
The formal statement and grid conventions are from the submission by @jleguina.
Proof: @grp06. The tour equivalence adapts the proof of A187174 by @grp06.
Source for A187174: https://oeis.org/A187174 (OEIS Foundation, CC BY-SA 4.0).
-/

namespace A187589Proof

open OMA.S_oeis_a187589
open Finset
open scoped BigOperators

private abbrev Tail := Fin 4 × Fin 4 × Fin 4 × Fin 4
private abbrev Word := Fin 4 × Tail

private def move (j : Fin 4) : ℤ × ℤ := moves.get (show Fin moves.length from j)

private theorem move_mem (j : Fin 4) : move j ∈ moves := List.get_mem _ _

private theorem move_injective : Function.Injective move := by decide

private noncomputable def moveIndex (d : ℤ × ℤ) (h : d ∈ moves) : Fin 4 :=
  Classical.choose (List.mem_iff_get.mp h)

private theorem moveIndex_spec (d : ℤ × ℤ) (h : d ∈ moves) :
    move (moveIndex d h) = d :=
  Classical.choose_spec (List.mem_iff_get.mp h)

private def offset (w : Word) : Fin 6 → ℤ × ℤ :=
  ![0,
    move w.1,
    move w.1 + move w.2.1,
    move w.1 + move w.2.1 + move w.2.2.1,
    move w.1 + move w.2.1 + move w.2.2.1 + move w.2.2.2.1,
    move w.1 + move w.2.1 + move w.2.2.1 + move w.2.2.2.1 + move w.2.2.2.2]

private def good (w : Word) : Prop := Function.Injective (offset w)

private instance : DecidablePred good := fun w =>
  inferInstanceAs (Decidable (Function.Injective (offset w)))

private abbrev GoodWord := {w : Word // good w}

private def lower (f : Fin 6 → ℤ) : ℤ := min (min (min (min (min (f 0) (f 1)) (f 2)) (f 3)) (f 4)) (f 5)
private def upper (f : Fin 6 → ℤ) : ℤ := max (max (max (max (max (f 0) (f 1)) (f 2)) (f 3)) (f 4)) (f 5)
private def span (f : Fin 6 → ℤ) : ℕ := (upper f - lower f).toNat

private theorem lower_le (f : Fin 6 → ℤ) (i : Fin 6) : lower f ≤ f i := by
  fin_cases i
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

private theorem le_upper (f : Fin 6 → ℤ) (i : Fin 6) : f i ≤ upper f := by
  fin_cases i
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))))
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem span_cast (f : Fin 6 → ℤ) : (span f : ℤ) = upper f - lower f := by
  have h := (lower_le f 0).trans (le_upper f 0)
  exact Int.toNat_of_nonneg (by omega)

private def xCoords (w : Word) (i : Fin 6) : ℤ := (offset w i).1
private def yCoords (w : Word) (i : Fin 6) : ℤ := (offset w i).2
private def width (w : Word) : ℕ := span (xCoords w)
private def height (w : Word) : ℕ := span (yCoords w)

private theorem translatedBounds {n : ℕ} (f : Fin 6 → ℤ)
    (t : Fin (n - span f)) (i : Fin 6) :
    0 ≤ (t.val : ℤ) + f i - lower f ∧ (t.val : ℤ) + f i - lower f < n := by
  have ht := t.isLt
  have hlo := lower_le f i
  have hhi := le_upper f i
  have hs := span_cast f
  omega

private def translatedCoord {n : ℕ} (f : Fin 6 → ℤ)
    (t : Fin (n - span f)) (i : Fin 6) : Fin n :=
  ⟨((t.val : ℤ) + f i - lower f).toNat, by
    have h := translatedBounds f t i
    omega⟩

private theorem translatedCoord_cast {n : ℕ} (f : Fin 6 → ℤ)
    (t : Fin (n - span f)) (i : Fin 6) :
    ((translatedCoord f t i).val : ℤ) = (t.val : ℤ) + f i - lower f :=
  Int.toNat_of_nonneg (translatedBounds f t i).1

private theorem originBounds {n : ℕ} (f : Fin 6 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) :
    0 ≤ b + lower f ∧ (b + lower f).toNat < n - span f := by
  have hlo (i : Fin 6) : -b ≤ f i := by have hi := (h i).1; omega
  have hhi (i : Fin 6) : f i ≤ (n : ℤ) - b - 1 := by have hi := (h i).2; omega
  have hl : -b ≤ lower f := le_min (le_min (le_min (le_min (le_min (hlo 0) (hlo 1)) (hlo 2)) (hlo 3)) (hlo 4)) (hlo 5)
  have hu : upper f ≤ (n : ℤ) - b - 1 :=
    max_le (max_le (max_le (max_le (max_le (hhi 0) (hhi 1)) (hhi 2)) (hhi 3)) (hhi 4)) (hhi 5)
  have hs := span_cast f
  omega

private def origin {n : ℕ} (f : Fin 6 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) : Fin (n - span f) :=
  ⟨(b + lower f).toNat, (originBounds f b h).2⟩

private theorem origin_cast {n : ℕ} (f : Fin 6 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) :
    ((origin f b h).val : ℤ) = b + lower f :=
  Int.toNat_of_nonneg (originBounds f b h).1

private abbrev Placements (n : ℕ) :=
  Σ w : GoodWord, Fin (n - width w.val) × Fin (n - height w.val)

private abbrev Tours (n : ℕ) := {p : Fin 6 → Fin n × Fin n // IsTour n 6 p}

private def draw {n : ℕ} (s : Placements n) (i : Fin 6) : Fin n × Fin n :=
  (translatedCoord (xCoords s.1.val) s.2.1 i, translatedCoord (yCoords s.1.val) s.2.2 i)

private def shift {n : ℕ} (s : Placements n) : ℤ × ℤ :=
  ((s.2.1.val : ℤ) - lower (xCoords s.1.val), (s.2.2.val : ℤ) - lower (yCoords s.1.val))

private theorem draw_coord {n : ℕ} (s : Placements n) (i : Fin 6) :
    toZ (draw s i) = shift s + offset s.1.val i := by
  apply Prod.ext
  · change ((translatedCoord (xCoords s.1.val) s.2.1 i).val : ℤ) =
      (s.2.1.val : ℤ) - lower (xCoords s.1.val) + xCoords s.1.val i
    calc
      _ = (s.2.1.val : ℤ) + xCoords s.1.val i - lower (xCoords s.1.val) :=
        translatedCoord_cast (xCoords s.1.val) s.2.1 i
      _ = _ := by ring
  · change ((translatedCoord (yCoords s.1.val) s.2.2 i).val : ℤ) =
      (s.2.2.val : ℤ) - lower (yCoords s.1.val) + yCoords s.1.val i
    calc
      _ = (s.2.2.val : ℤ) + yCoords s.1.val i - lower (yCoords s.1.val) :=
        translatedCoord_cast (yCoords s.1.val) s.2.2 i
      _ = _ := by ring

private theorem toZ_injective {n : ℕ} : Function.Injective (@toZ n) := by
  intro q r h
  apply Prod.ext
  · apply Fin.ext
    have hx : (q.1.val : ℤ) = r.1.val := congrArg Prod.fst h
    omega
  · apply Fin.ext
    have hy : (q.2.val : ℤ) = r.2.val := congrArg Prod.snd h
    omega

private theorem next_cases (i j : Fin 6) :
    j.val = i.val + 1 →
      (i = 0 ∧ j = 1) ∨
      (i = 1 ∧ j = 2) ∨
      (i = 2 ∧ j = 3) ∨
      (i = 3 ∧ j = 4) ∨
      (i = 4 ∧ j = 5) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem draw_step1 {n : ℕ} (s : Placements n) :
    toZ (draw s 1) - toZ (draw s 0) = move s.1.val.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1)) -
    (shift s + (0)) = move s.1.val.1
  abel

private theorem draw_step2 {n : ℕ} (s : Placements n) :
    toZ (draw s 2) - toZ (draw s 1) = move s.1.val.2.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2.1)) -
    (shift s + (move s.1.val.1)) = move s.1.val.2.1
  abel

private theorem draw_step3 {n : ℕ} (s : Placements n) :
    toZ (draw s 3) - toZ (draw s 2) = move s.1.val.2.2.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2.1 + move s.1.val.2.2.1)) -
    (shift s + (move s.1.val.1 + move s.1.val.2.1)) = move s.1.val.2.2.1
  abel

private theorem draw_step4 {n : ℕ} (s : Placements n) :
    toZ (draw s 4) - toZ (draw s 3) = move s.1.val.2.2.2.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2.1 + move s.1.val.2.2.1 + move s.1.val.2.2.2.1)) -
    (shift s + (move s.1.val.1 + move s.1.val.2.1 + move s.1.val.2.2.1)) = move s.1.val.2.2.2.1
  abel

private theorem draw_step5 {n : ℕ} (s : Placements n) :
    toZ (draw s 5) - toZ (draw s 4) = move s.1.val.2.2.2.2 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2.1 + move s.1.val.2.2.1 + move s.1.val.2.2.2.1 + move s.1.val.2.2.2.2)) -
    (shift s + (move s.1.val.1 + move s.1.val.2.1 + move s.1.val.2.2.1 + move s.1.val.2.2.2.1)) = move s.1.val.2.2.2.2
  abel

private def tourOf {n : ℕ} (s : Placements n) : Tours n := ⟨draw s, by
  constructor
  · intro i j h
    have hz := congrArg toZ h
    rw [draw_coord, draw_coord] at hz
    exact s.1.property (add_left_cancel hz)
  · intro i j h
    rcases next_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [draw_step1]; exact move_mem _
    · rw [draw_step2]; exact move_mem _
    · rw [draw_step3]; exact move_mem _
    · rw [draw_step4]; exact move_mem _
    · rw [draw_step5]; exact move_mem _⟩

private theorem tourOf_injective {n : ℕ} : Function.Injective (@tourOf n) := by
  intro s t h
  have he (i : Fin 6) : toZ (draw s i) = toZ (draw t i) :=
    congrArg (fun p : Tours n => toZ (p.val i)) h
  have h1 : s.1.val.1 = t.1.val.1 := move_injective (by
    rw [← draw_step1 s, ← draw_step1 t, he 0, he 1])
  have h2 : s.1.val.2.1 = t.1.val.2.1 := move_injective (by
    rw [← draw_step2 s, ← draw_step2 t, he 1, he 2])
  have h3 : s.1.val.2.2.1 = t.1.val.2.2.1 := move_injective (by
    rw [← draw_step3 s, ← draw_step3 t, he 2, he 3])
  have h4 : s.1.val.2.2.2.1 = t.1.val.2.2.2.1 := move_injective (by
    rw [← draw_step4 s, ← draw_step4 t, he 3, he 4])
  have h5 : s.1.val.2.2.2.2 = t.1.val.2.2.2.2 := move_injective (by
    rw [← draw_step5 s, ← draw_step5 t, he 4, he 5])
  have hw : s.1 = t.1 :=
    Subtype.ext (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 h5))))
  have hb := he 0
  rw [draw_coord, draw_coord] at hb
  have hs (u : Placements n) : offset u.1.val 0 = 0 := rfl
  simp only [hs, add_zero] at hb
  clear h he h1 h2 h3 h4 h5
  obtain ⟨w, u⟩ := s
  obtain ⟨v, z⟩ := t
  change w = v at hw
  subst v
  have hx := congrArg Prod.fst hb
  have hy := congrArg Prod.snd hb
  change (u.1.val : ℤ) - lower (xCoords w.val) =
    (z.1.val : ℤ) - lower (xCoords w.val) at hx
  change (u.2.val : ℤ) - lower (yCoords w.val) =
    (z.2.val : ℤ) - lower (yCoords w.val) at hy
  have hu : u = z := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  subst z
  rfl

private noncomputable def wordOf {n : ℕ} (p : Tours n) : Word :=
  (moveIndex _ (p.property.2 0 1 rfl),
    moveIndex _ (p.property.2 1 2 rfl),
    moveIndex _ (p.property.2 2 3 rfl),
    moveIndex _ (p.property.2 3 4 rfl),
    moveIndex _ (p.property.2 4 5 rfl))

private theorem wordOf_coord {n : ℕ} (p : Tours n) (i : Fin 6) :
    toZ (p.val i) = toZ (p.val 0) + offset (wordOf p) i := by
  have h1 : toZ (p.val 1) = toZ (p.val 0) + move (wordOf p).1 := by
    change _ = _ + move (moveIndex _ (p.property.2 0 1 rfl))
    rw [moveIndex_spec]
    abel
  have h2 : toZ (p.val 2) = toZ (p.val 1) + move (wordOf p).2.1 := by
    change _ = _ + move (moveIndex _ (p.property.2 1 2 rfl))
    rw [moveIndex_spec]
    abel
  have h3 : toZ (p.val 3) = toZ (p.val 2) + move (wordOf p).2.2.1 := by
    change _ = _ + move (moveIndex _ (p.property.2 2 3 rfl))
    rw [moveIndex_spec]
    abel
  have h4 : toZ (p.val 4) = toZ (p.val 3) + move (wordOf p).2.2.2.1 := by
    change _ = _ + move (moveIndex _ (p.property.2 3 4 rfl))
    rw [moveIndex_spec]
    abel
  have h5 : toZ (p.val 5) = toZ (p.val 4) + move (wordOf p).2.2.2.2 := by
    change _ = _ + move (moveIndex _ (p.property.2 4 5 rfl))
    rw [moveIndex_spec]
    abel
  fin_cases i
  · change toZ (p.val 0) = toZ (p.val 0) + 0
    exact (add_zero _).symm
  · exact h1
  · change toZ (p.val 2) = toZ (p.val 0) +
      (move (wordOf p).1 + move (wordOf p).2.1)
    rw [h2, h1]
    abel
  · change toZ (p.val 3) = toZ (p.val 0) +
      (move (wordOf p).1 + move (wordOf p).2.1 + move (wordOf p).2.2.1)
    rw [h3, h2, h1]
    abel
  · change toZ (p.val 4) = toZ (p.val 0) +
      (move (wordOf p).1 + move (wordOf p).2.1 + move (wordOf p).2.2.1 + move (wordOf p).2.2.2.1)
    rw [h4, h3, h2, h1]
    abel
  · change toZ (p.val 5) = toZ (p.val 0) +
      (move (wordOf p).1 + move (wordOf p).2.1 + move (wordOf p).2.2.1 + move (wordOf p).2.2.2.1 + move (wordOf p).2.2.2.2)
    rw [h5, h4, h3, h2, h1]
    abel

private theorem wordOf_good {n : ℕ} (p : Tours n) : good (wordOf p) := by
  intro i j h
  apply p.property.1
  apply toZ_injective
  rw [wordOf_coord p i, wordOf_coord p j, h]

private theorem coordBounds {n : ℕ} (q : Fin n) : 0 ≤ (q.val : ℤ) ∧ (q.val : ℤ) < n := by
  have h := q.isLt
  omega

private theorem wordOf_xBounds {n : ℕ} (p : Tours n) (i : Fin 6) :
    0 ≤ (toZ (p.val 0)).1 + xCoords (wordOf p) i ∧
      (toZ (p.val 0)).1 + xCoords (wordOf p) i < n := by
  have h : ((p.val i).1.val : ℤ) = (toZ (p.val 0)).1 + xCoords (wordOf p) i :=
    congrArg Prod.fst (wordOf_coord p i)
  rw [← h]
  exact coordBounds (p.val i).1

private theorem wordOf_yBounds {n : ℕ} (p : Tours n) (i : Fin 6) :
    0 ≤ (toZ (p.val 0)).2 + yCoords (wordOf p) i ∧
      (toZ (p.val 0)).2 + yCoords (wordOf p) i < n := by
  have h : ((p.val i).2.val : ℤ) = (toZ (p.val 0)).2 + yCoords (wordOf p) i :=
    congrArg Prod.snd (wordOf_coord p i)
  rw [← h]
  exact coordBounds (p.val i).2

private noncomputable def encode {n : ℕ} (p : Tours n) : Placements n :=
  ⟨⟨wordOf p, wordOf_good p⟩,
    origin (xCoords (wordOf p)) (toZ (p.val 0)).1 (wordOf_xBounds p),
    origin (yCoords (wordOf p)) (toZ (p.val 0)).2 (wordOf_yBounds p)⟩

private theorem shift_encode {n : ℕ} (p : Tours n) : shift (encode p) = toZ (p.val 0) := by
  apply Prod.ext
  · change ((origin (xCoords (wordOf p)) (toZ (p.val 0)).1 (wordOf_xBounds p)).val : ℤ) -
      lower (xCoords (wordOf p)) = (toZ (p.val 0)).1
    rw [origin_cast, add_sub_cancel_right]
  · change ((origin (yCoords (wordOf p)) (toZ (p.val 0)).2 (wordOf_yBounds p)).val : ℤ) -
      lower (yCoords (wordOf p)) = (toZ (p.val 0)).2
    rw [origin_cast, add_sub_cancel_right]

private theorem tourOf_encode {n : ℕ} (p : Tours n) : tourOf (encode p) = p := by
  apply Subtype.ext
  funext i
  apply toZ_injective
  change toZ (draw (encode p) i) = toZ (p.val i)
  rw [draw_coord, shift_encode, wordOf_coord p i]
  rfl

private noncomputable def tourEquiv (n : ℕ) : Tours n ≃ Placements n where
  toFun := encode
  invFun := tourOf
  left_inv := tourOf_encode
  right_inv s := tourOf_injective (tourOf_encode (tourOf s))

private def placementSum (n : ℕ) : ℕ :=
  ∑ w : GoodWord, (n - width w.val) * (n - height w.val)

private theorem count (n : ℕ) : a n = placementSum n := by
  calc
    a n = Fintype.card (Tours n) := (Fintype.card_subtype (IsTour n 6)).symm
    _ = Fintype.card (Placements n) := Fintype.card_congr (tourEquiv n)
    _ = placementSum n := by simp only [placementSum, Fintype.card_sigma,
      Fintype.card_prod, Fintype.card_fin]

/- The finite checks use four groups of 256 words, indexed by the first move. -/
private def chunk (f : Word → ℕ) (j : Fin 4) : ℕ :=
  ∑ t : Tail, if good (j, t) then f (j, t) else 0

private theorem sum_good (f : Word → ℕ) :
    (∑ w : GoodWord, f w.val) = ∑ j : Fin 4, chunk f j := by
  calc
    _ = ∑ w ∈ (univ : Finset Word).filter good, f w :=
      (Finset.sum_subtype (p := good) (univ.filter good) (by simp) f).symm
    _ = ∑ w : Word, if good w then f w else 0 := Finset.sum_filter good f
    _ = _ := Fintype.sum_prod_type (fun w : Word => if good w then f w else 0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem chunkSpan (j : Fin 4) :
    ∀ t : Tail, width (j, t) ≤ 5 ∧ height (j, t) ≤ 5 := by
  fin_cases j <;> decide

private theorem spanBounds (w : GoodWord) : width w.val ≤ 5 ∧ height w.val ≤ 5 :=
  chunkSpan w.val.1 w.val.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem wordCount :
    (∑ w : GoodWord, (fun _ : Word => 1) w.val) = 714 := by
  let f : Word → ℕ := fun _ : Word => 1
  change (∑ w : GoodWord, f w.val) = _
  rw [sum_good f, Fin.sum_univ_four]
  have h0 : chunk f 0 = 184 := by dsimp only [f]; decide
  have h1 : chunk f 1 = 164 := by dsimp only [f]; decide
  have h2 : chunk f 2 = 171 := by dsimp only [f]; decide
  have h3 : chunk f 3 = 195 := by dsimp only [f]; decide
  rw [h0, h1, h2, h3]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem linearMoment :
    (∑ w : GoodWord, (fun w : Word => width w + height w) w.val) = 3888 := by
  let f : Word → ℕ := fun w : Word => width w + height w
  change (∑ w : GoodWord, f w.val) = _
  rw [sum_good f, Fin.sum_univ_four]
  have h0 : chunk f 0 = 971 := by dsimp only [f]; decide
  have h1 : chunk f 1 = 801 := by dsimp only [f]; decide
  have h2 : chunk f 2 = 966 := by dsimp only [f]; decide
  have h3 : chunk f 3 = 1150 := by dsimp only [f]; decide
  rw [h0, h1, h2, h3]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 12000000 in
private theorem constantMoment :
    (∑ w : GoodWord, (fun w : Word => width w * height w) w.val) = 5104 := by
  let f : Word → ℕ := fun w : Word => width w * height w
  change (∑ w : GoodWord, f w.val) = _
  rw [sum_good f, Fin.sum_univ_four]
  have h0 : chunk f 0 = 1191 := by dsimp only [f]; decide
  have h1 : chunk f 1 = 926 := by dsimp only [f]; decide
  have h2 : chunk f 2 = 1347 := by dsimp only [f]; decide
  have h3 : chunk f 3 = 1640 := by dsimp only [f]; decide
  rw [h0, h1, h2, h3]

private theorem quadratic (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 714 * n ^ 2 - 3888 * n + 5104 := by
  have hc : Fintype.card GoodWord = 714 := Fintype.card_eq_sum_ones.trans wordCount
  have hl := linearMoment
  have hk := constantMoment
  have hl' : (∑ w : GoodWord, ((width w.val : ℤ) + height w.val)) = 3888 := by
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ℤ)) hl
  have hk' : (∑ w : GoodWord, (width w.val : ℤ) * height w.val) = 5104 := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ℤ)) hk
  rw [count, placementSum, Nat.cast_sum]
  calc
    _ = ∑ w : GoodWord, ((n : ℤ) ^ 2 -
          ((width w.val : ℤ) + height w.val) * n + (width w.val : ℤ) * height w.val) := by
      apply Finset.sum_congr rfl
      intro w _
      have hw : width w.val ≤ n := (spanBounds w).1.trans (by omega)
      have hh : height w.val ≤ n := (spanBounds w).2.trans (by omega)
      rw [Nat.cast_mul, Nat.cast_sub hw, Nat.cast_sub hh]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
        Finset.sum_const, Finset.card_univ, hc, hl', hk']
      norm_num [nsmul_eq_mul]

private def fits (n : ℕ) (w : Word) : ℕ :=
  (n - width w) * (n - height w)

private theorem count_chunks (n : ℕ) : a n = ∑ j : Fin 4, chunk (fits n) j :=
  (count n).trans (sum_good (fits n))

private def initialValues : Fin 5 → ℕ := ![0, 0, 0, 104, 1069]

private def initialChunk (n : Fin 5) (j : Fin 4) : ℕ :=
  (![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
    ![29, 43, 22, 10], ![283, 350, 239, 197]] : Fin 5 → Fin 4 → ℕ) n j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 24000000 in
private theorem initialChunk_eq (n : Fin 5) (j : Fin 4) :
    chunk (fits n.val) j = initialChunk n j := by
  fin_cases n <;> fin_cases j <;> decide

private theorem initial (n : Fin 5) : a n.val = initialValues n := by
  rw [count_chunks]
  simp only [initialChunk_eq, Fin.sum_univ_four]
  fin_cases n <;> decide

private theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [quadratic n (by omega), quadratic (n - 1) (by omega),
    quadratic (n - 2) (by omega), quadratic (n - 3) (by omega),
    Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n)]
  ring

private theorem series_of_counts (b : ℕ → ℤ)
    (h0 : b 0 = 0) (h1 : b 1 = 0) (h2 : b 2 = 0) (h3 : b 3 = 104)
    (h4 : b 4 = 1069) (h5 : b 5 = 3514) (h6 : b 6 = 7480) (h7 : b 7 = 12874)
    (step : ∀ n : ℕ, 7 < n → b n = 3 * b (n - 1) - 3 * b (n - 2) + b (n - 3)) :
    PowerSeries.mk b * (1 - PowerSeries.X) ^ 3 =
      PowerSeries.X ^ 3 *
        (104 + 757 * PowerSeries.X + 619 * PowerSeries.X ^ 2 +
          41 * PowerSeries.X ^ 3 - 93 * PowerSeries.X ^ 4) := by
  let X : PowerSeries ℤ := PowerSeries.X
  let C : ℤ →+* PowerSeries ℤ := PowerSeries.C
  let p : PowerSeries ℤ := PowerSeries.mk b
  have left : p * (1 - X) ^ 3 =
      p - C 3 * (p * X ^ 1) + C 3 * (p * X ^ 2) - p * X ^ 3 := by
    dsimp only [C]
    simp only [map_ofNat]
    ring
  have right : X ^ 3 * (104 + 757 * X + 619 * X ^ 2 + 41 * X ^ 3 - 93 * X ^ 4) =
      C 104 * X ^ 3 + C 757 * X ^ 4 + C 619 * X ^ 5 + C 41 * X ^ 6 - C 93 * X ^ 7 := by
    dsimp only [C]
    simp only [map_ofNat]
    ring
  change p * (1 - X) ^ 3 = _
  rw [left, right]
  apply PowerSeries.ext
  intro d
  dsimp only [p, C, X]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  by_cases hd : d ≤ 7
  · interval_cases d <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7]
  · have h1 : 1 ≤ d := by omega
    have h2 : 2 ≤ d := by omega
    have h3 : 3 ≤ d := by omega
    have h4 : d ≠ 4 := by omega
    have h5 : d ≠ 5 := by omega
    have h6 : d ≠ 6 := by omega
    have h7 : d ≠ 7 := by omega
    have h3' : d ≠ 3 := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_neg h3', if_neg h4,
      if_neg h5, if_neg h6, if_neg h7, add_zero, sub_zero]
    rw [step d (by omega)]
    ring

private theorem generatingFunction :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      PowerSeries.X ^ 3 *
        (104 + 757 * PowerSeries.X + 619 * PowerSeries.X ^ 2 +
          41 * PowerSeries.X ^ 3 - 93 * PowerSeries.X ^ 4) := by
  refine series_of_counts (fun n => (a n : ℤ)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ recurrence
  · exact congrArg Int.ofNat (show a 0 = 0 from initial 0)
  · exact congrArg Int.ofNat (show a 1 = 0 from initial 1)
  · exact congrArg Int.ofNat (show a 2 = 0 from initial 2)
  · exact congrArg Int.ofNat (show a 3 = 104 from initial 3)
  · exact congrArg Int.ofNat (show a 4 = 1069 from initial 4)
  · change (a 5 : ℤ) = 3514
    rw [quadratic 5 (by decide)] <;> decide
  · change (a 6 : ℤ) = 7480
    rw [quadratic 6 (by decide)] <;> decide
  · change (a 7 : ℤ) = 12874
    rw [quadratic 7 (by decide)] <;> decide

end A187589Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a187589.main :=
  ⟨A187589Proof.quadratic, A187589Proof.generatingFunction, A187589Proof.recurrence⟩
