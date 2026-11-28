import OMAStatements.S_oeis_a187859

/-!
# OEIS A187859

Source: https://oeis.org/A187859 (OEIS Foundation, CC BY-SA 4.0).
Sequence and empirical quadratic: R. H. Hardin.
The generating function and recurrence were conjectured by Colin Barker.
Formal statement: @jleguina. The placement equivalence and coefficient argument
adapt @grp06's A187299 proof (https://github.com/lefttosolve2/open-math-agents/pull/23828),
which in turn adapts @grp06's A187174 proof.
-/

namespace A187859Proof

open OMA.S_oeis_a187859
open Finset
open scoped BigOperators

private abbrev Word := Fin 8 × Fin 8 × Fin 8

private def move (j : Fin 8) : ℤ × ℤ := moves.get (show Fin moves.length from j)

private theorem move_mem (j : Fin 8) : move j ∈ moves := List.get_mem _ _

private theorem move_injective : Function.Injective move := by decide

private noncomputable def moveIndex (d : ℤ × ℤ) (h : d ∈ moves) : Fin 8 :=
  Classical.choose (List.mem_iff_get.mp h)

private theorem moveIndex_spec (d : ℤ × ℤ) (h : d ∈ moves) :
    move (moveIndex d h) = d :=
  Classical.choose_spec (List.mem_iff_get.mp h)

private def offset (w : Word) : Fin 4 → ℤ × ℤ :=
  ![0, move w.1, move w.1 + move w.2.1, move w.1 + move w.2.1 + move w.2.2]

private def good (w : Word) : Prop := Function.Injective (offset w)

private instance : DecidablePred good := fun w =>
  inferInstanceAs (Decidable (Function.Injective (offset w)))

private abbrev GoodWord := {w : Word // good w}

private def lower (f : Fin 4 → ℤ) : ℤ := min (min (min (f 0) (f 1)) (f 2)) (f 3)
private def upper (f : Fin 4 → ℤ) : ℤ := max (max (max (f 0) (f 1)) (f 2)) (f 3)
private def span (f : Fin 4 → ℤ) : ℕ := (upper f - lower f).toNat

private theorem lower_le (f : Fin 4 → ℤ) (i : Fin 4) : lower f ≤ f i := by
  fin_cases i
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  · exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

private theorem le_upper (f : Fin 4 → ℤ) (i : Fin 4) : f i ≤ upper f := by
  fin_cases i
  · exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem span_cast (f : Fin 4 → ℤ) : (span f : ℤ) = upper f - lower f := by
  have h := (lower_le f 0).trans (le_upper f 0)
  exact Int.toNat_of_nonneg (by omega)

private def xCoords (w : Word) (i : Fin 4) : ℤ := (offset w i).1
private def yCoords (w : Word) (i : Fin 4) : ℤ := (offset w i).2
private def width (w : Word) : ℕ := span (xCoords w)
private def height (w : Word) : ℕ := span (yCoords w)

private theorem translatedBounds {n : ℕ} (f : Fin 4 → ℤ)
    (t : Fin (n - span f)) (i : Fin 4) :
    0 ≤ (t.val : ℤ) + f i - lower f ∧ (t.val : ℤ) + f i - lower f < n := by
  have ht := t.isLt
  have hlo := lower_le f i
  have hhi := le_upper f i
  have hs := span_cast f
  omega

private def translatedCoord {n : ℕ} (f : Fin 4 → ℤ)
    (t : Fin (n - span f)) (i : Fin 4) : Fin n :=
  ⟨((t.val : ℤ) + f i - lower f).toNat, by
    have h := translatedBounds f t i
    omega⟩

private theorem translatedCoord_cast {n : ℕ} (f : Fin 4 → ℤ)
    (t : Fin (n - span f)) (i : Fin 4) :
    ((translatedCoord f t i).val : ℤ) = (t.val : ℤ) + f i - lower f :=
  Int.toNat_of_nonneg (translatedBounds f t i).1

private theorem originBounds {n : ℕ} (f : Fin 4 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) :
    0 ≤ b + lower f ∧ (b + lower f).toNat < n - span f := by
  have hlo (i : Fin 4) : -b ≤ f i := by have hi := (h i).1; omega
  have hhi (i : Fin 4) : f i ≤ (n : ℤ) - b - 1 := by have hi := (h i).2; omega
  have hl : -b ≤ lower f := le_min (le_min (le_min (hlo 0) (hlo 1)) (hlo 2)) (hlo 3)
  have hu : upper f ≤ (n : ℤ) - b - 1 :=
    max_le (max_le (max_le (hhi 0) (hhi 1)) (hhi 2)) (hhi 3)
  have hs := span_cast f
  omega

private def origin {n : ℕ} (f : Fin 4 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) : Fin (n - span f) :=
  ⟨(b + lower f).toNat, (originBounds f b h).2⟩

private theorem origin_cast {n : ℕ} (f : Fin 4 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) :
    ((origin f b h).val : ℤ) = b + lower f :=
  Int.toNat_of_nonneg (originBounds f b h).1

private abbrev Placements (n : ℕ) :=
  Σ w : GoodWord, Fin (n - width w.val) × Fin (n - height w.val)

private abbrev Tours (n : ℕ) := {p : Fin 4 → Fin n × Fin n // IsTour n 4 p}

private def draw {n : ℕ} (s : Placements n) (i : Fin 4) : Fin n × Fin n :=
  (translatedCoord (xCoords s.1.val) s.2.1 i, translatedCoord (yCoords s.1.val) s.2.2 i)

private def shift {n : ℕ} (s : Placements n) : ℤ × ℤ :=
  ((s.2.1.val : ℤ) - lower (xCoords s.1.val), (s.2.2.val : ℤ) - lower (yCoords s.1.val))

private theorem draw_coord {n : ℕ} (s : Placements n) (i : Fin 4) :
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

private theorem next_cases (i j : Fin 4) :
    j.val = i.val + 1 →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 3) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem draw_step₁ {n : ℕ} (s : Placements n) :
    toZ (draw s 1) - toZ (draw s 0) = move s.1.val.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + move s.1.val.1) - (shift s + 0) = move s.1.val.1
  abel

private theorem draw_step₂ {n : ℕ} (s : Placements n) :
    toZ (draw s 2) - toZ (draw s 1) = move s.1.val.2.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2.1)) -
    (shift s + move s.1.val.1) = move s.1.val.2.1
  abel

private theorem draw_step₃ {n : ℕ} (s : Placements n) :
    toZ (draw s 3) - toZ (draw s 2) = move s.1.val.2.2 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2.1 + move s.1.val.2.2)) -
    (shift s + (move s.1.val.1 + move s.1.val.2.1)) = move s.1.val.2.2
  abel

private def tourOf {n : ℕ} (s : Placements n) : Tours n := ⟨draw s, by
  constructor
  · intro i j h
    have hz := congrArg toZ h
    rw [draw_coord, draw_coord] at hz
    exact s.1.property (add_left_cancel hz)
  · intro i j h
    rcases next_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [draw_step₁]; exact move_mem _
    · rw [draw_step₂]; exact move_mem _
    · rw [draw_step₃]; exact move_mem _⟩

private theorem tourOf_injective {n : ℕ} : Function.Injective (@tourOf n) := by
  intro s t h
  have he (i : Fin 4) : toZ (draw s i) = toZ (draw t i) :=
    congrArg (fun p : Tours n => toZ (p.val i)) h
  have h₁ : s.1.val.1 = t.1.val.1 := move_injective (by
    rw [← draw_step₁ s, ← draw_step₁ t, he 0, he 1])
  have h₂ : s.1.val.2.1 = t.1.val.2.1 := move_injective (by
    rw [← draw_step₂ s, ← draw_step₂ t, he 1, he 2])
  have h₃ : s.1.val.2.2 = t.1.val.2.2 := move_injective (by
    rw [← draw_step₃ s, ← draw_step₃ t, he 2, he 3])
  have hw : s.1 = t.1 := Subtype.ext (Prod.ext h₁ (Prod.ext h₂ h₃))
  have hb := he 0
  rw [draw_coord, draw_coord] at hb
  have hs (u : Placements n) : offset u.1.val 0 = 0 := rfl
  simp only [hs, add_zero] at hb
  clear h he h₁ h₂ h₃
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
  (moveIndex _ (p.property.2 0 1 rfl), moveIndex _ (p.property.2 1 2 rfl),
    moveIndex _ (p.property.2 2 3 rfl))

private theorem wordOf_coord {n : ℕ} (p : Tours n) (i : Fin 4) :
    toZ (p.val i) = toZ (p.val 0) + offset (wordOf p) i := by
  have h₁ : toZ (p.val 1) = toZ (p.val 0) + move (wordOf p).1 := by
    change _ = _ + move (moveIndex _ (p.property.2 0 1 rfl))
    rw [moveIndex_spec]
    abel
  have h₂ : toZ (p.val 2) = toZ (p.val 1) + move (wordOf p).2.1 := by
    change _ = _ + move (moveIndex _ (p.property.2 1 2 rfl))
    rw [moveIndex_spec]
    abel
  have h₃ : toZ (p.val 3) = toZ (p.val 2) + move (wordOf p).2.2 := by
    change _ = _ + move (moveIndex _ (p.property.2 2 3 rfl))
    rw [moveIndex_spec]
    abel
  fin_cases i
  · change toZ (p.val 0) = toZ (p.val 0) + 0
    exact (add_zero _).symm
  · exact h₁
  · change toZ (p.val 2) = toZ (p.val 0) + (move (wordOf p).1 + move (wordOf p).2.1)
    rw [h₂, h₁]
    abel
  · change toZ (p.val 3) = toZ (p.val 0) +
      (move (wordOf p).1 + move (wordOf p).2.1 + move (wordOf p).2.2)
    rw [h₃, h₂, h₁]
    abel

private theorem wordOf_good {n : ℕ} (p : Tours n) : good (wordOf p) := by
  intro i j h
  apply p.property.1
  apply toZ_injective
  rw [wordOf_coord p i, wordOf_coord p j, h]

private theorem coordBounds {n : ℕ} (q : Fin n) : 0 ≤ (q.val : ℤ) ∧ (q.val : ℤ) < n := by
  have h := q.isLt
  omega

private theorem wordOf_xBounds {n : ℕ} (p : Tours n) (i : Fin 4) :
    0 ≤ (toZ (p.val 0)).1 + xCoords (wordOf p) i ∧
      (toZ (p.val 0)).1 + xCoords (wordOf p) i < n := by
  have h : ((p.val i).1.val : ℤ) = (toZ (p.val 0)).1 + xCoords (wordOf p) i :=
    congrArg Prod.fst (wordOf_coord p i)
  rw [← h]
  exact coordBounds (p.val i).1

private theorem wordOf_yBounds {n : ℕ} (p : Tours n) (i : Fin 4) :
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
    a n = Fintype.card (Tours n) := (Fintype.card_subtype (IsTour n 4)).symm
    _ = Fintype.card (Placements n) := Fintype.card_congr (tourEquiv n)
    _ = placementSum n := by simp only [placementSum, Fintype.card_sigma,
      Fintype.card_prod, Fintype.card_fin]

/- The only finite computation enumerates triples of move indices. -/
set_option maxRecDepth 40000 in
set_option maxHeartbeats 48000000 in
private theorem spanBounds : ∀ w : GoodWord, width w.val ≤ 6 ∧ height w.val ≤ 6 := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 48000000 in
private theorem moments :
    Fintype.card GoodWord = 497 ∧
    (∑ w : GoodWord, (width w.val + height w.val)) = 2652 ∧
    (∑ w : GoodWord, width w.val * height w.val) = 3448 := by
  decide

private theorem quadratic (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 497 * n ^ 2 - 2652 * n + 3448 := by
  obtain ⟨hc, hl, hk⟩ := moments
  have hl' : (∑ w : GoodWord, ((width w.val : ℤ) + height w.val)) = 2652 := by
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ℤ)) hl
  have hk' : (∑ w : GoodWord, (width w.val : ℤ) * height w.val) = 3448 := by
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

private def initialValues : Fin 9 → ℕ := ![0, 0, 0, 216, 968, 2754, 5428, 9237, 14040]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 48000000 in
private theorem initialSum (n : Fin 9) : placementSum n.val = initialValues n := by
  fin_cases n <;> decide

private theorem initial (n : Fin 9) : a n.val = initialValues n :=
  (count n.val).trans (initialSum n)

private theorem generatingFunction :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 3 =
      PowerSeries.X ^ 3 * (216 + 320 * PowerSeries.X + 498 * PowerSeries.X ^ 2 - 146 * PowerSeries.X ^ 3 + 247 * PowerSeries.X ^ 4 - 141 * PowerSeries.X ^ 5) := by
  let X : PowerSeries ℤ := PowerSeries.X
  let C : ℤ →+* PowerSeries ℤ := PowerSeries.C
  let p : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have left : p * (1 - X) ^ 3 =
      p - C 3 * (p * X ^ 1) + C 3 * (p * X ^ 2) - p * X ^ 3 := by
    dsimp only [C]
    simp only [map_ofNat]
    ring
  have right : X ^ 3 * (216 + 320 * X + 498 * X ^ 2 - 146 * X ^ 3 + 247 * X ^ 4 - 141 * X ^ 5) =
      C 216 * X ^ 3 + C 320 * X ^ 4 + C 498 * X ^ 5 - C 146 * X ^ 6 + C 247 * X ^ 7 - C 141 * X ^ 8 := by
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
  by_cases hd : d ≤ 8
  · have h0 : a 0 = 0 := initial 0
    have h1 : a 1 = 0 := initial 1
    have h2 : a 2 = 0 := initial 2
    have h3 : a 3 = 216 := initial 3
    have h4 : a 4 = 968 := initial 4
    have h5 : a 5 = 2754 := initial 5
    have h6 : a 6 = 5428 := initial 6
    have h7 : a 7 = 9237 := initial 7
    have h8 : a 8 = 14040 := initial 8
    interval_cases d <;> norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  · have h1 : 1 ≤ d := by omega
    have h2 : 2 ≤ d := by omega
    have h3 : 3 ≤ d := by omega
    have h4 : d ≠ 4 := by omega
    have h5 : d ≠ 5 := by omega
    have h6 : d ≠ 6 := by omega
    have h7 : d ≠ 7 := by omega
    have h8 : d ≠ 8 := by omega
    have h3ne : d ≠ 3 := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_neg h3ne, if_neg h4, if_neg h5,
      if_neg h6, if_neg h7, if_neg h8, add_zero, sub_zero]
    rw [quadratic d (by omega), quadratic (d - 1) (by omega),
      quadratic (d - 2) (by omega), quadratic (d - 3) (by omega),
      Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    ring

private theorem recurrence (n : ℕ) (hn : 8 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rw [quadratic n (by omega), quadratic (n - 1) (by omega),
    quadratic (n - 2) (by omega), quadratic (n - 3) (by omega),
    Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)]
  ring

end A187859Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a187859.main :=
  ⟨A187859Proof.quadratic, A187859Proof.generatingFunction, A187859Proof.recurrence⟩
