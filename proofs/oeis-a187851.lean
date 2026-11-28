import OMAStatements.S_oeis_a187851

/-!
# OEIS A187851

Source: https://oeis.org/A187851 (OEIS Foundation, CC BY-SA 4.0).
Sequence and empirical quadratic: R. H. Hardin.
Generating function and recurrence conjectures: Colin Barker.
The formal statement and grid conventions are from the submission by @jleguina.
Proof: @grp06, using the tour-to-placement equivalence from the @grp06 proof of
OEIS A187174 (https://oeis.org/A187174).
-/

namespace A187851Proof

open OMA.S_oeis_a187851
open Finset
open scoped BigOperators

private abbrev Word := Fin 16 × Fin 16

private def move (j : Fin 16) : ℤ × ℤ := moves.get (show Fin moves.length from j)

private theorem move_mem (j : Fin 16) : move j ∈ moves := List.get_mem _ _

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem move_injective : Function.Injective move := by decide

private noncomputable def moveIndex (d : ℤ × ℤ) (h : d ∈ moves) : Fin 16 :=
  Classical.choose (List.mem_iff_get.mp h)

private theorem moveIndex_spec (d : ℤ × ℤ) (h : d ∈ moves) :
    move (moveIndex d h) = d :=
  Classical.choose_spec (List.mem_iff_get.mp h)

private def offset (w : Word) : Fin 3 → ℤ × ℤ :=
  ![0, move w.1, move w.1 + move w.2]

private def good (w : Word) : Prop := Function.Injective (offset w)

private instance : DecidablePred good := fun w =>
  inferInstanceAs (Decidable (Function.Injective (offset w)))

private abbrev GoodWord := {w : Word // good w}

private def lower (f : Fin 3 → ℤ) : ℤ := min (min (f 0) (f 1)) (f 2)
private def upper (f : Fin 3 → ℤ) : ℤ := max (max (f 0) (f 1)) (f 2)
private def span (f : Fin 3 → ℤ) : ℕ := (upper f - lower f).toNat

private theorem lower_le (f : Fin 3 → ℤ) (i : Fin 3) : lower f ≤ f i := by
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

private theorem le_upper (f : Fin 3 → ℤ) (i : Fin 3) : f i ≤ upper f := by
  fin_cases i
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact le_max_right _ _

private theorem span_cast (f : Fin 3 → ℤ) : (span f : ℤ) = upper f - lower f := by
  have h := (lower_le f 0).trans (le_upper f 0)
  exact Int.toNat_of_nonneg (by omega)

private def xCoords (w : Word) (i : Fin 3) : ℤ := (offset w i).1
private def yCoords (w : Word) (i : Fin 3) : ℤ := (offset w i).2
private def width (w : Word) : ℕ := span (xCoords w)
private def height (w : Word) : ℕ := span (yCoords w)

private theorem translatedBounds {n : ℕ} (f : Fin 3 → ℤ)
    (t : Fin (n - span f)) (i : Fin 3) :
    0 ≤ (t.val : ℤ) + f i - lower f ∧ (t.val : ℤ) + f i - lower f < n := by
  have ht := t.isLt
  have hlo := lower_le f i
  have hhi := le_upper f i
  have hs := span_cast f
  omega

private def translatedCoord {n : ℕ} (f : Fin 3 → ℤ)
    (t : Fin (n - span f)) (i : Fin 3) : Fin n :=
  ⟨((t.val : ℤ) + f i - lower f).toNat, by
    have h := translatedBounds f t i
    omega⟩

private theorem translatedCoord_cast {n : ℕ} (f : Fin 3 → ℤ)
    (t : Fin (n - span f)) (i : Fin 3) :
    ((translatedCoord f t i).val : ℤ) = (t.val : ℤ) + f i - lower f :=
  Int.toNat_of_nonneg (translatedBounds f t i).1

private theorem originBounds {n : ℕ} (f : Fin 3 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) :
    0 ≤ b + lower f ∧ (b + lower f).toNat < n - span f := by
  have hlo (i : Fin 3) : -b ≤ f i := by have hi := (h i).1; omega
  have hhi (i : Fin 3) : f i ≤ (n : ℤ) - b - 1 := by have hi := (h i).2; omega
  have hl : -b ≤ lower f := le_min (le_min (hlo 0) (hlo 1)) (hlo 2)
  have hu : upper f ≤ (n : ℤ) - b - 1 :=
    max_le (max_le (hhi 0) (hhi 1)) (hhi 2)
  have hs := span_cast f
  omega

private def origin {n : ℕ} (f : Fin 3 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) : Fin (n - span f) :=
  ⟨(b + lower f).toNat, (originBounds f b h).2⟩

private theorem origin_cast {n : ℕ} (f : Fin 3 → ℤ) (b : ℤ)
    (h : ∀ i, 0 ≤ b + f i ∧ b + f i < n) :
    ((origin f b h).val : ℤ) = b + lower f :=
  Int.toNat_of_nonneg (originBounds f b h).1

private abbrev Placements (n : ℕ) :=
  Σ w : GoodWord, Fin (n - width w.val) × Fin (n - height w.val)

private abbrev Tours (n : ℕ) := {p : Fin 3 → Fin n × Fin n // IsTour n 3 p}

private def draw {n : ℕ} (s : Placements n) (i : Fin 3) : Fin n × Fin n :=
  (translatedCoord (xCoords s.1.val) s.2.1 i, translatedCoord (yCoords s.1.val) s.2.2 i)

private def shift {n : ℕ} (s : Placements n) : ℤ × ℤ :=
  ((s.2.1.val : ℤ) - lower (xCoords s.1.val), (s.2.2.val : ℤ) - lower (yCoords s.1.val))

private theorem draw_coord {n : ℕ} (s : Placements n) (i : Fin 3) :
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

private theorem next_cases (i j : Fin 3) :
    j.val = i.val + 1 →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  fin_cases i <;> fin_cases j <;> decide

private theorem draw_step₁ {n : ℕ} (s : Placements n) :
    toZ (draw s 1) - toZ (draw s 0) = move s.1.val.1 := by
  rw [draw_coord, draw_coord]
  change (shift s + move s.1.val.1) - (shift s + 0) = move s.1.val.1
  abel

private theorem draw_step₂ {n : ℕ} (s : Placements n) :
    toZ (draw s 2) - toZ (draw s 1) = move s.1.val.2 := by
  rw [draw_coord, draw_coord]
  change (shift s + (move s.1.val.1 + move s.1.val.2)) -
    (shift s + move s.1.val.1) = move s.1.val.2
  abel

private def tourOf {n : ℕ} (s : Placements n) : Tours n := ⟨draw s, by
  constructor
  · intro i j h
    have hz := congrArg toZ h
    rw [draw_coord, draw_coord] at hz
    exact s.1.property (add_left_cancel hz)
  · intro i j h
    rcases next_cases i j h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [draw_step₁]; exact move_mem _
    · rw [draw_step₂]; exact move_mem _⟩

private theorem tourOf_injective {n : ℕ} : Function.Injective (@tourOf n) := by
  intro s t h
  have he (i : Fin 3) : toZ (draw s i) = toZ (draw t i) :=
    congrArg (fun p : Tours n => toZ (p.val i)) h
  have h₁ : s.1.val.1 = t.1.val.1 := move_injective (by
    rw [← draw_step₁ s, ← draw_step₁ t, he 0, he 1])
  have h₂ : s.1.val.2 = t.1.val.2 := move_injective (by
    rw [← draw_step₂ s, ← draw_step₂ t, he 1, he 2])
  have hw : s.1 = t.1 := Subtype.ext (Prod.ext h₁ h₂)
  have hb := he 0
  rw [draw_coord, draw_coord] at hb
  have hs (u : Placements n) : offset u.1.val 0 = 0 := rfl
  simp only [hs, add_zero] at hb
  clear h he h₁ h₂
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
  (moveIndex _ (p.property.2 0 1 rfl), moveIndex _ (p.property.2 1 2 rfl))

private theorem wordOf_coord {n : ℕ} (p : Tours n) (i : Fin 3) :
    toZ (p.val i) = toZ (p.val 0) + offset (wordOf p) i := by
  have h₁ : toZ (p.val 1) = toZ (p.val 0) + move (wordOf p).1 := by
    change _ = _ + move (moveIndex _ (p.property.2 0 1 rfl))
    rw [moveIndex_spec]
    abel
  have h₂ : toZ (p.val 2) = toZ (p.val 1) + move (wordOf p).2 := by
    change _ = _ + move (moveIndex _ (p.property.2 1 2 rfl))
    rw [moveIndex_spec]
    abel
  fin_cases i
  · change toZ (p.val 0) = toZ (p.val 0) + 0
    exact (add_zero _).symm
  · exact h₁
  · change toZ (p.val 2) = toZ (p.val 0) + (move (wordOf p).1 + move (wordOf p).2)
    rw [h₂, h₁]
    abel

private theorem wordOf_good {n : ℕ} (p : Tours n) : good (wordOf p) := by
  intro i j h
  apply p.property.1
  apply toZ_injective
  rw [wordOf_coord p i, wordOf_coord p j, h]

private theorem coordBounds {n : ℕ} (q : Fin n) : 0 ≤ (q.val : ℤ) ∧ (q.val : ℤ) < n := by
  have h := q.isLt
  omega

private theorem wordOf_xBounds {n : ℕ} (p : Tours n) (i : Fin 3) :
    0 ≤ (toZ (p.val 0)).1 + xCoords (wordOf p) i ∧
      (toZ (p.val 0)).1 + xCoords (wordOf p) i < n := by
  have h : ((p.val i).1.val : ℤ) = (toZ (p.val 0)).1 + xCoords (wordOf p) i :=
    congrArg Prod.fst (wordOf_coord p i)
  rw [← h]
  exact coordBounds (p.val i).1

private theorem wordOf_yBounds {n : ℕ} (p : Tours n) (i : Fin 3) :
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
    a n = Fintype.card (Tours n) := (Fintype.card_subtype (IsTour n 3)).symm
    _ = Fintype.card (Placements n) := Fintype.card_congr (tourEquiv n)
    _ = placementSum n := by simp only [placementSum, Fintype.card_sigma,
      Fintype.card_prod, Fintype.card_fin]

/- The only finite computation enumerates pairs of move indices. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 24000000 in
private theorem spanBounds : ∀ w : GoodWord, width w.val ≤ 4 ∧ height w.val ≤ 4 := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 24000000 in
private theorem moments :
    Fintype.card GoodWord = 240 ∧
    (∑ w : GoodWord, (width w.val + height w.val)) = 904 ∧
    (∑ w : GoodWord, width w.val * height w.val) = 832 := by
  decide

private theorem quadratic (n : ℕ) (hn : 3 < n) :
    (a n : ℤ) = 240 * n ^ 2 - 904 * n + 832 := by
  obtain ⟨hc, hl, hk⟩ := moments
  have hl' : (∑ w : GoodWord, ((width w.val : ℤ) + height w.val)) = 904 := by
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_ofNat] using congrArg (fun k : ℕ => (k : ℤ)) hl
  have hk' : (∑ w : GoodWord, (width w.val : ℤ) * height w.val) = 832 := by
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

private def initialValues : Fin 7 → ℕ := ![0, 0, 24, 304, 1056, 2312, 4048]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 48000000 in
private theorem initialSum (n : Fin 7) : placementSum n.val = initialValues n := by
  fin_cases n <;> decide

private theorem initial (n : Fin 7) : a n.val = initialValues n :=
  (count n.val).trans (initialSum n)

private noncomputable abbrev X : PowerSeries ℤ := PowerSeries.X
private noncomputable abbrev C : ℤ →+* PowerSeries ℤ := PowerSeries.C
private abbrev p : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))

private noncomputable abbrev numerator : PowerSeries ℤ :=
  8 * X ^ 2 * (3 + 29 * X + 27 * X ^ 2 + 4 * X ^ 3 - 3 * X ^ 4)

private theorem product_coeff (d : ℕ) :
    PowerSeries.coeff d (p * (1 - X) ^ 3) =
      (a d : ℤ) - 3 * (if 1 ≤ d then (a (d - 1) : ℤ) else 0) +
        3 * (if 2 ≤ d then (a (d - 2) : ℤ) else 0) -
        (if 3 ≤ d then (a (d - 3) : ℤ) else 0) := by
  have h : p * (1 - X) ^ 3 =
      p - C 3 * (p * X ^ 1) + C 3 * (p * X ^ 2) - p * X ^ 3 := by
    dsimp only [C]
    simp only [map_ofNat]
    ring
  rw [h]
  dsimp only [p, C, X]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

private theorem numerator_coeff (d : ℕ) :
    PowerSeries.coeff d numerator =
      (if d = 2 then (24 : ℤ) else 0) + (if d = 3 then 232 else 0) +
        (if d = 4 then 216 else 0) + (if d = 5 then 32 else 0) -
        (if d = 6 then 24 else 0) := by
  have h : numerator =
      C 24 * X ^ 2 + C 232 * X ^ 3 + C 216 * X ^ 4 + C 32 * X ^ 5 - C 24 * X ^ 6 := by
    dsimp only [numerator, C]
    simp only [map_ofNat]
    ring
  rw [h]
  dsimp only [C, X]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul_X_pow]

private theorem coefficient_identity (d : ℕ) :
    PowerSeries.coeff d (p * (1 - X) ^ 3) = PowerSeries.coeff d numerator := by
  rw [product_coeff, numerator_coeff]
  by_cases hd : d ≤ 6
  · have h0 : a 0 = 0 := initial 0
    have h1 : a 1 = 0 := initial 1
    have h2 : a 2 = 24 := initial 2
    have h3 : a 3 = 304 := initial 3
    have h4 : a 4 = 1056 := initial 4
    have h5 : a 5 = 2312 := initial 5
    have h6 : a 6 = 4048 := initial 6
    interval_cases d <;> norm_num [h0, h1, h2, h3, h4, h5, h6]
  · have h1 : 1 ≤ d := by omega
    have h2 : 2 ≤ d := by omega
    have h3 : 3 ≤ d := by omega
    have hn2 : d ≠ 2 := by omega
    have hn3 : d ≠ 3 := by omega
    have hn4 : d ≠ 4 := by omega
    have hn5 : d ≠ 5 := by omega
    have hn6 : d ≠ 6 := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3, if_neg hn2, if_neg hn3,
      if_neg hn4, if_neg hn5, if_neg hn6, add_zero, sub_zero]
    rw [quadratic d (by omega), quadratic (d - 1) (by omega),
      quadratic (d - 2) (by omega), quadratic (d - 3) (by omega),
      Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
    ring

private theorem generatingFunction : p * (1 - X) ^ 3 = numerator := by
  apply PowerSeries.ext
  exact coefficient_identity

private theorem recurrence (d : ℕ) (hd : 6 < d) :
    (a d : ℤ) = 3 * a (d - 1) - 3 * a (d - 2) + a (d - 3) := by
  have h := coefficient_identity d
  rw [product_coeff, numerator_coeff] at h
  have h1 : 1 ≤ d := by omega
  have h2 : 2 ≤ d := by omega
  have h3 : 3 ≤ d := by omega
  have hn2 : d ≠ 2 := by omega
  have hn3 : d ≠ 3 := by omega
  have hn4 : d ≠ 4 := by omega
  have hn5 : d ≠ 5 := by omega
  have hn6 : d ≠ 6 := by omega
  simp only [if_pos h1, if_pos h2, if_pos h3, if_neg hn2, if_neg hn3,
    if_neg hn4, if_neg hn5, if_neg hn6, add_zero, sub_zero] at h
  linarith only [h]

end A187851Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a187851.main :=
  ⟨A187851Proof.quadratic, A187851Proof.generatingFunction, A187851Proof.recurrence⟩
