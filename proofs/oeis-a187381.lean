import OMAStatements.S_oeis_a187381
import Mathlib

/-! The general translation-counting and power-series lemmas follow Genbox’s proof in
PR 23762. The final section certifies the enumeration and coefficients for this move set. -/

namespace OMA.TourCount

abbrev Point := ℤ × ℤ

private def coordValues {k : ℕ} (f : Fin (k+1) → ℤ) : Finset ℤ :=
  Finset.univ.image f

private theorem value_member {k : ℕ} (f : Fin (k+1) → ℤ) (i : Fin (k+1)) :
    f i ∈ coordValues f := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

private theorem coord_nonempty {k : ℕ} (f : Fin (k+1) → ℤ) :
    (coordValues f).Nonempty := ⟨f 0, value_member f 0⟩

def low {k : ℕ} (f : Fin (k+1) → ℤ) : ℤ :=
  (coordValues f).min' (coord_nonempty f)

def high {k : ℕ} (f : Fin (k+1) → ℤ) : ℤ :=
  (coordValues f).max' (coord_nonempty f)

def span {k : ℕ} (f : Fin (k+1) → ℤ) : ℕ := (high f - low f).toNat

theorem low_le {k : ℕ} (f : Fin (k+1) → ℤ) (i : Fin (k+1)) :
    low f ≤ f i := Finset.min'_le _ _ (value_member f i)

theorem le_high {k : ℕ} (f : Fin (k+1) → ℤ) (i : Fin (k+1)) :
    f i ≤ high f := Finset.le_max' _ _ (value_member f i)

theorem at_low {k : ℕ} (f : Fin (k+1) → ℤ) :
    ∃ i, f i = low f := by
  have h : low f ∈ coordValues f := Finset.min'_mem _ _
  obtain ⟨i, _, hist⟩ := Finset.mem_image.mp h
  exact ⟨i, hist⟩

theorem at_high {k : ℕ} (f : Fin (k+1) → ℤ) :
    ∃ i, f i = high f := by
  have h : high f ∈ coordValues f := Finset.max'_mem _ _
  obtain ⟨i, _, hist⟩ := Finset.mem_image.mp h
  exact ⟨i, hist⟩

theorem span_cast {k : ℕ} (f : Fin (k+1) → ℤ) :
    ((span f : ℕ) : ℤ) = high f - low f :=
  Int.toNat_of_nonneg (sub_nonneg.mpr ((low_le f 0).trans (le_high f 0)))

def GoodShift {k : ℕ} (n : ℕ) (f : Fin (k+1) → ℤ) :=
  {x : ℤ // ∀ i, 0 ≤ x + f i ∧ x + f i < n}

private theorem shift_low {k n : ℕ} {f : Fin (k+1) → ℤ}
    (c : GoodShift n f) : 0 ≤ c.val + low f := by
  obtain ⟨i, eq⟩ := at_low f
  simpa only [eq] using (c.property i).1

private theorem shift_high {k n : ℕ} {f : Fin (k+1) → ℤ}
    (c : GoodShift n f) : c.val + high f < n := by
  obtain ⟨i, eq⟩ := at_high f
  simpa only [eq] using (c.property i).2

private def shiftIndex {k : ℕ} (n : ℕ) (f : Fin (k+1) → ℤ) (c : GoodShift n f) :
    Fin (n - span f) := by
  have base := shift_low c
  have last := shift_high c
  have cast := Int.toNat_of_nonneg base
  have width := span_cast f
  exact ⟨(c.val + low f).toNat, by omega⟩

private def indexShift {k : ℕ} (n : ℕ) (f : Fin (k+1) → ℤ) (u : Fin (n - span f)) :
    GoodShift n f := by
  refine ⟨(u.val : ℤ) - low f, ?_⟩
  intro i
  have width := span_cast f
  have lo := low_le f i
  have hi := le_high f i
  have bound := u.isLt
  constructor <;> omega

def shifts {k : ℕ} (n : ℕ) (f : Fin (k+1) → ℤ) :
    GoodShift n f ≃ Fin (n - span f) where
  toFun := shiftIndex n f
  invFun := indexShift n f
  left_inv c := by
    apply Subtype.ext
    change (((c.val + low f).toNat : ℕ) : ℤ) - low f = c.val
    rw [Int.toNat_of_nonneg (shift_low c)]
    omega
  right_inv u := by
    apply Fin.ext
    change ((u.val : ℤ) - low f + low f).toNat = u.val
    rw [sub_add_cancel]
    simp

def Inside (n : ℕ) (p : Point) : Prop :=
  (0 ≤ p.1 ∧ p.1 < n) ∧ (0 ≤ p.2 ∧ p.2 < n)

def Offsets {k : ℕ} (n : ℕ) (walk : Fin (k+1) → Point) :=
  {t : Point // ∀ i, Inside n (t + walk i)}

private def separate {k : ℕ} (n : ℕ) (walk : Fin (k+1) → Point) :
    Offsets n walk ≃
      GoodShift n (fun i => (walk i).1) × GoodShift n (fun i => (walk i).2) where
  toFun t := (⟨t.val.1, fun i => (t.property i).1⟩, ⟨t.val.2, fun i => (t.property i).2⟩)
  invFun t := ⟨(t.1.val, t.2.val), fun i => ⟨t.1.property i, t.2.property i⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def placements {k : ℕ} (n : ℕ) (walk : Fin (k+1) → Point) :
    Offsets n walk ≃ (Fin (n - span (fun i => (walk i).1)) ×
      Fin (n - span (fun i => (walk i).2))) :=
  (separate n walk).trans (Equiv.prodCongr (shifts n _) (shifts n _))

end OMA.TourCount

namespace OMA.TourCount

def walk {k : ℕ} (u : Fin k → Point) (i : Fin (k+1)) : Point :=
  ∑ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => j.val < i.val), u j

@[simp] theorem walk_zero {k : ℕ} (u : Fin k → Point) : walk u 0 = 0 := by
  simp [walk]

theorem walk_succ {k : ℕ} (u : Fin k → Point) (i : Fin k) :
    walk u i.succ = walk u i.castSucc + u i := by
  have split :
      (Finset.univ : Finset (Fin k)).filter (fun j => j.val < i.val+1) =
      insert i ((Finset.univ : Finset (Fin k)).filter (fun j => j.val < i.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases eq : j = i
      · exact Or.inl eq
      · right
        have different : j.val ≠ i.val := fun value => eq (Fin.ext value)
        omega
    · rintro (rfl | lt) <;> omega
  change (∑ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => j.val < i.val+1), u j) =
    (∑ j ∈ (Finset.univ : Finset (Fin k)).filter (fun j => j.val < i.val), u j) + u i
  rw [split, Finset.sum_insert (by simp)]
  exact add_comm _ _

def coordinates {n : ℕ} (p : Fin n × Fin n) : Point :=
  ((p.1.val : ℤ), (p.2.val : ℤ))

theorem coordinates_injective {n : ℕ} : Function.Injective (@coordinates n) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · have x := congrArg Prod.fst h
    change (p.1.val : ℤ) = (q.1.val : ℤ) at x
    exact_mod_cast x
  · have y := congrArg Prod.snd h
    change (p.2.val : ℤ) = (q.2.val : ℤ) at y
    exact_mod_cast y

theorem coordinates_inside {n : ℕ} (p : Fin n × Fin n) : Inside n (coordinates p) := by
  have x := p.1.isLt
  have y := p.2.isLt
  unfold coordinates Inside
  dsimp
  omega

def board {n : ℕ} (p : Point) (h : Inside n p) : Fin n × Fin n := by
  have x := Int.toNat_of_nonneg h.1.1
  have y := Int.toNat_of_nonneg h.2.1
  have bx := h.1.2
  have by' := h.2.2
  exact (⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩)

@[simp] theorem coordinates_board {n : ℕ} (p : Point) (h : Inside n p) :
    coordinates (board p h) = p := by
  apply Prod.ext
  · exact Int.toNat_of_nonneg h.1.1
  · exact Int.toNat_of_nonneg h.2.1

def IsTour (moves : Finset Point) (n k : ℕ) (p : Fin (k+1) → Fin n × Fin n) : Prop :=
  Function.Injective p ∧ ∀ i j, j.val = i.val+1 →
    coordinates (p j) - coordinates (p i) ∈ moves

instance (moves : Finset Point) (n k : ℕ) : DecidablePred (IsTour moves n k) := fun p => by
  unfold IsTour
  infer_instance

abbrev Tours (moves : Finset Point) (n k : ℕ) :=
  {p : Fin (k+1) → Fin n × Fin n // IsTour moves n k p}

abbrev MoveWord (moves : Finset Point) (k : ℕ) :=
  Fin k → {s : Point // s ∈ moves}

def relative {moves : Finset Point} {k : ℕ} (u : MoveWord moves k) : Fin (k+1) → Point :=
  walk (fun j => (u j).val)

def Simple {moves : Finset Point} {k : ℕ} (u : MoveWord moves k) : Prop :=
  Function.Injective (relative u)

instance (moves : Finset Point) (k : ℕ) : DecidablePred (@Simple moves k) := fun u => by
  unfold Simple
  infer_instance

abbrev SimpleWord (moves : Finset Point) (k : ℕ) :=
  {u : MoveWord moves k // Simple u}

def steps {moves : Finset Point} {n k : ℕ} (p : Tours moves n k) : MoveWord moves k :=
  fun j =>
    ⟨coordinates (p.val j.succ) - coordinates (p.val j.castSucc), p.property.2 _ _ rfl⟩

theorem relative_steps {moves : Finset Point} {n k : ℕ} (p : Tours moves n k)
    (i : Fin (k+1)) : relative (steps p) i = coordinates (p.val i) - coordinates (p.val 0) := by
  refine Fin.induction ?_ (fun j ih => ?_) i
  · simp [relative]
  · unfold relative at ih ⊢
    rw [walk_succ, ih]
    change coordinates (p.val j.castSucc) - coordinates (p.val 0) +
      (coordinates (p.val j.succ) - coordinates (p.val j.castSucc)) =
      coordinates (p.val j.succ) - coordinates (p.val 0)
    abel

private theorem simple_steps {moves : Finset Point} {n k : ℕ} (p : Tours moves n k) :
    Simple (steps p) := by
  intro i j eq
  rw [relative_steps, relative_steps] at eq
  apply p.property.1
  apply coordinates_injective
  have sum := congrArg (fun z => z + coordinates (p.val 0)) eq
  simpa only [sub_add_cancel] using sum

abbrev ShiftedWord (moves : Finset Point) (n k : ℕ) :=
  Σ u : SimpleWord moves k, Offsets n (relative u.val)

def extract {moves : Finset Point} {n k : ℕ} (p : Tours moves n k) :
    ShiftedWord moves n k := by
  refine ⟨⟨steps p, simple_steps p⟩, ⟨coordinates (p.val 0), ?_⟩⟩
  intro i
  change Inside n (coordinates (p.val 0) + relative (steps p) i)
  rw [relative_steps, add_sub_cancel]
  exact coordinates_inside (p.val i)

def reconstruct {moves : Finset Point} {n k : ℕ} (x : ShiftedWord moves n k) :
    Tours moves n k := by
  let p (i : Fin (k+1)) := board (x.2.val + relative x.1.val i) (x.2.property i)
  have geometry (i : Fin (k+1)) : coordinates (p i) = x.2.val+relative x.1.val i :=
    coordinates_board _ _
  refine ⟨p, ?_, ?_⟩
  · intro i j eq
    have eqZ := congrArg coordinates eq
    rw [geometry, geometry] at eqZ
    exact x.1.property (add_left_cancel eqZ)
  · intro i j step
    let edge : Fin k := ⟨i.val, by have h := j.isLt; omega⟩
    have earlier : edge.castSucc = i := Fin.ext rfl
    have later : edge.succ = j := Fin.ext step.symm
    rw [← earlier, ← later, geometry, geometry]
    unfold relative
    rw [walk_succ]
    have displacement :
        x.2.val + (walk (fun t => (x.1.val t).val) edge.castSucc + (x.1.val edge).val) -
          (x.2.val + walk (fun t => (x.1.val t).val) edge.castSucc) = (x.1.val edge).val := by
      abel
    rw [displacement]
    exact (x.1.val edge).property

@[simp] theorem reconstruct_coord {moves : Finset Point} {n k : ℕ} (x : ShiftedWord moves n k)
    (i : Fin (k+1)) : coordinates ((reconstruct x).val i) = x.2.val + relative x.1.val i :=
  coordinates_board _ (x.2.property i)

theorem reconstruct_extract {moves : Finset Point} {n k : ℕ} (p : Tours moves n k) :
    reconstruct (extract p) = p := by
  apply Subtype.ext
  funext i
  apply coordinates_injective
  rw [reconstruct_coord]
  change coordinates (p.val 0) + relative (steps p) i = coordinates (p.val i)
  rw [relative_steps, add_sub_cancel]

private theorem offset_heq {k n : ℕ} {u v : Fin (k+1) → Point} (eq : u = v)
    {x : Offsets n u} {y : Offsets n v} (same : x.val = y.val) : HEq x y := by
  cases eq
  exact heq_of_eq (Subtype.ext same)

theorem extract_reconstruct {moves : Finset Point} {n k : ℕ} (x : ShiftedWord moves n k) :
    extract (reconstruct x) = x := by
  have word : (extract (reconstruct x)).1 = x.1 := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    change coordinates ((reconstruct x).val j.succ) -
      coordinates ((reconstruct x).val j.castSucc) = (x.1.val j).val
    rw [reconstruct_coord, reconstruct_coord]
    unfold relative
    rw [walk_succ]
    abel
  have shift : (extract (reconstruct x)).2.val = x.2.val := by
    change coordinates ((reconstruct x).val 0) = x.2.val
    rw [reconstruct_coord]
    simp [relative]
  exact Sigma.ext word (offset_heq (congrArg (fun u : SimpleWord moves k => relative u.val) word) shift)

def shiftedTours (moves : Finset Point) (n k : ℕ) :
    Tours moves n k ≃ ShiftedWord moves n k :=
  ⟨extract, reconstruct, reconstruct_extract, extract_reconstruct⟩

end OMA.TourCount

namespace OMA.TourCount

def width {moves : Finset Point} {k : ℕ} (u : MoveWord moves k) : ℕ :=
  span (fun i => (relative u i).1)

def height {moves : Finset Point} {k : ℕ} (u : MoveWord moves k) : ℕ :=
  span (fun i => (relative u i).2)

abbrev IndexedPlacement {moves : Finset Point} {k : ℕ} (n : ℕ) (u : MoveWord moves k) :=
  Fin (n - width u) × Fin (n - height u)

def tourEquiv (moves : Finset Point) (n k : ℕ) :
    Tours moves n k ≃ (Σ u : SimpleWord moves k, IndexedPlacement n u.val) :=
  (shiftedTours moves n k).trans (Equiv.sigmaCongrRight fun u => placements n (relative u.val))

theorem card_tours (moves : Finset Point) (n k : ℕ) :
    Fintype.card (Tours moves n k) =
      ∑ u : SimpleWord moves k, (n - width u.val) * (n - height u.val) := by
  rw [Fintype.card_congr (tourEquiv moves n k), Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]

theorem count (moves : Finset Point) (n k : ℕ) :
    ((Finset.univ : Finset (Fin (k+1) → Fin n × Fin n)).filter (IsTour moves n k)).card =
      ∑ u : SimpleWord moves k, (n - width u.val) * (n - height u.val) := by
  have formula := card_tours moves n k
  rw [Fintype.card_subtype] at formula
  exact formula

theorem countList (moves : List Point) (n k : ℕ) :
    ((Finset.univ : Finset (Fin (k+1) → Fin n × Fin n)).filter
      (fun p => Function.Injective p ∧ ∀ i j, j.val = i.val+1 →
        coordinates (p j) - coordinates (p i) ∈ moves)).card =
      ∑ u : SimpleWord moves.toFinset k, (n - width u.val) * (n - height u.val) := by
  rw [← count moves.toFinset n k]
  congr 1
  ext p
  simp [IsTour]

end OMA.TourCount

namespace TourMoments

open scoped BigOperators

def placements {α : Type*} (walks : Finset α) (width height : α → ℕ) (n : ℕ) : ℕ :=
  ∑ w ∈ walks, (n-width w)*(n-height w)

def sums {α : Type*} (walks : Finset α) (width height : α → ℕ) : ℤ :=
  ∑ w ∈ walks, ((width w : ℤ) + height w)

def products {α : Type*} (walks : Finset α) (width height : α → ℕ) : ℤ :=
  ∑ w ∈ walks, ((width w : ℤ) * height w)

theorem quadratic {α : Type*} (walks : Finset α) (width height : α → ℕ) (n : ℕ)
    (hw : ∀ w ∈ walks, width w ≤ n) (hh : ∀ w ∈ walks, height w ≤ n) :
    (placements walks width height n : ℤ) =
      walks.card * (n : ℤ)^2 - sums walks width height * n + products walks width height := by
  unfold placements sums products
  push_cast
  calc
    (∑ w ∈ walks, ((n-width w : ℕ) : ℤ) * ((n-height w : ℕ) : ℤ))
      = ∑ w ∈ walks, ((n : ℤ)^2 - ((width w : ℤ)+height w)*n + (width w : ℤ)*height w) := by
        apply Finset.sum_congr rfl
        intro w hw'
        rw [Nat.cast_sub (hw w hw'), Nat.cast_sub (hh w hw')]
        ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_mul]
      simp

theorem extend {a b : ℕ → ℤ} {lower cut : ℕ}
    (small : ∀ j : Fin cut, lower ≤ j.val → a j = b j)
    (large : ∀ n ≥ cut, a n = b n) :
    ∀ n ≥ lower, a n = b n := by
  intro n hn
  by_cases h : n < cut
  · exact small ⟨n,h⟩ hn
  · exact large n (Nat.le_of_not_gt h)

end TourMoments

namespace OMA.TourSeries

open PowerSeries

/-- The coefficient of the series shifted by a power of the variable. -/
def shift (a : ℕ → ℤ) (k n : ℕ) : ℤ :=
  if k ≤ n then a (n - k) else 0

/-- The third backward difference, with zero values at negative indices. -/
def thirdDifference (a : ℕ → ℤ) (n : ℕ) : ℤ :=
  a n - 3 * shift a 1 n + 3 * shift a 2 n - shift a 3 n

theorem coeff_denominator (a : ℕ → ℤ) (n : ℕ) :
    coeff n (mk a * (1 - X)^3) = thirdDifference a n := by
  have expanded :
      mk a * (1 - X)^3 =
        mk a - C (3 : ℤ) * (mk a * X ^ 1) + C (3 : ℤ) * (mk a * X ^ 2) -
          mk a * X ^ 3 := by
    norm_num
    ring
  rw [expanded]
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk,
    thirdDifference, shift]

/-- A quadratic sequence has zero third backward difference once all four terms are in its quadratic range. -/
theorem thirdDifference_zero_of_quadratic
    (a : ℕ → ℤ) (cutoff : ℕ) (A B C : ℤ)
    (quadratic : ∀ n : ℕ, cutoff ≤ n → a n = A * (n : ℤ)^2 + B * n + C)
    (n : ℕ) (large : cutoff + 3 ≤ n) : thirdDifference a n = 0 := by
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  simp only [thirdDifference, shift, if_pos h1, if_pos h2, if_pos h3]
  rw [quadratic n (by omega), quadratic (n-1) (by omega),
    quadratic (n-2) (by omega), quadratic (n-3) (by omega)]
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3]
  ring

theorem recurrence_of_thirdDifference_zero (a : ℕ → ℤ) (n : ℕ)
    (large : 3 ≤ n) (vanishes : thirdDifference a n = 0) :
    a n = 3 * a (n-1) - 3 * a (n-2) + a (n-3) := by
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  simp only [thirdDifference, shift, if_pos h1, if_pos h2, if_pos large] at vanishes
  omega

theorem recurrence_of_quadratic
    (a : ℕ → ℤ) (cutoff : ℕ) (A B C : ℤ)
    (quadratic : ∀ n : ℕ, cutoff ≤ n → a n = A * (n : ℤ)^2 + B * n + C)
    (n : ℕ) (large : cutoff + 3 ≤ n) :
    a n = 3 * a (n-1) - 3 * a (n-2) + a (n-3) :=
  recurrence_of_thirdDifference_zero a n (by omega)
    (thirdDifference_zero_of_quadratic a cutoff A B C quadratic n large)

/-- A finite coefficient comparison suffices when both series have zero coefficients in the tail. -/
theorem eq_of_prefix
    (a : ℕ → ℤ) (cutoff length : ℕ) (A B C : ℤ) (p : PowerSeries ℤ)
    (quadratic : ∀ n : ℕ, cutoff ≤ n → a n = A * (n : ℤ)^2 + B * n + C)
    (length_ge : cutoff + 3 ≤ length)
    (checked : ∀ i : Fin length, thirdDifference a i = coeff i.val p)
    (tail : ∀ n : ℕ, length ≤ n → coeff n p = 0) :
    mk a * (1 - X)^3 = p := by
  apply PowerSeries.ext
  intro n
  rw [coeff_denominator]
  by_cases inside : n < length
  · exact checked ⟨n, inside⟩
  · rw [tail n (by omega)]
    exact thirdDifference_zero_of_quadratic a cutoff A B C quadratic n (by omega)

theorem eq_polynomial_of_prefix
    (a : ℕ → ℤ) (cutoff length : ℕ) (A B C : ℤ) (p : Polynomial ℤ)
    (quadratic : ∀ n : ℕ, cutoff ≤ n → a n = A * (n : ℤ)^2 + B * n + C)
    (length_ge : cutoff + 3 ≤ length) (degree_lt : p.natDegree < length)
    (checked : ∀ i : Fin length, thirdDifference a i = p.coeff i.val) :
    mk a * (1 - X)^3 = (p : PowerSeries ℤ) := by
  apply eq_of_prefix a cutoff length A B C _ quadratic length_ge
  · intro i
    rw [Polynomial.coeff_coe]
    exact checked i
  · intro n hn
    rw [Polynomial.coeff_coe]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (degree_lt.trans_le hn)

end OMA.TourSeries

namespace OMA.TourExample187381

open OMA.TourCount
open OMA.S_oeis_a187381 (a moves)
open scoped BigOperators

private abbrev Words := SimpleWord moves.toFinset 6
private def allWords : Finset Words := Finset.univ
private def wide (w : Words) : ℕ := width w.val
private def tall (w : Words) : ℕ := height w.val

private theorem placements_eq (n : ℕ) :
    a n = TourMoments.placements allWords wide tall n := by
  unfold OMA.S_oeis_a187381.a OMA.S_oeis_a187381.IsTour
  exact countList moves n 6

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
private theorem width_bound : ∀ w : Words, wide w ≤ 6 ∧ tall w ≤ 6 := by
  decide +kernel

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
private theorem moments : allWords.card = 487 ∧
    TourMoments.sums allWords wide tall = 3198 ∧
    TourMoments.products allWords wide tall = 5104 := by
  decide +kernel

private theorem tail (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 487 * (n : ℤ)^2 + (-3198) * n + 5104 := by
  rw [placements_eq]
  have out := TourMoments.quadratic allWords wide tall n
    (fun w _ => (width_bound w).1.trans hn) (fun w _ => (width_bound w).2.trans hn)
  rw [moments.1, moments.2.1, moments.2.2] at out
  exact out.trans (by push_cast; ring)

private def table (i : ℕ) : ℕ := ([0, 0, 0, 18, 324, 1418, 3448, 6581, 10688] : List ℕ)[i]!

set_option maxRecDepth 18000 in
set_option maxHeartbeats 0 in
private theorem prefix_check : ∀ i : Fin 9,
    TourMoments.placements allWords wide tall i = table i := by
  decide +kernel

private theorem values (i : ℕ) (hi : i < 9) : (a i : ℤ) = table i := by
  have checked := prefix_check ⟨i, hi⟩
  change TourMoments.placements allWords wide tall i = table i at checked
  rw [placements_eq, checked]

private noncomputable def polynomial : Polynomial ℤ :=
  Polynomial.X ^ 3 * (18 + 270 * Polynomial.X + 500 * Polynomial.X ^ 2 + 148 * Polynomial.X ^ 3 + 167 * Polynomial.X ^ 4 - 129 * Polynomial.X ^ 5)

private def targetCoefficient (n : ℕ) : ℤ :=
  (if n = 3 then 18 else 0) + (if n = 4 then 270 else 0) + (if n = 5 then 500 else 0) + (if n = 6 then 148 else 0) + (if n = 7 then 167 else 0) - (if n = 8 then 129 else 0)

private theorem polynomial_coefficient (n : ℕ) :
    polynomial.coeff n = targetCoefficient n := by
  have expanded : polynomial =
      Polynomial.C 18 * Polynomial.X^3 + Polynomial.C 270 * Polynomial.X^4 + Polynomial.C 500 * Polynomial.X^5 + Polynomial.C 148 * Polynomial.X^6 + Polynomial.C 167 * Polynomial.X^7 - Polynomial.C 129 * Polynomial.X^8 := by
    unfold polynomial
    norm_num <;> ring
  rw [expanded]
  simp only [targetCoefficient, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]

private theorem table_coefficients : ∀ i : Fin 9,
    OMA.TourSeries.thirdDifference (fun n => (table n : ℤ)) i = targetCoefficient i.val := by
  decide +kernel

private theorem coefficients (i : Fin 9) :
    OMA.TourSeries.thirdDifference (fun n => (a n : ℤ)) i = polynomial.coeff i.val := by
  rw [polynomial_coefficient, ← table_coefficients i]
  have bound := i.isLt
  simp only [OMA.TourSeries.thirdDifference, OMA.TourSeries.shift]
  rw [values i.val bound, values (i.val-1) (by omega),
    values (i.val-2) (by omega), values (i.val-3) (by omega)]


theorem main : type_of% @OMA.S_oeis_a187381.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    simpa only [sub_eq_add_neg, neg_mul] using tail n (by omega)
  · have h := OMA.TourSeries.eq_polynomial_of_prefix (fun n => (a n : ℤ)) 6 9 487 (-3198) 5104
      polynomial tail (by decide) (by unfold polynomial; compute_degree <;> decide) coefficients
    have numeral (n : ℕ) [n.AtLeastTwo] :
        ((OfNat.ofNat n : Polynomial ℤ) : PowerSeries ℤ) = (OfNat.ofNat n : PowerSeries ℤ) :=
      map_ofNat (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ) n
    change _ = PowerSeries.X ^ 3 * (18 + 270 * PowerSeries.X + 500 * PowerSeries.X ^ 2 + 148 * PowerSeries.X ^ 3 + 167 * PowerSeries.X ^ 4 - 129 * PowerSeries.X ^ 5)
    exact h.trans (by
      unfold polynomial
      simp only [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_sub,
        Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_zero, Polynomial.coe_neg, numeral])
  · intro n hn
    exact OMA.TourSeries.recurrence_of_quadratic (fun n => (a n : ℤ)) 6 487 (-3198) 5104 tail n (by omega)

end OMA.TourExample187381

theorem OMA.solution : type_of% @OMA.S_oeis_a187381.main :=
  OMA.TourExample187381.main
