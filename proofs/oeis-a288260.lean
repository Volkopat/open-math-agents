import OMAStatements.S_oeis_a288260

open OMA.S_oeis_a288260

private def expand {T : Type} (sub : T → List T) (s : List T) := s.flatMap sub
private def decode {T : Type} (bits : T → List Bool) (s : List T) := s.flatMap bits

private def orbit {T : Type} (sub : T → List T) (seed : List T) : ℕ → List T
  | 0 => seed
  | n+1 => expand sub (orbit sub seed n)

private def count {T : Type} (f : T → ℤ) : List T → ℤ
  | [] => 0
  | t :: s => f t + count f s

private def weight {T : Type} (bits : T → List Bool) (sub : T → List T) : ℕ → T → ℤ
  | 0, t => (bits t).length
  | n+1, t => count (weight bits sub n) (sub t)

private theorem count_append {T : Type} (f : T → ℤ) (s v : List T) :
    count f (s ++ v) = count f s + count f v := by
  induction s with
  | nil => simp [count]
  | cons t s ih => simp [count, ih, Int.add_assoc]

private theorem count_expand {T : Type} (bits : T → List Bool) (sub : T → List T) (k : ℕ) (s : List T) :
    count (weight bits sub (k+1)) s = count (weight bits sub k) (expand sub s) := by
  induction s with
  | nil => rfl
  | cons t s ih => exact (congrArg (count (weight bits sub k) (sub t) + ·) ih).trans (count_append _ _ _).symm

private theorem count_zero {T : Type} (bits : T → List Bool) (sub : T → List T) (s : List T) :
    count (weight bits sub 0) s = ((decode bits s).length : ℤ) := by
  induction s with
  | nil => rfl
  | cons t s ih => simpa [count, weight, decode] using congrArg (((bits t).length : ℤ) + ·) ih

private theorem from_tiles {T : Type} (bits : T → List Bool) (sub : T → List T) (seed : List T)
    (w : ℕ → List Bool) (encoding : ∀ n, w (n+1) = decode bits (orbit sub seed n))
    (init : ∀ n < 5, ((w n).length : ℤ) = reference n)
    (cell : ∀ t, weight bits sub 4 t = 2 * weight bits sub 3 t + 2 * weight bits sub 1 t - 3 * weight bits sub 0 t) :
    ∀ n, ((w n).length : ℤ) = reference n := by
  have read_length (k n : ℕ) : count (weight bits sub k) (orbit sub seed n) = ((w (n+k+1)).length : ℤ) := by
    induction k generalizing n with
    | zero => rw [count_zero, encoding]
    | succ k ih =>
      rw [count_expand]
      change count (weight bits sub k) (orbit sub seed (n+1)) = _
      rw [ih, show n + 1 + k = n + (k+1) by omega]
  have add_cells (s : List T) : count (weight bits sub 4) s = 2 * count (weight bits sub 3) s +
      2 * count (weight bits sub 1) s - 3 * count (weight bits sub 0) s := by
    induction s with
    | nil => rfl
    | cons t s ih =>
      have h := cell t
      simp only [count]
      omega
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 => apply init; decide
    | n+5 =>
      have hr := add_cells (orbit sub seed n)
      simp only [read_length] at hr
      change ((w (n+5)).length : ℤ) = 2 * ((w (n+4)).length : ℤ) + 2 * ((w (n+2)).length : ℤ) - 3 * ((w (n+1)).length : ℤ) at hr
      rw [hr, reference]
      change 2 * ((w (n+4)).length : ℤ) + 2 * ((w (n+2)).length : ℤ) - 3 * ((w (n+1)).length : ℤ) =
          2 * reference (n+4) + 2 * reference (n+2) - 3 * reference (n+1)
      rw [ih (n+4) (by omega), ih (n+2) (by omega), ih (n+1) (by omega)]

namespace ReplacementA

open OMA.S_oeis_a288260.RuleA

private inductive Start where
  | k2
private inductive Gap where
  | k1 | k3 | k4 | k2
private inductive Edge where
  | k1 | k3 | k2
private inductive Tile where
  | start (s : Start) | gap (g : Gap) | edge (e : Edge)

private def bits : Tile → List Bool
  | .start .k2 => [false, false, true]
  | .edge .k1 => [false]
  | .gap .k1 => [false, true]
  | .edge .k3 => [false, false, false]
  | .gap .k3 => [false, false, false, true]
  | .gap .k4 => [false, false, false, false, true]
  | .edge .k2 => [false, false]
  | .gap .k2 => [false, false, true]

private def morph : Tile → List Tile
  | .start .k2 => [.start .k2, .gap .k1]
  | .edge .k1 => [.edge .k3]
  | .gap .k1 => [.gap .k3]
  | .edge .k3 => [.gap .k4, .edge .k2]
  | .gap .k3 => [.gap .k4, .gap .k2]
  | .gap .k4 => [.gap .k4, .gap .k3, .gap .k1]
  | .edge .k2 => [.gap .k4, .edge .k1]
  | .gap .k2 => [.gap .k4, .gap .k1]

private def marker := [false, false]
private def seed : List Tile := [.start .k2, .edge .k1]

private inductive Body : List Tile → Prop
  | last (e : Edge) : Body [.edge e]
  | cons (g : Gap) {s : List Tile} : Body s → Body (.gap g :: s)

private inductive Whole : List Tile → Prop
  | start (k : Start) {s : List Tile} : Body s → Whole (.start k :: s)

private theorem body_closed (s : List Tile) (h : Body s) : Body (expand morph s) := by
  induction h with
  | last e => cases e <;> repeat constructor
  | cons g h ih => cases g <;> repeat first | exact ih | constructor

private theorem whole_closed (s : List Tile) (h : Whole s) : Whole (expand morph s) := by
  cases h with
  | start k h =>
    have ht := body_closed _ h
    cases k; repeat first | exact ht | constructor

-- A block of zeros followed by one ends each pass with the same marker.
-- Transfer that suffix to its neighbor, including at the right edge.
private theorem body_step (s : List Tile) (h : Body s) :
    marker ++ rewrite (decode bits s) = decode bits (expand morph s) := by
  induction h with
  | last e => cases e <;> rfl
  | @cons g tail h ih =>
    have transfer (v : List Bool) : marker ++ rewrite (bits (.gap g) ++ v) =
        decode bits (morph (.gap g)) ++ (marker ++ rewrite v) := by cases g <;> rfl
    calc
      _ = decode bits (morph (.gap g)) ++ (marker ++ rewrite (decode bits tail)) := transfer _
      _ = _ := by rw [ih]; simp [expand, decode, List.flatMap_append]

private theorem whole_step (s : List Tile) (h : Whole s) : rewrite (decode bits s) = decode bits (expand morph s) := by
  cases h with
  | @start k tail h =>
    have begins (v : List Bool) : rewrite (bits (.start k) ++ v) =
        decode bits (morph (.start k)) ++ (marker ++ rewrite v) := by cases k; rfl
    calc
      _ = decode bits (morph (.start k)) ++ (marker ++ rewrite (decode bits tail)) := begins _
      _ = _ := by rw [body_step _ h]; simp [expand, decode, List.flatMap_append]

private theorem result : ∀ n, ((word n).length : ℤ) = reference n := by
  apply from_tiles bits morph seed word
  · have good (n : ℕ) : Whole (orbit morph seed n) := by
      induction n with
      | zero => repeat constructor
      | succ n ih => exact whole_closed _ ih
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (congrArg rewrite ih).trans (whole_step _ (good n))
  · intro n hn
    match n with
    | 0 | 1 | 2 | 3 | 4 => decide
    | n+5 => omega
  · intro t
    cases t with
    | start k => cases k; decide
    | gap k => cases k <;> decide
    | edge k => cases k <;> decide

end ReplacementA

namespace ReplacementB

open OMA.S_oeis_a288260.RuleB

private inductive Start where
  | k1 | k2
private inductive Gap where
  | k1 | k3 | k2
private inductive Edge where
  | k0 | k1 | k2
private inductive Tile where
  | start (s : Start) | gap (g : Gap) | edge (e : Edge)

private def bits : Tile → List Bool
  | .start .k1 => [false, true]
  | .gap .k1 => [false, true]
  | .edge .k0 => []
  | .start .k2 => [false, false, true]
  | .gap .k3 => [false, false, false, true]
  | .edge .k1 => [false]
  | .gap .k2 => [false, false, true]
  | .edge .k2 => [false, false]

private def morph : Tile → List Tile
  | .start .k1 => [.start .k2]
  | .gap .k1 => [.gap .k3]
  | .edge .k0 => [.edge .k1]
  | .start .k2 => [.start .k1, .gap .k1, .gap .k1]
  | .gap .k3 => [.gap .k2, .gap .k1, .gap .k2]
  | .edge .k1 => [.edge .k2]
  | .gap .k2 => [.gap .k2, .gap .k1, .gap .k1]
  | .edge .k2 => [.gap .k2, .gap .k1, .edge .k0]

private def marker := [false]
private def seed : List Tile := [.start .k1, .gap .k1, .edge .k0]

private inductive Body : List Tile → Prop
  | last (e : Edge) : Body [.edge e]
  | cons (g : Gap) {s : List Tile} : Body s → Body (.gap g :: s)

private inductive Whole : List Tile → Prop
  | start (k : Start) {s : List Tile} : Body s → Whole (.start k :: s)

private theorem body_closed (s : List Tile) (h : Body s) : Body (expand morph s) := by
  induction h with
  | last e => cases e <;> repeat constructor
  | cons g h ih => cases g <;> repeat first | exact ih | constructor

private theorem whole_closed (s : List Tile) (h : Whole s) : Whole (expand morph s) := by
  cases h with
  | start k h =>
    have ht := body_closed _ h
    cases k <;> repeat first | exact ht | constructor

-- A block of zeros followed by one ends each pass with the same marker.
-- Transfer that suffix to its neighbor, including at the right edge.
private theorem body_step (s : List Tile) (h : Body s) :
    marker ++ rewrite (decode bits s) = decode bits (expand morph s) := by
  induction h with
  | last e => cases e <;> rfl
  | @cons g tail h ih =>
    have transfer (v : List Bool) : marker ++ rewrite (bits (.gap g) ++ v) =
        decode bits (morph (.gap g)) ++ (marker ++ rewrite v) := by cases g <;> rfl
    calc
      _ = decode bits (morph (.gap g)) ++ (marker ++ rewrite (decode bits tail)) := transfer _
      _ = _ := by rw [ih]; simp [expand, decode, List.flatMap_append]

private theorem whole_step (s : List Tile) (h : Whole s) : rewrite (decode bits s) = decode bits (expand morph s) := by
  cases h with
  | @start k tail h =>
    have begins (v : List Bool) : rewrite (bits (.start k) ++ v) =
        decode bits (morph (.start k)) ++ (marker ++ rewrite v) := by cases k <;> rfl
    calc
      _ = decode bits (morph (.start k)) ++ (marker ++ rewrite (decode bits tail)) := begins _
      _ = _ := by rw [body_step _ h]; simp [expand, decode, List.flatMap_append]

private theorem result : ∀ n, ((word n).length : ℤ) = reference n := by
  apply from_tiles bits morph seed word
  · have good (n : ℕ) : Whole (orbit morph seed n) := by
      induction n with
      | zero => repeat constructor
      | succ n ih => exact whole_closed _ ih
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact (congrArg rewrite ih).trans (whole_step _ (good n))
  · intro n hn
    match n with
    | 0 | 1 | 2 | 3 | 4 => decide
    | n+5 => omega
  · intro t
    cases t with
    | start k => cases k <;> decide
    | gap k => cases k <;> decide
    | edge k => cases k <;> decide

end ReplacementB

theorem OMA.solution : type_of% @OMA.S_oeis_a288260.main := by
  intro n
  exact ⟨ReplacementA.result n, ReplacementB.result n⟩
