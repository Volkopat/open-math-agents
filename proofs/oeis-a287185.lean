import OMAStatements.S_oeis_a287185

open OMA.S_oeis_a287185

private inductive Gap where
  | g2 | g5 | g3 | g6
private inductive Edge where
  | e0 | e1 | e2 | e3 | e4
private inductive Tile where
  | head | gap (k : Gap) | edge (k : Edge)

-- A gap contains zeros followed by one. Edges also encode the final zeros.
private def bits : Tile → List Bool
  | .head => []
  | .gap .g2 => [false, false, true]
  | .gap .g5 => [false, false, false, false, false, true]
  | .edge .e0 => [false, false, false, true, false]
  | .gap .g3 => [false, false, false, true]
  | .gap .g6 => [false, false, false, false, false, false, true]
  | .edge .e1 => [false, false, false, false, false]
  | .edge .e2 => [false, false, false, true, false, false]
  | .edge .e3 => [false, false, false, false, false, false, true, false]
  | .edge .e4 => [false, false, false, false]

private def morph : Tile → List Tile
  | .head => [.head, .gap .g2]
  | .gap .g2 => [.gap .g5]
  | .gap .g5 => [.gap .g3, .gap .g6]
  | .edge .e0 => [.edge .e1]
  | .gap .g3 => [.gap .g6]
  | .gap .g6 => [.gap .g3, .gap .g3, .gap .g5]
  | .edge .e1 => [.edge .e2]
  | .edge .e2 => [.edge .e3]
  | .edge .e3 => [.gap .g3, .gap .g3, .edge .e4]
  | .edge .e4 => [.edge .e0]

private def expand (s : List Tile) := s.flatMap morph
private def decode (s : List Tile) := s.flatMap bits

private inductive Body : List Tile → Prop
  | last (e : Edge) : Body [.edge e]
  | cons (g : Gap) {s : List Tile} : Body s → Body (.gap g :: s)

private theorem closed (s : List Tile) (hs : Body s) : Body (expand s) := by
  induction hs with
  | last e => cases e <;> repeat constructor
  | cons g h ih => cases g <;> repeat first | exact ih | constructor

-- Transferring 001 across every gap turns one rewrite pass into the substitution.
private theorem commute (s : List Tile) (hs : Body s) :
    rewrite (decode s) = [false, false, true] ++ decode (expand s) := by
  induction hs with
  | last e => cases e <;> rfl
  | @cons g tail h ih =>
    have step (v : List Bool) : rewrite (bits (.gap g) ++ v) = rewrite (bits (.gap g)) ++ rewrite v := by
      cases g <;> rfl
    change rewrite (bits (.gap g) ++ decode tail) = _
    rw [step, ih]
    cases g <;> rfl

private def bodyOrbit : ℕ → List Tile
  | 0 => [.gap .g2, .gap .g5, .edge .e0]
  | n+1 => .gap .g2 :: expand (bodyOrbit n)

private def orbit (n : ℕ) : List Tile := .head :: bodyOrbit n

private theorem form (n : ℕ) : Body (bodyOrbit n) := by
  induction n with
  | zero => repeat constructor
  | succ n ih => exact .cons _ (closed _ ih)

private theorem encode_word (n : ℕ) : word (n+3) = decode (orbit n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg rewrite ih).trans (commute _ (form n))

private def count (f : Tile → ℤ) : List Tile → ℤ
  | [] => 0
  | t :: s => f t + count f s

private def weight : ℕ → Tile → ℤ
  | 0, t => (bits t).length
  | n+1, t => count (weight n) (morph t)

private theorem count_append (f : Tile → ℤ) (s v : List Tile) :
    count f (s ++ v) = count f s + count f v := by
  induction s with
  | nil => simp [count]
  | cons t s ih => simp [count, ih, Int.add_assoc]

private theorem count_expand (k : ℕ) (s : List Tile) :
    count (weight (k+1)) s = count (weight k) (expand s) := by
  induction s with
  | nil => rfl
  | cons t s ih => exact (congrArg (count (weight k) (morph t) + ·) ih).trans (count_append _ _ _).symm

private theorem count_zero (s : List Tile) : count (weight 0) s = ((decode s).length : ℤ) := by
  induction s with
  | nil => rfl
  | cons t s ih => simpa [count, weight, decode] using congrArg (((bits t).length : ℤ) + ·) ih

private theorem count_orbit (k n : ℕ) : count (weight k) (orbit n) = ((word (n+k+3)).length : ℤ) := by
  induction k generalizing n with
  | zero => rw [count_zero, encode_word]
  | succ k ih =>
    rw [count_expand]
    change count (weight k) (orbit (n+1)) = _
    rw [ih, show n + 1 + k = n + (k+1) by omega]

private theorem recurrence (s : List Tile) : count (weight 8) s =
    3 * count (weight 6) s + count (weight 5) s + count (weight 3) s - 3 * count (weight 1) s - count (weight 0) s := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    have h : weight 8 t = 3 * weight 6 t + weight 5 t + weight 3 t - 3 * weight 1 t - weight 0 t := by
      cases t with
      | head => decide
      | gap g => cases g <;> decide
      | edge e => cases e <;> decide
    simp only [count]
    omega

set_option maxRecDepth 8192 in
theorem OMA.solution : type_of% @OMA.S_oeis_a287185.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => decide
    | n+11 =>
      have hr := recurrence (orbit n)
      simp only [count_orbit] at hr
      change ((word (n+11)).length : ℤ) = 3 * ((word (n+9)).length : ℤ) + ((word (n+8)).length : ℤ) + ((word (n+6)).length : ℤ) - 3 * ((word (n+4)).length : ℤ) - ((word (n+3)).length : ℤ) at hr
      rw [hr, reference]
      change 3 * ((word (n+9)).length : ℤ) + ((word (n+8)).length : ℤ) + ((word (n+6)).length : ℤ) - 3 * ((word (n+4)).length : ℤ) - ((word (n+3)).length : ℤ) = 3 * reference (n+9) + reference (n+8) + reference (n+6) - 3 * reference (n+4) - reference (n+3)
      rw [ih (n+9) (by omega), ih (n+8) (by omega), ih (n+6) (by omega), ih (n+4) (by omega), ih (n+3) (by omega)]
