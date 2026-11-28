import OMAStatements.S_oeis_a287439

open OMA.S_oeis_a287439

private inductive Tile where
  | a | b | c

private def bits : Tile → List Bool
  | .a => [false, false]
  | .b => [true, false, false, false]
  | .c => [false, true, false]

private def morph : Tile → List Tile
  | .a => [.b]
  | .b => [.a, .c, .a]
  | .c => [.a, .a]

private def expand (s : List Tile) := s.flatMap morph
private def decode (s : List Tile) := s.flatMap bits

private theorem commute (s : List Tile) : rewrite (decode s) = decode (expand s) := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    have h (v : List Bool) : rewrite (bits t ++ v) = decode (morph t) ++ rewrite v := by
      cases t <;> rfl
    simpa only [expand, decode, List.flatMap_cons, List.flatMap_append] using
      (h (decode s)).trans (congrArg (decode (morph t) ++ ·) ih)

private def orbit : ℕ → List Tile
  | 0 => [.a]
  | n+1 => expand (orbit n)

private theorem encode_word (n : ℕ) : word n = decode (orbit n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg rewrite ih).trans (commute _)

private def size (s : List Tile) : ℤ := (decode s).length

private theorem add_size (s t : List Tile) : size (s ++ t) = size s + size t := by
  simp [size, decode, List.flatMap_append]

private theorem recurrence (s : List Tile) :
    size (expand (expand (expand s))) = 2 * size (expand s) + 2 * size s := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    have h : size (expand (expand (expand [t]))) = 2 * size (expand [t]) + 2 * size [t] := by
      cases t <;> decide
    have app (u v : List Tile) : expand (u ++ v) = expand u ++ expand v := List.flatMap_append
    change size (expand (expand (expand ([t] ++ s)))) = 2 * size (expand ([t] ++ s)) + 2 * size ([t] ++ s)
    simp only [app, add_size]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a287439.main := by
  intro n
  rw [encode_word]
  change size (orbit n) = reference n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 => decide
    | n+3 =>
      exact (recurrence (orbit n)).trans (by
        change 2 * size (orbit (n+1)) + 2 * size (orbit n) = 2 * reference (n+1) + 2 * reference n
        rw [ih (n+1) (by omega), ih n (by omega)])
