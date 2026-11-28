import OMAStatements.S_oeis_a288317

open OMA.S_oeis_a288317


private inductive Tile where
  | a | b | c | d

private def bits : Tile → List Bool
  | .a => [false, false, false, true, false, false]
  | .b => [false, false, false, false, true]
  | .c => [false, true, false, false]
  | .d => [false, false, false, false, false, false, true]

private def morph : Tile → List Tile
  | .a => [.a, .b]
  | .b => [.a, .c]
  | .c => [.d]
  | .d => [.a, .c, .c]

private def expand (s : List Tile) := s.flatMap morph
private def decode (s : List Tile) := s.flatMap bits


private theorem commute (s : List Tile) (v : List Bool) :
    rewrite (decode s ++ v) = decode (expand s) ++ rewrite v := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    have h (u : List Bool) : rewrite (bits t ++ u) = decode (morph t) ++ rewrite u := by
      cases t <;> rfl
    simpa only [expand, decode, List.flatMap_cons, List.flatMap_append, List.append_assoc] using
      (h (decode s ++ v)).trans (congrArg (decode (morph t) ++ ·) ih)

private def orbit : ℕ → List Tile
  | 0 => [.a]
  | n+1 => expand (orbit n)

private theorem encode_word (n : ℕ) : word (n+2) = decode (orbit n) ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg rewrite ih).trans (commute _ _)

private def size (s : List Tile) : ℤ := (decode s).length

private theorem add_size (s t : List Tile) : size (s ++ t) = size s + size t := by
  simp [size, decode, List.flatMap_append]


private theorem length_word (n : ℕ) : ((word (n+2)).length : ℤ) = size (orbit n) + 1 := by
  simp [encode_word, size]

private def lengthAt : ℕ → List Tile → ℤ
  | 0, s => size s
  | n+1, s => lengthAt n (expand s)

private theorem length_add (k : ℕ) (s t : List Tile) :
    lengthAt k (s ++ t) = lengthAt k s + lengthAt k t := by
  induction k generalizing s t with
  | zero => exact add_size _ _
  | succ k ih => exact ((congrArg (lengthAt k) (List.flatMap_append (f := morph) (xs := s) (ys := t)))).trans (ih (expand s) (expand t))

set_option maxRecDepth 8192 in
private theorem recurrence (s : List Tile) : lengthAt 5 s =
    lengthAt 4 s + 3 * lengthAt 3 s - 2 * lengthAt 2 s - lengthAt 1 s := by
  induction s with
  | nil => rfl
  | cons t s ih =>
    have h : lengthAt 5 [t] = lengthAt 4 [t] + 3 * lengthAt 3 [t] - 2 * lengthAt 2 [t] - lengthAt 1 [t] := by
      cases t <;> decide
    change lengthAt 5 ([t] ++ s) = _
    change _ = lengthAt 4 ([t] ++ s) + 3 * lengthAt 3 ([t] ++ s) - 2 * lengthAt 2 ([t] ++ s) - lengthAt 1 ([t] ++ s)
    simp only [length_add]
    omega

theorem OMA.solution : type_of% @OMA.S_oeis_a288317.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => decide
    | n+7 =>
      rw [length_word (n+5), reference]
      have h1 := ih (n+3) (by omega)
      have h2 := ih (n+4) (by omega)
      have h3 := ih (n+5) (by omega)
      have h4 := ih (n+6) (by omega)
      rw [length_word (n+1)] at h1
      rw [length_word (n+2)] at h2
      rw [length_word (n+3)] at h3
      rw [length_word (n+4)] at h4
      have hr :=  recurrence (orbit n)
      change size (orbit (n+5)) = size (orbit (n+4)) + 3 * size (orbit (n+3)) - 2 * size (orbit (n+2)) - size (orbit (n+1)) at hr
      change size (orbit (n+5)) + 1 = reference (n+6) + 3 * reference (n+5) - 2 * reference (n+4) - reference (n+3)
      omega


