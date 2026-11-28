import OMAStatements.S_oeis_a288622

/-!
# Proof of OEIS A288622

We prove that for every `n : ℕ`, `(word n).length = a288465 n`.

Proof outline:
1. Define the three block types `B1 := [true]`, `B2 := [false, true]`, `B3 := [false, false, true]`
   and their encodings `encode : List (Fin 3) → List Bool` followed by a trailing `[false]`.
2. Define the block morphism `step : List (Fin 3) → List (Fin 3)` sending
   `0 ↦ [1]`, `1 ↦ [2]`, `2 ↦ [1, 0, 2]`.
   By induction on the block list, `scan (encode bs ++ [false]) = encode (step bs) ++ [false]`,
   since `scan` on `[false, false, true] ++ w` gives `[false, true, true, false] ++ scan ([true] ++ w)
   = [false, true, true, false, false, true] ++ scan w`.
3. Thus `word (n + 1) = encode (step^[n] [1, 0]) ++ [false]`.
4. Track the triple of block counts `(c1 n, c2 n, c3 n)` of `step^[n] [1, 0]`:
   `(c1 (n + 1), c2 (n + 1), c3 (n + 1)) = (c3 n, c1 n + c3 n, c2 n + c3 n)`.
   The word length is `L n = c1 n + 2 * c2 n + 3 * c3 n + 1`, which satisfies
   `L (n + 4) = 2 * L (n + 3) - L n` and agrees with `a288465 (n + 1)` on `n = 0, 1, 2, 3`.
-/

namespace OMA.A288622Proof

open OMA.S_oeis_a288622

private def block : Fin 3 → List Bool
  | ⟨0, _⟩ => [true]
  | ⟨1, _⟩ => [false, true]
  | ⟨2, _⟩ => [false, false, true]

private def encode : List (Fin 3) → List Bool
  | [] => []
  | b :: bs => block b ++ encode bs

private def stepBlock : Fin 3 → List (Fin 3)
  | ⟨0, _⟩ => [1]
  | ⟨1, _⟩ => [2]
  | ⟨2, _⟩ => [1, 0, 2]

private def step : List (Fin 3) → List (Fin 3)
  | [] => []
  | b :: bs => stepBlock b ++ step bs

private lemma encode_append (a b : List (Fin 3)) :
    encode (a ++ b) = encode a ++ encode b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [encode, ih, List.append_assoc]

private lemma scan_encode (bs : List (Fin 3)) :
    scan (encode bs ++ [false]) = encode (step bs) ++ [false] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨v, hv⟩
    interval_cases v
    · simp only [encode, block, step, stepBlock, List.cons_append, List.nil_append, scan]
      rw [ih]
    · simp only [encode, block, step, stepBlock, List.cons_append, List.nil_append, scan]
      rw [ih]
    · simp only [encode, block, step, stepBlock, List.cons_append, List.nil_append, scan]
      rw [ih]

private def seq : ℕ → List (Fin 3)
  | 0 => [1, 0]
  | n + 1 => step (seq n)

private lemma word_succ (n : ℕ) :
    word (n + 1) = encode (seq n) ++ [false] := by
  induction n with
  | zero => decide
  | succ n ih =>
    change scan (word (n + 1)) = encode (step (seq n)) ++ [false]
    rw [ih, scan_encode]

private def c1 (bs : List (Fin 3)) : ℕ := bs.count (0 : Fin 3)
private def c2 (bs : List (Fin 3)) : ℕ := bs.count (1 : Fin 3)
private def c3 (bs : List (Fin 3)) : ℕ := bs.count (2 : Fin 3)

private lemma encode_length (bs : List (Fin 3)) :
    (encode bs).length = c1 bs + 2 * c2 bs + 3 * c3 bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rcases b with ⟨v, hv⟩
    interval_cases v <;>
      simp [encode, block, c1, c2, c3, ih] <;> omega

private lemma counts_step (bs : List (Fin 3)) :
    c1 (step bs) = c3 bs ∧
    c2 (step bs) = c1 bs + c3 bs ∧
    c3 (step bs) = c2 bs + c3 bs := by
  induction bs with
  | nil => decide
  | cons b bs ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    simp only [c1, c2, c3] at h1 h2 h3
    rcases b with ⟨v, hv⟩
    interval_cases v <;>
      simp [step, stepBlock, c1, c2, c3] <;> omega

private lemma len_rec (n : ℕ) :
    (word (n + 5)).length + (word (n + 1)).length = 2 * (word (n + 4)).length := by
  have hlen : ∀ m, (word (m + 1)).length = c1 (seq m) + 2 * c2 (seq m) + 3 * c3 (seq m) + 1 := by
    intro m
    rw [word_succ, List.length_append, encode_length]
    rfl
  rw [hlen (n + 4), hlen n, hlen (n + 3)]
  have s0 := counts_step (seq n)
  have s1 := counts_step (seq (n + 1))
  have s2 := counts_step (seq (n + 2))
  have s3 := counts_step (seq (n + 3))
  change c1 (seq (n + 1)) = c3 (seq n) ∧
    c2 (seq (n + 1)) = c1 (seq n) + c3 (seq n) ∧
    c3 (seq (n + 1)) = c2 (seq n) + c3 (seq n) at s0
  change c1 (seq (n + 2)) = c3 (seq (n + 1)) ∧
    c2 (seq (n + 2)) = c1 (seq (n + 1)) + c3 (seq (n + 1)) ∧
    c3 (seq (n + 2)) = c2 (seq (n + 1)) + c3 (seq (n + 1)) at s1
  change c1 (seq (n + 3)) = c3 (seq (n + 2)) ∧
    c2 (seq (n + 3)) = c1 (seq (n + 2)) + c3 (seq (n + 2)) ∧
    c3 (seq (n + 3)) = c2 (seq (n + 2)) + c3 (seq (n + 2)) at s2
  change c1 (seq (n + 4)) = c3 (seq (n + 3)) ∧
    c2 (seq (n + 4)) = c1 (seq (n + 3)) + c3 (seq (n + 3)) ∧
    c3 (seq (n + 4)) = c2 (seq (n + 3)) + c3 (seq (n + 3)) at s3
  omega

theorem result : type_of% @OMA.S_oeis_a288622.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | 3 => decide
    | 4 => decide
    | m + 5 =>
      have hrec := len_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih4 := ih (m + 4) (by omega)
      have ha : a288465 (m + 5) = 2 * a288465 (m + 4) - a288465 (m + 1) := rfl
      omega

end OMA.A288622Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a288622.main := OMA.A288622Proof.result
