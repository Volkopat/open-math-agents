import OMAStatements.S_oeis_a287381
import Mathlib

open OMA.S_oeis_a287381

private inductive Block where
  | zeroZero
  | zeroOne
  | one
  deriving DecidableEq

private def letters : Block → List Bool
  | .zeroZero => [false,false]
  | .zeroOne => [false,true]
  | .one => [true]

private def encode (bs : List Block) : List Bool := bs.flatMap letters

private def core : Block → List Bool
  | .zeroZero => [false,false,true]
  | .zeroOne => [false,true]
  | .one => [true]

private def emit (b : Block) : List Bool := core b ++ [false]

private def trailing (q : Bool) : List Bool := if q then [false] else []

private theorem rewrite_encoded (bs : List Block) (q : Bool) :
    rewrite (encode bs ++ trailing q) = bs.flatMap emit ++ trailing q := by
  induction bs with
  | nil => cases q <;> rfl
  | cons b bs ih =>
    cases b <;>
      simp only [encode,List.flatMap_cons,letters,emit,core,List.cons_append,List.nil_append,rewrite] at ih ⊢ <;>
      rw [ih]

/-- Move the final zero of each block to the start of the next block. -/
private def moved : Block → List Block
  | .zeroZero => [.zeroZero,.zeroOne]
  | .zeroOne => [.zeroZero,.one]
  | .one => [.zeroOne]

private def advance (bs : List Block) : List Block := bs.flatMap moved

private theorem encode_shift (bs : List Block) :
    false :: bs.flatMap emit = encode (advance bs) ++ [false] := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;>
      simp only [advance,encode,List.flatMap_cons,letters,moved,emit,core,List.cons_append,
        List.nil_append] at ih ⊢ <;>
      rw [← ih]

private def spill (q : Bool) : List Block := if q then [.zeroZero] else []

private theorem one_step (bs : List Block) (q : Bool) :
    rewrite (encode (.zeroZero::bs) ++ trailing q) =
      encode (.zeroZero::.one::(advance bs++spill q)) ++ trailing (!q) := by
  rw [rewrite_encoded]
  change [false,false,true] ++ (false::bs.flatMap emit) ++ trailing q = _
  rw [encode_shift]
  cases q <;>
    simp [encode,letters,spill,trailing,List.flatMap_append,List.append_assoc]

private def state : ℕ → List Block × Bool
  | 0 => ([],false)
  | n+1 =>
    let s := state n
    (.one::(advance s.1 ++ spill s.2),!s.2)

private theorem word_state (n : ℕ) :
    word n = encode (.zeroZero::(state n).1) ++ trailing (state n).2 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [word,ih,one_step,state]

private def tally (target : Block) : List Block → ℤ
  | [] => 0
  | b::bs => (if b=target then 1 else 0) + tally target bs

private def c0 (bs : List Block) : ℤ := tally .zeroZero bs
private def c1 (bs : List Block) : ℤ := tally .zeroOne bs
private def c2 (bs : List Block) : ℤ := tally .one bs

private theorem tally_append (b : Block) (xs ys : List Block) :
    tally b (xs++ys) = tally b xs + tally b ys := by
  induction xs with
  | nil => simp [tally]
  | cons x xs ih => simp [tally,ih,add_assoc]

private theorem advance_cons (b : Block) (bs : List Block) :
    advance (b::bs) = moved b ++ advance bs := rfl

private theorem counts (bs : List Block) :
    c0 (advance bs) = c0 bs+c1 bs ∧ c1 (advance bs) = c0 bs+c2 bs ∧
    c2 (advance bs) = c1 bs := by
  induction bs with
  | nil => decide +kernel
  | cons b bs ih =>
    simp only [c0,c1,c2] at ih
    cases b <;> simp [c0,c1,c2,advance_cons,moved,tally] <;> omega

private theorem enc_length (bs : List Block) :
    ((encode bs).length : ℤ) = 2*c0 bs + 2*c1 bs + c2 bs := by
  induction bs with
  | nil => decide +kernel
  | cons b bs ih =>
    have hsplit : (encode (b::bs)).length = (letters b).length + (encode bs).length := by
      change (letters b ++ encode bs).length = _
      rw [List.length_append]
    rw [hsplit,Nat.cast_add,ih]
    cases b <;> simp [letters,c0,c1,c2,tally] <;> omega

private def bitWeight (q : Bool) : ℤ := if q then 1 else 0
private def A (n : ℕ) : ℤ := c0 (state n).1
private def B (n : ℕ) : ℤ := c1 (state n).1
private def C (n : ℕ) : ℤ := c2 (state n).1
private def Q (n : ℕ) : ℤ := bitWeight (state n).2

private theorem state_counts (n : ℕ) :
    A (n+1) = A n+B n+Q n ∧ B (n+1) = A n+C n ∧
    C (n+1) = B n+1 ∧ Q (n+1) = 1-Q n := by
  have h := counts (state n).1
  unfold A B C Q
  rw [state]
  simp only [c0,c1,c2] at h ⊢
  cases e : (state n).2 <;> simp [spill,tally,tally_append,bitWeight] <;> omega

private theorem word_length (n : ℕ) :
    ((word n).length : ℤ) = 2+2*A n+2*B n+C n+Q n := by
  rw [word_state,List.length_append,Nat.cast_add,enc_length]
  unfold A B C Q
  cases e : (state n).2 <;> simp [trailing,bitWeight,c0,c1,c2,tally] <;> omega

private theorem length_recurrence (n : ℕ) :
    ((word (n+3)).length : ℤ) =
      ((word (n+2)).length : ℤ) + 2*((word (n+1)).length : ℤ) - ((word n).length : ℤ) := by
  have h0 := state_counts n
  have h1 := state_counts (n+1)
  have h2 := state_counts (n+2)
  simp only [word_length]
  linarith only [h0.1,h0.2.1,h0.2.2.1,h0.2.2.2,h1.1,h1.2.1,h1.2.2.1,h1.2.2.2,
    h2.1,h2.2.1,h2.2.2.1,h2.2.2.2]

theorem OMA.solution : type_of% @OMA.S_oeis_a287381.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 3
    · interval_cases n <;> decide +kernel
    · obtain ⟨j,rfl⟩ : ∃ j, n=j+3 := ⟨n-3,by omega⟩
      rw [length_recurrence,ih (j+2) (by omega),ih (j+1) (by omega),ih j (by omega),reference]
      ring