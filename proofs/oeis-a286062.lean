import OMAStatements.S_oeis_a286062
import Mathlib

open OMA.S_oeis_a286062

/-- The scan consumes one of these three input blocks. -/
private inductive Block where
  | zeroZero
  | zeroOne
  | one
  deriving DecidableEq

private def letters : Block → List Bool
  | .zeroZero => [false,false]
  | .zeroOne => [false,true]
  | .one => [true]

private def replaceBlock : Block → List Block
  | .zeroZero => [.zeroZero,.one]
  | .zeroOne => [.zeroZero,.one,.one]
  | .one => [.zeroOne,.one]

private def encode (bs : List Block) : List Bool := bs.flatMap letters
private def advance (bs : List Block) : List Block := bs.flatMap replaceBlock

private theorem rewrite_blocks (bs : List Block) :
    rewrite (encode bs) = encode (advance bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b <;>
      simp only [encode,advance,List.flatMap_cons,letters,replaceBlock,List.cons_append,
        List.nil_append,rewrite] at ih ⊢ <;>
      rw [ih]

private def blocks : ℕ → List Block
  | 0 => [.zeroZero]
  | n+1 => advance (blocks n)

private theorem word_blocks (n : ℕ) : word n = encode (blocks n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [word,blocks,ih,rewrite_blocks]

private def tally (target : Block) : List Block → ℤ
  | [] => 0
  | b::bs => (if b=target then 1 else 0) + tally target bs

private def c0 (bs : List Block) : ℤ := tally .zeroZero bs
private def c1 (bs : List Block) : ℤ := tally .zeroOne bs
private def c2 (bs : List Block) : ℤ := tally .one bs

private theorem advance_cons (b : Block) (bs : List Block) :
    advance (b::bs) = replaceBlock b ++ advance bs := rfl

private theorem counts (bs : List Block) :
    c0 (advance bs) = c0 bs+c1 bs ∧
    c1 (advance bs) = c2 bs ∧
    c2 (advance bs) = c0 bs+2*c1 bs+c2 bs := by
  induction bs with
  | nil => decide +kernel
  | cons b bs ih =>
    simp only [c0,c1,c2] at ih
    cases b <;> simp [c0,c1,c2,advance_cons,replaceBlock,tally] <;> omega

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

private theorem length_recurrence (n : ℕ) :
    ((word (n+3)).length : ℤ) =
      2*((word (n+2)).length : ℤ) + 1*((word (n+1)).length : ℤ) - 1*((word n).length : ℤ) := by
  have h0 := counts (blocks n)
  have h1 := counts (blocks (n+1))
  have h2 := counts (blocks (n+2))
  change c0 (blocks (n+1)) = _ ∧ c1 (blocks (n+1)) = _ ∧ c2 (blocks (n+1)) = _ at h0
  change c0 (blocks (n+2)) = _ ∧ c1 (blocks (n+2)) = _ ∧ c2 (blocks (n+2)) = _ at h1
  change c0 (blocks (n+3)) = _ ∧ c1 (blocks (n+3)) = _ ∧ c2 (blocks (n+3)) = _ at h2
  simp only [word_blocks,enc_length]
  linarith only [h0.1,h0.2.1,h0.2.2,h1.1,h1.2.1,h1.2.2,h2.1,h2.2.1,h2.2.2]

theorem OMA.solution : type_of% @OMA.S_oeis_a286062.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n < 3
    · interval_cases n <;> decide +kernel
    · obtain ⟨j,rfl⟩ : ∃ j, n=j+3 := ⟨n-3,by omega⟩
      rw [length_recurrence,ih (j+2) (by omega),ih (j+1) (by omega),ih j (by omega),reference]