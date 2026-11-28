import Mathlib

/-!
# The Thue–Morse run lengths

The lengths of successive runs in the Thue–Morse word form A026465.
John W. Layman described this word as the fixed point obtained by iterating
`1 → 121`, `2 → 12221` on `1`. Alexander Povolotsky conjectured that it contains
infinitely many distinct palindromic subsequences. Michel Dekking proved both
claims in the entry using the second iterate of the Thue–Morse substitution.

The equality of the two infinite words is stated as equality of their finite
prefixes. Even Thue–Morse stages exhaust the infinite word. Dropping the last
run at each finite stage ensures that every retained run ends at a change of bit.
Over a finite alphabet, infinitely many distinct finite palindromes is equivalent
to the existence of palindromes of unbounded length.

Source: https://oeis.org/A026465 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a026465

def tau (s : List Bool) : List Bool := s.flatMap fun b => [b,!b]

def thueStage : ℕ → List Bool
  | 0 => [false]
  | n+1 => tau (thueStage n)

def runAux (b : Bool) (m : ℕ) : List Bool → List ℕ
  | [] => [m]
  | c::cs => if b=c then runAux b (m+1) cs else m :: runAux c 1 cs

def runLengths : List Bool → List ℕ
  | [] => []
  | b::bs => runAux b 1 bs

def runPrefix (r : List ℕ) : Prop :=
  ∃ k : ℕ, r <+: (runLengths (thueStage (2*k))).dropLast

def alpha : ℕ → List ℕ
  | 1 => [1,2,1]
  | 2 => [1,2,2,2,1]
  | _ => []

def runStage : ℕ → List ℕ
  | 0 => [1]
  | n+1 => (runStage n).flatMap alpha

theorem main :
    (∀ r : List ℕ, runPrefix r ↔ ∃ k : ℕ, r <+: runStage k) ∧
    (∀ m : ℕ, ∃ p r : List ℕ, m ≤ p.length ∧ p.reverse = p ∧ runPrefix r ∧ p.Sublist r) := by
  sorry

end OMA.S_oeis_a026465
