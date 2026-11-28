import Mathlib

/-!
# A181271, three binary rows ordered before and after taking the Gram matrix

Read each matrix by columns. Each adjacent pair of input rows is still tied,
or its strictly increasing order was fixed by an earlier column. The Gram
matrix of the prefix is symmetric, with six parity bits in the order
00,01,02,11,12,22. Still-tied input rows have equal Gram rows and columns.
This gives two all-tied states, eight of each singly-tied kind, and 64
fully separated states. Each 3-bit column updates the Gram matrix by its
outer product over the field with two elements. A decreasing first difference
in the input row order is discarded. The terminal condition compares the
three actual Gram rows lexicographically in increasing order.

The generating function is stated after multiplying by its degree-seven
denominator. The recurrence has Barker's original range n>9.

Source: https://oeis.org/A181271
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a181271

abbrev State := Fin 82
def bit (v i : ℕ) : ℕ := v / 2^i % 2

/-- Bit zero marks a strict comparison of rows 0 and 1. Bit one does so for rows 1 and 2. -/
def flags (s : State) : ℕ :=
  if s.val < 2 then 0 else if s.val < 10 then 2 else if s.val < 18 then 1 else 3

def gram (s : State) : ℕ :=
  if s.val < 2 then 63*s.val
  else if s.val < 10 then
    let h := s.val-2
    11*bit h 0 + 20*bit h 1 + 32*bit h 2
  else if s.val < 18 then
    let h := s.val-10
    bit h 0 + 6*bit h 1 + 56*bit h 2
  else s.val-18

def encode (f g : ℕ) : State :=
  let q := if f = 0 then bit g 0 else if f = 2 then
    2 + bit g 0 + 2*bit g 2 + 4*bit g 5
    else if f = 1 then 10 + bit g 0 + 2*bit g 1 + 4*bit g 5 else 18+g
  ⟨q%82, Nat.mod_lt _ (by decide)⟩

def step (s : State) (c : Fin 8) : Option State :=
  let a := bit c.val 2
  let b := bit c.val 1
  let d := bit c.val 0
  let f := flags s
  if (bit f 0 = 0 ∧ b < a) ∨ (bit f 1 = 0 ∧ d < b) then none
  else
    let f' := (if bit f 0 = 1 ∨ a < b then 1 else 0) +
      (if bit f 1 = 1 ∨ b < d then 2 else 0)
    some (encode f' (Nat.xor (gram s) (a + 2*a*b + 4*a*d + 8*b + 16*b*d + 32*d)))

def finalCount (s : State) : ℤ :=
  let g := gram s
  let r₀ := 4*bit g 0 + 2*bit g 1 + bit g 2
  let r₁ := 4*bit g 1 + 2*bit g 3 + bit g 4
  let r₂ := 4*bit g 2 + 2*bit g 4 + bit g 5
  if flags s = 3 ∧ r₀ < r₁ ∧ r₁ < r₂ then 1 else 0

def nextValue (v : State → ℤ) (s : State) (c : Fin 8) : ℤ :=
  match step s c with
  | none => 0
  | some t => v t

def advance (v : State → ℤ) (s : State) : ℤ :=
  ∑ c : Fin 8, nextValue v s c

def completions : ℕ → State → ℤ
  | 0 => finalCount
  | n+1 => advance (completions n)

def sequence (n : ℕ) : ℤ := completions n 0
def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 3 then 6 else if n = 4 then 3 else if n = 5 then -272 else if n = 6 then 444 else if n = 7 then 832 else if n = 8 then -960 else if n = 9 then -512 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 14*lag 1 n + 36*lag 2 n + 216*lag 3 n - 1056*lag 4 n + 384*lag 5 n + 3584*lag 6 n - 4096*lag 7 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+10) = 14*sequence (k+9) - 36*sequence (k+8) - 216*sequence (k+7) + 1056*sequence (k+6) - 384*sequence (k+5) - 3584*sequence (k+4) + 4096*sequence (k+3)) := by
  sorry

end OMA.S_oeis_a181271
