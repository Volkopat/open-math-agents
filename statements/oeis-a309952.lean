import Mathlib

/-!
# OEIS A309952: k first occurs in the XOR contraction sequence at index A000695(k)

Source: https://oeis.org/A309952 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (2019), offset 0: XOR contraction of binary representation of n. Comment: To calculate a(n)
write down the binary representation of n. Organize the digits in pairs and calculate the xor of
these pairs. The result is a(n) in binary. Example: for n=19 we have the binary representation
10011 = 01 00 11, the xor of the pairs gives 1 0 0, so a(19) = 4. Comment: Conjecture: The index
of the first occurrence of k in a is A000695(k). - Ivan N. Ianakiev, Aug 26 2019.
A000695 is the Moser-de Bruijn sequence (sums of distinct powers of 4, offset 0); its entry
describes it as 2[n]4, n written in base 2 and read in base 4.

Formalization notes:
* `Nat.digits 2 n` lists the binary digits of n from the least significant one. The pairs are
  formed from that end, and an odd number of digits gets a leading 0, as in the example and in
  the entry's programs; the XOR of a lone last digit b with 0 is b.
* A000695(k) is `Nat.ofDigits 4 (Nat.digits 2 k)`, the binary digits of k read in base 4.
* `main` says, for every k: a(A000695(k)) = k and a(m) differs from k for every m < A000695(k).
* Controls proved in the proof file: a(19) = 4, a(0..15) as in the entry, A000695(0..5) =
  0, 1, 4, 5, 16, 17.
-/

namespace OMA.S_oeis_a309952

/-- Replace each pair of consecutive digits, starting from the least significant one, by their
XOR; a last unpaired digit is paired with a leading 0. -/
def pairXor : List ℕ → List ℕ
  | [] => []
  | [b] => [b]
  | b₀ :: b₁ :: rest => (b₀ ^^^ b₁) :: pairXor rest

/-- a(n): the XOR contraction of the binary representation of n. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 2 (pairXor (Nat.digits 2 n))

/-- A000695(k): k written in base 2 and read in base 4 (the Moser-de Bruijn sequence). -/
def mdb (k : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 2 k)

/-- Ianakiev's conjecture: the first occurrence of k in A309952 is at index A000695(k). -/
theorem main : ∀ k : ℕ, a (mdb k) = k ∧ ∀ m < mdb k, a m ≠ k := by
  sorry

end OMA.S_oeis_a309952
