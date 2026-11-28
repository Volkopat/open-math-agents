import Mathlib

/-!
# Jacobsthal membership for every term of OEIS A102396

Source: https://oeis.org/A102396
Comparison sequence: https://oeis.org/A001045
Credit: @Heart-galaxy

Both sequences have offset 0. A102396 conjectures that all of its terms are
Jacobsthal numbers. Barry confirmed this on January 7, 2005 by identifying
a(n) with the Jacobsthal number at the binary digit weight of n.

We define the sequence independently using Cloitre's source recurrence:
a(0)=0, a(2*n)=a(n), a(2*n+1)=2*a(n)+1-2*t(n), where t is the Thue-Morse
sequence, namely the parity of the number of binary 1-digits. Nat.binaryRec
implements these two cases exactly. The separate weight recursion counts
1-digits, so weight(n) modulo 2 is the specified t(n). The recurrence is
written in the integers to preserve its ordinary signed subtraction.

J is the canonical Jacobsthal sequence: J(0)=0, J(1)=1,
J(n+2)=J(n+1)+2*J(n), also written in the integers. The theorem states
membership only; the stronger identifying formula is not assumed as a definition.
-/

namespace OMA.S_oeis_a102396

def weight (n : ℕ) : ℕ :=
  Nat.binaryRec (motive := fun _ => ℕ) 0 (fun b _ r => if b then r+1 else r) n

def a (n : ℕ) : ℤ :=
  Nat.binaryRec (motive := fun _ => ℤ) 0
    (fun b n r => if b then 2*r+1-2*((weight n % 2 : ℕ) : ℤ) else r) n

def J : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n+2 => J (n+1) + 2*J n


theorem main : ∀ n : ℕ, ∃ k : ℕ, a n = J k := by
  sorry

end OMA.S_oeis_a102396
