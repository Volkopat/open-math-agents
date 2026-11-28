import Mathlib

/-!
# A333905, the lexicographically first sequence with a concatenation divisor

The first term is indexed by one. The history is stored in reverse order.
Choose the least positive unused term that makes the last required decimal
divisibility hold. This greedy construction is the lexicographic minimum:
every finite eligible prefix can be extended. In fact, for last terms a,b one
may choose a sufficiently large decimal width d, and among a consecutive
d-digit integers above every used value one meets the residue −b*10^d mod a.

The second conjecture is Barker's homogeneous recurrence on its stated range.
Spezia's closed form is given by its equivalent two parity cases, obtained by
using (−1)^n and simplifying the half-integral powers of two.

Source: https://oeis.org/A333905
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a333905

def joinDecimal (x y : ℕ) : ℕ := x * 10^(Nat.log 10 y) * 10 + y

def eligible (h : List ℕ) (y : ℕ) : Bool :=
  decide (0 < y) && !(h.contains y) &&
    match h with
    | b::a::_ => decide (a ∣ joinDecimal b y)
    | _ => true

noncomputable def leastNext (h : List ℕ) : ℕ := sInf {y : ℕ | eligible h y = true}

noncomputable def history : ℕ → List ℕ
  | 0 => []
  | n+1 => leastNext (history n) :: history n

noncomputable def sequence (n : ℕ) : ℤ := ((history n).headD 0 : ℤ)
noncomputable def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ :=
  if n=1 then 1 else if n=2 then 2 else if n=3 then 1 else if n=5 then -1
  else if n=6 then -2 else if n=8 then -4 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 2*lag 2 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+7) = 2*sequence (k+5)) ∧
    (∀ k : ℕ, sequence (2*k+7) = 10*(2:ℤ)^k ∧
      sequence (2*k+8) = 8*(2:ℤ)^k) := by
  sorry

end OMA.S_oeis_a333905
