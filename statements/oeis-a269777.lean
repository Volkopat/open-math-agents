import Mathlib

/-!
# OEIS A269777, adjacent repeated letters in five-letter words

Source: https://oeis.org/A269777 (R. H. Hardin; conjectures of Colin Barker).
Credit: @Mapika

Scan adjacent pairs from left to right, recording the letter of each equal pair.
No letter on this list may be the cyclic successor of the preceding letter.
The length-five word is written as an ordered five-tuple. The ordinary generating
function starts at index one, as in the entry. Its rational expression is stated
coefficientwise by multiplying by `(1-X)^6`, whose constant term is one. The
coefficients of `6X(4+13X+2X^2+X^3)` are 24, 78, 12 and 6 in degrees 1 to 4.
-/
namespace OMA.S_oeis_a269777

abbrev Letter (n : ℕ) := Fin (n+1)
abbrev Word (n : ℕ) := Letter n × Letter n × Letter n × Letter n × Letter n

def repeated {n : ℕ} (w : Word n) : List (Letter n) :=
  let (a,b,c,d,e) := w
  (if a=b then [a] else []) ++ (if b=c then [b] else []) ++
    (if c=d then [c] else []) ++ (if d=e then [d] else [])

def Valid {n : ℕ} (w : Word n) : Prop := (repeated w).IsChain (fun x y => y ≠ x+1)

noncomputable def a (n : ℕ) : ℕ := Nat.card {w : Word n // Valid w}

noncomputable def c (j : ℤ) : ℤ := if 0 < j then a j.toNat else 0

noncomputable def conv (j : ℤ) : ℤ :=
  c j - 6*c (j-1) + 15*c (j-2) - 20*c (j-3) + 15*c (j-4) - 6*c (j-5) + c (j-6)

theorem main :
    (∀ j : ℕ, conv j = match j with | 1 => 24 | 2 => 78 | 3 => 12 | 4 => 6 | _ => 0) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6*a (n-1) - 15*a (n-2) + 20*a (n-3) - 15*a (n-4) +
      6*a (n-5) - a (n-6) := by
  sorry

end OMA.S_oeis_a269777
