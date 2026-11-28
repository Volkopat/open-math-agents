import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.List.Count

/-!
# Even denominators in an infinite Farey row (OEIS A078008)

Start with the adjacent endpoints 0/1 and 1/1. In each gap insert the
mediant and split the gap in two. Row n consists of the 2ⁿ newly inserted
fractions, so the first row contains just 1/2. Denominators are taken in
lowest terms. The coefficient sequence of (1-x)/((1+x)(1-2x)) is defined
from its recurrence and its first two coefficients.

Gary W. Adamson conjectured the equality in 2003.
Source: https://oeis.org/A078008
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a078008

abbrev Fraction := ℕ × ℕ
abbrev Gap := Fraction × Fraction

def mediant (g : Gap) : Fraction := (g.1.1+g.2.1, g.1.2+g.2.2)

def children (g : Gap) : List Gap := [(g.1,mediant g),(mediant g,g.2)]

def gaps : ℕ → List Gap
  | 0 => [((0,1),(1,1))]
  | n+1 => (gaps n).flatMap children

def evenDen (f : Fraction) : Bool :=
  (f.2 / f.1.gcd f.2) % 2 == 0

def fareyCount (n : ℕ) := (gaps n).countP (fun g => evenDen (mediant g))

def a : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | n+2 => a (n+1)+2*a n

theorem main : ∀ n : ℕ, a n = fareyCount n := by
  sorry

end OMA.S_oeis_a078008
