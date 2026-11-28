import Mathlib

/-!
# Three-color knight graphs on two-column arrays (OEIS A208428)

Colors are introduced as 0, 1, 2 in row-major order. Thus the possible
first rows are 00 and 01. Once 1 has appeared, all three colors are
available. A knight move in two columns changes row by two and column by
one, so each new cell must differ from the opposite cell two rows above.
The forward enumeration retains one boundary per valid array prefix,
including multiplicities when different arrays have the same boundary.

Colin Barker conjectured the ordinary generating function and closed form
in February 2018. The empirical recurrence is also given in the entry.
Sources: https://oeis.org/A208428
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a208428
open PowerSeries

abbrev Color := Fin 3
abbrev Row := Color × Color

structure Boundary where
  previous : Option Row
  current : Row
  seenOne : Bool
  deriving DecidableEq

def colors : List Color := [0,1,2]
def rows : List Row := colors.flatMap fun l => colors.map fun r => (l,r)

def allowed (b : Boundary) (r : Row) : Bool :=
  let ordered := (b.seenOne || r.1 != 2) && (b.seenOne || r.1 == 1 || r.2 != 2)
  let knight := match b.previous with
    | none => true
    | some old => r.1 != old.2 && r.2 != old.1
  ordered && knight

def extend (b : Boundary) : List Boundary :=
  ((rows.filter (allowed b)).map fun r =>
    ⟨some b.current,r,b.seenOne || r.1 == 1 || r.2 == 1⟩)

def boundaries : ℕ → List Boundary
  | 0 => [⟨none,(0,0),false⟩,⟨none,(0,1),true⟩]
  | n+1 => (boundaries n).flatMap extend

def a : ℕ → ℕ
  | 0 => 0
  | n+1 => (boundaries n).length

theorem main :
    (∀ n : ℕ, a (n+4)=4*a (n+3)) ∧
    ((1-4*X)*(PowerSeries.mk (fun n => (a n : ℚ))) = 2*X*(1+3*X-X^2)) ∧
    ∀ n : ℕ, a (n+3)=27*2^(2*n+1) := by
  sorry

end OMA.S_oeis_a208428
