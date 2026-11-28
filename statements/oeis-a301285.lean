import Mathlib

/-!
# A301285. Coordination sequence at a V2 vertex of the car net

Source: https://oeis.org/A301285
Credit: @Aryan-Poonacha

The adjacency list and root are from Rémy Sigrist's program
https://oeis.org/A301285/a301285.gp.txt. Coordinates index translates
of the fundamental cell. Increasing x moves right and increasing y moves up.
-/

namespace OMA.S_oeis_a301285

inductive Site where
  | A | B | C | D | E | F | G | H | I | J | K | L
  deriving DecidableEq

abbrev Vertex := ℤ × ℤ × Site

def neighbors : Vertex → Finset Vertex
  | (x,y,.A) => {(x,y+1,.L), (x,y,.B), (x-1,y,.C)}
  | (x,y,.B) => {(x,y,.A), (x,y,.C), (x,y,.D)}
  | (x,y,.C) => {(x+1,y,.A), (x,y,.B), (x,y,.E)}
  | (x,y,.D) => {(x,y,.B), (x,y,.F), (x-1,y,.E)}
  | (x,y,.E) => {(x,y,.C), (x+1,y,.D), (x,y,.F)}
  | (x,y,.F) => {(x,y,.D), (x,y,.E), (x,y,.G)}
  | (x,y,.G) => {(x,y,.F), (x,y,.H), (x,y,.I)}
  | (x,y,.H) => {(x,y,.G), (x-1,y,.I), (x,y,.J)}
  | (x,y,.I) => {(x,y,.G), (x+1,y,.H), (x,y,.K)}
  | (x,y,.J) => {(x,y,.H), (x,y,.L), (x,y,.K)}
  | (x,y,.K) => {(x,y,.I), (x,y,.J), (x+1,y,.L)}
  | (x,y,.L) => {(x,y-1,.A), (x,y,.J), (x-1,y,.K)}

def ball : ℕ → Finset Vertex
  | 0 => {(0,0,.A)}
  | n+1 => let S := ball n; S ∪ S.biUnion neighbors

def a : ℕ → ℤ
  | 0 => 1
  | n+1 => ((ball (n+1)).card : ℤ) - (ball n).card

/-- Colin Barker's generating function and recurrence of March 30, 2018. -/
def conjecture : Prop :=
  let S := PowerSeries.mk a
  let X : PowerSeries ℤ := PowerSeries.X
  S * ((1-X)^2*(1+X^2)^2*(1+X+X^2)) =
    1+2*X+5*X^2+7*X^3+7*X^4+7*X^5+5*X^6+2*X^7+X^8 ∧
  (∀ n : ℕ, 8 < n → a n = a (n-1)-2*a (n-2)+3*a (n-3)-2*a (n-4)+
    3*a (n-5)-2*a (n-6)+a (n-7)-a (n-8))

theorem main : conjecture := by sorry

end OMA.S_oeis_a301285
