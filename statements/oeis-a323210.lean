import Mathlib

/-!
# Four-row pattern avoidance and the shifted Jacobsthal squares

A208556 counts four-row binary arrays that avoid 000 and 001 horizontally
and avoid 001 and 011 vertically. We enumerate their columns. Colin Barker's
shift conjecture identifies the count at width n with A323210(n+1), for
every n ≥ 1. At the positive indices used here A323210(k) = 9 J(k)^2,
where J is the ordinary Jacobsthal sequence.

Sources: https://oeis.org/A323210 and https://oeis.org/A208556
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a323210

-- The bits two rows apart cannot form (0,1). Each such pair is therefore
-- represented by 0=(0,0), 1=(1,0), or 2=(1,1). These two pairs constitute
-- the four rows, in the order (row 1,row 3) and (row 2,row 4).
abbrev PairState := Fin 3
abbrev Column := PairState × PairState

def pairOK (a b : PairState) : Bool :=
  ((a != 0) || (b != 0)) && ((a == 2) || (b == 2))

-- A horizontal 00 can only occur at the final pair of positions, since
-- either possible third bit would make a forbidden triple.
def completions : ℕ → Column → ℕ
  | 0, _ => 1
  | 1, _ => Fintype.card Column
  | m+2, p => ∑ a : PairState, ∑ b : PairState,
      if pairOK p.1 a && pairOK p.2 b then completions (m+1) (a,b) else 0

-- An all-ones predecessor places no restriction on the first column.
def arrays (n : ℕ) : ℕ := completions n (2,2)

def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => jacobsthal (n+1) + 2*jacobsthal n

theorem main : ∀ n : ℕ, 1 ≤ n → arrays n = 9*(jacobsthal (n+1))^2 := by
  sorry

end OMA.S_oeis_a323210
