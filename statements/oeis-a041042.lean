import Mathlib

/-!
# OEIS A041042 and Lehmer's sequence A002316

Sources: https://oeis.org/A041042 and https://oeis.org/A002316.
Credit: @etaubman

The simple continued fraction of sqrt(27) is [5; 5, 10, 5, 10, ...].
The first two numerators are 5 and 26. From any consecutive pair (x,y)
at indices 4k, 4k+1, the next two are x+10y and 5x+51y. Two further
steps give 51x+520y and 260x+2651y, starting the next block.

For A002316 we use the twelve signed initial terms and the order-12
recurrence given in its OEIS entry. Both sequences have offset zero.
-/

namespace OMA.S_oeis_a041042

def block : Nat → Nat × Nat
  | 0 => (5, 26)
  | k + 1 =>
    let p := block k
    (51 * p.1 + 520 * p.2, 260 * p.1 + 2651 * p.2)

def weights : Nat → Nat × Nat
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (1, 10)
  | _ => (5, 51)

def part (r k : Nat) : Nat :=
  (weights r).1 * (block k).1 + (weights r).2 * (block k).2

def numerator (n : Nat) : Nat := part (n % 4) (n / 4)

def beta : Nat → Int
  | 0 => 1
  | 1 => 5
  | 2 => 26
  | 3 => 97
  | 4 => 265
  | 5 => 362
  | 6 => -1351
  | 7 => -13775
  | 8 => -70226
  | 9 => -262087
  | 10 => -716035
  | 11 => -978122
  | n + 12 => -2702 * beta (n + 6) - beta n

theorem main : ∀ n : Nat, ∃ m : Nat, (numerator n : Int) = |beta m| := by
  sorry

end OMA.S_oeis_a041042
