import Mathlib

/-!
# A371113, Conjecture 3 of M. F. Hasler

Source: https://oeis.org/A371113 (20 April 2024).
Credit: Robert Leshner (@rleshner).

At index n an unconstrained entry is the least nonnegative integer missing
from the n previous entries, so is at most n. Fix a target triple k and put
L = 3k+1. Every first or second entry through that pair is therefore at most L.
The state records the least unused value a and exactly those earlier third
entries at most L. All earlier first and second entries are below a. Choosing
the first two unmarked values a,b thus uses every value through b. Among
values b < c ≤ L we insert the least unused decimal palindrome completion,
if one exists. If none exists, the actual third entry exceeds L and leaves
the bounded set unchanged. A completion always exists in the original
unbounded process: arbitrarily many positive center digits consisting of
ones can be placed between the prefix and its reversal. This proves the
simulation invariant by induction, starting with a=0 and no earlier terms.

For a prefix word P of width w and a proposed suffix of width j ≤ w,
write P = U V, with U of width j. The concatenation is a palindrome exactly
when the suffix is reverse(U) and V is a palindrome. The final digit of U
must be nonzero to give a canonical suffix of width j: zero itself has
already been used. Hence there is at most one candidate at each width and
shortThird tries them in increasing order. The least possible suffix of
width w+1 is the digit 1 followed by reverse(P), since its first digit
occupies the center. From that value onwards scan tests integers directly.
All reversals use explicit widths, including the initial prefix 01.
-/
namespace OMA.S_oeis_a371113

/-- Append the reversed, zero-padded, width-w decimal expansion of n to acc. -/
def reverseInto : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | w+1, n, acc => reverseInto w (n/10) (10*acc + n%10)

/-- Decimal width, counting zero as one digit. -/
def countDigits : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel+1, n => if n < 10 then 1 else countDigits fuel (n/10) + 1

def width (n : ℕ) : ℕ := countDigits n n

/-- Try the possible completion widths up to the length of the prefix.
For each width j, the only possible suffix is the reverse of the first j
digits. The remaining digits of the prefix must form a palindrome. -/
def shortThird (b used limit : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Option ℕ
  | 0, _, _, _, _ => none
  | n+1, rem, place, suffix, power =>
    let d := rem / place
    let r := rem % place
    let c := d * power + suffix
    if d != 0 && b < c && c ≤ limit && !(used.testBit c) &&
        r == reverseInto n r 0 then some c
    else shortThird b used limit n r (place/10) c (10*power)

/-- Exhaustive fallback giving precisely the least available palindrome
completion in [start, limit]. Check at most fuel successive integers. -/
def scan (p w used : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | c, fuel+1 =>
    let v := p * 10^(width c) + c
    if !(used.testBit c) && v == reverseInto (w+width c) v 0 then some c
    else scan p w used (c+1) fuel

/-- Insert the least usable third entry into the finite bitmap if it lies
within the bound. Among longer completions the first is decimal 1 followed
by the whole reversed prefix. -/
def addThird (limit used a b : ℕ) : ℕ :=
  let p := a * 10^(width b) + b
  let w := width a + width b
  match shortThird b used limit w p (10^(w-1)) 0 1 with
  | some c => used ||| (1 <<< c)
  | none =>
    let c := reverseInto w p 0 + 10^w
    if c > limit then used
    else
      match scan p w used (max c (b+1)) (limit+1-max c (b+1)) with
      | some z => used ||| (1 <<< z)
      | none => used

/-- Choose the next unused entry at or above x. All first and second entries
already chosen are strictly below x. The fallback after fuel skips exceeds
the bound, where there are no marked entries. -/
def next (used : ℕ) : ℕ → ℕ → ℕ
  | x, 0 => x
  | x, fuel+1 => if used.testBit x then next used (x+1) fuel else x

def advance (limit : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  let b := next s.2 (s.1+1) (limit+1)
  let used := addThird limit s.2 s.1 b
  (next used (b+1) (limit+1), used)

def run (limit : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, s => s
  | k+1, s => run limit k (advance limit s)

def firstPair (k : ℕ) : ℕ × ℕ :=
  let limit := 3*k+1
  let s := run limit k (0,0)
  (s.1, next s.2 (s.1+1) (limit+1))

theorem main : ∀ k : ℕ, (firstPair k).2 - (firstPair k).1 = 1 ∨
    (firstPair k).2 - (firstPair k).1 = 2 := by
  sorry

end OMA.S_oeis_a371113
