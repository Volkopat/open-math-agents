import Mathlib.Data.List.Basic

/-! Clark Kimberling's printed prefix-length conjecture in OEIS A308355.
Row n of A128628 lists lengths of the partitions of n in decreasing
lexicographic order; the source displays row 1 as [1]. A025065 counts
partitions whose parts can be arranged as a palindrome. Comparing row n
with the limiting row means that its common-prefix length with row m has
the stated value for every sufficiently large m. The n+1 in the target
is the index printed in the conjecture.
Sources: https://oeis.org/A308355, https://oeis.org/A128628, https://oeis.org/A025065 -/

namespace OMA.S_oeis_a308355

/-- Partitions of the remaining total with a part-size cap and a length cap.
    For total n, an initial length cap n includes every positive-part partition. -/
def parts : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, total, _ => if total = 0 then [[]] else []
  | fuel+1, total, cap =>
    if total = 0 then [[]] else
      (List.range (min total cap)).reverse.flatMap fun j =>
        (parts fuel (total-(j+1)) (j+1)).map (fun tail => (j+1)::tail)

def row (n : ℕ) : List ℕ := (parts n n n).map List.length

def palCount (n : ℕ) : ℕ :=
  ((parts n n n).filter fun xs =>
    (xs.eraseDups.filter fun d => xs.count d % 2 == 1).length ≤ 1).length

def common : List ℕ → List ℕ → ℕ
  | a::xs, b::ys => if a = b then 1 + common xs ys else 0
  | _, _ => 0

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    common (row n) (row m) = palCount (n+1) := by
  sorry

end OMA.S_oeis_a308355
