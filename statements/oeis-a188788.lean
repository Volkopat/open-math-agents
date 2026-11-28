import Mathlib

/-!
# A188788, 5-site self-avoiding walks in a four-dimensional box

The original table A188784 counts a single visited grid vertex in row one
(n^4 possibilities) and an oriented grid edge in row two. Hence row 5
has 5 visited vertices and 4 unit moves. Enumerate the walks from the origin,
discarding every return to a previously visited vertex. An axis first used
can be made the next positive coordinate axis by a signed coordinate
permutation. If h axes are already used, it represents 2*(4−h) actual
extensions. Both directions of each previously used axis remain available.

For a walk shape with coordinate spans d₁,...,d₄, exactly
∏ᵢ max(n−dᵢ,0) integer translations fit in the box. This is the argument
of Robert Israel in https://oeis.org/A188784.

The generating function is stated after multiplying by its denominator.
Index zero has coefficient zero because the OEIS sequence starts at one.

Source: https://oeis.org/A188788
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a188788

abbrev Point := ℤ × ℤ × ℤ × ℤ

def coord (p : Point) : ℕ → ℤ
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | _ => p.2.2.2

def shift (p : Point) (u : ℤ) : ℕ → Point
  | 0 => (p.1+u,p.2.1,p.2.2.1,p.2.2.2)
  | 1 => (p.1,p.2.1+u,p.2.2.1,p.2.2.2)
  | 2 => (p.1,p.2.1,p.2.2.1+u,p.2.2.2)
  | _ => (p.1,p.2.1,p.2.2.1,p.2.2.2+u)

def translations (n : ℕ) (visited : List Point) : ℕ :=
  (Finset.range 4).prod fun i =>
    let low := visited.foldl (fun a p => min a (coord p i)) 0
    let high := visited.foldl (fun a p => max a (coord p i)) 0
    ((n : ℤ) - (high-low)).toNat

def extend (n : ℕ) : ℕ → ℕ → Point → List Point → ℕ
  | 0, _, _, visited => translations n visited
  | m+1, h, p, visited =>
    let next := fun (h' : ℕ) (q : Point) =>
      if q ∈ visited then 0 else extend n m h' q (q :: visited)
    let old := (Finset.range h).sum fun i => next h (shift p 1 i) + next h (shift p (-1) i)
    old + (if h < 4 then 2*(4-h)*next (h+1) (shift p 1 h) else 0)

def sequence (n : ℕ) : ℤ := (extend n 4 0 (0,0,0,0) [(0,0,0,0)] : ℤ)

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 2 then 1536 else if n = 3 then 31728 else if n = 4 then 36048 else if n = 5 then -7016 else if n = 6 then 2440 else if n = 7 then 184 else if n = 8 then -216 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 5*lag 1 n + 10*lag 2 n - 10*lag 3 n + 5*lag 4 n - lag 5 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+8) = 5*sequence (k+7) - 10*sequence (k+6) + 10*sequence (k+5) - 5*sequence (k+4) + sequence (k+3)) := by
  sorry

end OMA.S_oeis_a188788
