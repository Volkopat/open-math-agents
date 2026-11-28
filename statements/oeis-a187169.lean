import Mathlib

/-!
# A187169, 8-site self-avoiding walks in dimension 3

The first row of the source table A187162 counts a single visited vertex.
Thus its row 8 uses 7 nearest-neighbor moves. Start at the origin and exclude
every step to a previously visited vertex. After h distinct coordinate axes
have appeared, the first use of a fresh axis represents 2*(3−h) choices:
a signed coordinate permutation can make it the next positive axis.
The multiplicity is carried along the recursion. Different oriented walks,
including reversals when distinct, are counted as in the original problem.

A shape with coordinate spans eᵢ has ∏ᵢ max(n−eᵢ,0) placements in the box,
by independent translation in each coordinate. This is Robert Israel's
bounding-box observation on the related source table A188784. The target
states the published generating function and recurrence coefficientwise.

Sources: https://oeis.org/A187169 and https://oeis.org/A187162
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a187169

abbrev Point := ℤ × ℤ × ℤ
abbrev Span := ℕ × ℕ × ℕ
abbrev Profile := ℕ × Span

def coord (p : Point) : ℕ → ℤ
  | 0 => p.1
  | 1 => p.2.1
  | _ => p.2.2

def move (p : Point) (u : ℤ) : ℕ → Point
  | 0 => (p.1+u,p.2.1,p.2.2)
  | 1 => (p.1,p.2.1+u,p.2.2)
  | _ => (p.1,p.2.1,p.2.2+u)

def extent (seen : List Point) (i : ℕ) : ℕ :=
  let lo := seen.foldl (fun a p => min a (coord p i)) 0
  let hi := seen.foldl (fun a p => max a (coord p i)) 0
  (hi-lo).toNat

def enumerate : ℕ → ℕ → ℕ → Point → List Point → List Profile
  | 0, _, w, _, seen => [(w,extent seen 0,extent seen 1,extent seen 2)]
  | m+1, h, w, p, seen =>
    let next := fun (h' w' : ℕ) (q : Point) =>
      if q ∈ seen then [] else enumerate m h' w' q (q::seen)
    let old := (List.range h).flatMap fun i =>
      next h w (move p 1 i) ++ next h w (move p (-1) i)
    old ++ (if h < 3 then next (h+1) (w*2*(3-h)) (move p 1 h) else [])

def shapes : List Profile :=
  enumerate 7 0 1 (0,0,0) [(0,0,0)]

def placed (n : ℕ) (w : Profile) : ℤ :=
  (w.1 : ℤ) * ((n-w.2.1 : ℕ) : ℤ) * ((n-w.2.2.1 : ℕ) : ℤ) * ((n-w.2.2.2 : ℕ) : ℤ)

def sequence (n : ℕ) : ℤ := (shapes.map (placed n)).sum
def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 2 then 144 else if n = 3 then 67248 else if n = 4 then 338496 else if n = 5 then 159264 else if n = 6 then -72960 else if n = 7 then -15840 else if n = 8 then 8976 else if n = 9 then 2796 else if n = 10 then 216 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 4*lag 1 n + 6*lag 2 n - 4*lag 3 n + lag 4 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+11) = 4*sequence (k+10) - 6*sequence (k+9) + 4*sequence (k+8) - sequence (k+7)) := by
  sorry

end OMA.S_oeis_a187169
