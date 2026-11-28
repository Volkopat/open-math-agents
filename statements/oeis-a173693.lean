import Mathlib

/-!
# A173693: a(n) = ceiling(A107293(n)/2).

Source: https://oeis.org/A173693

Conjecture in the entry (R. J. Mathar, Feb 18 2016):
a(n) = a(n-1) + a(n-2) - a(n-3) + a(n-5) + a(n-31) - a(n-32) - a(n-33) + a(n-34) - a(n-36).

Formalization notes:
* Offset 0, for this sequence and for A107293. The data begin 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3, 5.
* A107293 is the sequence 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 9, ... attached to the 5 X 5 matrix
  M = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1],[1,0,-1,1,1]]. Here `b n` is defined
  exactly as the matrix program listed in A173693 computes it: v(0) = (0,0,0,0,1),
  v(n) = M v(n-1), and b(n) is the first component of v(n), that is, of M^n v(0). This agrees
  with the data of A107293 and with the recurrence b(n) = b(n-1) + b(n-2) - b(n-3) + b(n-5),
  b(0..4) = 0, 0, 0, 0, 1, stated in A107293 and used by the other program listed in A173693.
* The name of A107293 calls it the (1,1)-entry of M^n. Read literally at offset 0 that entry
  starts 1, 0, 0, 0, 0, 1, 1, 2, which is the data shifted by one place (the (1,1)-entry of
  M^(n+1) is the first component of M^n v(0)). The definition follows the data and the
  programs, since the literal reading would give a(0) = 1 against the data of A173693.
* The ceiling is taken in the rationals (`Int.ceil` of b(n)/2), so `a n` is an integer.
* The entry states no range for n. The recurrence is claimed for n ≥ 36, the least range in
  which every index n-1, ..., n-36 is at least the offset 0; the natural-number subtractions
  in the statement are then exact.
-/

namespace OMA.S_oeis_a173693

/-- The 5 X 5 integer matrix of A107293. -/
def M : Matrix (Fin 5) (Fin 5) ℤ :=
  !![0, 1, 0, 0, 0;
     0, 0, 1, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1;
     1, 0, -1, 1, 1]

/-- A107293: b(n) is the first component of M^n v, where v = (0, 0, 0, 0, 1). -/
def b (n : ℕ) : ℤ := ((M ^ n).mulVec ![0, 0, 0, 0, 1]) 0

/-- A173693: a(n) = ceiling(A107293(n)/2). -/
def a (n : ℕ) : ℤ := ⌈(b n : ℚ) / 2⌉

/-- Mathar's conjecture on A173693: the linear recurrence of order 36, for n ≥ 36. -/
theorem main :
    ∀ n : ℕ, 36 ≤ n →
      a n = a (n - 1) + a (n - 2) - a (n - 3) + a (n - 5) + a (n - 31) - a (n - 32)
        - a (n - 33) + a (n - 34) - a (n - 36) := by
  sorry

end OMA.S_oeis_a173693
