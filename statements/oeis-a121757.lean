import Mathlib

/-!
# A121757: Triangle read by rows: multiply Pascal's triangle by 1,2,6,24,120,720,... = A000142.

Source: https://oeis.org/A121757 (the array D: https://oeis.org/A253938)
Credit: @agchua

Roger Ford (May 19 2016), comment line of A121757, quoted verbatim:
  a(n,k) = D(n+1,k+1) Array D in A253938 is part of a conjectured formula for F(n,p,r) that
  relates Dyck path peaks and returns.  a(n,k) was discovered prior to array D.
The claim stated here is the identity a(n,k) = D(n+1,k+1); the conjectured formula for F(n,p,r)
of A253938 is only named in the comment as the place where D occurs.

Definitions.
* A121757 (offset 0, rows n >= 0, 0 <= k <= n), from its formula line
  a(n,k) = A007318(n,k)*A000142(k+1) (R. J. Mathar): a(n,k) = binomial(n,k) * (k+1)!.
* The coefficient array D(p,r) of A253938, 1 <= r <= p, from the formula lines of A253938:
  D(p,1) = 1, D(p,p) = r! (= p!), and D(p,r) = r*D(p-1,r-1) + D(p-1,r) otherwise
  (1 < r < p); its displayed rows are 1; 1, 2!; 1, 4, 3!; 1, 6, 18, 4!; 1, 8, 36, 96, 5!.
  The Lean function below is defined for all p, r; for 1 <= r <= p it follows exactly these
  rules (the third rule only calls D(p-1, r-1) and D(p-1, r) with 1 <= r-1 < r <= p-1), and its
  values outside 1 <= r <= p are not used by the statement.
The identity is stated for every row n >= 0 and every 0 <= k <= n, so that 1 <= k+1 <= n+1.
-/

namespace OMA.S_oeis_a121757

/-- A121757: a(n, k) = binomial(n, k) * (k+1)!. -/
def a (n k : ℕ) : ℕ := Nat.choose n k * Nat.factorial (k + 1)

/-- The array D(p, r) of A253938: D(p,1) = 1, D(p,p) = p!, D(p,r) = r*D(p-1,r-1) + D(p-1,r). -/
def D : ℕ → ℕ → ℕ
  | 0, _ => 0
  | p + 1, r =>
    if r = 1 then 1
    else if r = p + 1 then Nat.factorial (p + 1)
    else r * D p (r - 1) + D p r

/-- Roger Ford's claim: a(n,k) = D(n+1,k+1) for 0 <= k <= n. -/
theorem main : ∀ n k : ℕ, k ≤ n → a n k = D (n + 1) (k + 1) := by
  sorry

end OMA.S_oeis_a121757
