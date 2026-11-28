import Mathlib

/-!
# A347684: Array read by antidiagonals: T(n,k) (n>=1, k>=1) = f(n,k), where f(x,y) = x*red_inv(x,y) + y*red_inv(y,x) if gcd(x,y)=1, or 0 if gcd(x,y)>1, and red_inv is defined in the comments.

Source: https://oeis.org/A347684
Credit: @agchua

Comment line of A347684 (the entry is by N. J. A. Sloane, Sep 18 2021):
  Conjecture: The entries of this array can be expressed in terms of A347683 and A347687 as
  follows. Write k = j*n+i, where j >= 0 and 1 <= i <= n. Then
  T(n,k) = A347683(n,i) + 2*n*j*A347687(n,i).
The array has n, k >= 1, and the claim is stated for every n >= 1, j >= 0, 1 <= i <= n.
Definitions, as in the entries (comments and Maple programs of A347683, A347684, A347687):
* u^(-1) mod v is the residue r in 0..v-1 with u*r == 1 (mod v); `invMod u v` is the least
  such r in 0..v-1 (it is unique when gcd(u,v) = 1, and it is 0 for v = 1, as in Maple).
* red_inv(u,v) is u^(-1) mod v if 2*(u^(-1) mod v) <= v, otherwise v - u^(-1) mod v.
* f(x,y) = x*red_inv(x,y) + y*red_inv(y,x) if gcd(x,y) = 1, and 0 otherwise.
* A347684(n,k) = f(n,k) (array, n, k >= 1) and A347683(n,k) = f(n,k) (triangle, 1 <= k <= n).
* A347687(n,k) = (r(n+k) - r(k))/(2*n), 1 <= k <= n, where r is row n of A347684; the
  division is the integer division, which reproduces the listed terms of A347687.
-/

namespace OMA.S_oeis_a347684

/-- u^(-1) mod v: the least r in 0..v-1 with u*r == 1 (mod v), and 0 if there is none. -/
def invMod (u v : ℕ) : ℕ := ((List.range v).find? (fun r => u * r % v == 1 % v)).getD 0

/-- The reduced inverse red_inv(u,v) of u mod v. -/
def redInv (u v : ℕ) : ℕ := if v < 2 * invMod u v then v - invMod u v else invMod u v

/-- f(x,y) = x*red_inv(x,y) + y*red_inv(y,x) if gcd(x,y) = 1, and 0 otherwise. -/
def f (x y : ℕ) : ℕ := if Nat.gcd x y = 1 then x * redInv x y + y * redInv y x else 0

/-- A347684(n,k) = f(n,k), n, k >= 1. -/
def A347684 (n k : ℕ) : ℕ := f n k

/-- A347683(n,k) = f(n,k), 1 <= k <= n. -/
def A347683 (n k : ℕ) : ℕ := f n k

/-- A347687(n,k) = (A347684(n,n+k) - A347684(n,k))/(2n), 1 <= k <= n. -/
def A347687 (n k : ℕ) : ℤ := ((A347684 n (n + k) : ℤ) - A347684 n k) / (2 * n)

/-- The conjecture: for n >= 1 and k = j*n + i with j >= 0 and 1 <= i <= n,
T(n,k) = A347683(n,i) + 2*n*j*A347687(n,i). -/
theorem main : ∀ n j i : ℕ, 1 ≤ n → 1 ≤ i → i ≤ n →
    (A347684 n (j * n + i) : ℤ) = A347683 n i + 2 * n * j * A347687 n i := by
  sorry

end OMA.S_oeis_a347684
