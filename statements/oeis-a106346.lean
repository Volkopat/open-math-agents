import Mathlib

/-!
# A106346: Inverse of number triangle A106344.

Source: https://oeis.org/A106346
Credit: @agchua

Comment line of A106346 (no author given):
  Rows sums are A036987 (conjecture).

A106344 (name line): Triangle read by rows: T(n,k) = binomial(k,n-k) mod 2, offset 0, 0 <= k <= n.
As an infinite matrix A106344 is lower triangular with ones on the diagonal, so its inverse A106346
is lower triangular too, and for k <= n the entry (n, k) of the inverse is the entry (n, k) of the
inverse of the leading (n+1) x (n+1) block. A036987 is the Fredholm-Rueppel sequence, offset 0,
with formula line a(n) = 1 iff n = 2^m - 1, that is, iff n + 1 is a power of 2. The claim is
stated for every row n >= 0.
-/

namespace OMA.S_oeis_a106346

/-- A106344: T(n, k) = binomial(k, n - k) mod 2 for k <= n, and 0 above the diagonal. -/
def T (n k : ℕ) : ℕ := if k ≤ n then Nat.choose k (n - k) % 2 else 0

/-- The leading (N+1) x (N+1) block of A106344 as a rational matrix. -/
def block (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  Matrix.of fun i j => (T i.val j.val : ℚ)

/-- A106346(n, k) for 0 <= k <= n: the entry (n, k) of the inverse of the leading block of
size n + 1 of A106344. -/
noncomputable def S (n k : ℕ) : ℚ :=
  if h : k ≤ n then (block n)⁻¹ (Fin.last n) ⟨k, Nat.lt_succ_of_le h⟩ else 0

open Classical in
/-- A036987 (Fredholm-Rueppel sequence): a(n) = 1 if n + 1 is a power of 2, otherwise 0. -/
noncomputable def A036987 (n : ℕ) : ℕ := if ∃ m : ℕ, n + 1 = 2 ^ m then 1 else 0

/-- The conjecture: for every n >= 0, the sum of row n of A106346 is A036987(n). -/
theorem main : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), S n k = (A036987 n : ℚ) := by
  sorry

end OMA.S_oeis_a106346
