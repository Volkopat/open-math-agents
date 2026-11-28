import Mathlib

/-!
# A112971: row sums of the square of the Catalan Riordan array, mod 2

Source: https://oeis.org/A112971
Credit: @avivorly

Definition (%N): Row sums of the matrix ((1,xc(x))^2 mod 2), where c(x) is the g.f. of A000108.

Comment (%C, verbatim): (1,xc(x)) is the Riordan array T(n,k)=[x^n](xc(x))^k.
Conjectures: a(2^n)=a(2^(n+1)+1)=A005578(n);a(2^n-1)=a(3*2^n-1)=1.

A005578 (%N): a(2*n) = 2*a(2*n-1), a(2*n+1) = 2*a(2*n)-1 (offset 0, first term a(0) = 1;
data 1, 1, 2, 3, 6, 11, 22, 43, ...).

Conventions:
- `c` is the ordinary generating function of the Catalan numbers A000108,
  `c = Σ catalan n * x^n`, as a formal power series over `ℕ`.
- `M n k = [x^n] (x c(x))^k` is the Riordan array `(1, x c(x))` of the comment. It is lower
  triangular (`M n k = 0` for `k > n`).
- `M2 n k = Σ_{j=0..n} M n j * M j k` is the `(n, k)` entry of the matrix square. Stopping the sum
  at `j = n` is exact, since `M n j = 0` for `j > n`.
- `a n = Σ_{k=0..n} (M2 n k mod 2)`: the square is reduced mod 2 entrywise and row `n` is summed
  (entries with `k > n` vanish). Offset 0. This reproduces the listed terms
  1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 2, 2, 1, 6, 3, 4, 2, ... (all listed terms were checked with a
  computable twin built from the ballot numbers `M n k = k/(2n-k) * C(2n-k, n)`).
- `A005578` is defined by the entry's own %N recurrence with `a(0) = 1`; it agrees with the entry's
  %F `a(n) = ceiling(2^n/3) = 1 + floor(2^n/3)`.
- The conjectures are read for every `n ≥ 0`, with natural subtraction (`2^n - 1 = 0` at `n = 0`).
  Small cases against the data, `n = 0..4`:
  a(1) = a(3) = 1 = A005578(0); a(2) = a(5) = 1 = A005578(1); a(4) = a(9) = 2 = A005578(2);
  a(8) = a(17) = 3 = A005578(3); a(16) = a(33) = 6 = A005578(4);
  a(0) = a(1) = a(3) = a(7) = a(15) = 1 and a(2) = a(5) = a(11) = a(23) = a(47) = 1.
-/

namespace OMA.S_oeis_a112971

/-- The g.f. `c(x) = Σ catalan n * x^n` of the Catalan numbers A000108, over `ℕ`. -/
noncomputable def c : PowerSeries ℕ := PowerSeries.mk catalan

/-- The Riordan array `(1, x c(x))`: `M n k = [x^n] (x c(x))^k`. -/
noncomputable def M (n k : ℕ) : ℕ := PowerSeries.coeff n ((PowerSeries.X * c) ^ k)

/-- The `(n, k)` entry of the matrix square `M * M` (exact, since `M n j = 0` for `j > n`). -/
noncomputable def M2 (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), M n j * M j k

/-- A112971: the row sums of the matrix square reduced mod 2 entrywise. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), M2 n k % 2

/-- A005578, by its %N: `a(2n) = 2 a(2n-1)`, `a(2n+1) = 2 a(2n) - 1`, with `a(0) = 1`. -/
def A005578 : ℕ → ℕ
  | 0 => 1
  | n + 1 => if n % 2 = 0 then 2 * A005578 n - 1 else 2 * A005578 n

theorem main :
    ∀ n : ℕ, a (2 ^ n) = A005578 n ∧ a (2 ^ (n + 1) + 1) = A005578 n ∧
      a (2 ^ n - 1) = 1 ∧ a (3 * 2 ^ n - 1) = 1 := by
  sorry

end OMA.S_oeis_a112971
