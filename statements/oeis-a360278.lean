import Mathlib

/-!
# A360278: determinants det[v(j+k) + d(j,k)] for Lucas-type sequences

Source: https://oeis.org/A360278 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A360278, offset 1: Determinant of the matrix [L(j+k) + d(j,k)]_{1<=j, k<=n}, where L(n)
denotes the Lucas number A000032(n), and d(j,k) is 1 or 0 according as j = k or not. Data
4, 16, 44, 121, 319, 841, 2204, 5776, 15124, 39601, 103679, 271441, 710644, ...

Comments:
Conjecture 1: Let v(0) = 2, v(1) = A, and v(n+1) = A*v(n) + v(n-1) for n > 0. Then
A^2*det[v(j+k) + d(j,k)]_{1<=j, k<=n} = v(n+1)^2 - (A^2 + 4)*(n mod 2) for any positive integer
n. In particular, a(n) = L(n+1)^2 - 5*(n mod 2) for all n > 0.
Conjecture 2: Let v(0) = 2, v(1) = A, and v(n+1) = A*v(n) - v(n-1) for n > 0. Then
det[v(j+k) + d(j,k)]_{1<=j, k<=n} = u(n+1)^2 - n^2 for any positive integer n, where u(0) = 0,
u(1) = 1, and u(n+1) = A*u(n) - u(n-1) for all n > 0.
Conjecture 3: Let F(n) denote the Fibonacci number A000045(n). Then, for any positive integer
n, we have det[F(j+k) + d(j,k)]_{1<=j, k<=n} = F(n+1)^2 + (n mod 2).

Formalization notes.
* A is an arbitrary integer. `vP A` and `vM A` are the sequences v of Conjectures 1 and 2,
  and `uM A` is the sequence u of Conjecture 2. The Lucas numbers are `vP 1` (2, 1, 3, 4, 7, ...),
  and the Fibonacci numbers are `Nat.fib`.
* `D f n` is the determinant of the n X n integer matrix with the entries f(j+k) + d(j,k) for
  1 <= j, k <= n (the indices of `Fin n` are shifted by 1). The sequence is a(n) = D (vP 1) n.
* `main` is the conjunction of Conjecture 1, its special case for the Lucas numbers,
  Conjecture 2 and Conjecture 3, each for all n > 0.
-/

namespace OMA.S_oeis_a360278

/-- v(0) = 2, v(1) = A, v(n+1) = A v(n) + v(n-1) (the Lucas numbers for A = 1). -/
def vP (A : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => A
  | n + 2 => A * vP A (n + 1) + vP A n

/-- v(0) = 2, v(1) = A, v(n+1) = A v(n) - v(n-1). -/
def vM (A : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => A
  | n + 2 => A * vM A (n + 1) - vM A n

/-- u(0) = 0, u(1) = 1, u(n+1) = A u(n) - u(n-1). -/
def uM (A : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => A * uM A (n + 1) - uM A n

/-- det [f(j+k) + d(j,k)] for 1 ≤ j, k ≤ n, where d(j,k) is 1 or 0 according as j = k or not. -/
def D (f : ℕ → ℤ) (n : ℕ) : ℤ :=
  (Matrix.of fun (j k : Fin n) => f (((j : ℕ) + 1) + ((k : ℕ) + 1)) + if j = k then 1 else 0).det

/-- Conjectures 1, 2 and 3 of A360278. The sequence is a(n) = D (vP 1) n. -/
theorem main :
    (∀ (A : ℤ) (n : ℕ), 0 < n →
      A ^ 2 * D (vP A) n = vP A (n + 1) ^ 2 - (A ^ 2 + 4) * ((n % 2 : ℕ) : ℤ)) ∧
    (∀ n : ℕ, 0 < n → D (vP 1) n = vP 1 (n + 1) ^ 2 - 5 * ((n % 2 : ℕ) : ℤ)) ∧
    (∀ (A : ℤ) (n : ℕ), 0 < n → D (vM A) n = uM A (n + 1) ^ 2 - (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 0 < n →
      D (fun m => (Nat.fib m : ℤ)) n = (Nat.fib (n + 1) : ℤ) ^ 2 + ((n % 2 : ℕ) : ℤ)) := by
  sorry

end OMA.S_oeis_a360278
