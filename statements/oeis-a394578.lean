import Mathlib

/-!
# A394578: a(n) = 2^(2*n-1) * p(n, n+1/2), where p(n,x) is the Lagrange interpolating polynomial through (1,0) and (k,1) for k=2..n+1.

Source: https://oeis.org/A394578
Credit: @agchua

The comment lines of A394578 state two conjectures:
  Conjecture: a(n+1)/a(n) -> 1/4.
  Conjecture D-finite with recurrence n*a(n) +2*(-2*n+1)*a(n-1) +16*(-n+3)*a(n-2)
  +32*(2*n-7)*a(n-3)=0. - R. J. Mathar, Jun 30 2026
Both are stated below, as one conjunction.
Here p n is Mathlib's `Lagrange.interpolate` on the nodes i+1 (i = 0..n), with value 0 at
the node 1 and value 1 at the nodes 2..n+1: the polynomial of degree at most n through (1,0)
and (k,1), k = 2..n+1. The power 2^(2n-1) has an integer exponent (it is 1/2 for n = 0,
where p 0 = 0, so a(0) = 0 as in the data). The sequence has offset 0. The limit is read
in ℝ; for n = 0 the quotient divides by a(0) = 0, which does not affect a limit. The
recurrence uses a(n-3), so it is stated for n ≥ 3.
-/

namespace OMA.S_oeis_a394578

/-- p(n,x): the Lagrange interpolating polynomial through (1,0) and (k,1) for k = 2..n+1. -/
noncomputable def p (n : ℕ) : Polynomial ℝ :=
  Lagrange.interpolate (Finset.range (n + 1)) (fun i : ℕ => (i : ℝ) + 1)
    (fun i : ℕ => if i = 0 then (0 : ℝ) else 1)

/-- A394578(n) = 2^(2n-1) p(n, n+1/2). -/
noncomputable def a (n : ℕ) : ℝ := (2 : ℝ) ^ (2 * (n : ℤ) - 1) * (p n).eval ((n : ℝ) + 1 / 2)

/-- The two conjectures of A394578: a(n+1)/a(n) tends to 1/4, and Mathar's recurrence
n a(n) + 2(-2n+1) a(n-1) + 16(-n+3) a(n-2) + 32(2n-7) a(n-3) = 0 for n ≥ 3. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => a (n + 1) / a n) Filter.atTop (nhds (1 / 4)) ∧
    ∀ n : ℕ, 3 ≤ n →
      (n : ℝ) * a n + 2 * (-2 * (n : ℝ) + 1) * a (n - 1) + 16 * (-(n : ℝ) + 3) * a (n - 2)
        + 32 * (2 * (n : ℝ) - 7) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a394578
