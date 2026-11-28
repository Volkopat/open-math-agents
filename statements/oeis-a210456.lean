import Mathlib

/-!
# OEIS A210456: period of the digital roots of Fibonacci n-step numbers

The sequence starts from the seed 0,...,0,1 (n-1 zeros then a single 1);
each next term is the digital root (A010888) of the sum of the previous
n terms. The sequence is eventually periodic and a(n) is the length of
its period. The sliding window of n terms is a vector `Fin n → ℕ`;
`vinit n` is the seed, `vstep n` shifts left and injects the digital
root of the window sum, `seqN n k` is the head of the window at time k,
and `a210456 n` is the least positive eventual period (`sInf`).

The statement recorded here is the conjunction of the two conjectures
in the OEIS comments: every entry `a(n) > 1` is divisible by 3, and the
Helenius formulas `a(3^n - 1) = 3^(2n+1) - 3` and
`a(3^n) = 3^(2n+1) + 3^(n+1) + 3` for `n ≥ 1`.

Source: https://oeis.org/A210456
-/

namespace OMA.S_oeis_a210456

/-- Digital root (A010888): `0` if `m = 0`, else `(m - 1) % 9 + 1`,
the unique element of `{1,...,9}` congruent to `m` modulo 9. -/
def digitalRoot (m : ℕ) : ℕ := if m = 0 then 0 else (m - 1) % 9 + 1

/-- The OEIS seed `(0,...,0,1)`: `n - 1` zeros then a single `1`. -/
def vinit (n : ℕ) : Fin n → ℕ :=
  fun i => if (i : ℕ) + 1 < n then 0 else 1

/-- One step of the dynamics: shift left; the last entry becomes the
digital root of the window sum. -/
def vstep (n : ℕ) (v : Fin n → ℕ) : Fin n → ℕ :=
  fun i => if h : (i : ℕ) + 1 < n then v ⟨i + 1, h⟩ else digitalRoot (∑ j, v j)

/-- Window at time `k`: `k` iterates of `vstep` from the seed. -/
def vstate (n : ℕ) (k : ℕ) : Fin n → ℕ := (vstep n)^[k] (vinit n)

/-- The OEIS sequence: the term of index `k` is the head of the window
at time `k`. Dummy value `0` outside the domain (`n = 0`). -/
def seqN (n k : ℕ) : ℕ := if h : 0 < n then vstate n k ⟨0, h⟩ else 0

/-- `p` is an eventual period of the sequence: from some rank `k0` on,
the terms `k` and `k + p` coincide. -/
def IsEventualPeriod (n p : ℕ) : Prop :=
  ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → seqN n (k + p) = seqN n k

/-- The set of positive periods of the sequence. -/
abbrev periodSet (n : ℕ) : Set ℕ := {p : ℕ | 0 < p ∧ IsEventualPeriod n p}

/-- The OEIS term `a(n)`: the length of the period, i.e. the least
element of `periodSet n` (`sInf` on ℕ, `0` by convention if empty). -/
noncomputable def a210456 (n : ℕ) : ℕ := sInf (periodSet n)

theorem main : (∀ n : ℕ, 1 < a210456 n → 3 ∣ a210456 n) ∧
    (∀ n : ℕ, 1 ≤ n → a210456 (3 ^ n - 1) = 3 ^ (2 * n + 1) - 3 ∧
      a210456 (3 ^ n) = 3 ^ (2 * n + 1) + 3 ^ (n + 1) + 3) := by
  sorry

end OMA.S_oeis_a210456
