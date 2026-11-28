import Mathlib

/-!
# OEIS A334513: Kotesovec's and Barker's conjectures for Rule 25 on a cyclic ring of width n

Source: https://oeis.org/A334513
Credit: @yooeonwoo

Entry A334513 (offset 1): Eventual period of a single cell in rule 25 cellular automaton in a
cyclic universe of width n. Data: 2, 2, 3, 2, 15, 15, 21, 16, 9, 20, 22, 24, 26, 28, ...

Conjectures listed in the entry (all stated below as one conjunction):
* a(n) = 2 * n for n >= 10 (Vaclav Kotesovec, May 10 2020).
* a(n) = 2 * a(n - 1) - a(n - 2) for n > 11 (Colin Barker, May 09 2020).
* G.f.: x * (2 - 2*x + x^2 - 2*x^3 + 14*x^4 - 13*x^5 + 6*x^6 - 11*x^7 - 2*x^8 + 18*x^9 - 9*x^10)
  / (1 - x)^2 (Colin Barker, May 09 2020).

Formalization notes:
* On a cyclic universe of width n >= 1, a configuration is a function Fin n -> Bool, initialized
  at t = 0 with a single ON cell at position 0.
* One step updates each cell i according to Wolfram elementary cellular automaton Rule 25
  (bits 0, 3, 4: neighborhood 4*left + 2*center + right, with cyclic neighbors i - 1 and i + 1
  modulo n).
* a(n) is the smallest positive eventual period of the cyclic configuration for n >= 1, and
  a(0) = 0 so the ordinary generating function matches OEIS offset 1.
* The generating function identity A(x) = N(x) / D(x) is stated as A(x) * D(x) = N(x) in the
  formal power series ring over Z.
-/

namespace OMA.S_oeis_a334513

open PowerSeries

/-- One step of the 1D elementary cellular automaton with Wolfram code `rule` on a cyclic ring
of width `n`. -/
def step (rule n : ℕ) (s : Fin n → Bool) (i : Fin n) : Bool :=
  Nat.testBit rule
    (4 * (s ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).toNat +
     2 * (s i).toNat +
     (s ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩).toNat)

/-- Stage `t` of elementary cellular automaton `rule` on a cyclic ring of width `n`, initialized
with a single ON cell at position `0`. -/
def state (rule n : ℕ) : ℕ → Fin n → Bool
  | 0, i => decide (i.val = 0)
  | t + 1, i => step rule n (state rule n t) i

/-- `p` is an eventual period of the cyclic configuration of `rule` on width `n`. -/
def EventualPeriod (rule n p : ℕ) : Prop :=
  ∃ T : ℕ, ∀ t : ℕ, T ≤ t → state rule n (t + p) = state rule n t

/-- A334513(n): minimal positive eventual period of Rule 25 from a single ON cell on a cyclic
ring of width `n` (offset 1, with `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {p : ℕ | 0 < p ∧ EventualPeriod 25 n p}

/-- All three conjectures of OEIS A334513. -/
theorem main :
    (∀ n : ℕ, 10 ≤ n → a n = 2 * n) ∧
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 2 =
      X * (2 - 2 * X + X ^ 2 - 2 * X ^ 3 + 14 * X ^ 4 - 13 * X ^ 5 +
           6 * X ^ 6 - 11 * X ^ 7 - 2 * X ^ 8 + 18 * X ^ 9 - 9 * X ^ 10) := by
  sorry

end OMA.S_oeis_a334513
