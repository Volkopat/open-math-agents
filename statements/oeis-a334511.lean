import Mathlib

/-!
# OEIS A334511: Spezia's and Barker's conjectures for Rule 9 on a cyclic ring of width n

Source: https://oeis.org/A334511
Credit: @yooeonwoo

Entry A334511 (offset 1): Eventual period of a single cell in rule 9 cellular automaton in a
cyclic universe of width n. Data: 2, 2, 2, 2, 2, 9, 5, 12, 18, 5, 22, 12, 26, 14, ...

Conjectures listed in the entry (all stated below as one conjunction):
* a(n) = (3 - (-1)^n) * n / 2 for n > 10 (Stefano Spezia, Sep 11 2021).
* a(n) = 2 * a(n - 2) - a(n - 4) for n > 14 (Colin Barker, May 09 2020).
* G.f.: x * (2 + 2*x - 2*x^2 - 2*x^3 + 7*x^5 + 3*x^6 - 4*x^7 + 10*x^8 - 10*x^9 - 9*x^10 +
  14*x^11 - 5*x^13) / ((1 - x)^2 * (1 + x)^2) (Colin Barker, May 09 2020).

Formalization notes:
* On a cyclic universe of width n >= 1, a configuration is a function Fin n -> Bool, initialized
  at t = 0 with a single ON cell at position 0.
* One step updates each cell i according to Wolfram elementary cellular automaton Rule 9
  (bits 0, 3: neighborhood 4*left + 2*center + right, with cyclic neighbors i - 1 and i + 1
  modulo n).
* a(n) is the smallest positive eventual period of the cyclic configuration for n >= 1, and
  a(0) = 0 so the ordinary generating function matches OEIS offset 1.
* The generating function identity A(x) = N(x) / D(x) is stated as A(x) * D(x) = N(x) in the
  formal power series ring over Z.
-/

namespace OMA.S_oeis_a334511

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

/-- A334511(n): minimal positive eventual period of Rule 9 from a single ON cell on a cyclic
ring of width `n` (offset 1, with `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {p : ℕ | 0 < p ∧ EventualPeriod 9 n p}

/-- All three conjectures of OEIS A334511. -/
theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = (3 - (-1 : ℤ) ^ n) * n / 2) ∧
    (∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      X * (2 + 2 * X - 2 * X ^ 2 - 2 * X ^ 3 + 7 * X ^ 5 + 3 * X ^ 6 - 4 * X ^ 7 +
           10 * X ^ 8 - 10 * X ^ 9 - 9 * X ^ 10 + 14 * X ^ 11 - 5 * X ^ 13) := by
  sorry

end OMA.S_oeis_a334511
