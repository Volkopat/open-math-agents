import Mathlib

/-!
# OEIS A334514: Barker's conjectures for Rule 107 on a cyclic ring of width n

Source: https://oeis.org/A334514
Credit: @yooeonwoo

Entry A334514 (offset 1): Eventual period of a single cell in rule 107 cellular automaton in a
cyclic universe of width n. Data: 2, 2, 3, 2, 15, 2, 28, 2, 36, 20, 11, 12, 117, 28, 60, 8, 68, ...

Conjectures listed in the entry (both stated below as one conjunction):
* a(n) = 2 * a(n - 4) - a(n - 8) for n > 24 (Colin Barker, May 09 2020).
* G.f.: x * (2 + 2*x + 3*x^2 + 2*x^3 + 11*x^4 - 2*x^5 + 22*x^6 - 2*x^7 + 8*x^8 + 18*x^9 -
  42*x^10 + 10*x^11 + 60*x^12 - 10*x^13 + 66*x^14 - 14*x^15 - 130*x^16 - 33*x^18 + 16*x^19 +
  65*x^20 - 8*x^23) / ((1 - x)^2 * (1 + x)^2 * (1 + x^2)^2) (Colin Barker, May 09 2020).

Formalization notes:
* On a cyclic universe of width n >= 1, a configuration is a function Fin n -> Bool, initialized
  at t = 0 with a single ON cell at position 0.
* One step updates each cell i according to Wolfram elementary cellular automaton Rule 107
  (bits 0, 1, 3, 5, 6: neighborhood 4*left + 2*center + right, with cyclic neighbors i - 1 and
  i + 1 modulo n).
* a(n) is the smallest positive eventual period of the cyclic configuration for n >= 1, and
  a(0) = 0 so the ordinary generating function matches OEIS offset 1.
* The generating function identity A(x) = N(x) / D(x) is stated as A(x) * D(x) = N(x) in the
  formal power series ring over Z.
-/

namespace OMA.S_oeis_a334514

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

/-- A334514(n): minimal positive eventual period of Rule 107 from a single ON cell on a cyclic
ring of width `n` (offset 1, with `a 0 = 0`). -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else sInf {p : ℕ | 0 < p ∧ EventualPeriod 107 n p}

/-- Both conjectures of OEIS A334514. -/
theorem main :
    (∀ n : ℕ, 24 < n → (a n : ℤ) = 2 * a (n - 4) - a (n - 8)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2) =
      X * (2 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + 11 * X ^ 4 - 2 * X ^ 5 + 22 * X ^ 6 -
           2 * X ^ 7 + 8 * X ^ 8 + 18 * X ^ 9 - 42 * X ^ 10 + 10 * X ^ 11 + 60 * X ^ 12 -
           10 * X ^ 13 + 66 * X ^ 14 - 14 * X ^ 15 - 130 * X ^ 16 - 33 * X ^ 18 +
           16 * X ^ 19 + 65 * X ^ 20 - 8 * X ^ 23) := by
  sorry

end OMA.S_oeis_a334514
