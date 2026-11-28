import Mathlib

/-!
# OEIS A048963: Digits in periodic parts of reciprocals of primes

Source: https://oeis.org/A048963
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Table in which the `n`-th row lists the digits in the periodic part of the
base-10 expansion of `1 / p_n` (taking `[0]` for `p = 2, 5`).

Conjecture: Regarded as a decimal fraction by concatenating the rows,
this number is normal in base 10.
-/

namespace OMA.S_oeis_a048963

noncomputable def primeReciprocalPeriodDigits (n : ℕ) : List ℕ :=
  let p := Nat.nth Nat.Prime n
  if p = 2 ∨ p = 5 then
    [0]
  else
    let d := orderOf (10 : ZMod p)
    let q := (10 ^ d - 1) / p
    List.ofFn (fun i : Fin d => (q / 10 ^ (d - 1 - i.val)) % 10)

noncomputable def concatPrefix (m : ℕ) : List ℕ :=
  (List.range m).flatMap primeReciprocalPeriodDigits

noncomputable def digitAt (k : ℕ) : ℕ :=
  (concatPrefix (k + 1)).getD k 0

theorem main :
    ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < 10) →
      Filter.Tendsto
        (fun N : ℕ =>
          (((Finset.range N).filter (fun i =>
            (List.range w.length).map (fun j => digitAt (i + j)) = w)).card : ℝ) / (N : ℝ))
        Filter.atTop (nhds (1 / (10 : ℝ) ^ w.length)) := by
  sorry

end OMA.S_oeis_a048963
