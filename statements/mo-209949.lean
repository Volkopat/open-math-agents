import Mathlib

/-!
# Limit of endpoint Hermite interpolation with increasing orders

Source: https://mathoverflow.net/questions/209949
Credit: @connoranderson (agent: Codex)

For degree n the left endpoint has matching derivatives through order floor(n/2).
At the right endpoint they match through order n-floor(n/2)-1. Divisibility by
a power of X minus the endpoint expresses agreement of these Taylor coefficients.
-/

namespace OMA.S_mo_209949
open Polynomial Filter Set

noncomputable def tangentLine (x v slope : ℝ) : ℝ[X] := C v + C slope * (X-C x)

def EndpointConditions (n : ℕ) (a b A B c d : ℝ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n ∧ (X-C a)^(n/2+1) ∣ p - tangentLine a A c ∧
    (X-C b)^(n-n/2) ∣ p - tangentLine b B d

noncomputable def endpointLimit (a b A B c d x : ℝ) : ℝ :=
  let m := (a+b)/2
  let L := A+c*(x-a)
  let R := B+d*(x-b)
  if x < m then L else if m < x then R else (L+R)/2

theorem main : ∀ (a b A B c d : ℝ), a < b → ∀ P : ℕ → ℝ[X],
    (∀ n ≥ 3, EndpointConditions n a b A B c d (P n)) →
    (∀ x ∈ Icc a b, Tendsto (fun n => (P n).eval x) atTop (nhds (endpointLimit a b A B c d x))) ∧
    (TendstoUniformlyOn (fun n x => (P n).eval x) (endpointLimit a b A B c d) atTop (Icc a b) ↔
      A+c*((a+b)/2-a) = B+d*((a+b)/2-b)) ∧
    (c ≠ d → (B-A)/(b-a) ∈ Icc (min c d) (max c d) →
      DifferentiableOn ℝ (endpointLimit a b A B c d) (Ioo a b) →
      ∀ x ∈ Ioo a b, deriv (endpointLimit a b A B c d) x ∈ Icc (min c d) (max c d)) := by
  sorry

end OMA.S_mo_209949
