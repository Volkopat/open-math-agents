import Mathlib

namespace OMA.S_oeis_a101282

inductive SchroderStep where
  | U | D | H
  deriving DecidableEq

def stepLen : List SchroderStep → ℕ
  | [] => 0
  | .U :: l => 1 + stepLen l
  | .D :: l => 1 + stepLen l
  | .H :: l => 2 + stepLen l

def isSchroderAux : ℕ → List SchroderStep → Prop
  | h, [] => h = 0
  | h, .U :: l => isSchroderAux (h + 1) l
  | h, .D :: l => 0 < h ∧ isSchroderAux (h - 1) l
  | h, .H :: l => isSchroderAux h l

def valleys : List SchroderStep → ℕ
  | .D :: .U :: l => 1 + valleys (.U :: l)
  | _ :: l => valleys l
  | [] => 0

noncomputable def schroderValleyCount (n k : ℕ) : ℕ :=
  ({p : List SchroderStep | isSchroderAux 0 p ∧ stepLen p = 2 * n ∧ valleys p = k}).ncard

noncomputable def schroderRowPoly (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n + 1), (schroderValleyCount n k : Polynomial ℤ) * Polynomial.X ^ k

noncomputable def kurkovR : ℕ → ℕ → Polynomial ℤ
  | n, k =>
    if k = n then 1
    else if k = 0 then
      match n with
      | 0 => 1
      | m + 1 => ∑ j ∈ Finset.range (m + 1), kurkovR m j
    else if k < n then
      match n with
      | 0 => 0
      | m + 1 =>
        kurkovR m (k - 1) +
          (Polynomial.X + 1) *
            (kurkovR (m + 1) 0 - ∑ j ∈ Finset.range k, kurkovR m j)
    else 0
termination_by n k => (n, if k = 0 then 0 else 1)
decreasing_by
  all_goals simp_wf
  all_goals try (left; omega)
  all_goals try (right; simp_all)

theorem main :
    ∀ n : ℕ, schroderRowPoly n = kurkovR (n + 1) 0 := by
  sorry

end OMA.S_oeis_a101282
