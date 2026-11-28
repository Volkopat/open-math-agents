/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Wentao Li.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adapted the even-index sum decomposition and list evaluator from Wentao Li's
FCPalomar/OeisA000464/Solution.lean. The coefficient recurrence below is proved
directly for the statement's power series.
-/
import OMAStatements.S_oeis_a000464

namespace OMA.A000464Proof

open PowerSeries Finset OMA.S_oeis_a000464

private noncomputable def scaled (F : ℚ⟦X⟧) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * coeff n F

private theorem scaled_mul (F G : ℚ⟦X⟧) (n : ℕ) :
    scaled (F * G) n =
      ∑ k ∈ range (n + 1), (n.choose k : ℚ) * scaled F k * scaled G (n - k) := by
  unfold scaled
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i F * coeff j G),
    mul_sum]
  apply sum_congr rfl
  intro k hk
  have hFactorial : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n-k).factorial : ℚ) =
      (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt_succ (mem_range.mp hk))
  rw [← hFactorial]
  ring

private theorem sumPairs (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range (2 * m), f i = ∑ k ∈ range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      ih, sum_range_succ, add_assoc]

private theorem scaled_cos_even (k : ℕ) :
    scaled (rescale (2 : ℚ) (cos ℚ)) (2 * k) = (-4) ^ k := by
  simp [scaled, coeff_rescale, PowerSeries.cos, Nat.even_iff,
    show 2 * k / 2 = k by omega, pow_mul]
  field_simp
  rw [← mul_pow]
  norm_num

private theorem scaled_cos_odd (k : ℕ) :
    scaled (rescale (2 : ℚ) (cos ℚ)) (2 * k + 1) = 0 := by
  have h : (2 * k + 1) % 2 = 1 := by omega
  simp [scaled, coeff_rescale, PowerSeries.cos, Nat.even_iff, h]

private theorem scaled_sin_odd (k : ℕ) : scaled (sin ℚ) (2 * k + 1) = (-1) ^ k := by
  simp [scaled, PowerSeries.sin, Nat.even_iff, show (2 * k + 1) % 2 = 1 by omega,
    show (2 * k + 1) / 2 = k by omega]
  field_simp

private theorem recurrence (n : ℕ) :
    a n + ∑ j ∈ range n, ((2 * n + 1).choose (2 * (j + 1)) : ℚ) *
      (-4) ^ (j + 1) * a (n - 1 - j) = (-1) ^ n := by
  let C := rescale (2 : ℚ) (cos ℚ)
  have h0 : constantCoeff C ≠ 0 := by
    simp [C, ← coeff_zero_eq_constantCoeff_apply, coeff_rescale, PowerSeries.cos]
  have hmul : C * egf = sin ℚ := by
    change C * (sin ℚ * C⁻¹) = sin ℚ
    rw [mul_left_comm, PowerSeries.mul_inv_cancel C h0, mul_one]
  have h := scaled_mul C egf (2 * n + 1)
  rw [hmul, scaled_sin_odd, show 2 * n + 1 + 1 = 2 * (n + 1) by ring,
    sumPairs, sum_range_succ'] at h
  rw [h, add_comm]
  congr 1
  · apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    dsimp [C]
    rw [scaled_cos_even, scaled_cos_odd, mul_zero, zero_mul, add_zero,
      show 2 * n + 1 - 2 * (j + 1) = 2 * (n - 1 - j) + 1 by omega]
    rfl
  · dsimp [C]
    have he : scaled (rescale (2 : ℚ) (cos ℚ)) 0 = 1 := by
      simpa only [Nat.mul_zero, pow_zero] using scaled_cos_even 0
    have ho : scaled (rescale (2 : ℚ) (cos ℚ)) 1 = 0 := by
      simpa only [Nat.mul_zero, Nat.zero_add] using scaled_cos_odd 0
    rw [he, ho]
    simp [a, scaled]

private def chooseFast (n k : ℕ) : ℕ :=
  n.factorial / (k.factorial * (n - k).factorial)

private def step (n : ℕ) (l : List ℤ) : ℤ :=
  (-1) ^ n - ((List.range n).map fun j =>
    (chooseFast (2 * n + 1) (2 * (j + 1)) : ℤ) * (-4) ^ (j + 1) * l.getD j 0).sum

private def values : ℕ → List ℤ
  | 0 => []
  | n + 1 => step n (values n) :: values n

private theorem values_getD (n : ℕ) :
    ∀ j < n, ((values n).getD j 0 : ℚ) = a (n - 1 - j) := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    rcases j with _ | j
    · have hL :
          (∑ j ∈ range n, (chooseFast (2 * n + 1) (2 * (j + 1)) : ℚ) *
            (-4) ^ (j + 1) * ((values n).getD j 0 : ℚ)) =
          ∑ j ∈ range n,
            ((2 * n + 1).choose (2 * (j + 1)) : ℚ) * (-4) ^ (j + 1) * a (n - 1 - j) := by
        refine sum_congr rfl fun j hj => ?_
        have hj' := mem_range.mp hj
        rw [ih j hj', chooseFast, ← Nat.choose_eq_factorial_div_factorial (by omega)]
      show (step n (values n) : ℚ) = a (n + 1 - 1 - 0)
      rw [step, show n + 1 - 1 - 0 = n by omega,
        show ∀ f : ℕ → ℤ, ((List.range n).map f).sum = ∑ j ∈ range n, f j from fun _ => rfl]
      push_cast
      rw [hL]
      linear_combination (-1 : ℚ) * recurrence n
    · show ((values n).getD j 0 : ℚ) = a (n + 1 - 1 - (j + 1))
      rw [ih j (by omega), show n + 1 - 1 - (j + 1) = n - 1 - j by omega]

private def computed (n : ℕ) : ℤ := (values (n + 1)).getD 0 0

private theorem computed_eq (n : ℕ) : (computed n : ℚ) = a n := by
  simpa [computed] using values_getD (n + 1) 0 (by omega)

end OMA.A000464Proof

open OMA.A000464Proof OMA.S_oeis_a000464

set_option maxHeartbeats 400000 in
set_option maxRecDepth 4096 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a000464.main) := by
  intro h
  have htotient : Nat.totient 81 = 54 := by decide +kernel
  obtain ⟨z, hz⟩ := h 81 (by norm_num) 1 (by norm_num)
  rw [htotient] at hz
  change a 55 - a 1 = (81 : ℚ) * z at hz
  rw [← computed_eq 55, ← computed_eq 1] at hz
  have hzInt : computed 55 - computed 1 = 81 * z := by exact_mod_cast hz
  have h1 : computed 1 = 11 := by decide +kernel
  have h55 : computed 55 % 81 = 65 := by decide +kernel
  omega
