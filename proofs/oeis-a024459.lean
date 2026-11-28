import OMAStatements.S_oeis_a024459
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

-- Original Lean proof: @eliayousf.

namespace OpenMath.A024459

open Finset PowerSeries

open OMA.S_oeis_a024459

private theorem partial_succ (n m : ℕ) :
    weightedSum n (m + 1) = weightedSum n m + fibonacci (m + 1) * lucas (n - m) := by
  simp only [weightedSum, Finset.sum_range_succ]

private theorem partial_recur (n m : ℕ) (hm : m ≤ n + 1) :
    weightedSum (n + 2) m = weightedSum (n + 1) m + weightedSum n m := by
  unfold weightedSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [show n + 2 - k = (n - k) + 2 by omega, lucas,
    show n + 1 - k = (n - k) + 1 by omega, mul_add]

private def d (n : ℕ) : ℤ := a (n + 2) - a (n + 1) - a n

private theorem d_even (n : ℕ) : d (2 * n) = fibonacci (n + 1) * lucas n := by
  unfold d a
  rw [show (2*n+2+1)/2 = n+1 by omega,
    show (2*n+1+1)/2 = n+1 by omega, show (2*n+1)/2 = n by omega,
    partial_succ (2*n+2), partial_succ (2*n+1), partial_recur (2*n) n (by omega),
    show 2*n+2-n = n+2 by omega, show 2*n+1-n = n+1 by omega, lucas]
  ring

private theorem d_odd (n : ℕ) : d (2 * n + 1) = fibonacci (n + 2) * lucas (n + 2) := by
  unfold d a
  rw [show (2*n+1+2+1)/2 = (n+1)+1 by omega,
    show (2*n+1+1+1)/2 = n+1 by omega, show (2*n+1+1)/2 = n+1 by omega,
    partial_succ, partial_recur (2*n+1) (n+1) (by omega),
    show 2*n+1+2-(n+1)=n+2 by omega]
  ring

private theorem product_recur (p q : ℕ) :
    fibonacci (p + 3) * lucas (q + 3) =
      2 * (fibonacci (p + 2) * lucas (q + 2)) +
      2 * (fibonacci (p + 1) * lucas (q + 1)) - fibonacci p * lucas q := by
  have hl₂ : fibonacci (p + 2) = fibonacci (p + 1) + fibonacci p := rfl
  have hl₃ : fibonacci (p + 3) = fibonacci (p + 2) + fibonacci (p + 1) := rfl
  have hr₂ : lucas (q + 2) = lucas (q + 1) + lucas q := rfl
  have hr₃ : lucas (q + 3) = lucas (q + 2) + lucas (q + 1) := rfl
  simp only [hl₃, hr₃, hl₂, hr₂]
  ring

private theorem d_recur (n : ℕ) :
    d (n + 6) = 2*d (n + 4) + 2*d (n + 2) - d n := by
  let k := n / 2
  obtain he | ho : n = 2*k ∨ n = 2*k+1 := by omega
  · rw [show n+6=2*(k+3) by omega, show n+4=2*(k+2) by omega,
      show n+2=2*(k+1) by omega, he]
    simp only [d_even]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using product_recur (k+1) k
  · rw [show n+6=2*(k+3)+1 by omega, show n+4=2*(k+2)+1 by omega,
      show n+2=2*(k+1)+1 by omega, ho]
    simp only [d_odd]
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using product_recur (k+2) (k+2)

private noncomputable def fibResidual : ℤ⟦X⟧ := (1-X-X^2) * mk a

private theorem first_coeff (n : ℕ) :
    coeff n fibResidual =
      a n - (if 1 ≤ n then a (n-1) else 0) - (if 2 ≤ n then a (n-2) else 0) := by
  have hp : (1-X-X^2 : ℤ⟦X⟧) = 1-X^1-X^2 := by simp
  rw [fibResidual, hp]
  simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk]

private theorem first_shifted (n : ℕ) :
    coeff (n+2) fibResidual = d n := by
  rw [first_coeff, if_pos (by omega), if_pos (by omega),
    show n+2-1 = n+1 by omega, show n+2-2 = n by omega, d]

/-- Mathar's ordinary generating function, with numerator and denominator both negated. -/
theorem main : type_of% @OMA.S_oeis_a024459.main := by
  have hden :
      ((1+X^2 : ℤ⟦X⟧) * (1+X-X^2) * (1-X-X^2)^2) =
        (1-X-X^2) * (1-C 2*X^2-C 2*X^4+X^6) := by
    simp
    ring
  rw [hden, mul_comm (1-X-X^2 : ℤ⟦X⟧), mul_assoc]
  change _ * fibResidual = _
  ext n
  simp only [sub_mul, add_mul, one_mul, map_add, map_sub, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  by_cases hn : n < 8
  · interval_cases n <;>
      simp only [coeff_X, coeff_X_pow] <;>
      norm_num [first_coeff, a, weightedSum, lucas, fibonacci, Finset.sum_range_succ]
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 8 := ⟨n - 8, by omega⟩
    rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
      show k+8 = (k+6)+2 by omega, first_shifted,
      show k+6+2-2 = (k+4)+2 by omega, first_shifted,
      show k+6+2-4 = (k+2)+2 by omega, first_shifted,
      show k+6+2-6 = k+2 by omega, first_shifted]
    rw [d_recur]
    simp only [coeff_X, coeff_X_pow]
    split_ifs <;> omega

end OpenMath.A024459

theorem OMA.solution : type_of% @OMA.S_oeis_a024459.main := OpenMath.A024459.main
