import OMAStatements.S_oeis_a024469
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

namespace OpenMath.A024469

open Finset PowerSeries

open OMA.S_oeis_a024469

private theorem partial_succ (n m : ℕ) :
    weightedSum n (m + 1) = weightedSum n m + lucas (m + 1) * lucas (n - m) := by
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

private theorem d_even (n : ℕ) : d (2 * n) = lucas (n + 1) * lucas n := by
  unfold d a
  rw [show (2*n+2+1)/2 = n+1 by omega,
    show (2*n+1+1)/2 = n+1 by omega, show (2*n+1)/2 = n by omega,
    partial_succ (2*n+2), partial_succ (2*n+1), partial_recur (2*n) n (by omega),
    show 2*n+2-n = n+2 by omega, show 2*n+1-n = n+1 by omega, lucas]
  ring

private theorem d_odd (n : ℕ) : d (2 * n + 1) = lucas (n + 2) * lucas (n + 2) := by
  unfold d a
  rw [show (2*n+1+2+1)/2 = (n+1)+1 by omega,
    show (2*n+1+1+1)/2 = n+1 by omega, show (2*n+1+1)/2 = n+1 by omega,
    partial_succ, partial_recur (2*n+1) (n+1) (by omega),
    show 2*n+1+2-(n+1)=n+2 by omega]
  ring

private theorem product_recur (p q : ℕ) :
    lucas (p + 3) * lucas (q + 3) = 2 * (lucas (p + 2) * lucas (q + 2)) +
      2 * (lucas (p + 1) * lucas (q + 1)) - lucas p * lucas q := by
  have h2 (m : ℕ) : lucas (m + 2) = lucas (m + 1) + lucas m := rfl
  have h3 (m : ℕ) : lucas (m + 3) = lucas (m + 2) + lucas (m + 1) := rfl
  simp only [h3 p, h3 q, h2 p, h2 q]
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

/-- Mathar's ordinary generating function, with numerator and denominator both negated. -/
theorem main : ((1+X^2 : ℤ⟦X⟧) * (1+X-X^2) * (1-X-X^2)^2) * mk a =
    X + C 2 * X^2 + C 7 * X^3 - X^4 - C 4 * X^5 + C 2 * X^6 := by
  have r (k : ℕ) : a (k + 8) = a (k + 7) + 3 * a (k + 6) - 2 * a (k + 5) - 2 * a (k + 3) -
      3 * a (k + 2) + a (k + 1) + a k := by
    have := d_recur k
    simp only [d] at this
    linarith
  simp only [map_ofNat]
  ring_nf
  ext n
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | n <;> simp [coeff_X_pow, coeff_X,
    ← map_ofNat C, coeff_mul_C, coeff_X_pow_mul', -eq_intCast, r] <;>
    first | ring1 | norm_num [a, weightedSum, lucas, Finset.sum_range_succ]

end OpenMath.A024469

theorem OMA.solution : type_of% @OMA.S_oeis_a024469.main := OpenMath.A024469.main
