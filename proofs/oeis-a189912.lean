import OMAStatements.S_oeis_a189912
import Mathlib

namespace R189912
open OMA.S_oeis_a189912

/-- `C(2m, m) = (m + 1) * Cat(m)`. -/
theorem two_mul_choose (m : ℕ) : (2 * m).choose m = (m + 1) * catalan m := by
  first
    | rw [succ_mul_catalan_eq_centralBinom, Nat.centralBinom_eq_two_mul_choose]
    | exact (succ_mul_catalan_eq_centralBinom m).symm

/-- `C(2m + 1, m) = (2m + 1) * Cat(m)`. -/
theorem odd_choose (m : ℕ) : (2 * m + 1).choose m = (2 * m + 1) * catalan m := by
  have h1 := Nat.choose_mul_succ_eq (2 * m) m
  have h2 : 2 * m + 1 - m = m + 1 := by omega
  rw [h2, two_mul_choose m] at h1
  apply Nat.eq_of_mul_eq_mul_right (show 0 < m + 1 by omega)
  rw [← h1]
  ring

theorem cop (m : ℕ) : Nat.gcd (2 * m + 1) (m + 1) = 1 := by
  first
    | rw [show 2 * m + 1 = m + (m + 1) by ring, Nat.gcd_add_self_left, Nat.gcd_self_add_right,
        Nat.gcd_one_right]
    | (have h1 := Nat.gcd_dvd_left (2 * m + 1) (m + 1)
       have h2 := Nat.gcd_dvd_right (2 * m + 1) (m + 1)
       have h3 : Nat.gcd (2 * m + 1) (m + 1) ∣ (2 * m + 1) + 1 := by
         rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
         exact Dvd.dvd.mul_left h2 2
       exact Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h3))

theorem ext_even (m : ℕ) : extCatalan (2 * m) = catalan m := by
  have e1 : (2 * m + 1) / 2 = m := by omega
  have e2 : 2 * m / 2 = m := by omega
  unfold extCatalan centralBinomFloor
  rw [e1, e2, odd_choose m, two_mul_choose m, Nat.gcd_mul_right, cop m, one_mul]

theorem ext_odd (m : ℕ) : extCatalan (2 * m + 1) = (2 * m + 1) * catalan m := by
  have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  have e2 : (2 * m + 1) / 2 = m := by omega
  unfold extCatalan centralBinomFloor
  rw [e1, e2, Nat.choose_succ_succ', Nat.choose_symm_half, Nat.gcd_add_self_left, Nat.gcd_self,
    odd_choose m]

/-- Termwise identity, using `(2m + 1) * C(n, 2m + 1) = (n - 2m) * C(n, 2m)`. -/
theorem term_id (n m : ℕ) (h : 2 * m ≤ n) :
    n.choose (2 * m) * catalan m + n.choose (2 * m + 1) * ((2 * m + 1) * catalan m) =
      (n + 1 - 2 * m) * (n.choose (2 * m) * catalan m) := by
  have key := Nat.choose_succ_right_eq n (2 * m)
  have h2 : n + 1 - 2 * m = (n - 2 * m) + 1 := by omega
  rw [h2]
  generalize n - 2 * m = d at key ⊢
  calc n.choose (2 * m) * catalan m + n.choose (2 * m + 1) * ((2 * m + 1) * catalan m)
      = n.choose (2 * m) * catalan m + (n.choose (2 * m + 1) * (2 * m + 1)) * catalan m := by
        ring
    _ = n.choose (2 * m) * catalan m + (n.choose (2 * m) * d) * catalan m := by rw [key]
    _ = (d + 1) * (n.choose (2 * m) * catalan m) := by ring

/-- Grouping a sum over `range (2M)` into consecutive pairs. -/
theorem pair_sum (f : ℕ → ℕ) (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), f k = ∑ m ∈ Finset.range M, (f (2 * m) + f (2 * m + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h2 : 2 * (M + 1) = 2 * M + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem main_proof (n : ℕ) :
    a n = ∑ k ∈ Finset.range (n / 2 + 1), (n + 1 - 2 * k) * motzkinCoeff n k := by
  have hext : a n = ∑ k ∈ Finset.range (2 * (n / 2 + 1)), n.choose k * extCatalan k := by
    unfold OMA.S_oeis_a189912.a
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro x _ hx'
      simp only [Finset.mem_range] at hx'
      rw [Nat.choose_eq_zero_of_lt (show n < x by omega), zero_mul]
  rw [hext, pair_sum]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  show n.choose (2 * m) * extCatalan (2 * m) + n.choose (2 * m + 1) * extCatalan (2 * m + 1) =
    (n + 1 - 2 * m) * motzkinCoeff n m
  rw [ext_even, ext_odd]
  unfold motzkinCoeff
  exact term_id n m (by omega)

end R189912

theorem OMA.solution : type_of% @OMA.S_oeis_a189912.main := by
  intro n
  exact R189912.main_proof n
