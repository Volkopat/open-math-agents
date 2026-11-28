import OMAStatements.S_oeis_a144084
import Mathlib

-- Problem: A144084: T(n,k) is the number of partial bijections of height k (height(alpha) = |Im(alpha)|) of an n-element set.
-- Upstream: formal-conjectures statements/oeis-a144084.lean:0 (declaration OMA.S_oeis_a144084.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let L(n,r) be the sum over m of c(n,m) S(m+1,r+1), with c and S the Stirling numbers of the
first and second kind. The recurrences of c and S give
L(n+1,r) = (n + r + 1) L(n,r) + L(n,r-1) (the last term absent for r = 0), and induction on n
then shows L(n,r) r! = C(n,r) n!, using (r+1) C(n,r+1) = (n-r) C(n,r). The sum in the conjecture
is L(n,n-k) after reversing the index (the missing terms vanish), and
C(n,n-k) n! / (n-k)! = k! C(n,k)^2. -/

namespace A144084Aux

open OMA.S_oeis_a144084

/-- L(n,r) = ∑_m c(n,m) S(m+1,r+1). -/
def L (n r : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), Nat.stirlingFirst n m * Nat.stirlingSecond (m + 1) (r + 1)

/-- The same sum with second index r instead of r + 1. -/
def L' (n r : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), Nat.stirlingFirst n m * Nat.stirlingSecond (m + 1) r

theorem L'_zero (n : ℕ) : L' n 0 = 0 := by
  unfold L'
  apply Finset.sum_eq_zero
  intro m _
  rw [Nat.stirlingSecond_succ_zero, Nat.mul_zero]

theorem L'_succ (n r : ℕ) : L' n (r + 1) = L n r := rfl

theorem stirling_zero_mul (n : ℕ) : n * Nat.stirlingFirst n 0 = 0 := by
  cases n <;> simp

theorem L_rec (n r : ℕ) : L (n + 1) r = (n + r + 1) * L n r + L' n r := by
  have hA : n * L n r = n * ∑ i ∈ Finset.range (n + 1),
      Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (r + 1) := by
    have h1 : L n r = ∑ i ∈ Finset.range n,
        Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (r + 1) +
        Nat.stirlingFirst n 0 * Nat.stirlingSecond (0 + 1) (r + 1) := by
      unfold L
      rw [Finset.sum_range_succ']
    have h2 : ∑ i ∈ Finset.range (n + 1),
        Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (r + 1) =
        ∑ i ∈ Finset.range n,
          Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (r + 1) := by
      rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_add_one n), Nat.zero_mul,
        Nat.add_zero]
    rw [h1, h2, Nat.mul_add, ← Nat.mul_assoc, stirling_zero_mul, Nat.zero_mul, Nat.add_zero]
  have hB : ∑ i ∈ Finset.range (n + 1),
      Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1 + 1) (r + 1) = (r + 1) * L n r + L' n r := by
    unfold L L'
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.stirlingSecond_succ_succ]
    ring
  have hz : Nat.stirlingFirst (n + 1) 0 = 0 := Nat.stirlingFirst_succ_zero n
  have hC : L (n + 1) r = ∑ i ∈ Finset.range (n + 1),
      (n * Nat.stirlingFirst n (i + 1) + Nat.stirlingFirst n i) *
        Nat.stirlingSecond (i + 1 + 1) (r + 1) := by
    unfold L
    rw [Finset.sum_range_succ' (fun m =>
      Nat.stirlingFirst (n + 1) m * Nat.stirlingSecond (m + 1) (r + 1)), hz, Nat.zero_mul,
      Nat.add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.stirlingFirst_succ_succ]
  have hD : ∑ i ∈ Finset.range (n + 1),
      (n * Nat.stirlingFirst n (i + 1) + Nat.stirlingFirst n i) *
        Nat.stirlingSecond (i + 1 + 1) (r + 1) =
      n * ∑ i ∈ Finset.range (n + 1),
        Nat.stirlingFirst n (i + 1) * Nat.stirlingSecond (i + 1 + 1) (r + 1) +
      ∑ i ∈ Finset.range (n + 1),
        Nat.stirlingFirst n i * Nat.stirlingSecond (i + 1 + 1) (r + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hC, hD, ← hA, hB]
  ring

theorem key : ∀ n r : ℕ, L n r * r.factorial = n.choose r * n.factorial := by
  intro n
  induction n with
  | zero =>
    intro r
    cases r with
    | zero => simp [L, Nat.stirlingSecond_self]
    | succ r => simp [L, Nat.stirlingSecond_eq_zero_of_lt]
  | succ n ih =>
    intro r
    rw [L_rec]
    cases r with
    | zero =>
      rw [L'_zero, Nat.add_zero, Nat.add_zero]
      have h0 := ih 0
      simp only [Nat.factorial_zero, Nat.mul_one, Nat.choose_zero_right, Nat.one_mul] at h0 ⊢
      rw [h0, Nat.factorial_succ]
    | succ s =>
      rw [L'_succ]
      have ih1 := ih (s + 1)
      have ih0 := ih s
      have hch := Nat.choose_succ_right_eq n s
      have E : (n + (s + 1) + 1) * n.choose (s + 1) + (s + 1) * n.choose s =
          (n + 1) * (n.choose (s + 1) + n.choose s) := by
        rcases Nat.lt_or_ge n s with h | h
        · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
          simp
        · have h2 : n.choose (s + 1) * (s + 1) + n.choose s * (s + 1) = n.choose s * (n + 1) := by
            rw [hch, ← Nat.mul_add]
            congr 1
            omega
          nlinarith [h2]
      have ih1' : L n (s + 1) * ((s + 1) * s.factorial) = n.choose (s + 1) * n.factorial := by
        rw [← Nat.factorial_succ]
        exact ih1
      calc ((n + (s + 1) + 1) * L n (s + 1) + L n s) * (s + 1).factorial
          = (n + (s + 1) + 1) * (L n (s + 1) * ((s + 1) * s.factorial)) +
              (s + 1) * (L n s * s.factorial) := by
            rw [Nat.factorial_succ]
            ring
        _ = (n + (s + 1) + 1) * (n.choose (s + 1) * n.factorial) +
              (s + 1) * (n.choose s * n.factorial) := by rw [ih1', ih0]
        _ = ((n + (s + 1) + 1) * n.choose (s + 1) + (s + 1) * n.choose s) * n.factorial := by ring
        _ = ((n + 1) * (n.choose (s + 1) + n.choose s)) * n.factorial := by rw [E]
        _ = (n + 1).choose (s + 1) * (n + 1).factorial := by
            rw [Nat.choose_succ_succ, Nat.factorial_succ]
            ring

theorem sum_eq_L (n k : ℕ) (hk : k ≤ n) :
    ∑ j ∈ Finset.range (k + 1),
      Nat.stirlingFirst n (n - j) * Nat.stirlingSecond (n - j + 1) (n - k + 1) = L n (n - k) := by
  have hsub : Finset.range (k + 1) ⊆ Finset.range (n + 1) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hzero : ∀ j ∈ Finset.range (n + 1), j ∉ Finset.range (k + 1) →
      Nat.stirlingFirst n (n - j) * Nat.stirlingSecond (n - j + 1) (n - k + 1) = 0 := by
    intro j hj hj'
    simp only [Finset.mem_range, not_lt] at hj hj'
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega), Nat.mul_zero]
  rw [Finset.sum_subset hsub hzero]
  unfold L
  have h := Finset.sum_range_reflect (fun m =>
    Nat.stirlingFirst n m * Nat.stirlingSecond (m + 1) (n - k + 1)) (n + 1)
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.add_sub_cancel]

end A144084Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a144084.main := by
  intro n k hk
  rw [A144084Aux.sum_eq_L n k hk]
  have h := A144084Aux.key n (n - k)
  rw [Nat.choose_symm hk] at h
  have hf := Nat.choose_mul_factorial_mul_factorial hk
  have hpos : 0 < (n - k).factorial := Nat.factorial_pos _
  unfold OMA.S_oeis_a144084.T
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, ← hf]
  ring
