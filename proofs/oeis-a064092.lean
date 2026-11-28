import OMAStatements.S_oeis_a064092
import Mathlib

-- Problem: OEIS A064092, generalized Catalan numbers with parameter q = 9:
-- a(0) = 1, a(n) = (Sum_{m<n} (n-m) * C(n-1+m, m) * q^m) / n. Mathar's recurrence
-- (q-1) n a(n) - ((4q(q-1)-1) n - 6q(q-1)) a(n-1) - 2q (2n-3) a(n-2) = 0.
-- Proof, for every q. The ballot numbers t(n,m) = (n-m)/n * C(n-1+m, m) satisfy
-- t(n+1,m+1) - t(n+1,m) = t(n,m+1), so summation by parts gives
-- (1-q) a(n+1) - a(n) = -C(2n,n)/(n+1) * q^(n+1) (a Catalan number times a power of q).
-- Eliminating the Catalan numbers with (n+1) C(2n+2,n+1) = 2 (2n+1) C(2n,n) gives the recurrence.

open Finset

/-- The generalized Catalan numbers with parameter `q`:
`A q 0 = 1`, `A q n = (Sum_{m<n} (n-m) * C(n-1+m, m) * q^m) / n`. -/
def OMA.A (q : ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (∑ m ∈ range n, ((n : ℚ) - m) * ((n - 1 + m).choose m : ℚ) * q ^ m) / n

/-- Summation by parts against the geometric weights. -/
lemma OMA.abel (c : ℕ → ℚ) (q : ℚ) (N : ℕ) :
    (1 - q) * ∑ m ∈ range (N + 1), c m * q ^ m
      = c 0 + ∑ m ∈ range N, (c (m + 1) - c m) * q ^ (m + 1) - c N * q ^ (N + 1) := by
  induction N with
  | zero => simp; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ]
    ring

/-- The ballot numbers `(n-m)/n * C(n-1+m, m)` with `n = N + 1`. -/
def OMA.t (N m : ℕ) : ℚ := ((N : ℚ) + 1 - m) * ((N + m).choose m : ℚ) / ((N : ℚ) + 1)

lemma OMA.A_succ (q : ℚ) (N : ℕ) :
    OMA.A q (N + 1) = ∑ m ∈ range (N + 1), OMA.t N m * q ^ m := by
  unfold OMA.A OMA.t
  rw [if_neg (Nat.succ_ne_zero N), Finset.sum_div]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have h : N + 1 - 1 + m = N + m := by omega
  rw [h]
  push_cast
  ring

/-- Pascal-type recurrence of the ballot numbers. -/
lemma OMA.t_rec (K m : ℕ) : OMA.t (K + 1) (m + 1) - OMA.t (K + 1) m = OMA.t K (m + 1) := by
  unfold OMA.t
  have hrel : ((K + 1 + m).choose (m + 1) : ℚ) * ((m : ℚ) + 1)
      = ((K + 1 + m).choose m : ℚ) * ((K : ℚ) + 1) := by
    have h := Nat.choose_succ_right_eq (K + 1 + m) m
    have h2 : K + 1 + m - m = K + 1 := by omega
    rw [h2] at h
    exact_mod_cast h
  have hpas : ((K + 1 + (m + 1)).choose (m + 1) : ℚ)
      = ((K + 1 + m).choose m : ℚ) + ((K + 1 + m).choose (m + 1) : ℚ) := by
    have h : K + 1 + (m + 1) = (K + 1 + m) + 1 := by ring
    rw [h, Nat.choose_succ_succ]
    push_cast
    ring
  have hk : K + (m + 1) = K + 1 + m := by ring
  rw [hk, hpas]
  have h1 : ((K : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((K : ℚ) + 1 + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination hrel

lemma OMA.t_zero (N : ℕ) : OMA.t N 0 = 1 := by
  unfold OMA.t
  have h1 : ((N : ℚ) + 1) ≠ 0 := by positivity
  rw [Nat.choose_zero_right, Nat.cast_zero, Nat.cast_one, sub_zero, mul_one, div_self h1]

lemma OMA.t_diag (K : ℕ) : OMA.t K (K + 1) = 0 := by
  unfold OMA.t
  push_cast
  simp

lemma OMA.t_last (N : ℕ) : OMA.t N N = ((N + N).choose N : ℚ) / ((N : ℚ) + 1) := by
  unfold OMA.t
  ring

/-- First order relation with a Catalan forcing term. -/
lemma OMA.e_formula (q : ℚ) (N : ℕ) :
    (1 - q) * OMA.A q (N + 1) - OMA.A q N
      = -(((N + N).choose N : ℚ) / ((N : ℚ) + 1)) * q ^ (N + 1) := by
  rcases N with _ | K
  · unfold OMA.A
    simp
  · rw [OMA.A_succ q (K + 1), OMA.A_succ q K, OMA.abel, OMA.t_zero, OMA.t_last,
      Finset.sum_range_succ' (fun m => OMA.t K m * q ^ m) K, OMA.t_zero,
      Finset.sum_range_succ (fun m => (OMA.t (K + 1) (m + 1) - OMA.t (K + 1) m) * q ^ (m + 1)) K]
    have h1 : ∑ m ∈ range K, (OMA.t (K + 1) (m + 1) - OMA.t (K + 1) m) * q ^ (m + 1)
        = ∑ m ∈ range K, OMA.t K (m + 1) * q ^ (m + 1) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [OMA.t_rec]
    rw [h1, OMA.t_rec, OMA.t_diag]
    push_cast
    ring

/-- The three term recurrence, for every parameter `q`. -/
lemma OMA.rec3 (q : ℚ) (N : ℕ) :
    (q - 1) * ((N : ℚ) + 2) * OMA.A q (N + 2)
      - ((4 * q * (q - 1) - 1) * ((N : ℚ) + 2) - 6 * q * (q - 1)) * OMA.A q (N + 1)
      - 2 * q * (2 * ((N : ℚ) + 2) - 3) * OMA.A q N = 0 := by
  have e2 := OMA.e_formula q (N + 1)
  have e1 := OMA.e_formula q N
  have hc : ((N : ℚ) + 1) * ((N + 1 + (N + 1)).choose (N + 1) : ℚ)
      = 2 * ((N : ℚ) + N + 1) * ((N + N).choose N : ℚ) := by
    have h := Nat.succ_mul_centralBinom_succ N
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
    have h3 : 2 * (N + 1) = N + 1 + (N + 1) := by ring
    have h4 : 2 * N = N + N := by ring
    rw [h3, h4] at h
    exact_mod_cast h
  have h1 : ((N : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((N : ℚ) + 1 + 1) ≠ 0 := by positivity
  have key : ((N : ℚ) + 2) * ((1 - q) * OMA.A q (N + 2) - OMA.A q (N + 1))
      = q * (4 * (N : ℚ) + 2) * ((1 - q) * OMA.A q (N + 1) - OMA.A q N) := by
    have h3 : N + 1 + 1 = N + 2 := by ring
    rw [h3] at e2
    rw [e2, e1]
    push_cast
    field_simp
    linear_combination (-(q ^ (N + 2)) * ((N : ℚ) + 2)) * hc
  linear_combination -key

open OMA.S_oeis_a064092

theorem OMA.solution : type_of% @OMA.S_oeis_a064092.main := by
  intro n hn
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 2 := ⟨n - 2, by omega⟩
  have ha : ∀ m, a m = OMA.A 9 m := fun m => rfl
  have e0 : N + 2 - 1 = N + 1 := rfl
  have e1 : N + 2 - 2 = N := rfl
  rw [e0, e1, ha, ha, ha]
  have h := OMA.rec3 9 N
  push_cast
  linear_combination h
