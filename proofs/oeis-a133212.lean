import OMAStatements.S_oeis_a133212

namespace OMA133212

open Finset OMA.S_oeis_a133212

def T (f : ℕ → ℤ) (n : ℕ) : ℤ := ∑ j ∈ range (n + 1), (n.choose j : ℤ) * f j

def chi (j : ℕ) : ℤ := if 4 ∣ j then 1 else 0

lemma T_succ (f : ℕ → ℤ) (n : ℕ) : T f (n + 1) = T f n + T (fun j => f (j + 1)) n := by
  have A : ∑ j ∈ range (n + 1 + 1), ((n + 1).choose j : ℤ) * f j
      = ∑ j ∈ range (n + 1), ((n + 1).choose (j + 1) : ℤ) * f (j + 1) + f 0 := by
    rw [sum_range_succ']; simp
  have B : ∑ j ∈ range (n + 1), (n.choose j : ℤ) * f j
      = ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * f (j + 1) + f 0 := by
    rw [sum_range_succ']; simp
  have C : ∑ j ∈ range (n + 1), (n.choose (j + 1) : ℤ) * f (j + 1)
      = ∑ j ∈ range n, (n.choose (j + 1) : ℤ) * f (j + 1) := by
    rw [sum_range_succ]; simp
  have D : ∑ j ∈ range (n + 1), ((n + 1).choose (j + 1) : ℤ) * f (j + 1)
      = ∑ j ∈ range (n + 1), (n.choose j : ℤ) * f (j + 1)
        + ∑ j ∈ range (n + 1), (n.choose (j + 1) : ℤ) * f (j + 1) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  unfold T
  beta_reduce
  linarith

lemma chi_shift : (fun j => chi (j + 1 + 1 + 1 + 1)) = chi := by
  funext j
  unfold chi
  have : (4 ∣ j + 1 + 1 + 1 + 1) ↔ 4 ∣ j := by omega
  simp [this]

lemma T_rec (n : ℕ) : T chi (n + 4) = 4 * T chi (n + 3) - 6 * T chi (n + 2) + 4 * T chi (n + 1) := by
  have h0 := T_succ chi
  have h1 := T_succ (fun j => chi (j + 1))
  have h2 := T_succ (fun j => chi (j + 1 + 1))
  have h3 := T_succ (fun j => chi (j + 1 + 1 + 1))
  have e := h3 n
  rw [chi_shift] at e
  linear_combination h0 (n + 3) - 3 * h0 (n + 2) + 3 * h0 (n + 1) - h0 n
    + h1 (n + 2) - 2 * h1 (n + 1) + h1 n + h2 (n + 1) - h2 n + e

lemma b_eq (n : ℕ) : (b n : ℤ) = T chi n := by
  unfold b T chi
  have hset : (range (n + 1)).filter (fun j => 4 ∣ j) = (range (n / 4 + 1)).image (fun k => 4 * k) := by
    ext j
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hj, k, rfl⟩
      exact ⟨k, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, dvd_mul_right 4 k⟩
  have : ∑ j ∈ range (n + 1), (n.choose j : ℤ) * (if 4 ∣ j then 1 else 0)
      = ∑ j ∈ (range (n + 1)).filter (fun j => 4 ∣ j), (n.choose j : ℤ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [this, hset, sum_image (fun x _ y _ h => by omega)]
  push_cast
  rfl

lemma key : ∀ n : ℕ, a (n + 1) = 2 * T chi (n + 4) ∧ a (n + 2) = 2 * T chi (n + 5)
    ∧ a (n + 3) = 2 * T chi (n + 6) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩ <;> simp [a, T, chi, sum_range_succ, Nat.choose]
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨h2, h3, ?_⟩
    have hr := T_rec (n + 3)
    have ha : a (n + 4) = 4 * a (n + 3) - 6 * a (n + 2) + 4 * a (n + 1) := by rw [a]
    show a (n + 4) = 2 * T chi (n + 7)
    rw [ha, h1, h2, h3]
    linear_combination -2 * hr

end OMA133212

theorem OMA.solution : type_of% @OMA.S_oeis_a133212.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [OMA133212.b_eq]
  exact (OMA133212.key m).1

