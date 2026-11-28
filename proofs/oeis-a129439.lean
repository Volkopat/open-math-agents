import OMAStatements.S_oeis_a129439

namespace OMA.S_oeis_a129439

open Finset

lemma divisors_eq (n : ℕ) :
    (n + 1).divisors = (range (n + 2)).filter (fun d => d ∣ n + 1) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_range]
  constructor
  · rintro ⟨h, -⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.succ_pos n) h), h⟩
  · rintro ⟨-, h⟩
    exact ⟨h, Nat.succ_ne_zero n⟩

lemma D_closed (n : ℕ) : D n = ∏ d ∈ range (n + 1), d ^ (n / d) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    have hD : D (n + 1) = D n * ∏ d ∈ (n + 1).divisors, d := by
      simp only [D]; rw [prod_range_succ]
    rw [hD, ih]
    have e1 : ∀ d ∈ range (n + 1 + 1), d ^ ((n + 1) / d) =
        d ^ (n / d) * (if d ∣ n + 1 then d else 1) := by
      intro d _
      rw [Nat.succ_div, pow_add]
      split_ifs <;> simp
    rw [prod_congr rfl e1, prod_mul_distrib, prod_range_succ (fun d => d ^ (n / d)) (n + 1),
      Nat.div_eq_of_lt (Nat.lt_succ_self n), pow_zero, mul_one, ← prod_filter, ← divisors_eq]

lemma D_ext (m n : ℕ) (h : m ≤ n) : D m = ∏ d ∈ range (n + 1), d ^ (m / d) := by
  rw [D_closed]
  apply prod_subset (fun x hx => by simp only [mem_range] at hx ⊢; omega)
  intro d hd hdm
  simp only [mem_range] at hd hdm
  rw [Nat.div_eq_of_lt (by omega), pow_zero]

theorem solution_main : ∀ n k : ℕ, k ≤ n → D (n - k) * D k ∣ D n := by
  intro n k hk
  rw [D_ext (n - k) n (by omega), D_ext k n hk, D_closed, ← prod_mul_distrib]
  apply prod_dvd_prod_of_dvd
  intro d _
  rw [← pow_add]
  apply pow_dvd_pow
  have := (Nat.div_add_div_le_add_div : (n - k) / d + k / d ≤ (n - k + k) / d)
  rwa [Nat.sub_add_cancel hk] at this

end OMA.S_oeis_a129439

theorem OMA.solution : type_of% @OMA.S_oeis_a129439.main := OMA.S_oeis_a129439.solution_main
