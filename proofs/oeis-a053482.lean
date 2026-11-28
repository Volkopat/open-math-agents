import OMAStatements.S_oeis_a053482

namespace A053482P

noncomputable def S (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (k.factorial : ℚ)

noncomputable def U (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (k.factorial : ℚ) * (2 : ℚ) ^ k

lemma choose_fact (n k : ℕ) (h : k ≤ n) :
    (n.choose k : ℚ) * (k.factorial : ℚ) = (n.factorial : ℚ) * (((n - k).factorial : ℚ))⁻¹ := by
  have h1 : ((n.choose k : ℚ) * (k.factorial : ℚ)) * ((n - k).factorial : ℚ) = (n.factorial : ℚ) := by
    have := Nat.choose_mul_factorial_mul_factorial h
    exact_mod_cast this
  have h2 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  rw [← h1, mul_inv_cancel_right₀ h2]

lemma S_form (n : ℕ) :
    S n = (n.factorial : ℚ) * ∑ j ∈ Finset.range (n + 1), ((j.factorial : ℚ))⁻¹ := by
  unfold S
  have step : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (k.factorial : ℚ)
      = ∑ k ∈ Finset.range (n + 1), (n.factorial : ℚ) * (((n - k).factorial : ℚ))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    exact choose_fact n k (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  rw [step, ← Finset.mul_sum]
  congr 1
  have hrefl := Finset.sum_range_reflect (fun j : ℕ => (((j.factorial : ℚ)))⁻¹) (n + 1)
  simpa [Nat.add_sub_cancel] using hrefl

lemma U_form (n : ℕ) :
    U n = (n.factorial : ℚ) *
      ∑ j ∈ Finset.range (n + 1), ((j.factorial : ℚ))⁻¹ * (2 : ℚ) ^ (n - j) := by
  unfold U
  have step : ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (k.factorial : ℚ) * (2 : ℚ) ^ k
      = ∑ k ∈ Finset.range (n + 1),
          (n.factorial : ℚ) * (((n - k).factorial : ℚ))⁻¹ * (2 : ℚ) ^ k := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [choose_fact n k (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [step]
  have pull : ∑ k ∈ Finset.range (n + 1), (n.factorial : ℚ) * (((n - k).factorial : ℚ))⁻¹ * (2 : ℚ) ^ k
      = (n.factorial : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (((n - k).factorial : ℚ))⁻¹ * (2 : ℚ) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    ring
  rw [pull]
  congr 1
  have hrefl := Finset.sum_range_reflect
    (fun j : ℕ => ((j.factorial : ℚ))⁻¹ * (2 : ℚ) ^ (n - j)) (n + 1)
  rw [← hrefl]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [Finset.mem_range] at hj
  have e1 : n + 1 - 1 - j = n - j := by omega
  have e3 : n - (n - j) = j := by omega
  rw [e1, e3]

lemma S_rec (n : ℕ) (hn : 1 ≤ n) : S n = (n : ℚ) * S (n - 1) + 1 := by
  have e : n - 1 + 1 = n := by omega
  have h1 : S n = (n.factorial : ℚ) * ∑ j ∈ Finset.range (n + 1), ((j.factorial : ℚ))⁻¹ := S_form n
  have h2 : S (n - 1) = ((n - 1).factorial : ℚ) * ∑ j ∈ Finset.range n, ((j.factorial : ℚ))⁻¹ := by
    have h := S_form (n - 1)
    rwa [e] at h
  have hfac : ((n.factorial : ℚ)) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    have h := Nat.factorial_succ (n - 1)
    rw [e] at h
    exact_mod_cast h
  have hn0 : ((n.factorial : ℚ)) ≠ 0 := by positivity
  have hc : ((n : ℚ) * ((n - 1).factorial : ℚ)) ≠ 0 := by
    have h1 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h2 : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
    exact mul_ne_zero h1 h2
  rw [h2, h1, Finset.sum_range_succ, mul_add, hfac, mul_inv_cancel₀ hc]
  ring

lemma U_rec (n : ℕ) (hn : 1 ≤ n) : U n = 2 * (n : ℚ) * U (n - 1) + 1 := by
  have e : n - 1 + 1 = n := by omega
  have h1 : U n = (n.factorial : ℚ) *
      ∑ j ∈ Finset.range (n + 1), ((j.factorial : ℚ))⁻¹ * (2 : ℚ) ^ (n - j) := U_form n
  have h2 : U (n - 1) = ((n - 1).factorial : ℚ) *
      ∑ j ∈ Finset.range n, ((j.factorial : ℚ))⁻¹ * (2 : ℚ) ^ ((n - 1) - j) := by
    have h := U_form (n - 1)
    rwa [e] at h
  have hfac : ((n.factorial : ℚ)) = (n : ℚ) * ((n - 1).factorial : ℚ) := by
    have h := Nat.factorial_succ (n - 1)
    rw [e] at h
    exact_mod_cast h
  have hshift : ∑ j ∈ Finset.range n, ((j.factorial : ℚ))⁻¹ * (2 : ℚ) ^ (n - j)
      = 2 * ∑ j ∈ Finset.range n, ((j.factorial : ℚ))⁻¹ * (2 : ℚ) ^ ((n - 1) - j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have e1 : n - j = (n - 1 - j) + 1 := by omega
    rw [e1, pow_succ]
    ring
  have hc : ((n : ℚ) * ((n - 1).factorial : ℚ)) ≠ 0 := by
    have h1 : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have h2 : ((n - 1).factorial : ℚ) ≠ 0 := by positivity
    exact mul_ne_zero h1 h2
  have hpow : (2 : ℚ) ^ (n - n) = 1 := by rw [Nat.sub_self, pow_zero]
  rw [h2, h1, Finset.sum_range_succ, hshift, hfac, hpow, mul_one, mul_add, mul_inv_cancel₀ hc]
  ring

lemma Sbr (n : ℕ) (hn : 3 ≤ n) :
    S n - (3 * (n : ℚ) + 1) * S (n - 1) + ((2 * (n : ℚ) + 3) * ((n : ℚ) - 1)) * S (n - 2) -
      (2 * ((n : ℚ) - 1) * ((n : ℚ) - 2)) * S (n - 3) = -2 := by
  have e1 : S n = (n : ℚ) * S (n - 1) + 1 := S_rec n (by omega)
  have e2 : S (n - 1) = ((n : ℚ) - 1) * S (n - 2) + 1 := by
    have h := S_rec (n - 1) (by omega)
    have h1 : n - 1 - 1 = n - 2 := by omega
    rw [h1] at h
    rw [h, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have e3 : S (n - 2) = ((n : ℚ) - 2) * S (n - 3) + 1 := by
    have h := S_rec (n - 2) (by omega)
    have h1 : n - 2 - 1 = n - 3 := by omega
    rw [h1] at h
    rw [h, Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    ring
  rw [e1, e2, e3]
  ring

lemma Ubr (n : ℕ) (hn : 3 ≤ n) :
    U n - (3 * (n : ℚ) + 1) * U (n - 1) + ((2 * (n : ℚ) + 3) * ((n : ℚ) - 1)) * U (n - 2) -
      (2 * ((n : ℚ) - 1) * ((n : ℚ) - 2)) * U (n - 3) = -1 := by
  have e1 : U n = 2 * (n : ℚ) * U (n - 1) + 1 := U_rec n (by omega)
  have e2 : U (n - 1) = 2 * ((n : ℚ) - 1) * U (n - 2) + 1 := by
    have h := U_rec (n - 1) (by omega)
    have h1 : n - 1 - 1 = n - 2 := by omega
    rw [h1] at h
    rw [h, Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  have e3 : U (n - 2) = 2 * ((n : ℚ) - 2) * U (n - 3) + 1 := by
    have h := U_rec (n - 2) (by omega)
    have h1 : n - 2 - 1 = n - 3 := by omega
    rw [h1] at h
    rw [h, Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    ring
  rw [e1, e2, e3]
  ring

lemma ha (n : ℕ) : (OMA.S_oeis_a053482.a n : ℚ) = 2 * U n - S n := by
  unfold OMA.S_oeis_a053482.a S U
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hp : (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [hp]
  ring

lemma main_q (n : ℕ) (hn : 3 ≤ n) :
    (OMA.S_oeis_a053482.a n : ℚ) - (3 * (n : ℚ) + 1) * (OMA.S_oeis_a053482.a (n - 1) : ℚ) +
        ((2 * (n : ℚ) + 3) * ((n : ℚ) - 1)) * (OMA.S_oeis_a053482.a (n - 2) : ℚ) -
        (2 * ((n : ℚ) - 1) * ((n : ℚ) - 2)) * (OMA.S_oeis_a053482.a (n - 3) : ℚ) = 0 := by
  rw [ha n, ha (n - 1), ha (n - 2), ha (n - 3)]
  have b1 := Sbr n hn
  have b2 := Ubr n hn
  linear_combination 2 * b2 - b1

end A053482P

theorem OMA.solution : type_of% @OMA.S_oeis_a053482.main := by
  intro n hn
  have h := A053482P.main_q n hn
  have h3 : ((OMA.S_oeis_a053482.a n - (3 * (n : ℤ) + 1) * OMA.S_oeis_a053482.a (n - 1) +
      (2 * (n : ℤ) + 3) * ((n : ℤ) - 1) * OMA.S_oeis_a053482.a (n - 2) -
      2 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * OMA.S_oeis_a053482.a (n - 3) : ℤ) : ℚ) = 0 := by
    push_cast
    exact h
  exact_mod_cast h3
