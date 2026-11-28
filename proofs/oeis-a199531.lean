import OMAStatements.S_oeis_a199531

/-!
Proof of Barker's conjectures for A199531 (arrays `x(0..3)` of elements of `-n..n` with zero sum
and no two consecutive zero elements).

An array is determined by `(p, q, r) = (x 0, x 1, x 2)`, since `x 3 = -(p + q + r)`. For fixed
`p, q` in `[-n, n]`, the admissible `r` (those with `|p + q + r| ≤ n`) form an interval of
`2n + 1 - |p + q|` integers, from which `r = 0` is removed when `q = 0` or `p + q = 0` (two
consecutive zeros), and nothing is left when `p = q = 0`. Summing over `p, q`:
* `Σ_{p,q} |p + q| = H n` with `H (n + 1) = H n + 8 (n + 1)^2`, so `3 H n = 4n(n + 1)(2n + 1)`;
* the corrections add up to `(4n + 1) + 2n`.
Hence `3 a(n) = 3(2n + 1)^3 - 4n(n + 1)(2n + 1) - 3(6n + 1) = 16n^3 + 24n^2 - 4n` for every `n`.
The recurrence and the generating function follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a199531 Finset

/-- The integers `-n, ..., n`. -/
noncomputable abbrev I (n : ℕ) : Finset ℤ := Icc (-(n : ℤ)) n

/-- The conditions on `(x 0, x 1, x 2) = (p, q, r)` for the array `![p, q, r, -(p + q + r)]`. -/
def P (n : ℕ) (p q r : ℤ) : Prop :=
  -(p + q + r) ∈ I n ∧ ¬ (p = 0 ∧ q = 0) ∧ ¬ (q = 0 ∧ r = 0) ∧ ¬ (r = 0 ∧ -(p + q + r) = 0)

noncomputable instance decP (n : ℕ) (p q r : ℤ) : Decidable (P n p q r) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The triples `(x 0, x 1, x 2)` of the arrays counted by `a n`. -/
noncomputable def T (n : ℕ) : Finset (ℤ × ℤ × ℤ) :=
  (I n ×ˢ I n ×ˢ I n).filter (fun t => P n t.1 t.2.1 t.2.2)

theorem good_iff (x : Fin 4 → ℤ) :
    Good x ↔ x 0 + x 1 + x 2 + x 3 = 0 ∧ ¬ (x 0 = 0 ∧ x 1 = 0) ∧ ¬ (x 1 = 0 ∧ x 2 = 0) ∧
      ¬ (x 2 = 0 ∧ x 3 = 0) := by
  unfold Good
  rw [Fin.sum_univ_four]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, h' 0, h' 1, h' 2⟩
  · rintro ⟨h, h0, h1, h2⟩
    refine ⟨h, fun i => ?_⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

theorem a_eq_card_T (n : ℕ) : a n = #(T n) := by
  classical
  unfold a
  refine card_nbij' (fun x => (x 0, x 1, x 2))
    (fun t => ![t.1, t.2.1, t.2.2, -(t.1 + t.2.1 + t.2.2)]) ?_ ?_ ?_ ?_
  · intro x hx
    rw [mem_coe, mem_filter, Fintype.mem_piFinset, good_iff] at hx
    obtain ⟨hI, hs, h0, h1, h2⟩ := hx
    have h3 : x 3 = -(x 0 + x 1 + x 2) := by linarith
    rw [mem_coe, T, mem_filter, mem_product, mem_product]
    refine ⟨⟨hI 0, hI 1, hI 2⟩, ?_, h0, h1, ?_⟩
    · rw [← h3]
      exact hI 3
    · rw [← h3]
      exact h2
  · rintro ⟨p, q, r⟩ ht
    rw [mem_coe, T, mem_filter, mem_product, mem_product] at ht
    obtain ⟨⟨hp, hq, hr⟩, hs, h0, h1, h2⟩ := ht
    rw [mem_coe, mem_filter, Fintype.mem_piFinset, good_iff]
    refine ⟨fun i => ?_, ?_, ?_, ?_, ?_⟩
    · fin_cases i
      · exact hp
      · exact hq
      · exact hr
      · exact hs
    · simp only [Matrix.cons_val]
      ring
    · exact h0
    · exact h1
    · exact h2
  · intro x hx
    rw [mem_coe, mem_filter, good_iff] at hx
    obtain ⟨_, hs, _⟩ := hx
    have h3 : -(x 0 + x 1 + x 2) = x 3 := by linarith
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · exact h3
  · intro t _
    rfl

theorem card_T (n : ℕ) : #(T n) = ∑ p ∈ I n, ∑ q ∈ I n, #((I n).filter (P n p q)) := by
  rw [T, card_filter, sum_product]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_product]
  refine sum_congr rfl fun q _ => ?_
  rw [card_filter]

/-- The number of valid `r` for given `p, q`: the `r` with `|p + q + r| ≤ n` form an interval of
`2n + 1 - |p + q|` integers, from which `r = 0` is removed when `q = 0` or `p + q = 0`; nothing is
left when `p = q = 0`. -/
theorem card_fiber (n : ℕ) (p q : ℤ) (hp : p ∈ I n) (hq : q ∈ I n) :
    (#((I n).filter (P n p q)) : ℤ) =
      2 * n + 1 - |p + q| - (if q = 0 ∨ p + q = 0 then 1 else 0) -
        (if p = 0 ∧ q = 0 then 2 * (n : ℤ) else 0) := by
  rw [mem_Icc] at hp hq
  rw [abs_eq_max_neg]
  by_cases h0 : p = 0 ∧ q = 0
  · have he : (I n).filter (P n p q) = ∅ := by
      rw [filter_eq_empty_iff]
      intro r _ hr
      exact hr.2.1 h0
    rw [he, card_empty, if_pos (Or.inl h0.2), if_pos h0]
    omega
  · by_cases h1 : q = 0 ∨ p + q = 0
    · have he : (I n).filter (P n p q) =
          (Icc (max (-(n : ℤ)) (-n - (p + q))) (min (n : ℤ) (n - (p + q)))).erase 0 := by
        ext r
        simp only [mem_filter, mem_erase, mem_Icc, P, I]
        omega
      rw [he, card_erase_of_mem (by rw [mem_Icc]; omega), Int.card_Icc, if_pos h1, if_neg h0]
      omega
    · have he : (I n).filter (P n p q) =
          Icc (max (-(n : ℤ)) (-n - (p + q))) (min (n : ℤ) (n - (p + q))) := by
        ext r
        simp only [mem_filter, mem_Icc, P, I]
        omega
      rw [he, Int.card_Icc, if_neg h1, if_neg h0]
      omega

theorem zero_mem_I (n : ℕ) : (0 : ℤ) ∈ I n := by
  rw [mem_Icc]
  omega

theorem card_I (n : ℕ) : #(I n) = 2 * n + 1 := by
  rw [Int.card_Icc]
  omega

theorem I_succ (n : ℕ) : I (n + 1) = insert (-((n : ℤ) + 1)) (insert ((n : ℤ) + 1) (I n)) := by
  ext x
  simp only [I, mem_insert, mem_Icc]
  push_cast
  omega

/-- Peeling the two ends off `[-(n + 1), n + 1]`. -/
theorem sum_I_succ (n : ℕ) (f : ℤ → ℤ) :
    ∑ x ∈ I (n + 1), f x = ∑ x ∈ I n, f x + (f ((n : ℤ) + 1) + f (-((n : ℤ) + 1))) := by
  rw [I_succ, sum_insert, sum_insert]
  · ring
  all_goals
    simp only [I, mem_insert, mem_Icc]
    omega

/-- `H n = Σ_{p, q ∈ [-n, n]} |p + q|`. -/
noncomputable def H (n : ℕ) : ℤ := ∑ p ∈ I n, ∑ q ∈ I n, |p + q|

theorem H_zero : H 0 = 0 := by
  simp [H, I]

theorem H_succ (n : ℕ) : H (n + 1) = H n + 8 * ((n : ℤ) + 1) ^ 2 := by
  have h1 : ∀ p ∈ I (n + 1), ∑ q ∈ I (n + 1), |p + q| = ∑ q ∈ I n, |p + q| + (2 * n + 2) := by
    intro p hp
    rw [sum_I_succ n (fun q => |p + q|)]
    congr 1
    simp only [I, mem_Icc] at hp
    push_cast at hp
    rw [abs_eq_max_neg, abs_eq_max_neg]
    omega
  have h2 : ∀ q ∈ I n, ∑ p ∈ I (n + 1), |p + q| = ∑ p ∈ I n, |p + q| + (2 * n + 2) := by
    intro q hq
    rw [sum_I_succ n (fun p => |p + q|)]
    congr 1
    simp only [I, mem_Icc] at hq
    rw [abs_eq_max_neg, abs_eq_max_neg]
    omega
  calc H (n + 1) = ∑ p ∈ I (n + 1), (∑ q ∈ I n, |p + q| + (2 * n + 2)) := sum_congr rfl h1
    _ = ∑ q ∈ I n, ∑ p ∈ I (n + 1), |p + q| + ∑ p ∈ I (n + 1), (2 * (n : ℤ) + 2) := by
        rw [sum_add_distrib, sum_comm]
    _ = ∑ q ∈ I n, (∑ p ∈ I n, |p + q| + (2 * n + 2)) +
          ∑ p ∈ I (n + 1), (2 * (n : ℤ) + 2) := by
        rw [sum_congr rfl h2]
    _ = H n + 8 * ((n : ℤ) + 1) ^ 2 := by
        rw [sum_add_distrib, sum_comm, sum_const, sum_const, card_I, card_I]
        simp only [H, nsmul_eq_mul]
        push_cast
        ring

theorem H_eq (n : ℕ) : 3 * H n = 4 * n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp [H_zero]
  | succ n ih =>
    rw [H_succ]
    push_cast
    linear_combination ih

theorem inner_e (n : ℕ) (p : ℤ) (hp : p ∈ I n) :
    ∑ q ∈ I n, (if q = 0 ∨ p + q = 0 then (1 : ℤ) else 0) = if p = 0 then 1 else 2 := by
  rw [sum_boole]
  simp only [I, mem_Icc] at hp
  by_cases h : p = 0
  · have he : (I n).filter (fun q => q = 0 ∨ p + q = 0) = {0} := by
      ext q
      simp only [I, mem_filter, mem_Icc, mem_singleton]
      omega
    rw [he, if_pos h, card_singleton, Nat.cast_one]
  · have he : (I n).filter (fun q => q = 0 ∨ p + q = 0) = {0, -p} := by
      ext q
      simp only [I, mem_filter, mem_Icc, mem_insert, mem_singleton]
      omega
    rw [he, if_neg h, card_pair (by omega)]
    norm_num

theorem E_eq (n : ℕ) :
    ∑ p ∈ I n, ∑ q ∈ I n, (if q = 0 ∨ p + q = 0 then (1 : ℤ) else 0) = 4 * n + 1 := by
  rw [sum_congr rfl (fun p hp => inner_e n p hp)]
  have h : ∀ p ∈ I n, (if p = 0 then (1 : ℤ) else 2) = 2 - (if p = 0 then 1 else 0) := by
    intro p _
    split_ifs <;> norm_num
  rw [sum_congr rfl h, sum_sub_distrib, sum_const, card_I, sum_ite_eq' (I n) 0,
    if_pos (zero_mem_I n), nsmul_eq_mul]
  push_cast
  ring

theorem D_eq (n : ℕ) :
    ∑ p ∈ I n, ∑ q ∈ I n, (if p = 0 ∧ q = 0 then 2 * (n : ℤ) else 0) = 2 * n := by
  have h : ∀ p ∈ I n, ∑ q ∈ I n, (if p = 0 ∧ q = 0 then 2 * (n : ℤ) else 0) =
      if p = 0 then 2 * (n : ℤ) else 0 := by
    intro p _
    by_cases hp : p = 0
    · simp only [hp, true_and, if_true]
      rw [sum_ite_eq' (I n) 0, if_pos (zero_mem_I n)]
    · simp only [hp, false_and, if_false, sum_const_zero]
  rw [sum_congr rfl h, sum_ite_eq' (I n) 0, if_pos (zero_mem_I n)]

/-- The closed form `3 a(n) = 16 n^3 + 24 n^2 - 4 n`, for every `n`. -/
theorem a_closed (n : ℕ) : 3 * (a n : ℤ) = 16 * n ^ 3 + 24 * n ^ 2 - 4 * n := by
  rw [a_eq_card_T, card_T]
  push_cast
  rw [sum_congr rfl (fun p hp => sum_congr rfl (fun q hq => card_fiber n p q hp hq))]
  simp only [sum_sub_distrib]
  rw [E_eq, D_eq]
  have hH := H_eq n
  unfold H at hH
  simp only [sum_const, card_I, nsmul_eq_mul]
  push_cast
  linear_combination (-1 : ℤ) * hH

theorem closedQ (n : ℕ) : (a n : ℚ) = (16 * (n : ℚ) ^ 3 + 24 * n ^ 2 - 4 * n) / 3 := by
  have h := a_closed n
  have h' : 3 * (a n : ℚ) = 16 * (n : ℚ) ^ 3 + 24 * n ^ 2 - 4 * n := by exact_mod_cast h
  linarith

theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have h : (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
    rw [closedQ n, closedQ (n - 1), closedQ (n - 2), closedQ (n - 3), closedQ (n - 4)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      4 * X * (3 + 6 * X - X ^ 2) := by
  have hF : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      fun n : ℕ => (16 * (n : ℚ) ^ 3 + 24 * n ^ 2 - 4 * n) / 3 := by
    funext n
    split_ifs with h
    · subst h
      norm_num
    · exact closedQ n
  rw [hF]
  set A : ℚ⟦X⟧ := PowerSeries.mk fun n : ℕ => (16 * (n : ℚ) ^ 3 + 24 * n ^ 2 - 4 * n) / 3
    with hA
  have hpow : A * ((1 : ℚ⟦X⟧) - X) ^ 4 =
      C (1 : ℚ) * (A * X ^ 0) - C (4 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2) -
        C (4 : ℚ) * (A * X ^ 3) + C (1 : ℚ) * (A * X ^ 4) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (4 : ℚ⟦X⟧) * X * (3 + 6 * X - X ^ 2) =
      C (12 : ℚ) * X ^ 1 + C (24 : ℚ) * X ^ 2 - C (4 : ℚ) * X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [hpow, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk]
  by_cases hk : k < 4
  · interval_cases k <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 4 := ⟨k - 4, by omega⟩
    simp only [show 0 ≤ j + 4 by omega, show 1 ≤ j + 4 by omega, show 2 ≤ j + 4 by omega,
      show 3 ≤ j + 4 by omega, show 4 ≤ j + 4 by omega, show j + 4 - 0 = j + 4 by omega,
      show j + 4 - 1 = j + 3 by omega, show j + 4 - 2 = j + 2 by omega,
      show j + 4 - 3 = j + 1 by omega, show j + 4 - 4 = j by omega,
      show ¬ (j + 4 = 1) by omega, show ¬ (j + 4 = 2) by omega, show ¬ (j + 4 = 3) by omega,
      if_true, if_false]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a199531.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
