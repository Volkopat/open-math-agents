import OMAStatements.S_oeis_a326034

-- Problem: A326034: Number of knapsack partitions of n with largest part 3.
-- Upstream: formal-conjectures statements/oeis-a326034.lean:0 (declaration OMA.S_oeis_a326034.main)
-- Credit: @lettucrisp (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.


namespace OMA.A326034Proof
open OMA.S_oeis_a326034 Finset

/-- The explicit form of the knapsack condition when the part `3` occurs. -/
def K (x y z : ℕ) : Prop := (x = 0 ∧ (y ≤ 2 ∨ z = 1)) ∨ ((x = 1 ∨ x = 2) ∧ y = 0)

lemma knap_iff {x y z : ℕ} (hz : 0 < z) : Knapsack x y z ↔ K x y z := by
  constructor
  · intro h
    by_contra hK
    unfold K at hK
    push Not at hK
    by_cases hx : x = 0
    · obtain ⟨hy, hz2⟩ := hK.1 hx
      have := h 0 (by omega) 3 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) 2 (by omega) (by omega)
      omega
    · by_cases hx3 : 3 ≤ x
      · have := h 3 hx3 0 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) 1 (by omega) (by omega)
        omega
      · have hy : y ≠ 0 := hK.2 (by omega)
        have := h 1 (by omega) 1 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) 1 (by omega) (by omega)
        omega
  · intro hK x hx y hy z' hz' x' hx' y' hy' z'' hz'' e
    unfold K at hK
    refine ⟨by omega, by omega, by omega⟩

/-- The six possible shapes of a knapsack partition. -/
def gen (n : ℕ) : Fin 6 → ℕ × ℕ × ℕ
  | 0 => (0, 0, n / 3)
  | 1 => (0, 1, n / 3)
  | 2 => (2, 0, n / 3)
  | 3 => (0, 2, (n - 4) / 3)
  | 4 => (1, 0, n / 3)
  | 5 => (0, n / 2 - 1, 1)

def cond (n : ℕ) : Fin 6 → Bool
  | 0 => decide (n % 3 = 0 ∧ 3 ≤ n)
  | 1 => decide (n % 3 = 2 ∧ 5 ≤ n)
  | 2 => decide (n % 3 = 2 ∧ 5 ≤ n)
  | 3 => decide (n % 3 = 1 ∧ 7 ≤ n)
  | 4 => decide (n % 3 = 1 ∧ 4 ≤ n)
  | 5 => decide (n % 2 = 1 ∧ 9 ≤ n)

lemma mem_partitions (n : ℕ) (p : ℕ × ℕ × ℕ) :
    p ∈ partitions n ↔ ∃ i, cond n i = true ∧ gen n i = p := by
  obtain ⟨x, y, z⟩ := p
  simp only [partitions, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨hx, hy, hz⟩, hz0, he, hk⟩
    have hK := (knap_iff hz0).mp hk
    unfold K at hK
    rcases hK with ⟨rfl, hy2 | rfl⟩ | ⟨hx12, rfl⟩
    · rcases (show y = 0 ∨ y = 1 ∨ y = 2 by omega) with rfl | rfl | rfl
      · exact ⟨0, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
      · exact ⟨1, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
      · exact ⟨3, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
    · rcases (show y ≤ 2 ∨ 3 ≤ y by omega) with hy2 | hy3
      · rcases (show y = 0 ∨ y = 1 ∨ y = 2 by omega) with rfl | rfl | rfl
        · exact ⟨0, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
        · exact ⟨1, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
        · exact ⟨3, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
      · exact ⟨5, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
    · rcases hx12 with rfl | rfl
      · exact ⟨4, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
      · exact ⟨2, by simp only [cond, decide_eq_true_eq]; omega, by simp only [gen, Prod.mk.injEq, true_and, and_true]; omega⟩
  · rintro ⟨i, hc, hg⟩
    fin_cases i <;> simp only [cond, gen, Prod.mk.injEq, decide_eq_true_eq] at hc hg <;>
      obtain ⟨rfl, rfl, rfl⟩ := hg <;>
      refine ⟨⟨by omega, by omega, by omega⟩, by omega, by omega, (knap_iff (by omega)).mpr ?_⟩ <;>
      unfold K <;> omega

lemma a_eq (n : ℕ) : a n = ∑ i : Fin 6, if cond n i = true then 1 else 0 := by
  have h : partitions n = (Finset.univ.filter (fun i => cond n i = true)).image (gen n) := by
    ext p; rw [mem_partitions]; simp
  rw [a, h, Finset.card_image_of_injOn, Finset.card_filter]
  intro i hi j hj e
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  fin_cases i <;> fin_cases j <;> simp only [cond, gen, Prod.mk.injEq, decide_eq_true_eq] at hi hj e ⊢ <;> omega

/-- The closed form of `a`. -/
lemma a_formula (n : ℕ) : a n = (if 3 ≤ n then 1 else 0) + (if 5 ≤ n ∧ (n - 5) % 2 = 0 then 1 else 0)
    + (if 8 ≤ n ∧ (n - 8) % 3 = 0 then 1 else 0) + (if 10 ≤ n ∧ (n - 10) % 3 = 0 then 1 else 0) := by
  rw [a_eq, Fin.sum_univ_six]
  simp only [cond, decide_eq_true_eq]
  split_ifs <;> omega

open PowerSeries

lemma inv1 : (1 - X : PowerSeries ℚ)⁻¹ = mk (fun _ => 1) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  ext n
  rw [show (X : PowerSeries ℚ) = X ^ 1 from (pow_one X).symm, mul_sub, mul_one, map_sub,
    mul_comm, PowerSeries.coeff_X_pow_mul', coeff_mk, coeff_one]
  rcases n with _ | n <;> simp

lemma inv2 : (1 - X ^ 2 : PowerSeries ℚ)⁻¹ = mk (fun n => if n % 2 = 0 then 1 else 0) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  ext n
  rw [mul_sub, mul_one, map_sub, mul_comm, PowerSeries.coeff_X_pow_mul', coeff_mk, coeff_one]
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases h2 : 2 ≤ n
    · rw [if_pos h2, coeff_mk, if_neg h0]
      have : (n - 2) % 2 = n % 2 := by omega
      rw [this]; simp
    · rw [if_neg h2, if_neg h0]
      have : n = 1 := by omega
      subst this; simp

lemma inv3 : (1 - X ^ 3 : PowerSeries ℚ)⁻¹ = mk (fun n => if n % 3 = 0 then 1 else 0) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp)]
  ext n
  rw [mul_sub, mul_one, map_sub, mul_comm, PowerSeries.coeff_X_pow_mul', coeff_mk, coeff_one]
  by_cases h0 : n = 0
  · subst h0; simp
  · by_cases h3 : 3 ≤ n
    · rw [if_pos h3, coeff_mk, if_neg h0]
      have : (n - 3) % 3 = n % 3 := by omega
      rw [this]; simp
    · rw [if_neg h3, if_neg h0]
      have : n % 3 ≠ 0 := by omega
      simp [this]

end OMA.A326034Proof

open OMA.A326034Proof OMA.S_oeis_a326034 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a326034.main := by
  refine ⟨?_, ?_⟩
  · rw [inv1, inv2, inv3]
    ext n
    rw [G, coeff_mk, a_formula]
    simp only [map_add, add_mul, PowerSeries.coeff_X_pow_mul', coeff_mk]
    push_cast
    split_ifs <;> first | rfl | omega | (exfalso; omega) | norm_num
  · intro n hn
    rw [a_formula, a_formula]
    split_ifs <;> omega
