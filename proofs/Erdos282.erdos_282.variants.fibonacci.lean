import FormalConjectures.ErdosProblems.«282»

open Erdos282

theorem OMA.R {A x} (h : x ≤ 0) (t) : greedyUnitFractionRem A x t = 0 := by
  cases t <;> simp [greedyUnitFractionRem, h]

theorem OMA.M (p : ℕ) : ∀ (q : ℕ) (A : Set ℕ) (x : ℚ), x = p / q → x < 1 → (∀ m ∉ A, (m : ℚ) < 1 / x) →
    ∀ t, p ≤ t + 1 → greedyUnitFractionRem A x t = 0 := by
  induction p using Nat.strong_induction_on with | _ p ih => ?_
  intro q A x e h1 hA t ht
  rcases le_or_gt x 0 with h0 | h0
  · exact OMA.R h0 t
  have hp : (0 : ℚ) < p := by rcases p with _ | p <;> simp_all <;> positivity
  have hq : (0 : ℚ) < q := by rcases q with _ | q <;> simp_all
  have h1N := Nat.le_ceil (1 / x)
  have hc : ⌈1 / x⌉₊ ∈ A := by_contra fun h => (hA _ h).not_ge h1N
  have hS : sInf {n | n ∈ A ∧ 1 / x ≤ n} = ⌈1 / x⌉₊ :=
    le_antisymm (Nat.sInf_le ⟨hc, h1N⟩) (le_csInf ⟨_, hc, h1N⟩ fun _ h => Nat.ceil_le.2 h.2)
  have h2N := Nat.ceil_lt_add_one (one_div_pos.2 h0).le
  have hN : (0 : ℚ) < ⌈1 / x⌉₊ := (one_div_pos.2 h0).trans_le h1N
  generalize ⌈1 / x⌉₊ = N at *
  rw [e, one_div_div, div_le_iff₀ hp] at h1N
  rw [e, one_div_div, div_add_one hp.ne', lt_div_iff₀ hp] at h2N
  have a : q ≤ N * p := by exact_mod_cast h1N
  have b : N * p < q + p := by exact_mod_cast h2N
  rcases t with _ | t <;> rw [greedyUnitFractionRem, if_neg h0.not_ge] <;> simp only [hS]
  · obtain rfl : p = 1 := by have := Nat.cast_pos.1 hp; omega
    simp [e, show N = q by omega]
  have hpq : (p : ℚ) < q := by rwa [e, div_lt_one hq] at h1
  have r : x - 1 / N = ((N * p - q : ℕ) : ℚ) / ((q * N : ℕ) : ℚ) := by
    rw [e, Nat.cast_sub a]; push_cast; field_simp
  rcases le_or_gt (x - 1 / N) 0 with h | h
  · exact OMA.R h t
  refine ih _ (by omega) _ _ _ r (by linarith [one_div_pos.2 hN]) ?_ t (by omega)
  intro m hm
  by_cases hmA : m ∈ A
  · obtain rfl : m = N := by by_contra hc; exact hm ⟨hmA, hc⟩
    rw [lt_div_iff₀ h, e]
    field_simp
    nlinarith
  · exact (hA m hmA).trans (one_div_lt_one_div_of_lt h (by linarith [one_div_pos.2 hN]))

theorem OMA.solution : type_of% @Erdos282.erdos_282.variants.fibonacci := by
  intro x hx
  obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (Rat.num_pos.2 hx.1).le
  refine Filter.eventually_atTop.2 ⟨p, fun t ht => OMA.M p x.den _ x ?_ hx.2 (by simp) t (by omega)⟩
  simpa [hp] using (Rat.num_div_den x).symm
