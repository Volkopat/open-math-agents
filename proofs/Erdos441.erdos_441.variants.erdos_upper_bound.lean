import FormalConjectures.ErdosProblems.«441»

-- Problem: Erdős Problem 441 — erdos upper bound
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/441.lean:114 (declaration Erdos441.erdos_441.variants.erdos_upper_bound)
-- Credit: @philipsaint (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E441

lemma div_lt_div_of_lcm (N a b : ℕ) (ha : 0 < a) (hab : a < b) (hl : Nat.lcm a b ≤ N) :
    N / b < N / a := by
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := ⟨b - a, by omega⟩
  have hc : 0 < c := by omega
  have hdvd : Nat.gcd a (a + c) ∣ c := by
    simpa using Nat.dvd_sub (Nat.gcd_dvd_right a (a + c)) (Nat.gcd_dvd_left a (a + c))
  have hd : Nat.gcd a (a + c) ≤ c := Nat.le_of_dvd hc hdvd
  have hm : Nat.gcd a (a + c) * Nat.lcm a (a + c) = a * (a + c) := Nat.gcd_mul_lcm a (a + c)
  have key : a * (a + c) ≤ c * N := by
    rw [← hm]
    exact Nat.mul_le_mul hd hl
  set q := N / (a + c) with hqdef
  have hq : q * (a + c) ≤ N := Nat.div_mul_le_self N (a + c)
  have h3 : (q + 1) * a * (a + c) ≤ N * (a + c) := by
    have h5 := Nat.mul_le_mul_right a hq
    nlinarith [h5, key]
  have h4 : (q + 1) * a ≤ N := Nat.le_of_mul_le_mul_right h3 (by omega)
  have h6 : q + 1 ≤ N / a := (Nat.le_div_iff_mul_le ha).2 h4
  omega

lemma bound (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hl : ∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) : A.card ≤ 2 * Nat.sqrt N := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (fun a => a * a ≤ N)]
  have h1 : (A.filter (fun a => a * a ≤ N)).card ≤ Nat.sqrt N := by
    refine (Finset.card_le_card fun a ha => ?_).trans (Nat.card_Icc 1 _).le
    rw [Finset.mem_filter] at ha
    exact Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 (hA ha.1)).1, Nat.le_sqrt.2 ha.2⟩
  have h2 : (A.filter (fun a => ¬ a * a ≤ N)).card ≤ Nat.sqrt N := by
    refine (Finset.card_le_card_of_injOn (fun a => N / a) ?_ ?_).trans (Nat.card_Icc 1 _).le
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      have h := Finset.mem_Icc.1 (hA ha.1)
      rw [Finset.mem_coe, Finset.mem_Icc]
      have hlt : N / a < a := (Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)
      refine ⟨Nat.div_pos h.2 (by omega), Nat.le_sqrt.2 ?_⟩
      calc N / a * (N / a) ≤ N / a * a := Nat.mul_le_mul_left _ hlt.le
        _ ≤ N := Nat.div_mul_le_self N a
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      have ha1 := Finset.mem_Icc.1 (hA ha.1)
      have hb1 := Finset.mem_Icc.1 (hA hb.1)
      simp only at hab
      rcases lt_trichotomy a b with h | h | h
      · have := div_lt_div_of_lcm N a b (by omega) h (hl a ha.1 b hb.1)
        omega
      · exact h
      · have := div_lt_div_of_lcm N b a (by omega) h (hl b hb.1 a ha.1)
        omega
  omega

end OMA.E441

theorem OMA.solution : type_of% @Erdos441.erdos_441.variants.erdos_upper_bound := by
  refine ⟨0, fun N => ?_⟩
  have hg : Erdos441.g N ≤ 2 * Nat.sqrt N := by
    unfold Erdos441.g
    apply csSup_le'
    rintro k ⟨A, hA, hl, rfl⟩
    exact OMA.E441.bound N A hA hl
  have h4 : √(4 * (N : ℝ)) = 2 * √(N : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [add_zero, h4]
  calc (Erdos441.g N : ℝ) ≤ 2 * (Nat.sqrt N : ℝ) := by exact_mod_cast hg
    _ ≤ 2 * √(N : ℝ) := by
      gcongr
      exact Real.nat_sqrt_le_real_sqrt
