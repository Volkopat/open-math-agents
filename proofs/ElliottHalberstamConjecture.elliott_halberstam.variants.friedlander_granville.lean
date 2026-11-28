import FormalConjectures.Wikipedia.ElliottHalberstamConjecture

open Nat Finset Real

-- Problem: Elliott–Halberstam conjecture — friedlander granville
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/ElliottHalberstamConjecture.lean:73 (declaration ElliottHalberstamConjecture.elliott_halberstam.variants.friedlander_granville)
-- Credit: @senamakel (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open ElliottHalberstamConjecture in
theorem OMA.eh_key (x q : ℕ) (hq3 : 3 ≤ q) (hodd : q % 2 = 1) (hqx : q ≤ x) (hx : x < 2 * q + 1) :
    (1 / 2 : ℝ) ≤ E x q := by
  have : NeZero q := ⟨by omega⟩
  have hcop : Nat.Coprime 2 q := by
    rw [Nat.Prime.coprime_iff_not_dvd prime_two]
    omega
  set u : (ZMod q)ˣ := ZMod.unitOfCoprime 2 hcop
  have hu : ((u : (ZMod q)) ) = ((2 : ℕ) : ZMod q) := rfl
  set m : ℝ := (x.primeCounting : ℝ) / (q.totient : ℝ)
  have hbdd : BddAbove (Set.range fun a : (ZMod q)ˣ =>
      |(x.primeCountingMod q a : ℝ) - m|) := (Set.finite_range _).bddAbove
  have h1 : |(x.primeCountingMod q ((1 : (ZMod q)ˣ) : ZMod q) : ℝ) - m| ≤ E x q :=
    le_ciSup hbdd (1 : (ZMod q)ˣ)
  have h2 : |(x.primeCountingMod q (u : ZMod q) : ℝ) - m| ≤ E x q :=
    le_ciSup hbdd u
  have hn1 : x.primeCountingMod q ((1 : (ZMod q)ˣ) : ZMod q) = 0 := by
    have : ((1 : (ZMod q)ˣ) : ZMod q) = ((1 : ℕ) : ZMod q) := by simp
    rw [this, Nat.primeCountingMod_natCast_eq_card_filter_mod, Finset.card_eq_zero,
      filter_eq_empty_iff]
    rintro p hp ⟨hpp, hpm⟩
    rw [mem_Icc] at hp
    rw [mod_eq_of_lt (by omega : 1 < q)] at hpm
    have hp' : p = 1 ∨ p = q + 1 := by
      have h0 := div_add_mod p q
      rw [hpm] at h0
      have hdiv : p / q ≤ 2 := Nat.div_le_of_le_mul (by omega)
      interval_cases h : p / q <;> omega
    rcases hp' with rfl | rfl
    · exact Nat.not_prime_one hpp
    · have := hpp.eq_one_or_self_of_dvd 2 (by omega)
      omega
  have hn2 : 1 ≤ x.primeCountingMod q (u : ZMod q) := by
    rw [hu, Nat.primeCountingMod_natCast_eq_card_filter_mod, one_le_iff_ne_zero,
      Ne, Finset.card_eq_zero, ← Ne, ← nonempty_iff_ne_empty]
    refine ⟨2, ?_⟩
    rw [mem_filter, mem_Icc]
    exact ⟨⟨by omega, by omega⟩, prime_two, rfl⟩
  rw [hn1] at h1
  have hn2' : (1 : ℝ) ≤ (x.primeCountingMod q (u : ZMod q) : ℝ) := by exact_mod_cast hn2
  have := abs_sub_abs_le_abs_sub ((x.primeCountingMod q (u : ZMod q) : ℝ)) m
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (x.primeCountingMod q (u : ZMod q) : ℝ))] at this
  push_cast at h1
  rw [zero_sub, abs_neg] at h1
  linarith

open ElliottHalberstamConjecture in
theorem OMA.solution : type_of% @ElliottHalberstamConjecture.elliott_halberstam.variants.friedlander_granville := by
  intro h
  obtain ⟨C, hC, hb⟩ := h 1 one_pos
  set N : ℕ := ⌈exp (8 * C + 1)⌉₊ + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hx := hb (4 * N) (by omega)
  -- lower bound on the sum
  have hsub : (range N).image (fun i => 2 * N + 1 + 2 * i) ⊆ Finset.Icc 1 (4 * N) := by
    intro q hq
    simp only [mem_image, mem_range] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    simp only [mem_Icc]; omega
  have hnn : ∀ q ∈ Finset.Icc 1 (4 * N), q ∉ (range N).image (fun i => 2 * N + 1 + 2 * i) →
      (0 : ℝ) ≤ E (4 * N) q := fun q _ _ => iSup_nonneg fun _ => abs_nonneg _
  have hlow := sum_le_sum_of_subset_of_nonneg hsub hnn
  rw [sum_image (by intro a _ b _ hab; simp only at hab; omega)] at hlow
  have hlow2 : ∑ i ∈ range N, (1 / 2 : ℝ) ≤
      ∑ i ∈ range N, E (4 * N) (2 * N + 1 + 2 * i) := by
    apply sum_le_sum
    intro i hi
    rw [mem_range] at hi
    exact OMA.eh_key _ _ (by omega) (by omega) (by omega) (by omega)
  simp only [sum_const, card_range, nsmul_eq_mul] at hlow2
  have hsum : (N : ℝ) * (1 / 2) ≤ C * ((4 * N : ℕ) : ℝ) / Real.log ((4 * N : ℕ) : ℝ) ^ (1 : ℝ) :=
    hlow2.trans (hlow.trans hx)
  rw [rpow_one] at hsum
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hexp : exp (8 * C + 1) < ((4 * N : ℕ) : ℝ) := by
    have := le_ceil (exp (8 * C + 1))
    push_cast
    have : (⌈exp (8 * C + 1)⌉₊ : ℝ) + 1 = N := by rw [hN]; push_cast; ring
    linarith
  have hlog : 8 * C + 1 < Real.log ((4 * N : ℕ) : ℝ) := by
    rw [lt_log_iff_exp_lt (by positivity)]; exact hexp
  have hlpos : 0 < Real.log ((4 * N : ℕ) : ℝ) := by linarith
  rw [le_div_iff₀ hlpos] at hsum
  push_cast at hsum hlog
  nlinarith [mul_lt_mul_of_pos_left hlog hNpos]
