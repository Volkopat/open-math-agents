import OMAStatements.S_oeis_a269410

-- Problem: A269410: Number of length-4 0..n arrays with no repeated value greater than or equal to the previous repeated value.
-- Upstream: formal-conjectures statements/oeis-a269410.lean:0 (declaration OMA.S_oeis_a269410.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: sort the arrays (w, x, y, z) by the middle entries (x, y). With S = 0..n, the
-- admissible (w, z) are: all of S x S minus the row w = x and the column z = x if x = y
-- (n^2 pairs), all of S x S minus the pair (x, y) if x < y, and all of S x S if x > y. Summing over
-- x for fixed y gives (n+1)^3 - (2n+1) - y, and summing over y gives
-- 2a(n) = 2(n+1)^4 - 2(n+1)(2n+1) - n(n+1). The recurrence is the vanishing fifth difference of
-- this quartic, and the g.f. follows by comparing coefficients.

open OMA.S_oeis_a269410 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269410.main := by
  obtain ⟨fib, hfib⟩ : ∃ fib : ℕ → ℕ → ℕ → ℕ, ∀ n x y, fib n x y =
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p : ℕ × ℕ => ok p.1 x y p.2)).card :=
    ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨col, hcol⟩ : ∃ col : ℕ → ℕ → ℕ, ∀ n y, col n y =
      ∑ x ∈ Finset.range (n + 1), fib n x y :=
    ⟨_, fun _ _ => rfl⟩
  have hS : ∀ n x, x ≤ n → x ∈ Finset.range (n + 1) := by
    intro n x hx
    rw [Finset.mem_range]
    omega
  have hfs : ∀ n x y, (∑ w ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1),
      (if ok w x y z then 1 else 0)) = fib n x y := by
    intro n x y
    rw [hfib, Finset.card_filter]
    simp only [Finset.sum_product]
  have hsum : ∀ n, a n = ∑ y ∈ Finset.range (n + 1), col n y := by
    intro n
    calc a n = ∑ w ∈ Finset.range (n + 1), ∑ x ∈ Finset.range (n + 1),
          ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1),
            (if ok w x y z then 1 else 0) := by
          unfold a
          rw [Finset.card_filter]
          simp only [Finset.sum_product]
      _ = ∑ x ∈ Finset.range (n + 1), ∑ w ∈ Finset.range (n + 1),
          ∑ y ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1),
            (if ok w x y z then 1 else 0) := Finset.sum_comm
      _ = ∑ x ∈ Finset.range (n + 1), ∑ y ∈ Finset.range (n + 1),
          ∑ w ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1),
            (if ok w x y z then 1 else 0) :=
          Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
      _ = ∑ y ∈ Finset.range (n + 1), ∑ x ∈ Finset.range (n + 1),
          ∑ w ∈ Finset.range (n + 1), ∑ z ∈ Finset.range (n + 1),
            (if ok w x y z then 1 else 0) := Finset.sum_comm
      _ = ∑ y ∈ Finset.range (n + 1), col n y := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          rw [hcol]
          exact Finset.sum_congr rfl (fun x _ => hfs n x y)
  have hfeq : ∀ n x y, x = y → y ≤ n → fib n x y = n * n := by
    intro n x y hxy hy
    rw [hfib]
    have e : (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p : ℕ × ℕ => ok p.1 x y p.2) =
        (Finset.range (n + 1)).erase x ×ˢ (Finset.range (n + 1)).erase y := by
      ext ⟨w, z⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_erase, ok]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [e, Finset.card_product, Finset.card_erase_of_mem (hS n x (by omega)),
      Finset.card_erase_of_mem (hS n y hy), Finset.card_range, Nat.add_sub_cancel]
  have hflt : ∀ n x y, x < y → y ≤ n → fib n x y + 1 = (n + 1) * (n + 1) := by
    intro n x y hxy hy
    rw [hfib]
    have e : (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p : ℕ × ℕ => ok p.1 x y p.2) =
        (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).erase (x, y) := by
      ext ⟨w, z⟩
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_product, Finset.mem_range, ok,
        ne_eq, Prod.mk.injEq]
      constructor
      · intro h
        omega
      · intro h
        omega
    have hmem : (x, y) ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1) :=
      Finset.mem_product.mpr ⟨hS n x (by omega), hS n y hy⟩
    have hp : 1 ≤ (n + 1) * (n + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [e, Finset.card_erase_of_mem hmem, Finset.card_product, Finset.card_range,
      Nat.sub_add_cancel hp]
  have hfgt : ∀ n x y, y < x → fib n x y = (n + 1) * (n + 1) := by
    intro n x y hxy
    rw [hfib]
    have e : (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun p : ℕ × ℕ => ok p.1 x y p.2) =
        Finset.range (n + 1) ×ˢ Finset.range (n + 1) := by
      ext ⟨w, z⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, ok]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [e, Finset.card_product, Finset.card_range]
  have hcolv : ∀ n y, y ≤ n → col n y + (2 * n + 1) + y = (n + 1) * ((n + 1) * (n + 1)) := by
    intro n y hy
    have hpt : ∀ x ∈ Finset.range (n + 1), fib n x y + (if x = y then 2 * n + 1 else 0) +
        (if x < y then 1 else 0) = (n + 1) * (n + 1) := by
      intro x _
      rcases lt_trichotomy x y with h | h | h
      · rw [if_neg (show ¬ (x = y) by omega), if_pos h, add_zero]
        exact hflt n x y h hy
      · rw [if_pos h, if_neg (show ¬ (x < y) by omega), add_zero, hfeq n x y h hy]
        ring
      · rw [if_neg (show ¬ (x = y) by omega), if_neg (show ¬ (x < y) by omega), add_zero,
          add_zero]
        exact hfgt n x y h
    have hs := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (hS n y hy),
      ← Finset.card_filter, Finset.sum_const, Finset.card_range, smul_eq_mul, ← hcol n y] at hs
    have hf : (Finset.range (n + 1)).filter (fun x => x < y) = Finset.range y := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        omega
      · intro h
        omega
    rw [hf, Finset.card_range] at hs
    exact hs
  have hcf : ∀ n, 2 * a n + 2 * ((n + 1) * (2 * n + 1)) + (n + 1) * n =
      2 * ((n + 1) * ((n + 1) * ((n + 1) * (n + 1)))) := by
    intro n
    have hpt : ∀ y ∈ Finset.range (n + 1),
        col n y + (2 * n + 1) + y = (n + 1) * ((n + 1) * (n + 1)) := by
      intro y hy
      rw [Finset.mem_range] at hy
      exact hcolv n y (by omega)
    have hs := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_range, smul_eq_mul, smul_eq_mul, ← hsum n] at hs
    have hg := Finset.sum_range_id_mul_two (n + 1)
    rw [Nat.add_sub_cancel] at hg
    linarith
  have hcfz : ∀ n : ℕ, (2 : ℤ) * (a n : ℤ) + 2 * (((n : ℤ) + 1) * (2 * (n : ℤ) + 1)) +
      ((n : ℤ) + 1) * (n : ℤ) =
      2 * (((n : ℤ) + 1) * (((n : ℤ) + 1) * (((n : ℤ) + 1) * ((n : ℤ) + 1)))) := by
    intro n
    exact_mod_cast hcf n
  have hcfq : ∀ n : ℕ, (2 : ℚ) * (a n : ℚ) + 2 * (((n : ℚ) + 1) * (2 * (n : ℚ) + 1)) +
      ((n : ℚ) + 1) * (n : ℚ) =
      2 * (((n : ℚ) + 1) * (((n : ℚ) + 1) * (((n : ℚ) + 1) * ((n : ℚ) + 1)))) := by
    intro n
    exact_mod_cast hcf n
  have a0 : a 0 = 0 := by
    have h := hcf 0
    norm_num at h
    omega
  have a1 : a 1 = 9 := by
    have h := hcf 1
    norm_num at h
    omega
  have a2 : a 2 = 63 := by
    have h := hcf 2
    norm_num at h
    omega
  have a3 : a 3 = 222 := by
    have h := hcf 3
    norm_num at h
    omega
  have a4 : a 4 = 570 := by
    have h := hcf 4
    norm_num at h
    omega
  have q0 : (a 0 : ℚ) = 0 := by exact_mod_cast a0
  have q1 : (a 1 : ℚ) = 9 := by exact_mod_cast a1
  have q2 : (a 2 : ℚ) = 63 := by exact_mod_cast a2
  have q3 : (a 3 : ℚ) = 222 := by exact_mod_cast a3
  have q4 : (a 4 : ℚ) = 570 := by exact_mod_cast a4
  have hq : ∀ m, 5 ≤ m → (a m : ℚ) - 5 * (a (m - 1) : ℚ) + 10 * (a (m - 2) : ℚ) -
      10 * (a (m - 3) : ℚ) + 5 * (a (m - 4) : ℚ) - (a (m - 5) : ℚ) = 0 := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
      show k + 5 - 5 = k by omega]
    have h0 := hcfq k
    have h1 := hcfq (k + 1)
    have h2 := hcfq (k + 2)
    have h3 := hcfq (k + 3)
    have h4 := hcfq (k + 4)
    have h5 := hcfq (k + 5)
    push_cast at h1 h2 h3 h4 h5
    linarith
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega,
      show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega]
    have h1 := hcfz (k + 1)
    have h2 := hcfz (k + 2)
    have h3 := hcfz (k + 3)
    have h4 := hcfz (k + 4)
    have h5 := hcfz (k + 5)
    have h6 := hcfz (k + 6)
    push_cast at h1 h2 h3 h4 h5 h6
    linarith
  · have e : PowerSeries.mk (fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 5 =
        PowerSeries.mk (fun n => (a n : ℚ))
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 *
            (PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4)
          - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10]
      ring
    have e2 : (3 * PowerSeries.X * (3 + 6 * PowerSeries.X - PowerSeries.X ^ 2) :
        PowerSeries ℚ) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9 * PowerSeries.X ^ 1
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18 * PowerSeries.X ^ 2
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * PowerSeries.X ^ 3 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 9,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 18,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3]
      ring
    rw [e, e2]
    ext m
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases Nat.lt_or_ge m 5 with hm | hm
    · interval_cases m
      · norm_num [q0]
      · norm_num [q0, q1]
      · norm_num [q0, q1, q2]
      · norm_num [q0, q1, q2, q3]
      · norm_num [q0, q1, q2, q3, q4]
    · simp (disch := omega) only [if_pos, if_neg]
      linarith [hq m hm]
