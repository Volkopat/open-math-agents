import OMAStatements.S_oeis_a269685

-- Problem: A269685: Number of length-n 0..3 arrays with no repeated value differing from the previous repeated value by plus or minus one modulo 3+1.
-- Upstream: formal-conjectures statements/oeis-a269685.lean:0 (declaration OMA.S_oeis_a269685.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (as for A269684): let V(m, p, v) count the admissible arrays of length m+1 that
-- start with v when p is the latest repeated value before them. Splitting off the second entry u
-- (Fin.consEquiv): V(m+1, p, v) = [compat p v] V(m, v, v) + Sum_{u != v} V(m, p, u). Every value
-- is compatible after exactly 2 previous repeated values. With F = Sum_v V(., none, v),
-- G = Sum_r V(., r, r) and T = Sum_r Sum_v V(., r, v) this gives F' = 3F + G, T' = 2G + 3T and
-- G' = T (a value is compatible with itself), so a(n+1) = F(n) satisfies
-- a(n+3) = 6a(n+2) - 7a(n+1) - 6a(n), with a(1), a(2), a(3) = 4, 16, 64. The closed form follows
-- by induction (3 and the roots of x^2 - 3x - 2 are the roots of the characteristic polynomial),
-- and the g.f. by comparing coefficients.

namespace P1A269685

open OMA.S_oeis_a269685

theorem ok_cc (p : Option ℕ) (x y : ℕ) (t : List ℕ) :
    ok p (x :: y :: t) = if x = y then compat p x && ok (some x) (y :: t) else ok p (y :: t) := by
  rw [ok.eq_1]

theorem ok_one (p : Option ℕ) (x : ℕ) : ok p [x] = true := by
  simp [ok]

theorem hL (m : ℕ) (x : Fin (m + 1) → Fin 4) :
    List.ofFn (fun i => ((x i : Fin 4) : ℕ)) =
      ((x 0 : Fin 4) : ℕ) :: List.ofFn (fun i => ((Fin.tail x i : Fin 4) : ℕ)) :=
  List.ofFn_succ

theorem consSplit (m : ℕ) (P : List ℕ → Bool) :
    (∑ x : Fin (m + 1) → Fin 4,
        if P (List.ofFn (fun i => ((x i : Fin 4) : ℕ))) = true then (1 : ℕ) else 0) =
      ∑ v : Fin 4, ∑ t : Fin m → Fin 4,
        if P ((v : ℕ) :: List.ofFn (fun i => ((t i : Fin 4) : ℕ))) = true then (1 : ℕ) else 0 := by
  have h1 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 4)).symm
    (fun x : Fin (m + 1) → Fin 4 =>
      if P (List.ofFn (fun i => ((x i : Fin 4) : ℕ))) = true then (1 : ℕ) else 0)
    (fun p : Fin 4 × (Fin m → Fin 4) =>
      if P ((p.1 : ℕ) :: List.ofFn (fun i => ((p.2 i : Fin 4) : ℕ))) = true then (1 : ℕ) else 0)
    (fun x => congrArg (fun l => if P l = true then (1 : ℕ) else 0) (hL m x))
  exact h1.trans (Fintype.sum_prod_type _)

theorem hcr : ∀ r : Fin 4, compat (some (r : ℕ)) (r : ℕ) = true := by
  decide

theorem hcnt (v : Fin 4) :
    (∑ r : Fin 4, if compat (some (r : ℕ)) (v : ℕ) = true then (1 : ℕ) else 0) = 2 := by
  rw [Fin.sum_univ_four]
  revert v
  decide

theorem hpull (v : Fin 4) (X : ℕ) :
    (∑ r : Fin 4, if compat (some (r : ℕ)) (v : ℕ) = true then X else 0) = 2 * X := by
  calc (∑ r : Fin 4, if compat (some (r : ℕ)) (v : ℕ) = true then X else 0)
      = ∑ r : Fin 4, (if compat (some (r : ℕ)) (v : ℕ) = true then (1 : ℕ) else 0) * X := by
        refine Finset.sum_congr rfl (fun r _ => ?_)
        by_cases h : compat (some (r : ℕ)) (v : ℕ) = true
        · rw [if_pos h, if_pos h, one_mul]
        · rw [if_neg h, if_neg h, zero_mul]
    _ = 2 * X := by
        rw [← Finset.sum_mul, hcnt v]

end P1A269685

open OMA.S_oeis_a269685 P1A269685 in
theorem OMA.solution : type_of% @OMA.S_oeis_a269685.main := by
  obtain ⟨V, hVd⟩ : ∃ V : ℕ → Option ℕ → Fin 4 → ℕ, ∀ m p v, V m p v =
      ∑ t : Fin m → Fin 4,
        (if ok p ((v : ℕ) :: List.ofFn (fun i => ((t i : Fin 4) : ℕ))) = true then (1 : ℕ)
          else 0) :=
    ⟨_, fun _ _ _ => rfl⟩
  have hV0 : ∀ p v, V 0 p v = 1 := by
    intro p v
    rw [hVd, Fintype.sum_unique, List.ofFn_zero, if_pos (ok_one p (v : ℕ))]
  have hV1 : ∀ m p v, V (m + 1) p v = ∑ u : Fin 4,
      (if v = u then (if compat p (v : ℕ) = true then V m (some (v : ℕ)) u else 0)
        else V m p u) := by
    intro m p v
    rw [hVd, consSplit m (fun l => ok p ((v : ℕ) :: l))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases h : v = u
    · have hvu : (v : ℕ) = (u : ℕ) := congrArg Fin.val h
      rw [if_pos h, hVd]
      cases hc : compat p (v : ℕ)
      · rw [if_neg (show ¬ (false = true) by decide)]
        refine Finset.sum_eq_zero (fun t _ => ?_)
        rw [ok_cc, if_pos hvu, hc, Bool.false_and, if_neg (show ¬ (false = true) by decide)]
      · rw [if_pos rfl]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [ok_cc, if_pos hvu, hc, Bool.true_and]
    · rw [if_neg h, hVd]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [ok_cc, if_neg (show ¬ ((v : ℕ) = (u : ℕ)) from fun h' => h (Fin.ext h'))]
  have hV2 : ∀ m p v, V (m + 1) p v + V m p v =
      (if compat p (v : ℕ) = true then V m (some (v : ℕ)) v else 0) +
        ∑ u : Fin 4, V m p u := by
    intro m p v
    have hpt : ∀ u ∈ (Finset.univ : Finset (Fin 4)),
        (if v = u then (if compat p (v : ℕ) = true then V m (some (v : ℕ)) u else 0)
          else V m p u) + (if v = u then V m p u else 0) =
          (if v = u then (if compat p (v : ℕ) = true then V m (some (v : ℕ)) u else 0)
            else 0) + V m p u := by
      intro u _
      by_cases h : v = u
      · rw [if_pos h, if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg h, zero_add, add_zero]
    have hs := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ v), if_pos (Finset.mem_univ v), ← hV1 m p v] at hs
    exact hs
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ, ∀ m, F m = ∑ v : Fin 4, V m none v := ⟨_, fun _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ, ∀ m, G m = ∑ r : Fin 4, V m (some (r : ℕ)) r :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = ∑ r : Fin 4, ∑ v : Fin 4, V m (some (r : ℕ)) v :=
    ⟨_, fun _ => rfl⟩
  have eF : ∀ m, F (m + 1) = 3 * F m + G m := by
    intro m
    have p1 : ∀ v : Fin 4, V (m + 1) none v + V m none v =
        V m (some (v : ℕ)) v + ∑ u : Fin 4, V m none u := by
      intro v
      have h := hV2 m none v
      rw [if_pos (show compat none (v : ℕ) = true from rfl)] at h
      exact h
    have hs : ∑ v : Fin 4, (V (m + 1) none v + V m none v) =
        ∑ v : Fin 4, (V m (some (v : ℕ)) v + ∑ u : Fin 4, V m none u) :=
      Finset.sum_congr rfl (fun v _ => p1 v)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hs
    rw [hF, hF, hG]
    omega
  have eG : ∀ m, G (m + 1) = T m := by
    intro m
    have p2 : ∀ r : Fin 4, V (m + 1) (some (r : ℕ)) r = ∑ u : Fin 4, V m (some (r : ℕ)) u := by
      intro r
      have h := hV2 m (some (r : ℕ)) r
      rw [if_pos (hcr r)] at h
      omega
    rw [hG, hT]
    exact Finset.sum_congr rfl (fun r _ => p2 r)
  have eT : ∀ m, T (m + 1) = 2 * G m + 3 * T m := by
    intro m
    have p3 : ∀ r : Fin 4, ∑ v : Fin 4, V (m + 1) (some (r : ℕ)) v +
        ∑ v : Fin 4, V m (some (r : ℕ)) v =
        ∑ v : Fin 4, (if compat (some (r : ℕ)) (v : ℕ) = true then V m (some (v : ℕ)) v else 0) +
          4 * ∑ u : Fin 4, V m (some (r : ℕ)) u := by
      intro r
      have hs : ∑ v : Fin 4, (V (m + 1) (some (r : ℕ)) v + V m (some (r : ℕ)) v) =
          ∑ v : Fin 4, ((if compat (some (r : ℕ)) (v : ℕ) = true then
            V m (some (v : ℕ)) v else 0) + ∑ u : Fin 4, V m (some (r : ℕ)) u) :=
        Finset.sum_congr rfl (fun v _ => hV2 m (some (r : ℕ)) v)
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hs
      exact hs
    have hdbl : ∑ r : Fin 4, ∑ v : Fin 4,
        (if compat (some (r : ℕ)) (v : ℕ) = true then V m (some (v : ℕ)) v else 0) = 2 * G m := by
      rw [Finset.sum_comm, hG, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun v _ => hpull v (V m (some (v : ℕ)) v))
    have hs2 : ∑ r : Fin 4, (∑ v : Fin 4, V (m + 1) (some (r : ℕ)) v +
        ∑ v : Fin 4, V m (some (r : ℕ)) v) =
        ∑ r : Fin 4, (∑ v : Fin 4,
          (if compat (some (r : ℕ)) (v : ℕ) = true then V m (some (v : ℕ)) v else 0) +
          4 * ∑ u : Fin 4, V m (some (r : ℕ)) u) :=
      Finset.sum_congr rfl (fun r _ => p3 r)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hdbl, ← Finset.mul_sum] at hs2
    rw [hT, hT]
    omega
  have hAa : ∀ m, a (m + 1) = F m := by
    intro m
    rw [hF]
    unfold a
    rw [Finset.card_filter, consSplit m (ok none)]
    exact Finset.sum_congr rfl (fun v _ => (hVd m none v).symm)
  have hF0 : F 0 = 4 := by
    rw [hF]
    simp [hV0]
  have hG0 : G 0 = 4 := by
    rw [hG]
    simp [hV0]
  have hT0 : T 0 = 16 := by
    rw [hT]
    simp [hV0]
  have hF1 : F 1 = 16 := by
    have e := eF 0
    rw [show (0 : ℕ) + 1 = 1 from rfl] at e
    omega
  have hG1 : G 1 = 16 := by
    have e := eG 0
    rw [show (0 : ℕ) + 1 = 1 from rfl] at e
    omega
  have hF2 : F 2 = 64 := by
    have e := eF 1
    rw [show (1 : ℕ) + 1 = 2 from rfl] at e
    omega
  have hrecF : ∀ k, F (k + 3) + 7 * F (k + 1) + 6 * F k = 6 * F (k + 2) := by
    intro k
    have e1 := eF k
    have e2 := eF (k + 1)
    have e3 := eF (k + 2)
    have g1 := eG k
    have g2 := eG (k + 1)
    have t1 := eT k
    rw [show k + 1 + 1 = k + 2 by omega] at e2 g2
    rw [show k + 2 + 1 = k + 3 by omega] at e3
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (a (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
    have hmk : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk b := by
      congr 1
      funext n
      exact (hb n).symm
    have hbF : ∀ n, b n = (F n : ℚ) := by
      intro n
      rw [hb, hAa]
    have hb0 : b 0 = 4 := by
      rw [hbF]
      exact_mod_cast hF0
    have hb1 : b 1 = 16 := by
      rw [hbF]
      exact_mod_cast hF1
    have hb2 : b 2 = 64 := by
      rw [hbF]
      exact_mod_cast hF2
    have hr3 : ∀ m, 3 ≤ m →
        b m - 6 * b (m - 1) + 7 * b (m - 2) + 6 * b (m - 3) = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
        show k + 3 - 3 = k by omega, hbF (k + 3), hbF (k + 2), hbF (k + 1), hbF k]
      have h' : (F (k + 3) : ℚ) + 7 * F (k + 1) + 6 * F k = 6 * F (k + 2) := by
        exact_mod_cast hrecF k
      linarith
    have gfb : PowerSeries.mk b *
        ((1 - 3 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2)) =
        4 * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) := by
      have e : PowerSeries.mk b *
          ((1 - 3 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2)) =
          PowerSeries.mk b
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk b * PowerSeries.X ^ 1)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * (PowerSeries.mk b * PowerSeries.X ^ 2)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk b * PowerSeries.X ^ 3) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7]
        ring
      have e2 : (4 * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) : PowerSeries ℚ) =
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * PowerSeries.X ^ 0
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * PowerSeries.X ^ 1
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * PowerSeries.X ^ 2 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_C]
      rcases Nat.lt_or_ge m 3 with hm | hm
      · interval_cases m
        · norm_num [hb0]
        · norm_num [hb0, hb1]
        · norm_num [hb0, hb1, hb2]
      · simp (disch := omega) only [if_pos, if_neg]
        linarith [hr3 m hm]
    rw [hmk]
    calc PowerSeries.X * PowerSeries.mk b *
          ((1 - 3 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2))
        = PowerSeries.X * (PowerSeries.mk b *
          ((1 - 3 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2))) := by
          ring
      _ = PowerSeries.X * (4 * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) := by
          rw [gfb]
      _ = 4 * PowerSeries.X * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) := by
          ring
  · have hsq : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ x, c x = -17 * 2 ^ (2 + x) * 3 ^ x +
        (51 - 15 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ x +
        3 * (3 + Real.sqrt 17) ^ x * (17 + 5 * Real.sqrt 17) := ⟨_, fun _ => rfl⟩
    have hF0r : (F 0 : ℝ) = 4 := by exact_mod_cast hF0
    have hF1r : (F 1 : ℝ) = 16 := by exact_mod_cast hF1
    have hF2r : (F 2 : ℝ) = 64 := by exact_mod_cast hF2
    have trip : ∀ m, 51 * 2 ^ (m + 1) * (F m : ℝ) = c (m + 1) ∧
        51 * 2 ^ (m + 2) * (F (m + 1) : ℝ) = c (m + 2) ∧
        51 * 2 ^ (m + 3) * (F (m + 2) : ℝ) = c (m + 3) := by
      intro m
      induction m with
      | zero =>
        show 51 * 2 ^ 1 * (F 0 : ℝ) = c 1 ∧ 51 * 2 ^ 2 * (F 1 : ℝ) = c 2 ∧
          51 * 2 ^ 3 * (F 2 : ℝ) = c 3
        refine ⟨?_, ?_, ?_⟩
        · rw [hF0r, hc 1]
          linear_combination ((-30)) * hsq
        · rw [hF1r, hc 2]
          linear_combination ((-282)) * hsq
        · rw [hF2r, hc 3]
          linear_combination ((-2238) + (-30) * Real.sqrt 17 ^ 2) * hsq
      | succ k ih =>
        obtain ⟨i1, i2, i3⟩ := ih
        show 51 * 2 ^ (k + 2) * (F (k + 1) : ℝ) = c (k + 2) ∧
          51 * 2 ^ (k + 3) * (F (k + 2) : ℝ) = c (k + 3) ∧
          51 * 2 ^ (k + 4) * (F (k + 3) : ℝ) = c (k + 4)
        refine ⟨i2, i3, ?_⟩
        have hR : (F (k + 3) : ℝ) + 7 * F (k + 1) + 6 * F k = 6 * F (k + 2) := by
          exact_mod_cast hrecF k
        rw [hc (k + 1)] at i1
        rw [hc (k + 2)] at i2
        rw [hc (k + 3)] at i3
        rw [hc (k + 4)]
        linear_combination 51 * 2 ^ (k + 4) * hR + 12 * i3 - 28 * i2 - 48 * i1 +
          (-((51 - 15 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ (k + 1) * (-3 - Real.sqrt 17) +
            3 * (17 + 5 * Real.sqrt 17) * (3 + Real.sqrt 17) ^ (k + 1) * (Real.sqrt 17 - 3))) * hsq
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hE := (trip m).1
    rw [hc (m + 1)] at hE
    have hinv : (2 : ℝ) ^ (m + 1) * ((2 : ℝ) ^ (m + 1))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    rw [hAa m, zpow_neg, zpow_natCast]
    linear_combination ((2 : ℝ) ^ (m + 1))⁻¹ / 51 * hE - (F m : ℝ) * hinv
