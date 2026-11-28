import OMAStatements.S_oeis_a267229

-- Problem: A267229: Number of length-n 0..5 arrays with no following elements greater than or equal to the first repeated value.
-- Upstream: formal-conjectures statements/oeis-a267229.lean:0 (declaration OMA.S_oeis_a267229.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (as for A267465): split an array of length m+1 into its first entry v and the rest
-- (Fin.consEquiv). Let V(m, v) count the admissible arrays of length m+1 that start with v, and
-- B(m, v) the arrays of length m with all entries less than v, so B(m, v) = v^m. Looking at the
-- second entry u: if u = v, the first repeated value is v and the rest must be less than v;
-- otherwise the array is admissible iff its tail is. So V(m+1, v) = B(m, v) + Sum_{u != v} V(m, u),
-- and summing over v, a(m+2) = 5a(m+1) + 0^m + 1 + 2^m + ... + 5^m with a(1) = 6. This gives the closed form
-- by induction (for n >= 2), the closed form is annihilated by (1 - x)(1 - 2x)(1 - 3x)(1 - 4x)(1 - 5x)^2 (a ring
-- identity, with 6^n = 2^n 3^n where needed), and the g.f. follows by comparing coefficients.

namespace P1A267229

open OMA.S_oeis_a267229

theorem ok_cc (x y : ℕ) (t : List ℕ) :
    ok (x :: y :: t) = if x = y then t.all (fun c => decide (c < x)) else ok (y :: t) := by
  rw [ok.eq_1]

theorem ok_one (x : ℕ) : ok [x] = true := by
  simp [ok]

theorem hL (m : ℕ) (x : Fin (m + 1) → Fin 6) :
    List.ofFn (fun i => ((x i : Fin 6) : ℕ)) =
      ((x 0 : Fin 6) : ℕ) :: List.ofFn (fun i => ((Fin.tail x i : Fin 6) : ℕ)) :=
  List.ofFn_succ

theorem consSplit (m : ℕ) (P : List ℕ → Bool) :
    (∑ x : Fin (m + 1) → Fin 6,
        if P (List.ofFn (fun i => ((x i : Fin 6) : ℕ))) = true then (1 : ℕ) else 0) =
      ∑ v : Fin 6, ∑ t : Fin m → Fin 6,
        if P ((v : ℕ) :: List.ofFn (fun i => ((t i : Fin 6) : ℕ))) = true then (1 : ℕ) else 0 := by
  have h1 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 6)).symm
    (fun x : Fin (m + 1) → Fin 6 =>
      if P (List.ofFn (fun i => ((x i : Fin 6) : ℕ))) = true then (1 : ℕ) else 0)
    (fun p : Fin 6 × (Fin m → Fin 6) =>
      if P ((p.1 : ℕ) :: List.ofFn (fun i => ((p.2 i : Fin 6) : ℕ))) = true then (1 : ℕ) else 0)
    (fun x => congrArg (fun l => if P l = true then (1 : ℕ) else 0) (hL m x))
  exact h1.trans (Fintype.sum_prod_type _)

theorem hB (v : ℕ) (m : ℕ) : (∑ s : Fin m → Fin 6,
    if (List.ofFn (fun i => ((s i : Fin 6) : ℕ))).all (fun c => decide (c < v)) = true
      then (1 : ℕ) else 0) =
    (∑ u : Fin 6, if (u : ℕ) < v then (1 : ℕ) else 0) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, Fintype.sum_unique, List.ofFn_zero, List.all_nil,
      if_pos (show true = true from rfl)]
  | succ m ih =>
    rw [consSplit m (fun l => l.all (fun c => decide (c < v)))]
    have hpt : ∀ (u : Fin 6) (t : Fin m → Fin 6),
        (if (((u : ℕ) :: List.ofFn (fun i => ((t i : Fin 6) : ℕ))).all
          (fun c => decide (c < v))) = true then (1 : ℕ) else 0) =
        (if (u : ℕ) < v then (1 : ℕ) else 0) *
          (if (List.ofFn (fun i => ((t i : Fin 6) : ℕ))).all (fun c => decide (c < v)) = true
            then (1 : ℕ) else 0) := by
      intro u t
      rw [ite_zero_mul_ite_zero, one_mul]
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    simp only [hpt, ← Finset.mul_sum]
    rw [ih, ← Finset.sum_mul]
    ring

end P1A267229

open OMA.S_oeis_a267229 P1A267229 in
theorem OMA.solution : type_of% @OMA.S_oeis_a267229.main := by
  obtain ⟨B, hBd⟩ : ∃ B : ℕ → Fin 6 → ℕ, ∀ m v, B m v = ∑ s : Fin m → Fin 6,
      (if (List.ofFn (fun i => ((s i : Fin 6) : ℕ))).all (fun c => decide (c < (v : ℕ))) = true
        then (1 : ℕ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℕ → Fin 6 → ℕ, ∀ m v, V m v = ∑ t : Fin m → Fin 6,
      (if ok ((v : ℕ) :: List.ofFn (fun i => ((t i : Fin 6) : ℕ))) = true then (1 : ℕ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  have hV0 : ∀ v, V 0 v = 1 := by
    intro v
    rw [hVd, Fintype.sum_unique, List.ofFn_zero, if_pos (ok_one (v : ℕ))]
  have hV1 : ∀ m v, V (m + 1) v = ∑ u : Fin 6, (if v = u then B m v else V m u) := by
    intro m v
    rw [hVd, consSplit m (fun l => ok ((v : ℕ) :: l))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    by_cases h : v = u
    · rw [if_pos h, hBd]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [ok_cc, if_pos (show (v : ℕ) = (u : ℕ) from congrArg Fin.val h)]
    · rw [if_neg h, hVd]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [ok_cc, if_neg (show ¬ ((v : ℕ) = (u : ℕ)) from fun h' => h (Fin.ext h'))]
  have hV2 : ∀ m v, V (m + 1) v + V m v = B m v + ∑ u : Fin 6, V m u := by
    intro m v
    have hpt : ∀ u ∈ (Finset.univ : Finset (Fin 6)),
        (if v = u then B m v else V m u) + (if v = u then V m u else 0) =
          (if v = u then B m v else 0) + V m u := by
      intro u _
      by_cases h : v = u
      · rw [if_pos h, if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, if_neg h, zero_add, add_zero]
    have hs := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq,
      if_pos (Finset.mem_univ v), if_pos (Finset.mem_univ v), ← hV1 m v] at hs
    exact hs
  have hA : ∀ m, ∑ v : Fin 6, V (m + 1) v = 5 * ∑ v : Fin 6, V m v + ∑ v : Fin 6, B m v := by
    intro m
    have hpt : ∀ v ∈ (Finset.univ : Finset (Fin 6)),
        V (m + 1) v + V m v = B m v + ∑ u : Fin 6, V m u := fun v _ => hV2 m v
    have hs := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hs
    omega
  have hBs : ∀ m, ∑ v : Fin 6, B m v = 0 ^ m + 1 + 2 ^ m + 3 ^ m + 4 ^ m + 5 ^ m := by
    intro m
    have c0 : (∑ u : Fin 6, if (u : ℕ) < ((0 : Fin 6) : ℕ) then (1 : ℕ) else 0) = 0 := by
      rw [Fin.sum_univ_six]
      decide
    have c1 : (∑ u : Fin 6, if (u : ℕ) < ((1 : Fin 6) : ℕ) then (1 : ℕ) else 0) = 1 := by
      rw [Fin.sum_univ_six]
      decide
    have c2 : (∑ u : Fin 6, if (u : ℕ) < ((2 : Fin 6) : ℕ) then (1 : ℕ) else 0) = 2 := by
      rw [Fin.sum_univ_six]
      decide
    have c3 : (∑ u : Fin 6, if (u : ℕ) < ((3 : Fin 6) : ℕ) then (1 : ℕ) else 0) = 3 := by
      rw [Fin.sum_univ_six]
      decide
    have c4 : (∑ u : Fin 6, if (u : ℕ) < ((4 : Fin 6) : ℕ) then (1 : ℕ) else 0) = 4 := by
      rw [Fin.sum_univ_six]
      decide
    have c5 : (∑ u : Fin 6, if (u : ℕ) < ((5 : Fin 6) : ℕ) then (1 : ℕ) else 0) = 5 := by
      rw [Fin.sum_univ_six]
      decide
    rw [Fin.sum_univ_six, hBd, hBd, hBd, hBd, hBd, hBd, hB ((0 : Fin 6) : ℕ) m, hB ((1 : Fin 6) : ℕ) m, hB ((2 : Fin 6) : ℕ) m, hB ((3 : Fin 6) : ℕ) m, hB ((4 : Fin 6) : ℕ) m, hB ((5 : Fin 6) : ℕ) m, c0, c1, c2, c3, c4, c5, one_pow]
  have hAa : ∀ m, a (m + 1) = ∑ v : Fin 6, V m v := by
    intro m
    unfold a
    rw [Finset.card_filter, consSplit m ok]
    exact Finset.sum_congr rfl (fun v _ => (hVd m v).symm)
  have a1 : a (0 + 1) = 6 := by
    have h := hAa 0
    rw [Fin.sum_univ_six, hV0, hV0, hV0, hV0, hV0, hV0] at h
    exact h
  have hrec : ∀ m, a (m + 1 + 1) = 5 * a (m + 1) + (0 ^ m + 1 + 2 ^ m + 3 ^ m + 4 ^ m + 5 ^ m) := by
    intro m
    rw [hAa (m + 1), hA m, hBs m, hAa m]
  have hq : ∀ m : ℕ, (a (m + 1 + 1) : ℚ) = (-5 * (15 + 5 * 2 ^ (m + 3) + 10 * 3 ^ (m + 2) + 15 * 4 ^ (m + 2) - 97 * 5 ^ (m + 2)) + 12 * 5 ^ (m + 2) * ((m : ℚ) + 2)) / 300 := by
    intro m
    induction m with
    | zero =>
      have hc : (a (0 + 1 + 1) : ℚ) = 5 * (a (0 + 1) : ℚ) + ((0 : ℚ) ^ 0 + 1 + 2 ^ 0 + 3 ^ 0 + 4 ^ 0 + 5 ^ 0) := by
        exact_mod_cast hrec 0
      rw [hc, a1]
      norm_num
    | succ k ih =>
      have hc : (a (k + 1 + 1 + 1) : ℚ) = 5 * (a (k + 1 + 1) : ℚ) + ((0 : ℚ) ^ (k + 1) + 1 + 2 ^ (k + 1) + 3 ^ (k + 1) + 4 ^ (k + 1) + 5 ^ (k + 1)) := by
        exact_mod_cast hrec (k + 1)
      rw [hc, ih, (zero_pow (by omega : k + 1 ≠ 0) : (0 : ℚ) ^ (k + 1) = 0)]
      push_cast
      ring
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (a (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
    have hmk : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk b := by
      congr 1
      funext n
      exact (hb n).symm
    have hbq : ∀ j, 1 ≤ j → b j = (-5 * (15 + 5 * 2 ^ (j + 2) + 10 * 3 ^ (j + 1) + 15 * 4 ^ (j + 1) - 97 * 5 ^ (j + 1)) + 12 * 5 ^ (j + 1) * ((j : ℚ) + 1)) / 300 := by
      intro j hj
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      rw [hb, hq i]
      push_cast
      ring
    have b0 : b 0 = 6 := by
      rw [hb]
      exact_mod_cast a1
    have b1 : b 1 = 36 := by
      rw [hbq 1 (by norm_num)]
      norm_num
    have b2 : b 2 = 195 := by
      rw [hbq 2 (by norm_num)]
      norm_num
    have b3 : b 3 = 1030 := by
      rw [hbq 3 (by norm_num)]
      norm_num
    have b4 : b 4 = 5375 := by
      rw [hbq 4 (by norm_num)]
      norm_num
    have b5 : b 5 = 27854 := by
      rw [hbq 5 (by norm_num)]
      norm_num
    have b6 : b 6 = 143695 := by
      rw [hbq 6 (by norm_num)]
      norm_num
    have hr : ∀ m, 7 ≤ m → b m - 20 * b (m - 1) + 160 * b (m - 2) - 650 * b (m - 3) + 1399 * b (m - 4) - 1490 * b (m - 5) + 600 * b (m - 6) = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 7 := ⟨m - 7, by omega⟩
      rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega, hbq (k + 7) (by omega), hbq (k + 6) (by omega), hbq (k + 5) (by omega), hbq (k + 4) (by omega), hbq (k + 3) (by omega), hbq (k + 2) (by omega), hbq (k + 1) (by omega)]
      push_cast
      ring
    have gfb : PowerSeries.mk b * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) ^ 2) = (6 : PowerSeries ℚ) - 84 * PowerSeries.X + 435 * PowerSeries.X ^ 2 - 1010 * PowerSeries.X ^ 3 + 969 * PowerSeries.X ^ 4 - 172 * PowerSeries.X ^ 5 - 120 * PowerSeries.X ^ 6 := by
      have e : PowerSeries.mk b * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) ^ 2) = PowerSeries.mk b - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20 * (PowerSeries.mk b * PowerSeries.X ^ 1) + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 160 * (PowerSeries.mk b * PowerSeries.X ^ 2) - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 650 * (PowerSeries.mk b * PowerSeries.X ^ 3) + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1399 * (PowerSeries.mk b * PowerSeries.X ^ 4) - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1490 * (PowerSeries.mk b * PowerSeries.X ^ 5) + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 600 * (PowerSeries.mk b * PowerSeries.X ^ 6) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 20, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 160, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 650, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1399, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1490, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 600]
        ring
      have e2 : (6 : PowerSeries ℚ) - 84 * PowerSeries.X + 435 * PowerSeries.X ^ 2 - 1010 * PowerSeries.X ^ 3 + 969 * PowerSeries.X ^ 4 - 172 * PowerSeries.X ^ 5 - 120 * PowerSeries.X ^ 6 = (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * PowerSeries.X ^ 0 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84 * PowerSeries.X ^ 1 + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 435 * PowerSeries.X ^ 2 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1010 * PowerSeries.X ^ 3 + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 969 * PowerSeries.X ^ 4 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 172 * PowerSeries.X ^ 5 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 120 * PowerSeries.X ^ 6 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 84, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 435, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 1010, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 969, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 172, map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 120]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_C]
      rcases Nat.lt_or_ge m 7 with hm | hm
      · interval_cases m
        · norm_num [b0]
        · norm_num [b0, b1]
        · norm_num [b0, b1, b2]
        · norm_num [b0, b1, b2, b3]
        · norm_num [b0, b1, b2, b3, b4]
        · norm_num [b0, b1, b2, b3, b4, b5]
        · norm_num [b0, b1, b2, b3, b4, b5, b6]
      · simp (disch := omega) only [if_pos, if_neg]
        linarith [hr m hm]
    rw [hmk]
    calc PowerSeries.X * PowerSeries.mk b * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) ^ 2)
        = PowerSeries.X * (PowerSeries.mk b * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) ^ 2)) := by
          ring
      _ = PowerSeries.X * ((6 : PowerSeries ℚ) - 84 * PowerSeries.X + 435 * PowerSeries.X ^ 2 - 1010 * PowerSeries.X ^ 3 + 969 * PowerSeries.X ^ 4 - 172 * PowerSeries.X ^ 5 - 120 * PowerSeries.X ^ 6) := by
          rw [gfb]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
    rw [hq m]
    push_cast
    ring
