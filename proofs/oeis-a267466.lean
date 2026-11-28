import OMAStatements.S_oeis_a267466

-- Problem: A267466: Number of length-n 0..3 arrays with no following elements larger than the first repeated value.
-- Upstream: formal-conjectures statements/oeis-a267466.lean:0 (declaration OMA.S_oeis_a267466.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea (as for A267465): split an array of length m+1 into its first entry v and the rest
-- (Fin.consEquiv). Let V(m, v) count the admissible arrays of length m+1 that start with v, and
-- B(m, v) the arrays of length m with all entries at most v, so B(m, v) = (v+1)^m. Looking at the
-- second entry u: if u = v, the first repeated value is v and the rest must be at most v;
-- otherwise the array is admissible iff its tail is. So V(m+1, v) = B(m, v) + Sum_{u != v} V(m, u),
-- and summing over v, a(m+2) = 3a(m+1) + 1 + 2^m + 3^m + 4^m with a(1) = 4. This gives the closed
-- form by induction, the closed form is annihilated by (1 - x)(1 - 2x)(1 - 3x)^2(1 - 4x) (a ring
-- identity), and the g.f. follows by comparing coefficients.

namespace P1A267466

open OMA.S_oeis_a267466

theorem ok_cc (x y : ℕ) (t : List ℕ) :
    ok (x :: y :: t) = if x = y then t.all (fun c => decide (c ≤ x)) else ok (y :: t) := by
  rw [ok.eq_1]

theorem ok_one (x : ℕ) : ok [x] = true := by
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

theorem hB (v : ℕ) (m : ℕ) : (∑ s : Fin m → Fin 4,
    if (List.ofFn (fun i => ((s i : Fin 4) : ℕ))).all (fun c => decide (c ≤ v)) = true
      then (1 : ℕ) else 0) =
    (∑ u : Fin 4, if (u : ℕ) ≤ v then (1 : ℕ) else 0) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, Fintype.sum_unique, List.ofFn_zero, List.all_nil,
      if_pos (show true = true from rfl)]
  | succ m ih =>
    rw [consSplit m (fun l => l.all (fun c => decide (c ≤ v)))]
    have hpt : ∀ (u : Fin 4) (t : Fin m → Fin 4),
        (if (((u : ℕ) :: List.ofFn (fun i => ((t i : Fin 4) : ℕ))).all
          (fun c => decide (c ≤ v))) = true then (1 : ℕ) else 0) =
        (if (u : ℕ) ≤ v then (1 : ℕ) else 0) *
          (if (List.ofFn (fun i => ((t i : Fin 4) : ℕ))).all (fun c => decide (c ≤ v)) = true
            then (1 : ℕ) else 0) := by
      intro u t
      rw [ite_zero_mul_ite_zero, one_mul]
      simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    simp only [hpt, ← Finset.mul_sum]
    rw [ih, ← Finset.sum_mul]
    ring

end P1A267466

open OMA.S_oeis_a267466 P1A267466 in
theorem OMA.solution : type_of% @OMA.S_oeis_a267466.main := by
  obtain ⟨B, hBd⟩ : ∃ B : ℕ → Fin 4 → ℕ, ∀ m v, B m v = ∑ s : Fin m → Fin 4,
      (if (List.ofFn (fun i => ((s i : Fin 4) : ℕ))).all (fun c => decide (c ≤ (v : ℕ))) = true
        then (1 : ℕ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨V, hVd⟩ : ∃ V : ℕ → Fin 4 → ℕ, ∀ m v, V m v = ∑ t : Fin m → Fin 4,
      (if ok ((v : ℕ) :: List.ofFn (fun i => ((t i : Fin 4) : ℕ))) = true then (1 : ℕ) else 0) :=
    ⟨_, fun _ _ => rfl⟩
  have hV0 : ∀ v, V 0 v = 1 := by
    intro v
    rw [hVd, Fintype.sum_unique, List.ofFn_zero, if_pos (ok_one (v : ℕ))]
  have hV1 : ∀ m v, V (m + 1) v = ∑ u : Fin 4, (if v = u then B m v else V m u) := by
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
  have hV2 : ∀ m v, V (m + 1) v + V m v = B m v + ∑ u : Fin 4, V m u := by
    intro m v
    have hpt : ∀ u ∈ (Finset.univ : Finset (Fin 4)),
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
  have hA : ∀ m, ∑ v : Fin 4, V (m + 1) v = 3 * ∑ v : Fin 4, V m v + ∑ v : Fin 4, B m v := by
    intro m
    have hpt : ∀ v ∈ (Finset.univ : Finset (Fin 4)),
        V (m + 1) v + V m v = B m v + ∑ u : Fin 4, V m u := fun v _ => hV2 m v
    have hs := Finset.sum_congr rfl hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul] at hs
    omega
  have hBs : ∀ m, ∑ v : Fin 4, B m v = 1 + 2 ^ m + 3 ^ m + 4 ^ m := by
    intro m
    have c0 : (∑ u : Fin 4, if (u : ℕ) ≤ ((0 : Fin 4) : ℕ) then (1 : ℕ) else 0) = 1 := by
      rw [Fin.sum_univ_four]
      decide
    have c1 : (∑ u : Fin 4, if (u : ℕ) ≤ ((1 : Fin 4) : ℕ) then (1 : ℕ) else 0) = 2 := by
      rw [Fin.sum_univ_four]
      decide
    have c2 : (∑ u : Fin 4, if (u : ℕ) ≤ ((2 : Fin 4) : ℕ) then (1 : ℕ) else 0) = 3 := by
      rw [Fin.sum_univ_four]
      decide
    have c3 : (∑ u : Fin 4, if (u : ℕ) ≤ ((3 : Fin 4) : ℕ) then (1 : ℕ) else 0) = 4 := by
      rw [Fin.sum_univ_four]
      decide
    rw [Fin.sum_univ_four, hBd, hBd, hBd, hBd, hB ((0 : Fin 4) : ℕ) m, hB ((1 : Fin 4) : ℕ) m,
      hB ((2 : Fin 4) : ℕ) m, hB ((3 : Fin 4) : ℕ) m, c0, c1, c2, c3, one_pow]
  have hAa : ∀ m, a (m + 1) = ∑ v : Fin 4, V m v := by
    intro m
    unfold a
    rw [Finset.card_filter, consSplit m ok]
    exact Finset.sum_congr rfl (fun v _ => (hVd m v).symm)
  have a1 : a 1 = 4 := by
    have h := hAa 0
    rw [Fin.sum_univ_four, hV0, hV0, hV0, hV0] at h
    exact h
  have hrec : ∀ m, a (m + 1 + 1) = 3 * a (m + 1) + (1 + 2 ^ m + 3 ^ m + 4 ^ m) := by
    intro m
    rw [hAa (m + 1), hA m, hBs m, hAa m]
  have hq : ∀ m : ℕ, (a (m + 1) : ℚ) = (-18 - 9 * 2 ^ (m + 2) + 50 * 3 ^ (m + 1) +
      9 * 4 ^ (m + 1) + 4 * 3 ^ (m + 1) * ((m : ℚ) + 1)) / 36 := by
    intro m
    induction m with
    | zero => norm_num [a1]
    | succ k ih =>
      have hc : (a (k + 1 + 1) : ℚ) = 3 * (a (k + 1) : ℚ) + (1 + 2 ^ k + 3 ^ k + 4 ^ k) := by
        exact_mod_cast hrec k
      rw [hc, ih]
      push_cast
      ring
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (a (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
    have hmk : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk b := by
      congr 1
      funext n
      exact (hb n).symm
    have hbq : ∀ m, b m = (-18 - 9 * 2 ^ (m + 2) + 50 * 3 ^ (m + 1) +
        9 * 4 ^ (m + 1) + 4 * 3 ^ (m + 1) * ((m : ℚ) + 1)) / 36 :=
      fun m => (hb m).trans (hq m)
    have hr5 : ∀ m, 5 ≤ m →
        b m - 13 * b (m - 1) + 65 * b (m - 2) - 155 * b (m - 3) + 174 * b (m - 4) -
          72 * b (m - 5) = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
      rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
        show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
        show k + 5 - 5 = k by omega,
        hbq (k + 5), hbq (k + 4), hbq (k + 3), hbq (k + 2), hbq (k + 1), hbq k]
      push_cast
      ring
    have gfb : PowerSeries.mk b *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) ^ 2 *
          (1 - 4 * PowerSeries.X)) =
        2 * (2 - 18 * PowerSeries.X + 55 * PowerSeries.X ^ 2 - 65 * PowerSeries.X ^ 3 +
          23 * PowerSeries.X ^ 4) := by
      have e : PowerSeries.mk b *
          ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) ^ 2 *
            (1 - 4 * PowerSeries.X)) =
          PowerSeries.mk b
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 13 * (PowerSeries.mk b * PowerSeries.X ^ 1)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 65 * (PowerSeries.mk b * PowerSeries.X ^ 2)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 155 * (PowerSeries.mk b * PowerSeries.X ^ 3)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 174 * (PowerSeries.mk b * PowerSeries.X ^ 4)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72 *
              (PowerSeries.mk b * PowerSeries.X ^ 5) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 13,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 65,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 155,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 174,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 72]
        ring
      have e2 : (2 * (2 - 18 * PowerSeries.X + 55 * PowerSeries.X ^ 2 - 65 * PowerSeries.X ^ 3 +
          23 * PowerSeries.X ^ 4) : PowerSeries ℚ) =
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * PowerSeries.X ^ 0
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36 * PowerSeries.X ^ 1
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 110 * PowerSeries.X ^ 2
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 130 * PowerSeries.X ^ 3
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 46 * PowerSeries.X ^ 4 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 36,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 110,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 130,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 46]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_C]
      rcases Nat.lt_or_ge m 5 with hm | hm
      · interval_cases m
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
        · norm_num [hbq]
      · simp (disch := omega) only [if_pos, if_neg]
        linarith [hr5 m hm]
    rw [hmk]
    calc PowerSeries.X * PowerSeries.mk b *
          ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) ^ 2 *
            (1 - 4 * PowerSeries.X))
        = PowerSeries.X * (PowerSeries.mk b *
          ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) ^ 2 *
            (1 - 4 * PowerSeries.X))) := by
          ring
      _ = PowerSeries.X * (2 * (2 - 18 * PowerSeries.X + 55 * PowerSeries.X ^ 2 -
          65 * PowerSeries.X ^ 3 + 23 * PowerSeries.X ^ 4)) := by
          rw [gfb]
      _ = 2 * PowerSeries.X * (2 - 18 * PowerSeries.X + 55 * PowerSeries.X ^ 2 -
          65 * PowerSeries.X ^ 3 + 23 * PowerSeries.X ^ 4) := by
          ring
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hq m]
    push_cast
    ring
