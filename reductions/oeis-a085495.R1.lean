import OMAStatements.S_oeis_a085495

-- Reduction oeis-a085495.R1 of A085495: Maximal order of a finite subgroup of the group GL(n,Q).
-- Credit: @notswizz
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- Proved here unconditionally: every odd n (2 * maxSL n = maxGL n). A finite H in SL(n,Q) gives
-- the subgroup H x {I, -I} of GL(n,Q) of order 2|H| (det(-I) = -1 for odd n), and a finite G in
-- GL(n,Q) meets SL(n,Q) in a subgroup of index at most 2 (its determinants are roots of unity in
-- Q, so +1 or -1). No Minkowski bound is needed: if the orders are unbounded both sSup are 0.
-- What remains is even n. H1: the small even n (2, 4, 6, 8, 10), where the maximal finite
-- subgroups are exceptional (Nebe-Plesken tables). H2: even n >= 12, the generic range where
-- Feit's theorem (resting on Weisfeiler and the classification of finite simple groups) says the
-- maximal order 2^n n! is attained only by the signed permutation matrices.
-- Thanks to @MartinFoxy, whose note suggested this odd/even split.

open Matrix OMA.S_oeis_a085495

namespace OMA.R_oeis_a085495_R1

def H1 : Prop := ∀ n : ℕ, Even n → 2 ≤ n → n ≤ 10 → 2 * maxSL n = maxGL n

def H2 : Prop := ∀ n : ℕ, Even n → 12 ≤ n → 2 * maxSL n = maxGL n

variable {n : ℕ}


theorem sc_comm (g : GL (Fin n) ℚ) (u : ℤˣ) :
    Commute g (Units.map (Int.castRingHom (Matrix (Fin n) (Fin n) ℚ)).toMonoidHom u) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp

theorem det_sc_neg (hn : Odd n) : GeneralLinearGroup.det
    (Units.map (Int.castRingHom (Matrix (Fin n) (Fin n) ℚ)).toMonoidHom (-1)) = -1 := by
  ext
  simp [Matrix.det_neg, hn.neg_one_pow]

theorem double (hn : Odd n) (H : Subgroup (SpecialLinearGroup (Fin n) ℚ)) [Finite H] :
    ∃ K : Subgroup (GL (Fin n) ℚ), Finite K ∧ Nat.card K = 2 * Nat.card H := by
  set f : H × ℤˣ →* GL (Fin n) ℚ :=
    (SpecialLinearGroup.toGL.comp H.subtype).noncommCoprod
      (Units.map (Int.castRingHom (Matrix (Fin n) (Fin n) ℚ)).toMonoidHom)
      (fun _ _ => sc_comm _ _) with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨h, u⟩ hh
    simp only [hf, MonoidHom.noncommCoprod_apply, MonoidHom.comp_apply] at hh
    have hd := congrArg GeneralLinearGroup.det hh
    rw [map_mul, map_one] at hd
    have h1 : GeneralLinearGroup.det (SpecialLinearGroup.toGL (H.subtype h)) = 1 := by
      ext; simp
    rw [h1, one_mul] at hd
    rcases Int.units_eq_one_or u with rfl | rfl
    · rw [map_one, mul_one] at hh
      have : H.subtype h = 1 := SpecialLinearGroup.toGL_injective (by simpa using hh)
      ext1
      · exact Subtype.ext (by simpa using this)
      · rfl
    · rw [det_sc_neg hn] at hd
      exact absurd hd (by decide)
  refine ⟨f.range, ?_, ?_⟩
  · exact Set.finite_range _ |>.to_subtype
  · have : Nat.card f.range = Nat.card (H × ℤˣ) := Nat.card_range_of_injective hinj
    rw [this, Nat.card_prod, mul_comm]
    congr
    simp [Nat.card_eq_fintype_card]

theorem units_rat_torsion (x : ℚˣ) (m : ℕ) (hm : m ≠ 0) (hx : x ^ m = 1) : x = 1 ∨ x = -1 := by
  have h1 : ((x : ℚ)) ^ m = 1 := by
    have := congrArg Units.val hx; simpa using this
  have h2 : |(x : ℚ)| ^ m = 1 := by rw [← abs_pow, h1, abs_one]
  have h3 : |(x : ℚ)| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg _) hm).mp h2
  rcases abs_eq (zero_le_one) |>.mp h3 with h | h
  · left; ext; simpa using h
  · right; ext; simpa using h

theorem halve (H : Subgroup (GL (Fin n) ℚ)) [Finite H] :
    ∃ K : Subgroup (SpecialLinearGroup (Fin n) ℚ), Finite K ∧ Nat.card H ≤ 2 * Nat.card K := by
  set d : H →* ℚˣ := GeneralLinearGroup.det.comp H.subtype with hd
  have hr : Nat.card d.range ≤ 2 := by
    have hsub : (d.range : Set ℚˣ) ⊆ {1, -1} := by
      rintro _ ⟨h, rfl⟩
      have hm : Nat.card H ≠ 0 := Nat.card_pos.ne'
      have : (d h) ^ Nat.card H = 1 := by
        rw [← map_pow, pow_card_eq_one', map_one]
      rcases units_rat_torsion _ _ hm this with h1 | h1 <;> simp [h1]
    calc Nat.card d.range = (d.range : Set ℚˣ).ncard := (Nat.card_coe_set_eq _)
      _ ≤ ({1, -1} : Set ℚˣ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
        rw [Set.ncard_pair (by decide)]
  have e : d.ker ≃ H.comap SpecialLinearGroup.toGL :=
    { toFun := fun h => ⟨⟨h.1.1.1, by
          have := h.2
          rw [MonoidHom.mem_ker] at this
          have := congrArg Units.val this
          simpa [hd] using this⟩, by
          show SpecialLinearGroup.toGL _ ∈ H
          convert h.1.2 using 1
          exact Units.ext rfl⟩
      invFun := fun s => ⟨⟨SpecialLinearGroup.toGL s.1, s.2⟩, by
          rw [MonoidHom.mem_ker]; ext; simp [hd]⟩
      left_inv := fun h => Subtype.ext (Subtype.ext (Units.ext rfl))
      right_inv := fun s => Subtype.ext (Subtype.ext rfl) }
  refine ⟨H.comap SpecialLinearGroup.toGL, ?_, ?_⟩
  · exact Finite.of_equiv _ e
  · rw [← Nat.card_congr e, Subgroup.card_eq_card_quotient_mul_card_subgroup d.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange d).toEquiv]
    exact Nat.mul_le_mul_right _ hr

theorem odd_case (hn : Odd n) : 2 * maxSL n = maxGL n := by
  set A := {k | ∃ H : Subgroup (GL (Fin n) ℚ), Finite H ∧ Nat.card H = k} with hAdef
  set B := {k | ∃ H : Subgroup (SpecialLinearGroup (Fin n) ℚ), Finite H ∧ Nat.card H = k}
    with hBdef
  have hBA : ∀ k ∈ B, 2 * k ∈ A := by
    rintro _ ⟨H, hH, rfl⟩
    exact double hn H
  have hAB : ∀ k ∈ A, ∃ j ∈ B, k ≤ 2 * j := by
    rintro _ ⟨H, hH, rfl⟩
    obtain ⟨K, hK, hle⟩ := halve H
    exact ⟨_, ⟨K, hK, rfl⟩, hle⟩
  have hA1 : A.Nonempty := ⟨1, ⊥, inferInstance, Subgroup.card_bot⟩
  have hB1 : B.Nonempty := ⟨1, ⊥, inferInstance, Subgroup.card_bot⟩
  show 2 * sSup B = sSup A
  by_cases hBb : BddAbove B
  · obtain ⟨b, hb⟩ := hBb
    have hAb : BddAbove A := by
      refine ⟨2 * b, fun k hk => ?_⟩
      obtain ⟨j, hj, hkj⟩ := hAB k hk
      exact hkj.trans (Nat.mul_le_mul_left 2 (hb hj))
    have hBb' : BddAbove B := ⟨b, hb⟩
    apply le_antisymm
    · exact le_csSup hAb (hBA _ (Nat.sSup_mem hB1 hBb'))
    · obtain ⟨j, hj, hkj⟩ := hAB _ (Nat.sSup_mem hA1 hAb)
      exact hkj.trans (Nat.mul_le_mul_left 2 (le_csSup hBb' hj))
  · have hAb : ¬ BddAbove A := by
      rintro ⟨a, ha⟩
      exact hBb ⟨a, fun k hk => (show k ≤ 2 * k by omega).trans (ha (hBA k hk))⟩
    rw [csSup_of_not_bddAbove hBb, csSup_of_not_bddAbove hAb, csSup_empty]
    simp

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a085495.main := by
  intro h1 h2 n hn
  rcases Nat.even_or_odd n with he | ho
  · by_cases h : n ≤ 10
    · have : 2 ≤ n := by
        obtain ⟨k, hk⟩ := he
        omega
      exact h1 n he this h
    · exact h2 n he (by obtain ⟨k, hk⟩ := he; omega)
  · exact odd_case ho

end OMA.R_oeis_a085495_R1
