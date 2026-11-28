import OMAStatements.S_oeis_a101912
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace OMA.P_oeis_a101912

open OMA.S_oeis_a101912

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

private lemma coeff_sq_zmod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) =
      if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul]
  let S := Finset.antidiagonal n
  let S_lt := S.filter (fun p : ℕ × ℕ => p.1 < p.2)
  let S_gt := S.filter (fun p : ℕ × ℕ => p.2 < p.1)
  let S_eq := S.filter (fun p : ℕ × ℕ => p.1 = p.2)
  have hpart : S = S_lt ∪ S_gt ∪ S_eq := by
    ext p
    simp only [Finset.mem_union, S_lt, S_gt, S_eq, Finset.mem_filter]
    constructor
    · intro hp
      rcases lt_trichotomy p.1 p.2 with h | h | h
      · exact Or.inl (Or.inl ⟨hp, h⟩)
      · exact Or.inr ⟨hp, h⟩
      · exact Or.inl (Or.inr ⟨hp, h⟩)
    · rintro ((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp
  have hd1 : Disjoint S_lt S_gt := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [S_lt, S_gt, Finset.mem_filter] at h1 h2; omega
  have hd2 : Disjoint (S_lt ∪ S_gt) S_eq := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_union, S_lt, S_gt, S_eq, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> omega
  rw [show Finset.antidiagonal n = S from rfl, hpart, Finset.sum_union hd2, Finset.sum_union hd1]
  have hswap : ∑ p ∈ S_lt, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f =
      ∑ p ∈ S_gt, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [S_lt, S_gt, S, Finset.mem_filter, Finset.mem_antidiagonal] at hp ⊢
      exact ⟨by omega, hp.2⟩
    · intro p₁ _ p₂ _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro q hq
      simp only [S_lt, S_gt, S, Finset.mem_filter, Finset.mem_antidiagonal] at hq ⊢
      exact ⟨(q.2, q.1), ⟨by omega, hq.2⟩, rfl⟩
    · intro p _; exact mul_comm _ _
  rw [← hswap, zmod2_add_self, zero_add]
  split_ifs with hev
  · have hSeq : S_eq = {(n / 2, n / 2)} := by
      ext ⟨a, b⟩
      simp only [S_eq, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_singleton,
        Prod.mk.injEq]
      omega
    rw [hSeq, Finset.sum_singleton, zmod2_mul_self]
  · have hSeq : S_eq = ∅ := by
      ext ⟨a, b⟩
      simp only [S_eq, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.notMem_empty,
        iff_false, not_and]
      omega
    rw [hSeq, Finset.sum_empty]

private lemma ps_zmod2_mul_eq_zero {f g : PowerSeries (ZMod 2)}
    (hf : f ≠ 0) (hfg : f * g = 0) : g = 0 := by
  by_contra hg
  have hex_f : ∃ m : ℕ, PowerSeries.coeff m f ≠ 0 := by
    by_contra h
    apply hf; ext m; by_contra hm; exact h ⟨m, hm⟩
  have hex_g : ∃ n : ℕ, PowerSeries.coeff n g ≠ 0 := by
    by_contra h
    apply hg; ext n; by_contra hn; exact h ⟨n, hn⟩
  classical
  let m := Nat.find hex_f
  let n := Nat.find hex_g
  have hm : PowerSeries.coeff m f ≠ 0 := Nat.find_spec hex_f
  have hn : PowerSeries.coeff n g ≠ 0 := Nat.find_spec hex_g
  have hmlt : ∀ k < m, PowerSeries.coeff k f = 0 := by
    intro k hk; by_contra h; exact Nat.find_min hex_f hk h
  have hnlt : ∀ k < n, PowerSeries.coeff k g = 0 := by
    intro k hk; by_contra h; exact Nat.find_min hex_g hk h
  have hc := congrArg (PowerSeries.coeff (m + n)) hfg
  rw [PowerSeries.coeff_mul, map_zero, Finset.sum_eq_single (m, n)] at hc
  · exact mul_ne_zero hm hn hc
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    by_cases ha : a < m
    · rw [hmlt a ha, zero_mul]
    · have hb : b < n := by
        by_contra hbn
        exact hne (Prod.ext (by omega) (by omega))
      rw [hnlt b hb, mul_zero]
  · intro hnot; exact False.elim (hnot (Finset.mem_antidiagonal.mpr rfl))

private lemma A2_eq (A₂ : PowerSeries (ZMod 2))
    (hA₂ : A₂ = PowerSeries.mk (fun n => (a101912 n : ZMod 2))) :
    A₂ + PowerSeries.X * A₂ ^ 3 = 1 := by
  ext n
  cases n with
  | zero =>
    simp [hA₂, a101912]
  | succ m =>
    rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero m)]
    rw [show A₂ ^ 3 = A₂ ^ 2 * A₂ by ring, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (A₂ ^ 2) * PowerSeries.coeff j A₂)]
    have hsum_even : ∑ i ∈ Finset.range (m + 1),
        PowerSeries.coeff i (A₂ ^ 2) * PowerSeries.coeff (m - i) A₂ =
        ∑ k : Fin (m / 2 + 1), (a101912 k.val : ZMod 2) * (a101912 (m - 2 * k.val) : ZMod 2) := by
      have hrew : ∀ i ∈ Finset.range (m + 1),
          PowerSeries.coeff i (A₂ ^ 2) * PowerSeries.coeff (m - i) A₂ =
          if i % 2 = 0 then (a101912 (i / 2) : ZMod 2) * (a101912 (m - i) : ZMod 2) else 0 := by
        intro i _
        rw [coeff_sq_zmod2]
        split_ifs
        · simp [hA₂]
        · simp
      rw [Finset.sum_congr rfl hrew, ← Finset.sum_filter]
      symm
      refine Finset.sum_bij (fun (k : Fin (m / 2 + 1)) _ => 2 * k.val) ?_ ?_ ?_ ?_
      · intro k _
        simp only [Finset.mem_filter, Finset.mem_range]
        have := k.isLt; omega
      · intro k₁ _ k₂ _ h
        ext; omega
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        exact ⟨⟨i / 2, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
      · intro k _
        simp only [show 2 * k.val / 2 = k.val by omega]
    rw [hsum_even, hA₂, PowerSeries.coeff_mk]
    have hrec : (a101912 (m + 1) : ℤ) +
        ∑ k : Fin (m / 2 + 1), a101912 k.val * a101912 (m - 2 * k.val) = 0 := by
      rw [a101912]; ring
    have hcast := congrArg (Int.cast (R := ZMod 2)) hrec
    simpa [Int.cast_sum, Int.cast_mul] using hcast

private lemma exists_int_poly_mul {A : ℕ → ℤ} {P Q : Polynomial ℚ} (hP : P ≠ 0)
    (hEq : (P : PowerSeries ℚ) * PowerSeries.mk (fun n => (A n : ℚ)) = (Q : PowerSeries ℚ)) :
    ∃ Pz Qz : Polynomial ℤ, Pz ≠ 0 ∧
      (Pz : PowerSeries ℤ) * PowerSeries.mk A = (Qz : PowerSeries ℤ) := by
  let S := P.support ∪ Q.support
  let D : ℕ := ∏ i ∈ S, (P.coeff i).den * (Q.coeff i).den
  have hDpos : 0 < D := Finset.prod_pos fun i _ => Nat.mul_pos (P.coeff i).pos (Q.coeff i).pos
  have hDne : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hD_int_P : ∀ i : ℕ, ∃ z : ℤ, (D : ℚ) * P.coeff i = (z : ℚ) := by
    intro i
    by_cases hi : i ∈ P.support
    · have hiS : i ∈ S := Finset.mem_union_left _ hi
      have hdvd : (P.coeff i).den ∣ D :=
        dvd_trans (dvd_mul_right _ _) (Finset.dvd_prod_of_mem _ hiS)
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : ℤ) * (P.coeff i).num, ?_⟩
      have hq : P.coeff i = ((P.coeff i).num : ℚ) / ((P.coeff i).den : ℚ) :=
        (Rat.num_div_den (P.coeff i)).symm
      have hden_ne : ((P.coeff i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (P.coeff i).den_nz
      calc (D : ℚ) * P.coeff i
          = (((P.coeff i).den * c : ℕ) : ℚ) * (((P.coeff i).num : ℚ) / ((P.coeff i).den : ℚ)) := by
            rw [hc, ← hq]
        _ = ((c : ℤ) * (P.coeff i).num : ℤ) := by
            push_cast; field_simp
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]
      exact ⟨0, by simp⟩
  have hD_int_Q : ∀ i : ℕ, ∃ z : ℤ, (D : ℚ) * Q.coeff i = (z : ℚ) := by
    intro i
    by_cases hi : i ∈ Q.support
    · have hiS : i ∈ S := Finset.mem_union_right _ hi
      have hdvd : (Q.coeff i).den ∣ D :=
        dvd_trans (dvd_mul_left _ _) (Finset.dvd_prod_of_mem _ hiS)
      obtain ⟨c, hc⟩ := hdvd
      refine ⟨(c : ℤ) * (Q.coeff i).num, ?_⟩
      have hq : Q.coeff i = ((Q.coeff i).num : ℚ) / ((Q.coeff i).den : ℚ) :=
        (Rat.num_div_den (Q.coeff i)).symm
      have hden_ne : ((Q.coeff i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Q.coeff i).den_nz
      calc (D : ℚ) * Q.coeff i
          = (((Q.coeff i).den * c : ℕ) : ℚ) * (((Q.coeff i).num : ℚ) / ((Q.coeff i).den : ℚ)) := by
            rw [hc, ← hq]
        _ = ((c : ℤ) * (Q.coeff i).num : ℤ) := by
            push_cast; field_simp
    · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]
      exact ⟨0, by simp⟩
  let Pz : Polynomial ℤ := ∑ i ∈ P.support, Polynomial.monomial i (Classical.choose (hD_int_P i))
  let Qz : Polynomial ℤ := ∑ i ∈ Q.support, Polynomial.monomial i (Classical.choose (hD_int_Q i))
  have hPz_coeff : ∀ i : ℕ, (Pz.coeff i : ℚ) = (D : ℚ) * P.coeff i := by
    intro i
    simp only [Pz, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hi : i ∈ P.support
    · rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte]
        exact (Classical.choose_spec (hD_int_P i)).symm
      · intro j _ hji; simp [hji]
      · intro hnot; exact absurd hi hnot
    · rw [Finset.sum_eq_zero]
      · rw [Polynomial.notMem_support_iff.mp hi, mul_zero, Int.cast_zero]
      · intro j hj; have hji : j ≠ i := fun h => hi (h ▸ hj); simp [hji]
  have hQz_coeff : ∀ i : ℕ, (Qz.coeff i : ℚ) = (D : ℚ) * Q.coeff i := by
    intro i
    simp only [Qz, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    by_cases hi : i ∈ Q.support
    · rw [Finset.sum_eq_single i]
      · simp only [↓reduceIte]
        exact (Classical.choose_spec (hD_int_Q i)).symm
      · intro j _ hji; simp [hji]
      · intro hnot; exact absurd hi hnot
    · rw [Finset.sum_eq_zero]
      · rw [Polynomial.notMem_support_iff.mp hi, mul_zero, Int.cast_zero]
      · intro j hj; have hji : j ≠ i := fun h => hi (h ▸ hj); simp [hji]
  refine ⟨Pz, Qz, ?_, ?_⟩
  · intro h0
    apply hP
    ext i
    have hi := hPz_coeff i
    rw [h0, Polynomial.coeff_zero, Int.cast_zero] at hi
    exact (mul_eq_zero.mp hi.symm).resolve_left hDne
  · ext n
    have hq := congrArg (PowerSeries.coeff n) hEq
    rw [PowerSeries.coeff_mul] at hq ⊢
    simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk] at hq ⊢
    have hmul : ((∑ p ∈ Finset.antidiagonal n, Pz.coeff p.1 * A p.2 : ℤ) : ℚ) = (Qz.coeff n : ℚ) := by
      push_cast
      rw [hQz_coeff n, ← hq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hPz_coeff p.1, mul_assoc]
    exact_mod_cast hmul

private lemma exists_zmod2_poly_mul {A : ℕ → ℤ} {Pz Qz : Polynomial ℤ} (hPz : Pz ≠ 0)
    (hEq : (Pz : PowerSeries ℤ) * PowerSeries.mk A = (Qz : PowerSeries ℤ)) :
    ∃ p q : Polynomial (ZMod 2), p ≠ 0 ∧
      (p : PowerSeries (ZMod 2)) * PowerSeries.mk (fun n => (A n : ZMod 2)) =
        (q : PowerSeries (ZMod 2)) := by
  have hmain : ∀ M : ℕ, ∀ Pz Qz : Polynomial ℤ, Pz ≠ 0 →
      (∑ i ∈ Pz.support, (Pz.coeff i).natAbs) ≤ M →
      (Pz : PowerSeries ℤ) * PowerSeries.mk A = (Qz : PowerSeries ℤ) →
      ∃ p q : Polynomial (ZMod 2), p ≠ 0 ∧
        (p : PowerSeries (ZMod 2)) * PowerSeries.mk (fun n => (A n : ZMod 2)) =
          (q : PowerSeries (ZMod 2)) := by
    intro M
    induction M using Nat.strongRecOn with
    | ind M ih =>
      intro Pz Qz hPz hM hEq
      let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
      let p : Polynomial (ZMod 2) := Pz.map φ
      let q : Polynomial (ZMod 2) := Qz.map φ
      have hpq : (p : PowerSeries (ZMod 2)) * PowerSeries.mk (fun n => (A n : ZMod 2)) =
          (q : PowerSeries (ZMod 2)) := by
        ext n
        have h := congrArg (fun x => φ (PowerSeries.coeff n x)) hEq
        rw [PowerSeries.coeff_mul] at h ⊢
        simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk, map_sum, map_mul] at h ⊢
        simpa [p, q, φ, Polynomial.coeff_map] using h
      by_cases hp0 : p = 0
      · have hq0 : q = 0 := by
          rw [hp0, Polynomial.coe_zero, zero_mul] at hpq
          ext n
          have := congrArg (PowerSeries.coeff n) hpq
          simpa using this.symm
        have hP_even : ∀ i : ℕ, 2 ∣ Pz.coeff i := by
          intro i
          have hi : (Pz.coeff i : ZMod 2) = 0 := by
            have := congrArg (fun f => Polynomial.coeff f i) hp0
            simpa [p, φ, Polynomial.coeff_map] using this
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hi
        have hQ_even : ∀ i : ℕ, 2 ∣ Qz.coeff i := by
          intro i
          have hi : (Qz.coeff i : ZMod 2) = 0 := by
            have := congrArg (fun f => Polynomial.coeff f i) hq0
            simpa [q, φ, Polynomial.coeff_map] using this
          exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hi
        let P' : Polynomial ℤ := ∑ i ∈ Pz.support, Polynomial.monomial i (Pz.coeff i / 2)
        let Q' : Polynomial ℤ := ∑ i ∈ Qz.support, Polynomial.monomial i (Qz.coeff i / 2)
        have hP'_coeff : ∀ i : ℕ, 2 * P'.coeff i = Pz.coeff i := by
          intro i
          simp only [P', Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
          by_cases hi : i ∈ Pz.support
          · rw [Finset.sum_eq_single i]
            · simp only [↓reduceIte]; exact Int.mul_ediv_cancel' (hP_even i)
            · intro j _ hji; simp [hji]
            · intro hnot; exact absurd hi hnot
          · rw [Finset.sum_eq_zero]
            · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]
            · intro j hj; have hji : j ≠ i := fun h => hi (h ▸ hj); simp [hji]
        have hQ'_coeff : ∀ i : ℕ, 2 * Q'.coeff i = Qz.coeff i := by
          intro i
          simp only [Q', Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
          by_cases hi : i ∈ Qz.support
          · rw [Finset.sum_eq_single i]
            · simp only [↓reduceIte]; exact Int.mul_ediv_cancel' (hQ_even i)
            · intro j _ hji; simp [hji]
            · intro hnot; exact absurd hi hnot
          · rw [Finset.sum_eq_zero]
            · rw [Polynomial.notMem_support_iff.mp hi, mul_zero]
            · intro j hj; have hji : j ≠ i := fun h => hi (h ▸ hj); simp [hji]
        have hP'ne : P' ≠ 0 := by
          intro h0; apply hPz; ext i
          rw [← hP'_coeff i, h0, Polynomial.coeff_zero, mul_zero]
        have hEq' : (P' : PowerSeries ℤ) * PowerSeries.mk A = (Q' : PowerSeries ℤ) := by
          ext n
          have h := congrArg (PowerSeries.coeff n) hEq
          rw [PowerSeries.coeff_mul] at h ⊢
          simp only [Polynomial.coeff_coe, PowerSeries.coeff_mk] at h ⊢
          have h2 : 2 * ∑ x ∈ Finset.antidiagonal n, P'.coeff x.1 * A x.2 = 2 * Q'.coeff n := by
            rw [Finset.mul_sum, hQ'_coeff n, ← h]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← mul_assoc, hP'_coeff x.1]
          linarith
        have hsum_lt : (∑ i ∈ P'.support, (P'.coeff i).natAbs) <
            ∑ i ∈ Pz.support, (Pz.coeff i).natAbs := by
          have hsub : P'.support ⊆ Pz.support := by
            intro i hi
            rw [Polynomial.mem_support_iff] at hi ⊢
            rw [← hP'_coeff i]; omega
          have hpos_sum : 0 < ∑ i ∈ P'.support, (P'.coeff i).natAbs := by
            obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hP'ne
            have h1 : 0 < (P'.coeff i).natAbs :=
              Int.natAbs_pos.mpr (Polynomial.mem_support_iff.mp hi)
            exact lt_of_lt_of_le h1
              (Finset.single_le_sum (f := fun j => (P'.coeff j).natAbs) (fun _ _ => Nat.zero_le _) hi)
          have hdouble : 2 * ∑ i ∈ P'.support, (P'.coeff i).natAbs =
              ∑ i ∈ Pz.support, (Pz.coeff i).natAbs := by
            rw [Finset.mul_sum]
            have h1 : ∑ i ∈ P'.support, 2 * (P'.coeff i).natAbs =
                ∑ i ∈ P'.support, (Pz.coeff i).natAbs := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← hP'_coeff i, Int.natAbs_mul]; rfl
            rw [h1]
            refine Finset.sum_subset hsub fun i _ hi' => ?_
            have h0 : P'.coeff i = 0 := Polynomial.notMem_support_iff.mp hi'
            rw [← hP'_coeff i, h0, mul_zero]; rfl
          omega
        exact ih (∑ i ∈ P'.support, (P'.coeff i).natAbs) (by omega) P' Q' hP'ne le_rfl hEq'
      · exact ⟨p, q, hp0, hpq⟩
  exact hmain (∑ i ∈ Pz.support, (Pz.coeff i).natAbs) Pz Qz hPz le_rfl hEq

private theorem prove_disproof : ¬ type_of% @OMA.S_oeis_a101912.main := by
  rintro ⟨P, Q, hPne, hEq⟩
  obtain ⟨Pz, Qz, hPzne, hEqz⟩ := exists_int_poly_mul hPne hEq
  obtain ⟨p, q, hpne, hpq⟩ := exists_zmod2_poly_mul hPzne hEqz
  let A₂ : PowerSeries (ZMod 2) := PowerSeries.mk (fun n => (a101912 n : ZMod 2))
  have hA2 : A₂ + PowerSeries.X * A₂ ^ 3 = 1 := A2_eq A₂ rfl
  let g := EuclideanDomain.gcd p q
  have hg_dvd_p : g ∣ p := EuclideanDomain.gcd_dvd_left p q
  have hg_dvd_q : g ∣ q := EuclideanDomain.gcd_dvd_right p q
  obtain ⟨R, hR⟩ := hg_dvd_p
  obtain ⟨S, hS⟩ := hg_dvd_q
  have hgne : g ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hR; exact hpne hR
  have hRne : R ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hR; exact hpne hR
  have hRA : (R : PowerSeries (ZMod 2)) * A₂ = (S : PowerSeries (ZMod 2)) := by
    have hgne_ps : (g : PowerSeries (ZMod 2)) ≠ 0 := by
      intro h0; apply hgne; ext n
      have := congrArg (PowerSeries.coeff n) h0; simpa using this
    have hzero : (g : PowerSeries (ZMod 2)) * ((R : PowerSeries (ZMod 2)) * A₂ - (S : PowerSeries (ZMod 2))) = 0 := by
      rw [mul_sub, ← mul_assoc, ← Polynomial.coe_mul, ← hR, hpq, hS, Polynomial.coe_mul, sub_self]
    exact sub_eq_zero.mp (ps_zmod2_mul_eq_zero hgne_ps hzero)
  have hpoly_ps : ((S * R ^ 2 + Polynomial.X * S ^ 3 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) =
      ((R ^ 3 : Polynomial (ZMod 2)) : PowerSeries (ZMod 2)) := by
    have hmul := congrArg (fun f => (R : PowerSeries (ZMod 2)) ^ 3 * f) hA2
    simp only [mul_add, mul_one] at hmul
    have h1 : (R : PowerSeries (ZMod 2)) ^ 3 * A₂ = (S : PowerSeries (ZMod 2)) * (R : PowerSeries (ZMod 2)) ^ 2 := by
      calc (R : PowerSeries (ZMod 2)) ^ 3 * A₂
          = ((R : PowerSeries (ZMod 2)) * A₂) * (R : PowerSeries (ZMod 2)) ^ 2 := by ring
        _ = (S : PowerSeries (ZMod 2)) * (R : PowerSeries (ZMod 2)) ^ 2 := by rw [hRA]
    have h2 : (R : PowerSeries (ZMod 2)) ^ 3 * (PowerSeries.X * A₂ ^ 3) =
        PowerSeries.X * (S : PowerSeries (ZMod 2)) ^ 3 := by
      calc (R : PowerSeries (ZMod 2)) ^ 3 * (PowerSeries.X * A₂ ^ 3)
          = PowerSeries.X * ((R : PowerSeries (ZMod 2)) * A₂) ^ 3 := by ring
        _ = PowerSeries.X * (S : PowerSeries (ZMod 2)) ^ 3 := by rw [hRA]
    rw [h1, h2] at hmul
    simpa [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X] using hmul
  have hpoly : S * R ^ 2 + Polynomial.X * S ^ 3 = R ^ 3 := by
    ext n
    have := congrArg (PowerSeries.coeff n) hpoly_ps
    rwa [Polynomial.coeff_coe, Polynomial.coeff_coe] at this
  have hcop : IsCoprime S R := by
    let a := EuclideanDomain.gcdA p q
    let b := EuclideanDomain.gcdB p q
    have hbez : g = p * a + q * b := EuclideanDomain.gcd_eq_gcd_ab p q
    rw [hR, hS] at hbez
    have h1 : g * 1 = g * (R * a + S * b) := by
      calc g * 1 = g := mul_one g
        _ = g * R * a + g * S * b := hbez
        _ = g * (R * a + S * b) := by ring
    have h1' : R * a + S * b = 1 := (mul_left_cancel₀ hgne h1).symm
    exact ⟨b, a, by rw [mul_comm b S, mul_comm a R, add_comm]; exact h1'⟩
  have hS_dvd : S ∣ R ^ 3 := by
    refine ⟨R ^ 2 + Polynomial.X * S ^ 2, ?_⟩
    rw [← hpoly]; ring
  have hS_unit : IsUnit S := (hcop.pow_right (n := 3)).isUnit_of_dvd' dvd_rfl hS_dvd
  have hS_eq_one : S = 1 := by
    rw [Polynomial.isUnit_iff] at hS_unit
    obtain ⟨c, hc_unit, hc_eq⟩ := hS_unit
    have hc1 : c = 1 := by
      fin_cases c
      · exact absurd hc_unit not_isUnit_zero
      · rfl
    subst hc1
    simpa using hc_eq.symm
  rw [hS_eq_one, one_mul, one_pow, mul_one] at hpoly
  have hXeq : Polynomial.X = R ^ 2 * (R + 1) := by
    have h0 : R ^ 2 + R ^ 2 = (0 : Polynomial (ZMod 2)) := by
      ext n; simp [zmod2_add_self]
    calc Polynomial.X = R ^ 2 + (R ^ 2 + Polynomial.X) := by rw [← add_assoc, h0, zero_add]
      _ = R ^ 2 + R ^ 3 := by rw [hpoly]
      _ = R ^ 2 * (R + 1) := by ring
  by_cases hdeg : R.natDegree = 0
  · have hRC : R = Polynomial.C (R.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    have hc : R.coeff 0 = 0 ∨ R.coeff 0 = 1 := by
      generalize R.coeff 0 = c
      fin_cases c
      · left; rfl
      · right; rfl
    rcases hc with h0 | h1
    · rw [hRC, h0, map_zero] at hXeq
      simp at hXeq
    · rw [hRC, h1, map_one] at hXeq
      have h11 : (1 : Polynomial (ZMod 2)) + 1 = 0 := by ext n; simp [zmod2_add_self]
      rw [h11, mul_zero] at hXeq
      exact Polynomial.X_ne_zero hXeq
  · have hRpos : 1 ≤ R.natDegree := Nat.pos_of_ne_zero hdeg
    have hR1_deg : (R + 1).natDegree = R.natDegree := by
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt]
      rw [Polynomial.natDegree_one]
      omega
    have hR1_ne : R + 1 ≠ 0 := by
      intro h0; rw [h0, Polynomial.natDegree_zero] at hR1_deg; omega
    have hdeg_eq : (Polynomial.X : Polynomial (ZMod 2)).natDegree = (R ^ 2 * (R + 1)).natDegree :=
      congrArg Polynomial.natDegree hXeq
    rw [Polynomial.natDegree_X, Polynomial.natDegree_mul (pow_ne_zero 2 hRne) hR1_ne,
      Polynomial.natDegree_pow, hR1_deg] at hdeg_eq
    omega

end OMA.P_oeis_a101912

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a101912.main) :=
  OMA.P_oeis_a101912.prove_disproof
