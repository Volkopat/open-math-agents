import OMAStatements.S_oeis_a219431
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

namespace OMA.P_oeis_a219431

open OMA.S_oeis_a219431

/-! ### Part 1: Overpartitions mod 4 via distinct part sizes -/

private lemma card_divisors_sq_odd (n : ℕ) (hn : 0 < n) : Odd (n ^ 2).divisors.card := by
  have hsq : IsSquare (n ^ 2) := ⟨n, sq n⟩
  rw [Nat.odd_iff]
  have h1 : Odd (Nat.divisors (n ^ 2)).card := by
    have hinv : ∀ d ∈ (n ^ 2).divisors, n ^ 2 / d ∈ (n ^ 2).divisors := by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨Nat.div_dvd_of_dvd hd.1, hd.2⟩
    let S := (n ^ 2).divisors
    let A := S.filter (fun d => d < n)
    let B := S.filter (fun d => n < d)
    have hns : n ∈ S := by
      rw [Nat.mem_divisors]
      exact ⟨⟨n, by ring⟩, by positivity⟩
    have hun : S = insert n (A ∪ B) := by
      ext d
      simp only [Finset.mem_insert, Finset.mem_union, A, B, Finset.mem_filter]
      constructor
      · intro hd
        rcases lt_trichotomy d n with hlt | rfl | hgt
        · exact Or.inr (Or.inl ⟨hd, hlt⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨hd, hgt⟩)
      · rintro (rfl | ⟨hd, _⟩ | ⟨hd, _⟩)
        · exact hns
        · exact hd
        · exact hd
    have hn_not : n ∉ A ∪ B := by
      simp only [Finset.mem_union, A, B, Finset.mem_filter]
      omega
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro d hA hB
      simp only [A, B, Finset.mem_filter] at hA hB
      omega
    have hcard_eq : A.card = B.card := by
      refine Finset.card_bij (fun d _ => n ^ 2 / d) ?_ ?_ ?_
      · intro d hd
        simp only [A, B, Finset.mem_filter] at hd ⊢
        refine ⟨hinv d hd.1, ?_⟩
        rw [Nat.mem_divisors] at hd
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1.1 (by positivity)
        have hmul : d * (n ^ 2 / d) = n ^ 2 := Nat.mul_div_cancel' hd.1.1
        nlinarith
      · intro d1 hd1 d2 hd2 h
        simp only [A, Finset.mem_filter] at hd1 hd2
        rw [Nat.mem_divisors] at hd1 hd2
        have h1 : d1 * (n ^ 2 / d1) = n ^ 2 := Nat.mul_div_cancel' hd1.1.1
        have h2 : d2 * (n ^ 2 / d2) = n ^ 2 := Nat.mul_div_cancel' hd2.1.1
        have hpos : 0 < n ^ 2 / d1 := by
          have : d1 * (n ^ 2 / d1) = n ^ 2 := h1
          nlinarith
        rw [h] at h1 hpos
        exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
      · intro d hd
        simp only [A, B, Finset.mem_filter] at hd ⊢
        refine ⟨n ^ 2 / d, ⟨hinv d hd.1, ?_⟩, ?_⟩
        · rw [Nat.mem_divisors] at hd
          have hmul : d * (n ^ 2 / d) = n ^ 2 := Nat.mul_div_cancel' hd.1.1
          nlinarith
        · rw [Nat.mem_divisors] at hd
          exact Nat.div_div_self hd.1.1 (by positivity)
    change Odd S.card
    rw [hun, Finset.card_insert_of_notMem hn_not, Finset.card_union_of_disjoint hdisj, ← hcard_eq]
    exact ⟨A.card, by ring⟩
  exact Nat.odd_iff.mp h1

private lemma overpartitionCount_mod4 (N : ℕ) (hN : 0 < N) :
    (overpartitionCount N : ZMod 4) = 2 * ((N.divisors.card : ℕ) : ZMod 4) := by
  unfold overpartitionCount
  push_cast
  let U : Finset (Nat.Partition N) := Finset.univ
  let S1 := U.filter (fun p => p.parts.toFinset.card = 1)
  let S2 := U.filter (fun p => 2 ≤ p.parts.toFinset.card)
  have hpos_card : ∀ p : Nat.Partition N, 1 ≤ p.parts.toFinset.card := by
    intro p
    have hne : p.parts ≠ 0 := by
      intro h0
      have hsum := p.parts_sum
      rw [h0, Multiset.sum_zero] at hsum
      omega
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    exact Finset.card_pos.mpr ⟨a, Multiset.mem_toFinset.mpr ha⟩
  have hun : U = S1 ∪ S2 := by
    ext p
    simp only [U, S1, S2, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff]
    have := hpos_card p
    omega
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2
    omega
  change ∑ p ∈ U, ((2 : ZMod 4) ^ p.parts.toFinset.card) = _
  rw [hun, Finset.sum_union hdisj]
  have hS2 : ∑ p ∈ S2, ((2 : ZMod 4) ^ p.parts.toFinset.card) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp only [S2, Finset.mem_filter] at hp
    have hk : p.parts.toFinset.card = 2 + (p.parts.toFinset.card - 2) := by omega
    rw [hk, pow_add, show (2 : ZMod 4) ^ 2 = 0 by decide, zero_mul]
  have hS1 : ∑ p ∈ S1, ((2 : ZMod 4) ^ p.parts.toFinset.card) = 2 * (S1.card : ZMod 4) := by
    have hconst : ∑ p ∈ S1, ((2 : ZMod 4) ^ p.parts.toFinset.card) = ∑ _p ∈ S1, (2 : ZMod 4) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      simp only [S1, Finset.mem_filter] at hp
      rw [hp.2, pow_one]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hS2, add_zero, hS1]
  congr 2
  -- Bijection between S1 and N.divisors
  refine Finset.card_bij (fun p hp =>
      (Finset.card_eq_one.mp (Finset.mem_filter.mp hp).2).choose) ?_ ?_ ?_
  · intro p hp
    have hcard1 : p.parts.toFinset.card = 1 := (Finset.mem_filter.mp hp).2
    set d := (Finset.card_eq_one.mp hcard1).choose
    have hd_eq : p.parts.toFinset = {d} := (Finset.card_eq_one.mp hcard1).choose_spec
    have hall : ∀ x ∈ p.parts, x = d := by
      intro x hx
      have : x ∈ ({d} : Finset ℕ) := by rw [← hd_eq]; exact Multiset.mem_toFinset.mpr hx
      exact Finset.mem_singleton.mp this
    have hparts_eq : p.parts = Multiset.replicate p.parts.card d :=
      Multiset.eq_replicate.mpr ⟨rfl, hall⟩
    have hsum : p.parts.card * d = N := by
      have := p.parts_sum
      rw [hparts_eq, Multiset.sum_replicate, smul_eq_mul] at this
      exact this
    rw [Nat.mem_divisors]
    exact ⟨⟨p.parts.card, by linarith⟩, by omega⟩
  · intro p1 hp1 p2 hp2 hEq
    have h1 := (Finset.mem_filter.mp hp1).2
    have h2 := (Finset.mem_filter.mp hp2).2
    set d1 := (Finset.card_eq_one.mp h1).choose
    set d2 := (Finset.card_eq_one.mp h2).choose
    have hd1 : p1.parts.toFinset = {d1} := (Finset.card_eq_one.mp h1).choose_spec
    have hd2 : p2.parts.toFinset = {d2} := (Finset.card_eq_one.mp h2).choose_spec
    have heq1 : p1.parts = Multiset.replicate p1.parts.card d1 :=
      Multiset.eq_replicate.mpr ⟨rfl, fun x hx =>
        Finset.mem_singleton.mp (by rw [← hd1]; exact Multiset.mem_toFinset.mpr hx)⟩
    have heq2 : p2.parts = Multiset.replicate p2.parts.card d2 :=
      Multiset.eq_replicate.mpr ⟨rfl, fun x hx =>
        Finset.mem_singleton.mp (by rw [← hd2]; exact Multiset.mem_toFinset.mpr hx)⟩
    have hsum1 : p1.parts.card * d1 = N := by
      have := p1.parts_sum; rw [heq1, Multiset.sum_replicate, smul_eq_mul] at this; exact this
    have hsum2 : p2.parts.card * d2 = N := by
      have := p2.parts_sum; rw [heq2, Multiset.sum_replicate, smul_eq_mul] at this; exact this
    have hd1_pos : 0 < d1 := by
      have : d1 ∈ p1.parts := Multiset.mem_toFinset.mp (by rw [hd1]; simp)
      exact p1.parts_pos this
    have hcard_eq : p1.parts.card = p2.parts.card := by
      rw [← hEq] at hsum2
      exact Nat.eq_of_mul_eq_mul_right hd1_pos (hsum1.trans hsum2.symm)
    ext x
    rw [heq1, heq2, hcard_eq, hEq]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd.1 hN
    let m := N / d
    have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd hN hd.1) hdpos
    have hmd : m * d = N := Nat.div_mul_cancel hd.1
    let p : Nat.Partition N :=
      { parts := Multiset.replicate m d
        parts_pos := fun hx => by
          rw [Multiset.mem_replicate] at hx
          rw [hx.2]; exact hdpos
        parts_sum := by rw [Multiset.sum_replicate, smul_eq_mul]; exact hmd }
    have htoFinset : p.parts.toFinset = {d} := by
      ext x
      simp only [p, Multiset.mem_toFinset, Multiset.mem_replicate, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    have hpS1 : p ∈ S1 := by
      simp only [S1, U, Finset.mem_filter, Finset.mem_univ, true_and, htoFinset,
        Finset.card_singleton]
    refine ⟨p, hpS1, ?_⟩
    have hspec := (Finset.card_eq_one.mp (Finset.mem_filter.mp hpS1).2).choose_spec
    exact Finset.singleton_injective (hspec.symm.trans htoFinset)

private lemma overpartitionCount_sq_mod4 (n : ℕ) (hn : 0 < n) :
    (overpartitionCount (n ^ 2) : ZMod 4) = 2 := by
  rw [overpartitionCount_mod4 (n ^ 2) (by positivity)]
  obtain ⟨k, hk⟩ := card_divisors_sq_odd n hn
  rw [hk]
  push_cast
  calc (2 : ZMod 4) * (2 * (k : ZMod 4) + 1)
      = 4 * (k : ZMod 4) + 2 := by ring
    _ = 0 * (k : ZMod 4) + 2 := by rw [show (4 : ZMod 4) = 0 by decide]
    _ = 2 := by ring

private lemma overpartitionCount_zero : overpartitionCount 0 = 1 := by
  unfold overpartitionCount
  have huniv : (Finset.univ : Finset (Nat.Partition 0)) = {Nat.Partition.indiscrete 0} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    ext x
    have h0 : p.parts = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
      have hpos : 0 < a := p.parts_pos ha
      have hle : a ≤ p.parts.sum := Multiset.le_sum_of_mem ha
      rw [p.parts_sum] at hle
      omega
    have h0' : (Nat.Partition.indiscrete 0).parts = 0 := by
      by_contra hne
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
      have hpos : 0 < a := (Nat.Partition.indiscrete 0).parts_pos ha
      have hle : a ≤ (Nat.Partition.indiscrete 0).parts.sum := Multiset.le_sum_of_mem ha
      rw [(Nat.Partition.indiscrete 0).parts_sum] at hle
      omega
    rw [h0, h0']
  rw [huniv, Finset.sum_singleton]
  have h0' : (Nat.Partition.indiscrete 0).parts = 0 := by
    by_contra hne
    obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hne
    have hpos : 0 < a := (Nat.Partition.indiscrete 0).parts_pos ha
    have hle : a ≤ (Nat.Partition.indiscrete 0).parts.sum := Multiset.le_sum_of_mem ha
    rw [(Nat.Partition.indiscrete 0).parts_sum] at hle
    omega
  rw [h0']; simp

/-! ### Part 2: Power series logarithmic derivative mod 4 -/

private lemma four_eq_zero_ps : (4 : PowerSeries (ZMod 4)) = 0 := by
  change PowerSeries.C (4 : ZMod 4) = 0
  rw [show (4 : ZMod 4) = 0 by decide, map_zero]

private lemma map_derivative {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : PowerSeries R) :
    PowerSeries.map φ (PowerSeries.derivative R f) = PowerSeries.derivative S (PowerSeries.map φ f) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative, PowerSeries.coeff_derivative,
    PowerSeries.coeff_map, map_mul, map_add, map_natCast, map_one]

private lemma coeff_X_mul_eq {R : Type*} [CommRing R] (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X * f) =
      if 1 ≤ n then PowerSeries.coeff (n - 1) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with h1
  · rw [Finset.sum_eq_single (1, n - 1)]
    · rw [PowerSeries.coeff_X, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have ha1 : p.1 ≠ 1 := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X, if_neg ha1, zero_mul]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X, if_neg (by omega), zero_mul]

private lemma int_mod4_eq_of_zmod4 {x : ℤ} {r : ℤ} (hr0 : 0 ≤ r) (hr4 : r < 4)
    (h : (x : ZMod 4) = (r : ZMod 4)) : x % 4 = r := by
  have hdvd : ((4 : ℕ) : ℤ) ∣ (x - r) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact sub_eq_zero.mpr h
  obtain ⟨q, hq⟩ := hdvd
  push_cast at hq
  have hx : x = 4 * q + r := by linarith
  omega

end OMA.P_oeis_a219431

theorem OMA.solution : type_of% @OMA.S_oeis_a219431.main := by
  intro A hA n
  let φ : ℤ →+* ZMod 4 := Int.castRingHom (ZMod 4)
  let Fm : PowerSeries (ZMod 4) := PowerSeries.map φ OMA.S_oeis_a219431.Fseries
  let Am : PowerSeries (ZMod 4) := PowerSeries.map φ A
  have hrel : Fm * Am = PowerSeries.X * PowerSeries.derivative (ZMod 4) Fm := by
    have hmap := congrArg (PowerSeries.map φ) hA
    rw [map_mul, map_mul, PowerSeries.map_X, OMA.P_oeis_a219431.map_derivative] at hmap
    exact hmap
  let U : PowerSeries (ZMod 4) := PowerSeries.mk fun k => if k = 0 then 0 else 1
  have hFm_eq : Fm = 1 + 2 * U := by
    ext k
    rw [PowerSeries.coeff_map, OMA.S_oeis_a219431.Fseries, PowerSeries.coeff_mk, map_add,
      PowerSeries.coeff_one]
    change (OMA.S_oeis_a219431.overpartitionCount (k ^ 2) : ZMod 4) =
      (if k = 0 then 1 else 0) + PowerSeries.coeff k (PowerSeries.C (2 : ZMod 4) * U)
    rw [PowerSeries.coeff_C_mul]
    cases k with
    | zero =>
      simp only [zero_pow (by omega : 2 ≠ 0), OMA.P_oeis_a219431.overpartitionCount_zero,
        Nat.cast_one, ↓reduceIte, U, PowerSeries.coeff_mk, mul_zero, add_zero]
    | succ m =>
      rw [OMA.P_oeis_a219431.overpartitionCount_sq_mod4 (m + 1) (by omega),
        if_neg (by omega), zero_add]
      simp [U]
  have hAm_eq : Am = (1 - 2 * U) * (PowerSeries.X * PowerSeries.derivative (ZMod 4) Fm) := by
    have hinv : (1 - 2 * U) * Fm = 1 := by
      rw [hFm_eq]
      calc (1 - 2 * U) * (1 + 2 * U) = 1 - 4 * U ^ 2 := by ring
        _ = 1 - 0 * U ^ 2 := by rw [OMA.P_oeis_a219431.four_eq_zero_ps]
        _ = 1 := by ring
    calc Am = 1 * Am := by ring
      _ = ((1 - 2 * U) * Fm) * Am := by rw [hinv]
      _ = (1 - 2 * U) * (Fm * Am) := by ring
      _ = (1 - 2 * U) * (PowerSeries.X * PowerSeries.derivative (ZMod 4) Fm) := by rw [hrel]
  have hAm_simp : Am = PowerSeries.X * PowerSeries.derivative (ZMod 4) (2 * U) := by
    have hd : PowerSeries.derivative (ZMod 4) Fm = PowerSeries.derivative (ZMod 4) (2 * U) := by
      rw [hFm_eq, map_add, PowerSeries.derivative_one, zero_add]
    have hd2 : PowerSeries.derivative (ZMod 4) (2 * U) = 2 * PowerSeries.derivative (ZMod 4) U := by
      ext k
      rw [PowerSeries.coeff_derivative,
        show (2 : PowerSeries (ZMod 4)) = PowerSeries.C (2 : ZMod 4) from rfl,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_derivative]
      ring
    rw [hAm_eq, hd, hd2]
    calc (1 - 2 * U) * (PowerSeries.X * (2 * PowerSeries.derivative (ZMod 4) U))
        = PowerSeries.X * (2 * PowerSeries.derivative (ZMod 4) U) -
          4 * (U * PowerSeries.X * PowerSeries.derivative (ZMod 4) U) := by ring
      _ = PowerSeries.X * (2 * PowerSeries.derivative (ZMod 4) U) -
          0 * (U * PowerSeries.X * PowerSeries.derivative (ZMod 4) U) := by
            rw [OMA.P_oeis_a219431.four_eq_zero_ps]
      _ = PowerSeries.X * (2 * PowerSeries.derivative (ZMod 4) U) := by ring
  have hcoeff : ∀ k : ℕ, ((PowerSeries.coeff k A : ℤ) : ZMod 4) = 2 * (k : ZMod 4) := by
    intro k
    have h1 : ((PowerSeries.coeff k A : ℤ) : ZMod 4) = PowerSeries.coeff k Am := by
      rw [PowerSeries.coeff_map]; rfl
    rw [h1, hAm_simp, OMA.P_oeis_a219431.coeff_X_mul_eq]
    cases k with
    | zero => simp
    | succ m =>
      simp only [show 1 ≤ m + 1 by omega, ↓reduceIte, show m + 1 - 1 = m by omega]
      rw [PowerSeries.coeff_derivative,
        show (2 : PowerSeries (ZMod 4)) = PowerSeries.C (2 : ZMod 4) from rfl,
        PowerSeries.coeff_C_mul]
      simp [U]
  constructor
  · apply OMA.P_oeis_a219431.int_mod4_eq_of_zmod4 (by omega) (by omega)
    rw [hcoeff (2 * n + 1)]
    push_cast
    calc (2 : ZMod 4) * (2 * (n : ZMod 4) + 1)
        = 4 * (n : ZMod 4) + 2 := by ring
      _ = 0 * (n : ZMod 4) + 2 := by rw [show (4 : ZMod 4) = 0 by decide]
      _ = 2 := by ring
  · apply OMA.P_oeis_a219431.int_mod4_eq_of_zmod4 (by omega) (by omega)
    rw [hcoeff (2 * n)]
    push_cast
    calc (2 : ZMod 4) * (2 * (n : ZMod 4))
        = 4 * (n : ZMod 4) := by ring
      _ = 0 * (n : ZMod 4) := by rw [show (4 : ZMod 4) = 0 by decide]
      _ = 0 := by ring
