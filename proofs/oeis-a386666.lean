import OMAStatements.S_oeis_a386666
import Mathlib.Tactic

namespace OMA.P_oeis_a386666

open OMA.S_oeis_a386666

private lemma zmod3_add_three (a : ZMod 3) : a + a + a = 0 := by
  fin_cases a <;> rfl

private lemma zmod3_cube (a : ZMod 3) : a ^ 3 = a := by
  fin_cases a <;> rfl

private lemma coeff_X_mul_eq (f : PowerSeries (ZMod 3)) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.X : PowerSeries (ZMod 3)) * f) =
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
    have ha1 : p.1 ≠ 1 := by omega
    rw [PowerSeries.coeff_X, if_neg ha1, zero_mul]

/-- Frobenius endomorphism on `(ZMod 3)⟦X⟧`: cubing triples exponents. -/
private lemma coeff_cube_zmod3 (f : PowerSeries (ZMod 3)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 3) =
      if n % 3 = 0 then PowerSeries.coeff (n / 3) f else 0 := by
  have htriple : PowerSeries.coeff n (f ^ 3) =
      ∑ t ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
        (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = n),
        PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f := by
    rw [show f ^ 3 = (f * f) * f by ring, PowerSeries.coeff_mul]
    simp_rw [PowerSeries.coeff_mul, Finset.sum_mul]
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun p _ => (p.2.1, p.2.2, p.1.2)) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    · intro p1 hp1 p2 hp2 h
      rcases p1 with ⟨⟨s1, c1⟩, ⟨a1, b1⟩⟩
      rcases p2 with ⟨⟨s2, c2⟩, ⟨a2, b2⟩⟩
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal] at hp1 hp2
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hs : s1 = s2 := by omega
      subst hs; rfl
    · intro t ht
      rcases t with ⟨a, b, c⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
      refine ⟨⟨(a + b, c), (a, b)⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, Finset.mem_antidiagonal]
      exact ⟨ht.2, trivial⟩
    · intro _ _; rfl
  rw [htriple]
  let B := (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))
  let T := B.filter (fun t : ℕ × ℕ × ℕ => t.1 + t.2.1 + t.2.2 = n)
  let D := T.filter (fun t => t.1 = t.2.1 ∧ t.2.1 = t.2.2)
  let R0 := T.filter (fun t => t.1 ≤ t.2.1 ∧ t.1 < t.2.2)
  let R1 := T.filter (fun t => t.2.2 ≤ t.1 ∧ t.2.2 < t.2.1)
  let R2 := T.filter (fun t => t.2.1 ≤ t.2.2 ∧ t.2.1 < t.1)
  have hd01 : Disjoint R0 R1 := by
    rw [Finset.disjoint_left]; intro t h0 h1
    simp only [R0, R1, Finset.mem_filter] at h0 h1; omega
  have hd012 : Disjoint (R0 ∪ R1) R2 := by
    rw [Finset.disjoint_left]; intro t h01 h2
    simp only [Finset.mem_union, R0, R1, R2, Finset.mem_filter] at h01 h2
    rcases h01 with h | h <;> omega
  have hdR : Disjoint ((R0 ∪ R1) ∪ R2) D := by
    rw [Finset.disjoint_left]; intro t hR hD
    simp only [Finset.mem_union, R0, R1, R2, D, Finset.mem_filter] at hR hD
    rcases hR with (h | h) | h <;> omega
  have hun : T = ((R0 ∪ R1) ∪ R2) ∪ D := by
    ext ⟨a, b, c⟩
    simp only [Finset.mem_union, T, R0, R1, R2, D, Finset.mem_filter]
    constructor
    · intro ht
      by_cases habc : a = b ∧ b = c
      · exact Or.inr ⟨ht, habc⟩
      · left
        by_cases h0 : a ≤ b ∧ a < c
        · exact Or.inl (Or.inl ⟨ht, h0⟩)
        · by_cases h1 : c ≤ a ∧ c < b
          · exact Or.inl (Or.inr ⟨ht, h1⟩)
          · exact Or.inr ⟨ht, by omega⟩
    · rintro (((⟨ht, _⟩ | ⟨ht, _⟩) | ⟨ht, _⟩) | ⟨ht, _⟩) <;> exact ht
  have hrot1 : ∑ t ∈ R1, PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f =
      ∑ t ∈ R0, PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f := by
    refine Finset.sum_bij (fun t _ => (t.2.2, t.1, t.2.1)) ?_ ?_ ?_ ?_
    · intro ⟨a, b, c⟩ ht
      simp only [R1, R0, T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩; rfl
    · intro ⟨a, b, c⟩ ht
      refine ⟨(b, c, a), ?_, rfl⟩
      simp only [R1, R0, T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro ⟨a, b, c⟩ _; ring
  have hrot2 : ∑ t ∈ R2, PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f =
      ∑ t ∈ R0, PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f := by
    refine Finset.sum_bij (fun t _ => (t.2.1, t.2.2, t.1)) ?_ ?_ ?_ ?_
    · intro ⟨a, b, c⟩ ht
      simp only [R2, R0, T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro ⟨a1, b1, c1⟩ _ ⟨a2, b2, c2⟩ _ h
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩; rfl
    · intro ⟨a, b, c⟩ ht
      refine ⟨(c, a, b), ?_, rfl⟩
      simp only [R2, R0, T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht ⊢
      omega
    · intro ⟨a, b, c⟩ _; ring
  have hdiag : ∑ t ∈ D, PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f =
      if n % 3 = 0 then PowerSeries.coeff (n / 3) f else 0 := by
    split_ifs with h3
    · have hDeq : D = {(n / 3, n / 3, n / 3)} := by
        ext ⟨a, b, c⟩
        simp only [D, T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
          Finset.mem_singleton, Prod.mk.injEq]
        omega
      rw [hDeq, Finset.sum_singleton, show PowerSeries.coeff (n / 3) f * PowerSeries.coeff (n / 3) f *
          PowerSeries.coeff (n / 3) f = (PowerSeries.coeff (n / 3) f) ^ 3 by ring, zmod3_cube]
    · have hDeq : D = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro ⟨a, b, c⟩ ht
        simp only [D, T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
        omega
      rw [hDeq, Finset.sum_empty]
  change ∑ t ∈ T, PowerSeries.coeff t.1 f * PowerSeries.coeff t.2.1 f * PowerSeries.coeff t.2.2 f = _
  rw [hun, Finset.sum_union hdR, Finset.sum_union hd012, Finset.sum_union hd01, hrot1, hrot2,
    zmod3_add_three, zero_add, hdiag]

private lemma coeff_pow_eq_zero_of_lt {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) :
    ∀ k n : ℕ, n < k → PowerSeries.coeff n (g ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases hb : b = 0
    · subst hb
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hg0, mul_zero]
    · rw [ih a (by omega), zero_mul]

private lemma coeff_pow_eq_zero_of_lt2 {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) (hg1 : PowerSeries.coeff 1 g = 0) :
    ∀ k n : ℕ, n < 2 * k → PowerSeries.coeff n (g ^ k) = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ m ih =>
    intro n hn
    rw [pow_succ, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases hb0 : b = 0
    · subst hb0; rw [PowerSeries.coeff_zero_eq_constantCoeff, hg0, mul_zero]
    · by_cases hb1 : b = 1
      · subst hb1; rw [hg1, mul_zero]
      · rw [ih a (by omega), zero_mul]

private lemma compPS_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (f g : PowerSeries R) :
    PowerSeries.map φ (compPS f g) = compPS (PowerSeries.map φ f) (PowerSeries.map φ g) := by
  ext n
  simp only [compPS, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => by rw [← map_pow, PowerSeries.coeff_map]

private lemma compPS_one {R : Type*} [CommRing R] (g : PowerSeries R) :
    compPS 1 g = 1 := by
  ext n
  simp only [compPS, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rw [Finset.sum_eq_single 0]
  · simp [PowerSeries.coeff_one]
  · intro k _ hk; simp [hk]
  · intro h0; exfalso; apply h0; simp

private lemma compPS_X {R : Type*} [CommRing R] {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) :
    compPS PowerSeries.X g = g := by
  ext n
  simp only [compPS, PowerSeries.coeff_mk, PowerSeries.coeff_X]
  cases n with
  | zero =>
    simp [PowerSeries.coeff_zero_eq_constantCoeff, hg0]
  | succ m =>
    rw [Finset.sum_eq_single 1]
    · simp
    · intro k _ hk; simp [hk]
    · intro h1; exfalso; apply h1; simp

private lemma compPS_add {R : Type*} [CommRing R] (f h g : PowerSeries R) :
    compPS (f + h) g = compPS f g + compPS h g := by
  ext n
  simp only [compPS, map_add, PowerSeries.coeff_mk, add_mul, Finset.sum_add_distrib]

private lemma compPS_sub {R : Type*} [CommRing R] (f h g : PowerSeries R) :
    compPS (f - h) g = compPS f g - compPS h g := by
  ext n
  simp only [compPS, map_sub, PowerSeries.coeff_mk, sub_mul, Finset.sum_sub_distrib]

private lemma compPS_mul {R : Type*} [CommRing R] (f h : PowerSeries R) {g : PowerSeries R}
    (hg0 : PowerSeries.constantCoeff g = 0) :
    compPS (f * h) g = compPS f g * compPS h g := by
  ext n
  simp only [compPS, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
  have hrhs : ∑ p ∈ Finset.antidiagonal n,
      (∑ j ∈ Finset.range (p.1 + 1), PowerSeries.coeff j f * PowerSeries.coeff p.1 (g ^ j)) *
      (∑ l ∈ Finset.range (p.2 + 1), PowerSeries.coeff l h * PowerSeries.coeff p.2 (g ^ l)) =
      ∑ p ∈ Finset.antidiagonal n,
      (∑ j ∈ Finset.range (n + 1), PowerSeries.coeff j f * PowerSeries.coeff p.1 (g ^ j)) *
      (∑ l ∈ Finset.range (n + 1), PowerSeries.coeff l h * PowerSeries.coeff p.2 (g ^ l)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    congr 1
    · refine Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => ?_
      rw [Finset.mem_range] at hj
      rw [coeff_pow_eq_zero_of_lt hg0 j p.1 (by omega), mul_zero]
    · refine Finset.sum_subset (Finset.range_mono (by omega)) fun l _ hl => ?_
      rw [Finset.mem_range] at hl
      rw [coeff_pow_eq_zero_of_lt hg0 l p.2 (by omega), mul_zero]
  rw [hrhs]
  have hswap : ∑ p ∈ Finset.antidiagonal n,
      (∑ j ∈ Finset.range (n + 1), PowerSeries.coeff j f * PowerSeries.coeff p.1 (g ^ j)) *
      (∑ l ∈ Finset.range (n + 1), PowerSeries.coeff l h * PowerSeries.coeff p.2 (g ^ l)) =
      ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        PowerSeries.coeff j f * PowerSeries.coeff l h * PowerSeries.coeff n (g ^ (j + l)) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [pow_add, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring
  rw [hswap]
  have hgroup : ∑ k ∈ Finset.range (n + 1),
      (∑ p ∈ Finset.antidiagonal k, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 h) *
        PowerSeries.coeff n (g ^ k) =
      ∑ j ∈ Finset.range (n + 1), ∑ l ∈ Finset.range (n + 1),
        PowerSeries.coeff j f * PowerSeries.coeff l h * PowerSeries.coeff n (g ^ (j + l)) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_sigma']
    symm
    rw [← Finset.sum_product']
    refine (Finset.sum_subset (s₁ := ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
      (fun p => p.1 + p.2 ≤ n)) (Finset.filter_subset _ _) ?_).symm.trans ?_
    · intro p hp hnot
      simp only [Finset.mem_filter, hp, true_and, not_le] at hnot
      rw [coeff_pow_eq_zero_of_lt hg0 (p.1 + p.2) n hnot, mul_zero]
    · refine Finset.sum_bij (fun p _ => ⟨p.1 + p.2, p⟩) ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal]
        exact ⟨by omega, trivial⟩
      · intro p1 _ p2 _ h
        exact congrArg Sigma.snd h
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_antidiagonal] at hq
        refine ⟨q.2, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
        · cases q; simp only [Sigma.mk.inj_iff] at hq ⊢; exact ⟨hq.2, heq_of_eq rfl⟩
      · intro p _; rfl
  exact hgroup

private lemma noDigitTwo_iff_div3 (n : ℕ) :
    IsNoDigitTwoBase3 n ↔ n % 3 ≠ 2 ∧ IsNoDigitTwoBase3 (n / 3) := by
  unfold IsNoDigitTwoBase3
  constructor
  · intro h
    refine ⟨?_, fun k => ?_⟩
    · have h0 := h 0; simpa using h0
    · have hk := h (k + 1)
      rw [pow_succ', ← Nat.div_div_eq_div_mul] at hk
      exact hk
  · rintro ⟨hn3, hdiv⟩ k
    cases k with
    | zero => simpa using hn3
    | succ r =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      exact hdiv r

private lemma noDigitTwo_zero : IsNoDigitTwoBase3 0 := fun _ => by simp

open Classical in
private noncomputable def Pseries : PowerSeries (ZMod 3) :=
  PowerSeries.mk fun n => if IsNoDigitTwoBase3 n then 1 else 0

open Classical in
private lemma one_add_X_mul_P3 :
    (1 + (PowerSeries.X : PowerSeries (ZMod 3))) * Pseries ^ 3 = Pseries := by
  ext n
  rw [add_mul, one_mul, map_add, coeff_X_mul_eq, coeff_cube_zmod3]
  by_cases h3 : n % 3 = 0
  · rw [if_pos h3]
    have hsec : (if 1 ≤ n then PowerSeries.coeff (n - 1) (Pseries ^ 3) else 0) = 0 := by
      split_ifs with h1
      · rw [coeff_cube_zmod3, if_neg (by omega)]
      · rfl
    rw [hsec, add_zero]
    simp only [Pseries, PowerSeries.coeff_mk]
    have hiff : IsNoDigitTwoBase3 (n / 3) ↔ IsNoDigitTwoBase3 n := by
      rw [noDigitTwo_iff_div3 n]; exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
    by_cases h : IsNoDigitTwoBase3 n
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
  · by_cases h31 : n % 3 = 1
    · have h1 : 1 ≤ n := by omega
      rw [if_neg h3, zero_add, if_pos h1, coeff_cube_zmod3, if_pos (by omega)]
      simp only [Pseries, PowerSeries.coeff_mk]
      rw [show (n - 1) / 3 = n / 3 by omega]
      have hiff : IsNoDigitTwoBase3 (n / 3) ↔ IsNoDigitTwoBase3 n := by
        rw [noDigitTwo_iff_div3 n]; exact ⟨fun h => ⟨by omega, h⟩, fun h => h.2⟩
      by_cases h : IsNoDigitTwoBase3 n
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    · have h32 : n % 3 = 2 := by omega
      rw [if_neg h3, zero_add]
      have hsec : (if 1 ≤ n then PowerSeries.coeff (n - 1) (Pseries ^ 3) else 0) = 0 := by
        split_ifs with h1
        · rw [coeff_cube_zmod3, if_neg (by omega)]
        · rfl
      rw [hsec]
      simp only [Pseries, PowerSeries.coeff_mk]
      rw [if_neg (fun h => ((noDigitTwo_iff_div3 n).mp h).1 h32)]

private lemma mul_cancel_unit_zmod3 {f g : PowerSeries (ZMod 3)}
    (hg0 : PowerSeries.constantCoeff g ≠ 0) (h : f * g = 0) : f = 0 := by
  ext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hc := congrArg (PowerSeries.coeff n) h
    rw [PowerSeries.coeff_mul, map_zero] at hc
    rw [Finset.sum_eq_single (n, 0)] at hc
    · rw [PowerSeries.coeff_zero_eq_constantCoeff] at hc
      exact (mul_eq_zero.mp hc).resolve_right hg0
    · rintro ⟨a, b⟩ hab hne
      rw [Finset.mem_antidiagonal] at hab
      have hlt : a < n := by
        have hb : b ≠ 0 := fun hb0 => hne (Prod.ext (by omega) hb0)
        omega
      rw [ih a hlt, map_zero, zero_mul]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega

open Classical in
private lemma one_add_X_mul_P2 :
    (1 + (PowerSeries.X : PowerSeries (ZMod 3))) * Pseries ^ 2 = 1 := by
  have hmul : ((1 + (PowerSeries.X : PowerSeries (ZMod 3))) * Pseries ^ 2 - 1) * Pseries = 0 := by
    calc ((1 + PowerSeries.X) * Pseries ^ 2 - 1) * Pseries
        = (1 + PowerSeries.X) * Pseries ^ 3 - Pseries := by ring
      _ = Pseries - Pseries := by rw [one_add_X_mul_P3]
      _ = 0 := sub_self _
  have hP0 : PowerSeries.constantCoeff Pseries ≠ 0 := by
    simp [Pseries, noDigitTwo_zero]
  exact sub_eq_zero.mp (mul_cancel_unit_zmod3 hP0 hmul)

open Classical in
private noncomputable def Bseries : PowerSeries (ZMod 3) :=
  1 - (1 + (PowerSeries.X : PowerSeries (ZMod 3))) * Pseries

open Classical in
private lemma Bseries_props :
    PowerSeries.constantCoeff Bseries = 0 ∧
    PowerSeries.coeff 1 Bseries = 1 ∧
    Bseries ^ 2 = compPS Bseries (PowerSeries.X ^ 2 + Bseries ^ 3) := by
  set t : PowerSeries (ZMod 3) := (1 + PowerSeries.X) * Pseries
  have ht2 : t ^ 2 = 1 + PowerSeries.X := by
    calc t ^ 2 = (1 + PowerSeries.X) * ((1 + PowerSeries.X) * Pseries ^ 2) := by ring
      _ = (1 + PowerSeries.X) * 1 := by rw [one_add_X_mul_P2]
      _ = 1 + PowerSeries.X := mul_one _
  have ht0 : PowerSeries.constantCoeff t = 1 := by
    simp [t, Pseries, noDigitTwo_zero]
  have hB0 : PowerSeries.constantCoeff Bseries = 0 := by
    show PowerSeries.constantCoeff (1 - t) = 0
    rw [map_sub, map_one, ht0, sub_self]
  have hB1 : PowerSeries.coeff 1 Bseries = 1 := by
    show PowerSeries.coeff 1 (1 - (1 + PowerSeries.X) * Pseries) = 1
    rw [map_sub, PowerSeries.coeff_one, if_neg (by decide), add_mul, one_mul, map_add,
      coeff_X_mul_eq, if_pos (by decide)]
    simp only [Pseries, PowerSeries.coeff_mk, Nat.sub_self, show IsNoDigitTwoBase3 1 from by
      rw [noDigitTwo_iff_div3]; exact ⟨by decide, noDigitTwo_zero⟩, noDigitTwo_zero, ite_true]
    decide
  refine ⟨hB0, hB1, ?_⟩
  set g : PowerSeries (ZMod 3) := PowerSeries.X ^ 2 + Bseries ^ 3
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    simp [g, hB0]
  have hcomp_sq : (1 - compPS Bseries g) ^ 2 = 1 + g := by
    have h1 : compPS (1 - Bseries) g = 1 - compPS Bseries g := by
      rw [compPS_sub, compPS_one]
    rw [← h1, sq, ← compPS_mul _ _ hg0, ← sq]
    have h1B : (1 - Bseries) ^ 2 = 1 + PowerSeries.X := by
      show (1 - (1 - t)) ^ 2 = 1 + PowerSeries.X
      rw [sub_sub_cancel]; exact ht2
    rw [h1B, compPS_add, compPS_one, compPS_X hg0]
  have h3zero : (3 : PowerSeries (ZMod 3)) = 0 := by
    ext n
    rw [show (3 : PowerSeries (ZMod 3)) = PowerSeries.C (3 : ZMod 3) from rfl,
      map_zero, PowerSeries.coeff_C]
    split_ifs <;> decide
  have hB2_sq : (1 - Bseries ^ 2) ^ 2 = 1 + g := by
    have hX : (PowerSeries.X : PowerSeries (ZMod 3)) = t ^ 2 - 1 := by
      rw [ht2]; ring
    have hBdef : Bseries = 1 - t := rfl
    calc (1 - Bseries ^ 2) ^ 2
        = (1 - (1 - t) ^ 2) ^ 2 := by rw [hBdef]
      _ = (1 + (t ^ 2 - 1) ^ 2 + (1 - t) ^ 3) + 3 * (-1 + t + t ^ 2 - t ^ 3) := by ring
      _ = (1 + (t ^ 2 - 1) ^ 2 + (1 - t) ^ 3) + 0 * (-1 + t + t ^ 2 - t ^ 3) := by rw [h3zero]
      _ = 1 + (t ^ 2 - 1) ^ 2 + (1 - t) ^ 3 := by ring
      _ = 1 + g := by rw [← hX, ← hBdef]; ring
  have hsq_eq : (1 - compPS Bseries g) ^ 2 = (1 - Bseries ^ 2) ^ 2 := by
    rw [hcomp_sq, hB2_sq]
  have hfac : ((1 - compPS Bseries g) - (1 - Bseries ^ 2)) *
      ((1 - compPS Bseries g) + (1 - Bseries ^ 2)) = 0 := by
    calc _ = (1 - compPS Bseries g) ^ 2 - (1 - Bseries ^ 2) ^ 2 := by ring
      _ = 0 := sub_eq_zero.mpr hsq_eq
  have hcomp0 : PowerSeries.constantCoeff (compPS Bseries g) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    simp [compPS, hB0]
  have hu : PowerSeries.constantCoeff ((1 - compPS Bseries g) + (1 - Bseries ^ 2)) ≠ 0 := by
    simp only [map_add, map_sub, map_one, map_pow, hcomp0, hB0]
    decide
  have heq := sub_eq_zero.mp (mul_cancel_unit_zmod3 hu hfac)
  have : Bseries ^ 2 = compPS Bseries g := by
    calc Bseries ^ 2 = 1 - (1 - Bseries ^ 2) := by ring
      _ = 1 - (1 - compPS Bseries g) := by rw [heq]
      _ = compPS Bseries g := by ring
  exact this

private lemma unique_solution_zmod3 {A B : PowerSeries (ZMod 3)}
    (hA0 : PowerSeries.constantCoeff A = 0) (hA1 : PowerSeries.coeff 1 A = 1)
    (hAeq : A ^ 2 = compPS A (PowerSeries.X ^ 2 + A ^ 3))
    (hB0 : PowerSeries.constantCoeff B = 0) (hB1 : PowerSeries.coeff 1 B = 1)
    (hBeq : B ^ 2 = compPS B (PowerSeries.X ^ 2 + B ^ 3)) :
    A = B := by
  ext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    match n with
    | 0 =>
      rw [PowerSeries.coeff_zero_eq_constantCoeff, hA0, hB0]
    | 1 => rw [hA1, hB1]
    | m + 2 =>
      set gA : PowerSeries (ZMod 3) := PowerSeries.X ^ 2 + A ^ 3
      set gB : PowerSeries (ZMod 3) := PowerSeries.X ^ 2 + B ^ 3
      have hgA0 : PowerSeries.constantCoeff gA = 0 := by simp [gA, hA0]
      have hgB0 : PowerSeries.constantCoeff gB = 0 := by simp [gB, hB0]
      have hgA1 : PowerSeries.coeff 1 gA = 0 := by
        simp only [gA, map_add, PowerSeries.coeff_X_pow, coeff_cube_zmod3,
          show (1 : ℕ) ≠ 2 by omega, show (1 : ℕ) % 3 ≠ 0 by omega, ite_false, add_zero]
      have hgB1 : PowerSeries.coeff 1 gB = 0 := by
        simp only [gB, map_add, PowerSeries.coeff_X_pow, coeff_cube_zmod3,
          show (1 : ℕ) ≠ 2 by omega, show (1 : ℕ) % 3 ≠ 0 by omega, ite_false, add_zero]
      have hg_agree : ∀ j ≤ m + 3, PowerSeries.coeff j gA = PowerSeries.coeff j gB := by
        intro j hj
        simp only [gA, gB, map_add, coeff_cube_zmod3]
        congr 1
        split_ifs with h3
        · exact ih (j / 3) (by omega)
        · rfl
      have hgpow_agree : ∀ k j, j ≤ m + 3 →
          PowerSeries.coeff j (gA ^ k) = PowerSeries.coeff j (gB ^ k) := by
        intro k
        induction k with
        | zero => intro j _; rfl
        | succ r ihr =>
          intro j hj
          rw [pow_succ, pow_succ, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [Finset.mem_antidiagonal] at hp
          rw [ihr p.1 (by omega), hg_agree p.2 (by omega)]
      have hcomp_agree : PowerSeries.coeff (m + 3) (compPS A gA) =
          PowerSeries.coeff (m + 3) (compPS B gB) := by
        simp only [compPS, PowerSeries.coeff_mk]
        refine Finset.sum_congr rfl fun k hk => ?_
        by_cases hlt : k < m + 2
        · rw [ih k hlt, hgpow_agree k (m + 3) (le_refl _)]
        · rw [coeff_pow_eq_zero_of_lt2 hgA0 hgA1 k (m + 3) (by omega),
            coeff_pow_eq_zero_of_lt2 hgB0 hgB1 k (m + 3) (by omega), mul_zero, mul_zero]
      have hsq_agree : PowerSeries.coeff (m + 3) (A ^ 2) = PowerSeries.coeff (m + 3) (B ^ 2) := by
        rw [hAeq, hBeq]; exact hcomp_agree
      rw [sq, sq, PowerSeries.coeff_mul, PowerSeries.coeff_mul] at hsq_agree
      have hsplit : ∀ f : PowerSeries (ZMod 3),
          PowerSeries.constantCoeff f = 0 → PowerSeries.coeff 1 f = 1 →
          ∑ p ∈ Finset.antidiagonal (m + 3), PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f =
            2 * PowerSeries.coeff (m + 2) f +
              ∑ p ∈ (Finset.antidiagonal (m + 3)).filter (fun p => 2 ≤ p.1 ∧ 2 ≤ p.2),
                PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f := by
        intro f hf0 hf1
        let S := Finset.antidiagonal (m + 3)
        let S0 := S.filter (fun p => p.1 = 0 ∨ p.2 = 0)
        let S1 := S.filter (fun p => (p.1 = 1 ∧ p.2 = m + 2) ∨ (p.1 = m + 2 ∧ p.2 = 1))
        let S2 := S.filter (fun p => 2 ≤ p.1 ∧ 2 ≤ p.2)
        have hd01 : Disjoint S0 S1 := by
          rw [Finset.disjoint_left]; intro p h0 h1
          simp only [S0, S1, Finset.mem_filter] at h0 h1; omega
        have hd012 : Disjoint (S0 ∪ S1) S2 := by
          rw [Finset.disjoint_left]; intro p h01 h2
          simp only [Finset.mem_union, S0, S1, S2, Finset.mem_filter] at h01 h2
          rcases h01 with h | h <;> omega
        have hun : S = (S0 ∪ S1) ∪ S2 := by
          ext ⟨a, b⟩
          simp only [Finset.mem_union, S, S0, S1, S2, Finset.mem_filter, Finset.mem_antidiagonal]
          omega
        have hS0 : ∑ p ∈ S0, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f = 0 := by
          apply Finset.sum_eq_zero
          rintro ⟨a, b⟩ hp
          simp only [S0, Finset.mem_filter] at hp
          rcases hp.2 with rfl | rfl
          · rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, zero_mul]
          · rw [PowerSeries.coeff_zero_eq_constantCoeff, hf0, mul_zero]
        have hS1 : ∑ p ∈ S1, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f =
            2 * PowerSeries.coeff (m + 2) f := by
          have hS1eq : S1 = {(1, m + 2), (m + 2, 1)} := by
            ext ⟨a, b⟩
            simp only [S1, S, Finset.mem_filter, Finset.mem_antidiagonal, Finset.mem_insert,
              Finset.mem_singleton, Prod.mk.injEq]
            omega
          rw [hS1eq, Finset.sum_pair (by intro h; simp only [Prod.mk.injEq] at h; omega),
            hf1, one_mul, mul_one]
          ring
        change ∑ p ∈ S, PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 f = _
        rw [hun, Finset.sum_union hd012, Finset.sum_union hd01, hS0, zero_add, hS1]
      rw [hsplit A hA0 hA1, hsplit B hB0 hB1] at hsq_agree
      have hmid : ∑ p ∈ (Finset.antidiagonal (m + 3)).filter (fun p => 2 ≤ p.1 ∧ 2 ≤ p.2),
            PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 A =
          ∑ p ∈ (Finset.antidiagonal (m + 3)).filter (fun p => 2 ≤ p.1 ∧ 2 ≤ p.2),
            PowerSeries.coeff p.1 B * PowerSeries.coeff p.2 B := by
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [Finset.mem_filter, Finset.mem_antidiagonal] at hp
        rw [ih p.1 (by omega), ih p.2 (by omega)]
      rw [hmid] at hsq_agree
      have h2eq : 2 * PowerSeries.coeff (m + 2) A = 2 * PowerSeries.coeff (m + 2) B :=
        add_right_cancel hsq_agree
      have hmul2 := congrArg (fun z : ZMod 3 => 2 * z) h2eq
      have h4 : (2 : ZMod 3) * 2 = 1 := by decide
      simpa only [← mul_assoc, h4, one_mul] using hmul2

open Classical in
private theorem prove_main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      PowerSeries.coeff 1 A = 1 →
      A ^ 2 = compPS A (PowerSeries.X ^ 2 + 4 * A ^ 3) →
      ∀ n : ℕ, 1 ≤ n →
        let v : ZMod 3 := if IsNoDigitTwoBase3 n then 2 else 0
        ((PowerSeries.coeff (3 * n) A : ℤ) : ZMod 3) = v ∧
        2 * ((PowerSeries.coeff (3 * n + 1) A : ℤ) : ZMod 3) = v ∧
        ((PowerSeries.coeff (3 * n + 2) A : ℤ) : ZMod 3) = v := by
  intro A hA0 hA1 hAeq n hn
  set Am : PowerSeries (ZMod 3) := PowerSeries.map (Int.castRingHom (ZMod 3)) A
  have hAm0 : PowerSeries.constantCoeff Am = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, hA0, map_zero]
  have hAm1 : PowerSeries.coeff 1 Am = 1 := by
    rw [PowerSeries.coeff_map, hA1, map_one]
  have hAmeq : Am ^ 2 = compPS Am (PowerSeries.X ^ 2 + Am ^ 3) := by
    have hm := congrArg (PowerSeries.map (Int.castRingHom (ZMod 3))) hAeq
    rw [map_pow, compPS_map, map_add, map_pow, PowerSeries.map_X, map_mul, map_ofNat,
      map_pow] at hm
    have h4 : (4 : PowerSeries (ZMod 3)) = 1 := by
      ext k
      rw [show (4 : PowerSeries (ZMod 3)) = PowerSeries.C (4 : ZMod 3) from rfl,
        PowerSeries.coeff_C, PowerSeries.coeff_one]
      split_ifs <;> decide
    rwa [h4, one_mul] at hm
  obtain ⟨hB0, hB1, hBeq⟩ := Bseries_props
  have hEq : Am = Bseries := unique_solution_zmod3 hAm0 hAm1 hAmeq hB0 hB1 hBeq
  have hcoeff : ∀ k : ℕ, 1 ≤ k →
      ((PowerSeries.coeff k A : ℤ) : ZMod 3) =
        -((if IsNoDigitTwoBase3 k then (1 : ZMod 3) else 0) +
          (if IsNoDigitTwoBase3 (k - 1) then (1 : ZMod 3) else 0)) := by
    intro k hk
    have hc := congrArg (PowerSeries.coeff k) hEq
    rw [PowerSeries.coeff_map] at hc
    rw [show ((PowerSeries.coeff k A : ℤ) : ZMod 3) =
        (Int.castRingHom (ZMod 3)) (PowerSeries.coeff k A) from rfl, hc]
    simp only [Bseries, map_sub, PowerSeries.coeff_one, show k ≠ 0 by omega, ↓reduceIte, zero_sub,
      add_mul, one_mul, map_add, coeff_X_mul_eq, hk, Pseries, PowerSeries.coeff_mk]
  have h3n0 : IsNoDigitTwoBase3 (3 * n) ↔ IsNoDigitTwoBase3 n := by
    rw [noDigitTwo_iff_div3 (3 * n), show 3 * n / 3 = n by omega]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have h3n1 : IsNoDigitTwoBase3 (3 * n + 1) ↔ IsNoDigitTwoBase3 n := by
    rw [noDigitTwo_iff_div3 (3 * n + 1), show (3 * n + 1) / 3 = n by omega]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  have h3nm1 : ¬ IsNoDigitTwoBase3 (3 * n - 1) := by
    intro h
    have := ((noDigitTwo_iff_div3 (3 * n - 1)).mp h).1
    omega
  have h3n2 : ¬ IsNoDigitTwoBase3 (3 * n + 2) := by
    intro h
    have := ((noDigitTwo_iff_div3 (3 * n + 2)).mp h).1
    omega
  dsimp only
  rw [hcoeff (3 * n) (by omega), hcoeff (3 * n + 1) (by omega), hcoeff (3 * n + 2) (by omega),
    show 3 * n + 1 - 1 = 3 * n by omega, show 3 * n + 2 - 1 = 3 * n + 1 by omega]
  by_cases h : IsNoDigitTwoBase3 n
  · rw [if_pos h, if_pos (h3n0.mpr h), if_neg h3nm1, if_pos (h3n1.mpr h), if_neg h3n2]
    refine ⟨by decide, by decide, by decide⟩
  · rw [if_neg h, if_neg (fun h' => h (h3n0.mp h')), if_neg h3nm1,
      if_neg (fun h' => h (h3n1.mp h')), if_neg h3n2]
    refine ⟨by decide, by decide, by decide⟩

end OMA.P_oeis_a386666

theorem OMA.solution : type_of% @OMA.S_oeis_a386666.main :=
  OMA.P_oeis_a386666.prove_main
