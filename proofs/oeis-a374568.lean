import OMAStatements.S_oeis_a374568
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA374568Proof

open Classical
open OMA.S_oeis_a374568

private noncomputable def psComp2 (F G : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F * PowerSeries.coeff n (G ^ k)

private noncomputable def seriesPow4 : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if ∃ k : ℕ, n = 4 ^ k then 1 else 0

private noncomputable def seriesPow2 : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if ∃ j : ℕ, n = 2 ^ j then 1 else 0

private lemma map_psComp (F G : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (psComp F G) =
      psComp2 (PowerSeries.map (Int.castRingHom (ZMod 2)) F)
              (PowerSeries.map (Int.castRingHom (ZMod 2)) G) := by
  ext n
  simp only [PowerSeries.coeff_map, psComp, psComp2, PowerSeries.coeff_mk, map_sum, map_mul,
    ← map_pow]

private lemma coeff_sq_mod2 (f : PowerSeries (ZMod 2)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 2) =
      if n % 2 = 0 then PowerSeries.coeff (n / 2) f else 0 := by
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j f)]
  set S := Finset.range (n + 1)
  set Slt := S.filter (fun i => i < n - i)
  set Sgt := S.filter (fun i => n - i < i)
  set Seq := S.filter (fun i => i = n - i)
  have hdisj1 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2; omega
  have hdisj2 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
  have hunion : S = (Slt ∪ Sgt) ∪ Seq := by
    ext i; simp only [Slt, Sgt, Seq, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hi; rcases lt_trichotomy i (n - i) with h | h | h
      · exact Or.inl (Or.inl ⟨hi, h⟩)
      · exact Or.inr ⟨hi, h⟩
      · exact Or.inl (Or.inr ⟨hi, h⟩)
    · rintro ((⟨hi, _⟩ | ⟨hi, _⟩) | ⟨hi, _⟩) <;> exact hi
  have hsym :
      ∑ i ∈ Sgt, PowerSeries.coeff i f * PowerSeries.coeff (n - i) f =
      ∑ i ∈ Slt, PowerSeries.coeff i f * PowerSeries.coeff (n - i) f := by
    apply Finset.sum_bij (fun i _ => n - i)
    · intro i hi; simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_range] at hi ⊢; omega
    · intro a ha b hb h; simp only [Sgt, S, Finset.mem_filter, Finset.mem_range] at ha hb; omega
    · intro i hi; simp only [Slt, Sgt, S, Finset.mem_filter, Finset.mem_range] at hi ⊢
      exact ⟨n - i, ⟨by omega, by omega⟩, by omega⟩
    · intro i hi
      simp only [Sgt, S, Finset.mem_filter, Finset.mem_range] at hi
      rw [show n - (n - i) = i by omega, mul_comm]
  change ∑ i ∈ S, PowerSeries.coeff i f * PowerSeries.coeff (n - i) f = _
  rw [hunion, Finset.sum_union hdisj2, Finset.sum_union hdisj1, hsym]
  have h2z : ∀ x : ZMod 2, x + x = 0 := by decide
  rw [h2z, zero_add]
  by_cases hpar : n % 2 = 0
  · rw [if_pos hpar]
    have hSeq : Seq = {n / 2} := by
      ext i; simp only [Seq, S, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [hSeq, Finset.sum_singleton, show n - n / 2 = n / 2 by omega]
    have hsq : ∀ x : ZMod 2, x * x = x := by decide
    exact hsq _
  · rw [if_neg hpar]
    have hSeq : Seq = ∅ := by
      ext i; simp only [Seq, S, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty,
        iff_false]; omega
    rw [hSeq, Finset.sum_empty]

private lemma two_eq_zero_ps2 : (2 : PowerSeries (ZMod 2)) = 0 := by
  ext k; rw [show (2 : PowerSeries (ZMod 2)) = PowerSeries.C 2 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (2 : ZMod 2) = 0 by decide]

private lemma add_pow_two_pow_mod2 (u v : PowerSeries (ZMod 2)) :
    ∀ m : ℕ, (u + v) ^ (2 ^ m) = u ^ (2 ^ m) + v ^ (2 ^ m) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, pow_mul, ih]
    have hsq : ∀ a b : PowerSeries (ZMod 2), (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
      intro a b
      calc (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by ring
        _ = a ^ 2 + b ^ 2 := by rw [two_eq_zero_ps2, zero_mul, zero_mul, add_zero]
    rw [hsq, ← pow_mul, ← pow_mul]

private lemma psComp2_pow4_eq_pow2 :
    psComp2 seriesPow4 (PowerSeries.X + PowerSeries.X ^ 2) = seriesPow2 := by
  ext n
  unfold psComp2 seriesPow4 seriesPow2
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  simp only [PowerSeries.coeff_mk]
  have hterm : ∀ k : ℕ,
      ((PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries (ZMod 2)) ^ (4 ^ k)) =
        PowerSeries.X ^ (4 ^ k) + PowerSeries.X ^ (2 * 4 ^ k) := by
    intro k
    have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
      rw [pow_mul]; norm_num
    rw [h4, add_pow_two_pow_mod2, ← pow_mul, ← h4]
  by_cases hpow2 : ∃ j : ℕ, n = 2 ^ j
  · rw [if_pos hpow2]
    rcases hpow2 with ⟨j, rfl⟩
    have hj_half : 4 ^ (j / 2) ≤ 2 ^ j := by
      have h4 : 4 ^ (j / 2) = 2 ^ (2 * (j / 2)) := by rw [pow_mul]; norm_num
      rw [h4]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [Finset.sum_eq_single (4 ^ (j / 2))]
    · rw [if_pos ⟨j / 2, rfl⟩, one_mul, hterm (j / 2), map_add,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
      have h4 : 4 ^ (j / 2) = 2 ^ (2 * (j / 2)) := by rw [pow_mul]; norm_num
      by_cases hpar : j % 2 = 0
      · have heq1 : 2 ^ j = 4 ^ (j / 2) := by rw [h4]; congr 1; omega
        have hne2 : 2 ^ j ≠ 2 * 4 ^ (j / 2) := by
          have : 1 ≤ 4 ^ (j / 2) := Nat.one_le_pow _ 4 (by decide)
          omega
        rw [if_pos heq1, if_neg hne2, add_zero]
      · have hne1 : 2 ^ j ≠ 4 ^ (j / 2) := by
          rw [h4]
          intro h
          have hinj := Nat.pow_right_injective (by decide : 2 ≤ 2) h
          omega
        have heq2 : 2 ^ j = 2 * 4 ^ (j / 2) := by
          rw [h4, ← pow_succ']; congr 1; omega
        rw [if_neg hne1, if_pos heq2, zero_add]
    · intro m _ hne
      by_cases hex : ∃ k : ℕ, m = 4 ^ k
      · rcases hex with ⟨k, rfl⟩
        rw [if_pos ⟨k, rfl⟩, one_mul, hterm k, map_add,
          PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
        have hk_ne : k ≠ j / 2 := fun h => hne (by rw [h])
        have h4 : 4 ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
        have hne1 : 2 ^ j ≠ 4 ^ k := by
          rw [h4]; intro h
          have := Nat.pow_right_injective (by decide : 2 ≤ 2) h
          omega
        have hne2 : 2 ^ j ≠ 2 * 4 ^ k := by
          rw [h4, ← pow_succ']; intro h
          have := Nat.pow_right_injective (by decide : 2 ≤ 2) h
          omega
        rw [if_neg hne1, if_neg hne2, add_zero]
      · rw [if_neg hex, zero_mul]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hpow2]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hex : ∃ k : ℕ, m = 4 ^ k
    · rcases hex with ⟨k, rfl⟩
      rw [if_pos ⟨k, rfl⟩, one_mul, hterm k, map_add,
        PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow]
      have h4 : 4 ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
      have hne1 : n ≠ 4 ^ k := fun h => hpow2 ⟨2 * k, by rw [h, h4]⟩
      have hne2 : n ≠ 2 * 4 ^ k := fun h => hpow2 ⟨2 * k + 1, by rw [h, h4, pow_succ']⟩
      rw [if_neg hne1, if_neg hne2, add_zero]
    · rw [if_neg hex, zero_mul]

private lemma unique_F_eq_seriesPow2 (F : PowerSeries (ZMod 2))
    (hF0 : PowerSeries.coeff 0 F = 0) (hFeq : PowerSeries.X = F - F ^ 2) :
    F = seriesPow2 := by
  have hFadd : F = PowerSeries.X + F ^ 2 := by
    calc F = (F - F ^ 2) + F ^ 2 := by ring
      _ = PowerSeries.X + F ^ 2 := by rw [← hFeq]
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold seriesPow2
    rw [PowerSeries.coeff_mk]
    match n with
    | 0 =>
      rw [hF0, if_neg (by rintro ⟨j, hj⟩; have := Nat.one_le_pow j 2 (by decide); omega)]
    | 1 =>
      have h := congrArg (PowerSeries.coeff 1) hFadd
      rw [map_add, PowerSeries.coeff_X, if_pos rfl, coeff_sq_mod2] at h
      simpa [if_pos (⟨0, rfl⟩ : ∃ j : ℕ, 1 = 2 ^ j)] using h
    | m + 2 =>
      rw [hFadd, map_add, PowerSeries.coeff_X, if_neg (by omega), zero_add, coeff_sq_mod2]
      by_cases hpar : (m + 2) % 2 = 0
      · rw [if_pos hpar, ih ((m + 2) / 2) (by omega)]
        simp only [seriesPow2, PowerSeries.coeff_mk]
        have hiff : (∃ j : ℕ, (m + 2) / 2 = 2 ^ j) ↔ (∃ j : ℕ, m + 2 = 2 ^ j) := by
          constructor
          · rintro ⟨j, hj⟩; exact ⟨j + 1, by rw [pow_succ]; omega⟩
          · rintro ⟨j, hj⟩
            cases j with
            | zero => omega
            | succ j' => exact ⟨j', by rw [pow_succ] at hj; omega⟩
        by_cases hex : ∃ j : ℕ, (m + 2) / 2 = 2 ^ j
        · rw [if_pos hex, if_pos (hiff.mp hex)]
        · rw [if_neg hex, if_neg (mt hiff.mpr hex)]
      · rw [if_neg hpar]
        have hnot : ¬ ∃ j : ℕ, m + 2 = 2 ^ j := by
          rintro ⟨j, hj⟩
          cases j with
          | zero => omega
          | succ j' => rw [pow_succ] at hj; omega
        rw [if_neg hnot]

private lemma coeff_G_pow_diag (G : PowerSeries (ZMod 2))
    (hG0 : PowerSeries.coeff 0 G = 0) (hG1 : PowerSeries.coeff 1 G = 1) :
    ∀ k : ℕ, (∀ m < k, PowerSeries.coeff m (G ^ k) = 0) ∧ PowerSeries.coeff k (G ^ k) = 1 := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun m hm => by omega, ?_⟩
    simp
  | succ k ih =>
    constructor
    · intro m hm
      rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hik : i < k
      · rw [ih.1 i hik, zero_mul]
      · rw [show m - i = 0 by omega, hG0, mul_zero]
    · rw [pow_succ, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i (G ^ k) * PowerSeries.coeff j G)]
      rw [Finset.sum_eq_single k]
      · rw [show k + 1 - k = 1 by omega, ih.2, hG1, mul_one]
      · intro i hi hne
        rw [Finset.mem_range] at hi
        by_cases hik : i < k
        · rw [ih.1 i hik, zero_mul]
        · rw [show k + 1 - i = 0 by omega, hG0, mul_zero]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

private lemma psComp2_inj_left (F1 F2 G : PowerSeries (ZMod 2))
    (hG0 : PowerSeries.coeff 0 G = 0) (hG1 : PowerSeries.coeff 1 G = 1)
    (heq : psComp2 F1 G = psComp2 F2 G) : F1 = F2 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) heq
    simp only [psComp2, PowerSeries.coeff_mk] at hn
    conv at hn => lhs; rw [Finset.sum_range_succ]
    conv at hn => rhs; rw [Finset.sum_range_succ]
    rw [(coeff_G_pow_diag G hG0 hG1 n).2, mul_one, mul_one] at hn
    have hpre :
        ∑ k ∈ Finset.range n, PowerSeries.coeff k F1 * PowerSeries.coeff n (G ^ k) =
        ∑ k ∈ Finset.range n, PowerSeries.coeff k F2 * PowerSeries.coeff n (G ^ k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      rw [ih k hk]
    rw [hpre] at hn
    exact add_left_cancel hn

private lemma map_A_eq_seriesPow4 {A : PowerSeries ℤ} (hA : IsA374568 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A = seriesPow4 := by
  let phi : PowerSeries ℤ →+* PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2))
  let G : PowerSeries (ZMod 2) := PowerSeries.X + PowerSeries.X ^ 2
  have hsub_eq_add : phi (PowerSeries.X - PowerSeries.X ^ 2) = G := by
    dsimp only [phi, G]
    rw [map_sub, map_pow, PowerSeries.map_X]
    calc (PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries (ZMod 2))
        = PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 2 := by ring
      _ = PowerSeries.X + PowerSeries.X ^ 2 := by rw [two_eq_zero_ps2, zero_mul, sub_zero]
  have hadd_eq : phi (PowerSeries.X + PowerSeries.X ^ 2) = G := by
    dsimp only [phi, G]
    rw [map_add, map_pow, PowerSeries.map_X]
  have hFeq : PowerSeries.X = psComp2 (phi A) G - (psComp2 (phi A) G) ^ 2 := by
    have h := congrArg phi hA.2
    rw [map_sub, map_pow, map_psComp, map_psComp, hsub_eq_add, hadd_eq] at h
    dsimp only [phi] at h
    rw [PowerSeries.map_X] at h
    exact h
  have hF0 : PowerSeries.coeff 0 (psComp2 (phi A) G) = 0 := by
    simp [psComp2, phi, hA.1]
  have hF_eq : psComp2 (phi A) G = seriesPow2 :=
    unique_F_eq_seriesPow2 (psComp2 (phi A) G) hF0 hFeq
  have hG0 : PowerSeries.coeff 0 G = 0 := by
    simp [G]
  have hG1 : PowerSeries.coeff 1 G = 1 := by
    simp [G, PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  exact psComp2_inj_left (phi A) seriesPow4 G hG0 hG1 (hF_eq.trans psComp2_pow4_eq_pow2.symm)

end OeisA374568Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a374568.main := by
  intro A hA n
  have hmod : PowerSeries.coeff n A % 2 = 1 ↔ ((PowerSeries.coeff n A : ℤ) : ZMod 2) = 1 := by
    constructor
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] := by rw [Int.ModEq]; omega
      simpa using (ZMod.intCast_eq_intCast_iff _ _ 2).mpr h'
    · intro h
      have h' : PowerSeries.coeff n A ≡ 1 [ZMOD ((2 : ℕ) : ℤ)] :=
        (ZMod.intCast_eq_intCast_iff _ _ 2).mp (by simpa using h)
      rw [Int.ModEq] at h'; omega
  rw [hmod]
  have h := congrArg (PowerSeries.coeff n) (OeisA374568Proof.map_A_eq_seriesPow4 hA)
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, OeisA374568Proof.seriesPow4,
    PowerSeries.coeff_mk] at h
  rw [h]
  split_ifs with hex
  · simp [hex]
  · simp [hex]
