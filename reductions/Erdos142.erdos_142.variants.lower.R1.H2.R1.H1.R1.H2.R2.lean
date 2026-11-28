import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1
import Mathlib

-- Reduction Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H2.R2 of step Erdos142.erdos_142.variants.lower.R1.H2.R1.H1.R1.H2
-- Credit: @DPS0340

/-!
# General Gowers U^(k-1) reduction for super-polylogarithmic r_k(N) bounds (k ≥ 5)

We reduce the `k ≥ 5` super-polylogarithmic bound
`r k N ≤ N * exp (-c * (log log N) ^ A)` (`A > 1`)
to two statements on prime cyclic groups `ZMod p` via Bertrand's postulate (`2N < p ≤ 4N`):
- `H1`: for each `k ≥ 5`, every sufficiently dense subset of `ZMod p` whose balanced function
  `1_S - α` has large Gowers `U^(k-1)` cube sum contains a nontrivial `k`-term progression;
- `H2`: the general Gowers `U^s` generalized von Neumann inequality on `ZMod p` for all `s ≥ 1`.

The telescoping expansion of `∏_{i < k} 1_S(x + i*d) - α^k` splits the `k`-AP count discrepancy
into `k` linear forms, each controlled by `H2` with `s = k - 1`, matching `H1`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2

open Finset Filter Real Erdos142
open scoped Topology

/-- For every k ≥ 5, every sufficiently dense subset of ZMod p whose balanced function has large
Gowers U^(k-1) cube sum contains a nontrivial k-term arithmetic progression in ZMod p. -/
def H1 : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ A c : ℝ, 1 < A ∧ 0 < c ∧ ∀ᶠ p : ℕ in Filter.atTop, ∀ [Fact p.Prime],
    ∀ S : Finset (ZMod p),
      let α : ℝ := (S.card : ℝ) / (p : ℝ)
      let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
      (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) →
      (p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)) ≤
        ∑ x : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
          ∏ ω : Fin (k - 1) → Bool,
            f (x + ∑ j : Fin (k - 1), if ω j then h j else 0) →
      ∃ x d : ZMod p, d ≠ 0 ∧ ∀ i : Fin k, x + (i.val : ZMod p) * d ∈ S

/-- General Gowers U^s generalized von Neumann inequality on ZMod p: for all s ≥ 1,
pairwise distinct shifts c : Fin (s + 1) → ZMod p, and 1-bounded functions on the first s slots,
the (s + 1)-term linear form is controlled by the Gowers U^s cube sum of the last function. -/
def H2 : Prop :=
  ∀ (s p : ℕ) [Fact p.Prime], 1 ≤ s →
    ∀ (c : Fin (s + 1) → ZMod p), Function.Injective c →
    ∀ (f : Fin (s + 1) → ZMod p → ℝ),
      (∀ i : Fin s, ∀ x : ZMod p, |f i.castSucc x| ≤ 1) →
      (∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin (s + 1), f i (x + c i * d)) ^ (2 ^ s) ≤
      (p : ℝ) ^ (2 ^ (s + 1) - s - 1) *
        ∑ x : ZMod p, ∑ h : Fin s → ZMod p,
          ∏ ω : Fin s → Bool,
            f (Fin.last s) (x + ∑ j : Fin s, if ω j then h j else 0)

lemma prod_sub_prod_eq_sum : ∀ (k : ℕ) (u v : Fin k → ℝ),
    (∏ i : Fin k, u i) - (∏ i : Fin k, v i) =
    ∑ m : Fin k, ∏ i : Fin k,
      if i < m then v i else if i = m then u i - v i else u i := by
  intro k
  induction k with
  | zero => intro u v; simp
  | succ k ih =>
    intro u v
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    have hsplit : (∏ i : Fin k, u i.castSucc) * u (Fin.last k) -
        (∏ i : Fin k, v i.castSucc) * v (Fin.last k) =
        ((∏ i : Fin k, u i.castSucc) - (∏ i : Fin k, v i.castSucc)) * u (Fin.last k) +
        (∏ i : Fin k, v i.castSucc) * (u (Fin.last k) - v (Fin.last k)) := by ring
    rw [hsplit, ih (fun i => u i.castSucc) (fun i => v i.castSucc), Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro m _
      rw [Fin.prod_univ_castSucc]
      have hlast1 : ¬ (Fin.last k < m.castSucc) := not_lt.mpr (Fin.le_last _)
      have hlast2 : Fin.last k ≠ m.castSucc := (Fin.castSucc_lt_last m).ne'
      simp only [hlast1, hlast2, ↓reduceIte]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp [Fin.castSucc_lt_castSucc_iff, Fin.castSucc_inj]
    · rw [Fin.prod_univ_castSucc]
      have hlast1 : ¬ (Fin.last k < Fin.last k) := lt_irrefl _
      simp only [hlast1, ↓reduceIte]
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      simp [Fin.castSucc_lt_last i]

lemma exists_extremal_embed {k N : ℕ} (hk : 4 ≤ k) (hN : 2 ≤ N) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (S : Finset (ZMod p)),
      2 * N < p ∧ p ≤ 4 * N ∧ r k N = S.card ∧
      ∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ S) → d = 0 := by
  classical
  have hk1 : (1 : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (show 1 < k by omega)
  obtain ⟨S₀, hS₀, hf, hcard⟩ : ∃ S₀ : Finset ℕ, S₀ ⊆ Icc 1 N ∧ (S₀ : Set ℕ).IsAPOfLengthFree k ∧
      r k N = S₀.card := by
    let C : Set ℕ := {m | ∃ S₀ : Finset ℕ, ∃ _ : S₀ ⊆ Icc 1 N,
      ∃ _ : (S₀ : Set ℕ).IsAPOfLengthFree k, S₀.card = m}
    have hz : 0 ∈ C := ⟨∅, empty_subset _, fun T hT h => (Set.not_isAPOfLength_empty
      (by exact_mod_cast (show 0 < k by omega))
      (Set.subset_empty_iff.mp (by simpa using hT) ▸ h)).elim, rfl⟩
    have hb : BddAbove C := ⟨N, by rintro _ ⟨U, hU, -, rfl⟩; simpa using card_le_card hU⟩
    obtain ⟨S₀, hS₀, hf, he⟩ := Nat.sSup_mem ⟨0, hz⟩ hb
    exact ⟨S₀, hS₀, hf, he.symm⟩
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 * N) (by omega)
  have hfact : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hci : ∀ {u v : ℕ}, u < p → v < p → (u : ZMod p) = (v : ZMod p) → u = v := fun hu hv e => by
    have := congrArg ZMod.val e; rwa [ZMod.val_natCast_of_lt hu, ZMod.val_natCast_of_lt hv] at this
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) (S₀ : Set ℕ) := fun x hx y hy =>
    hci (by have := (mem_Icc.mp (hS₀ hx)).2; omega) (by have := (mem_Icc.mp (hS₀ hy)).2; omega)
  refine ⟨p, hfact, S₀.image Nat.cast, hlo, by omega, by rw [hcard, card_image_of_injOn hinj], ?_⟩
  intro a d hAP
  choose x hxS hxEq using fun i : Fin k => mem_image.mp (hAP i)
  have hxle : ∀ i : Fin k, x i ≤ N := fun i => (mem_Icc.mp (hS₀ (hxS i))).2
  let δ : ℤ := (x ⟨1, by omega⟩ : ℤ) - (x ⟨0, by omega⟩ : ℤ)
  have hstep : ∀ n : ℕ, ∀ hn : n + 1 < k,
      (x ⟨n + 1, hn⟩ : ℤ) - (x ⟨n, by omega⟩ : ℤ) = δ := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ m ih =>
      intro hn
      have hm : x ⟨m, by omega⟩ + x ⟨m + 2, hn⟩ = 2 * x ⟨m + 1, by omega⟩ := by
        apply hci (by have := hxle ⟨m, by omega⟩; have := hxle ⟨m + 2, hn⟩; omega)
                  (by have := hxle ⟨m + 1, by omega⟩; omega)
        push_cast
        rw [hxEq ⟨m, by omega⟩, hxEq ⟨m + 2, hn⟩, hxEq ⟨m + 1, by omega⟩]
        simp only [Nat.cast_add, Nat.cast_ofNat]; ring
      have hmZ : (x ⟨m, by omega⟩ : ℤ) + (x ⟨m + 2, hn⟩ : ℤ) = 2 * (x ⟨m + 1, by omega⟩ : ℤ) := by
        exact_mod_cast hm
      linarith [ih (by omega)]
  have hlin : ∀ n : ℕ, ∀ hn : n < k, (x ⟨n, hn⟩ : ℤ) = (x ⟨0, by omega⟩ : ℤ) + n * δ := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ m ih =>
      intro hn
      have := hstep m hn
      have := ih (by omega)
      push_cast; linarith
  by_cases hδ : δ = 0
  · have h0 := hxEq ⟨0, by omega⟩; have h1 := hxEq ⟨1, by omega⟩
    simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] at h0 h1
    have h01 : x ⟨0, by omega⟩ = x ⟨1, by omega⟩ := by omega
    have hEq : a + 0 = a + d := by
      have : a = a + d := h0.symm.trans (by rw [h01, h1])
      simpa using this
    exact (add_left_cancel hEq).symm
  · exfalso
    let s := δ.natAbs; have hs : 0 < s := Int.natAbs_pos.mpr hδ
    let b := if 0 < δ then x ⟨0, by omega⟩ else x ⟨k - 1, by omega⟩
    let T := (range k).image (fun i => b + i * s)
    have hsubT : (T : Set ℕ) ⊆ (S₀ : Set ℕ) := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hy
      have hi' : i < k := mem_range.mp hi
      by_cases hp0 : 0 < δ
      · have : b + i * s = x ⟨i, hi'⟩ := by
          have := hlin i hi'; have : (s : ℤ) = δ := Int.natAbs_of_nonneg hp0.le
          dsimp [b]; rw [if_pos hp0]; zify; nlinarith
        rw [this]; exact hxS ⟨i, hi'⟩
      · have hn0 : δ < 0 := lt_of_le_of_ne (not_lt.mp hp0) hδ
        have : b + i * s = x ⟨k - 1 - i, by omega⟩ := by
          have := hlin (k - 1) (by omega); have := hlin (k - 1 - i) (by omega)
          have : (s : ℤ) = -δ := Int.ofNat_natAbs_of_nonpos hn0.le
          have : ((k - 1 - i : ℕ) : ℤ) + i = ((k - 1 : ℕ) : ℤ) := by omega
          dsimp [b]; rw [if_neg hp0]; zify; nlinarith
        rw [this]; exact hxS ⟨k - 1 - i, by omega⟩
    have hcT : T.card = k := by
      rw [card_image_of_injective _ fun i j e => Nat.eq_of_mul_eq_mul_right hs (Nat.add_left_cancel e),
        card_range]
    exact hk1.not_ge (hf _ hsubT ⟨b, s, by simp [hcT], by ext y; simp [T]⟩)

lemma ap_count_no_nontriv {k p : ℕ} [Fact p.Prime] (hk : 1 ≤ k) (S : Finset (ZMod p))
    (hfree : ∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ S) → d = 0) :
    (∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin k,
      (if x + (i.val : ZMod p) * d ∈ S then (1 : ℝ) else 0)) = (S.card : ℝ) := by
  classical
  have hinner : ∀ x : ZMod p,
      (∑ d : ZMod p, ∏ i : Fin k, (if x + (i.val : ZMod p) * d ∈ S then (1 : ℝ) else 0)) =
      if x ∈ S then (1 : ℝ) else 0 := by
    intro x
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · by_cases hx : x ∈ S
      · simp [hx]
      · simp only [mul_zero, add_zero, hx, ↓reduceIte]
        exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin k)) rfl
    · intro d _ hd0
      have hnot : ¬ ∀ i : Fin k, x + (i.val : ZMod p) * d ∈ S := fun h => hd0 (hfree x d h)
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    · intro h; exact (h (Finset.mem_univ 0)).elim
  simp_rw [hinner]
  simp

lemma large_u_norm_of_free {k p : ℕ} [Fact p.Prime] (hk : 5 ≤ k) (hkp : k < p)
    (hvn : H2) (S : Finset (ZMod p))
    (hfree : ∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ S) → d = 0)
    (hdense : (2 : ℝ) ≤ (p : ℝ) * ((S.card : ℝ) / (p : ℝ)) ^ (k - 1)) :
    let α : ℝ := (S.card : ℝ) / (p : ℝ)
    let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
    (p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)) ≤
      ∑ x : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
        ∏ ω : Fin (k - 1) → Bool,
          f (x + ∑ j : Fin (k - 1), if ω j then h j else 0) := by
  classical
  intro α f
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hα0 : 0 ≤ α := div_nonneg (Nat.cast_nonneg _) hp_pos.le
  have hα1 : α ≤ 1 := by
    rw [div_le_one hp_pos]
    have hc : S.card ≤ Fintype.card (ZMod p) := Finset.card_le_univ S
    rw [ZMod.card] at hc
    exact_mod_cast hc
  let indS : ZMod p → ℝ := fun x => if x ∈ S then 1 else 0
  let g : Fin k → Fin k → ZMod p → ℝ := fun m i y =>
    if i < m then α else if i = m then f y else indS y
  have hcount : (∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin k, indS (x + (i.val : ZMod p) * d)) =
      (S.card : ℝ) := ap_count_no_nontriv (by omega) S hfree
  have hconst : (∑ _x : ZMod p, ∑ _d : ZMod p, ∏ _i : Fin k, α) = (p : ℝ) ^ 2 * α ^ k := by
    simp [ZMod.card, sq, mul_assoc]
  have htele : (S.card : ℝ) - (p : ℝ) ^ 2 * α ^ k =
      ∑ m : Fin k, ∑ x : ZMod p, ∑ d : ZMod p,
        ∏ i : Fin k, g m i (x + (i.val : ZMod p) * d) := by
    rw [← hcount, ← hconst, ← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, prod_sub_prod_eq_sum]
    trans ∑ x : ZMod p, ∑ m : Fin k, ∑ d : ZMod p,
        ∏ i : Fin k, g m i (x + (i.val : ZMod p) * d)
    · apply Finset.sum_congr rfl; intro x _
      exact Finset.sum_comm
    · exact Finset.sum_comm
  have hcard_le : (S.card : ℝ) ≤ (1 / 2 : ℝ) * ((p : ℝ) ^ 2 * α ^ k) := by
    have hS_eq : (S.card : ℝ) = (p : ℝ) * α := by
      dsimp [α]; field_simp
    have hpow : α ^ k = α * α ^ (k - 1) := by
      conv_lhs => rw [show k = 1 + (k - 1) by omega, pow_add, pow_one]
    rw [hS_eq, hpow]
    have hmul := mul_le_mul_of_nonneg_left hdense (mul_nonneg hp_pos.le hα0)
    linarith
  have hdisc : (1 / 2 : ℝ) * ((p : ℝ) ^ 2 * α ^ k) ≤
      ∑ m : Fin k, |∑ x : ZMod p, ∑ d : ZMod p,
        ∏ i : Fin k, g m i (x + (i.val : ZMod p) * d)| := by
    have h1 : (1 / 2 : ℝ) * ((p : ℝ) ^ 2 * α ^ k) ≤ |(S.card : ℝ) - (p : ℝ) ^ 2 * α ^ k| := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact h1.trans (htele ▸ Finset.abs_sum_le_sum_abs _ _)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hex_m : ∃ m : Fin k, (p : ℝ) ^ 2 * α ^ k / (2 * (k : ℝ)) ≤
      |∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin k, g m i (x + (i.val : ZMod p) * d)| := by
    by_contra hno
    push Not at hno
    have hsum_lt : ∑ m : Fin k, |∑ x : ZMod p, ∑ d : ZMod p,
        ∏ i : Fin k, g m i (x + (i.val : ZMod p) * d)| <
        ∑ _m : Fin k, (p : ℝ) ^ 2 * α ^ k / (2 * (k : ℝ)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      · intro m _; exact hno m
    have hrhs : (∑ _m : Fin k, (p : ℝ) ^ 2 * α ^ k / (2 * (k : ℝ))) =
        (1 / 2 : ℝ) * ((p : ℝ) ^ 2 * α ^ k) := by
      simp [Fintype.card_fin]
      field_simp
    linarith
  obtain ⟨m, hm⟩ := hex_m
  let s : ℕ := k - 1
  have hsk : s + 1 = k := by omega
  let e : Fin (s + 1) ≃ Fin k := finCongr hsk
  let σ : Fin (s + 1) ≃ Fin (s + 1) := Equiv.swap (e.symm m) (Fin.last s)
  let c' : Fin (s + 1) → ZMod p := fun i => ((e (σ i)).val : ZMod p)
  have hc'_inj : Function.Injective c' := by
    intro i j hij
    have hi : (e (σ i)).val < p := lt_trans (e (σ i)).isLt hkp
    have hj : (e (σ j)).val < p := lt_trans (e (σ j)).isLt hkp
    have hval := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hval
    exact σ.injective (e.injective (Fin.ext hval))
  let f' : Fin (s + 1) → ZMod p → ℝ := fun i y => g m (e (σ i)) y
  have hf'_bdd : ∀ i : Fin s, ∀ y : ZMod p, |f' i.castSucc y| ≤ 1 := by
    intro i y
    have hne : e (σ i.castSucc) ≠ m := by
      intro heq
      have h1 : σ i.castSucc = e.symm m := by rw [← heq, Equiv.symm_apply_apply]
      have h2 : i.castSucc = Fin.last s := by
        apply σ.injective
        rw [h1, Equiv.swap_apply_right]
      exact (Fin.castSucc_lt_last i).ne h2
    dsimp [f', g]
    by_cases hlt : e (σ i.castSucc) < m
    · rw [if_pos hlt, abs_of_nonneg hα0]; exact hα1
    · rw [if_neg hlt, if_neg hne]
      dsimp [indS]; split_ifs <;> norm_num
  have hf'_last : f' (Fin.last s) = f := by
    ext y
    have heq : e (σ (Fin.last s)) = m := by
      dsimp [σ]
      rw [Equiv.swap_apply_right, Equiv.apply_symm_apply]
    dsimp [f', g]
    rw [heq, if_neg (lt_irrefl _), if_pos rfl]
  have hsum_eq : (∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin (s + 1), f' i (x + c' i * d)) =
      ∑ x : ZMod p, ∑ d : ZMod p, ∏ i : Fin k, g m i (x + (i.val : ZMod p) * d) := by
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro d _
    exact Fintype.prod_equiv (σ.trans e) _ _ (fun _ => rfl)
  have hvn_app := hvn s p (by omega) c' hc'_inj f' hf'_bdd
  rw [hf'_last, hsum_eq] at hvn_app
  have heven : Even (2 ^ s) := by
    rw [show s = (s - 1) + 1 by omega, pow_succ']
    exact even_two_mul _
  have hnn_lhs : 0 ≤ (p : ℝ) ^ 2 * α ^ k / (2 * (k : ℝ)) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hα0 k)) (mul_nonneg (by norm_num) hk_pos.le)
  have hpow_le : ((p : ℝ) ^ 2 * α ^ k / (2 * (k : ℝ))) ^ (2 ^ s) ≤
      (p : ℝ) ^ (2 ^ (s + 1) - s - 1) *
        ∑ x : ZMod p, ∑ h : Fin s → ZMod p,
          ∏ ω : Fin s → Bool,
            f (x + ∑ j : Fin s, if ω j then h j else 0) := by
    have h1 := pow_le_pow_left₀ hnn_lhs hm (2 ^ s)
    rw [heven.pow_abs] at h1
    exact h1.trans hvn_app
  have hexp_sum : (2 ^ (s + 1) - s - 1) + k = 2 * 2 ^ s := by
    have hle : s + 1 ≤ 2 ^ (s + 1) := by
      have := Nat.lt_two_pow_self (n := s + 1)
      omega
    have hpow2 : 2 ^ (s + 1) = 2 * 2 ^ s := by rw [pow_succ, mul_comm]
    omega
  have hlhs_eq : ((p : ℝ) ^ 2 * α ^ k / (2 * (k : ℝ))) ^ (2 ^ s) =
      (p : ℝ) ^ (2 ^ (s + 1) - s - 1) *
        ((p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ s)) := by
    rw [mul_div_assoc, mul_pow, ← pow_mul, ← mul_assoc, ← pow_add, hexp_sum]
  rw [hlhs_eq] at hpow_le
  exact le_of_mul_le_mul_left hpow_le (pow_pos hp_pos _)

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1.H2 := by
  intro h1 h2 k hk
  obtain ⟨A, c, hA, hc, hp_ev⟩ := h1 k hk
  refine ⟨A, c / 2, hA, half_pos hc, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hpow_ll : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ A) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < A)).comp hloglog
  have hratio : Tendsto (fun x : ℝ => Real.log x ^ A / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop A (s := 1) zero_lt_one).tendsto_div_nhds_zero
  have hcomp : Tendsto (fun p : ℕ => Real.log (Real.log (p : ℝ)) ^ A / Real.log (p : ℝ))
      atTop (𝓝 0) := hratio.comp hlog
  have hkc_pos : 0 < 1 / (2 * ((k - 1 : ℕ) : ℝ) * c) := by
    have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
    positivity
  have hp_good : ∀ᶠ p : ℕ in atTop,
      k < p ∧ (2 : ℝ) ≤ (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) ^ (k - 1) ∧
      ∀ [Fact p.Prime], ∀ S : Finset (ZMod p),
        let α : ℝ := (S.card : ℝ) / (p : ℝ)
        let f : ZMod p → ℝ := fun x => (if x ∈ S then (1 : ℝ) else 0) - α
        (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) →
        (p : ℝ) ^ k * (α ^ k / (2 * (k : ℝ))) ^ (2 ^ (k - 1)) ≤
          ∑ x : ZMod p, ∑ h : Fin (k - 1) → ZMod p,
            ∏ ω : Fin (k - 1) → Bool,
              f (x + ∑ j : Fin (k - 1), if ω j then h j else 0) →
        ∃ x d : ZMod p, d ≠ 0 ∧ ∀ i : Fin k, x + (i.val : ZMod p) * d ∈ S := by
    filter_upwards [hp_ev, eventually_gt_atTop k,
      hlog.eventually (eventually_ge_atTop (2 * Real.log 2)),
      hcomp.eventually (gt_mem_nhds hkc_pos)] with p hp1 hkp hlog2 hdiv
    refine ⟨hkp, ?_, hp1⟩
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    have hlog_pos : 0 < Real.log (p : ℝ) := by
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hmul := (div_lt_iff₀ hlog_pos).mp hdiv
    have hkc : 0 < ((k - 1 : ℕ) : ℝ) * c := by
      have : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k - 1 by omega)
      positivity
    have hbound : ((k - 1 : ℕ) : ℝ) * c * Real.log (Real.log (p : ℝ)) ^ A ≤
        Real.log (p : ℝ) / 2 := by
      have := mul_le_mul_of_nonneg_left hmul.le hkc.le
      have hk1_ne : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
      have heq : ((k - 1 : ℕ) : ℝ) * c * (1 / (2 * ((k - 1 : ℕ) : ℝ) * c) * Real.log (p : ℝ)) =
          Real.log (p : ℝ) / 2 := by field_simp
      linarith
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log (p : ℝ) + ((k - 1 : ℕ) : ℝ) * (-c * Real.log (Real.log (p : ℝ)) ^ A)) := by
          apply Real.exp_le_exp.mpr
          have hmul_eq : ((k - 1 : ℕ) : ℝ) * (-c * Real.log (Real.log (p : ℝ)) ^ A) =
              -(((k - 1 : ℕ) : ℝ) * c * Real.log (Real.log (p : ℝ)) ^ A) := by ring
          linarith
      _ = (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) ^ (k - 1) := by
          rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hp_pos]
  obtain ⟨P₀, hP₀⟩ := eventually_atTop.mp hp_good
  filter_upwards [eventually_ge_atTop (max P₀ 4),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
    hpow_ll.eventually (eventually_ge_atTop (2 * Real.log 4 / c))] with N hN hll1 hll4
  have hN2 : 2 ≤ N := by have := le_max_right P₀ 4; omega
  obtain ⟨p, hfact, S, hlo, hhi, hcard, hfree⟩ := exists_extremal_embed (k := k) (by omega) hN2
  have hpP₀ : P₀ ≤ p := by have := le_max_left P₀ 4; omega
  obtain ⟨hkp, hdense_base, hinv⟩ := hP₀ p hpP₀
  by_contra hgt
  push Not at hgt
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hlog_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (Real.log (p : ℝ)) := by
    apply Real.log_le_log (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
    exact Real.log_le_log hN_pos (by exact_mod_cast (show N ≤ p by omega))
  have hpow_le : Real.log (Real.log (N : ℝ)) ^ A ≤ Real.log (Real.log (p : ℝ)) ^ A :=
    Real.rpow_le_rpow (by linarith) hlog_le (by linarith)
  have hScard : (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) := by
    have h4 : (4 : ℝ) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) ≤
        Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) := by
      have h4e : (4 : ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
      rw [h4e, ← Real.exp_add, Real.exp_le_exp]
      have : Real.log 4 ≤ (c / 2) * Real.log (Real.log (N : ℝ)) ^ A := by
        have := mul_le_mul_of_nonneg_left hll4 (half_pos hc).le
        have heq : (c / 2) * (2 * Real.log 4 / c) = Real.log 4 := by field_simp
        linarith
      linarith
    have hexp_le : Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) ≤
        Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hp4N : (p : ℝ) ≤ 4 * (N : ℝ) := by exact_mod_cast hhi
    rw [← hcard]
    calc (p : ℝ) * Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A)
        ≤ (4 * (N : ℝ)) * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A) :=
          mul_le_mul hp4N hexp_le (Real.exp_pos _).le (by positivity)
      _ = (N : ℝ) * (4 * Real.exp (-c * Real.log (Real.log (N : ℝ)) ^ A)) := by ring
      _ ≤ (N : ℝ) * Real.exp (-(c / 2) * Real.log (Real.log (N : ℝ)) ^ A) :=
          mul_le_mul_of_nonneg_left h4 hN_pos.le
      _ < (r k N : ℝ) := hgt
  have hα_gt : Real.exp (-c * Real.log (Real.log (p : ℝ)) ^ A) < (S.card : ℝ) / (p : ℝ) := by
    rw [lt_div_iff₀ hp_pos]; linarith
  have hdense : (2 : ℝ) ≤ (p : ℝ) * ((S.card : ℝ) / (p : ℝ)) ^ (k - 1) := by
    refine hdense_base.trans ?_
    apply mul_le_mul_of_nonneg_left _ hp_pos.le
    exact pow_le_pow_left₀ (Real.exp_pos _).le hα_gt.le (k - 1)
  have hU := large_u_norm_of_free hk hkp h2 S hfree hdense
  obtain ⟨x, d, hd0, hAP⟩ := hinv S hScard hU
  exact hd0 (hfree x d hAP)

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R1_H1_R1_H2_R2
