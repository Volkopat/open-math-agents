import OMAStatements.S_oeis_a364509
import Mathlib

/-!
# Proof of OEIS A364509 Supercongruence Conjecture

For every `n, k : ℕ`, we prove exact integrality of
`T(n, k) = (2k)! (2nk)! ((n+2)k)! / (k!² (nk)! ((n+1)k)!²)`
via a direct floor inequality independent of `n`, then apply the Kazandzidis unit-product
supercongruence with `2 + 2n + (n + 2) = 2 + n + 2(n + 1) = 3n + 4`.
-/

namespace OeisA364509Proof

open Finset

private def unitProd (p N : ℕ) : ℕ :=
  ∏ j ∈ (Finset.Icc 1 N).filter (fun j => ¬ p ∣ j), j

private lemma unitProd_coprime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    Nat.Coprime (unitProd p N) p := by
  unfold unitProd
  refine Nat.Coprime.prod_left fun j hj => ?_
  have hndvd : ¬ p ∣ j := (mem_filter.mp hj).2
  exact (hp.coprime_iff_not_dvd.mpr hndvd).symm

/-- `(M * p)! = unitProd p (M * p) * p^M * M!`. -/
private lemma factorial_mul_prime (p : ℕ) (hp : 0 < p) (M : ℕ) :
    (M * p).factorial = unitProd p (M * p) * p ^ M * M.factorial := by
  induction M with
  | zero => simp [unitProd]
  | succ M ih =>
    have hstep : ((M + 1) * p).factorial =
        (M * p).factorial * ∏ j ∈ Finset.Ioc (M * p) ((M + 1) * p), j := by
      have h1 : ∀ k : ℕ, (M * p + k).factorial =
          (M * p).factorial * ∏ j ∈ Finset.Ioc (M * p) (M * p + k), j := by
        intro k
        induction k with
        | zero => simp
        | succ k ihk =>
          rw [show M * p + (k + 1) = (M * p + k) + 1 by omega, Nat.factorial_succ, ihk]
          have hIoc : Finset.Ioc (M * p) (M * p + k + 1) =
              insert (M * p + k + 1) (Finset.Ioc (M * p) (M * p + k)) := by
            ext x; simp only [mem_Ioc, mem_insert]; omega
          have hnm : M * p + k + 1 ∉ Finset.Ioc (M * p) (M * p + k) := by
            simp only [mem_Ioc]; omega
          rw [hIoc, prod_insert hnm]; ring
      simpa [add_mul, one_mul] using h1 p
    have hsplit : Finset.Ioc (M * p) ((M + 1) * p) =
        insert ((M + 1) * p) ((Finset.Ioc (M * p) ((M + 1) * p)).filter (fun j => ¬ p ∣ j)) := by
      ext j
      simp only [mem_Ioc, mem_insert, mem_filter]
      constructor
      · intro ⟨h1, h2⟩
        by_cases hd : p ∣ j
        · left
          rcases hd with ⟨k, rfl⟩
          have hk1 : M < k := by nlinarith
          have hk2 : k ≤ M + 1 := by nlinarith
          have : k = M + 1 := by omega
          rw [this, mul_comm]
        · right; exact ⟨⟨h1, h2⟩, hd⟩
      · rintro (rfl | ⟨⟨h1, h2⟩, _⟩)
        · exact ⟨by nlinarith, le_rfl⟩
        · exact ⟨h1, h2⟩
    have hnm : (M + 1) * p ∉ (Finset.Ioc (M * p) ((M + 1) * p)).filter (fun j => ¬ p ∣ j) := by
      simp only [mem_filter, not_and, not_not]; intro _; exact dvd_mul_left p (M + 1)
    have hU : unitProd p ((M + 1) * p) =
        unitProd p (M * p) * ∏ j ∈ (Finset.Ioc (M * p) ((M + 1) * p)).filter (fun j => ¬ p ∣ j), j := by
      unfold unitProd
      have hunion : (Finset.Icc 1 ((M + 1) * p)).filter (fun j => ¬ p ∣ j) =
          (Finset.Icc 1 (M * p)).filter (fun j => ¬ p ∣ j) ∪
          (Finset.Ioc (M * p) ((M + 1) * p)).filter (fun j => ¬ p ∣ j) := by
        have hle : M * p ≤ (M + 1) * p := Nat.mul_le_mul_right p (Nat.le_succ M)
        ext j; simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]; omega
      have hdisj : Disjoint ((Finset.Icc 1 (M * p)).filter (fun j => ¬ p ∣ j))
          ((Finset.Ioc (M * p) ((M + 1) * p)).filter (fun j => ¬ p ∣ j)) := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2; omega
      rw [hunion, prod_union hdisj]
    rw [hstep, hsplit, prod_insert hnm, ih, hU, pow_succ, Nat.factorial_succ]
    ring

/-- First-order expansion of `∏ (a i + d i)` when every product `d i * d j = 0`. -/
private lemma prod_add_of_mul_eq_zero {ι R : Type*} [DecidableEq ι] [CommRing R]
    (s : Finset ι) (a d : ι → R) (hd : ∀ i j, d i * d j = 0) :
    ∏ i ∈ s, (a i + d i) = (∏ i ∈ s, a i) + ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [prod_insert hx, ih, prod_insert hx, sum_insert hx, erase_insert hx]
    have hcross : d x * ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j = 0 := by
      rw [mul_sum]
      exact sum_eq_zero fun i _ => by rw [← mul_assoc, hd x i, zero_mul]
    have hsum : a x * ∑ i ∈ s, d i * ∏ j ∈ s.erase i, a j =
        ∑ i ∈ s, d i * ∏ j ∈ (insert x s).erase i, a j := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hne : x ≠ i := fun h => hx (h ▸ hi)
      have her : (insert x s).erase i = insert x (s.erase i) := erase_insert_of_ne hne
      have hnx : x ∉ s.erase i := fun h => hx (mem_of_mem_erase h)
      rw [her, prod_insert hnx]; ring
    linear_combination hcross + hsum

/-- Sum of `j⁻²` over units mod `p^r` vanishes in `ZMod (p^r)` for prime `p ≥ 5`. -/
private lemma sum_inv_sq_units_eq_zero {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) :
    let Q := p ^ r
    ∑ j ∈ (Finset.Icc 1 Q).filter (fun j => ¬ p ∣ j), ((j : ZMod Q) ^ 2)⁻¹ = 0 := by
  intro Q
  have hQ_pos : 0 < Q := by positivity
  have : NeZero Q := ⟨by omega⟩
  set S := (Finset.Icc 1 Q).filter (fun j => ¬ p ∣ j)
  have h2cop : Nat.Coprime 2 Q := (hp.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by decide) h; omega)).symm.pow_right r
  have h3cop : Nat.Coprime 3 Q := (hp.coprime_iff_not_dvd.mpr (by
    intro h; have := Nat.le_of_dvd (by decide) h; omega)).symm.pow_right r
  have h2u : IsUnit (2 : ZMod Q) := (ZMod.isUnit_iff_coprime 2 Q).mpr h2cop
  have h3u : IsUnit (3 : ZMod Q) := (ZMod.isUnit_iff_coprime 3 Q).mpr h3cop
  -- Multiplication by `2` permutes `S` modulo `Q`
  let f : ℕ → ℕ := fun j => (2 * j) % Q
  have hf_mem : ∀ j ∈ S, f j ∈ S := by
    intro j hj
    have hndvd : ¬ p ∣ j := (mem_filter.mp hj).2
    have hndvd2j : ¬ p ∣ 2 * j := by
      intro h; rcases hp.dvd_mul.mp h with h2 | hj'
      · have := Nat.le_of_dvd (by decide) h2; omega
      · exact hndvd hj'
    have hpQ : p ∣ Q := dvd_pow_self p (by omega)
    have hndvdf : ¬ p ∣ f j := by
      intro h
      have : p ∣ 2 * j := by
        have hdiv := Nat.div_add_mod (2 * j) Q
        have h1 : p ∣ Q * (2 * j / Q) := dvd_mul_of_dvd_left hpQ _
        have h2 : p ∣ Q * (2 * j / Q) + f j := dvd_add h1 h
        rwa [hdiv] at h2
      exact hndvd2j this
    have hf_pos : 1 ≤ f j := by
      by_contra h0
      have hfz : f j = 0 := by omega
      exact hndvdf (hfz ▸ dvd_zero p)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hf_pos, (Nat.mod_lt _ hQ_pos).le⟩, hndvdf⟩
  have hf_inj : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb hab
    have hmod : ((2 : ZMod Q) * (a : ZMod Q)) = ((2 : ZMod Q) * (b : ZMod Q)) := by
      dsimp only [f] at hab
      have h1 : ((2 * a % Q : ℕ) : ZMod Q) = ((2 * b % Q : ℕ) : ZMod Q) := by rw [hab]
      simpa only [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat] using h1
    have hab_z : (a : ZMod Q) = (b : ZMod Q) := h2u.mul_left_cancel hmod
    have ha_le : a < Q := by
      have ha1 := (mem_Icc.mp (mem_filter.mp ha).1).2
      have hna := (mem_filter.mp ha).2
      have hne : a ≠ Q := fun h => hna (h ▸ dvd_pow_self p (by omega))
      omega
    have hb_le : b < Q := by
      have hb1 := (mem_Icc.mp (mem_filter.mp hb).1).2
      have hnb := (mem_filter.mp hb).2
      have hne : b ≠ Q := fun h => hnb (h ▸ dvd_pow_self p (by omega))
      omega
    have ha_val : (a : ZMod Q).val = a := ZMod.val_natCast_of_lt ha_le
    have hb_val : (b : ZMod Q).val = b := ZMod.val_natCast_of_lt hb_le
    rw [← ha_val, ← hb_val, hab_z]
  have hf_img : S.image f = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hf_mem)
      (by rw [Finset.card_image_of_injOn hf_inj])
  set T : ZMod Q := ∑ j ∈ S, ((j : ZMod Q) ^ 2)⁻¹
  have hT_eq : T = ∑ j ∈ S, ((f j : ZMod Q) ^ 2)⁻¹ := by
    dsimp only [T]
    conv_lhs => rw [← hf_img]
    exact Finset.sum_image hf_inj
  have h4T : (4 : ZMod Q) * T = T := by
    conv_lhs => rw [hT_eq]
    rw [Finset.mul_sum]
    dsimp only [T]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hfj : (f j : ZMod Q) = 2 * (j : ZMod Q) := by
      simp only [f, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_ofNat]
    rw [hfj]
    have hju : IsUnit ((j : ZMod Q) ^ 2) :=
      ((ZMod.isUnit_iff_coprime j Q).mpr
        ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2).symm.pow_right r)).pow 2
    have h4u : IsUnit (4 : ZMod Q) := by
      have : (4 : ZMod Q) = 2 * 2 := by norm_num
      rw [this]; exact h2u.mul h2u
    have hsq : (2 * (j : ZMod Q)) ^ 2 = 4 * (j : ZMod Q) ^ 2 := by ring
    rw [hsq]
    have h1 : (4 * (j : ZMod Q) ^ 2) * (4 * (j : ZMod Q) ^ 2)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ (h4u.mul hju)
    have h2 : (j : ZMod Q) ^ 2 * ((j : ZMod Q) ^ 2)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit _ hju
    linear_combination ((j : ZMod Q) ^ 2)⁻¹ * h1 - 4 * (4 * (j : ZMod Q) ^ 2)⁻¹ * h2
  have h3T : (3 : ZMod Q) * T = 0 := by linear_combination h4T
  exact h3u.mul_left_cancel (by rw [h3T, mul_zero])

/-- Single-block congruence: `∏_{1 ≤ j ≤ Q, ¬ p ∣ j} (t * Q + j) ≡ unitProd p Q [MOD Q^3]`. -/
private lemma block_prod_congr {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (t : ℕ) :
    let Q := p ^ r
    (∏ j ∈ (Finset.Icc 1 Q).filter (fun j => ¬ p ∣ j), (t * Q + j)) ≡
      unitProd p Q [MOD Q ^ 3] := by
  intro Q
  have hQ_pos : 0 < Q := by positivity
  have : NeZero (Q ^ 3) := ⟨by positivity⟩
  have : NeZero Q := ⟨by omega⟩
  set S := (Finset.Icc 1 Q).filter (fun j => ¬ p ∣ j)
  set B := ∏ j ∈ S, (t * Q + j)
  set U := unitProd p Q
  rw [← ZMod.natCast_eq_natCast_iff]
  -- Symmetry `j ↦ Q - j` on `S`
  let rev : ℕ → ℕ := fun j => Q - j
  have hrev_mem : ∀ j ∈ S, rev j ∈ S := by
    intro j hj
    have hj1 := (mem_Icc.mp (mem_filter.mp hj).1).1
    have hj2 := (mem_Icc.mp (mem_filter.mp hj).1).2
    have hndvd := (mem_filter.mp hj).2
    have hpQ : p ∣ Q := dvd_pow_self p (by omega)
    have hjlt : j < Q := lt_of_le_of_ne hj2 (fun h => hndvd (h ▸ hpQ))
    have hndvd' : ¬ p ∣ Q - j := by
      intro h
      have h1 : p ∣ Q - j + j := by rwa [Nat.sub_add_cancel hj2]
      exact hndvd ((Nat.dvd_add_right h).mp h1)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp only [rev]; omega, by dsimp only [rev]; omega⟩, hndvd'⟩
  have hrev_inj : Set.InjOn rev (S : Set ℕ) := by
    intro a ha b hb hab
    have ha2 := (mem_Icc.mp (mem_filter.mp ha).1).2
    have hb2 := (mem_Icc.mp (mem_filter.mp hb).1).2
    dsimp only [rev] at hab; omega
  have hrev_img : S.image rev = S :=
    Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hrev_mem)
      (by rw [Finset.card_image_of_injOn hrev_inj])
  -- Compute `B^2` in `ZMod (Q^3)` using `j ↦ Q - j`
  have hB_sq : ((B : ZMod (Q ^ 3)) ^ 2) =
      ∏ j ∈ S, (((j : ZMod (Q ^ 3)) * ((Q - j : ℕ) : ZMod (Q ^ 3))) +
        ((t * (t + 1) : ℕ) : ZMod (Q ^ 3)) * (Q : ZMod (Q ^ 3)) ^ 2) := by
    rw [sq]
    have hB1 : (B : ZMod (Q ^ 3)) = ∏ j ∈ S, ((t * Q + j : ℕ) : ZMod (Q ^ 3)) := by
      simp [B]
    have hB2 : (B : ZMod (Q ^ 3)) = ∏ j ∈ S, ((t * Q + (Q - j) : ℕ) : ZMod (Q ^ 3)) := by
      rw [hB1]; conv_lhs => rw [← hrev_img]
      exact Finset.prod_image hrev_inj
    conv_lhs => arg 1; rw [hB1]
    conv_lhs => arg 2; rw [hB2]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj2 : j ≤ Q := (mem_Icc.mp (mem_filter.mp hj).1).2
    have hcast : ((Q - j : ℕ) : ZMod (Q ^ 3)) = (Q : ZMod (Q ^ 3)) - (j : ZMod (Q ^ 3)) :=
      Nat.cast_sub hj2
    push_cast
    rw [hcast]; ring
  -- Expand `hB_sq` to first order since `(Q^2)^2 = Q^4 = 0` in `ZMod (Q^3)`
  have hQ4 : (Q : ZMod (Q ^ 3)) ^ 2 * (Q : ZMod (Q ^ 3)) ^ 2 = 0 := by
    have : (Q : ZMod (Q ^ 3)) ^ 2 * (Q : ZMod (Q ^ 3)) ^ 2 = ((Q ^ 3 * Q : ℕ) : ZMod (Q ^ 3)) := by
      push_cast; ring
    rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [prod_add_of_mul_eq_zero S
        (fun j => (j : ZMod (Q ^ 3)) * ((Q - j : ℕ) : ZMod (Q ^ 3)))
        (fun _ => ((t * (t + 1) : ℕ) : ZMod (Q ^ 3)) * (Q : ZMod (Q ^ 3)) ^ 2)
        (fun _ _ => by linear_combination ((t * (t + 1) : ℕ) : ZMod (Q ^ 3)) ^ 2 * hQ4)] at hB_sq
  have hprod_U2 : (∏ j ∈ S, (j : ZMod (Q ^ 3)) * ((Q - j : ℕ) : ZMod (Q ^ 3))) =
      (U : ZMod (Q ^ 3)) ^ 2 := by
    rw [Finset.prod_mul_distrib, sq]
    have hU1 : (U : ZMod (Q ^ 3)) = ∏ j ∈ S, (j : ZMod (Q ^ 3)) := by simp [U, unitProd, S]
    have hU2 : (U : ZMod (Q ^ 3)) = ∏ j ∈ S, ((Q - j : ℕ) : ZMod (Q ^ 3)) := by
      rw [hU1]; conv_lhs => rw [← hrev_img]
      exact Finset.prod_image hrev_inj
    rw [← hU1, ← hU2]
  -- Show the first-order correction vanishes in `ZMod (Q^3)`
  have hcorr_zero : ∑ j ∈ S,
      (((t * (t + 1) : ℕ) : ZMod (Q ^ 3)) * (Q : ZMod (Q ^ 3)) ^ 2) *
        ∏ i ∈ S.erase j, (i : ZMod (Q ^ 3)) * ((Q - i : ℕ) : ZMod (Q ^ 3)) = 0 := by
    rw [← Finset.mul_sum]
    suffices hsum0 : (Q : ZMod (Q ^ 3)) ^ 2 *
        ∑ j ∈ S, ∏ i ∈ S.erase j, (i : ZMod (Q ^ 3)) * ((Q - i : ℕ) : ZMod (Q ^ 3)) = 0 by
      linear_combination ((t * (t + 1) : ℕ) : ZMod (Q ^ 3)) * hsum0
    -- It suffices to show `∑ j ∈ S, ∏ i ∈ S.erase j, i * (Q - i) = 0` in `ZMod Q`!
    set M : ℕ := ∑ j ∈ S, ∏ i ∈ S.erase j, i * (Q - i)
    have hM_cast : (∑ j ∈ S, ∏ i ∈ S.erase j,
        (i : ZMod (Q ^ 3)) * ((Q - i : ℕ) : ZMod (Q ^ 3))) = (M : ZMod (Q ^ 3)) := by
      simp [M]
    rw [hM_cast]
    have hQ_dvd_M : Q ∣ M := by
      rw [← ZMod.natCast_eq_zero_iff]
      have hM_Q : (M : ZMod Q) =
          ∑ j ∈ S, ∏ i ∈ S.erase j, (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q) := by
        simp [M]
      rw [hM_Q]
      have hU2_Q : (U : ZMod Q) ^ 2 = ∏ i ∈ S, (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q) := by
        rw [Finset.prod_mul_distrib, sq]
        have h1 : (U : ZMod Q) = ∏ i ∈ S, (i : ZMod Q) := by simp [U, unitProd, S]
        have h2 : (U : ZMod Q) = ∏ i ∈ S, ((Q - i : ℕ) : ZMod Q) := by
          rw [h1]; conv_lhs => rw [← hrev_img]; exact Finset.prod_image hrev_inj
        rw [← h1, ← h2]
      have hterm : ∀ j ∈ S,
          (∏ i ∈ S.erase j, (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q)) =
          -((U : ZMod Q) ^ 2) * ((j : ZMod Q) ^ 2)⁻¹ := by
        intro j hj
        have hj2 : j ≤ Q := (mem_Icc.mp (mem_filter.mp hj).1).2
        have hqj : ((Q - j : ℕ) : ZMod Q) = -(j : ZMod Q) := by
          rw [Nat.cast_sub hj2, ZMod.natCast_self, zero_sub]
        have hju : IsUnit ((j : ZMod Q) ^ 2) :=
          ((ZMod.isUnit_iff_coprime j Q).mpr
            ((hp.coprime_iff_not_dvd.mpr (mem_filter.mp hj).2).symm.pow_right r)).pow 2
        have hmul : ((j : ZMod Q) * ((Q - j : ℕ) : ZMod Q)) *
            (∏ i ∈ S.erase j, (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q)) = (U : ZMod Q) ^ 2 := by
          rw [hU2_Q, Finset.mul_prod_erase S (fun i => (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q)) hj]
        rw [hqj] at hmul
        have hmul' : (j : ZMod Q) ^ 2 *
            (∏ i ∈ S.erase j, (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q)) = -((U : ZMod Q) ^ 2) := by
          linear_combination -hmul
        have hinv : (j : ZMod Q) ^ 2 * ((j : ZMod Q) ^ 2)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hju
        linear_combination ((j : ZMod Q) ^ 2)⁻¹ * hmul' -
          (∏ i ∈ S.erase j, (i : ZMod Q) * ((Q - i : ℕ) : ZMod Q)) * hinv
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
          sum_inv_sq_units_eq_zero hp hp5 hr, mul_zero]
    rcases hQ_dvd_M with ⟨k, hk⟩
    rw [hk]
    have : (Q : ZMod (Q ^ 3)) ^ 2 * ((Q * k : ℕ) : ZMod (Q ^ 3)) =
        ((Q ^ 3 : ℕ) : ZMod (Q ^ 3)) * (k : ZMod (Q ^ 3)) := by
      push_cast; ring
    rw [this, ZMod.natCast_self, zero_mul]
  rw [hprod_U2, hcorr_zero, add_zero] at hB_sq
  -- Cancel the unit `B + U` from `(B - U) * (B + U) = 0`
  have hB_mod_p : B ≡ U [MOD p] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hpQ : p ∣ Q := dvd_pow_self p (by omega)
    have hQ0 : (Q : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff Q p).mpr hpQ
    simp only [B, U, unitProd, S, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; rw [hQ0, mul_zero, zero_add]
  have hBU_cop : Nat.Coprime (B + U) (Q ^ 3) := by
    apply Nat.Coprime.pow_right 3
    dsimp only [Q]
    apply Nat.Coprime.pow_right r
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    have h0 : ((B + U : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
    have hBU_p : (B : ZMod p) = (U : ZMod p) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hB_mod_p
    have h2U : (2 : ZMod p) * (U : ZMod p) = 0 := by
      push_cast at h0; linear_combination h0 - hBU_p
    have hp2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide) h; omega
    have h2u : IsUnit (2 : ZMod p) := (ZMod.isUnit_iff_coprime 2 p).mpr
      (hp.coprime_iff_not_dvd.mpr hp2).symm
    have hU0 : (U : ZMod p) = 0 := h2u.mul_left_cancel (by rw [h2U, mul_zero])
    have hpU : p ∣ U := (ZMod.natCast_eq_zero_iff U p).mp hU0
    exact (hp.coprime_iff_not_dvd.mp (unitProd_coprime hp Q).symm) hpU
  have hBU_u : IsUnit ((B : ZMod (Q ^ 3)) + (U : ZMod (Q ^ 3))) := by
    rw [← Nat.cast_add]; exact (ZMod.isUnit_iff_coprime _ _).mpr hBU_cop
  have hdiff : ((B : ZMod (Q ^ 3)) + (U : ZMod (Q ^ 3))) *
      ((B : ZMod (Q ^ 3)) - (U : ZMod (Q ^ 3))) = 0 := by
    linear_combination hB_sq
  have hsub0 : (B : ZMod (Q ^ 3)) - (U : ZMod (Q ^ 3)) = 0 :=
    hBU_u.mul_left_cancel (by rw [hdiff, mul_zero])
  exact sub_eq_zero.mp hsub0

/-- Universal unit-product supercongruence: `unitProd p (m * p^r) ≡ (unitProd p (p^r))^m [MOD p^(3*r)]`. -/
private lemma unitProd_mul_pow_congr {p r : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hr : 1 ≤ r) (m : ℕ) :
    unitProd p (m * p ^ r) ≡ (unitProd p (p ^ r)) ^ m [MOD p ^ (3 * r)] := by
  have hQ3 : p ^ (3 * r) = (p ^ r) ^ 3 := by rw [← pow_mul, mul_comm]
  rw [hQ3]
  set Q := p ^ r
  induction m with
  | zero => simp [unitProd]; exact Nat.ModEq.refl 1
  | succ m ih =>
    have hsplit : unitProd p ((m + 1) * Q) =
        unitProd p (m * Q) * ∏ j ∈ (Finset.Icc 1 Q).filter (fun j => ¬ p ∣ j), (m * Q + j) := by
      unfold unitProd
      have hmQ_le : m * Q ≤ (m + 1) * Q := Nat.mul_le_mul_right Q (Nat.le_succ m)
      have hunion : (Finset.Icc 1 ((m + 1) * Q)).filter (fun j => ¬ p ∣ j) =
          (Finset.Icc 1 (m * Q)).filter (fun j => ¬ p ∣ j) ∪
          (Finset.Ioc (m * Q) ((m + 1) * Q)).filter (fun j => ¬ p ∣ j) := by
        ext j; simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]; omega
      have hdisj : Disjoint ((Finset.Icc 1 (m * Q)).filter (fun j => ¬ p ∣ j))
          ((Finset.Ioc (m * Q) ((m + 1) * Q)).filter (fun j => ¬ p ∣ j)) := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2; omega
      rw [hunion, prod_union hdisj]
      congr 1
      have hpQ : p ∣ Q := dvd_pow_self p (by omega)
      have himg : ((Finset.Icc 1 Q).filter (fun j => ¬ p ∣ j)).image (fun j => m * Q + j) =
          (Finset.Ioc (m * Q) ((m + 1) * Q)).filter (fun j => ¬ p ∣ j) := by
        ext x
        simp only [mem_image, mem_filter, mem_Icc, mem_Ioc]
        have hmQ_add : (m + 1) * Q = m * Q + Q := by ring
        constructor
        · rintro ⟨j, ⟨⟨h1, h2⟩, hndvd⟩, rfl⟩
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          intro hd
          have hmQ : p ∣ m * Q := dvd_mul_of_dvd_right hpQ m
          exact hndvd ((Nat.dvd_add_right hmQ).mp hd)
        · rintro ⟨⟨h1, h2⟩, hndvd⟩
          refine ⟨x - m * Q, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
          intro hd
          have hmQ : p ∣ m * Q := dvd_mul_of_dvd_right hpQ m
          have : p ∣ m * Q + (x - m * Q) := dvd_add hmQ hd
          exact hndvd (by rwa [Nat.add_sub_cancel' (by omega)] at this)
      rw [← himg, prod_image (fun a _ b _ h => by omega)]
    rw [hsplit, pow_succ]
    exact ih.mul (block_prod_congr hp hp5 hr m)



private lemma div_mul_eq_of_dvd {a L b r d : ℕ} (hL : L = a * b) (ha : 0 < a) (hb : 0 < b) :
    (a * r) / d = (a * ((L * r) / d)) / L := by
  have h1 : (a * r) / d = (a * r * b) / (d * b) := (Nat.mul_div_mul_right (a * r) d hb).symm
  have h2 : a * r * b = L * r := by rw [hL]; ring
  have h3 : (L * r) / (d * b) = ((L * r) / d) / b := (Nat.div_div_eq_div_mul (L * r) d b).symm
  have h4 : ((L * r) / d) / b = (a * ((L * r) / d)) / (a * b) := (Nat.mul_div_mul_left _ _ ha).symm
  rw [h1, h2, h3, h4, ← hL]

private lemma padic_factorial_eq {q K m : ℕ} (hq : q.Prime) (hK_pos : 0 < K) (hK : m < q ^ K) :
    m.factorial.factorization q = ∑ i ∈ Finset.Ico 1 K, m / q ^ i := by
  have : Fact q.Prime := ⟨hq⟩
  rw [Nat.factorization_def _ hq]
  have hlog : Nat.log q m < K := by
    by_cases hm0 : m = 0
    · subst hm0; simpa using hK_pos
    · exact Nat.log_lt_of_lt_pow hm0 hK
  exact padicValNat_factorial hlog

private lemma mul_div_mod_decomp (a n d : ℕ) (hd : 0 < d) :
    (a * n) / d = a * (n / d) + (a * (n % d)) / d := by
  have h := Nat.div_add_mod n d
  have h1 : a * n = d * (a * (n / d)) + a * (n % d) := by
    calc a * n = a * (d * (n / d) + n % d) := by rw [h]
      _ = d * (a * (n / d)) + a * (n % d) := by ring
  rw [h1, Nat.mul_add_div hd]




private lemma add_div_mod_decomp (a b d : ℕ) (hd : 0 < d) :
    (a + b) / d = a / d + b / d + (a % d + b % d) / d := by
  have ha := Nat.div_add_mod a d
  have hb := Nat.div_add_mod b d
  have hab : a + b = d * (a / d + b / d) + (a % d + b % d) := by linarith
  rw [hab, Nat.mul_add_div hd]

private lemma floor_ineq_T (n k d : ℕ) (hd : 0 < d) :
    2 * (k / d) + (n * k) / d + 2 * (((n + 1) * k) / d) ≤
      (2 * k) / d + (2 * n * k) / d + ((n + 2) * k) / d := by
  have h2k : (2 * k) / d = 2 * (k / d) + (2 * (k % d)) / d := mul_div_mod_decomp 2 k d hd
  have h2nk : (2 * n * k) / d = 2 * ((n * k) / d) + (2 * ((n * k) % d)) / d := by
    rw [show 2 * n * k = 2 * (n * k) by ring]
    exact mul_div_mod_decomp 2 (n * k) d hd
  have hn1 : ((n + 1) * k) / d = (n * k) / d + k / d + ((n * k) % d + k % d) / d := by
    rw [show (n + 1) * k = n * k + k by ring]
    exact add_div_mod_decomp (n * k) k d hd
  have hn2 : ((n + 2) * k) / d = (n * k) / d + 2 * (k / d) + ((n * k) % d + 2 * (k % d)) / d := by
    have ha := Nat.div_add_mod (n * k) d
    have hb := Nat.div_add_mod k d
    have hsplit : (n + 2) * k = d * ((n * k) / d + 2 * (k / d)) + ((n * k) % d + 2 * (k % d)) := by
      have : (n + 2) * k = n * k + 2 * k := by ring
      linarith
    rw [hsplit, Nat.mul_add_div hd]
  rw [h2k, h2nk, hn1, hn2]
  set rk := k % d
  set rn := (n * k) % d
  have hrk : rk < d := Nat.mod_lt k hd
  have hrn : rn < d := Nat.mod_lt (n * k) hd
  have hrem : 2 * ((rn + rk) / d) ≤ (2 * rk) / d + (2 * rn) / d + (rn + 2 * rk) / d := by
    by_cases hsum : rn + rk < d
    · rw [Nat.div_eq_of_lt hsum]; exact Nat.zero_le _
    · have h1 : (rn + rk) / d = 1 := by
        apply Nat.div_eq_of_lt_le <;> omega
      have h2 : 1 ≤ (rn + 2 * rk) / d := by
        rw [Nat.le_div_iff_mul_le hd]; omega
      have h3 : 1 ≤ (2 * rk) / d ∨ 1 ≤ (2 * rn) / d := by
        by_cases h : d ≤ 2 * rk
        · left; rw [Nat.le_div_iff_mul_le hd]; omega
        · right; rw [Nat.le_div_iff_mul_le hd]; omega
      rw [h1]
      rcases h3 with h3a | h3b
      · exact le_trans (by decide : 2 * 1 ≤ 1 + 0 + 1)
          (Nat.add_le_add (Nat.add_le_add h3a (Nat.zero_le _)) h2)
      · exact le_trans (by decide : 2 * 1 ≤ 0 + 1 + 1)
          (Nat.add_le_add (Nat.add_le_add (Nat.zero_le _) h3b) h2)
  omega

private lemma T_dvd (n k : ℕ) :
    (k.factorial ^ 2 * (n * k).factorial * ((n + 1) * k).factorial ^ 2) ∣
      ((2 * k).factorial * (2 * n * k).factorial * ((n + 2) * k).factorial) := by
  have hpos1 : k.factorial ^ 2 * (n * k).factorial * ((n + 1) * k).factorial ^ 2 ≠ 0 := by positivity
  have hpos2 : (2 * k).factorial * (2 * n * k).factorial * ((n + 2) * k).factorial ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hpos1 hpos2]
  intro q
  by_cases hq : q.Prime
  · set K := (2 * n + 2) * k + 2
    have hpow : ∀ m ≤ (2 * n + 2) * k, m < q ^ K := fun m hm =>
      lt_of_le_of_lt hm (lt_of_lt_of_le (by omega : (2 * n + 2) * k < K)
        (Nat.le_of_lt (Nat.lt_pow_self hq.one_lt)))
    simp only [Nat.factorization_mul, Nat.factorization_pow, ne_eq,
               Nat.factorial_ne_zero, mul_eq_zero, pow_eq_zero_iff',
               not_false_eq_true, or_self, false_and,
               Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [padic_factorial_eq hq (by omega) (hpow k (by nlinarith)),
        padic_factorial_eq hq (by omega) (hpow (n * k) (by nlinarith)),
        padic_factorial_eq hq (by omega) (hpow ((n + 1) * k) (by nlinarith)),
        padic_factorial_eq hq (by omega) (hpow (2 * k) (by nlinarith)),
        padic_factorial_eq hq (by omega) (hpow (2 * n * k) (by nlinarith)),
        padic_factorial_eq hq (by omega) (hpow ((n + 2) * k) (by nlinarith))]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => floor_ineq_T n k (q ^ i) (pow_pos hq.pos i)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hq]

end OeisA364509Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a364509.main := by
  intro n p m r hp hp5 hm hr
  set K := m * p ^ r
  set M := m * p ^ (r - 1)
  have hK_eq : K = M * p := by
    dsimp only [K, M]
    have h : r = (r - 1) + 1 := by omega
    conv_lhs => rw [h]
    rw [pow_succ]; ring
  have hp_pos : 0 < p := hp.pos
  have hmul_K : OMA.S_oeis_a364509.T n K *
      (K.factorial ^ 2 * (n * K).factorial * ((n + 1) * K).factorial ^ 2) =
      (2 * K).factorial * (2 * n * K).factorial * ((n + 2) * K).factorial :=
    Nat.div_mul_cancel (OeisA364509Proof.T_dvd n K)
  have hmul_M : OMA.S_oeis_a364509.T n M *
      (M.factorial ^ 2 * (n * M).factorial * ((n + 1) * M).factorial ^ 2) =
      (2 * M).factorial * (2 * n * M).factorial * ((n + 2) * M).factorial :=
    Nat.div_mul_cancel (OeisA364509Proof.T_dvd n M)
  have hf : ∀ c : ℕ, (c * K).factorial =
      OeisA364509Proof.unitProd p (c * K) * p ^ (c * M) * (c * M).factorial := by
    intro c
    have h := OeisA364509Proof.factorial_mul_prime p hp_pos (c * M)
    rwa [show c * M * p = c * K by rw [hK_eq]; ring] at h
  have hf1 : K.factorial = OeisA364509Proof.unitProd p K * p ^ M * M.factorial := by
    simpa using hf 1
  set U_num := OeisA364509Proof.unitProd p (2 * K) * OeisA364509Proof.unitProd p (2 * n * K) *
      OeisA364509Proof.unitProd p ((n + 2) * K)
  set U_den := OeisA364509Proof.unitProd p K ^ 2 * OeisA364509Proof.unitProd p (n * K) *
      OeisA364509Proof.unitProd p ((n + 1) * K) ^ 2
  have hcancel_pos : 0 < p ^ ((3 * n + 4) * M) *
      (M.factorial ^ 2 * (n * M).factorial * ((n + 1) * M).factorial ^ 2) := by positivity
  have hrel : OMA.S_oeis_a364509.T n K * U_den = OMA.S_oeis_a364509.T n M * U_num := by
    apply Nat.eq_of_mul_eq_mul_right hcancel_pos
    have hp_den : (p ^ M) ^ 2 * p ^ (n * M) * (p ^ ((n + 1) * M)) ^ 2 = p ^ ((3 * n + 4) * M) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    have hp_num : p ^ (2 * M) * p ^ (2 * n * M) * p ^ ((n + 2) * M) = p ^ ((3 * n + 4) * M) := by
      rw [← pow_add, ← pow_add]; congr 1; ring
    calc OMA.S_oeis_a364509.T n K * U_den *
          (p ^ ((3 * n + 4) * M) * (M.factorial ^ 2 * (n * M).factorial * ((n + 1) * M).factorial ^ 2))
        = OMA.S_oeis_a364509.T n K *
            (K.factorial ^ 2 * (n * K).factorial * ((n + 1) * K).factorial ^ 2) := by
            rw [hf1, hf n, hf (n + 1), ← hp_den]; dsimp only [U_den]; ring
      _ = (2 * K).factorial * (2 * n * K).factorial * ((n + 2) * K).factorial := hmul_K
      _ = U_num * p ^ ((3 * n + 4) * M) *
            ((2 * M).factorial * (2 * n * M).factorial * ((n + 2) * M).factorial) := by
            rw [hf 2, hf (2 * n), hf (n + 2), ← hp_num]; dsimp only [U_num]; ring
      _ = OMA.S_oeis_a364509.T n M * U_num *
          (p ^ ((3 * n + 4) * M) * (M.factorial ^ 2 * (n * M).factorial * ((n + 1) * M).factorial ^ 2)) := by
            rw [← hmul_M]; ring
  set u0 := OeisA364509Proof.unitProd p (p ^ r)
  have hc : ∀ c : ℕ, OeisA364509Proof.unitProd p (c * K) ≡ u0 ^ (c * m) [MOD p ^ (3 * r)] := by
    intro c; simpa [K, mul_assoc] using OeisA364509Proof.unitProd_mul_pow_congr hp hp5 hr (c * m)
  have hU_num : U_num ≡ u0 ^ ((3 * n + 4) * m) [MOD p ^ (3 * r)] := by
    have h := ((hc 2).mul (hc (2 * n))).mul (hc (n + 2))
    rwa [← pow_add, ← pow_add, show 2 * m + 2 * n * m + (n + 2) * m = (3 * n + 4) * m by ring] at h
  have hU_den : U_den ≡ u0 ^ ((3 * n + 4) * m) [MOD p ^ (3 * r)] := by
    have hc1 : OeisA364509Proof.unitProd p K ≡ u0 ^ m [MOD p ^ (3 * r)] := by simpa using hc 1
    have h := ((hc1.pow 2).mul (hc n)).mul ((hc (n + 1)).pow 2)
    rwa [← pow_mul, ← pow_mul, ← pow_add, ← pow_add,
         show m * 2 + n * m + (n + 1) * m * 2 = (3 * n + 4) * m by ring] at h
  have hU_eq : U_num ≡ U_den [MOD p ^ (3 * r)] := hU_num.trans hU_den.symm
  have hcop_den : Nat.Coprime U_den (p ^ (3 * r)) := by
    apply Nat.Coprime.pow_right
    exact (((OeisA364509Proof.unitProd_coprime hp K).pow_left 2).mul_left
      (OeisA364509Proof.unitProd_coprime hp (n * K))).mul_left
      ((OeisA364509Proof.unitProd_coprime hp ((n + 1) * K)).pow_left 2)
  have hcongr_mul : OMA.S_oeis_a364509.T n K * U_den ≡ OMA.S_oeis_a364509.T n M * U_den [MOD p ^ (3 * r)] := by
    rw [hrel]; exact Nat.ModEq.mul_left _ hU_eq
  exact Nat.ModEq.cancel_right_of_coprime hcop_den.symm hcongr_mul
