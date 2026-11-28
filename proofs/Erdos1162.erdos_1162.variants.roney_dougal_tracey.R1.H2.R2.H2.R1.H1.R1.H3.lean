import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H1_R1
import Mathlib

-- Step Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R2.H2.R1.H1.R1.H3: hypothesis H3 of reduction Erdos1162.erdos_1162.variants.roney_dougal_tracey.R1.H2.R2.H2.R1.H1.R1
-- Credit: @ignacio-rocco
-- Dixon's exponential order bound for solvable permutation groups: |D| <= 4^n.

namespace DixonBound

open scoped Classical commutatorElement

private lemma pow_three_le_four_pow {p : ℕ} (hp : 1 ≤ p) : p ^ 3 ≤ 4 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rcases (show k = 1 ∨ k = 2 ∨ 3 ≤ k by omega) with rfl | rfl | hk3
    · decide
    · decide
    · have hk2 : 9 ≤ k ^ 2 := by nlinarith
      have hstep : (k + 1) ^ 3 ≤ 4 * k ^ 3 := by nlinarith
      calc (k + 1) ^ 3 ≤ 4 * k ^ 3 := hstep
        _ ≤ 4 * 4 ^ k := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (k + 1) := by rw [pow_succ']

private lemma add_one_le_two_pow (d : ℕ) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => decide
  | succ k ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ']
    omega

private lemma sq_add_le_two_mul_two_pow_sub_one {d : ℕ} (hd : 2 ≤ d) :
    d + d * d ≤ 2 * (2 ^ d - 1) := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : k + 1 ≤ 2 ^ k := add_one_le_two_pow k
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
    have hmul : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    omega

private lemma mul_add_sq_le_three_mul_pow_sub_one {p d : ℕ} (hp : 3 ≤ p) (hd : 2 ≤ d) :
    p * (d + d * d) ≤ 3 * (p ^ d - 1) := by
  induction d, hd using Nat.le_induction with
  | base =>
    have h1 : 1 ≤ p ^ 2 := by nlinarith
    have h2 : 2 * p + 1 ≤ p ^ 2 := by nlinarith
    omega
  | succ k hk ih =>
    have hp1 : 1 ≤ p ^ k := Nat.one_le_pow k p (by omega)
    have hkd : k + 1 ≤ p ^ k :=
      (add_one_le_two_pow k).trans (Nat.pow_le_pow_left (by omega : 2 ≤ p) k)
    have h2p : 2 * p ≤ 3 * (p - 1) := by omega
    have hstep : p * (2 * k + 2) ≤ 3 * (p - 1) * p ^ k := by
      calc p * (2 * k + 2) = (2 * p) * (k + 1) := by ring
        _ ≤ (3 * (p - 1)) * p ^ k := Nat.mul_le_mul h2p hkd
    have hdiff : 3 * (p ^ (k + 1) - 1) = 3 * (p ^ k - 1) + 3 * (p - 1) * p ^ k := by
      zify [hp1, show 1 ≤ p ^ (k + 1) from Nat.one_le_pow _ _ (by omega), show 1 ≤ p by omega]
      rw [pow_succ']
      ring
    have hlhs : p * (k + 1 + (k + 1) * (k + 1)) = p * (k + k * k) + p * (2 * k + 2) := by ring
    omega

private lemma pow_add_sq_le_four_pow_sub_one {p d : ℕ} (hp : 2 ≤ p) (hd : 1 ≤ d) :
    p ^ (d + d * d) ≤ 4 ^ (p ^ d - 1) := by
  rcases eq_or_lt_of_le hd with rfl | hd2
  · have h11 : 1 + 1 * 1 = 2 := rfl
    rw [h11, pow_one]
    induction p, hp using Nat.le_induction with
    | base => decide
    | succ k hk ih =>
      have hstep : (k + 1) ^ 2 ≤ 4 * k ^ 2 := by nlinarith
      have hsub : k + 1 - 1 = (k - 1) + 1 := by omega
      rw [hsub, pow_succ' 4]
      exact hstep.trans (Nat.mul_le_mul_left 4 ih)
  · rcases eq_or_lt_of_le hp with rfl | hp3
    · have hexp : d + d * d ≤ 2 * (2 ^ d - 1) := sq_add_le_two_mul_two_pow_sub_one hd2
      calc 2 ^ (d + d * d) ≤ 2 ^ (2 * (2 ^ d - 1)) := Nat.pow_le_pow_right (by omega) hexp
        _ = (2 ^ 2) ^ (2 ^ d - 1) := by rw [pow_mul]
        _ = 4 ^ (2 ^ d - 1) := by norm_num
    · have hA : p ^ 3 ≤ 4 ^ p := pow_three_le_four_pow (by omega)
      have hB : p * (d + d * d) ≤ 3 * (p ^ d - 1) :=
        mul_add_sq_le_three_mul_pow_sub_one hp3 hd2
      have hcube : (p ^ (d + d * d)) ^ 3 ≤ (4 ^ (p ^ d - 1)) ^ 3 := by
        calc (p ^ (d + d * d)) ^ 3 = (p ^ 3) ^ (d + d * d) := by rw [← pow_mul, mul_comm, pow_mul]
          _ ≤ (4 ^ p) ^ (d + d * d) := Nat.pow_le_pow_left hA _
          _ = 4 ^ (p * (d + d * d)) := by rw [← pow_mul]
          _ ≤ 4 ^ (3 * (p ^ d - 1)) := Nat.pow_le_pow_right (by omega) hB
          _ = (4 ^ (p ^ d - 1)) ^ 3 := by rw [mul_comm, pow_mul]
      by_contra hlt
      push Not at hlt
      have : (4 ^ (p ^ d - 1)) ^ 3 < (p ^ (d + d * d)) ^ 3 :=
        Nat.pow_lt_pow_left hlt (by decide)
      omega

private lemma exists_normal_elem_abelian {G : Type*} [Group G] [Finite G]
    [Group.IsSolvable G] (hG : Nontrivial G) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (N : Subgroup G),
      N.Normal ∧ N ≠ ⊥ ∧ (∀ x y : N, x * y = y * x) ∧ (∀ x : N, x ^ p = 1) := by
  have hex : ∃ m, derivedSeries G m = ⊥ := Group.IsSolvable.solvable
  let m := Nat.find hex
  have hm : derivedSeries G m = ⊥ := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, derivedSeries_zero] at hm
    obtain ⟨x, y, hxy⟩ := hG
    have hx : x = 1 := (Subgroup.mem_bot.mp (hm ▸ Subgroup.mem_top x))
    have hy : y = 1 := (Subgroup.mem_bot.mp (hm ▸ Subgroup.mem_top y))
    exact hxy (hx.trans hy.symm)
  let k := m - 1
  have hkm : k + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)
  let A : Subgroup G := derivedSeries G k
  have hA_ne : A ≠ ⊥ := Nat.find_min hex (show k < m by omega)
  have hA_norm : A.Normal := derivedSeries_normal G k
  have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have hcomm : ⁅x, y⁆ ∈ derivedSeries G (k + 1) := by
      rw [derivedSeries_succ]
      exact Subgroup.commutator_mem_commutator hx hy
    rw [hkm, hm, Subgroup.mem_bot] at hcomm
    rw [commutatorElement_def] at hcomm
    calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
      _ = 1 * (y * x) := by rw [hcomm]
      _ = y * x := one_mul _
  have hA_nontriv : Nontrivial A := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hA_ne
  let _ : Fintype A := Fintype.ofFinite A
  have hcardA : 1 < Fintype.card A := Fintype.one_lt_card
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hcardA)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha_ord⟩ := exists_prime_orderOf_dvd_card (G := A) p hpdvd
  let N : Subgroup G := {
    carrier := {g : G | g ∈ A ∧ g ^ p = 1}
    one_mem' := ⟨A.one_mem, one_pow p⟩
    mul_mem' := fun {x y} hx hy => by
      refine ⟨A.mul_mem hx.1 hy.1, ?_⟩
      rw [(show Commute x y from hA_comm x hx.1 y hy.1).mul_pow, hx.2, hy.2, one_mul]
    inv_mem' := fun {x} hx => ⟨A.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩
  }
  have hN_norm : N.Normal := {
    conj_mem := fun n hn g => by
      refine ⟨hA_norm.conj_mem n hn.1 g, ?_⟩
      rw [conj_pow, hn.2, mul_one, mul_inv_cancel]
  }
  have hN_ne : N ≠ ⊥ := by
    intro hbot
    have haN : (a : G) ∈ N := by
      refine ⟨a.2, ?_⟩
      have h1 : a ^ p = 1 := by rw [← ha_ord, pow_orderOf_eq_one]
      have h2 := congrArg Subtype.val h1
      simpa using h2
    rw [hbot, Subgroup.mem_bot] at haN
    have ha1 : a = 1 := Subtype.ext haN
    rw [ha1, orderOf_one] at ha_ord
    exact hp.ne_one ha_ord.symm
  refine ⟨p, ⟨hp⟩, N, hN_norm, hN_ne, ?_, ?_⟩
  · intro x y
    exact Subtype.ext (hA_comm x.1 x.2.1 y.1 y.2.1)
  · intro x
    exact Subtype.ext x.2.2

private lemma card_solvable_perm_le_four_pow_sub_one :
    ∀ (n : ℕ), 1 ≤ n → ∀ (α : Type*) [Fintype α], Fintype.card α = n →
      ∀ (D : Subgroup (Equiv.Perm α)), Group.IsSolvable D →
        Nat.card D ≤ 4 ^ (n - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn α _ hcard D hsolv
    have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
    rcases eq_or_lt_of_le hn with rfl | hn2
    · have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hle : Nat.card D ≤ Nat.card (Equiv.Perm α) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      have hperm : Nat.card (Equiv.Perm α) = 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcard]; decide
      omega
    let _ : MulAction D α := {
      smul := fun g x => (g : Equiv.Perm α) x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
    }
    by_cases htrans : MulAction.IsPretransitive D α
    · by_cases himprim : ∃ s : Setoid α,
          (∀ (g : D) (x y : α), s.r x y → s.r ((g : Equiv.Perm α) x) ((g : Equiv.Perm α) y)) ∧
          (∃ x y : α, x ≠ y ∧ s.r x y) ∧
          (∃ u v : α, ¬ s.r u v)
      · obtain ⟨s, hs_inv, ⟨x₁, x₂, hxne, hxs⟩, ⟨u₁, u₂, hu_ns⟩⟩ := himprim
        let _ : Setoid α := s
        let Q := Quotient s
        have : Fintype Q := Quotient.fintype s
        let b := Fintype.card Q
        have hb2 : 2 ≤ b := by
          have hneQ : (⟦u₁⟧ : Q) ≠ ⟦u₂⟧ := fun heq => hu_ns (Quotient.exact heq)
          exact Fintype.one_lt_card_iff.mpr ⟨⟦u₁⟧, ⟦u₂⟧, hneQ⟩
        have hpermQ : ∀ g : D, ∀ x y : α, s.r x y → s.r ((g : Equiv.Perm α) x) ((g : Equiv.Perm α) y) :=
          hs_inv
        let actQ (g : D) : Equiv.Perm Q := {
          toFun := Quotient.map' (g : Equiv.Perm α) (hpermQ g)
          invFun := Quotient.map' ((g⁻¹ : D) : Equiv.Perm α) (hpermQ g⁻¹)
          left_inv := fun q => Quotient.inductionOn' q fun x => by
            change ⟦((g⁻¹ : D) : Equiv.Perm α) (((g : Equiv.Perm α) x))⟧ = ⟦x⟧
            have : ((g⁻¹ : D) : Equiv.Perm α) ((g : Equiv.Perm α) x) = x := by
              change ((g⁻¹ * g : D) : Equiv.Perm α) x = x
              simp
            rw [this]
          right_inv := fun q => Quotient.inductionOn' q fun x => by
            change ⟦((g : Equiv.Perm α) (((g⁻¹ : D) : Equiv.Perm α) x))⟧ = ⟦x⟧
            have : ((g : Equiv.Perm α) (((g⁻¹ : D) : Equiv.Perm α) x)) = x := by
              change ((g * g⁻¹ : D) : Equiv.Perm α) x = x
              simp
            rw [this]
        }
        let ψ : D →* Equiv.Perm Q := {
          toFun := actQ
          map_one' := by
            ext q
            exact Quotient.inductionOn' q fun x => rfl
          map_mul' := fun g₁ g₂ => by
            ext q
            exact Quotient.inductionOn' q fun x => rfl
        }
        let B (q : Q) := {x : α // (⟦x⟧ : Q) = q}
        let a := Fintype.card (B ⟦x₁⟧)
        have hB_card : ∀ q : Q, Fintype.card (B q) = a := by
          intro q
          refine Quotient.inductionOn' q fun y => ?_
          obtain ⟨g, hg⟩ := htrans.exists_smul_eq x₁ y
          have hg' : (g : Equiv.Perm α) x₁ = y := hg
          let e : B ⟦x₁⟧ ≃ B ⟦y⟧ := {
            toFun := fun z => ⟨(g : Equiv.Perm α) z.1, by
              have hz : s.r z.1 x₁ := Quotient.exact z.2
              have : s.r ((g : Equiv.Perm α) z.1) y := hg' ▸ hpermQ g z.1 x₁ hz
              exact Quotient.sound this⟩
            invFun := fun z => ⟨((g⁻¹ : D) : Equiv.Perm α) z.1, by
              have hz : s.r z.1 y := Quotient.exact z.2
              have hinv : ((g⁻¹ : D) : Equiv.Perm α) y = x₁ := by
                rw [← hg']
                change ((g⁻¹ * g : D) : Equiv.Perm α) x₁ = x₁
                simp
              have : s.r (((g⁻¹ : D) : Equiv.Perm α) z.1) x₁ := hinv ▸ hpermQ g⁻¹ z.1 y hz
              exact Quotient.sound this⟩
            left_inv := fun z => Subtype.ext (by
              change ((g⁻¹ * g : D) : Equiv.Perm α) z.1 = z.1; simp)
            right_inv := fun z => Subtype.ext (by
              change ((g * g⁻¹ : D) : Equiv.Perm α) z.1 = z.1; simp)
          }
          exact (Fintype.card_congr e).symm
        have ha2 : 2 ≤ a := by
          have hmem1 : (⟦x₁⟧ : Q) = ⟦x₁⟧ := rfl
          have hmem2 : (⟦x₂⟧ : Q) = ⟦x₁⟧ := Quotient.sound (s.symm hxs)
          exact Fintype.one_lt_card_iff.mpr ⟨⟨x₁, hmem1⟩, ⟨x₂, hmem2⟩,
            fun heq => hxne (congrArg Subtype.val heq)⟩
        have hab : b * a = n := by
          have e : α ≃ Σ q : Q, B q := {
            toFun := fun x => ⟨⟦x⟧, ⟨x, rfl⟩⟩
            invFun := fun p => p.2.1
            left_inv := fun _ => rfl
            right_inv := fun ⟨q, ⟨x, hx⟩⟩ => by subst hx; rfl
          }
          have hc := Fintype.card_congr e
          rw [hcard, Fintype.card_sigma] at hc
          simp only [hB_card, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hc
          exact hc.symm
        have ha_lt : a < n := by nlinarith
        have hb_lt : b < n := by nlinarith
        have hsolv_img : Group.IsSolvable ψ.range :=
          Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
        have hcard_img : Nat.card ψ.range ≤ 4 ^ (b - 1) :=
          ih b hb_lt (by omega) Q rfl ψ.range hsolv_img
        let K := ψ.ker
        have hK_mem : ∀ (k : K) (q : Q) (z : B q), (⟦(k.1 : Equiv.Perm α) z.1⟧ : Q) = q := by
          intro k q z
          have hq : (ψ k.1) (⟦z.1⟧ : Q) = ⟦z.1⟧ := by rw [k.2]; rfl
          exact hq.trans z.2
        let res (q : Q) : K →* Equiv.Perm (B q) := {
          toFun := fun k => {
            toFun := fun z => ⟨(k.1 : Equiv.Perm α) z.1, hK_mem k q z⟩
            invFun := fun z => ⟨((k⁻¹).1 : Equiv.Perm α) z.1, hK_mem k⁻¹ q z⟩
            left_inv := fun z => Subtype.ext (by
              change (((k⁻¹ * k : K).1 : D) : Equiv.Perm α) z.1 = z.1; simp)
            right_inv := fun z => Subtype.ext (by
              change (((k * k⁻¹ : K).1 : D) : Equiv.Perm α) z.1 = z.1; simp)
          }
          map_one' := by ext z; rfl
          map_mul' := fun k₁ k₂ => by ext z; rfl
        }
        let emb : K → Π q : Q, (res q).range :=
          fun k q => (res q).rangeRestrict k
        have hemb_inj : Function.Injective emb := by
          intro k₁ k₂ heq
          apply Subtype.ext
          apply Subtype.ext
          ext x
          have hq := congrArg (fun f => (f ⟦x⟧).1 ⟨x, rfl⟩) heq
          exact congrArg Subtype.val hq
        have hcard_K_le : Nat.card K ≤ ∏ q : Q, Nat.card (res q).range := by
          calc Nat.card K ≤ Nat.card (Π q : Q, (res q).range) :=
                Nat.card_le_card_of_injective emb hemb_inj
            _ = ∏ q : Q, Nat.card (res q).range := Nat.card_pi
        have hcard_Kq : ∀ q : Q, Nat.card (res q).range ≤ 4 ^ (a - 1) := by
          intro q
          have hsolv_Kq : Group.IsSolvable (res q).range :=
            Group.isSolvable_of_surjective (res q).rangeRestrict_surjective
          exact ih a ha_lt (by omega) (B q) (hB_card q) (res q).range hsolv_Kq
        have hcard_K : Nat.card K ≤ (4 ^ (a - 1)) ^ b := by
          calc Nat.card K ≤ ∏ q : Q, Nat.card (res q).range := hcard_K_le
            _ ≤ ∏ _q : Q, 4 ^ (a - 1) := Finset.prod_le_prod' fun q _ => hcard_Kq q
            _ = (4 ^ (a - 1)) ^ b := by simp [b]
        have hcard_D : Nat.card D = Nat.card ψ.range * Nat.card K := by
          have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
          have h2 : Nat.card (D ⧸ K) = Nat.card ψ.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
          rw [h2] at h1
          exact h1
        rw [hcard_D]
        calc Nat.card ψ.range * Nat.card K
            ≤ 4 ^ (b - 1) * (4 ^ (a - 1)) ^ b := Nat.mul_le_mul hcard_img hcard_K
          _ = 4 ^ ((b - 1) + (a - 1) * b) := by rw [← pow_mul, ← pow_add]
          _ = 4 ^ (n - 1) := by
            congr 1
            have : (b - 1) + (a - 1) * b = b * a - 1 := by
              zify [show 1 ≤ b by omega, show 1 ≤ a by omega, show 1 ≤ b * a by nlinarith]
              ring
            rw [this, hab]
      · have hprim : ∀ s : Setoid α,
            (∀ (g : D) (x y : α), s.r x y → s.r ((g : Equiv.Perm α) x) ((g : Equiv.Perm α) y)) →
            (∃ x y : α, x ≠ y ∧ s.r x y) →
            ∀ u v : α, s.r u v := by
          intro s hinv hex u v
          by_contra hnuv
          exact himprim ⟨s, hinv, hex, u, v, hnuv⟩
        have hD_nontriv : Nontrivial D := by
          obtain ⟨x₁, x₂, hne⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card α)
          obtain ⟨g, hg⟩ := htrans.exists_smul_eq x₁ x₂
          refine ⟨⟨g, 1, ?_⟩⟩
          intro h1
          rw [h1] at hg
          exact hne hg
        obtain ⟨p, hp_fact, N, hN_norm, hN_ne, hN_comm, hN_pow⟩ :=
          exists_normal_elem_abelian (G := D) hD_nontriv
        have hp : p.Prime := hp_fact.out
        let sN : Setoid α := {
          r := fun x y => ∃ g : N, ((g : D) : Equiv.Perm α) x = y
          iseqv := {
            refl := fun x => ⟨1, rfl⟩
            symm := fun {x y} ⟨g, hg⟩ => ⟨g⁻¹, by
              rw [← hg]
              change (((g⁻¹ * g : N) : D) : Equiv.Perm α) x = x; simp⟩
            trans := fun {x y z} ⟨g₁, h₁⟩ ⟨g₂, h₂⟩ => ⟨g₂ * g₁, by
              change ((g₂ : D) : Equiv.Perm α) (((g₁ : D) : Equiv.Perm α) x) = z
              rw [h₁, h₂]⟩
          }
        }
        have hsN_inv : ∀ (g : D) (x y : α), sN.r x y →
            sN.r ((g : Equiv.Perm α) x) ((g : Equiv.Perm α) y) := by
          intro g x y ⟨a, ha⟩
          refine ⟨⟨g * a.1 * g⁻¹, hN_norm.conj_mem a.1 a.2 g⟩, ?_⟩
          change ((g : Equiv.Perm α) (((a : D) : Equiv.Perm α) (((g⁻¹ : D) : Equiv.Perm α)
            ((g : Equiv.Perm α) x)))) = (g : Equiv.Perm α) y
          have hcancel : (((g⁻¹ : D) : Equiv.Perm α) ((g : Equiv.Perm α) x)) = x := by
            change ((g⁻¹ * g : D) : Equiv.Perm α) x = x; simp
          rw [hcancel, ha]
        have hsN_nondiag : ∃ x y : α, x ≠ y ∧ sN.r x y := by
          have hexN : ∃ g : N, g ≠ 1 := by
            by_contra hall
            push Not at hall
            apply hN_ne
            rw [Subgroup.eq_bot_iff_forall]
            intro g hg
            exact congrArg Subtype.val (hall ⟨g, hg⟩)
          obtain ⟨g, hgne⟩ := hexN
          have hperm_ne : ((g : D) : Equiv.Perm α) ≠ 1 := by
            intro h1
            exact hgne (Subtype.ext (Subtype.ext h1))
          have hex_x : ∃ x : α, ((g : D) : Equiv.Perm α) x ≠ x := by
            by_contra hall
            push Not at hall
            apply hperm_ne
            ext x
            exact hall x
          obtain ⟨x, hx⟩ := hex_x
          exact ⟨x, ((g : D) : Equiv.Perm α) x, hx.symm, g, rfl⟩
        have hN_trans : ∀ x y : α, ∃ g : N, ((g : D) : Equiv.Perm α) x = y :=
          hprim sN hsN_inv hsN_nondiag
        obtain ⟨x₀⟩ := ‹Nonempty α›
        have hN_bij : Function.Bijective (fun g : N => ((g : D) : Equiv.Perm α) x₀) := by
          refine ⟨?_, fun y => hN_trans x₀ y⟩
          intro g₁ g₂ heq
          dsimp only at heq
          let h : N := g₂⁻¹ * g₁
          have hhx₀ : ((h : D) : Equiv.Perm α) x₀ = x₀ := by
            change ((g₂⁻¹ : D) : Equiv.Perm α) (((g₁ : D) : Equiv.Perm α) x₀) = x₀
            rw [heq]
            change (((g₂⁻¹ * g₂ : N) : D) : Equiv.Perm α) x₀ = x₀
            simp
          have hh1 : h = 1 := by
            apply Subtype.ext
            apply Subtype.ext
            ext y
            obtain ⟨k, hk⟩ := hN_trans x₀ y
            rw [← hk]
            change (((h * k : N) : D) : Equiv.Perm α) x₀ = ((k : D) : Equiv.Perm α) x₀
            rw [hN_comm h k]
            change ((k : D) : Equiv.Perm α) (((h : D) : Equiv.Perm α) x₀) =
              ((k : D) : Equiv.Perm α) x₀
            rw [hhx₀]
          exact (eq_of_inv_mul_eq_one hh1).symm
        have hcardN : Nat.card N = n := by
          rw [Nat.card_congr (Equiv.ofBijective _ hN_bij), Nat.card_eq_fintype_card, hcard]
        let _ : CommGroup N := {
          (inferInstance : Group N) with
          mul_comm := hN_comm
        }
        let _ : AddCommGroup (Additive N) := inferInstance
        have hAtors : ∀ x : Additive N, p • x = 0 := fun x => hN_pow (Additive.toMul x)
        let _ : Module (ZMod p) (Additive N) := {
          smul := fun c x => c.val • x
          one_smul := fun x => by
            have h1 : (1 : ZMod p).val = 1 := ZMod.val_one p
            change (1 : ZMod p).val • x = x
            rw [h1, one_nsmul]
          mul_smul := fun c₁ c₂ x => by
            change (c₁ * c₂).val • x = c₁.val • (c₂.val • x)
            rw [ZMod.val_mul, ← mul_nsmul, mul_comm c₂.val c₁.val]
            have hmod : c₁.val * c₂.val = p * (c₁.val * c₂.val / p) + (c₁.val * c₂.val % p) :=
              (Nat.div_add_mod _ _).symm
            conv_rhs => rw [hmod, add_nsmul, mul_comm p, mul_nsmul, hAtors, zero_add]
          smul_zero := fun c => smul_zero c.val
          smul_add := fun c x y => smul_add c.val x y
          add_smul := fun c₁ c₂ x => by
            change (c₁ + c₂).val • x = c₁.val • x + c₂.val • x
            rw [ZMod.val_add, ← add_nsmul]
            have hmod : c₁.val + c₂.val = p * ((c₁.val + c₂.val) / p) + ((c₁.val + c₂.val) % p) :=
              (Nat.div_add_mod _ _).symm
            conv_rhs => rw [hmod, add_nsmul, mul_comm p, mul_nsmul, hAtors, zero_add]
          zero_smul := fun x => by
            change (0 : ZMod p).val • x = 0
            rw [ZMod.val_zero, zero_nsmul]
        }
        let _ : Fintype N := Fintype.ofFinite N
        let _ : Fintype (Additive N) := Fintype.ofFinite (Additive N)
        let d := Module.finrank (ZMod p) (Additive N)
        have hN_pow_d : Nat.card N = p ^ d := by
          have h1 : Fintype.card (Additive N) = (Fintype.card (ZMod p)) ^ d :=
            Module.card_eq_pow_finrank (K := ZMod p) (V := Additive N)
          rw [ZMod.card] at h1
          rw [Nat.card_congr Additive.toMul.symm, Nat.card_eq_fintype_card, h1]
        have hn_eq : n = p ^ d := hcardN.symm.trans hN_pow_d
        have hd1 : 1 ≤ d := by
          by_contra hd0
          have : d = 0 := by omega
          rw [this, pow_zero] at hn_eq
          omega
        let H : Subgroup D := MulAction.stabilizer D x₀
        have hcard_D : Nat.card D = n * Nat.card H := by
          have horb : (MulAction.orbit D x₀) = Set.univ := by
            ext y
            simp only [Set.mem_univ, iff_true, MulAction.mem_orbit_iff]
            exact htrans.exists_smul_eq x₀ y
          have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group D x₀
          have horb_card : Fintype.card (MulAction.orbit D x₀) = n := by
            rw [← hcard]
            exact Fintype.card_congr ((Equiv.setCongr horb).trans (Equiv.Set.univ α))
          rw [horb_card] at h1
          simpa [Nat.card_eq_fintype_card, H] using h1.symm
        let conjLin (h : H) : Additive N →ₗ[ZMod p] Additive N := {
          toFun := fun x =>
            Additive.ofMul ⟨h.1 * (Additive.toMul x).1 * h.1⁻¹,
              hN_norm.conj_mem (Additive.toMul x).1 (Additive.toMul x).2 h.1⟩
          map_add' := fun x y => by
            apply Additive.toMul.injective
            apply Subtype.ext
            change h.1 * ((Additive.toMul x).1 * (Additive.toMul y).1) * h.1⁻¹ =
              (h.1 * (Additive.toMul x).1 * h.1⁻¹) * (h.1 * (Additive.toMul y).1 * h.1⁻¹)
            group
          map_smul' := fun c x => by
            dsimp
            let f : Additive N →+ Additive N := {
              toFun := fun z =>
                Additive.ofMul ⟨h.1 * (Additive.toMul z).1 * h.1⁻¹,
                  hN_norm.conj_mem (Additive.toMul z).1 (Additive.toMul z).2 h.1⟩
              map_zero' := by
                apply Additive.toMul.injective
                apply Subtype.ext
                change h.1 * 1 * h.1⁻¹ = 1
                group
              map_add' := fun a b => by
                apply Additive.toMul.injective
                apply Subtype.ext
                change h.1 * ((Additive.toMul a).1 * (Additive.toMul b).1) * h.1⁻¹ =
                  (h.1 * (Additive.toMul a).1 * h.1⁻¹) * (h.1 * (Additive.toMul b).1 * h.1⁻¹)
                group
            }
            exact f.map_nsmul c.val x
        }
        have hconj_inj : Function.Injective conjLin := by
          intro h₁ h₂ heq
          let h : H := h₂⁻¹ * h₁
          have hcomm : ∀ a : N, h.1 * a.1 = a.1 * h.1 := by
            intro a
            have ha := congrArg (fun L => (Additive.toMul (L (Additive.ofMul a))).1) heq
            dsimp [conjLin] at ha
            calc h.1 * a.1 = h₂.1⁻¹ * (h₁.1 * a.1 * h₁.1⁻¹) * h₁.1 := by
                  change h₂.1⁻¹ * h₁.1 * a.1 = _; group
              _ = h₂.1⁻¹ * (h₂.1 * a.1 * h₂.1⁻¹) * h₁.1 := by rw [ha]
              _ = a.1 * h.1 := by change _ = a.1 * (h₂.1⁻¹ * h₁.1); group
          have hh1 : h = 1 := by
            apply Subtype.ext
            apply Subtype.ext
            ext y
            obtain ⟨a, ha⟩ := hN_trans x₀ y
            rw [← ha]
            have hact : ((h.1 * a.1 : D) : Equiv.Perm α) x₀ =
                ((a.1 * h.1 : D) : Equiv.Perm α) x₀ := by rw [hcomm a]
            have hhx₀ : ((h.1 : D) : Equiv.Perm α) x₀ = x₀ := h.2
            calc ((h.1 : D) : Equiv.Perm α) (((a : D) : Equiv.Perm α) x₀)
                = ((h.1 * a.1 : D) : Equiv.Perm α) x₀ := rfl
              _ = ((a.1 * h.1 : D) : Equiv.Perm α) x₀ := hact
              _ = ((a : D) : Equiv.Perm α) (((h.1 : D) : Equiv.Perm α) x₀) := rfl
              _ = ((a : D) : Equiv.Perm α) x₀ := by rw [hhx₀]
          exact (eq_of_inv_mul_eq_one hh1).symm
        have hfinLin : Finite (Additive N →ₗ[ZMod p] Additive N) :=
          Finite.of_injective DFunLike.coe DFunLike.coe_injective
        let _ : Fintype (Additive N →ₗ[ZMod p] Additive N) := Fintype.ofFinite _
        have hcard_H : Nat.card H ≤ p ^ (d * d) := by
          have hlin : Nat.card (Additive N →ₗ[ZMod p] Additive N) = p ^ (d * d) := by
            have h1 : Fintype.card (Additive N →ₗ[ZMod p] Additive N) =
                (Fintype.card (ZMod p)) ^ Module.finrank (ZMod p) (Additive N →ₗ[ZMod p] Additive N) :=
              Module.card_eq_pow_finrank
            rw [ZMod.card, Module.finrank_linearMap] at h1
            rw [Nat.card_eq_fintype_card, h1]
          rw [← hlin]
          exact Nat.card_le_card_of_injective conjLin hconj_inj
        rw [hcard_D, hn_eq]
        calc p ^ d * Nat.card H ≤ p ^ d * p ^ (d * d) := Nat.mul_le_mul_left _ hcard_H
          _ = p ^ (d + d * d) := by rw [← pow_add]
          _ ≤ 4 ^ (p ^ d - 1) := pow_add_sq_le_four_pow_sub_one hp.two_le hd1
    · obtain ⟨x₀⟩ := ‹Nonempty α›
      let O : Set α := MulAction.orbit D x₀
      have hO_ne : O.Nonempty := ⟨x₀, MulAction.mem_orbit_self x₀⟩
      have hOc_ne : Oᶜ.Nonempty := by
        by_contra h
        rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
        apply htrans
        refine ⟨fun x y => ?_⟩
        have hx : x ∈ O := h ▸ Set.mem_univ x
        have hy : y ∈ O := h ▸ Set.mem_univ y
        obtain ⟨g₁, hg₁⟩ := hx
        obtain ⟨g₂, hg₂⟩ := hy
        dsimp only at hg₁ hg₂
        refine ⟨g₂ * g₁⁻¹, ?_⟩
        rw [mul_smul, ← hg₁, inv_smul_smul, hg₂]
      let α₁ := {x : α // x ∈ O}
      let α₂ := {x : α // x ∉ O}
      have h1_pos : 1 ≤ Fintype.card α₁ := Fintype.card_pos_iff.mpr ⟨⟨x₀, MulAction.mem_orbit_self x₀⟩⟩
      obtain ⟨y₀, hy₀⟩ := hOc_ne
      have h2_pos : 1 ≤ Fintype.card α₂ := Fintype.card_pos_iff.mpr ⟨⟨y₀, hy₀⟩⟩
      have hsum : Fintype.card α₁ + Fintype.card α₂ = n := by
        have e : α ≃ α₁ ⊕ α₂ := {
          toFun := fun x => if hx : x ∈ O then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, hx⟩
          invFun := Sum.elim Subtype.val Subtype.val
          left_inv := fun x => by by_cases hx : x ∈ O <;> simp [hx]
          right_inv := fun s => by
            cases s with
            | inl z => simp [z.2]
            | inr z => simp [z.2]
        }
        rw [← hcard, Fintype.card_congr e, Fintype.card_sum]
      have h1_lt : Fintype.card α₁ < n := by omega
      have h2_lt : Fintype.card α₂ < n := by omega
      have hO_inv : ∀ (g : D) (x : α), x ∈ O → ((g : Equiv.Perm α) x) ∈ O := by
        intro g x ⟨h, hh⟩
        change (h : Equiv.Perm α) x₀ = x at hh
        exact ⟨g * h, by change (g : Equiv.Perm α) (((h : Equiv.Perm α) x₀)) = _; rw [hh]⟩
      have hOc_inv : ∀ (g : D) (x : α), x ∉ O → ((g : Equiv.Perm α) x) ∉ O := by
        intro g x hnx hx
        apply hnx
        have := hO_inv g⁻¹ _ hx
        have hcancel : (((g⁻¹ : D) : Equiv.Perm α) ((g : Equiv.Perm α) x)) = x := by
          change ((g⁻¹ * g : D) : Equiv.Perm α) x = x; simp
        rwa [hcancel] at this
      let ρ₁ : D →* Equiv.Perm α₁ := {
        toFun := fun g => {
          toFun := fun z => ⟨(g : Equiv.Perm α) z.1, hO_inv g z.1 z.2⟩
          invFun := fun z => ⟨((g⁻¹ : D) : Equiv.Perm α) z.1, hO_inv g⁻¹ z.1 z.2⟩
          left_inv := fun z => Subtype.ext (by
            change ((g⁻¹ * g : D) : Equiv.Perm α) z.1 = z.1; simp)
          right_inv := fun z => Subtype.ext (by
            change ((g * g⁻¹ : D) : Equiv.Perm α) z.1 = z.1; simp)
        }
        map_one' := by ext z; rfl
        map_mul' := fun g₁ g₂ => by ext z; rfl
      }
      let ρ₂ : D →* Equiv.Perm α₂ := {
        toFun := fun g => {
          toFun := fun z => ⟨(g : Equiv.Perm α) z.1, hOc_inv g z.1 z.2⟩
          invFun := fun z => ⟨((g⁻¹ : D) : Equiv.Perm α) z.1, hOc_inv g⁻¹ z.1 z.2⟩
          left_inv := fun z => Subtype.ext (by
            change ((g⁻¹ * g : D) : Equiv.Perm α) z.1 = z.1; simp)
          right_inv := fun z => Subtype.ext (by
            change ((g * g⁻¹ : D) : Equiv.Perm α) z.1 = z.1; simp)
        }
        map_one' := by ext z; rfl
        map_mul' := fun g₁ g₂ => by ext z; rfl
      }
      let emb : D → ρ₁.range × ρ₂.range :=
        fun g => (ρ₁.rangeRestrict g, ρ₂.rangeRestrict g)
      have hemb_inj : Function.Injective emb := by
        intro g₁ g₂ heq
        apply Subtype.ext
        ext x
        by_cases hx : x ∈ O
        · have h1 := congrArg (fun p => (p.1.1 ⟨x, hx⟩).1) heq
          exact h1
        · have h2 := congrArg (fun p => (p.2.1 ⟨x, hx⟩).1) heq
          exact h2
      have hsolv1 : Group.IsSolvable ρ₁.range :=
        Group.isSolvable_of_surjective ρ₁.rangeRestrict_surjective
      have hsolv2 : Group.IsSolvable ρ₂.range :=
        Group.isSolvable_of_surjective ρ₂.rangeRestrict_surjective
      have hc1 : Nat.card ρ₁.range ≤ 4 ^ (Fintype.card α₁ - 1) :=
        ih (Fintype.card α₁) h1_lt h1_pos α₁ rfl ρ₁.range hsolv1
      have hc2 : Nat.card ρ₂.range ≤ 4 ^ (Fintype.card α₂ - 1) :=
        ih (Fintype.card α₂) h2_lt h2_pos α₂ rfl ρ₂.range hsolv2
      calc Nat.card D ≤ Nat.card (ρ₁.range × ρ₂.range) :=
            Nat.card_le_card_of_injective emb hemb_inj
        _ = Nat.card ρ₁.range * Nat.card ρ₂.range := Nat.card_prod _ _
        _ ≤ 4 ^ (Fintype.card α₁ - 1) * 4 ^ (Fintype.card α₂ - 1) := Nat.mul_le_mul hc1 hc2
        _ = 4 ^ ((Fintype.card α₁ - 1) + (Fintype.card α₂ - 1)) := by rw [← pow_add]
        _ ≤ 4 ^ (n - 1) := Nat.pow_le_pow_right (by omega) (by omega)

end DixonBound

theorem OMA.solution : OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H1_R1.H3 := by
  intro n D hD
  have hnat : Nat.card D ≤ 4 ^ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hle : Nat.card D ≤ Nat.card (Equiv.Perm (Fin 0)) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      have h0 : Nat.card (Equiv.Perm (Fin 0)) = 1 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
      omega
    · exact (DixonBound.card_solvable_perm_le_four_pow_sub_one n hn (Fin n) (Fintype.card_fin n) D hD).trans
        (Nat.pow_le_pow_right (by omega) (Nat.sub_le n 1))
  have hreal : (Nat.card D : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by exact_mod_cast hnat
  calc (Nat.card D : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := hreal
    _ = ((2 : ℝ) ^ (2 : ℝ)) ^ n := by norm_num
    _ = (2 : ℝ) ^ (2 * (n : ℝ)) := by
      rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 : ℝ)) n, ← Real.rpow_mul (by norm_num)]
