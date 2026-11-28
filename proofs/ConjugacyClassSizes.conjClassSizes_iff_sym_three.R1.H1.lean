import OMAReductions.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_R1
import Mathlib

/-! Proof of H1: the elementary structure of anti-homogeneous groups. -/

-- Credit: @LordMike

open ConjugacyClassSizes

theorem qs_conj_pow_of_coprime {G : Type} [Group G] [Fintype G]
    (h : HasDistinctConjClassSizes G) (x : G) (n : ℕ) (hn : (Nat.card G).Coprime n) :
    IsConj x (x ^ n) := by
  classical
  have hx : (x ^ n) ^ (Nat.card G).gcdB n = x := (powCoprime hn).symm_apply_apply x
  have hC : ∀ g : G, Commute g x ↔ Commute g (x ^ n) := by
    intro g
    constructor
    · intro hg
      exact hg.pow_right n
    · intro hg
      have h2 : Commute g ((x ^ n) ^ (Nat.card G).gcdB n) := hg.zpow_right _
      rwa [hx] at h2
  have hstab : MulAction.stabilizer (ConjAct G) x = MulAction.stabilizer (ConjAct G) (x ^ n) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ConjAct.smul_def,
      ConjAct.smul_def, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
    exact hC (ConjAct.ofConjAct g)
  have hs : Nat.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (MulAction.stabilizer (ConjAct G) (x ^ n)) := by
    rw [hstab]
  have h1 := ConjClasses.card_carrier x
  have h2 := ConjClasses.card_carrier (x ^ n)
  simp only [Fintype.card_eq_nat_card] at h1 h2
  have hcls : conjClassCard (ConjClasses.mk x) = conjClassCard (ConjClasses.mk (x ^ n)) := by
    unfold conjClassCard
    rw [h1, h2, hs]
  exact ConjClasses.mk_eq_mk_iff_isConj.mp (h hcls)

theorem qs_even_card {G : Type} [Group G] [Fintype G] [Nontrivial G]
    (h : HasDistinctConjClassSizes G) : Even (Nat.card G) := by
  by_contra hne
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hne
  have hcop : Nat.Coprime (Nat.card G) (2 * k) := by
    rw [hk]
    have hR : Nat.gcd (2 * k + 1) (2 * k) ∣ 2 * k := Nat.gcd_dvd_right _ _
    have hL : Nat.gcd (2 * k + 1) (2 * k) ∣ 2 * k + 1 := Nat.gcd_dvd_left _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hR).mp hL)
  have hpow : ∀ x : G, x ^ (2 * k + 1) = 1 := fun x => by
    rw [← hk]
    exact pow_card_eq_one'
  have hall : ∀ x : G, x = 1 := by
    intro x
    have hinv : x ^ (2 * k) = x⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ]
      exact hpow x
    obtain ⟨c, hc⟩ := isConj_iff.mp (qs_conj_pow_of_coprime h x (2 * k) hcop)
    rw [hinv] at hc
    have hc2 : c ^ 2 * x = x * c ^ 2 := by
      have e : c ^ 2 * x * (c ^ 2)⁻¹ = x := by
        have e1 : c ^ 2 * x * (c ^ 2)⁻¹ = c * (c * x * c⁻¹) * c⁻¹ := by
          rw [pow_two]
          group
        have e2 : c * (c * x * c⁻¹) * c⁻¹ = c * x⁻¹ * c⁻¹ := by rw [hc]
        have e3 : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
        rw [e1, e2, e3, hc, inv_inv]
      exact mul_inv_eq_iff_eq_mul.mp e
    have hcpow : (c ^ 2) ^ (k + 1) = c := by
      have hc1 : c ^ (2 * k + 1) = 1 := hpow c
      calc (c ^ 2) ^ (k + 1) = c ^ (1 + (2 * k + 1)) := by
            rw [← pow_mul]
            congr 1
            ring
        _ = c := by rw [pow_add, hc1, mul_one, pow_one]
    have hcomm : Commute c x := by
      have h3 : Commute ((c ^ 2) ^ (k + 1)) x :=
        (show Commute (c ^ 2) x from hc2).pow_left (k + 1)
      rw [hcpow] at h3
      exact h3
    have hxinv : x = x⁻¹ := by
      rw [hcomm.eq, mul_inv_cancel_right] at hc
      exact hc
    have hx2 : x ^ 2 = 1 := by
      calc x ^ 2 = x * x⁻¹ := by rw [pow_two, ← hxinv]
        _ = 1 := mul_inv_cancel x
    calc x = x ^ (2 * k + 1) * x := by rw [hpow x, one_mul]
      _ = x ^ (2 * (k + 1)) := by
            rw [← pow_succ]
            congr 1
      _ = (x ^ 2) ^ (k + 1) := pow_mul x 2 (k + 1)
      _ = 1 := by rw [hx2, one_pow]
  obtain ⟨y, hy⟩ := exists_ne (1 : G)
  exact hy (hall y)

theorem OMA.solution : OMA.R_ConjugacyClassSizes_conjClassSizes_iff_sym_three_R1.H1 := by
  intro G _ _ _ h
  exact ⟨fun x n hn => qs_conj_pow_of_coprime h x n hn,
    trivial_center_of_hasDistinctConjClassSizes h, qs_even_card h⟩

