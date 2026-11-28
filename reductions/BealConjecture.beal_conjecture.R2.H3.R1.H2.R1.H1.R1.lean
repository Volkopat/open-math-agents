import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1

-- Reduction BealConjecture.beal_conjecture.R2.H3.R1.H2.R1.H1.R1 of step BealConjecture.beal_conjecture.R2.H3.R1.H2.R1.H1
-- Credit: @Anthial

/-! The positive-difference leaf, single-wall split: the derivation below is
complete (prime coprimality arguments + primitive triple (u,-v,w) + gap
closure), so the leaf reduces to two islands, of which H2 is PROVED in this
file: the wall is exactly the published Bruin classification
("On Powers as Sums of Two Cubes", https://link.springer.com/chapter/10.1007/10722028_9):
every primitive integer solution of x^3 + y^3 = z^5 has |z| = 1. -/

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1

private theorem gap_cube (v : ℕ) (hv : v ≠ 0) : v ^ 3 + 1 < (v + 1) ^ 3 := by
  have h : (v + 1) ^ 3 = v ^ 3 + 3 * v ^ 2 + 3 * v + 1 := by ring
  rw [h]
  omega

private theorem gap_one (u v : ℕ) (hv : v ≠ 0) : u ^ 3 ≠ v ^ 3 + 1 := by
  intro h
  have hlt := gap_cube v hv
  have hmono : u ≤ v → u ^ 3 ≤ v ^ 3 := fun hm => Nat.pow_le_pow_left hm 3
  have hge : v + 1 ≤ u := by
    by_contra hc
    have := hmono (by omega)
    omega
  have : (v + 1) ^ 3 ≤ u ^ 3 := Nat.pow_le_pow_left hge 3
  omega

private theorem dvd_sub_of_add {p m n : ℕ} (hp : p ∣ m + n) (hn : p ∣ n) : p ∣ m := by
  obtain ⟨c, hc⟩ := hp
  obtain ⟨k, hk⟩ := hn
  refine ⟨c - k, ?_⟩
  have h1 : m + n = p * k + m := by
    rw [hk]
    ring
  have h2 : p * c = p * k + m := by
    linarith
  have h3 : p * (c - k) = p * c - p * k := by
    rw [Nat.mul_sub_left_distrib]
  have h4 : m + n = p * c := by
    linarith
  omega

private theorem coprime_wu {u v w : ℕ} (hcruv : u.Coprime v)
    (heq : u ^ 3 = v ^ 3 + w ^ 5) : w.Coprime u := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpw hpu
  have hu31 : u ∣ u ^ 3 := ⟨u ^ 2, by ring⟩
  have hp3 : p ∣ u ^ 3 := hpu.trans hu31
  have hsum : p ∣ v ^ 3 + w ^ 5 := by
    rw [← heq]
    exact hp3
  have hw51 : w ∣ w ^ 5 := ⟨w ^ 4, by ring⟩
  have hpw5 : p ∣ w ^ 5 := hpw.trans hw51
  have hpv3 : p ∣ v ^ 3 := dvd_sub_of_add hsum hpw5
  have hpv : p ∣ v := Nat.Prime.dvd_of_dvd_pow hp hpv3
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpu, hpv⟩) hcruv

private theorem coprime_wv {u v w : ℕ} (hcruv : u.Coprime v)
    (heq : u ^ 3 = v ^ 3 + w ^ 5) : w.Coprime v := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpw hpv
  have hv31 : v ∣ v ^ 3 := ⟨v ^ 2, by ring⟩
  have hp3 : p ∣ v ^ 3 := hpv.trans hv31
  have hw51 : w ∣ w ^ 5 := ⟨w ^ 4, by ring⟩
  have hpw5 : p ∣ w ^ 5 := hpw.trans hw51
  have h : p ∣ u ^ 3 := by
    rw [heq]
    exact dvd_add hp3 hpw5
  have hpu : p ∣ u := Nat.Prime.dvd_of_dvd_pow hp h
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpu, hpv⟩) hcruv

/-- Bruin's classification (the single live wall): every primitive integer
solution of x^3 + y^3 = z^5 has |z| = 1. -/
def H1 : Prop := ∀ x y z : ℤ, IsCoprime x y → IsCoprime x z → IsCoprime y z →
    x ^ 3 + y ^ 3 = z ^ 5 → z.natAbs = 1

/-- The cube-gap island: v^3 + 1 is never a positive cube; proved in this
file. -/
def H2 : Prop := ∀ u v : ℕ, v ≠ 0 → u ^ 3 ≠ v ^ 3 + 1

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1.H1 := by
  intro hbruin hgap u v w hu hv hw hcruv heq
  have hvw : IsCoprime (v : ℤ) (w : ℤ) := (coprime_wv hcruv heq).symm.isCoprime
  have huw : IsCoprime (u : ℤ) (w : ℤ) := (coprime_wu hcruv heq).symm.isCoprime
  have hneg : IsCoprime (u : ℤ) (-(v : ℤ)) := hcruv.isCoprime.neg_right
  have hnegw : IsCoprime (-(v : ℤ)) (w : ℤ) := hvw.neg_left
  have heqZ : (u : ℤ) ^ 3 + (-(v : ℤ)) ^ 3 = (w : ℤ) ^ 5 := by
    have heqZ' : (u : ℤ) ^ 3 = (v : ℤ) ^ 3 + (w : ℤ) ^ 5 := by exact_mod_cast heq
    linear_combination heqZ'
  have hzw : (w : ℤ).natAbs = 1 :=
    hbruin (u : ℤ) (-(v : ℤ)) (w : ℤ) hneg huw hnegw heqZ
  have hw1 : w = 1 := by
    have h2 : (w : ℤ) = 1 ∨ (w : ℤ) = -1 := Int.natAbs_eq_iff.mp hzw
    rcases h2 with h | h
    · exact_mod_cast h
    · exfalso
      have : (w : ℤ) ≥ 0 := by exact_mod_cast Nat.zero_le w
      linarith
  subst hw1
  exact hgap u v hv heq

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H1_R1
