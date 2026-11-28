import OMAStatements.S_mo_368734

namespace OMA.R_mo_368734_R1

def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 5 ≠ 1 →
    Function.Bijective (fun x : ZMod p => x ^ 5 + 3)

def H2 : Prop :=
  Set.Infinite {p : ℕ | p.Prime ∧ p % 5 ≠ 1 ∧
    ∀ k : ℕ, 1 ≤ k → k < p → ((fun x : ZMod p => x ^ 5 + 3)^[k]) 0 ≠ 0}

lemma iterate_cancel_of_lt {α : Type*} {f : α → α} (hf : Function.Injective f)
    {a b : ℕ} (hab : a < b) {x : α} (heq : (f^[a]) x = (f^[b]) x) :
    (f^[b - a]) x = x := by
  have hb : b = a + (b - a) := (Nat.add_sub_of_le (Nat.le_of_lt hab)).symm
  rw [hb, Function.iterate_add_apply] at heq
  exact (hf.iterate a heq).symm

lemma orderOf_eq_prime_of_orbit {p : ℕ} (hp : p.Prime)
    (σ : Equiv.Perm (ZMod p))
    (horb : ∀ k : ℕ, 1 ≤ k → k < p → ((σ : ZMod p → ZMod p)^[k]) 0 ≠ 0) :
    orderOf σ = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj_orb : Function.Injective (fun i : Fin p => ((σ : ZMod p → ZMod p)^[i.val]) 0) := by
    intro i j hij
    by_contra hne
    have hval_ne : i.val ≠ j.val := fun h => hne (Fin.ext h)
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · have h0 := iterate_cancel_of_lt σ.injective hlt hij
      exact horb (j.val - i.val) (Nat.sub_pos_of_lt hlt) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt) h0
    · exact hval_ne heq
    · have h0 := iterate_cancel_of_lt σ.injective hgt hij.symm
      exact horb (i.val - j.val) (Nat.sub_pos_of_lt hgt) (Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt) h0
  have hbij_orb : Function.Bijective (fun i : Fin p => ((σ : ZMod p → ZMod p)^[i.val]) 0) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj_orb, by simp [ZMod.card]⟩
  have hcard_lt : Fintype.card (ZMod p) < Fintype.card (Fin (p + 1)) := by
    simp [ZMod.card]
  obtain ⟨a, b, hab_ne, hab_eq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (p + 1) => ((σ : ZMod p → ZMod p)^[i.val]) 0) hcard_lt
  have hp_zero : ((σ : ZMod p → ZMod p)^[p]) 0 = 0 := by
    have hval_ne : a.val ≠ b.val := fun h => hab_ne (Fin.ext h)
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · have h0 := iterate_cancel_of_lt σ.injective hlt hab_eq
      have hle : b.val - a.val ≤ p := by omega
      rcases lt_or_eq_of_le hle with hlt_p | heq_p
      · exact False.elim (horb (b.val - a.val) (Nat.sub_pos_of_lt hlt) hlt_p h0)
      · rwa [heq_p] at h0
    · exact False.elim (hval_ne heq)
    · have h0 := iterate_cancel_of_lt σ.injective hgt hab_eq.symm
      have hle : a.val - b.val ≤ p := by omega
      rcases lt_or_eq_of_le hle with hlt_p | heq_p
      · exact False.elim (horb (a.val - b.val) (Nat.sub_pos_of_lt hgt) hlt_p h0)
      · rwa [heq_p] at h0
  have hpow_p : σ ^ p = 1 := by
    ext x
    obtain ⟨i, rfl⟩ := hbij_orb.2 x
    change ((σ : ZMod p → ZMod p)^[p]) (((σ : ZMod p → ZMod p)^[i.val]) 0) = ((σ : ZMod p → ZMod p)^[i.val]) 0
    rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hp_zero]
  have hdvd : orderOf σ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow_p
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp_eq
  · exfalso
    have hσ1 : σ = 1 := orderOf_eq_one_iff.mp h1
    have h01 : ((σ : ZMod p → ZMod p)^[1]) 0 = 0 := by simp [hσ1]
    exact horb 1 (le_refl 1) hp.one_lt h01
  · exact hp_eq

lemma natDegree_X_pow_five_add_three :
    2 ≤ ((Polynomial.X : Polynomial ℤ) ^ 5 + Polynomial.C 3).natDegree := by
  have hcoeff : ((Polynomial.X : Polynomial ℤ) ^ 5 + Polynomial.C 3).coeff 5 ≠ 0 := by
    simp [Polynomial.coeff_X_pow]
  have hle : 5 ≤ ((Polynomial.X : Polynomial ℤ) ^ 5 + Polynomial.C 3).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeff
  omega

theorem main : H1 → H2 → type_of% @OMA.S_mo_368734.main := by
  intro h1 h2
  refine ⟨(Polynomial.X : Polynomial ℤ) ^ 5 + Polynomial.C 3, natDegree_X_pow_five_add_three, ?_⟩
  refine h2.mono ?_
  rintro p ⟨hp, hp5, horb⟩
  refine ⟨hp, ?_⟩
  let σ : Equiv.Perm (ZMod p) := Equiv.ofBijective (fun x : ZMod p => x ^ 5 + 3) (h1 p hp hp5)
  have hcoe : (σ : ZMod p → ZMod p) = fun x : ZMod p => x ^ 5 + 3 := rfl
  refine ⟨σ, ?_, ?_⟩
  · apply orderOf_eq_prime_of_orbit hp σ
    rwa [hcoe]
  · intro x
    have hσx : σ x = x ^ 5 + 3 := rfl
    rw [hσx]
    simp

end OMA.R_mo_368734_R1
