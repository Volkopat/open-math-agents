import OMAReductions.R_Erdos364_erdos_364_variants_strong_R1_H3_R1
import Mathlib.NumberTheory.LegendreSymbol.Basic

-- Credit: @Alewawa

/-! Separate square neighbors of the middle square's root from the case
of three nontrivial squarefree cube kernels. -/

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1_H3_R1_H1_R1

private theorem prime_sq_dvd_of_powerful {n p : ℕ} (hn : n.Powerful) (hp : p.Prime)
    (hd : p ∣ n) : p^2 ∣ n := by
  by_cases hz : n = 0
  · simp [hz]
  · exact hn p (Nat.mem_primeFactors.mpr ⟨hp, hd, hz⟩)

/-- The squarefree part of a powerful number divides its square-root factor.
This is the factorization argument used in the parent reduction. -/
private theorem cube_kernel {n : ℕ} (hn : n.Powerful) (hn0 : 0 < n)
    (hnonsq : ¬ ∃ a : ℕ, n = a^2) :
    ∃ a u : ℕ, 1 < u ∧ Squarefree u ∧ n = a^2*u^3 ∧ u ∣ n := by
  obtain ⟨u, s, hu, hs, hprod, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn0
  have hfact : n.factorization = 2 • s.factorization + u.factorization := by
    rw [← hprod, Nat.factorization_mul (pow_ne_zero 2 hs.ne') hu.ne', Nat.factorization_pow]
  have hdiv : u ∣ s := by
    rw [← Nat.factorization_le_iff_dvd hu.ne' hs.ne', Finsupp.le_iff]
    intro p hp
    have hpu : p ∈ u.primeFactors := Nat.support_factorization u ▸ hp
    obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpu
    have hpn : p ∣ n := hprod ▸ (hpd.mul_left (s^2))
    have h₂ := (Nat.Prime.pow_dvd_iff_le_factorization hpp hn0.ne').mp
      (prime_sq_dvd_of_powerful hn hpp hpn)
    have h₁ := (Nat.squarefree_iff_factorization_le_one hu.ne').mp hsf p
    have he : n.factorization p = 2 * s.factorization p + u.factorization p := by
      simp [hfact, Finsupp.add_apply, two_smul, two_mul]
    omega
  obtain ⟨a, ha⟩ := hdiv
  have he : n = a^2*u^3 := by
    rw [← hprod, ha]
    ring
  refine ⟨a,u,?_,hsf,he,he.symm ▸ (dvd_pow_self u (by decide : (3 : ℕ) ≠ 0)).mul_left (a^2)⟩
  by_contra! h
  have hu1 : u = 1 := by omega
  exact hnonsq ⟨a, by simpa [hu1] using he⟩

private theorem sq_mod8_odd (a : ℕ) (ha : a^2 % 2 = 1) : a^2 % 8 = 1 := by
  have h := Nat.pow_mod a 2 8
  have h₂ : (a^2 % 8) % 2 = 1 := by
    rwa [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
  rw [h] at h₂ ⊢
  have ha8 := Nat.mod_lt a (by decide : 0 < 8)
  interval_cases a % 8 <;> norm_num at h₂ <;> decide

private theorem cube_kernel_mod8 (a u : ℕ) (hodd : (a^2*u^3)%2 = 1) :
    (a^2*u^3)%8 = u%8 := by
  have he : (a^2*u^3)%8 = ((a%8)^2*(u%8)^3)%8 := by
    rw [Nat.mul_mod (a^2) (u^3) 8, Nat.pow_mod a 2 8, Nat.pow_mod u 3 8,
      ← Nat.mul_mod]
  have h₂ : ((a^2*u^3)%8)%2 = 1 := by
    rwa [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 8)]
  rw [he] at h₂ ⊢
  have hsmall : ∀ a u : Fin 8, (((a.val^2*u.val^3)%8)%2 = 1) →
      (a.val^2*u.val^3)%8 = u.val := by decide
  exact hsmall ⟨a%8, Nat.mod_lt _ (by decide)⟩ ⟨u%8, Nat.mod_lt _ (by decide)⟩ h₂

private theorem not_square_succ_square {x : ℕ} (hx : 0 < x) :
    ¬ ∃ a : ℕ, x^2+1 = a^2 := by
  rintro ⟨a,ha⟩
  have hxa : x < a := by
    by_contra! hh
    have := Nat.pow_le_pow_left hh 2
    omega
  have hh := Nat.pow_le_pow_left (show x+1 ≤ a by omega) 2
  nlinarith

private theorem prime_divisor_four {x p : ℕ} (hxe : x%2 = 0) (hp : p.Prime)
    (hd : p ∣ x^2+1) : p%4 = 1 := by
  have hodd : (x^2+1)%2 = 1 := by
    simp [Nat.add_mod, Nat.pow_mod x 2 2, hxe]
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  have hoddp := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  let : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  push_cast at hz
  have h' : (x : ZMod p)^2 = -1 := eq_neg_of_add_eq_zero_left hz
  have hn := ZMod.mod_four_ne_three_of_sq_eq_neg_one h'
  omega

private theorem coprime_neighbors {x : ℕ} (hx : 2 ≤ x) (he : x%2 = 0) :
    (x-1).Coprime (x+1) ∧ (x-1).Coprime (x^2+1) ∧ (x+1).Coprime (x^2+1) := by
  have ho₁ : Odd (x-1) := Nat.odd_iff.mpr (by omega)
  have ho₂ : Odd (x+1) := Nat.odd_iff.mpr (by omega)
  have hform : x^2+1 = (x-1)*(x+1)+2 := by
    obtain ⟨y,rfl⟩ : ∃ y : ℕ, x=y+1 := ⟨x-1,by omega⟩
    rw [Nat.add_sub_cancel]
    ring
  refine ⟨?_,?_,?_⟩
  · rw [show x+1 = (x-1)+2 by omega, Nat.coprime_self_add_right, Nat.coprime_two_right]
    exact ho₁
  · rw [hform, Nat.coprime_add_iff_right (dvd_mul_right _ _), Nat.coprime_two_right]
    exact ho₁
  · rw [hform, Nat.coprime_add_iff_right (dvd_mul_left _ _), Nat.coprime_two_right]
    exact ho₂

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem small_cases (x : ℕ) (hx : x ≤ 1024) :
    ¬ (2 ≤ x ∧ x%2 = 0 ∧ ¬ x.Powerful ∧
      (x-1).Powerful ∧ (x+1).Powerful ∧ (x^2+1).Powerful) := by
  have htest : ∀ t : Fin 1025, ¬ (2 ≤ t.val ∧ t.val%2 = 0 ∧ ¬ t.val.Powerful ∧
      (t.val-1).Powerful ∧ (t.val+1).Powerful ∧ (t.val^2+1).Powerful) := by decide +kernel
  exact htest ⟨x,by omega⟩

private theorem powerful_sq_cube (a u : ℕ) : (a^2*u^3).Powerful := by
  intro p hp
  obtain ⟨hpr, hd, _⟩ := Nat.mem_primeFactors.mp hp
  rcases hpr.dvd_mul.mp hd with ha | hu
  · exact (pow_dvd_pow_of_dvd (hpr.dvd_of_dvd_pow ha) 2).mul_right _
  · have h : p^2 ∣ u^3 :=
      (pow_dvd_pow_of_dvd (hpr.dvd_of_dvd_pow hu) 2).trans
        (pow_dvd_pow u (by decide : 2 ≤ 3))
    exact h.mul_left _

private theorem powerful_sq (a : ℕ) : (a^2).Powerful := by
  simpa using powerful_sq_cube a 1

/-- The case where the lower neighbor of the square root is a square. -/
def H1 : Prop :=
  ¬ ∃ x a b c u w : ℕ, 1024 < x ∧ x%8 = 2 ∧ ¬ x.Powerful ∧
    x-1 = a^2 ∧ x+1 = b^2*u^3 ∧ x^2+1 = c^2*w^3 ∧
    1 < u ∧ Squarefree u ∧ u%8 = 3 ∧
    1 < w ∧ Squarefree w ∧ w%8 = 5 ∧ u.Coprime w ∧
    (∀ p : ℕ, p.Prime → p ∣ w → p%4 = 1)

/-- The case where the upper neighbor of the square root is a square. -/
def H2 : Prop :=
  ¬ ∃ x a b c u w : ℕ, 1024 < x ∧ x%8 = 0 ∧ ¬ x.Powerful ∧
    x-1 = a^2*u^3 ∧ x+1 = b^2 ∧ x^2+1 = c^2*w^3 ∧
    1 < u ∧ Squarefree u ∧ u%8 = 7 ∧
    1 < w ∧ Squarefree w ∧ w%8 = 1 ∧ u.Coprime w ∧
    (∀ p : ℕ, p.Prime → p ∣ w → p%4 = 1)

/-- Neither neighbor is a square. All three cube kernels are nontrivial. -/
def H3 : Prop :=
  ¬ ∃ x a b c u v w : ℕ, 1024 < x ∧ x%2 = 0 ∧ ¬ x.Powerful ∧
    x-1 = a^2*u^3 ∧ x+1 = b^2*v^3 ∧ x^2+1 = c^2*w^3 ∧
    1 < u ∧ 1 < v ∧ 1 < w ∧ Squarefree u ∧ Squarefree v ∧ Squarefree w ∧
    u.Coprime v ∧ u.Coprime w ∧ v.Coprime w ∧
    (∀ p : ℕ, p.Prime → p ∣ w → p%4 = 1)

theorem main : H1 → H2 → H3 → OMA.R_Erdos364_erdos_364_variants_strong_R1_H3_R1.H1 := by
  intro h₁ h₂ h₃
  rintro ⟨x,hx,he,hn,hL,hR,hN⟩
  have hlarge : 1024 < x := by
    by_contra! h
    exact small_cases x h ⟨hx,he,hn,hL,hR,hN⟩
  obtain ⟨c,w,hw,hwf,hC,hwd⟩ := cube_kernel hN (by positivity)
    (not_square_succ_square (by omega))
  have hP : ∀ p : ℕ, p.Prime → p ∣ w → p%4 = 1 :=
    fun p hp hd => prime_divisor_four he hp (hd.trans hwd)
  obtain ⟨hcLR,hcLC,hcRC⟩ := coprime_neighbors hx he
  have hoddL : (x-1)%2 = 1 := by omega
  have hoddR : (x+1)%2 = 1 := by omega
  have hoddC : (x^2+1)%2 = 1 := by simp [Nat.add_mod, Nat.pow_mod x 2 2, he]
  have hwmod := cube_kernel_mod8 c w (hC ▸ hoddC)
  by_cases hlsq : ∃ a : ℕ, x-1 = a^2
  · obtain ⟨a,ha⟩ := hlsq
    have hL8 : (x-1)%8 = 1 := ha.symm ▸ sq_mod8_odd a (ha ▸ hoddL)
    have hx8 : x%8 = 2 := by omega
    have hrsq : ¬ ∃ b : ℕ, x+1 = b^2 := by
      rintro ⟨b,hb⟩
      have hR8 : (x+1)%8 = 1 := hb.symm ▸ sq_mod8_odd b (hb ▸ hoddR)
      omega
    obtain ⟨b,u,hu,huf,hB,hud⟩ := cube_kernel hR (by omega) hrsq
    have humod := cube_kernel_mod8 b u (hB ▸ hoddR)
    rw [← hB] at humod
    rw [← hC, Nat.add_mod, Nat.pow_mod x 2 8, hx8] at hwmod
    norm_num at hwmod
    exact h₁ ⟨x,a,b,c,u,w,hlarge,hx8,hn,ha,hB,hC,hu,huf,by omega,hw,hwf,hwmod.symm,
      hcRC.of_dvd hud hwd,hP⟩
  · by_cases hrsq : ∃ b : ℕ, x+1 = b^2
    · obtain ⟨b,hb⟩ := hrsq
      have hR8 : (x+1)%8 = 1 := hb.symm ▸ sq_mod8_odd b (hb ▸ hoddR)
      have hx8 : x%8 = 0 := by omega
      obtain ⟨a,u,hu,huf,hA,hud⟩ := cube_kernel hL (by omega) hlsq
      have humod := cube_kernel_mod8 a u (hA ▸ hoddL)
      rw [← hA] at humod
      rw [← hC, Nat.add_mod, Nat.pow_mod x 2 8, hx8] at hwmod
      norm_num at hwmod
      exact h₂ ⟨x,a,b,c,u,w,hlarge,hx8,hn,hA,hb,hC,hu,huf,by omega,hw,hwf,hwmod.symm,
        hcLC.of_dvd hud hwd,hP⟩
    · obtain ⟨a,u,hu,huf,hA,hud⟩ := cube_kernel hL (by omega) hlsq
      obtain ⟨b,v,hv,hvf,hB,hvd⟩ := cube_kernel hR (by omega) hrsq
      exact h₃ ⟨x,a,b,c,u,v,w,hlarge,he,hn,hA,hB,hC,hu,hv,hw,huf,hvf,hwf,
        hcLR.of_dvd hud hvd,hcLC.of_dvd hud hwd,hcRC.of_dvd hvd hwd,hP⟩

/-- The three structured cases are jointly equivalent to the requested step. -/
theorem cases_iff : (H1 ∧ H2 ∧ H3) ↔ OMA.R_Erdos364_erdos_364_variants_strong_R1_H3_R1.H1 := by
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    exact main h₁ h₂ h₃
  · intro h
    refine ⟨?_,?_,?_⟩
    · rintro ⟨x,a,b,c,u,w,hx,he,hn,hL,hR,hC,_⟩
      exact h ⟨x,by omega,by omega,hn,hL.symm ▸ powerful_sq a,
        hR.symm ▸ powerful_sq_cube b u,hC.symm ▸ powerful_sq_cube c w⟩
    · rintro ⟨x,a,b,c,u,w,hx,he,hn,hL,hR,hC,_⟩
      exact h ⟨x,by omega,by omega,hn,hL.symm ▸ powerful_sq_cube a u,
        hR.symm ▸ powerful_sq b,hC.symm ▸ powerful_sq_cube c w⟩
    · rintro ⟨x,a,b,c,u,v,w,hx,he,hn,hL,hR,hC,_⟩
      exact h ⟨x,by omega,he,hn,hL.symm ▸ powerful_sq_cube a u,
        hR.symm ▸ powerful_sq_cube b v,hC.symm ▸ powerful_sq_cube c w⟩

end OMA.R_Erdos364_erdos_364_variants_strong_R1_H3_R1_H1_R1
