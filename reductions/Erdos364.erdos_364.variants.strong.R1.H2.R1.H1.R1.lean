import OMAReductions.R_Erdos364_erdos_364_variants_strong_R1_H2_R1
import Mathlib

/-! Elementary structure of primitive progressions of three powerful integers. -/

namespace Erdos364PrimitiveKernels

open Nat

/-- A positive powerful integer is a square times the cube of a squarefree integer. -/
theorem square_mul_cube : ∀ n : ℕ, 0 < n → n.Powerful →
    ∃ u v : ℕ, Squarefree v ∧ n = u^2*v^3 := by
  intro n
  induction n using Nat.recOnPrimePow with
  | zero => omega
  | one => exact fun _ _ => ⟨1,1,by simp,by norm_num⟩
  | prime_pow_mul a p e hp hpa he ih =>
    intro hpos hfull
    have ha : 0 < a := Nat.pos_of_ne_zero (fun h => hpa (h ▸ dvd_zero p))
    have hAp : a.Powerful := by
      intro q hq
      obtain ⟨hqP,hqa,haz⟩ := Nat.mem_primeFactors.mp hq
      have hqp : q ≠ p := fun h => hpa (h ▸ hqa)
      have hcop : (q^2).Coprime (p^e) := (Nat.coprime_primes hqP hp).mpr hqp |>.pow_left 2 |>.pow_right e
      have h := hfull q (Nat.mem_primeFactors.mpr ⟨hqP,dvd_mul_of_dvd_right hqa _,hpos.ne'⟩)
      exact hcop.dvd_of_dvd_mul_left h
    obtain ⟨u,v,hv,hav⟩ := ih ha hAp
    have hpdiv : p ∣ p^e*a := dvd_mul_of_dvd_left (dvd_pow_self p he.ne') a
    have h2div := hfull p (Nat.mem_primeFactors.mpr ⟨hp,hpdiv,hpos.ne'⟩)
    have he2 : 2 ≤ e := by
      by_contra! h
      have h1 : e = 1 := by omega
      rw [h1, pow_one, pow_two] at h2div
      exact hpa (Nat.dvd_of_mul_dvd_mul_left hp.pos h2div)
    by_cases heven : e % 2 = 0
    · have hp2 : p^e = (p^(e/2))^2 := by
        rw [← pow_mul]
        congr 1
        omega
      refine ⟨p^(e/2)*u, v, hv, ?_⟩
      rw [hp2, hav, mul_pow]
      ring
    · have hp3 : p^e = (p^((e-3)/2))^2*p^3 := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
      have hpv : ¬ p ∣ v := fun h => hpa (hav ▸ dvd_mul_of_dvd_right (h.trans (dvd_pow_self v (by decide))) _)
      have hcop := hp.coprime_iff_not_dvd.mpr hpv
      refine ⟨p^((e-3)/2)*u, p*v, (Nat.squarefree_mul hcop).2 ⟨hp.squarefree,hv⟩, ?_⟩
      rw [hp3, hav, mul_pow, mul_pow]
      ring

private theorem square_spacing {u v d : ℕ} (hlt : u^2 < v^2) (hgap : v^2 ≤ u^2 + 2*d) : u^2 ≤ d^2 := by
  have huv : u < v := by
    by_contra! h
    have hn := Nat.pow_le_pow_left h 2
    omega
  have hstep := Nat.pow_le_pow_left (Nat.succ_le_of_lt huv) 2
  rw [show (u+1)^2 = u^2+2*u+1 by ring] at hstep
  exact Nat.pow_le_pow_left (by omega) 2

private theorem cube_dvd_of_pair {a d b : ℕ} (h0 : b^3 ∣ a) (h1 : b^3 ∣ a+d) : b^3 ∣ d := by
  simpa using (Nat.dvd_sub h1 h0)

/-- Any repetition among the three cube factors of a primitive triple gives two squares
and hence a quadratic bound in the common difference. -/
theorem repeated_kernel_gap {a d u v w b c e : ℕ}
    (ha : 0 < a) (hd : 0 < d) (hcop : a.Coprime d)
    (hx : a = u^2*b^3) (hy : a+d = v^2*c^3) (hz : a+2*d = w^2*e^3)
    (hr : b = c ∨ b = e ∨ c = e) : a ≤ d^2 := by
  have hb : b^3 ∣ a := hx ▸ dvd_mul_left _ _
  have hc : c^3 ∣ a+d := hy ▸ dvd_mul_left _ _
  have he : e^3 ∣ a+2*d := hz ▸ dvd_mul_left _ _
  rcases hr with hbc | hbe | hce
  · subst c
    have hbd := cube_dvd_of_pair hb hc
    have hb1 : b^3 = 1 := Nat.dvd_one.mp (Nat.dvd_gcd hb hbd |>.trans (by simp [hcop]))
    simp [hb1] at hx hy
    rw [hx]
    exact square_spacing (hy ▸ hx ▸ (show a < a+d by omega)) (by omega : v^2 ≤ u^2+2*d)
  · subst e
    have hbd := cube_dvd_of_pair hb he
    have hbcop : (b^3).Coprime d := hcop.of_dvd_left hb
    have hsmall := Nat.le_of_dvd (by decide : 0 < 2) (hbcop.dvd_of_dvd_mul_left (by simpa [mul_comm] using hbd))
    have hbpos : 0 < b := by
      by_contra! h
      have h0 : b=0 := by omega
      simp [h0] at hx
      omega
    have hb1 : b=1 := by
      by_contra! h
      have h2 : 2 ≤ b := by omega
      have hp := Nat.pow_le_pow_left h2 3
      norm_num at hp
      omega
    simp [hb1] at hx hz
    rw [hx]
    exact square_spacing (hz ▸ hx ▸ (show a < a+2*d by omega)) (by omega : w^2 ≤ u^2+2*d)
  · subst e
    have hcd : c^3 ∣ d := by
      have h := Nat.dvd_sub he hc
      convert h using 1
      omega
    have hca : c^3 ∣ a := by simpa using Nat.dvd_sub hc hcd
    have hc1 : c^3 = 1 := Nat.dvd_one.mp (Nat.dvd_gcd hca hcd |>.trans (by simp [hcop]))
    simp [hc1] at hy hz
    have hbound : v^2 ≤ d^2 := square_spacing (by omega : v^2 < w^2) (by omega : w^2 ≤ v^2+2*d)
    omega

/-- The cube factors of the three terms are pairwise coprime in a primitive progression. -/
theorem kernels_coprime {a d b c e : ℕ} (hcop : a.Coprime d)
    (hb : b^3 ∣ a) (hc : c^3 ∣ a+d) (he : e^3 ∣ a+2*d) :
    b.Coprime c ∧ b.Coprime e ∧ c.Coprime e := by
  have hdisjoint (p : ℕ) (hp : p.Prime) (ha : p ∣ a) (hd : p ∣ d) : False := by
    have hg := Nat.dvd_gcd ha hd
    rw [show a.gcd d = 1 from hcop] at hg
    exact hp.ne_one (Nat.dvd_one.mp hg)
  have haq : ∀ p : ℕ, p ∣ b → p ∣ a := fun p hp => (hp.trans (dvd_pow_self _ (by decide))).trans hb
  have hcq : ∀ p : ℕ, p ∣ c → p ∣ a+d := fun p hp => (hp.trans (dvd_pow_self _ (by decide))).trans hc
  have heq : ∀ p : ℕ, p ∣ e → p ∣ a+2*d := fun p hp => (hp.trans (dvd_pow_self _ (by decide))).trans he
  refine ⟨Nat.coprime_of_dvd ?_, Nat.coprime_of_dvd ?_, Nat.coprime_of_dvd ?_⟩
  · intro p hp hpb hpc
    exact hdisjoint p hp (haq p hpb) (by simpa using Nat.dvd_sub (hcq p hpc) (haq p hpb))
  · intro p hp hpb hpe
    have hra : p^3 ∣ a := (pow_dvd_pow_of_dvd hpb 3).trans hb
    have hre : p^3 ∣ a+2*d := (pow_dvd_pow_of_dvd hpe 3).trans he
    have hp2d := cube_dvd_of_pair hra hre
    have hpcop : (p^3).Coprime d := hcop.of_dvd_left hra
    have hsmall := Nat.le_of_dvd (by decide : 0 < 2) (hpcop.dvd_of_dvd_mul_left
      (by simpa [mul_comm] using hp2d))
    have hpbig := Nat.pow_le_pow_left hp.two_le 3
    norm_num at hpbig
    omega
  · intro p hp hpc hpe
    have hd : p ∣ d := by convert Nat.dvd_sub (heq p hpe) (hcq p hpc) using 1; omega
    have ha : p ∣ a := by simpa using Nat.dvd_sub (hcq p hpc) hd
    exact hdisjoint p hp ha hd

/-- An odd step forces the middle term to be divisible by four. -/
theorem odd_step_middle {a d : ℕ} (hd : d % 2 = 1)
    (h₀ : a.Powerful) (h₁ : (a+d).Powerful) (h₂ : (a+2*d).Powerful) :
    4 ∣ a+d ∧ a % 2 = 1 := by
  have exclude {x : ℕ} (h : x.Powerful) : x % 4 ≠ 2 := by
    exact fun hm => Nat.not_full_of_prime_mod_prime_sq x 1 Nat.prime_two hm h
  have h₀' := exclude h₀
  have h₁' := exclude h₁
  have h₂' := exclude h₂
  constructor
  · omega
  · omega

end Erdos364PrimitiveKernels

namespace OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1_H1_R1

open Nat Erdos364PrimitiveKernels

/-- Primitive even-step triples with distinct squarefree cube factors. -/
def H1 : Prop := ∃ k C : ℕ, 0 < k ∧ ∀ a d u v w b c e : ℕ,
    0 < a → 0 < d → a.Coprime d → d % 2 = 0 → a % 2 = 1 →
    Squarefree b → Squarefree c → Squarefree e → b.Coprime c → b.Coprime e → c.Coprime e →
    b ≠ c → b ≠ e → c ≠ e →
    a = u^2*b^3 → a+d = v^2*c^3 → a+2*d = w^2*e^3 → a ≤ C*d^k

/-- Primitive odd-step triples with distinct squarefree cube factors. -/
def H2 : Prop := ∃ k C : ℕ, 0 < k ∧ ∀ a d u v w b c e : ℕ,
    0 < a → 0 < d → a.Coprime d → d % 2 = 1 → a % 2 = 1 → 4 ∣ a+d →
    Squarefree b → Squarefree c → Squarefree e → b.Coprime c → b.Coprime e → c.Coprime e →
    b ≠ c → b ≠ e → c ≠ e →
    a = u^2*b^3 → a+d = v^2*c^3 → a+2*d = w^2*e^3 → a ≤ C*d^k

theorem main : H1 → H2 → OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1.H1 := by
  rintro ⟨k₀,C₀,_,heven⟩ ⟨k₁,C₁,_,hodd⟩
  let k := max 2 (max k₀ k₁)
  let C := max 1 (max C₀ C₁)
  have hk2 : 2 ≤ k := le_max_left _ _
  have hC1 : 1 ≤ C := le_max_left _ _
  refine ⟨k,C,by omega,fun a d ha hd hpa hpb hpc hcop => ?_⟩
  have lift {j D : ℕ} (hj : j ≤ k) (hD : D ≤ C) (h : a ≤ D*d^j) : a ≤ C*d^k :=
    h.trans (Nat.mul_le_mul hD (pow_le_pow_right₀ (by omega) hj))
  obtain ⟨u,b,hb,hx⟩ := square_mul_cube a ha hpa
  obtain ⟨v,c,hc,hy⟩ := square_mul_cube (a+d) (by omega) hpb
  obtain ⟨w,e,he,hz⟩ := square_mul_cube (a+2*d) (by omega) hpc
  by_cases hr : b = c ∨ b = e ∨ c = e
  · apply lift hk2 hC1
    simpa using repeated_kernel_gap ha hd hcop hx hy hz hr
  push Not at hr
  obtain ⟨hbc,hbe,hce⟩ := hr
  obtain ⟨hcc₁,hcc₂,hcc₃⟩ := kernels_coprime hcop
    (hx ▸ dvd_mul_left _ _) (hy ▸ dvd_mul_left _ _) (hz ▸ dvd_mul_left _ _)
  rcases (show d % 2 = 0 ∨ d % 2 = 1 by omega) with hd₀ | hd₁
  · have hao : a % 2 = 1 := by
      by_contra! h
      have hgcd := Nat.dvd_gcd (show 2 ∣ a by omega) (show 2 ∣ d by omega)
      rw [show a.gcd d = 1 from hcop] at hgcd
      omega
    exact lift ((le_max_left k₀ k₁).trans (le_max_right _ _))
      ((le_max_left C₀ C₁).trans (le_max_right _ _))
      (heven a d u v w b c e ha hd hcop hd₀ hao hb hc he hcc₁ hcc₂ hcc₃ hbc hbe hce hx hy hz)
  · obtain ⟨hm,hao⟩ := odd_step_middle hd₁ hpa hpb hpc
    exact lift ((le_max_right k₀ k₁).trans (le_max_right _ _))
      ((le_max_right C₀ C₁).trans (le_max_right _ _))
      (hodd a d u v w b c e ha hd hcop hd₁ hao hm hb hc he hcc₁ hcc₂ hcc₃ hbc hbe hce hx hy hz)

end OMA.R_Erdos364_erdos_364_variants_strong_R1_H2_R1_H1_R1
