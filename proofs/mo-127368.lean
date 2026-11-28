import OMAStatements.S_mo_127368

/-!
# Two prime products

Emerton gave the factorizations for all positive integer arguments in a
2013 comment on joro's question. The proof below establishes convergence,
the two general identities, and the requested evaluations at 2 and 1.

https://mathoverflow.net/questions/127368/two-products-over-primes#comment328396_127368
-/

namespace Euler127

theorem hasProd_real_zeta (s : ℕ) (hs : 2 ≤ s) :
    HasProd (fun p : Nat.Primes => (1 - 1 / (p : ℝ)^s)⁻¹)
      (∑' n : ℕ, 1 / ((n : ℝ)+1)^s) := by
  have hs0 : s ≠ 0 := by omega
  let f : ℕ →*₀ ℝ :=
    { toFun := fun n => ((n:ℝ)^s)⁻¹
      map_zero' := by simp [hs0]
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_pow, mul_comm] }
  have hf : Summable (fun n => f n) := Real.summable_nat_pow_inv.mpr hs
  have hp := EulerProduct.eulerProduct_completely_multiplicative_hasProd hf.norm
  rw [hf.tsum_eq_zero_add, map_zero, zero_add] at hp
  simpa [f,one_div] using hp

end Euler127

namespace Euler127
open Real

private theorem zeta_shift {s : ℕ} (hs : s ≠ 0) {x : ℝ}
    (h : HasSum (fun n : ℕ => 1/(n:ℝ)^s) x) :
    (∑' n : ℕ, 1/((n:ℝ)+1)^s) = x := by
  have h' := (hasSum_nat_add_iff 1 (f := fun n : ℕ => 1/(n:ℝ)^s) (g := x)).mpr
    (by simpa [hs] using h)
  simpa only [Nat.cast_add, Nat.cast_one] using h'.tsum_eq

theorem zeta_two_shift : (∑' n : ℕ, 1 / ((n:ℝ)+1)^2) = π^2/6 :=
  zeta_shift (by decide) hasSum_zeta_two

theorem zeta_four_shift : (∑' n : ℕ, 1 / ((n:ℝ)+1)^4) = π^4/90 :=
  zeta_shift (by decide) hasSum_zeta_four

theorem zeta_six_shift : (∑' n : ℕ, 1 / ((n:ℝ)+1)^6) = π^6/945 := by
  apply zeta_shift (by decide)
  have h := hasSum_zeta_nat (k:=3) (by decide)
  have hb : bernoulli 6 = 1/42 := by decide +kernel
  norm_num [hb,Nat.factorial] at h
  convert! h using 1 <;> ring_nf

end Euler127

namespace Euler127

theorem dirichlet_sum_pos {s : ℕ} (hs : 2 ≤ s) :
    0 < ∑' n : ℕ, 1 / ((n : ℝ) + 1)^s := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s))
  have h' : Summable (fun n : ℕ => 1 / ((n : ℝ)+1)^s) := by simpa using h
  exact h'.tsum_pos (fun n => by positivity) 0 (by norm_num)

theorem prime_factor_identities {x : ℝ} (hx : 1 < x) :
    (1 + 1 / (x * (x + 1)) = (1 - 1/x^2)⁻¹ / (1 - 1/x^3)⁻¹) ∧
    (1 + 1 / (x * (x - 1)) = (1 - 1/x^2)⁻¹ * (1 - 1/x^3)⁻¹ / (1 - 1/x^6)⁻¹) := by
  have hx0 := (zero_lt_one.trans hx).ne'
  have factor {y : ℝ} (hy : 1 < y) : (1-1/y)⁻¹ = y/(y-1) := by
    rw [← div_self (zero_lt_one.trans hy).ne', ← sub_div, inv_div]
  have h2 := one_lt_pow₀ hx (by decide : (2:ℕ) ≠ 0)
  have h3 := one_lt_pow₀ hx (by decide : (3:ℕ) ≠ 0)
  have h6 := one_lt_pow₀ hx (by decide : (6:ℕ) ≠ 0)
  rw [factor h2, factor h3, factor h6]
  constructor <;> field_simp [sub_ne_zero.mpr hx.ne', sub_ne_zero.mpr h2.ne',
    sub_ne_zero.mpr h3.ne', sub_ne_zero.mpr h6.ne'] <;> ring

/-- Emerton's two product formulas hold at every positive integer argument.
The HasProd assertions include convergence. -/
theorem prime_products (k : ℕ) (hk : 0 < k) :
    let Z := fun s : ℕ => ∑' n : ℕ, 1/((n:ℝ)+1)^s
    HasProd (fun p : Nat.Primes => 1+1/((p:ℝ)^k*((p:ℝ)^k+1))) (Z (2*k)/Z (3*k)) ∧
    HasProd (fun p : Nat.Primes => 1+1/((p:ℝ)^k*((p:ℝ)^k-1))) (Z (2*k)*Z (3*k)/Z (6*k)) := by
  intro Z
  have h2 := hasProd_real_zeta (2*k) (by omega)
  have h3 := hasProd_real_zeta (3*k) (by omega)
  have h6 := hasProd_real_zeta (6*k) (by omega)
  have hlocal (p : Nat.Primes) := prime_factor_identities
    (one_lt_pow₀ (by exact_mod_cast p.prop.one_lt : 1 < (p:ℝ)) hk.ne')
  constructor
  · apply (h2.div₀ h3 (dirichlet_sum_pos (by omega : 2 ≤ 3*k)).ne').congr_fun
    intro p
    simpa only [Nat.mul_comm 2 k,Nat.mul_comm 3 k,pow_mul] using (hlocal p).1
  · apply ((h2.mul h3).div₀ h6 (dirichlet_sum_pos (by omega : 2 ≤ 6*k)).ne').congr_fun
    intro p
    simpa only [Nat.mul_comm 2 k,Nat.mul_comm 3 k,Nat.mul_comm 6 k,pow_mul] using (hlocal p).2

end Euler127

open Euler127

theorem OMA.solution : type_of% @OMA.S_mo_127368.main := by
  have hf := (prime_products 2 (by decide)).1.tprod_eq
  have hg := (prime_products 1 (by decide)).2.tprod_eq
  norm_num only [Nat.reduceMul, pow_one] at hf hg
  rw [zeta_four_shift, zeta_six_shift] at hf
  rw [zeta_two_shift, zeta_six_shift] at hg
  constructor
  · rw [hf]
    field_simp [Real.pi_ne_zero]
    ring
  · rw [hg]
    field_simp [Real.pi_ne_zero]
    ring
