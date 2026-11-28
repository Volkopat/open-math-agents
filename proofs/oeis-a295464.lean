import OMAStatements.S_oeis_a295464
import Mathlib

/-!
Proof of Peter Bala's fractional-index integrality conjecture for OEIS A295464.

Method. For even n the quantity is the integral factorial ratio a(n/2). For odd n, Legendre's
duplication formula, in the form Gamma(t/2 + 1) = t! Gamma(1/2) / (2^t (t div 2)!) for odd t,
turns every half-integer factorial into integer ones; the factors Gamma(1/2) cancel and what is
left is 2^E times a ratio of factorials of k*n/2 (natural division). Its integrality follows from
Legendre's formula once the Landau step-function inequality
  sum over the denominator of floor(k*n/Q) <= sum over the numerator of floor(k*n/Q)
holds for every Q; reducing n modulo Q puts this on a finite grid that the kernel checks by
`decide`.

Attribution. The lemmas factorial_prod_ne_zero, padic_prod_factorial, factorial_prod_dvd_of_floor,
quotient_cast_integral, mul_div_reduce and grid_floor, and the proof of ffact_half_odd, are adapted
from the-omega-institute/trureturing, file
D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.lean (commit
ff444aeb6b57ff09b8e46cfa5b8e62baf80d7efa), Copyright the-omega-institute contributors, used under the Apache License,
Version 2.0. The generic grid reduction (sum_split, grid_landau, half_dvd) and the assembly for
this entry are new.
-/

namespace A295464P

open OMA.S_oeis_a295464

lemma factorial_prod_ne_zero (L : List ℕ) : (L.map Nat.factorial).prod ≠ 0 := by
  simp [Nat.factorial_ne_zero]

lemma padic_prod_factorial (p : ℕ) [hp : Fact p.Prime] (L : List ℕ) :
    padicValNat p (L.map Nat.factorial).prod = (L.map (fun n => padicValNat p n.factorial)).sum := by
  rw [← Fin.prod_univ_fun_getElem L Nat.factorial, ← Fin.sum_univ_fun_getElem L (fun n => padicValNat p n.factorial)]
  have hf (i : Fin L.length) (_hi : i ∈ Finset.univ) : (L[i.val]).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hh : (padicValNat p (∏ i : Fin L.length, (L[i.val]).factorial) : ℕ∞) =
      ((∑ i : Fin L.length, padicValNat p (L[i.val]).factorial : ℕ) : ℕ∞) := by
    rw [padicValNat_eq_emultiplicity (Finset.prod_ne_zero_iff.mpr hf), Nat.cast_sum]
    exact (Finset.emultiplicity_prod (Nat.prime_iff.mp hp.out) Finset.univ (fun i : Fin L.length => (L[i.val]).factorial)).trans
      (Finset.sum_congr rfl (fun i hi => (padicValNat_eq_emultiplicity (hf i hi)).symm))
  exact_mod_cast hh

lemma factorial_prod_dvd_of_floor (A B : List ℕ)
    (h : ∀ q : ℕ, 0 < q →
      (B.map (fun n => n / q)).sum ≤ (A.map (fun n => n / q)).sum) :
    (B.map Nat.factorial).prod ∣ (A.map Nat.factorial).prod := by
  classical
  apply (Nat.factorization_prime_le_iff_dvd (factorial_prod_ne_zero B)
    (factorial_prod_ne_zero A)).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    padic_prod_factorial, padic_prod_factorial]
  let bound := (A ++ B).sum + 1
  have vf (m : ℕ) (hm : m ∈ A ++ B) :
      padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 bound, m / p^j := by
    apply padicValNat_factorial
    have hh : m ≤ (A ++ B).sum := List.le_sum_of_mem hm
    exact lt_of_le_of_lt (p.log_le_self m) (by dsimp [bound]; omega)
  have swap (L : List ℕ) (hL : ∀ x ∈ L, x ∈ A ++ B) :
      (L.map (fun n => padicValNat p n.factorial)).sum =
        ∑ j ∈ Finset.Ico 1 bound, (L.map (fun n => n / p^j)).sum := by
    calc
      _ = (L.map (fun n => ∑ j ∈ Finset.Ico 1 bound, n / p^j)).sum := by
        congr 1
        apply List.map_congr_left
        intro n hn
        exact vf n (hL n hn)
      _ = _ := by
        simpa only [Multiset.map_coe, Multiset.sum_coe] using
          (Multiset.sum_map_sum (m := (L : Multiset ℕ)) (s := Finset.Ico 1 bound) (f := fun n j => n / p^j))
  rw [swap B (by intro x hx; exact List.mem_append_right A hx),
    swap A (by intro x hx; exact List.mem_append_left B hx)]
  exact Finset.sum_le_sum (fun j _ => h (p^j) (pow_pos hp.pos j))

lemma quotient_cast_integral {A B : ℕ} (h : B ∣ A) (hB : B ≠ 0) :
    ∃ z : ℤ, (z : ℝ) = (A : ℝ) / (B : ℝ) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨(k : ℤ), ?_⟩
  rw [hk]
  push_cast
  field_simp

lemma mul_div_reduce (c n q : ℕ) (hq : 0 < q) :
    c*n/q = c*(n/q)+c*(n%q)/q := by
  calc
    c*n/q = (q*(c*(n/q))+c*(n%q))/q := by
      congr 1
      have := Nat.div_add_mod n q
      nlinarith
    _ = c*(n/q)+c*(n%q)/q := by rw [Nat.mul_add_div hq]

lemma grid_floor (L c d r q : ℕ) (hd : 0 < d) (hcd : L = c*d) :
    c*r/q = (L*r/q)/d := by
  rw [Nat.div_div_eq_div_mul, hcd,
    show c*d*r = d*(c*r) by ring,
    show q*d = d*q by ring, Nat.mul_div_mul_left _ _ hd]

lemma sum_split (L Q n : ℕ) (hL : 0 < L) (hQ : 0 < Q) (cs : List ℕ) (hc : ∀ c ∈ cs, c ∣ L) :
    (cs.map (fun c => c * n / Q)).sum =
      cs.sum * (n / Q) + (cs.map (fun c => (L * (n % Q) / Q) / (L / c))).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hcL : c ∣ L := hc c (by simp)
    have ih' := ih (fun x hx => hc x (by simp [hx]))
    have hpos : 0 < L / c := Nat.div_pos (Nat.le_of_dvd hL hcL) (Nat.pos_of_dvd_of_pos hcL hL)
    have h1 : c * n / Q = c * (n / Q) + (L * (n % Q) / Q) / (L / c) := by
      rw [mul_div_reduce c n Q hQ, grid_floor L c (L / c) (n % Q) Q hpos (Nat.mul_div_cancel' hcL).symm]
    simp only [List.map_cons, List.sum_cons]
    rw [ih', h1]
    ring

lemma grid_landau (L : ℕ) (hL : 0 < L) (cs ds : List ℕ) (hc : ∀ c ∈ cs ++ ds, c ∣ L)
    (hs : ds.sum ≤ cs.sum)
    (hg : ∀ v < L, (ds.map (fun d => v / (L / d))).sum ≤ (cs.map (fun c => v / (L / c))).sum)
    (n Q : ℕ) (hQ : 0 < Q) :
    (ds.map (fun d => d * n / Q)).sum ≤ (cs.map (fun c => c * n / Q)).sum := by
  rw [sum_split L Q n hL hQ cs (fun c h => hc c (List.mem_append_left _ h)),
    sum_split L Q n hL hQ ds (fun c h => hc c (List.mem_append_right _ h))]
  have hv : L * (n % Q) / Q < L := by
    apply (Nat.div_lt_iff_lt_mul hQ).mpr
    exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt n hQ) hL
  have := hg _ hv
  have := Nat.mul_le_mul_right (n / Q) hs
  omega

/-- Landau-type divisibility for factorials of `k * n / 2`. -/
lemma half_dvd (L : ℕ) (hL : 0 < L) (cs ds : List ℕ) (hc : ∀ c ∈ cs ++ ds, c ∣ L)
    (hs : ds.sum ≤ cs.sum)
    (hg : ∀ v < L, (ds.map (fun d => v / (L / d))).sum ≤ (cs.map (fun c => v / (L / c))).sum)
    (n : ℕ) :
    ((ds.map (fun k => k * n / 2)).map Nat.factorial).prod ∣
      ((cs.map (fun k => k * n / 2)).map Nat.factorial).prod := by
  apply factorial_prod_dvd_of_floor
  intro q hq
  simp only [List.map_map, Function.comp_def, Nat.div_div_eq_div_mul]
  exact grid_landau L hL cs ds hc hs hg n (2 * q) (by omega)

lemma ffact_nat (n : ℕ) : ffact (n : ℝ) = (n.factorial : ℝ) := by
  simp [ffact, Real.Gamma_nat_eq_factorial]

lemma ffact_half_even (t : ℕ) (ht : t % 2 = 0) : ffact ((t : ℝ) / 2) = ((t / 2).factorial : ℝ) := by
  have he : (t : ℝ) / 2 = ((t / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero ht) (by norm_num)]; norm_num
  rw [he, ffact_nat]

lemma ffact_half_odd (t : ℕ) (ht : t % 2 = 1) :
    ffact ((t : ℝ) / 2) = (t.factorial : ℝ) * Real.Gamma (1/2) / (2^t * ((t/2).factorial : ℝ)) := by
  obtain ⟨h, rfl⟩ : ∃ h, t = 2*h+1 := ⟨t/2, by omega⟩
  rw [show (2*h+1)/2 = h by omega]
  rw [ffact, show ((2 * h + 1 : ℕ) : ℝ) / 2 + 1 = (h : ℝ) + 1 + 1/2 by push_cast; ring,
    Real.Gamma_nat_add_one_add_half, Real.Gamma_one_half_eq,
    Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  push_cast
  rw [show 2*h+1 = h+h+1 by omega]
  simp only [pow_add, pow_one]
  field_simp


set_option maxRecDepth 20000 in
lemma half_case : ∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2) * ffact (3 * (n : ℝ) / 2) / (ffact (15 * (n : ℝ) / 2) * ffact (5 * (n : ℝ)) * ffact (7 * (n : ℝ) / 2) * ffact (3 * (n : ℝ))) = z := by
  intro n
  rw [show (3 : ℝ) * n = ((3 * n : ℕ) : ℝ) by push_cast; ring, show (5 : ℝ) * n = ((5 * n : ℕ) : ℝ) by push_cast; ring, show (7 : ℝ) * n = ((7 * n : ℕ) : ℝ) by push_cast; ring, show (15 : ℝ) * n = ((15 * n : ℕ) : ℝ) by push_cast; ring]
  simp only [ffact_nat]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · -- n even: the integral factorial ratio at n / 2
    rw [ffact_half_even (5 * n) (by omega), ffact_half_even (3 * n) (by omega), ffact_half_even (15 * n) (by omega), ffact_half_even (7 * n) (by omega)]
    have hd := half_dvd 210 (by norm_num) [30, 5, 3] [15, 10, 7, 6] (by decide) (by decide) (by decide) n
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hd
    rw [show 6 * n / 2 = 3 * n by omega, show 10 * n / 2 = 5 * n by omega, show 30 * n / 2 = 15 * n by omega] at hd
    obtain ⟨z, hz⟩ := quotient_cast_integral hd (by positivity)
    refine ⟨z, ?_⟩
    rw [hz]
    push_cast
    field_simp
  · -- n odd: Legendre duplication turns each half-integer factorial into integer ones
    rw [ffact_half_odd (5 * n) (by omega), ffact_half_odd (3 * n) (by omega), ffact_half_odd (15 * n) (by omega), ffact_half_odd (7 * n) (by omega)]
    have hd := half_dvd 210 (by norm_num) [30, 10, 6, 15, 7] [5, 3, 30, 10, 14, 6] (by decide) (by decide) (by decide) n
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hd
    rw [show 6 * n / 2 = 3 * n by omega, show 10 * n / 2 = 5 * n by omega, show 14 * n / 2 = 7 * n by omega, show 30 * n / 2 = 15 * n by omega] at hd
    obtain ⟨z, hz⟩ := quotient_cast_integral hd (by positivity)
    refine ⟨2 ^ (14 * n) * z, ?_⟩
    push_cast
    rw [hz]
    push_cast
    have hG : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp
    ring

end A295464P

theorem OMA.solution : type_of% @OMA.S_oeis_a295464.main := A295464P.half_case
