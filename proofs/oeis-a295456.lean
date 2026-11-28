import OMAStatements.S_oeis_a295456
import Mathlib

/-!
Proof of Peter Bala's fractional-index integrality conjecture for OEIS A295456.

Method. For even n the quantity is the integral factorial ratio a(n/2). For odd n, Legendre's
duplication formula, in the form Gamma(t/2 + 1) = t! Gamma(1/2) / (2^t (t div 2)!) for odd t,
turns every half-integer factorial into integer ones; the factors Gamma(1/2) cancel and what is
left is 2^E times a ratio of factorials of k*n/2 (natural division). Its integrality follows from
Legendre's formula once the Landau step-function inequality
  sum over the denominator of floor(k*n/Q) <= sum over the numerator of floor(k*n/Q)
holds for every Q; reducing n modulo Q puts this on a finite grid that the kernel checks by
`decide`.

For the arguments with denominator 3 and n prime to 3, each fractional factorial of the
numerator is paired with one of the denominator with the same fractional part; their quotient is
a power of 3 times a product of an arithmetic progression with difference 3 (`ffact_prog`).
For a prime p not dividing 3, the p-adic valuation of such a progression counts the multiples of
p^k in a residue class of an interval (`cnt_closed`); the resulting local inequality is reduced
modulo 3*p^k to a finite grid checked by `decide +kernel` (`core`, `local_ineq`). For p dividing
3 the progressions are prime to p and the integer factorials satisfy Landau's inequality.

Attribution. The lemmas factorial_prod_ne_zero, padic_prod_factorial, factorial_prod_dvd_of_floor,
quotient_cast_integral, mul_div_reduce and grid_floor, and the proof of ffact_half_odd, are adapted
from the-omega-institute/trureturing, file
D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.lean, and
padic_eq_card, padic_finset_prod and the bijection in cnt_closed from
D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.lean (commit
ff444aeb6b57ff09b8e46cfa5b8e62baf80d7efa), Copyright the-omega-institute contributors, used under the
Apache License, Version 2.0. The remaining lemmas and the assembly for this entry are new.
-/

namespace A295456P

open OMA.S_oeis_a295456

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


/-! Progression products for the fractional arguments with denominator 3. -/

def prog (a m : ℕ) : ℕ := ∏ k ∈ Finset.range m, (a + 3 * (k + 1))

lemma prog_ne_zero (a m : ℕ) : prog a m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun k _ => by omega)

lemma ffact_pos (x : ℝ) (hx : 0 ≤ x) : 0 < ffact x := Real.Gamma_pos_of_pos (by linarith)

lemma ffact_prog (a m : ℕ) :
    ffact (((a + 3 * m : ℕ) : ℝ) / 3) = ffact ((a : ℝ) / 3) * (prog a m : ℝ) / (3 : ℝ) ^ m := by
  induction m with
  | zero => simp [prog]
  | succ m ih =>
    have h1 : ((a + 3 * (m + 1) : ℕ) : ℝ) / 3 = ((a + 3 * m : ℕ) : ℝ) / 3 + 1 := by
      push_cast; field_simp; ring
    have hy : (0 : ℝ) ≤ ((a + 3 * m : ℕ) : ℝ) / 3 := by positivity
    rw [h1, ffact, Real.Gamma_add_one (by positivity), ← ffact, ih]
    simp only [prog, Finset.prod_range_succ]
    push_cast
    field_simp
    ring

def cntp (a m q : ℕ) : ℕ := ((Finset.range m).filter (fun j => q ∣ a + 3 * (j + 1))).card

lemma padic_eq_card (p n b : ℕ) [hp : Fact p.Prime] (hn : 0 < n) (hb : p.log n < b) :
    padicValNat p n = ((Finset.Ico 1 b).filter (fun k => p ^ k ∣ n)).card := by
  exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) hn.ne') ▸
    Nat.emultiplicity_eq_card_pow_dvd hp.out.ne_one hn hb)

lemma padic_finset_prod {ι : Type*} (p : ℕ) [hp : Fact p.Prime] (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    padicValNat p (∏ i ∈ S, f i) = ∑ i ∈ S, padicValNat p (f i) := by
  have hh : (padicValNat p (∏ i ∈ S, f i) : ℕ∞) =
      ((∑ i ∈ S, padicValNat p (f i) : ℕ) : ℕ∞) := by
    rw [padicValNat_eq_emultiplicity (Finset.prod_ne_zero_iff.mpr hf), Nat.cast_sum]
    exact (Finset.emultiplicity_prod (Nat.prime_iff.mp hp.out) S f).trans
      (Finset.sum_congr rfl (fun i hi => (padicValNat_eq_emultiplicity (hf i hi)).symm))
  exact_mod_cast hh

lemma padic_prog (p a m K : ℕ) [hp : Fact p.Prime] (hK : a + 3 * m < K) :
    padicValNat p (prog a m) = ∑ k ∈ Finset.Ico 1 K, cntp a m (p ^ k) := by
  classical
  rw [prog, padic_finset_prod p _ _ (by intro i _; omega)]
  have one (j : ℕ) (hj : j ∈ Finset.range m) :
      padicValNat p (a + 3 * (j + 1)) =
        ∑ k ∈ Finset.Ico 1 K, if p ^ k ∣ a + 3 * (j + 1) then 1 else 0 := by
    simp only [Finset.mem_range] at hj
    rw [padic_eq_card p _ K (by omega) (lt_of_le_of_lt (p.log_le_self _) (by nlinarith))]
    exact (Finset.sum_boole (fun k : ℕ => p ^ k ∣ a + 3 * (j + 1)) (Finset.Ico 1 K)).symm
  rw [Finset.sum_congr rfl one, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [cntp, Finset.card_filter]

lemma list_sum_swap {α : Type*} (L : List α) (s : Finset ℕ) (g : α → ℕ → ℕ) :
    (L.map (fun x => ∑ k ∈ s, g x k)).sum = ∑ k ∈ s, (L.map (fun x => g x k)).sum := by
  induction L with
  | nil => simp
  | cons x L ih => simp [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

lemma padic_list_prod {α : Type*} (p : ℕ) [hp : Fact p.Prime] (L : List α) (f : α → ℕ)
    (hf : ∀ x, f x ≠ 0) :
    padicValNat p (L.map f).prod = (L.map (fun x => padicValNat p (f x))).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    rw [padicValNat.mul (hf x) (by simp [List.prod_eq_zero_iff, hf]), ih]

lemma mixed_dvd (A B : List ℕ) (PN PD : List (ℕ × ℕ))
    (h : ∀ p k : ℕ, p.Prime → 1 ≤ k →
      (B.map (fun x => x / p ^ k)).sum + (PD.map (fun x => cntp x.1 x.2 (p ^ k))).sum ≤
        (A.map (fun x => x / p ^ k)).sum + (PN.map (fun x => cntp x.1 x.2 (p ^ k))).sum) :
    (B.map Nat.factorial).prod * (PD.map (fun x => prog x.1 x.2)).prod ∣
      (A.map Nat.factorial).prod * (PN.map (fun x => prog x.1 x.2)).prod := by
  classical
  have nzF : ∀ L : List ℕ, (L.map Nat.factorial).prod ≠ 0 := fun L => by
    simp [List.prod_eq_zero_iff, Nat.factorial_ne_zero]
  have nzP : ∀ L : List (ℕ × ℕ), (L.map (fun x => prog x.1 x.2)).prod ≠ 0 := fun L => by
    simp [List.prod_eq_zero_iff, prog_ne_zero]
  apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero (nzF B) (nzP PD))
    (mul_ne_zero (nzF A) (nzP PN))).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    padicValNat.mul (nzF B) (nzP PD), padicValNat.mul (nzF A) (nzP PN),
    padic_list_prod p B _ Nat.factorial_ne_zero, padic_list_prod p PD _ (fun x => prog_ne_zero _ _),
    padic_list_prod p A _ Nat.factorial_ne_zero, padic_list_prod p PN _ (fun x => prog_ne_zero _ _)]
  set K := (A ++ B).sum + ((PN ++ PD).map (fun x => x.1 + 3 * x.2)).sum + 1 with hK
  have vf (L : List ℕ) (hL : ∀ x ∈ L, x ∈ A ++ B) :
      (L.map (fun x => padicValNat p x.factorial)).sum =
        ∑ k ∈ Finset.Ico 1 K, (L.map (fun x => x / p ^ k)).sum := by
    rw [← list_sum_swap]
    congr 1
    apply List.map_congr_left
    intro x hx
    apply padicValNat_factorial
    have := List.le_sum_of_mem (hL x hx)
    exact lt_of_le_of_lt (p.log_le_self x) (by omega)
  have vp (L : List (ℕ × ℕ)) (hL : ∀ x ∈ L, x ∈ PN ++ PD) :
      (L.map (fun x => padicValNat p (prog x.1 x.2))).sum =
        ∑ k ∈ Finset.Ico 1 K, (L.map (fun x => cntp x.1 x.2 (p ^ k))).sum := by
    rw [← list_sum_swap]
    congr 1
    apply List.map_congr_left
    intro x hx
    apply padic_prog
    have : x.1 + 3 * x.2 ≤ ((PN ++ PD).map (fun x => x.1 + 3 * x.2)).sum :=
      List.le_sum_of_mem (List.mem_map.mpr ⟨x, hL x hx, rfl⟩)
    omega
  rw [vf B (fun x hx => List.mem_append_right A hx), vf A (fun x hx => List.mem_append_left B hx),
    vp PD (fun x hx => List.mem_append_right PN hx), vp PN (fun x hx => List.mem_append_left PD hx),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  exact h p k hp (Finset.mem_Ico.mp hk).1

lemma rcount (lo r : ℕ) (hr : r < 3) (k : ℕ) :
    ((Finset.Ioc lo (lo + k)).filter (fun l => l % 3 = r)).card =
      (lo + k + 3 - r) / 3 - (lo + 3 - r) / 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [show lo + (k + 1) = (lo + k) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih]
    split_ifs with hh <;> omega

lemma cnt_closed (al c be n q : ℕ) (hq : 0 < q) (hqD : q % 3 = 1 ∨ q % 3 = 2)
    (hab : al * n + 3 * (c * n) = be * n) :
    cntp (al * n) (c * n) q =
      (be * n / q + 3 - al * n * q % 3) / 3 - (al * n / q + 3 - al * n * q % 3) / 3 := by
  classical
  have key : cntp (al * n) (c * n) q =
      ((Finset.Ioc (al * n / q) (be * n / q)).filter (fun l => l % 3 = al * n * q % 3)).card := by
    apply Finset.card_bij (fun j _ => (al * n + 3 * (j + 1)) / q)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      have he : q * ((al * n + 3 * (j + 1)) / q) = al * n + 3 * (j + 1) := Nat.mul_div_cancel' hj.2
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨(Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith),
        (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)⟩, ?_⟩
      set l := (al * n + 3 * (j + 1)) / q
      have hm : q * l % 3 = al * n % 3 := by rw [he]; omega
      rw [Nat.mul_mod] at hm
      rw [Nat.mul_mod (al * n) q]
      rcases hqD with h | h <;> rw [h] at hm ⊢ <;> omega
    · intro j hj k hk heq
      simp only [Finset.mem_filter, Finset.mem_range] at hj hk
      have hej := Nat.mul_div_cancel' hj.2
      have hek := Nat.mul_div_cancel' hk.2
      rw [heq] at hej
      omega
    · intro l hl
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hl
      have hlo : al * n < q * l := by
        have := (Nat.div_lt_iff_lt_mul hq).mp hl.1.1
        nlinarith
      have hhi : q * l ≤ be * n := by
        have := (Nat.le_div_iff_mul_le hq).mp hl.1.2
        nlinarith
      have hm : q * l % 3 = al * n % 3 := by
        have h2 := hl.2
        rw [Nat.mul_mod (al * n) q] at h2
        rw [Nat.mul_mod]
        rcases hqD with h | h <;> rw [h] at h2 ⊢ <;> omega
      set w := q * l
      set t := (w - al * n) / 3
      have ht : w = al * n + 3 * t := by omega
      have htpos : 0 < t := by omega
      have htmax : t ≤ c * n := by omega
      refine ⟨t - 1, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_range]
        refine ⟨by omega, ?_⟩
        rw [show al * n + 3 * (t - 1 + 1) = w by omega]
        exact dvd_mul_right q l
      · rw [show al * n + 3 * (t - 1 + 1) = q * l by omega, Nat.mul_div_right _ hq]
  have hle : al * n / q ≤ be * n / q := Nat.div_le_div_right (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [key, hk, rcount _ _ (Nat.mod_lt _ (by norm_num)) k]

lemma cnt_zero (a m k : ℕ) (hk : 1 ≤ k) (ha : a % 3 ≠ 0) : cntp a m (3 ^ k) = 0 := by
  rw [cntp, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  have : 3 ∣ a + 3 * (j + 1) := (dvd_pow_self 3 (by omega)).trans hj
  omega

lemma pow_mod_D (p k : ℕ) (hp : p.Prime) (hp0 : p ≠ 3) : (p ^ k) % 3 = 1 ∨ (p ^ k) % 3 = 2 := by
  have h : ¬ 3 ∣ p ^ k := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.Prime.dvd_of_dvd_pow (by norm_num) h)
    exact hp0 this.symm
  omega

set_option maxRecDepth 20000 in
lemma half_case : ∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2) * ffact (2 * (n : ℝ)) / (ffact (15 * (n : ℝ) / 2) * ffact (6 * (n : ℝ)) * ffact (5 * (n : ℝ)) * ffact ((n : ℝ))) = z := by
  intro n
  rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by push_cast; ring, show (5 : ℝ) * n = ((5 * n : ℕ) : ℝ) by push_cast; ring, show (6 : ℝ) * n = ((6 * n : ℕ) : ℝ) by push_cast; ring, show (15 : ℝ) * n = ((15 * n : ℕ) : ℝ) by push_cast; ring]
  simp only [ffact_nat]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · -- n even: the integral factorial ratio at n / 2
    rw [ffact_half_even (5 * n) (by omega), ffact_half_even (15 * n) (by omega)]
    have hd := half_dvd 60 (by norm_num) [30, 5, 4] [15, 12, 10, 2] (by decide) (by decide) (by decide) n
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hd
    rw [show 2 * n / 2 = n by omega, show 4 * n / 2 = 2 * n by omega, show 10 * n / 2 = 5 * n by omega, show 12 * n / 2 = 6 * n by omega, show 30 * n / 2 = 15 * n by omega] at hd
    obtain ⟨z, hz⟩ := quotient_cast_integral hd (by positivity)
    refine ⟨z, ?_⟩
    rw [hz]
    push_cast
    field_simp
  · -- n odd: Legendre duplication turns each half-integer factorial into integer ones
    rw [ffact_half_odd (5 * n) (by omega), ffact_half_odd (15 * n) (by omega)]
    have hd := half_dvd 60 (by norm_num) [30, 10, 4, 15] [5, 30, 12, 10, 2] (by decide) (by decide) (by decide) n
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hd
    rw [show 2 * n / 2 = n by omega, show 4 * n / 2 = 2 * n by omega, show 10 * n / 2 = 5 * n by omega, show 12 * n / 2 = 6 * n by omega, show 30 * n / 2 = 15 * n by omega] at hd
    obtain ⟨z, hz⟩ := quotient_cast_integral hd (by positivity)
    refine ⟨2 ^ (10 * n) * z, ?_⟩
    push_cast
    rw [hz]
    push_cast
    have hG : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp
    ring

set_option maxRecDepth 20000 in
lemma core0 (t v : ℕ) (hv : v < 60) :
    ((15 * t + v / 4) + (12 * t + v / 5)) + (((30 * t + v / 2 + 3 - 1) / 3 - (12 * t + v / 5 + 3 - 1) / 3)) ≤ ((30 * t + v / 2)) + (((15 * t + v / 4 + 3 - 2) / 3 - (6 * t + v / 10 + 3 - 2) / 3)) := by
  have key : ∀ w < 60, (w / 4 + w / 5) + (((w / 2 + 3 - 1) / 3 - (w / 5 + 3 - 1) / 3)) ≤ (w / 2) + (((w / 4 + 3 - 2) / 3 - (w / 10 + 3 - 2) / 3)) ∧ (w / 10 + 3 - 2) / 3 ≤ (w / 4 + 3 - 2) / 3 ∧ (w / 5 + 3 - 1) / 3 ≤ (w / 2 + 3 - 1) / 3 := by decide +kernel
  have k := key v hv
  have s0_2 : (6 * t + v / 10 + 3 - 2) / 3 = 2 * t + (v / 10 + 3 - 2) / 3 := by omega
  have s0_5 : (15 * t + v / 4 + 3 - 2) / 3 = 5 * t + (v / 4 + 3 - 2) / 3 := by omega
  have s1_4 : (12 * t + v / 5 + 3 - 1) / 3 = 4 * t + (v / 5 + 3 - 1) / 3 := by omega
  have s1_10 : (30 * t + v / 2 + 3 - 1) / 3 = 10 * t + (v / 2 + 3 - 1) / 3 := by omega
  rw [s0_2, s0_5, s1_4, s1_10]
  generalize (v / 10 + 3 - 2) / 3 = y0 at k ⊢
  generalize (v / 4 + 3 - 2) / 3 = y1 at k ⊢
  generalize (v / 5 + 3 - 1) / 3 = y2 at k ⊢
  generalize (v / 2 + 3 - 1) / 3 = y3 at k ⊢
  generalize v / 2 = x2 at k ⊢
  generalize v / 4 = x4 at k ⊢
  generalize v / 5 = x5 at k ⊢
  generalize v / 10 = x10 at k ⊢
  omega

set_option maxRecDepth 20000 in
lemma core1 (t v : ℕ) (hv : v < 60) :
    ((15 * t + v / 4) + (12 * t + v / 5)) + (((30 * t + v / 2 + 3 - 2) / 3 - (12 * t + v / 5 + 3 - 2) / 3)) ≤ ((30 * t + v / 2)) + (((15 * t + v / 4 + 3 - 1) / 3 - (6 * t + v / 10 + 3 - 1) / 3)) := by
  have key : ∀ w < 60, (w / 4 + w / 5) + (((w / 2 + 3 - 2) / 3 - (w / 5 + 3 - 2) / 3)) ≤ (w / 2) + (((w / 4 + 3 - 1) / 3 - (w / 10 + 3 - 1) / 3)) ∧ (w / 10 + 3 - 1) / 3 ≤ (w / 4 + 3 - 1) / 3 ∧ (w / 5 + 3 - 2) / 3 ≤ (w / 2 + 3 - 2) / 3 := by decide +kernel
  have k := key v hv
  have s0_2 : (6 * t + v / 10 + 3 - 1) / 3 = 2 * t + (v / 10 + 3 - 1) / 3 := by omega
  have s0_5 : (15 * t + v / 4 + 3 - 1) / 3 = 5 * t + (v / 4 + 3 - 1) / 3 := by omega
  have s1_4 : (12 * t + v / 5 + 3 - 2) / 3 = 4 * t + (v / 5 + 3 - 2) / 3 := by omega
  have s1_10 : (30 * t + v / 2 + 3 - 2) / 3 = 10 * t + (v / 2 + 3 - 2) / 3 := by omega
  rw [s0_2, s0_5, s1_4, s1_10]
  generalize (v / 10 + 3 - 1) / 3 = y0 at k ⊢
  generalize (v / 4 + 3 - 1) / 3 = y1 at k ⊢
  generalize (v / 5 + 3 - 2) / 3 = y2 at k ⊢
  generalize (v / 2 + 3 - 2) / 3 = y3 at k ⊢
  generalize v / 2 = x2 at k ⊢
  generalize v / 4 = x4 at k ⊢
  generalize v / 5 = x5 at k ⊢
  generalize v / 10 = x10 at k ⊢
  omega

set_option maxRecDepth 20000 in
lemma core2 (t v : ℕ) (hv : v < 60) :
    ((15 * t + v / 4) + (12 * t + v / 5)) + (((30 * t + v / 2 + 3 - 2) / 3 - (12 * t + v / 5 + 3 - 2) / 3)) ≤ ((30 * t + v / 2)) + (((15 * t + v / 4 + 3 - 1) / 3 - (6 * t + v / 10 + 3 - 1) / 3)) := by
  have key : ∀ w < 60, (w / 4 + w / 5) + (((w / 2 + 3 - 2) / 3 - (w / 5 + 3 - 2) / 3)) ≤ (w / 2) + (((w / 4 + 3 - 1) / 3 - (w / 10 + 3 - 1) / 3)) ∧ (w / 10 + 3 - 1) / 3 ≤ (w / 4 + 3 - 1) / 3 ∧ (w / 5 + 3 - 2) / 3 ≤ (w / 2 + 3 - 2) / 3 := by decide +kernel
  have k := key v hv
  have s0_2 : (6 * t + v / 10 + 3 - 1) / 3 = 2 * t + (v / 10 + 3 - 1) / 3 := by omega
  have s0_5 : (15 * t + v / 4 + 3 - 1) / 3 = 5 * t + (v / 4 + 3 - 1) / 3 := by omega
  have s1_4 : (12 * t + v / 5 + 3 - 2) / 3 = 4 * t + (v / 5 + 3 - 2) / 3 := by omega
  have s1_10 : (30 * t + v / 2 + 3 - 2) / 3 = 10 * t + (v / 2 + 3 - 2) / 3 := by omega
  rw [s0_2, s0_5, s1_4, s1_10]
  generalize (v / 10 + 3 - 1) / 3 = y0 at k ⊢
  generalize (v / 4 + 3 - 1) / 3 = y1 at k ⊢
  generalize (v / 5 + 3 - 2) / 3 = y2 at k ⊢
  generalize (v / 2 + 3 - 2) / 3 = y3 at k ⊢
  generalize v / 2 = x2 at k ⊢
  generalize v / 4 = x4 at k ⊢
  generalize v / 5 = x5 at k ⊢
  generalize v / 10 = x10 at k ⊢
  omega

set_option maxRecDepth 20000 in
lemma core3 (t v : ℕ) (hv : v < 60) :
    ((15 * t + v / 4) + (12 * t + v / 5)) + (((30 * t + v / 2 + 3 - 1) / 3 - (12 * t + v / 5 + 3 - 1) / 3)) ≤ ((30 * t + v / 2)) + (((15 * t + v / 4 + 3 - 2) / 3 - (6 * t + v / 10 + 3 - 2) / 3)) := by
  have key : ∀ w < 60, (w / 4 + w / 5) + (((w / 2 + 3 - 1) / 3 - (w / 5 + 3 - 1) / 3)) ≤ (w / 2) + (((w / 4 + 3 - 2) / 3 - (w / 10 + 3 - 2) / 3)) ∧ (w / 10 + 3 - 2) / 3 ≤ (w / 4 + 3 - 2) / 3 ∧ (w / 5 + 3 - 1) / 3 ≤ (w / 2 + 3 - 1) / 3 := by decide +kernel
  have k := key v hv
  have s0_2 : (6 * t + v / 10 + 3 - 2) / 3 = 2 * t + (v / 10 + 3 - 2) / 3 := by omega
  have s0_5 : (15 * t + v / 4 + 3 - 2) / 3 = 5 * t + (v / 4 + 3 - 2) / 3 := by omega
  have s1_4 : (12 * t + v / 5 + 3 - 1) / 3 = 4 * t + (v / 5 + 3 - 1) / 3 := by omega
  have s1_10 : (30 * t + v / 2 + 3 - 1) / 3 = 10 * t + (v / 2 + 3 - 1) / 3 := by omega
  rw [s0_2, s0_5, s1_4, s1_10]
  generalize (v / 10 + 3 - 2) / 3 = y0 at k ⊢
  generalize (v / 4 + 3 - 2) / 3 = y1 at k ⊢
  generalize (v / 5 + 3 - 1) / 3 = y2 at k ⊢
  generalize (v / 2 + 3 - 1) / 3 = y3 at k ⊢
  generalize v / 2 = x2 at k ⊢
  generalize v / 4 = x4 at k ⊢
  generalize v / 5 = x5 at k ⊢
  generalize v / 10 = x10 at k ⊢
  omega

lemma local_ineq (n q : ℕ) (hq : 0 < q) (hqD : q % 3 = 1 ∨ q % 3 = 2)
    (hnD : n % 3 = 1 ∨ n % 3 = 2) :
    (5 * n / q + 4 * n / q) + (((10 * n / q + 3 - 4 * n * q % 3) / 3 - (4 * n / q + 3 - 4 * n * q % 3) / 3)) ≤ (10 * n / q) + (((5 * n / q + 3 - 2 * n * q % 3) / 3 - (2 * n / q + 3 - 2 * n * q % 3) / 3)) := by
  rcases hqD with hq' | hq' <;> rcases hnD with hn | hn
  · -- q % 3 = 1, n % 3 = 1
    have hr2 : 2 * n * q % 3 = 2 := by rw [Nat.mul_mod, Nat.mul_mod 2 n, hn, hq'] <;> decide
    have hr4 : 4 * n * q % 3 = 1 := by rw [Nat.mul_mod, Nat.mul_mod 4 n, hn, hq'] <;> decide
    rw [hr2, hr4]
    obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < 3 * q ∧ n = 3 * q * t + s :=
      ⟨n / (3 * q), n % (3 * q), Nat.mod_lt _ (by omega), (Nat.div_add_mod n (3 * q)).symm⟩
    have e2 : 2 * (3 * q * t + s) / q = 6 * t + 20 * s / q / 10 := by
      rw [show 2 * (3 * q * t + s) = 2 * s + q * (6 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 2 10 s q (by norm_num) (by norm_num)]
      ring
    have e4 : 4 * (3 * q * t + s) / q = 12 * t + 20 * s / q / 5 := by
      rw [show 4 * (3 * q * t + s) = 4 * s + q * (12 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 4 5 s q (by norm_num) (by norm_num)]
      ring
    have e5 : 5 * (3 * q * t + s) / q = 15 * t + 20 * s / q / 4 := by
      rw [show 5 * (3 * q * t + s) = 5 * s + q * (15 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 5 4 s q (by norm_num) (by norm_num)]
      ring
    have e10 : 10 * (3 * q * t + s) / q = 30 * t + 20 * s / q / 2 := by
      rw [show 10 * (3 * q * t + s) = 10 * s + q * (30 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 10 2 s q (by norm_num) (by norm_num)]
      ring
    try simp only [Nat.one_mul] at *
    rw [e2, e4, e5, e10]
    have hv : 20 * s / q < 60 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    generalize 20 * s / q = v at hv ⊢
    exact core0 t v hv
  · -- q % 3 = 1, n % 3 = 2
    have hr2 : 2 * n * q % 3 = 1 := by rw [Nat.mul_mod, Nat.mul_mod 2 n, hn, hq'] <;> decide
    have hr4 : 4 * n * q % 3 = 2 := by rw [Nat.mul_mod, Nat.mul_mod 4 n, hn, hq'] <;> decide
    rw [hr2, hr4]
    obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < 3 * q ∧ n = 3 * q * t + s :=
      ⟨n / (3 * q), n % (3 * q), Nat.mod_lt _ (by omega), (Nat.div_add_mod n (3 * q)).symm⟩
    have e2 : 2 * (3 * q * t + s) / q = 6 * t + 20 * s / q / 10 := by
      rw [show 2 * (3 * q * t + s) = 2 * s + q * (6 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 2 10 s q (by norm_num) (by norm_num)]
      ring
    have e4 : 4 * (3 * q * t + s) / q = 12 * t + 20 * s / q / 5 := by
      rw [show 4 * (3 * q * t + s) = 4 * s + q * (12 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 4 5 s q (by norm_num) (by norm_num)]
      ring
    have e5 : 5 * (3 * q * t + s) / q = 15 * t + 20 * s / q / 4 := by
      rw [show 5 * (3 * q * t + s) = 5 * s + q * (15 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 5 4 s q (by norm_num) (by norm_num)]
      ring
    have e10 : 10 * (3 * q * t + s) / q = 30 * t + 20 * s / q / 2 := by
      rw [show 10 * (3 * q * t + s) = 10 * s + q * (30 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 10 2 s q (by norm_num) (by norm_num)]
      ring
    try simp only [Nat.one_mul] at *
    rw [e2, e4, e5, e10]
    have hv : 20 * s / q < 60 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    generalize 20 * s / q = v at hv ⊢
    exact core1 t v hv
  · -- q % 3 = 2, n % 3 = 1
    have hr2 : 2 * n * q % 3 = 1 := by rw [Nat.mul_mod, Nat.mul_mod 2 n, hn, hq'] <;> decide
    have hr4 : 4 * n * q % 3 = 2 := by rw [Nat.mul_mod, Nat.mul_mod 4 n, hn, hq'] <;> decide
    rw [hr2, hr4]
    obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < 3 * q ∧ n = 3 * q * t + s :=
      ⟨n / (3 * q), n % (3 * q), Nat.mod_lt _ (by omega), (Nat.div_add_mod n (3 * q)).symm⟩
    have e2 : 2 * (3 * q * t + s) / q = 6 * t + 20 * s / q / 10 := by
      rw [show 2 * (3 * q * t + s) = 2 * s + q * (6 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 2 10 s q (by norm_num) (by norm_num)]
      ring
    have e4 : 4 * (3 * q * t + s) / q = 12 * t + 20 * s / q / 5 := by
      rw [show 4 * (3 * q * t + s) = 4 * s + q * (12 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 4 5 s q (by norm_num) (by norm_num)]
      ring
    have e5 : 5 * (3 * q * t + s) / q = 15 * t + 20 * s / q / 4 := by
      rw [show 5 * (3 * q * t + s) = 5 * s + q * (15 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 5 4 s q (by norm_num) (by norm_num)]
      ring
    have e10 : 10 * (3 * q * t + s) / q = 30 * t + 20 * s / q / 2 := by
      rw [show 10 * (3 * q * t + s) = 10 * s + q * (30 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 10 2 s q (by norm_num) (by norm_num)]
      ring
    try simp only [Nat.one_mul] at *
    rw [e2, e4, e5, e10]
    have hv : 20 * s / q < 60 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    generalize 20 * s / q = v at hv ⊢
    exact core2 t v hv
  · -- q % 3 = 2, n % 3 = 2
    have hr2 : 2 * n * q % 3 = 2 := by rw [Nat.mul_mod, Nat.mul_mod 2 n, hn, hq'] <;> decide
    have hr4 : 4 * n * q % 3 = 1 := by rw [Nat.mul_mod, Nat.mul_mod 4 n, hn, hq'] <;> decide
    rw [hr2, hr4]
    obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < 3 * q ∧ n = 3 * q * t + s :=
      ⟨n / (3 * q), n % (3 * q), Nat.mod_lt _ (by omega), (Nat.div_add_mod n (3 * q)).symm⟩
    have e2 : 2 * (3 * q * t + s) / q = 6 * t + 20 * s / q / 10 := by
      rw [show 2 * (3 * q * t + s) = 2 * s + q * (6 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 2 10 s q (by norm_num) (by norm_num)]
      ring
    have e4 : 4 * (3 * q * t + s) / q = 12 * t + 20 * s / q / 5 := by
      rw [show 4 * (3 * q * t + s) = 4 * s + q * (12 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 4 5 s q (by norm_num) (by norm_num)]
      ring
    have e5 : 5 * (3 * q * t + s) / q = 15 * t + 20 * s / q / 4 := by
      rw [show 5 * (3 * q * t + s) = 5 * s + q * (15 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 5 4 s q (by norm_num) (by norm_num)]
      ring
    have e10 : 10 * (3 * q * t + s) / q = 30 * t + 20 * s / q / 2 := by
      rw [show 10 * (3 * q * t + s) = 10 * s + q * (30 * t) by ring, Nat.add_mul_div_left _ _ hq,
        grid_floor 20 10 2 s q (by norm_num) (by norm_num)]
      ring
    try simp only [Nat.one_mul] at *
    rw [e2, e4, e5, e10]
    have hv : 20 * s / q < 60 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    generalize 20 * s / q = v at hv ⊢
    exact core3 t v hv

lemma frac_case : ∀ n : ℕ, ∃ z : ℤ, ffact (10 * (n : ℝ)) * ffact (5 * (n : ℝ) / 3) * ffact (4 * (n : ℝ) / 3) / (ffact (5 * (n : ℝ)) * ffact (4 * (n : ℝ)) * ffact (10 * (n : ℝ) / 3) * ffact (2 * (n : ℝ) / 3)) = z := by
  intro n
  by_cases h3 : n % 3 = 0
  · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    obtain ⟨z, hz⟩ := half_case (2 * m)
    refine ⟨z, ?_⟩
    rw [← hz]
    push_cast
    ring_nf
  have hnD : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by push_cast; ring, show (4 : ℝ) * n = ((4 * n : ℕ) : ℝ) by push_cast; ring, show (5 : ℝ) * n = ((5 * n : ℕ) : ℝ) by push_cast; ring, show (10 : ℝ) * n = ((10 * n : ℕ) : ℝ) by push_cast; ring]
  simp only [ffact_nat]
  rw [show ((5 * n : ℕ) : ℝ) = ((2 * n + 3 * (1 * n) : ℕ) : ℝ) by push_cast; ring, ffact_prog]
  rw [show ((10 * n : ℕ) : ℝ) = ((4 * n + 3 * (2 * n) : ℕ) : ℝ) by push_cast; ring, ffact_prog]
  have hd := mixed_dvd [10 * n] [5 * n, 4 * n] [(2 * n, 1 * n)] [(4 * n, 2 * n)] (by
    intro p k hp hk
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases hp0 : p = 3
    · subst hp0
      rw [cnt_zero (2 * n) (1 * n) k hk (by omega), cnt_zero (4 * n) (2 * n) k hk (by omega)]
      have hl := grid_landau 20 (by norm_num) [10] [5, 4] (by decide) (by decide) (by decide) n (3 ^ k) (by positivity)
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.one_mul] at hl
      omega
    · have hq := pow_mod_D p k hp hp0
      rw [cnt_closed 2 1 5 n (p ^ k) (pow_pos hp.pos k) hq (by ring), cnt_closed 4 2 10 n (p ^ k) (pow_pos hp.pos k) hq (by ring)]
      exact local_ineq n (p ^ k) (pow_pos hp.pos k) hq hnD)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hd
  obtain ⟨z, hz⟩ := quotient_cast_integral hd (by simp [Nat.factorial_ne_zero, prog_ne_zero])
  have hf0 : ffact (((2 * n : ℕ) : ℝ) / 3) ≠ 0 := (ffact_pos _ (by positivity)).ne'
  generalize ffact (((2 * n : ℕ) : ℝ) / 3) = F0 at hf0 ⊢
  have hf1 : ffact (((4 * n : ℕ) : ℝ) / 3) ≠ 0 := (ffact_pos _ (by positivity)).ne'
  generalize ffact (((4 * n : ℕ) : ℝ) / 3) = F1 at hf1 ⊢
  refine ⟨3 ^ (1 * n) * z, ?_⟩
  push_cast
  rw [hz]
  push_cast
  field_simp
  all_goals ring

end A295456P

theorem OMA.solution : type_of% @OMA.S_oeis_a295456.main := ⟨A295456P.half_case, A295456P.frac_case⟩
