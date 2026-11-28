import OMAReductions.R_Erdos67_erdos_67_variants_complex_R1
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The stochastic Erdős discrepancy theorem

Following Tao, *The Erdős discrepancy problem* (2016), reduce Theorem 1.8
to the two-point inverse theorem (Theorem 1.10) and the analytic comparison
with a modified Dirichlet character on good residue classes (equation (4.8)).
The finite argument following (4.8) is proved below.

Credit: @yuka30240. The logarithmic-weight estimates, continuity lemmas and
van der Corput argument are from @tkaiman's reduction Erdos67.erdos_67.R1.
-/

open Filter Finset MeasureTheory Complex
open scoped Topology Classical BigOperators ZMod

namespace OMA.R_Erdos67_erdos_67_variants_complex_R1_H2_R1

lemma period_sum_shift {E : Type*} [AddCancelCommMonoid E] {f : ℕ → E} {M : ℕ} (hf : Function.Periodic f M) (h : ℕ) :
    ∑ a ∈ range M, f (a + h) = ∑ a ∈ range M, f a := by
  induction h with
  | zero => simp
  | succ h ih =>
    have e := sum_range_succ' (fun a => f (a + h)) M
    rw [sum_range_succ] at e
    simp only [Nat.zero_add] at e
    have hp : f (M + h) = f h := by simpa [Nat.add_comm] using hf h
    rw [hp] at e
    convert (add_right_cancel e.symm).trans ih using 2 with a
    rw [Nat.succ_add, Nat.add_succ]

/-- A primitive character averages to zero against any sequence with a period
s not divisible by its conductor, over a common period N. -/
lemma primitive_twisted_sum {q s N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hqN : q ∣ N) (hqs : ¬ q ∣ s) (F : ℕ → ℂ)
    (hs : Function.Periodic F s) (hN : Function.Periodic F N) :
    ∑ x ∈ range N, χ (x : ZMod q) * F x = 0 := by
  classical
  let e (j : ZMod q) (x : ℕ) := ZMod.stdAddChar (j * (x : ZMod q))
  have he j a b : e j (a+b) = e j a * e j b := by
    simp only [e, Nat.cast_add, mul_add, AddChar.map_add_eq_mul]
  have heN j : e j N = 1 := by
    simp [e, (ZMod.natCast_eq_zero_iff N q).2 hqN]
  have kill (j : ZMod q) (hj : IsUnit j) : ∑ x ∈ range N, e j x * F x = 0 := by
    have hp : Function.Periodic (fun x => e j x * F x) N := by
      intro x
      simp [he, heN, hN x]
    have hshift := period_sum_shift hp s
    have hne : e j s ≠ 1 := by
      intro h
      have hz : j * (s : ZMod q) = 0 := ZMod.injective_stdAddChar
        (h.trans ZMod.stdAddChar.map_zero_eq_one.symm)
      exact hqs ((ZMod.natCast_eq_zero_iff s q).mp ((hj.mul_right_inj).mp (by simpa using hz)))
    have heq : e j s * (∑ x ∈ range N, e j x * F x) = ∑ x ∈ range N, e j x * F x := by
      calc
        _ = ∑ x ∈ range N, e j (x+s) * F (x+s) := by
          rw [mul_sum]
          exact sum_congr rfl fun x _ => by rw [he, hs x]; ring
        _ = _ := hshift
    have hz : (e j s - 1) * (∑ x ∈ range N, e j x * F x) = 0 := by
      rw [sub_mul, one_mul, heq, sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)
  have expand (x : ℕ) : χ (x : ZMod q) =
      ∑ j : ZMod q, ((q : ℂ)⁻¹ * 𝓕 (χ : ZMod q → ℂ) j) * e j x := by
    have hi := congrFun (ZMod.dft.symm_apply_apply (χ : ZMod q → ℂ)) (x : ZMod q)
    rw [ZMod.invDFT_apply] at hi
    rw [← hi]
    simp only [smul_eq_mul, mul_sum]
    exact sum_congr rfl fun j _ => by dsimp [e]; ring
  simp_rw [expand, sum_mul]
  rw [sum_comm]
  apply sum_eq_zero
  intro j _
  simp_rw [mul_assoc, ← mul_sum]
  by_cases hu : IsUnit j
  · simp [kill j hu]
  · have hn : ¬ IsUnit (-j) := by simpa using hu
    simp [hχ.fourierTransform_eq_inv_mul_gaussSum, MulChar.map_nonunit _ hn]

lemma layer_period {q d : ℕ} (hd : 0 < d) (χ : DirichletCharacter ℂ q) :
    Function.Periodic (fun n : ℕ => if d ∣ n then χ (((n/d : ℕ) : ZMod q)) else 0) (d*q) := by
  intro n
  simp only [← Nat.dvd_add_iff_left (dvd_mul_right d q), Nat.add_mul_div_left n q hd,
    Nat.cast_add, ZMod.natCast_self, add_zero]

lemma sum_at_multiples {E : Type*} [AddCommMonoid E] {d : ℕ} (hd : 0 < d) (K : ℕ) (f : ℕ → E) :
    ∑ n ∈ range (d*K), (if d ∣ n then f (n/d) else 0) = ∑ b ∈ range K, f b := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    rw [sum_eq_single 0]
    · simp [Nat.mul_div_cancel_left _ hd]
    · intro m hm hm0
      apply if_neg
      rw [← Nat.dvd_add_iff_right (dvd_mul_right d K)]
      exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hm0) (mem_range.mp hm)
    · simp [hd]

lemma separates_periods {q d b K : ℕ} (hq : 0 < q) (hd : 0 < d)
    (hdK : d ∣ q^K) (hdb : ¬ d ∣ b) :
    ∃ s : ℕ, ¬ q ∣ s ∧ b*q ∣ d*s := by
  let g := Nat.gcd d b
  let u := d/g
  let v := b/g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hd
  have hdu : u*g = d := Nat.div_mul_cancel (Nat.gcd_dvd_left d b)
  have hbv : v*g = b := Nat.div_mul_cancel (Nat.gcd_dvd_right d b)
  have hcop : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg
  have hu : u ≠ 1 := by
    intro h
    have hgd : g = d := by simpa [h] using hdu
    exact hdb (hgd ▸ Nat.gcd_dvd_right d b)
  obtain ⟨p, hp, hpu⟩ := Nat.exists_prime_and_dvd hu
  have hpq : p ∣ q := hp.dvd_of_dvd_pow (hpu.trans ((Dvd.intro g hdu).trans hdK))
  have hpv : ¬ p ∣ v := fun h => hp.not_dvd_one (hcop ▸ Nat.dvd_gcd hpu h)
  let w := q/p
  have hw : w*p = q := Nat.div_mul_cancel hpq
  have hwpos : 0 < w := Nat.div_pos (Nat.le_of_dvd hq hpq) hp.pos
  refine ⟨w*v, ?_, ?_⟩
  · intro h
    rw [← hw] at h
    exact hpv (Nat.dvd_of_mul_dvd_mul_left hwpos h)
  · obtain ⟨c,hc⟩ := hpu
    refine ⟨c, ?_⟩
    rw [← hdu, ← hbv, ← hw, hc]
    ring

lemma period_of_dvd {E : Type*} {f : ℕ → E} {d M : ℕ}
    (h : Function.Periodic f d) (hd : d ∣ M) : Function.Periodic f M := by
  obtain ⟨k, rfl⟩ := hd
  simpa [Nat.mul_comm] using h.nat_mul k

lemma sparse_shift_cancel {q d b K : ℕ} (hq : 0 < q) (hd : d ∣ q^K)
    (hb : b ∣ q^K) (hdb : ¬ d ∣ b) (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (F : ℕ → ℂ) (hF : Function.Periodic F (b*q)) (j : ℕ) :
    ∑ a ∈ range (q^(K+1)), (if d ∣ a+j then χ ((((a+j)/d : ℕ) : ZMod q)) else 0) * F a = 0 := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let M := q^(K+1)
  let V (a : ℕ) : ℂ := if d ∣ a then χ (((a/d : ℕ) : ZMod q)) else 0
  have hdp := Nat.pos_of_dvd_of_pos hd (pow_pos hq K)
  have hbp := Nat.pos_of_dvd_of_pos hb (pow_pos hq K)
  have hDM : d*q ∣ M := by simpa [M, pow_succ] using mul_dvd_mul_right hd q
  have hBM : b*q ∣ M := by simpa [M, pow_succ] using mul_dvd_mul_right hb q
  have hVM : Function.Periodic V M := period_of_dvd (layer_period hdp χ) hDM
  have hFM := period_of_dvd hF hBM
  let shift := (b*q)*(j+1) - j
  have ha : shift+j = (j+1)*(b*q) := by
    have hle := Nat.le_mul_of_pos_left (j+1) (Nat.mul_pos hbp hq)
    dsimp [shift]
    rw [Nat.mul_comm (b*q)]
    rw [Nat.mul_comm (j+1) (b*q)] at *
    omega
  let G (x : ℕ) := F (x+shift)
  have hG : Function.Periodic G (b*q) := fun n => by
    simpa only [G, Nat.add_right_comm n (b*q) shift] using hF (n+shift)
  have hGM := period_of_dvd hG hBM
  have hGj a : G (a+j) = F a := by
    change F (a+j+shift) = F a
    rw [Nat.add_right_comm, Nat.add_assoc, ha]
    exact hF.nat_mul (j+1) a
  have unshift : ∑ a ∈ range M, V (a+j) * F a = ∑ a ∈ range M, V a * G a := by
    simpa only [Pi.mul_apply, hGj] using period_sum_shift (hVM.mul hGM) j
  change ∑ a ∈ range M, V (a+j) * F a = 0
  rw [unshift]
  let N := M/d
  have hdM : d ∣ M := (dvd_mul_right d q).trans hDM
  have hdN : d*N = M := Nat.mul_div_cancel' hdM
  have hqN : q ∣ N := (Nat.dvd_div_iff_mul_dvd hdM).mpr hDM
  have eqsum : ∑ a ∈ range M, V a * G a = ∑ x ∈ range N, χ (x : ZMod q) * G (d*x) := by
    rw [← sum_at_multiples hdp N, hdN]
    apply sum_congr rfl
    intro a _
    by_cases h : d ∣ a
    · simp [V, h, Nat.mul_div_cancel' h]
    · simp [V, h]
  rw [eqsum]
  obtain ⟨s, hqs, hds⟩ := separates_periods hq hdp hd hdb
  apply primitive_twisted_sum χ hχ hqN hqs (fun x => G (d*x))
  · intro a
    dsimp only
    rw [Nat.mul_add]
    exact period_of_dvd hG hds (d*a)
  · intro a
    dsimp only
    rw [Nat.mul_add, hdN]
    exact hGM (d*a)

/-- Window sums of distinct divisor layers of a primitive character are orthogonal
over one complete residue system. This is Tao's cancellation (4.11). -/
lemma orthogonal_windows {q K : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (h : ℕ) :
    let V (d a : ℕ) := ∑ m ∈ range h,
      if d ∣ a + m + 1 then χ ((((a+m+1)/d : ℕ) : ZMod q)) else 0
    ∀ d ∈ (q^K).divisors, ∀ b ∈ (q^K).divisors, d ≠ b →
      ∑ a ∈ range (q^(K+1)), V d a * star (V b a) = 0 := by
  intro V
  have cancel {d b : ℕ} (hd : d ∣ q^K) (hb : b ∣ q^K) (hdb : ¬ d ∣ b) :
      ∑ a ∈ range (q^(K+1)), V d a * star (V b a) = 0 := by
    let F (a : ℕ) := star (V b a)
    have hper : Function.Periodic F (b*q) := by
      intro a
      apply congrArg star
      apply sum_congr rfl
      intro m _
      have e := layer_period (Nat.pos_of_dvd_of_pos hb (pow_pos hq K)) χ (a+m+1)
      simpa only [show a + b*q + m + 1 = (a+m+1) + b*q by omega] using e
    change ∑ a ∈ range (q^(K+1)), V d a * F a = 0
    simp only [V, sum_mul]
    rw [sum_comm]
    apply sum_eq_zero
    intro m _
    simpa only [Nat.add_assoc] using sparse_shift_cancel hq hd hb hdb χ hχ F hper (m+1)
  intro d hd b hb hne
  have hd' := (Nat.mem_divisors.mp hd).1
  have hb' := (Nat.mem_divisors.mp hb).1
  by_cases hdb : d ∣ b
  · have e := congrArg (starRingEnd ℂ) (cancel hb' hd' (fun h => hne (Nat.dvd_antisymm hdb h)))
    simpa [Complex.star_def, mul_comm] using e
  · exact cancel hd' hb' hdb

lemma sum_norm_sq_orthogonal (D : Finset ℕ) (M : ℕ) (V : ℕ → ℕ → ℂ) (c : ℕ → ℂ)
    (hc : ∀ d ∈ D, ‖c d‖ = 1)
    (ho : ∀ d ∈ D, ∀ b ∈ D, d ≠ b → ∑ a ∈ range M, V d a * star (V b a) = 0) :
    ∑ a ∈ range M, ‖∑ d ∈ D, c d * V d a‖ ^ 2 =
      ∑ d ∈ D, ∑ a ∈ range M, ‖V d a‖ ^ 2 := by
  classical
  let W d a := c d * V d a
  have pair (d : ℕ) (hd : d ∈ D) (b : ℕ) (hb : b ∈ D) (hne : d ≠ b) :
      ∑ a ∈ range M, W d a * star (W b a) = 0 := by
    have factor a : W d a * star (W b a) =
        (c d * star (c b)) * (V d a * star (V b a)) := by simp [W, star_mul]; ring
    simp_rw [factor, ← mul_sum, ho d hd b hb hne, mul_zero]
  have diag d (hd : d ∈ D) (a : ℕ) :
      W d a * star (W d a) = ((‖V d a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj']
    simp [W, hc d hd]
  have sqcast (v : ℂ) : ((‖v‖^2 : ℝ) : ℂ) = v * star v := by
    rw [Complex.star_def, Complex.mul_conj', Complex.ofReal_pow]
  apply Complex.ofReal_inj.mp
  simp only [Complex.ofReal_sum]
  change ∑ a ∈ range M, ((‖∑ d ∈ D, W d a‖ ^ 2 : ℝ) : ℂ) = _
  simp_rw [sqcast (∑ _ ∈ _, _), star_sum, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm, sum_eq_single d]
  · exact sum_congr rfl (fun a _ => diag d hd a)
  · intro b hb hbd
    exact pair d hd b hb hbd.symm
  · exact fun he => (he hd).elim

/-- The coprime quotient condition singles out the gcd layer, even on bad residues. -/
lemma divisor_expansion {q : ℕ} (hq : 0 < q) (K n : ℕ) (χ : DirichletCharacter ℂ q)
    (u : ℕ → ℂ) :
    ∑ d ∈ (q^K).divisors, u d *
      (if d ∣ n then χ (((n/d : ℕ) : ZMod q)) else 0) =
        u (n.gcd (q^K)) * χ (((n / n.gcd (q^K) : ℕ) : ZMod q)) := by
  classical
  let g := n.gcd (q^K)
  have hgD : g ∈ (q^K).divisors := Nat.mem_divisors.mpr
    ⟨Nat.gcd_dvd_right _ _, (pow_pos hq K).ne'⟩
  rw [sum_eq_single g]
  · rw [if_pos (Nat.gcd_dvd_left _ _)]
  · intro d hd hne
    by_cases hdn : d ∣ n
    · rw [if_pos hdn]
      apply mul_eq_zero_of_right
      apply χ.map_nonunit
      intro hu
      have cop := (ZMod.isUnit_iff_coprime (n/d) q).mp hu
      have cop' : g.Coprime (n/d) :=
        (cop.symm.pow_left K).coprime_dvd_left (Nat.gcd_dvd_right _ _)
      have hgd : g ∣ d := cop'.dvd_of_dvd_mul_right (by
        rw [Nat.mul_div_cancel' hdn]; exact Nat.gcd_dvd_left _ _)
      exact hne (Nat.dvd_antisymm (Nat.dvd_gcd hdn (Nat.mem_divisors.mp hd).1) hgd)
    · simp [hdn]
  · exact fun h => (h hgD).elim

lemma coprime_quotient_on_good {q : ℕ} (hq : 0 < q) (K n : ℕ)
    (hgood : ∀ p ∈ q.primeFactors, ¬ p^(K+1) ∣ n) :
    (n / n.gcd (q^K)).Coprime q := by
  by_contra h
  obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  let g := n.gcd (q^K)
  have hg : 0 < g := Nat.gcd_pos_of_pos_right _ (pow_pos hq K)
  have hcop := Nat.coprime_div_gcd_div_gcd (m := n) (n := q^K) hg
  have hpe : p.Coprime (q^K/g) := hcop.coprime_dvd_left hpn
  have hgd := Nat.gcd_dvd_right n (q^K)
  have hpow : p^K ∣ g := (hpe.pow_left K).dvd_of_dvd_mul_right (by
    rw [Nat.mul_div_cancel' hgd]; exact pow_dvd_pow_of_dvd hpq K)
  apply hgood p (Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩)
  rw [pow_succ]
  simpa only [g, Nat.mul_div_cancel' (Nat.gcd_dvd_left n (q^K))] using Nat.mul_dvd_mul hpow hpn

lemma reciprocal_prime_power_count {q K : ℕ} (hq : 0 < q) (m : ℕ) :
    let M := q^(K+1)
    ∑ p ∈ q.primeFactors, ∑ a ∈ range M,
      (if p^(K+1) ∣ a+m+1 then (1 : ℝ) else 0) ≤ (q : ℝ) * M / 2^(K+1) := by
  intro M
  have count p (hp : p ∈ q.primeFactors) :
      ∑ a ∈ range M, (if p^(K+1) ∣ a+m+1 then (1 : ℝ) else 0) ≤ M / (2:ℝ)^(K+1) := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    let P := p^(K+1)
    have hP := pow_pos hprime.pos (K+1)
    have hd : P ∣ M := pow_dvd_pow_of_dvd (Nat.dvd_of_mem_primeFactors hp) _
    let f (a : ℕ) : ℝ := if P ∣ a then 1 else 0
    have hper : Function.Periodic f M := by
      intro x
      simp only [f, ← Nat.dvd_add_iff_left hd]
    have shift := period_sum_shift hper (m+1)
    change ∑ a ∈ range M, (if P ∣ a+m+1 then (1:ℝ) else 0) ≤ _
    simp only [Nat.add_assoc]
    change ∑ a ∈ range M, f (a+(m+1)) ≤ _
    rw [shift]
    obtain ⟨b, hb⟩ := hd
    have eq : ∑ a ∈ range M, f a = b := by
      rw [hb]
      simpa [f] using sum_at_multiples hP b (fun _ => (1:ℝ))
    rw [eq, le_div_iff₀ (by positivity)]
    have hsmall : 2^(K+1) ≤ P := Nat.pow_le_pow_left hprime.two_le _
    exact_mod_cast (show b * 2^(K+1) ≤ M by rw [hb, Nat.mul_comm P b]; gcongr)
  have hcard : q.primeFactors.card ≤ q := by
    have sub : q.primeFactors ⊆ Icc 1 q := fun p hp =>
      mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_le,
        Nat.le_of_dvd hq (Nat.dvd_of_mem_primeFactors hp)⟩
    simpa using card_le_card sub
  calc
    _ ≤ ∑ _p ∈ q.primeFactors, (M : ℝ) / 2^(K+1) := sum_le_sum count
    _ = (q.primeFactors.card : ℝ) * (M / (2 : ℝ)^(K+1)) := by simp
    _ ≤ q * (M / (2 : ℝ)^(K+1)) := by gcongr
    _ = _ := by ring

/-- Removing all rows meeting a high prime power costs at most one normalized unit
of second moment once the exponent dominates the cube of the longest window. -/
lemma good_row_transfer {q K R h : ℕ} (hq : 0 < q) (hh : h ≤ R)
    (hK : R^3*q ≤ 2^(K+1)) (χ : DirichletCharacter ℂ q) (u : ℕ → ℂ)
    (hu : ∀ n ≥ 1, ‖u n‖ = 1) (hm : ∀ x y, u (x*y) = u x * u y)
    (hc : ∀ n, n.Coprime q → u n = χ (n : ZMod q)) :
    let M := q^(K+1)
    let G := (range M).filter fun a =>
      ∀ p ∈ q.primeFactors, ∀ m ∈ range R, ¬ p^(K+1) ∣ a+m+1
    let V (d a : ℕ) := ∑ m ∈ range h,
      if d ∣ a+m+1 then χ ((((a+m+1)/d : ℕ) : ZMod q)) else 0
    ∑ a ∈ range M, ‖∑ d ∈ (q^K).divisors, u d * V d a‖^2 ≤
      (∑ a ∈ G, ‖∑ m ∈ range h, u (a+m+1)‖^2) + M := by
  classical
  intro M G V
  let w (n : ℕ) := u (n.gcd (q^K)) * χ (((n / n.gcd (q^K) : ℕ) : ZMod q))
  have row a : (∑ d ∈ (q^K).divisors, u d * V d a) = ∑ m ∈ range h, w (a+m+1) := by
    simp only [V, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl (fun m _ => divisor_expansion hq K (a+m+1) χ u)
  have hb n : ‖w n‖ ≤ 1 := by
    have hg := Nat.gcd_pos_of_pos_right n (pow_pos hq K)
    simpa [w, norm_mul, hu _ hg] using χ.norm_le_one (((n / n.gcd (q^K) : ℕ) : ZMod q))
  let bad (m a : ℕ) := ∑ p ∈ q.primeFactors,
    (if p^(K+1) ∣ a+m+1 then (1:ℝ) else 0)
  have hbad m a : 0 ≤ bad m a := sum_nonneg fun _ _ => by split <;> norm_num
  have point a (ha : a ∈ range M) :
      ‖∑ m ∈ range h, w (a+m+1)‖^2 ≤
        (if a ∈ G then ‖∑ m ∈ range h, u (a+m+1)‖^2 else 0) +
          (R:ℝ)^2 * ∑ m ∈ range R, bad m a := by
    by_cases good : a ∈ G
    · have eq : ∑ m ∈ range h, w (a+m+1) = ∑ m ∈ range h, u (a+m+1) := by
        apply sum_congr rfl
        intro m hm'
        let n := a+m+1
        have hcop := coprime_quotient_on_good hq K n (fun p hp =>
          (mem_filter.mp good).2 p hp m (range_mono hh hm'))
        change w n = u n
        dsimp only [w]
        rw [← hc _ hcop, ← hm, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
      rw [eq, if_pos good]
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sum_nonneg fun m _ => hbad m a))
    · have hnot : ¬ ∀ p ∈ q.primeFactors, ∀ m ∈ range R, ¬ p^(K+1) ∣ a+m+1 :=
        fun h => good (mem_filter.mpr ⟨ha,h⟩)
      push Not at hnot
      obtain ⟨p,hp,m,hm',hd⟩ := hnot
      have hone : 1 ≤ bad m a := by
        calc
          (1:ℝ) = (if p^(K+1) ∣ a+m+1 then 1 else 0) := by rw [if_pos hd]
          _ ≤ _ := single_le_sum (f := fun p => if p^(K+1) ∣ a+m+1 then (1:ℝ) else 0)
            (fun _ _ => by split <;> norm_num) hp
      have he : 1 ≤ ∑ i ∈ range R, bad i a :=
        hone.trans (single_le_sum (fun i _ => hbad i a) hm')
      have hn : ‖∑ m ∈ range h, w (a+m+1)‖ ≤ R := calc
        _ ≤ _ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ range h, (1:ℝ) := sum_le_sum fun _ _ => hb _
        _ ≤ _ := by simpa using (show (h:ℝ) ≤ R by exact_mod_cast hh)
      rw [if_neg good, zero_add]
      exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans (le_mul_of_one_le_right (sq_nonneg _) he)
  simp_rw [row]
  refine (sum_le_sum point).trans ?_
  rw [sum_add_distrib, ← sum_filter, ← mul_sum, sum_comm]
  have hf : (range M).filter (· ∈ G) = G := by
    ext a
    exact mem_filter.trans ⟨And.right, fun ha => ⟨(mem_filter.mp ha).1, ha⟩⟩
  rw [hf]
  apply add_le_add_right
  have counts m : ∑ a ∈ range M, bad m a ≤ q*M / (2:ℝ)^(K+1) := by
    dsimp only [bad]
    rw [sum_comm]
    exact reciprocal_prime_power_count hq m
  calc
    _ ≤ (R:ℝ)^2 * ∑ _m ∈ range R, ((q:ℝ)*M / 2^(K+1)) := by
      gcongr with m; exact counts m
    _ = ((R:ℝ)^3*q) / 2^(K+1) * M := by simp; ring
    _ ≤ 1 * M := by
      gcongr
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast hK
    _ = _ := one_mul _

lemma period_sum_blocks {f : ℕ → ℝ} {T : ℕ} (hf : Function.Periodic f T) (b : ℕ) :
    ∑ a ∈ range (b * T), f a = b * ∑ a ∈ range T, f a := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    simp_rw [Nat.add_comm (b * T), period_sum_shift hf (b * T)]
    push_cast
    ring

/-- A complete window of length r has one multiple of r. -/
lemma one_multiple {r : ℕ} (hr : 0 < r) (a : ℕ) (u : ℕ → ℂ) :
    ∑ m ∈ range r, (if r ∣ a + m + 1 then u ((a + m + 1) / r) else 0) =
      u (a / r + 1) := by
  let j := r - 1 - a % r
  have hmod := Nat.mod_lt a hr
  have hj : j < r := by dsimp [j]; omega
  have hnext : a + j + 1 = (a / r + 1) * r := by
    have := Nat.mod_add_div a r
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (a / r)] 
    dsimp [j]
    omega
  rw [sum_eq_single j]
  · rw [hnext, if_pos (dvd_mul_left _ _), Nat.mul_div_cancel _ hr]
  · intro m hm hne
    apply if_neg
    intro hd
    have hm' := mem_range.mp hm
    have he := Nat.mul_div_cancel' hd
    have hlow : a / r < (a + m + 1) / r := by
      by_contra! h
      have := Nat.mul_le_mul_left r h
      have := Nat.div_mul_le_self a r
      rw [Nat.mul_comm (a / r) r] at this
      omega
    have hupp : (a + m + 1) / r < a / r + 2 := by
      rw [Nat.div_lt_iff_lt_mul hr]
      have := Nat.mod_add_div a r
      rw [Nat.add_mul, Nat.mul_comm (a / r)]
      omega
    have eq : (a + m + 1) / r = a / r + 1 := by omega
    rw [eq, Nat.mul_comm] at he
    exact hne (by omega)
  · intro hj'
    exact (hj' (mem_range.mpr hj)).elim

/-- The residue class 1 modulo q alone supplies at least a 1/q share of the energy. -/
lemma complete_block_energy {q r M : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hd : r * q ∣ M) (χ : DirichletCharacter ℂ q) (h : ℕ) :
    (M : ℝ) ≤ q * ∑ a ∈ range M, ‖χ ((((a + h) / r + 1 : ℕ) : ZMod q))‖ ^ 2 := by
  let f (a : ℕ) : ℝ := ‖χ (((a / r + 1 : ℕ) : ZMod q))‖ ^ 2
  have hp : Function.Periodic f (r * q) := by
    intro a
    dsimp [f]
    rw [Nat.add_mul_div_left a q hr]
    simp [Nat.cast_add, add_assoc]
  obtain ⟨b, hb⟩ := hd
  rw [Nat.mul_comm (r * q) b] at hb
  have hPM : Function.Periodic f M := by
    rw [hb]
    simpa [nsmul_eq_mul] using hp.nsmul b
  change (M : ℝ) ≤ q * ∑ a ∈ range M, f (a + h)
  rw [period_sum_shift hPM h, hb, period_sum_blocks hp b]
  have hsub : range r ⊆ range (r*q) := range_mono (Nat.le_mul_of_pos_right r hq)
  have lower : (r : ℝ) ≤ ∑ a ∈ range (r*q), f a := calc
    (r : ℝ) = ∑ a ∈ range r, (1 : ℝ) := by simp
    _ = ∑ a ∈ range r, f a := sum_congr rfl fun a ha => by
      simp [f, Nat.div_eq_of_lt (mem_range.mp ha)]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
  push_cast
  calc
    _ = (q : ℝ) * (b * r) := by ring
    _ ≤ _ := by gcongr

lemma sum_short_shift {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) {L r : ℕ} (hr : r ≤ L) :
    ∑ t ∈ range L, f (t + r) ≤ ∑ t ∈ range (2*L), f t := by
  calc
    _ = ∑ t ∈ Ico r (r+L), f t := by
      rw [sum_Ico_eq_sum_range]
      simp [Nat.add_comm]
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun t _ _ => hf t)
      intro t ht
      have := mem_Ico.mp ht
      exact mem_range.mpr (by omega)

lemma increments_force_energy (S : ℕ → ℕ → ℂ) (q M L r : ℕ) (hr : r ≤ L)
    (hinc : ∀ t < L, (M : ℝ) ≤ q *
      ∑ a ∈ range M, ‖S a (t+r) - S a t‖ ^ 2) :
    (L : ℝ) * M ≤ 4 * q * ∑ t ∈ range (2*L), ∑ a ∈ range M, ‖S a t‖ ^ 2 := by
  let E (t : ℕ) : ℝ := ∑ a ∈ range M, ‖S a t‖ ^ 2
  have hE t : 0 ≤ E t := sum_nonneg fun _ _ => sq_nonneg _
  have point t (ht : t < L) : (M : ℝ) ≤ q * (2 * (E (t+r) + E t)) := by
    refine (hinc t ht).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg q))
    simp only [E, ← sum_add_distrib, mul_sum]
    apply sum_le_sum
    intro a _
    have h := norm_sub_le (S a (t+r)) (S a t)
    have h2 := mul_self_le_mul_self (norm_nonneg _) h
    nlinarith [sq_nonneg (‖S a (t+r)‖ - ‖S a t‖)]
  have hall := sum_le_sum (s := range L) (fun t ht => point t (mem_range.mp ht))
  simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum, sum_add_distrib] at hall
  have hs := sum_short_shift hE hr
  have ht : ∑ t ∈ range L, E t ≤ ∑ t ∈ range (2*L), E t :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ => hE i)
  change (L : ℝ) * M ≤ 4 * q * ∑ t ∈ range (2*L), E t
  calc
    _ ≤ _ := hall
    _ ≤ (q : ℝ) * (2 * ((∑ t ∈ range (2*L), E t) + ∑ t ∈ range (2*L), E t)) := by
      gcongr
    _ = _ := by ring

/-- Compare two prefix lengths separated by r, then average over all starting residues. -/
lemma layer_lower_bound {q M L r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hrL : r ≤ L) (hd : r*q ∣ M) (χ : DirichletCharacter ℂ q) :
    let V (a h : ℕ) := ∑ m ∈ range h,
      if r ∣ a + m + 1 then χ ((((a + m + 1) / r : ℕ) : ZMod q)) else 0
    (L : ℝ) * M ≤ 4 * q *
      ∑ t ∈ range (2*L), ∑ a ∈ range M, ‖V a (2*L+1+t)‖ ^ 2 := by
  intro V
  apply increments_force_energy (fun a t => V a (2*L+1+t)) q M L r hrL
  intro t _
  have diff (a : ℕ) (h : ℕ) :
      V a (h+r) - V a h = χ ((((a+h)/r+1 : ℕ) : ZMod q)) := by
    dsimp [V]
    rw [sum_range_add, add_sub_cancel_left]
    simpa only [Nat.add_assoc] using one_multiple hr (a+h) (fun j => χ (j : ZMod q))
  simpa only [← Nat.add_assoc (2*L+1) t r, diff] using complete_block_energy hq hr hd χ (2*L+1+t)

/-- Each power q^i ≤ L contributes a full-period lower bound. Orthogonality
allows these bounds to be added even though the original character extension
carries a different phase on each divisor. -/
lemma finite_character_obstruction {C Q J L q K : ℕ} (hCL : C < L) (hL : 0 < L)
    (hJ : 8 * (C+1) * Q < J) (hscale : Q^J ≤ L) (hJK : J ≤ K)
    (hq : 0 < q) (hqQ : q ≤ Q) (hK : (4*L)^3*q ≤ 2^(K+1))
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (u : ℕ →* ℂ)
    (hu : ∀ n ≥ 1, ‖u n‖ = 1) (hc : ∀ n, n.Coprime q → u n = χ (n : ZMod q)) :
    let M := q^(K+1)
    let G := (range M).filter fun a =>
      ∀ p ∈ q.primeFactors, ∀ m ∈ range (4*L), ¬ p^(K+1) ∣ a+m+1
    ¬ (∑ t ∈ range (2*L), ∑ a ∈ G, ‖∑ m ∈ range (2*L+1+t), u (a+m+1)‖^2)
        ≤ (C : ℝ) * (2*L) * M := by
  classical
  intro M G hsmall
  by_cases hq1 : q = 1
  · subst q
    have one (n : ℕ) : u n = 1 := by
      rw [hc n (Nat.coprime_one_right _), Subsingleton.elim (n : ZMod 1) 1, map_one]
    simp only [one, sum_const, nsmul_one, card_range, Complex.norm_natCast] at hsmall
    have hG : G = {0} := by simp [G, M]
    simp only [hG, card_singleton, one_smul] at hsmall
    have hzero := single_le_sum (s := range (2*L)) (f := fun t : ℕ => ((2*L+1+t : ℕ) : ℝ)^2)
      (fun t _ => sq_nonneg _) (mem_range.mpr (show 0 < 2*L by omega))
    have hcL : (C : ℝ) < L := by exact_mod_cast hCL
    have hl : (0 : ℝ) < L := by exact_mod_cast hL
    have hbad := hzero.trans hsmall
    simp only [M, one_pow, Nat.cast_one, mul_one, Nat.add_zero, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] at hbad
    nlinarith [mul_nonneg (sub_nonneg.mpr hcL.le) hl.le]
  have hq2 : 2 ≤ q := by omega
  let D := (q^K).divisors
  let V (d a h : ℕ) := ∑ m ∈ range h,
    if d ∣ a+m+1 then χ ((((a+m+1)/d : ℕ) : ZMod q)) else 0
  let energy (d t : ℕ) := ∑ a ∈ range M, ‖V d a (2*L+1+t)‖^2
  let raw (t : ℕ) := ∑ a ∈ G, ‖∑ m ∈ range (2*L+1+t), u (a+m+1)‖^2
  have hnon d t : 0 ≤ energy d t := sum_nonneg fun _ _ => sq_nonneg _
  have hD d (hd : d ∈ D) : ‖u d‖ = 1 :=
    hu _ (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (pow_pos hq K))
  have per_length t (ht : t ∈ range (2*L)) : ∑ d ∈ D, energy d t ≤ raw t + M := by
    have htt : 2*L+1+t ≤ 4*L := by have := mem_range.mp ht; omega
    have upper := good_row_transfer hq htt hK χ (u : ℕ → ℂ) hu u.map_mul hc
    have eq := sum_norm_sq_orthogonal D M (fun d a => V d a (2*L+1+t)) u hD
      (orthogonal_windows hq χ hχ (2*L+1+t))
    exact eq.ge.trans upper
  have total : ∑ d ∈ D, ∑ t ∈ range (2*L), energy d t ≤ ((C : ℝ)+1)*(2*L)*M := by
    rw [sum_comm]
    refine (sum_le_sum per_length).trans ?_
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    change (∑ t ∈ range (2*L), raw t) ≤ _ at hsmall
    push_cast
    linarith
  let powers := (range J).image (q^·)
  have sub : powers ⊆ D := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hd
    exact Nat.mem_divisors.mpr ⟨pow_dvd_pow q ((mem_range.mp hi).le.trans hJK), (pow_pos hq K).ne'⟩
  have hpos : (0:ℝ) < (L:ℝ)*M := by
    have hM : 0 < M := pow_pos hq _
    positivity
  have layers i (hi : i ∈ range J) :
      (L : ℝ)*M ≤ 4*q*∑ t ∈ range (2*L), energy (q^i) t := by
    have hiJ := (mem_range.mp hi).le
    have hrL : q^i ≤ L := (Nat.pow_le_pow_right hq hiJ).trans ((Nat.pow_le_pow_left hqQ J).trans hscale)
    have hd : q^i*q ∣ M := by
      rw [← pow_succ]
      exact pow_dvd_pow q (by omega)
    exact layer_lower_bound hq (pow_pos hq i) hrL hd χ
  have lower := sum_le_sum layers
  simp only [sum_const, card_range, nsmul_eq_mul, ← mul_sum] at lower
  have hpows : ∑ i ∈ range J, ∑ t ∈ range (2*L), energy (q^i) t ≤
        ∑ d ∈ D, ∑ t ∈ range (2*L), energy d t := by
    rw [← sum_image (f := fun d => ∑ t ∈ range (2*L), energy d t) (Nat.pow_right_injective hq2).injOn]
    exact sum_le_sum_of_subset_of_nonneg sub (fun d _ _ => sum_nonneg fun t _ => hnon d t)
  have bound : (J:ℝ) * (L*M) ≤ (8*((C:ℝ)+1)*Q) * (L*M) := calc
    _ ≤ _ := lower
    _ ≤ (4*(q:ℝ))*(((C:ℝ)+1)*(2*L)*M) := by gcongr; exact hpows.trans total
    _ = (8*((C:ℝ)+1)*q) * (L*M) := by ring
    _ ≤ _ := by gcongr
  have hj' : (8*((C:ℝ)+1)*Q) < J := by exact_mod_cast hJ
  exact (not_lt_of_ge bound) (mul_lt_mul_of_pos_right hj' hpos)

lemma mulEval_norm (z : ℕ → Metric.sphere (0 : ℂ) 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖if n = 0 then (0 : ℂ) else n.factorization.prod fun p a => (z p).1 ^ a‖ = 1 := by
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0, Finsupp.prod, norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_pow, mem_sphere_zero_iff_norm.mp (z p).2, one_pow]

lemma mulEval_continuous (n : ℕ) :
    Continuous (fun z : ℕ → Metric.sphere (0 : ℂ) 1 =>
      if n = 0 then (0 : ℂ) else n.factorization.prod fun p a => (z p).1 ^ a) := by
  by_cases hn : n = 0
  · simp [hn]; exact continuous_const
  · simp only [hn, ↓reduceIte, Finsupp.prod]
    exact continuous_finsetProd _ fun p _ =>
      (continuous_subtype_val.comp (continuous_apply p)).pow _

lemma energy_continuous (n : ℕ) :
    Continuous (fun z : ℕ → Metric.sphere (0 : ℂ) 1 =>
      ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2) :=
  ((continuous_finsetSum _ fun k _ => mulEval_continuous k).norm).pow 2

lemma sum_inv_Icc_two_le_log (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (1 / (n : ℝ)) ≤ Real.log (N : ℝ) := by
  induction N with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hsub : Finset.Icc 2 (k + 2) = insert (k + 2) (Finset.Icc 2 (k + 1)) := by
        ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hsub, Finset.sum_insert (by simp)]
      have hk1 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hk2 : (0 : ℝ) < (k + 2 : ℕ) := by positivity
      have hlog := Real.log_le_sub_one_of_pos (div_pos hk1 hk2)
      rw [Real.log_div hk1.ne' hk2.ne'] at hlog
      have h1 : ((k + 1 : ℕ) : ℝ) / ((k + 2 : ℕ) : ℝ) - 1 = -(1 / ((k + 2 : ℕ) : ℝ)) := by
        push_cast; field_simp; ring
      linarith

lemma sum_inv_Icc_ge_log_sub (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ) ≤ ∑ n ∈ Finset.Icc a b, (1 / (n : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have hapos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha1pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos ha1pos hapos)
    rw [Real.log_div ha1pos.ne' hapos.ne'] at hlog
    have h1 : ((a + 1 : ℕ) : ℝ) / (a : ℝ) - 1 = 1 / (a : ℝ) := by push_cast; field_simp; ring
    linarith
  | succ k hka ih =>
    have hsub : Finset.Icc a (k + 1) = insert (k + 1) (Finset.Icc a k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsub, Finset.sum_insert (by simp)]
    have hk1pos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hk2pos : (0 : ℝ) < (k + 2 : ℕ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hk2pos hk1pos)
    rw [Real.log_div hk2pos.ne' hk1pos.ne'] at hlog
    have h1 : ((k + 2 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 = 1 / ((k + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    linarith

lemma sum_inv_sqrt_bounds {X : ℕ} (hX : 100 ≤ X) :
    (1 / 3 : ℝ) * Real.log (X : ℝ) ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) ∧
    ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) ≤ Real.log (X : ℝ) := by
  have hsqrt_le : Nat.sqrt X + 1 ≤ X := by
    have h1 : Nat.sqrt X ≤ 10 → Nat.sqrt X + 1 ≤ X := by omega
    have h2 : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    nlinarith
  constructor
  · have h1 := sum_inv_Icc_ge_log_sub (Nat.sqrt X + 1) X (by omega) hsqrt_le
    have hXpos : (0 : ℝ) < X := by positivity
    have hlog_ge : Real.log (X : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) :=
      Real.log_le_log hXpos (by exact_mod_cast Nat.le_succ X)
    have hs_le : ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (X : ℝ) := by
      have hsq : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt X))]
        exact Real.sqrt_le_sqrt (by rw [sq]; exact_mod_cast Nat.sqrt_le X)
      have h1le : (1 : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ X by omega))
      push_cast; linarith
    have hlog_s : Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ Real.log 2 + (1 / 2 : ℝ) * Real.log (X : ℝ) := by
      calc
        Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ)
            ≤ Real.log (2 * Real.sqrt (X : ℝ)) := Real.log_le_log (by positivity) hs_le
        _ = Real.log 2 + Real.log (Real.sqrt (X : ℝ)) :=
              Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hXpos).ne'
        _ = Real.log 2 + (1 / 2 : ℝ) * Real.log (X : ℝ) := by
              rw [Real.log_sqrt hXpos.le]; ring
    have hlog2 : 6 * Real.log 2 ≤ Real.log (X : ℝ) := by
      have h64 : (2 : ℝ) ^ 6 ≤ (X : ℝ) := by
        have : 64 ≤ X := by omega
        have : (64 : ℝ) ≤ X := by exact_mod_cast this
        linarith
      calc 6 * Real.log 2 = Real.log ((2 : ℝ) ^ 6) := by rw [Real.log_pow]; ring
        _ ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h64
    linarith
  · have hsub : Finset.Icc (Nat.sqrt X + 1) X ⊆ Finset.Icc 2 X := by
      intro n hn
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
      have hs1 : 1 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
      (sum_inv_Icc_two_le_log X)

lemma van_der_corput_pretentious
    (h1 : ∀ (h₁ h₂ : ℕ), h₁ ≠ h₂ → ∀ ε : ℝ, 0 < ε →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℕ, A ≤ (X : ℝ) → ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
        let g : ℕ → ℂ := fun n =>
          if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
        ε * Real.log (X : ℝ) <
          ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + h₁) * star (g (n + h₂)) / (n : ℂ)‖ →
        ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
          1 ≤ q ∧ (q : ℝ) ≤ A ∧ |t| ≤ A * (X : ℝ) ∧
          ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
            (1 - (g p * star (χ (p : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ A)
    (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ) (hB : 0 ≤ B)
    (hL2 : ∀ n : ℕ,
      ∫ z, ‖∑ k ∈ Finset.Icc 1 n,
        (if k = 0 then (0 : ℂ) else k.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2
        ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ B) :
    ∀ ε : ℝ, 0 < ε → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ X : ℕ, Q ≤ (X : ℝ) →
      (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z : ℕ → Metric.sphere (0 : ℂ) 1 |
        ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
            1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
            ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
              (1 - ((if p = 0 then (0 : ℂ) else p.factorization.prod fun q_1 a => (z q_1).1 ^ a) *
                star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q} ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let g : (ℕ → Metric.sphere (0 : ℂ) 1) → ℕ → ℂ := fun z n =>
    if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
  let H : ℕ := Nat.ceil (16 * (B + 1) / ε) + 4
  have hH4 : 4 ≤ H := by dsimp [H]; omega
  have hH_big : 16 * (B + 1) / ε + 3 ≤ (H : ℝ) := by
    have := Nat.le_ceil (16 * (B + 1) / ε)
    dsimp [H]; push_cast; linarith
  let Pairs : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter fun p => p.1 ≠ p.2
  have hPairs_card : Pairs.card ≤ H ^ 2 := by
    calc Pairs.card ≤ (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).card := Finset.card_filter_le _ _
      _ = H ^ 2 := by simp [sq]
  have hA_ex : ∀ p : ℕ × ℕ, ∃ A : ℝ, 1 ≤ A ∧
      (p.1 ≠ p.2 → ∀ X : ℕ, A ≤ (X : ℝ) → ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
        (1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ) <
          ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ →
        ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
          1 ≤ q ∧ (q : ℝ) ≤ A ∧ |t| ≤ A * (X : ℝ) ∧
          ∑ pr ∈ (Finset.Icc 1 X).filter Nat.Prime,
            (1 - (g z pr * star (χ (pr : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (pr : ℝ))).re) / (pr : ℝ) ≤ A) := by
    intro p
    by_cases hne : p.1 ≠ p.2
    · obtain ⟨A, hA1, hA⟩ := h1 p.1 p.2 hne (1 / (2 * (H : ℝ) ^ 2)) (by positivity)
      exact ⟨A, hA1, fun _ => hA⟩
    · exact ⟨1, le_rfl, fun h => absurd h hne⟩
  choose Afn hAfn_ge1 hAfn using hA_ex
  let Q : ℝ := max 100 (∑ p ∈ Pairs, Afn p) + 1
  have hQ_ge1 : 1 ≤ Q := by
    have : (100 : ℝ) ≤ max 100 (∑ p ∈ Pairs, Afn p) := le_max_left _ _
    dsimp [Q]; linarith
  refine ⟨Q, hQ_ge1, fun X hXQ => ?_⟩
  have hX100 : 100 ≤ X := by
    have : (100 : ℝ) ≤ Q := by dsimp [Q]; linarith [le_max_left (100 : ℝ) (∑ p ∈ Pairs, Afn p)]
    have : (100 : ℝ) ≤ X := this.trans hXQ
    exact_mod_cast this
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have ⟨hinv_lo, hinv_hi⟩ := sum_inv_sqrt_bounds hX100
  let G : (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun z =>
    ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
      (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2
  have hG_cont : Continuous G := by
    refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
    exact ((continuous_finsetSum _ fun h _ => mulEval_continuous (n + h)).norm).pow 2
  have hG_nn : ∀ z, 0 ≤ G z := fun z =>
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (sq_nonneg _)
  have hG_int : Integrable G (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
    hG_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
  have hG_mean : ∫ z, G z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ 4 * (B + 1) * Real.log (X : ℝ) := by
    have hterm_int : ∀ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        Integrable (fun z => (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) := fun n _ =>
      (continuous_const.mul (((continuous_finsetSum _ fun h _ =>
        mulEval_continuous (n + h)).norm).pow 2)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hterm_le : ∀ n : ℕ,
        ∫ z, ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ 4 * B := by
      intro n
      have hpw : ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
          ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 ≤
            2 * ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2 + 2 * ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2 := by
        intro z
        have hdiff : ∑ h ∈ Finset.Icc 1 H, g z (n + h) =
            (∑ k ∈ Finset.Icc 1 (n + H), g z k) - (∑ k ∈ Finset.Icc 1 n, g z k) := by
          have hunion : Finset.Icc 1 (n + H) = Finset.Icc 1 n ∪ Finset.Icc (n + 1) (n + H) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
          have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Icc (n + 1) (n + H)) := by
            rw [Finset.disjoint_left]; intro k hk1 hk2
            simp only [Finset.mem_Icc] at hk1 hk2; omega
          have hshift : ∑ k ∈ Finset.Icc (n + 1) (n + H), g z k =
              ∑ h ∈ Finset.Icc 1 H, g z (n + h) := by
            refine Finset.sum_bij (fun k _ => k - n) ?_ ?_ ?_ ?_
            · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
            · intro k₁ hk₁ k₂ hk₂ h; simp only [Finset.mem_Icc] at hk₁ hk₂; omega
            · intro h hh; refine ⟨n + h, ?_, by omega⟩
              simp only [Finset.mem_Icc] at hh ⊢; omega
            · intro k hk; simp only [Finset.mem_Icc] at hk
              congr 1; omega
          rw [hunion, Finset.sum_union hdisj, hshift, add_sub_cancel_left]
        rw [hdiff]
        have htri : ‖(∑ k ∈ Finset.Icc 1 (n + H), g z k) - ∑ k ∈ Finset.Icc 1 n, g z k‖ ≤
            ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ + ‖∑ k ∈ Finset.Icc 1 n, g z k‖ :=
          norm_sub_le _ _
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ - ‖∑ k ∈ Finset.Icc 1 n, g z k‖)]
      have hint1 : Integrable (fun z => ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
        (((continuous_finsetSum _ fun h _ => mulEval_continuous (n + h)).norm).pow 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint2 : Integrable (fun z => 2 * ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
        ((energy_continuous (n + H)).const_mul 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hint3 : Integrable (fun z => 2 * ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2)
          (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
        ((energy_continuous n).const_mul 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc
        ∫ z, ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))
            ≤ ∫ z, (2 * ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2 +
                2 * ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2) ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
              integral_mono hint1 (hint2.add hint3) hpw
        _ = 2 * (∫ z, ‖∑ k ∈ Finset.Icc 1 (n + H), g z k‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) +
            2 * (∫ z, ‖∑ k ∈ Finset.Icc 1 n, g z k‖ ^ 2 ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))) := by
              rw [integral_add hint2 hint3, integral_const_mul, integral_const_mul]
        _ ≤ 4 * B := by linarith [hL2 (n + H), hL2 n]
    calc
      ∫ z, G z ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1))
          = ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              ∫ z, (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2
                ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
            integral_finsetSum _ hterm_int
      _ = ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              (1 / (n : ℝ)) * ∫ z, ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2
                ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) :=
            Finset.sum_congr rfl fun n _ => integral_const_mul _ _
      _ ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) * (4 * B) :=
            Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hterm_le n) (by positivity)
      _ = (4 * B) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) := by
            rw [← Finset.sum_mul, mul_comm]
      _ ≤ (4 * B) * Real.log (X : ℝ) := mul_le_mul_of_nonneg_left hinv_hi (by positivity)
      _ ≤ 4 * (B + 1) * Real.log (X : ℝ) := by nlinarith
  let T : ℝ := (4 * (B + 1) / ε) * Real.log (X : ℝ)
  have hT_pos : 0 < T := by positivity
  have hmarkov : (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z} ≤ ENNReal.ofReal ε := by
    have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hG_nn) hG_int T
    rw [measureReal_def] at hm
    have h1 : T * ((μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z}).toReal ≤ 4 * (B + 1) * Real.log (X : ℝ) :=
      hm.trans hG_mean
    have h2 : ((μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z}).toReal ≤ ε := by
      have hmul : T * ε = 4 * (B + 1) * Real.log (X : ℝ) := by dsimp [T]; field_simp [hε.ne']
      nlinarith
    have hfin : (μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z | T ≤ G z} ≠ ⊤ := measure_ne_top _ _
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal h2
  refine (measure_mono ?_).trans hmarkov
  intro z hz
  change T ≤ G z
  by_contra hlt
  push Not at hlt
  have hexpand : G z = (H : ℝ) * (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ))) +
      (∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
    have hpoint : ∀ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        (1 / (n : ℝ)) * ‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 =
          (H : ℝ) * (1 / (n : ℝ)) +
          (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
      intro n hn
      have hnorm : ((‖∑ h ∈ Finset.Icc 1 H, g z (n + h)‖ ^ 2 : ℝ) : ℂ) =
          (H : ℂ) + ∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) := by
        have hsq : ∀ w : ℂ, ((‖w‖ ^ 2 : ℝ) : ℂ) = w * star w := fun w => by
          rw [Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
        rw [hsq, Complex.star_def, map_sum, Finset.sum_mul]
        simp_rw [← Complex.star_def, Finset.mul_sum]
        rw [← Finset.sum_product']
        let Diag : Finset (ℕ × ℕ) :=
          (Finset.Icc 1 H ×ˢ Finset.Icc 1 H).filter fun p => p.1 = p.2
        have hpart : Finset.Icc 1 H ×ˢ Finset.Icc 1 H = Diag ∪ Pairs := by
          ext p; simp only [Diag, Pairs, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hp; rcases eq_or_ne p.1 p.2 with h | h
            · exact Or.inl ⟨hp, h⟩
            · exact Or.inr ⟨hp, h⟩
          · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
        have hdisj : Disjoint Diag Pairs :=
          Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
        rw [hpart, Finset.sum_union hdisj]
        congr 1
        have hdiag_eq : ∑ p ∈ Diag, g z (n + p.1) * star (g z (n + p.2)) =
            ∑ h ∈ Finset.Icc 1 H, (1 : ℂ) := by
          refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
          · intro p hp; exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
          · intro p₁ hp₁ p₂ hp₂ h
            have h1 := (Finset.mem_filter.mp hp₁).2
            have h2 := (Finset.mem_filter.mp hp₂).2
            ext <;> omega
          · intro h hh
            refine ⟨(h, h), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hh, hh⟩, rfl⟩, rfl⟩
          · intro p hp
            have heq := (Finset.mem_filter.mp hp).2
            have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1).1
            rw [← heq, Complex.star_def, Complex.mul_conj', mulEval_norm z (by omega)]
            simp
        rw [hdiag_eq]; simp
      have hre := congrArg Complex.re hnorm
      simp only [Complex.ofReal_re, Complex.add_re, Complex.natCast_re] at hre
      have hdiv : (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re =
          (1 / (n : ℝ)) * (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2))).re := by
        rw [← Finset.sum_div, div_eq_mul_inv]
        have hinv : ((n : ℂ)⁻¹) = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
        rw [hinv, mul_comm, Complex.re_ofReal_mul]
        ring
      rw [hdiv, hre]; ring
    calc
      G z = ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              ((H : ℝ) * (1 / (n : ℝ)) +
                (∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re) :=
            Finset.sum_congr rfl hpoint
      _ = (H : ℝ) * (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ))) +
            (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              ∑ p ∈ Pairs, g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Complex.re_sum]
      _ = (H : ℝ) * (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ))) +
            (∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re := by
            rw [Finset.sum_comm]
  have hdiag_gt : T + Real.log (X : ℝ) ≤ (H : ℝ) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) := by
    have h1 : (4 * (B + 1) / ε + 1) * Real.log (X : ℝ) ≤ (H : ℝ) * ((1 / 3 : ℝ) * Real.log (X : ℝ)) := by
      have : 4 * (B + 1) / ε + 1 ≤ (H : ℝ) * (1 / 3 : ℝ) := by
        have hpos : 0 ≤ (B + 1) / ε := by positivity
        have hHb : 16 * ((B + 1) / ε) + 3 ≤ (H : ℝ) := by simpa [mul_div_assoc] using hH_big
        have hgoal : 4 * ((B + 1) / ε) + 1 ≤ (H : ℝ) * (1 / 3 : ℝ) := by linarith
        simpa [mul_div_assoc] using hgoal
      nlinarith
    have h2 : (H : ℝ) * ((1 / 3 : ℝ) * Real.log (X : ℝ)) ≤
        (H : ℝ) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv_lo (by positivity)
    dsimp [T]; linarith
  have hoff_gt : Real.log (X : ℝ) <
      ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := by
    have hre_le : -(∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re ≤
        ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
          g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := by
      calc
        -(∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
            g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)).re
            ≤ ‖∑ p ∈ Pairs, ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
                g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ :=
              (neg_le_abs _).trans (Complex.abs_re_le_norm _)
        _ ≤ ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := norm_sum_le _ _
    linarith
  have hex_pair : ∃ p ∈ Pairs,
      (1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ) <
        ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
          g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ := by
    by_contra hno
    push Not at hno
    have hsum_le : ∑ p ∈ Pairs, ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        g z (n + p.1) * star (g z (n + p.2)) / (n : ℂ)‖ ≤
        (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) := by
      calc
        _ ≤ ∑ _ ∈ Pairs, ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) :=
              Finset.sum_le_sum hno
        _ = (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) := by simp
    have hle_half : (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) ≤
        (1 / 2 : ℝ) * Real.log (X : ℝ) := by
      have hP : (Pairs.card : ℝ) ≤ (H : ℝ) ^ 2 := by exact_mod_cast hPairs_card
      have hH2_pos : (0 : ℝ) < (H : ℝ) ^ 2 := by positivity
      calc
        (Pairs.card : ℝ) * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ))
            ≤ (H : ℝ) ^ 2 * ((1 / (2 * (H : ℝ) ^ 2)) * Real.log (X : ℝ)) :=
              mul_le_mul_of_nonneg_right hP (by positivity)
        _ = (1 / 2 : ℝ) * Real.log (X : ℝ) := by field_simp [hH2_pos.ne']
    linarith
  obtain ⟨p, hpPairs, hp_gt⟩ := hex_pair
  have hp_ne : p.1 ≠ p.2 := (Finset.mem_filter.mp hpPairs).2
  have hA_le_Q : Afn p ≤ Q := by
    have h1 : Afn p ≤ ∑ q ∈ Pairs, Afn q :=
      Finset.single_le_sum (fun q _ => le_trans zero_le_one (hAfn_ge1 q)) hpPairs
    have h2 : ∑ q ∈ Pairs, Afn q ≤ max 100 (∑ q ∈ Pairs, Afn q) := le_max_right _ _
    dsimp [Q]; linarith
  obtain ⟨q, χ, t, hq1, hqA, htA, hdist⟩ := hAfn p hp_ne X (hA_le_Q.trans hXQ) z hp_gt
  apply hz
  refine ⟨q, χ, t, hq1, hqA.trans hA_le_Q, ?_, hdist.trans hA_le_Q⟩
  exact htA.trans (mul_le_mul_of_nonneg_right hA_le_Q (Nat.cast_nonneg X))

/-- Tao's logarithmically averaged inverse theorem, in the form shared with the real variant. -/
def H1 : Prop :=
  ∀ (h₁ h₂ : ℕ), h₁ ≠ h₂ → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℕ, A ≤ (X : ℝ) → ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
      let g : ℕ → ℂ := fun n =>
        if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
      ε * Real.log (X : ℝ) <
        ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + h₁) * star (g (n + h₂)) / (n : ℂ)‖ →
      ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q ∧ (q : ℝ) ≤ A ∧ |t| ≤ A * (X : ℝ) ∧
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          (1 - (g p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ A

/-- Analytic comparison (4.8). For window lengths in (2L,4L], some primitive
character has a completely multiplicative extension with bounded mean square
on good classes modulo q^(K+1). The modulus bound is fixed before L is chosen,
and the exponent can be taken arbitrarily large before the averaging scale X. -/
def H2 : Prop :=
  let mulEval : (ℕ → Metric.sphere (0 : ℂ) 1) → ℕ → ℂ := fun z n =>
    if n = 0 then 0 else n.factorization.prod fun p a => (z p).1 ^ a
  ∀ (μ : MeasureTheory.ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1)) (B : ℝ), 0 ≤ B →
    (∀ n : ℕ, ∫ z, ‖∑ k ∈ Finset.Icc 1 n, mulEval z k‖ ^ 2
      ∂(μ : MeasureTheory.Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ B) →
    (∀ ε : ℝ, 0 < ε → ∃ Q : ℝ, 1 ≤ Q ∧ ∀ X : ℕ, Q ≤ (X : ℝ) →
      (μ : MeasureTheory.Measure (ℕ → Metric.sphere (0 : ℂ) 1)) {z : ℕ → Metric.sphere (0 : ℂ) 1 |
        ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
            1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
            ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
              (1 - (mulEval z p * star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q} ≤
        ENNReal.ofReal ε) →
    ∃ C Q L₀ : ℕ, ∀ L ≥ L₀, ∀ U : ℕ,
      ∃ (q K : ℕ) (χ : DirichletCharacter ℂ q) (u : ℕ →* ℂ),
      1 ≤ q ∧ q ≤ Q ∧ U ≤ K ∧ χ.IsPrimitive ∧
      (∀ n ≥ 1, ‖u n‖ = 1) ∧ (∀ n, n.Coprime q → u n = χ (n : ZMod q)) ∧
      let M := q^(K+1)
      let G := (range M).filter fun a =>
        ∀ p ∈ q.primeFactors, ∀ m ∈ range (4*L), ¬ p^(K+1) ∣ a+m+1
      (∑ t ∈ range (2*L), ∑ a ∈ G, ‖∑ m ∈ range (2*L+1+t), u (a+m+1)‖^2)
        ≤ (C : ℝ) * (2*L) * M

theorem main : H1 → H2 → OMA.R_Erdos67_erdos_67_variants_complex_R1.H2 := by
  intro hElliott hTransfer μ B
  by_contra! hsmall
  have hB : 0 ≤ B := by simpa using hsmall 0
  have hL2 (n : ℕ) :
      ∫ z, ‖∑ j ∈ Icc 1 n,
        (if j = 0 then (0 : ℂ) else j.factorization.prod fun p a => (z p).1 ^ a)‖ ^ 2
          ∂(μ : Measure (ℕ → Metric.sphere (0 : ℂ) 1)) ≤ B := by
    refine (le_of_eq ?_).trans (hsmall n)
    apply integral_congr_ae
    filter_upwards with z
    congr 2
    apply sum_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := by have := (mem_Icc.mp hj).1; omega
    simp [hj0, Finsupp.prod, Nat.support_factorization]
  have pret := van_der_corput_pretentious hElliott μ B hB hL2
  obtain ⟨C, Q, L₀, compare⟩ := hTransfer μ B hB hL2 pret
  let J := 8*(C+1)*(Q+1) + 1
  let L := Q^J + C + L₀ + 1
  obtain ⟨q,K,χ,u,hq,hqQ,hK,hχ,hu,hc,hsmall'⟩ :=
    compare L (by dsimp [L]; omega) ((4*L)^3*Q+J)
  have hpow : (4*L)^3*q ≤ 2^(K+1) := calc
    _ ≤ (4*L)^3*Q := Nat.mul_le_mul_left _ hqQ
    _ ≤ K+1 := by omega
    _ ≤ 2^(K+1) := (Nat.lt_two_pow_self (n := K+1)).le
  apply finite_character_obstruction (J := J) (Q := Q) (L := L) (C := C)
    (by dsimp [L]; omega) (by dsimp [L]; omega) (by dsimp [J]; nlinarith)
    (by dsimp [L]; omega) (by omega) hq hqQ hpow χ hχ u hu hc hsmall'

end OMA.R_Erdos67_erdos_67_variants_complex_R1_H2_R1
