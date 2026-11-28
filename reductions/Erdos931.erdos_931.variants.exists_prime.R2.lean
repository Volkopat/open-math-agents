import FormalConjectures.ErdosProblems.«931»
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Pell
import Mathlib.Data.ZMod.Basic

/-!
At each separation, the first two entries of the earlier block have prime
support in a fixed finite set. This cross-difference argument is the local
version of the bound in @ivillar's proof of R1.H1, and is used in Venkat,
Equal prime divisors in disjoint blocks of consecutive integers, Sections 6.1
and 6.3. The bound here uses a modular period for each allowed prime.
If Y_e is the second coordinate of the e-th power and 2*Y_e is
supported on S, it divides e times the product of the certified prime powers.
A doubling estimate proves that the first strict cutoff also excludes all
larger indices.
-/

open Finset

namespace OMA.R_Erdos931_erdos_931_variants_exists_prime_R2

private theorem exists_y_dvd {d : ℤ} (a : Pell.Solution₁ d) {m : ℕ} (hm : m ≠ 0) :
    ∃ N : ℕ, 0 < N ∧ N ≤ m*m ∧ (m : ℤ) ∣ (a ^ N).y := by
  let : NeZero m := ⟨hm⟩
  let f (n : ℕ) : ZMod m × ZMod m := (Int.cast (a ^ n).x, Int.cast (a ^ n).y)
  obtain ⟨i, j, hij, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun n : Fin (m*m + 1) => f n) (by simp)
  have hi : (i : ℕ) ≤ m*m := by omega
  have hj : (j : ℕ) ≤ m*m := by omega
  replace hij : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  generalize (i : ℕ) = i' at hi hij heq
  generalize (j : ℕ) = j' at hj hij heq
  clear i j
  rename' i' => i, j' => j
  wlog hlt : i < j generalizing i j
  · exact this (i := j) (j := i) hj hi hij.symm heq.symm (by omega)
  refine ⟨j - i, by omega, by omega, ?_⟩
  have hpow : a ^ (j - i) = a ^ j * (a ^ i)⁻¹ := by
    rw [← mul_inv_eq_iff_eq_mul, inv_inv, ← pow_add, Nat.sub_add_cancel hlt.le]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hpow, Pell.Solution₁.y_mul,
    Pell.Solution₁.y_inv, Pell.Solution₁.x_inv]
  push_cast
  have hx : ((a ^ i).x : ZMod m) = ((a ^ j).x : ZMod m) := congrArg Prod.fst heq
  have hy : ((a ^ i).y : ZMod m) = ((a ^ j).y : ZMod m) := congrArg Prod.snd heq
  rw [hx, hy]
  ring

private theorem pell_sub_pow_dvd_iff {d : ℤ} {m : ℕ} (a : Pell.Solution₁ d) :
    (m : ℤ√d) ∣ (↑(a ^ 2) : ℤ√d) - 1 ↔ (m : ℤ) ∣ 2 * a.y := by
  have h : (↑(a ^ 2) : ℤ√d) - 1 = (⟨0, 2 * a.y⟩ : ℤ√d) * (a : ℤ√d) := by
    ext
    · change (a ^ 2).x - 1 = _
      rw [pow_two, Pell.Solution₁.x_mul, ← sq a.x, a.prop_x]
      simp only [Zsqrtd.re_mul, zero_mul, zero_add]
      change 1 + d * a.y ^ 2 + d * (a.y * a.y) - 1 = d * (2 * a.y) * a.y
      ring
    · change (a ^ 2).y - 0 = _
      rw [pow_two, Pell.Solution₁.y_mul]
      simp only [Zsqrtd.im_mul, zero_mul, zero_add]
      change a.x * a.y + a.y * a.x - 0 = 2 * a.y * a.x
      ring
  rw [h, (show IsUnit (a : ℤ√d) from Unitary.isUnit_coe).dvd_mul_right,
    ← Int.cast_natCast, Zsqrtd.intCast_dvd]
  simp

private theorem geom_dvd_sub {R : Type*} [CommRing R] {m z : R}
    (hz : m ∣ z - 1) (n : ℕ) : m ∣ (∑ i ∈ range n, z^i) - (n : R) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.cast_succ, add_sub_add_comm]
    exact dvd_add ih (dvd_trans hz (by simpa using sub_dvd_pow_sub_pow z 1 n))

private theorem scalar_dvd_iff {d : ℤ} (p : ℕ) (w : ℤ√d) :
    (p : ℤ√d) ∣ w ↔ (p : ℤ) ∣ w.re ∧ (p : ℤ) ∣ w.im := by
  rw [← Int.cast_natCast, Zsqrtd.intCast_dvd]

private theorem dvd_mul_of_scalar_congr {d : ℤ} {p r : ℕ} (hp : p.Prime)
    (hr : ¬p ∣ r) (w g : ℤ√d) (hg : (p : ℤ√d) ∣ g - (r : ℤ√d)) :
    (p : ℤ√d) ∣ w * g ↔ (p : ℤ√d) ∣ w := by
  have hdiff : (p : ℤ√d) ∣ w * g - w * (r : ℤ√d) := by
    rw [← mul_sub]
    exact dvd_mul_of_dvd_right hg w
  rw [dvd_iff_dvd_of_dvd_sub hdiff, scalar_dvd_iff, scalar_dvd_iff]
  simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast,
    mul_zero, zero_add, add_zero]
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hri : ¬(p : ℤ) ∣ (r : ℤ) := by exact_mod_cast hr
  simp [hpi.dvd_mul, hri]

private theorem pow_prime_power_remainder {d : ℤ} {p e : ℕ} (hp : p.Prime) {z w : ℤ√d}
    (hz : (p : ℤ√d)^2 ∣ z - 1)
    (hw : z - 1 = (p : ℤ√d)^e * w) (hnw : ¬(p : ℤ√d) ∣ w) (j : ℕ) :
    ∃ u : ℤ√d, z ^ (p ^ j) - 1 = (p : ℤ√d)^(e+j) * u ∧ ¬(p : ℤ√d) ∣ u := by
  induction j with
  | zero => exact ⟨w, by simpa using hw, hnw⟩
  | succ j ih =>
    obtain ⟨u, hu, hnu⟩ := ih
    let z' := z ^ (p ^ j)
    have hz' : (p : ℤ√d)^2 ∣ z' - 1 :=
      dvd_trans hz (by simpa [z'] using sub_dvd_pow_sub_pow z 1 (p ^ j))
    obtain ⟨c, hc⟩ := geom_dvd_sub hz' p
    let g : ℤ√d := 1 + (p : ℤ√d) * c
    have hg : (p : ℤ√d) ∣ g - (1 : ℤ√d) := ⟨c, by dsimp [g]; ring⟩
    refine ⟨u * g, ?_, ?_⟩
    · have hsum : (∑ i ∈ range p, z'^i) = (p : ℤ√d) * g := by
        dsimp [g]
        linear_combination hc
      rw [pow_succ p j, pow_mul, ← geom_sum_mul, show z ^ (p ^ j) = z' from rfl,
        hsum, show z' - 1 = (p : ℤ√d)^(e+j) * u from hu, show e+j.succ = e+j+1 by omega,
        pow_succ]
      ring
    · exact (dvd_mul_of_scalar_congr (r := 1) hp (by simpa using hp.ne_one) u g
        (by simpa using hg)).not.mpr hnu

private theorem pow_remainder {d : ℤ} {p e n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    {z w : ℤ√d} (hz : (p : ℤ√d)^2 ∣ z - 1)
    (hw : z - 1 = (p : ℤ√d)^e * w) (hnw : ¬(p : ℤ√d) ∣ w) :
    ∃ u : ℤ√d, z ^ n - 1 = (p : ℤ√d)^(e + n.factorization p) * u ∧
      ¬(p : ℤ√d) ∣ u := by
  obtain ⟨u, hu, hnu⟩ := pow_prime_power_remainder hp hz hw hnw (n.factorization p)
  let z' := z ^ (p ^ n.factorization p)
  let r := n / p ^ n.factorization p
  have hr : ¬p ∣ r := Nat.not_dvd_ordCompl hp hn
  have hnr : p ^ n.factorization p * r = n := Nat.ordProj_mul_ordCompl_eq_self n p
  let g : ℤ√d := ∑ i ∈ range r, z'^i
  have hz' : (p : ℤ√d) ∣ z' - 1 :=
    dvd_trans (dvd_trans (dvd_pow_self _ (by decide : 2 ≠ 0)) hz)
      (by simpa [z'] using sub_dvd_pow_sub_pow z 1 (p ^ n.factorization p))
  refine ⟨u * g, ?_, (dvd_mul_of_scalar_congr hp hr u g (geom_dvd_sub hz' r)).not.mpr hnu⟩
  conv_lhs => rw [← hnr, pow_mul]
  change z'^r - 1 = _
  rw [← geom_sum_mul, show z' - 1 = _ from hu, show (∑ i ∈ range r, z'^i) = g from rfl]
  ring

private theorem y_dvd_y_pow {d : ℤ} (a : Pell.Solution₁ d) (n : ℕ) :
    a.y ∣ (a ^ n).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Pell.Solution₁.y_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

private theorem scalar_pow_cancel {d : ℤ} {p e : ℕ} (hp : p ≠ 0) {a b : ℤ√d}
    (h : (p : ℤ√d)^e * a = (p : ℤ√d)^e * b) : a = b := by
  rw [← Nat.cast_pow, ← Int.cast_natCast] at h
  have hne : (↑(p ^ e) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero e hp
  ext
  · apply mul_left_cancel₀ hne
    simpa only [Zsqrtd.re_smul] using congrArg Zsqrtd.re h
  · apply mul_left_cancel₀ hne
    simpa only [Zsqrtd.im_smul] using congrArg Zsqrtd.im h

private theorem double_y_nonneg {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y) (i : ℕ) : 0 ≤ 2 * (a^i).y := by
  cases i with
  | zero => simp
  | succ i =>
    have hi := Pell.Solution₁.y_pow_succ_pos (by omega : 0 < a.x) hay i
    rw [Nat.succ_eq_add_one] at hi
    omega

private theorem double_y_ne_zero {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y) {i : ℕ} (hi : 0 < i) :
    (2 * (a^i).y).toNat ≠ 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  have hj := Pell.Solution₁.y_pow_succ_pos (by omega : 0 < a.x) hay j
  omega

/-- A single modular period bounds the extra exponent of one allowed prime. -/
private theorem pell_factorization_le {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y) {p N n : ℕ} (hp : p.Prime) (hN : 0 < N)
    (hn : 0 < n) (hdiv : p^2 ∣ (2 * (a ^ N).y).toNat) :
    ((2 * (a ^ n).y).toNat).factorization p ≤
      ((2 * (a ^ N).y).toNat).factorization p + n.factorization p := by
  let v (i : ℕ) := (2 * (a ^ i).y).toNat
  have hv (i : ℕ) : (v i : ℤ) = 2 * (a ^ i).y :=
    Int.toNat_of_nonneg (double_y_nonneg a hax hay i)
  have hdvd (i r : ℕ) :
      (r : ℤ√d) ∣ (↑((a ^ i)^2) : ℤ√d) - 1 ↔ r ∣ v i := by
    rw [pell_sub_pow_dvd_iff, ← hv, Int.natCast_dvd_natCast]
  let z := (↑((a ^ N)^2) : ℤ√d)
  let e := (v N).factorization p
  have hvN := double_y_ne_zero a hax hay hN
  have hvn := double_y_ne_zero a hax hay hn
  have hz : (p : ℤ√d)^2 ∣ z - 1 := by
    rw [← Nat.cast_pow, hdvd]
    exact hdiv
  have hez : (p : ℤ√d)^e ∣ z - 1 := by
    rw [← Nat.cast_pow, hdvd]
    exact (hp.pow_dvd_iff_le_factorization hvN).2 le_rfl
  obtain ⟨w, hw⟩ := hez
  have hnw : ¬(p : ℤ√d) ∣ w := by
    rintro ⟨r, hr⟩
    have hbad : (p : ℤ√d)^(e+1) ∣ z - 1 :=
      ⟨r, by rw [hw, hr, pow_succ, mul_assoc]⟩
    rw [← Nat.cast_pow, hdvd, hp.pow_dvd_iff_le_factorization hvN] at hbad
    exact Nat.not_succ_le_self e hbad
  obtain ⟨u, hu, hnu⟩ := pow_remainder hp hn.ne' hz hw hnw
  have hin : v n ∣ v (N*n) := by
    rw [← Int.natCast_dvd_natCast, hv, hv, mul_comm N, pow_mul]
    exact mul_dvd_mul_left _ (y_dvd_y_pow (a ^ n) N)
  change (v n).factorization p ≤ e + n.factorization p
  by_contra! htoo
  have hpow : p^(e+n.factorization p+1) ∣ v (N*n) :=
    ((hp.pow_dvd_iff_le_factorization hvn).2 htoo).trans hin
  have hcast : (p : ℤ√d)^(e+n.factorization p+1) ∣ z^n - 1 := by
    have h := (hdvd (N*n) _).2 hpow
    rw [Nat.cast_pow] at h
    have coe (i : ℕ) : (↑(a ^ i) : ℤ√d) = (a : ℤ√d)^i :=
      SubmonoidClass.coe_pow a i
    simpa only [z, ← pow_mul, coe, Nat.mul_assoc, Nat.mul_comm 2 n] using h
  obtain ⟨c, hc⟩ := hcast
  rw [hu, pow_succ, mul_assoc] at hc
  exact hnu ⟨c, scalar_pow_cancel hp.ne_zero hc⟩

private theorem double_y_step {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y) (i : ℕ) :
    2 * (2 * (a^i).y).toNat ≤ (2 * (a^(i+1)).y).toNat := by
  let v (j : ℕ) := (2 * (a ^ j).y).toNat
  change 2 * v i ≤ v (i+1)
  have hx := Pell.Solution₁.x_pow_pos (by omega : 0 < a.x) i
  have hy : 0 ≤ (a ^ i).y := by have := double_y_nonneg a hax hay i; omega
  have hmul := mul_le_mul_of_nonneg_left (show (2 : ℤ) ≤ a.x by omega) hy
  have hpos := mul_nonneg hx.le hay.le
  have hv (j : ℕ) : (v j : ℤ) = 2 * (a ^ j).y :=
    Int.toNat_of_nonneg (double_y_nonneg a hax hay j)
  exact_mod_cast (show ((2 * v i : ℕ) : ℤ) ≤ (v (i+1) : ℤ) by
    push_cast
    rw [hv, hv, pow_succ, Pell.Solution₁.y_mul]
    linarith)

/-- A finite certificate for a cutoff on indices with prescribed support. -/
private theorem certified_index_bound {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y) (S : Finset ℕ) (hpS : ∀ p ∈ S, p.Prime)
    (E : ℕ → ℕ) (T : ℕ)
    (hE : ∀ p ∈ S, ∃ t ∈ Icc 1 (p^4),
      p^2 ∣ (2 * (a^t).y).toNat ∧ ¬p^(E p+1) ∣ (2 * (a^t).y).toNat)
    (hT : ((∏ p ∈ S, p^(E p)) * (T+1) : ℕ) < (2 * (a^(T+1)).y).toNat)
    {n : ℕ} (hn : 0 < n) (hs : (2 * (a^n).y).toNat.primeFactors ⊆ S) : n ≤ T := by
  let v (i : ℕ) := (2 * (a ^ i).y).toNat
  let C := ∏ p ∈ S, p^(E p)
  have hC : C ≠ 0 := prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hpS p hp).ne_zero
  have hvn := double_y_ne_zero a hax hay hn
  have hVdvd : v n ∣ C * n := by
    rw [← Nat.factorization_prime_le_iff_dvd hvn (mul_ne_zero hC hn.ne')]
    intro p hp
    by_cases hpn : p ∣ v n
    · have hmem := hs (Nat.mem_primeFactors.mpr ⟨hp, hpn, hvn⟩)
      obtain ⟨t, ht, hdiv, hndiv⟩ := hE p hmem
      have htpos : 0 < t := (mem_Icc.mp ht).1
      have hvt := double_y_ne_zero a hax hay htpos
      have hfac := pell_factorization_le a hax hay hp htpos hn hdiv
      have hEt := mt (hp.pow_dvd_iff_le_factorization hvt).mpr hndiv
      have hpC : p^(E p) ∣ C := dvd_prod_of_mem (fun p => p^(E p)) hmem
      have hCp := (hp.pow_dvd_iff_le_factorization hC).1 hpC
      rw [Nat.factorization_mul hC hn.ne', Finsupp.add_apply]
      omega
    · change (v n).factorization p ≤ _
      rw [Nat.factorization_eq_zero_of_not_dvd hpn]
      exact Nat.zero_le _
  have hstep (i : ℕ) : 2 * v i ≤ v (i+1) := double_y_step a hax hay i
  have hgrow (i : ℕ) (hi : T+1 ≤ i) : C*i < v i := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    induction j with
    | zero => rw [Nat.add_zero]; exact hT
    | succ j ih =>
      have hpos : 1 ≤ T+1+j := by omega
      have hle : C * (T+1+j+1) ≤ 2 * (C*(T+1+j)) := by
        rw [mul_left_comm]
        exact Nat.mul_le_mul_left C (by omega)
      rw [Nat.add_succ]
      exact (hle.trans_lt (Nat.mul_lt_mul_of_pos_left (ih (by omega)) (by decide))).trans_le (hstep _)
  by_contra! h
  exact (not_lt_of_ge (Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hC) hn) hVdvd))
    (hgrow n h)

/-- The cutoff certificate exists independently of the prime tests. -/
theorem exists_index_certificate {d : ℤ} (a : Pell.Solution₁ d)
    (hax : 1 < a.x) (hay : 0 < a.y) (S : Finset ℕ) (hpS : ∀ p ∈ S, p.Prime) :
    let v := fun t : ℕ => (2 * (a^t).y).toNat
    ∃ (E : ℕ → ℕ) (T : ℕ),
      (∀ p ∈ S, ∃ t ∈ Icc 1 (p^4), p^2 ∣ v t ∧ ¬p^(E p+1) ∣ v t) ∧
      ((∏ p ∈ S, p^(E p)) * (T+1) : ℕ) < v (T+1) := by
  classical
  dsimp only
  let v (t : ℕ) := (2 * (a^t).y).toNat
  have hperiod (p : ℕ) (hp : p ∈ S) : ∃ t ∈ Icc 1 (p^4), p^2 ∣ v t := by
    obtain ⟨t, ht, hbound, hdiv⟩ := exists_y_dvd a (pow_ne_zero 2 (hpS p hp).ne_zero)
    have ht' : t ≤ p^4 := by
      simpa only [← pow_add, show 2 + 2 = 4 by decide] using hbound
    refine ⟨t, mem_Icc.mpr ⟨ht, ht'⟩, ?_⟩
    rw [← Int.natCast_dvd_natCast, show (v t : ℤ) = 2 * (a^t).y from
      Int.toNat_of_nonneg (double_y_nonneg a hax hay t)]
    exact dvd_mul_of_dvd_right hdiv 2
  let E (p : ℕ) := if hp : p ∈ S then (v (Classical.choose (hperiod p hp))).factorization p else 0
  let C := ∏ p ∈ S, p^(E p)
  let T := 2*(C+1)-1
  refine ⟨E, T, ?_, ?_⟩
  · intro p hp
    let t := Classical.choose (hperiod p hp)
    have ht := Classical.choose_spec (hperiod p hp)
    have htpos : 0 < t := (mem_Icc.mp ht.1).1
    refine ⟨t, ht.1, ht.2, ?_⟩
    change ¬p^(E p+1) ∣ v t
    rw [(hpS p hp).pow_dvd_iff_le_factorization (double_y_ne_zero a hax hay htpos)]
    change ¬E p + 1 ≤ (v t).factorization p
    have hEq : E p = (v t).factorization p := dif_pos hp
    rw [hEq]
    exact Nat.not_succ_le_self _
  · change C*(T+1) < v (T+1)
    have hT : T+1 = (C+1)+(C+1) := by dsimp [T]; omega
    have hlow (i : ℕ) (hi : 0 < i) : 2^i ≤ v i := by
      induction i with
      | zero => omega
      | succ i ih =>
        cases i with
        | zero =>
          simp only [Nat.zero_add, pow_one, v]
          omega
        | succ i =>
          rw [pow_succ']
          exact (Nat.mul_le_mul_left 2 (ih (Nat.succ_pos _))).trans (double_y_step a hax hay _)
    have hpow : (C+1)+(C+1) ≤ 2^(C+1) := by
      rw [pow_succ']
      have h : C < 2^C := Nat.lt_two_pow_self
      omega
    calc
      C*(T+1) < (T+1)*(T+1) := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ ≤ 2^(T+1) := by rw [hT, pow_add]; exact Nat.mul_le_mul hpow hpow
      _ ≤ v (T+1) := hlow _ (by omega)

private theorem exists_pell_candidate (S : Finset ℕ) (h2 : 2 ∈ S)
    (hpS : ∀ p ∈ S, p.Prime) {x : ℕ} (hx : 0 < x)
    (hs : ∀ p : ℕ, p.Prime → p ∣ x * (x+1) → p ∈ S) :
    ∃ D ∈ (∏ p ∈ S, p).divisors,
      ∃ a : Pell.Solution₁ (D : ℤ), Pell.IsFundamental a ∧
        ∃ n : ℕ, 0 < n ∧ (a^n).x = 2 * (x : ℤ) + 1 ∧
          (2 * (a^n).y).toNat.primeFactors ⊆ S := by
  have hpos : 0 < 4 * (x * (x+1)) := by positivity
  obtain ⟨D, y, hD, hy, heq, hsq⟩ := Nat.sq_mul_squarefree_of_pos hpos
  have hsup (p : ℕ) (hp : p.Prime) (h : p ∣ 4 * (x * (x+1))) : p ∈ S := by
    rcases hp.dvd_mul.mp h with h4 | hprod
    · have hpd : p ∣ 2 := hp.dvd_of_dvd_pow (n := 2) h4
      obtain rfl := (Nat.dvd_prime Nat.prime_two).mp hpd |>.resolve_left hp.ne_one
      exact h2
    · exact hs p hp hprod
  have hDmember : D ∈ (∏ p ∈ S, p).divisors := by
    rw [Nat.mem_divisors]
    constructor
    · have hsubset : D.primeFactors ⊆ S := by
        intro p hp
        obtain ⟨hprime, hpd, _⟩ := Nat.mem_primeFactors.mp hp
        apply hsup p hprime
        exact hpd.trans (heq ▸ dvd_mul_left D (y^2))
      simpa only [Nat.prod_primeFactors_of_squarefree hsq] using
        prod_dvd_prod_of_subset D.primeFactors S (fun p => p) hsubset
    · exact prod_ne_zero_iff.mpr (fun p hp => (hpS p hp).ne_zero)
  have heqZ : (y : ℤ)^2 * D = 4 * ((x : ℤ) * (x+1)) := by exact_mod_cast heq
  let b : Pell.Solution₁ (D : ℤ) := Pell.Solution₁.mk (2*(x : ℤ)+1) y (by nlinarith)
  have hbx : 1 < b.x := by
    dsimp [b]
    have hxZ : 0 < (x : ℤ) := by exact_mod_cast hx
    omega
  have hby : 0 < b.y := by
    change 0 < (y : ℤ)
    exact_mod_cast hy
  have hgen : ∃ a : Pell.Solution₁ (D : ℤ), Pell.IsFundamental a :=
    Pell.IsFundamental.exists_of_not_isSquare (Pell.Solution₁.d_pos_of_one_lt_x hbx)
      (Pell.Solution₁.d_nonsquare_of_one_lt_x hbx)
  let a := Classical.choose hgen
  have ha : Pell.IsFundamental a := Classical.choose_spec hgen
  obtain ⟨n, hn⟩ := ha.eq_pow_of_nonneg (show 0 < b.x by omega) hby.le
  have hnpos : 0 < n := by
    by_contra! h
    interval_cases n
    simp [hn] at hby
  have hsmooth : (2 * (a^n).y).toNat.primeFactors ⊆ S := by
    intro p hp
    obtain ⟨hp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
    rw [← hn] at hpd
    change p ∣ (2 * (y : ℤ)).toNat at hpd
    rw [← Int.ofNat_two, ← Int.natCast_mul, Int.toNat_natCast] at hpd
    rcases hp.dvd_mul.mp hpd with hpd | hpd
    · obtain rfl := (Nat.dvd_prime Nat.prime_two).mp hpd |>.resolve_left hp.ne_one
      exact h2
    · apply hsup p hp
      rw [← heq]
      exact (hpd.trans (dvd_pow_self y (by decide : 2 ≠ 0))).trans (dvd_mul_right _ _)
  exact ⟨D, hDmember, a, ha, n, hnpos, (congrArg Pell.Solution₁.x hn).symm, hsmooth⟩

private theorem first_two_smooth {k₁ k₂ n d : ℕ} (hk₁ : 2 ≤ k₁) (hd : k₁ ≤ d)
    (h : (∏ i ∈ Icc 1 k₁, (n + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n + d + j)).primeFactors) :
    ∀ p : ℕ, p.Prime → p ∣ (n+1) * (n+2) →
      p ∈ (∏ j ∈ Icc 0 k₂, (d - 1 + j)).primeFactors := by
  intro p hp hpd
  obtain ⟨i, hi1, hi2, hpi⟩ : ∃ i : ℕ, 1 ≤ i ∧ i ≤ 2 ∧ p ∣ n+i := by
    rcases hp.dvd_mul.mp hpd with h | h
    · exact ⟨1, by decide, by decide, h⟩
    · exact ⟨2, by decide, by decide, h⟩
  have hleft : p ∈ (∏ i ∈ Icc 1 k₁, (n + i)).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hp, hpi.trans (dvd_prod_of_mem (n + ·) (mem_Icc.mpr ⟨hi1, hi2.trans hk₁⟩)),
      prod_ne_zero_iff.mpr fun j hj => by have := (mem_Icc.mp hj).1; omega⟩
  rw [h, Nat.mem_primeFactors] at hleft
  obtain ⟨j, hj, hpj⟩ := hp.prime.dvd_finsetProd_iff _ |>.mp hleft.2.1
  obtain ⟨hj₁, hj₂⟩ := mem_Icc.mp hj
  have hδ : (n + d + j) - (n + i) = d - 1 + (j + 1 - i) := by omega
  have hdiv := Nat.dvd_sub hpj hpi
  rw [hδ] at hdiv
  rw [Nat.mem_primeFactors]
  exact ⟨hp, hdiv.trans (dvd_prod_of_mem (fun j => d - 1 + j)
    (mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩)),
    prod_ne_zero_iff.mpr (fun j _ => by omega)⟩

/-- Finite Pell verification for separations through 38. -/
def H1 : Prop :=
  ∀ d ∈ Icc 3 38, ∀ k₂ ∈ Icc 3 d,
    let S := insert 2 (∏ j ∈ Icc 0 k₂, (d - 1 + j)).primeFactors
    let M := ∏ p ∈ S, p
    ∀ D : ℕ, D ∈ M.divisors → ¬IsSquare (D : ℤ) →
      ∃ U V : ℕ, 1 < U ∧ 0 < V ∧ (U : ℤ)^2 - (D : ℤ) * (V : ℤ)^2 = 1 ∧
        ∀ u ∈ Icc 2 U, ∀ v ∈ Icc 1 V, (u : ℤ)^2 - (D : ℤ) * (v : ℤ)^2 = 1 →
          let y := fun t : ℕ => (2 * ((⟨u, v⟩ : ℤ√(D : ℤ))^t).im).toNat
          ∃ (E : ℕ → ℕ) (T : ℕ),
            (∀ p ∈ S, ∃ t ∈ Icc 1 (p^4), p^2 ∣ y t ∧ ¬p^(E p+1) ∣ y t) ∧
            (∏ p ∈ S, p^(E p)) * (T+1) < y (T+1) ∧
            ∀ e ∈ Icc 1 T, (y e).primeFactors ⊆ S →
              let n := ((((⟨u, v⟩ : ℤ√(D : ℤ))^e).re.toNat) - 3) / 2
              ∀ k₁ ∈ Icc k₂ d,
                (∏ i ∈ Icc 1 k₁, (n + i)).primeFactors =
                  (∏ j ∈ Icc 1 k₂, (n + d + j)).primeFactors →
                ∃ p ∈ Icc n (n+d), p.Prime

/-- The bounded test at each remaining separation. -/
def H2 : Prop :=
  ∀ d : ℕ, 38 < d → ∀ k₂ ∈ Icc 3 d,
    let S := insert 2 (∏ j ∈ Icc 0 k₂, (d - 1 + j)).primeFactors
    let M := ∏ p ∈ S, p
    ∀ D : ℕ, D ∈ M.divisors → ¬IsSquare (D : ℤ) →
      ∃ U V : ℕ, 1 < U ∧ 0 < V ∧ (U : ℤ)^2 - (D : ℤ) * (V : ℤ)^2 = 1 ∧
        ∀ u ∈ Icc 2 U, ∀ v ∈ Icc 1 V, (u : ℤ)^2 - (D : ℤ) * (v : ℤ)^2 = 1 →
          let y := fun t : ℕ => (2 * ((⟨u, v⟩ : ℤ√(D : ℤ))^t).im).toNat
          ∃ (E : ℕ → ℕ) (T : ℕ),
            (∀ p ∈ S, ∃ t ∈ Icc 1 (p^4), p^2 ∣ y t ∧ ¬p^(E p+1) ∣ y t) ∧
            (∏ p ∈ S, p^(E p)) * (T+1) < y (T+1) ∧
            ∀ e ∈ Icc 1 T, (y e).primeFactors ⊆ S →
              let n := ((((⟨u, v⟩ : ℤ√(D : ℤ))^e).re.toNat) - 3) / 2
              ∀ k₁ ∈ Icc k₂ d,
                (∏ i ∈ Icc 1 k₁, (n + i)).primeFactors =
                  (∏ j ∈ Icc 1 k₂, (n + d + j)).primeFactors →
                ∃ p ∈ Icc n (n+d), p.Prime

theorem main : H1 → H2 → type_of% @Erdos931.erdos_931.variants.exists_prime := by
  intro short long k₁ k₂ n₁ n₂ hk hmin horder heq
  let d := n₂ - n₁
  have hnd : n₁ + d = n₂ := by dsimp [d]; omega
  have hkd : k₁ ≤ d := by dsimp [d]; omega
  have hd : 3 ≤ d := hmin.trans (hk.trans hkd)
  have hk₂ : k₂ ∈ Icc 3 d := mem_Icc.mpr ⟨hmin, hk.trans hkd⟩
  have heq' : (∏ i ∈ Icc 1 k₁, (n₁ + i)).primeFactors =
      (∏ j ∈ Icc 1 k₂, (n₁ + d + j)).primeFactors := by rw [hnd]; exact heq
  let S := insert 2 (∏ j ∈ Icc 0 k₂, (d - 1 + j)).primeFactors
  have h2 : 2 ∈ S := mem_insert_self _ _
  have hS : ∀ p ∈ S, p.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (Nat.mem_primeFactors.mp hp).1
  obtain ⟨D, hD, a, ha, e, hepos, hx, hysmooth⟩ :=
    exists_pell_candidate S h2 hS (x := n₁ + 1) (by omega) fun p hp hpdiv =>
      mem_insert_of_mem (first_two_smooth (by omega) hkd heq' p hp (by simpa using hpdiv))
  have hcases := fun h : d ≤ 38 => short d (mem_Icc.mpr ⟨hd, h⟩) k₂ hk₂ D hD ha.d_nonsquare
  obtain ⟨U, V, hU, hV, heqUV, hverify⟩ :=
    if h : d ≤ 38 then hcases h
    else long d (lt_of_not_ge h) k₂ hk₂ D hD ha.d_nonsquare
  let b := Pell.Solution₁.mk (d := (D : ℤ)) U V heqUV
  have hbX : 1 < b.x := by change 1 < (U : ℤ); exact_mod_cast hU
  have hbY : 0 < b.y := by change 0 < (V : ℤ); exact_mod_cast hV
  have hX := ha.x_le_x hbX
  have hY := ha.y_le_y hbX hbY
  let u := a.x.toNat
  let v := a.y.toNat
  have hu : (u : ℤ) = a.x := Int.toNat_of_nonneg ha.x_pos.le
  have hv : (v : ℤ) = a.y := Int.toNat_of_nonneg ha.2.1.le
  have huU : u ∈ Icc 2 U := by
    have hh := ha.1
    change a.x ≤ (U : ℤ) at hX
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hvV : v ∈ Icc 1 V := by
    have hh := ha.2.1
    change a.y ≤ (V : ℤ) at hY
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hequv : (u : ℤ)^2 - (D : ℤ) * (v : ℤ)^2 = 1 := by
    rw [hu, hv]
    exact a.prop
  have hcoe : (⟨(u : ℤ), (v : ℤ)⟩ : ℤ√(D : ℤ)) = (a : ℤ√(D : ℤ)) := by
    rw [hu, hv]
    exact Zsqrtd.ext rfl rfl
  have hn : ((((⟨(u : ℤ), (v : ℤ)⟩ : ℤ√(D : ℤ))^e).re.toNat) - 3) / 2 = n₁ := by
    rw [hcoe, ← (SubmonoidClass.coe_pow a e : (↑(a ^ e) : ℤ√(D : ℤ)) = _)]
    change ((a ^ e).x.toNat - 3) / 2 = n₁
    rw [hx]
    omega
  obtain ⟨E, T, hE, hT, hcandidates⟩ := hverify u huU v hvV hequv
  have hy (j : ℕ) : ((⟨(u : ℤ), (v : ℤ)⟩ : ℤ√(D : ℤ))^j).im = (a^j).y := by
    rw [hcoe, ← (SubmonoidClass.coe_pow a j : (↑(a ^ j) : ℤ√(D : ℤ)) = _)]
    rfl
  simp only [hy] at hE hT
  have hle := certified_index_bound a ha.1 ha.2.1 S hS E T hE hT hepos hysmooth
  have hcheck := hcandidates e (mem_Icc.mpr ⟨hepos, hle⟩)
    (by simpa only [hy] using hysmooth)
  dsimp only at hcheck
  rw [hn] at hcheck
  obtain ⟨p, hp, hprime⟩ := hcheck k₁ (mem_Icc.mpr ⟨hk, hkd⟩) heq'
  rw [mem_Icc, hnd] at hp
  exact ⟨p, hprime, hp.1, hp.2⟩

end OMA.R_Erdos931_erdos_931_variants_exists_prime_R2
