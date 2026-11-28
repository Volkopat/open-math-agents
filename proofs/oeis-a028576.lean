import OMAStatements.S_oeis_a028576
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace A028576Work
open scoped BigOperators

theorem six_mul_sum_range_sq (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, (i : ℤ)^2) =
      ((n : ℤ) - 1) * n * (2 * (n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      simp only [Nat.cast_succ]
      ring

theorem six_mul_sum_range_sq_diff (p x : ℕ) :
    6 * ((∑ i ∈ Finset.range (p*x), (i : ℤ)^2) -
         (p : ℤ)^2 * (∑ i ∈ Finset.range x, (i : ℤ)^2)) =
      (p : ℤ) * x * ((p : ℤ) - 1) * (2 * (p : ℤ) * (x : ℤ)^2 - 1) := by
  rw [mul_sub, mul_left_comm 6 ((p : ℤ)^2), six_mul_sum_range_sq, six_mul_sum_range_sq]
  push_cast
  ring

theorem pair_expand {R : Type*} [CommRing R] {a i j x y : R}
    (h : i + j = a) (hx : i * x = 1) (hy : j * y = 1) (hc : a^3 = 0) :
    (1 + a * x) * (1 + a * y) = 1 - 2 * a^2 * x^2 := by
  have hxy : x + y = a * x * y := by
    calc
      x+y = (j*y)*x+(i*x)*y := by simp [hy,hx]
      _ = a*x*y := by rw [←h]; ring
  have h₂ : a^2*x*y + a^2*x^2 = 0 := by
    calc
      _ = a^2*x*(x+y) := by ring
      _ = a^3*x^2*y := by rw [hxy]; ring
      _ = 0 := by rw [hc]; ring
  calc
    _ = 1+a*(x+y)+a^2*x*y := by ring
    _ = 1+2*(a^2*x*y) := by rw [hxy]; ring
    _ = 1 - 2*a^2*x^2 := by rw [eq_neg_of_add_eq_zero_left h₂]; ring

theorem prod_linear {R ι : Type*} [CommRing R] (s : Finset ι) (z : ι → R)
    (a : R) (hc : a^3 = 0) :
    (∏ i ∈ s, (1 + a^2 * z i)) = 1 + a^2 * (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
      have h₄ : a^4 = 0 := by rw [show 4 = 3+1 by decide, pow_add, hc]; simp
      calc
        _ = 1 + a^2 * (z i + ∑ j ∈ s, z j) + a^4 * z i * (∑ j ∈ s, z j) := by ring
        _ = _ := by simp [h₄]

theorem paired_prod {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → ι)
    (v x : ι → R) (a : R) (hfs : ∀ i ∈ s, f i ∈ s)
    (hinv : ∀ i ∈ s, f (f i) = i)
    (hpair : ∀ i ∈ s, v i + v (f i) = a)
    (hx : ∀ i ∈ s, v i * x i = 1) (hc : a^3 = 0) :
    (∏ i ∈ s, (1 + a * x i))^2 = 1 - 2*a^2 * (∑ i ∈ s, (x i)^2) := by
  have hb : (∏ i ∈ s, (1 + a * x (f i))) = ∏ i ∈ s, (1 + a * x i) :=
    Finset.prod_nbij' f f hfs hfs hinv hinv (fun _ _ => rfl)
  calc
    _ = (∏ i ∈ s, (1 + a * x i)) * (∏ i ∈ s, (1 + a * x (f i))) := by
      rw [hb, pow_two]
    _ = ∏ i ∈ s, (1 + a^2 * (-2 * (x i)^2)) := by
      rw [←Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      rw [pair_expand (hpair i hi) (hx i hi) (hx (f i) (hfs i hi)) hc]
      ring
    _ = _ := by rw [prod_linear _ _ _ hc, ←Finset.mul_sum]; ring

theorem six_mul_sum_sq_units (p x : ℕ) (hp : 0 < p) :
    6 * (∑ i ∈ (Finset.range (p*x)).filter (fun i => ¬ p ∣ i), (i : ℤ)^2) =
      (p : ℤ) * x * ((p : ℤ) - 1) * (2 * (p : ℤ) * (x : ℤ)^2 - 1) := by
  have hpart := Finset.sum_filter_add_sum_filter_not (Finset.range (p*x))
      (fun i : ℕ => p ∣ i) (f := fun i : ℕ => (i : ℤ)^2)
  have hmult : (∑ i ∈ (Finset.range (p*x)).filter (fun i => p ∣ i), (i : ℤ)^2) =
      (p : ℤ)^2 * (∑ i ∈ Finset.range x, (i : ℤ)^2) := by
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_nbij' (fun i : ℕ => p*i) (fun i : ℕ => i/p) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left hi hp), dvd_mul_right p i⟩
    · intro i hi
      exact Finset.mem_range.mpr ((Nat.div_lt_iff_lt_mul hp).2 (by
        rw [mul_comm]; exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1))
    · intro i _
      rw [mul_comm, Nat.mul_div_cancel i hp]
    · intro i hi
      rw [mul_comm, Nat.div_mul_cancel (Finset.mem_filter.mp hi).2]
    · intro i _
      push_cast
      ring
  rw [hmult] at hpart
  have heq : (∑ i ∈ (Finset.range (p*x)).filter (fun i => ¬ p ∣ i), (i : ℤ)^2) =
      (∑ i ∈ Finset.range (p*x), (i : ℤ)^2) -
      (p : ℤ)^2 * (∑ i ∈ Finset.range x, (i : ℤ)^2) := by
    rw [←hpart]
    ring
  rw [heq, six_mul_sum_range_sq_diff]


end A028576Work

namespace A028576Work
open scoped BigOperators

/-- Product of factors before the cut not divisible by p; the cut is itself divisible by p. -/
def stripped (p t : ℕ) : ℕ := ∏ i ∈ Finset.range t, if p ∣ i then 1 else i

theorem factorial_split (p x : ℕ) (hp : 0 < p) :
    (p*x).factorial = p^x * x.factorial * stripped p (p*x) := by
  have hposit : (p*x).factorial = ∏ i ∈ Finset.Ico 1 (p*x+1), i :=
    (Finset.prod_Ico_id_eq_factorial (p*x)).symm
  have hmul : (∏ i ∈ (Finset.Ico 1 (p*x+1)).filter (fun i => p ∣ i), i) =
      p^x * x.factorial := by
    have card : (Finset.Ico 1 (x+1)).card = x := by simp
    have hconst : (∏ _i ∈ Finset.Ico 1 (x+1), p) = p^x := by
      rw [Finset.prod_const, card]
    rw [← Finset.prod_Ico_id_eq_factorial x, ← hconst, ← Finset.prod_mul_distrib]
    symm
    refine Finset.prod_nbij' (fun i : ℕ => p*i) (fun i : ℕ => i/p) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_Ico, Nat.lt_succ_iff] at hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨?_, Nat.lt_succ_of_le (Nat.mul_le_mul_left _ hi.2)⟩, dvd_mul_right p i⟩
      exact Nat.succ_le_iff.mpr (Nat.mul_pos hp hi.1)
    · intro i hi
      have hm := Finset.mem_filter.mp hi
      have hij := Finset.mem_Ico.mp hm.1
      have hh := Nat.div_mul_cancel hm.2
      apply Finset.mem_Ico.mpr
      constructor
      · apply Nat.one_le_iff_ne_zero.mpr
        intro he
        rw [he, zero_mul] at hh
        exact (Nat.ne_of_gt hij.1) hh.symm
      · apply Nat.lt_succ_of_le
        calc
          i/p ≤ (p*x)/p := Nat.div_le_div_right (Nat.le_of_lt_succ hij.2)
          _ = x := Nat.mul_div_cancel_left x hp
    · intro i _
      rw [mul_comm, Nat.mul_div_cancel i hp]
    · intro i hi
      rw [mul_comm, Nat.div_mul_cancel (Finset.mem_filter.mp hi).2]
    · intro i _
      rfl
  have hrest : (∏ i ∈ (Finset.Ico 1 (p*x+1)).filter (fun i => ¬p ∣ i), i) =
      stripped p (p*x) := by
    unfold stripped
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
    have heq : (Finset.Ico 1 (p*x+1)).filter (fun i => ¬p ∣ i) =
        (Finset.range (p*x)).filter (fun i => ¬p ∣ i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
      constructor
      · rintro ⟨⟨hi, hj⟩, hn⟩
        have hne : i ≠ p*x := fun he => hn (he ▸ dvd_mul_right p x)
        exact ⟨by omega, hn⟩
      · rintro ⟨hi, hn⟩
        have hp : i ≠ 0 := fun hh => hn (hh ▸ dvd_zero p)
        exact ⟨⟨by omega, by omega⟩, hn⟩
    rw [heq]
  rw [hposit, ← Finset.prod_filter_mul_prod_filter_not _ (fun i => p∣i), hmul, hrest]

theorem stripped_double (p x : ℕ) :
    stripped p (p*x + p*x) = stripped p (p*x) *
      ∏ i ∈ (Finset.range (p*x)).filter (fun i => ¬p ∣ i), (p*x+i) := by
  unfold stripped
  rw [Finset.prod_range_add]
  congr 1
  trans ∏ i ∈ Finset.range (p*x), if p ∣ i then 1 else (p*x+i)
  · apply Finset.prod_congr rfl
    intro i hi
    simp only [← Nat.dvd_add_iff_right (dvd_mul_right p x)]
  · rw [Finset.prod_ite, Finset.prod_const_one, one_mul]

theorem choose_stripped (p x : ℕ) (hp : 0 < p) :
    (p*x+p*x).choose (p*x) * stripped p (p*x)^2 =
      (x+x).choose x * stripped p (p*x) *
        ∏ i ∈ (Finset.range (p*x)).filter (fun i => ¬p ∣ i), (p*x+i) := by
  have hx : 0 < p^x * x.factorial := Nat.mul_pos (Nat.pow_pos hp) (Nat.factorial_pos x)
  apply Nat.mul_right_cancel (Nat.pow_pos hx (n := 2))
  calc
    _ = (p*x+p*x).factorial := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial (p*x) (p*x), factorial_split p x hp]
      ring
    _ = _ := by
      rw [← Nat.mul_add, factorial_split p (x+x) hp, pow_add,
        ← Nat.add_choose_mul_factorial_mul_factorial x x,
        Nat.mul_add, stripped_double]
      ring

theorem two_dvd_choose_self {x : ℕ} (hx : 0 < x) : 2 ∣ (x+x).choose x := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hx)
  rw [show a+1+(a+1) = ((a+1)+a)+1 by omega, Nat.choose_succ_succ]
  have hh : ((a+1)+a).choose (a+1) = ((a+1)+a).choose a := by
    convert Nat.choose_symm (Nat.le_add_left a (a+1)) using 2 <;> omega
  rw [hh]
  exact ⟨((a+1)+a).choose a, by omega⟩


end A028576Work

namespace A028576Work
open scoped BigOperators

theorem cast_mul_inv_of_prime_pow {p r i : ℕ} (hp : p.Prime) (hn : ¬ p ∣ i) :
    (i : ZMod (p^r)) * (i : ZMod (p^r))⁻¹ = 1 := by
  apply ZMod.mul_inv_of_unit
  have h := ((hp.coprime_iff_not_dvd).mpr hn).symm.pow_right r
  exact (ZMod.unitOfCoprime i h).isUnit

theorem inverse_square_sum_mod (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    (∑ i ∈ (Finset.range (p^r)).filter (fun j => ¬p ∣ j), ((i : ZMod (p^r))⁻¹)^2) =
      ∑ i ∈ (Finset.range (p^r)).filter (fun j => ¬p ∣ j), (i : ZMod (p^r))^2 := by
  letI : NeZero (p^r) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let s := (Finset.range (p^r)).filter (fun j => ¬p ∣ j)
  let f : ℕ → ℕ := fun i => ((i : ZMod (p^r))⁻¹).val
  have hfc : ∀ i, (f i : ZMod (p^r)) = (i : ZMod (p^r))⁻¹ :=
    fun i => ZMod.natCast_zmod_val ((i : ZMod (p^r))⁻¹)
  have hfs : ∀ i ∈ s, f i ∈ s := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    let u := Units.mkOfMulEqOne ((i : ZMod (p^r))⁻¹) (i : ZMod (p^r))
      (by rw [mul_comm]; exact cast_mul_inv_of_prime_pow hp hi')
    have hc : (f i).Coprime (p^r) := ZMod.val_coe_unit_coprime u
    have hc' := ((Nat.coprime_pow_right_iff hr (f i) p).mp hc).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      (hp.coprime_iff_not_dvd).mp hc'⟩
  have hff : ∀ i ∈ s, f (f i) = i := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hfi' := (Finset.mem_filter.mp (hfs i hi)).2
    have he : ((f i : ℕ) : ZMod (p^r))⁻¹ = (i : ZMod (p^r)) := by
      calc
        _ = ((i : ZMod (p^r)) * (i : ZMod (p^r))⁻¹) * ((f i : ℕ) : ZMod (p^r))⁻¹ := by
          rw [cast_mul_inv_of_prime_pow hp hi', one_mul]
        _ = (i : ZMod (p^r)) * ((f i : ZMod (p^r)) * ((f i : ℕ) : ZMod (p^r))⁻¹) := by
          rw [hfc, mul_assoc]
        _ = _ := by rw [cast_mul_inv_of_prime_pow hp hfi', mul_one]
    change (((f i : ℕ) : ZMod (p^r))⁻¹).val = i
    rw [he, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  exact Finset.sum_nbij' f f hfs hfs hff hff (fun i _ => by rw [hfc])

theorem sum_periodic_multiples {R : Type*} [AddCommMonoid R] (q e : ℕ) (g : ℕ → R)
    (h : ∀ i, g (q + i) = g i) :
    (∑ i ∈ Finset.range (q * e), g i) = e • (∑ i ∈ Finset.range q, g i) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.mul_succ, add_comm (q*e) q, Finset.sum_range_add]
    simp only [h, ih, succ_nsmul]
    exact add_comm _ _

theorem inverse_square_sum_mod_multiple (p r e : ℕ) (hp : p.Prime) (hr : 0 < r) :
    (∑ i ∈ (Finset.range (p^r * e)).filter (fun j => ¬p ∣ j), ((i : ZMod (p^r))⁻¹)^2) =
      ∑ i ∈ (Finset.range (p^r * e)).filter (fun j => ¬p ∣ j), (i : ZMod (p^r))^2 := by
  have hd : p ∣ p^r := dvd_pow_self p (Nat.ne_of_gt hr)
  have hp' : ∀ i : ℕ, (¬ p ∣ p^r+i) ↔ ¬ p ∣ i :=
    fun i => not_congr (Nat.dvd_add_iff_right hd).symm
  simp only [Finset.sum_filter]
  rw [sum_periodic_multiples, sum_periodic_multiples]
  · congr 1
    simpa only [Finset.sum_filter] using inverse_square_sum_mod p r hp hr
  all_goals intro i; simp only [hp', Nat.cast_add, ZMod.natCast_self, zero_add]


end A028576Work

namespace A028576Bridge
open scoped BigOperators

theorem ratio_eq_prod {R ι : Type*} [CommRing R] (s : Finset ι)
    (v x : ι → R) (a A B : R) (hx : ∀ i ∈ s, v i * x i = 1)
    (hAB : A * (∏ i ∈ s, v i)^2 =
      B * (∏ i ∈ s, v i) * (∏ i ∈ s, (a+v i))) :
    A = B * (∏ i ∈ s, (1 + a*x i)) := by
  let U := ∏ i ∈ s, v i
  let V := ∏ i ∈ s, (a+v i)
  let W := ∏ i ∈ s, x i
  have hUW : U*W = 1 := by
    simp only [U,W,←Finset.prod_mul_distrib]
    trans ∏ _i ∈ s, (1 : R)
    · exact Finset.prod_congr rfl hx
    · simp
  have hVW : V*W = ∏ i ∈ s, (1+a*x i) := by
    simp only [V,W,←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [add_mul, hx i hi, add_comm]
  change A*U^2 = B*U*V at hAB
  calc
    _ = A*(U*W)^2 := by rw [hUW, one_pow, mul_one]
    _ = (A*U^2)*W^2 := by ring
    _ = (B*U*V)*W^2 := by rw [hAB]
    _ = B*(U*W)*(V*W) := by ring
    _ = _ := by rw [hUW, mul_one, hVW]


end A028576Bridge
namespace A028576Gauss
open A028576Work A028576Bridge
open scoped BigOperators

def H (t : ℕ) : ℕ := (t+t).choose t / 2

lemma choose_eq_two_mul_H {t : ℕ} (ht : 0 < t) : (t+t).choose t = 2 * H t := by
  rw [H, mul_comm, Nat.div_mul_cancel (two_dvd_choose_self ht)]

lemma gauss {p r e : ℕ} (hp : p.Prime) (he : 0 < e) :
    ((p : ℤ)^(r+1))^2 ∣ (H (p^(r+1)*e) : ℤ)^2 - (H (p^r*e) : ℤ)^2 ∧
    ((p : ℤ)^(r+1))^3 ∣ 3*((H (p^(r+1)*e) : ℤ)^2 - (H (p^r*e) : ℤ)^2) := by
  let q := p^(r+1)
  let x := p^r*e
  let t := q*e
  let R := ZMod (q^3)
  let S := ZMod q
  let T := ZMod (q^2)
  have hx : 0 < x := Nat.mul_pos (Nat.pow_pos hp.pos) he
  have ht : 0 < t := Nat.mul_pos (Nat.pow_pos hp.pos) he
  have htx : p*x = t := by simp only [t,q,x,pow_succ']; ring
  have hpp : p ∣ t := ⟨x, htx.symm⟩
  let s := (Finset.range t).filter (fun i => ¬ p ∣ i)
  have hfac := choose_stripped p x hp.pos
  rw [htx, choose_eq_two_mul_H ht, choose_eq_two_mul_H hx] at hfac
  have hhalf : H t * stripped p t^2 = H x * stripped p t *
      (∏ i ∈ s, (t+i)) := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    change 2*(H t * stripped p t^2) = 2*(H x*stripped p t*(∏ i ∈ s, (t+i)))
    simpa only [mul_assoc] using hfac
  have hsprod : stripped p t = ∏ i ∈ s, i := by
    unfold stripped s
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul]
  rw [hsprod] at hhalf
  let f : ℕ → ℕ := fun i => t-i
  have hfs : ∀ i ∈ s, f i ∈ s := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hi, hd⟩
    have hi0 : 0 < i := by
      by_contra! h
      have hz : i = 0 := by omega
      exact hd (hz ▸ dvd_zero p)
    have hlt := Finset.mem_range.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (by change t-i < t; omega), ?_⟩
    intro hf
    have hd' := Nat.dvd_sub hpp hf
    apply hd
    convert hd' using 1
    change i = t-(t-i)
    omega
  have hinv : ∀ i ∈ s, f (f i) = i := by
    intro i hi
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    change t-(t-i)=i
    omega
  have hcast : ∀ i ∈ s, (i : R) + (f i : R) = (t : R) := by
    intro i hi
    rw [←Nat.cast_add]
    congr 1
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    change i+(t-i)=t
    omega
  have hhPow : q^3 = p^((r+1)*3) := by rw [pow_mul]
  have hu : ∀ i ∈ s, (i : R) * (i : R)⁻¹ = 1 := by
    intro i hi
    have hc := (Finset.mem_filter.mp hi).2
    apply ZMod.mul_inv_of_unit
    exact (ZMod.isUnit_iff_coprime i (q^3)).mpr
      (by rw [hhPow]; exact ((hp.coprime_iff_not_dvd).mpr hc).symm.pow_right _)
  have hq : (q : R)^3 = 0 := by rw [←Nat.cast_pow]; exact ZMod.natCast_self (q^3)
  have hcube : (t : R)^3 = 0 := by rw [show (t : R) = (q : R)*(e : R) by exact Nat.cast_mul q e, mul_pow, hq, zero_mul]
  have hhAB : (H t : R) * (∏ i ∈ s, (i : R))^2 =
      (H x : R) * (∏ i ∈ s, (i : R)) * (∏ i ∈ s, ((t : R)+(i : R))) := by
    have hc := congrArg (fun u : ℕ => (u : R)) hhalf
    push_cast at hc
    exact hc
  have hRatio := ratio_eq_prod s (fun i : ℕ => (i : R)) (fun i : ℕ => (i : R)⁻¹)
    (t : R) (H t : R) (H x : R) hu hhAB
  have hPair := paired_prod s f (fun i : ℕ => (i : R)) (fun i : ℕ => (i : R)⁻¹)
    (t : R) hfs hinv hcast hu hcube
  let L : R := ∑ i ∈ s, ((i : R)⁻¹)^2
  have hdif : (H t : R)^2 - (H x : R)^2 = -2*(H x : R)^2*(t : R)^2*L := by
    rw [hRatio, mul_pow, hPair]
    change _ = -2*(H x : R)^2*(t : R)^2*(∑ i ∈ s, ((i : R)⁻¹)^2)
    ring
  have hd32 : q^2 ∣ q^3 := by
    rw [show 3 = 2+1 by decide, pow_succ]
    exact dvd_mul_right _ _
  let psi : R →+* T := ZMod.castHom hd32 T
  have hsmallRaw := congrArg psi hdif
  have hqsmall : (q : T)^2 = 0 := by
    rw [←Nat.cast_pow]; exact ZMod.natCast_self (q^2)
  have htsmall : (t : T)^2 = 0 := by
    rw [show (t : T) = (q : T)*(e : T) by exact Nat.cast_mul q e, mul_pow, hqsmall, zero_mul]
  have hsmall : (H t : T)^2 - (H x : T)^2 = 0 := by
    simp only [map_sub, map_mul, map_pow, map_neg] at hsmallRaw
    rw [show psi (H t : R) = (H t : T) from map_natCast psi (H t),
      show psi (H x : R) = (H x : T) from map_natCast psi (H x),
      show psi (t : R) = (t : T) from map_natCast psi t, htsmall, mul_zero, zero_mul] at hsmallRaw
    exact hsmallRaw
  have hd31 : q ∣ q^3 := dvd_pow_self q (by decide)
  let phi : R →+* S := ZMod.castHom hd31 S
  have hInv : ∀ i ∈ s, phi ((i : R)⁻¹) = (i : S)⁻¹ := by
    intro i hi
    have h₁ : (i : S)*phi ((i : R)⁻¹) = 1 := by
      have hm := congrArg phi (hu i hi)
      rw [map_mul, map_one, show phi (i : R) = (i : S) from map_natCast phi i] at hm
      exact hm
    have hc := (Finset.mem_filter.mp hi).2
    have h₂ : (i : S)*(i : S)⁻¹ = 1 := cast_mul_inv_of_prime_pow hp hc
    calc
      _ = ((i : S)*(i : S)⁻¹) * phi ((i : R)⁻¹) := by rw [h₂, one_mul]
      _ = (i : S)⁻¹ * ((i : S)*phi ((i : R)⁻¹)) := by ring
      _ = _ := by rw [h₁, mul_one]
  have hphi : phi L = ∑ i ∈ s, (i : S)^2 := by
    unfold L
    rw [map_sum]
    trans ∑ i ∈ s, ((i : S)⁻¹)^2
    · apply Finset.sum_congr rfl
      intro i hi
      rw [map_pow, hInv i hi]
    · exact inverse_square_sum_mod_multiple p (r+1) e hp (Nat.succ_pos r)
  have hsum := congrArg (Int.castRingHom S) (six_mul_sum_sq_units p x hp.pos)
  have hqzero : (q : S) = 0 := ZMod.natCast_self q
  have htzero : (t : S) = 0 := by rw [show (t : S) = (q : S)*(e : S) by exact Nat.cast_mul q e, hqzero, zero_mul]
  have h6sum : 6 * (∑ i ∈ s, (i : S)^2) = 0 := by
    have hsum' : (6 : S) * (∑ i ∈ s, (i : S)^2) =
       (p : S)*(x : S)*((p : S)-1)*(2*(p : S)*(x : S)^2-1) := by
      simp only [map_mul, map_sub, map_pow, map_sum, map_natCast, map_ofNat, map_one] at hsum
      rw [htx] at hsum
      exact hsum
    rwa [←Nat.cast_mul, htx, htzero, zero_mul, zero_mul] at hsum' 
  have hz : phi (6*L) = 0 := by
    rw [map_mul, map_ofNat, hphi, h6sum]
  letI : NeZero (q^3) := ⟨pow_ne_zero _ (pow_ne_zero _ hp.ne_zero)⟩
  have hNatVal : (↑(6*L : R).val : R) = 6*L := ZMod.natCast_zmod_val _
  have hzero : ((6*L : R).val : S) = 0 := by
    calc
      _ = phi ((6*L : R).val : R) := by rw [map_natCast]
      _ = _ := by rw [hNatVal, hz]
  obtain ⟨b, hb⟩ := (ZMod.natCast_eq_zero_iff _ q).mp hzero
  have hKill : (q : R)^2 * (6*L) = 0 := by
    rw [←hNatVal, hb, Nat.cast_mul]
    calc
      _ = (q : R)^3*(b : R) := by ring
      _ = _ := by rw [hq, zero_mul]
  have hLarge : 3*((H t : R)^2 - (H x : R)^2) = 0 := by
    rw [hdif, show (t : R) = (q : R)*(e : R) by exact Nat.cast_mul q e]
    calc
      _ = -((H x : R)^2*(e : R)^2)*((q : R)^2*(6*L)) := by ring
      _ = _ := by rw [hKill, mul_zero]
  constructor
  · have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((H t : ℤ)^2-(H x : ℤ)^2) (q^2)).mp (by push_cast; exact hsmall)
    exact_mod_cast hh
  · have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd
      (3*((H t : ℤ)^2-(H x : ℤ)^2)) (q^3)).mp (by push_cast; exact hLarge)
    exact_mod_cast hh

end A028576Gauss
namespace A028576Final
open A028576Gauss
open scoped BigOperators
open ArithmeticFunction

lemma gcd_factor {a b A B : ℕ} (ha : a ∣ A) (hb : b ∣ B) (h : A.Coprime B) :
    (a*b).gcd A = a := by
  obtain ⟨c, hc⟩ := ha
  have hd : c ∣ A := ⟨a, by rw [hc, mul_comm]⟩
  have hh := (h.coprime_dvd_left hd).coprime_dvd_right hb
  rw [hc, Nat.gcd_mul_left, hh.symm.gcd_eq_one, mul_one]

lemma sum_coprime_divs {M : Type*} [AddCommMonoid M] {A B : ℕ}
    (hA : 0 < A) (hB : 0 < B) (h : A.Coprime B) (g : ℕ → M) :
    (∑ d ∈ (A*B).divisors, g d) =
      ∑ a ∈ A.divisors, ∑ b ∈ B.divisors, g (a*b) := by
  classical
  rw [←Finset.sum_product']
  symm
  refine Finset.sum_nbij (fun ab : ℕ × ℕ => ab.1*ab.2) ?_ ?_ ?_ ?_
  · intro ab hab
    rcases Finset.mem_product.mp hab with ⟨ha,hb⟩
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul (Nat.mem_divisors.mp ha).1
      (Nat.mem_divisors.mp hb).1, Nat.ne_of_gt (Nat.mul_pos hA hB)⟩
  · rintro ⟨a,b⟩ ha ⟨c,d⟩ hc eq
    simp only [Finset.mem_coe,Finset.mem_product] at ha hc
    have hab := gcd_factor (Nat.mem_divisors.mp ha.1).1 (Nat.mem_divisors.mp ha.2).1 h
    have hcd := gcd_factor (Nat.mem_divisors.mp hc.1).1 (Nat.mem_divisors.mp hc.2).1 h
    change a*b = c*d at eq
    have h': a=c := by rw [←hab, eq, hcd]
    apply Prod.ext h'
    rw [←h'] at eq
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mem_divisors ha.1) eq
  · intro d hd
    have hd' := (Nat.mem_divisors.mp hd).1
    obtain ⟨a,b,ha,hb,hab⟩ := Nat.dvd_mul.mp hd'
    exact ⟨(a,b), Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨ha,Nat.ne_of_gt hA⟩,
      Nat.mem_divisors.mpr ⟨hb,Nat.ne_of_gt hB⟩⟩,hab⟩
  · intro _ _
    rfl

def S₀ (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, moebius (n/d) * (H d : ℤ)^2

lemma mobius_pair {p r m : ℕ} (hp : p.Prime) (hm : 0 < m) (hc : p.Coprime m) :
    S₀ (p^(r+1)*m) =
      ∑ e ∈ m.divisors, moebius (m/e) *
        ((H (p^(r+1)*e) : ℤ)^2 - (H (p^r*e) : ℤ)^2) := by
  unfold S₀
  rw [sum_coprime_divs (Nat.pow_pos hp.pos) hm (hc.pow_left (r+1))]
  rw [Nat.sum_divisors_prime_pow hp, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have he' := (Nat.mem_divisors.mp he).1
  have he0 := Nat.pos_of_mem_divisors he
  have hdiv : ∀ j ≤ r+1, (p^(r+1)*m)/(p^j * e) = p^(r+1-j)*(m/e) := by
    intro j hj
    apply Nat.div_eq_of_eq_mul_right (Nat.mul_pos (Nat.pow_pos hp.pos) he0)
    calc
      _ = (p^(j+(r+1-j)))*(e*(m/e)) := by
        rw [Nat.add_sub_of_le hj, mul_comm e, Nat.div_mul_cancel he']
      _ = _ := by rw [pow_add]; ring
  have heCop : p.Coprime (m/e) := hc.coprime_dvd_right (Nat.div_dvd_of_dvd he')
  have hb : ∀ j ≤ r+1,
    moebius ((p^(r+1)*m)/(p^j * e)) * (H (p^j*e) : ℤ)^2 =
      moebius (p^(r+1-j)) * moebius (m/e) * (H (p^j*e) : ℤ)^2 := by
    intro j hj
    rw [hdiv j hj, isMultiplicative_moebius.map_mul_of_coprime (heCop.pow_left _)]
  have hrew : (∑ j ∈ Finset.range (r+1+1),
    moebius ((p^(r+1)*m)/(p^j * e)) * (H (p^j*e) : ℤ)^2) =
    ∑ j ∈ Finset.range (r+1+1),
      moebius (p^(r+1-j)) * moebius (m/e) * (H (p^j*e) : ℤ)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hb j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  rw [hrew, Finset.sum_range_succ, Finset.sum_range_succ]
  have hzero : (∑ j ∈ Finset.range r,
      moebius (p^(r+1-j)) * moebius (m/e) * (H (p^j*e) : ℤ)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hlt := Finset.mem_range.mp hj
    rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega), zero_mul, zero_mul]
  rw [hzero, zero_add, show r+1-r = 1 by omega, Nat.sub_self, pow_zero, pow_one,
    moebius_apply_prime hp, moebius_apply_one]
  ring


end A028576Final

namespace A028576Closure
open A028576Gauss A028576Final
open scoped BigOperators
open ArithmeticFunction

lemma assemble_prime_parts (n k : ℕ) (a : ℤ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ((p : ℤ)^n.factorization p)^k ∣ a) : (n : ℤ)^k ∣ a := by
  rw [← Int.natCast_pow, ← Int.dvd_natAbs, Int.natCast_dvd_natCast]
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p j hp hd
  have hj := (hp.pow_dvd_iff_le_factorization (pow_ne_zero _ hn)).mp hd
  rw [Nat.factorization_pow] at hj
  change j ≤ k * n.factorization p at hj
  have hloc : (p : ℤ)^(k * n.factorization p) ∣ a := by
    rw [mul_comm k, pow_mul]
    exact h p hp
  have hh : (p : ℤ)^j ∣ a := (pow_dvd_pow (p : ℤ) hj).trans hloc
  rwa [← Int.natCast_pow, ← Int.dvd_natAbs, Int.natCast_dvd_natCast] at hh

lemma S₀_divisibility (n : ℕ) (hn : n ≠ 0) :
    (n : ℤ)^2 ∣ S₀ n ∧ (n : ℤ)^3 ∣ 3*S₀ n := by
  have h (p : ℕ) (hp : p.Prime) :
      ((p : ℤ)^n.factorization p)^2 ∣ S₀ n ∧
      ((p : ℤ)^n.factorization p)^3 ∣ 3*S₀ n := by
    let m := n / p^n.factorization p
    have hm' : p^n.factorization p*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hc : p.Coprime m := Nat.coprime_ordCompl hp hn
    have hm : 0 < m := by
      by_contra! hh
      have hm0 : m=0 := Nat.eq_zero_of_not_pos (by omega)
      rw [hm0, mul_zero] at hm'
      exact hn hm'.symm
    cases hq : n.factorization p with
    | zero => simp
    | succ r =>
      rw [hq] at hm'
      have hpair := mobius_pair (r := r) hp hm hc
      rw [hm'] at hpair
      constructor
      · rw [hpair]
        apply Finset.dvd_sum
        intro d hd
        exact dvd_mul_of_dvd_right (gauss (r := r) hp (Nat.pos_of_mem_divisors hd)).1 _
      · rw [hpair, Finset.mul_sum]
        apply Finset.dvd_sum
        intro d hd
        rw [←mul_assoc, mul_comm 3, mul_assoc]
        exact dvd_mul_of_dvd_right (gauss (r := r) hp (Nat.pos_of_mem_divisors hd)).2 _
  exact ⟨assemble_prime_parts n 2 (S₀ n) hn (fun p hp => (h p hp).1),
    assemble_prime_parts n 3 (3 * S₀ n) hn (fun p hp => (h p hp).2)⟩

lemma original_S (n : ℕ) : OMA.S_oeis_a028576.S n = 4 * S₀ n := by
  unfold OMA.S_oeis_a028576.S S₀
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [two_mul, choose_eq_two_mul_H (Nat.pos_of_mem_divisors hd)]
  push_cast
  ring

end A028576Closure

open A028576Gauss A028576Final A028576Closure

theorem OMA.solution : type_of% @OMA.S_oeis_a028576.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn0
  have hs : OMA.S_oeis_a028576.a n = S₀ n / (n : ℤ) := by
    unfold OMA.S_oeis_a028576.a
    rw [original_S, Int.mul_ediv_mul_of_pos _ _ (by decide : (0 : ℤ) < 4)]
  obtain ⟨h₂, h₃⟩ := S₀_divisibility n hn0
  have hndvd : (n : ℤ) ∣ S₀ n :=
    (dvd_pow_self (n : ℤ) (by decide : 2 ≠ 0)).trans h₂
  constructor
  · rw [hs, Int.dvd_ediv_iff_mul_dvd hndvd, ←pow_two]
    exact h₂
  · obtain ⟨q, hq⟩ := hndvd
    rw [hs, Int.ediv_eq_of_eq_mul_right hn' hq]
    obtain ⟨w, hw⟩ := h₃
    refine ⟨w, mul_left_cancel₀ hn' ?_⟩
    calc
      _ = 3 * ((n : ℤ) * q) := by ring
      _ = 3 * S₀ n := by rw [←hq]
      _ = (n : ℤ)^3*w := hw
      _ = _ := by ring

