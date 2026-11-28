import OMAStatements.S_mo_393993

/-!
# Missing zero digits in factorials

Dömötör Pálvölgyi asks whether 40! is the last factorial whose only decimal
zeros are trailing. The source is https://mathoverflow.net/questions/393993.

This file proves that the exceptional indices have upper Banach density
zero. The same holds if only an arbitrarily slowly growing number of final
digits of the stripped factorial are tested. The proof establishes uniform
distribution over the units modulo every power of five in moving intervals,
by inserting isolated base-five digits. Divisibility by large powers of two
then restricts a zero-free decimal suffix to at most 23^m residues modulo
25^m. For the distribution of stripped factorial digits in arbitrary bases,
see Bartosz Sobolewski, Acta Arithmetica 191 (2019), 173–189.

We also classify every power of five, and give positive lower density for
the starts of runs of any fixed length that share the leading digits 101.
A kernel certificate gives the exact exceptions through 50040. The remaining
inputs are a larger finite suffix computation, and a leading-digit estimate
on the sparse indices surviving a logarithmically growing suffix sieve.
-/

open OMA.S_mo_393993

namespace Fact393

theorem digit_in_quotient {b k m : ℕ} (hb : 1<b) (e : ℕ)
    (h : k ∈ Nat.digits b (m/b^e)) : k∈Nat.digits b m := by
  induction e generalizing m with
  | zero => simpa using h
  | succ e ih =>
    by_cases hm : m=0
    · simp [hm] at h
    rw [Nat.digits_eq_cons_digits_div hb hm]
    apply List.mem_cons_of_mem
    apply ih
    simpa only [Nat.div_div_eq_div_mul, Nat.pow_succ',mul_comm] using h

theorem kept_digit_of_prefix {m s e : ℕ} (he : m/10^e=s) (hs : ¬10∣s) {k : ℕ}
    (hd : k∈Nat.digits 10 s) : k∈Nat.digits 10 (m/10^(padicValNat 10 m)) := by
  let t := padicValNat 10 m
  have le : t≤e := by
    by_contra! h
    have hpow : 10^(e+1) ∣ m := (pow_dvd_pow 10 h).trans pow_padicValNat_dvd
    obtain ⟨j,hj⟩ := hpow
    have hp : 0 < 10^e := by positivity
    apply hs
    rw [←he,hj,pow_succ,mul_assoc,Nat.mul_div_cancel_left _ hp]
    exact dvd_mul_right _ _
  apply digit_in_quotient (by decide : 1<10) (e-t)
  rw [Nat.div_div_eq_div_mul, ←pow_add, Nat.add_sub_of_le le,he]
  exact hd

theorem prefix_101_not_zero_free {n e : ℕ} (h1 : 101*10^e ≤ n.factorial)
    (h2 : n.factorial < 102*10^e) : ¬ ZerosAtEnd n := by
  have hp : 0<10^e := by positivity
  have he : n.factorial/10^e=101 := by
    have := (Nat.le_div_iff_mul_le hp).mpr h1
    have := (Nat.div_lt_iff_lt_mul hp).mpr h2
    omega
  exact fun hz => hz (kept_digit_of_prefix he (by decide) (by decide : 0∈Nat.digits 10 101))

private theorem log_scaled_factorial (n e : ℕ) :
    Real.logb 10 ((n.factorial:ℝ)*10^e)=Real.logb 10 (n.factorial:ℝ)+e := by
  rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<10),mul_one]

theorem log_window_not_zero_free {n : ℕ} {z : ℤ}
    (lo : Real.logb 10 101 < Real.logb 10 (n.factorial:ℝ)-z)
    (hi : Real.logb 10 (n.factorial:ℝ)-z < Real.logb 10 102) : ¬ ZerosAtEnd n := by
  have b : (1:ℝ)<10 := by norm_num
  cases z with
  | ofNat e =>
    have A (k : ℝ) (hk:0<k) : Real.logb 10 (k*10^e)=Real.logb 10 k+e := by
      rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<10),mul_one]
    change Real.logb 10 101 < Real.logb 10 (n.factorial:ℝ)-(e:ℝ) at lo
    change Real.logb 10 (n.factorial:ℝ)-(e:ℝ) < Real.logb 10 102 at hi
    have lo' := (Real.logb_lt_logb_iff b (by positivity : 0 < (101:ℝ)*10^e) (by positivity : 0<(n.factorial:ℝ))).mp
      (by rw [A 101 (by norm_num)]; linarith)
    have hi' := (Real.logb_lt_logb_iff b (by positivity : 0<(n.factorial:ℝ)) (by positivity : 0 < (102:ℝ)*10^e)).mp
      (by rw [A 102 (by norm_num)]; linarith)
    apply prefix_101_not_zero_free (e:=e)
    · exact_mod_cast lo'.le
    · exact_mod_cast hi'
  | negSucc e =>
    have W := log_scaled_factorial n (e+1)
    push_cast at W lo hi
    have hL : (101:ℝ)<(n.factorial:ℝ)*10^(e+1) :=
      (Real.logb_lt_logb_iff b (by norm_num) (by positivity)).mp (by rw [W]; linarith)
    have hU : (n.factorial:ℝ)*10^(e+1)<(102:ℝ) :=
      (Real.logb_lt_logb_iff b (by positivity) (by norm_num)).mp (by rw [W]; linarith)
    have l : 101<n.factorial*10^(e+1) := by exact_mod_cast hL
    have u : n.factorial*10^(e+1)<102 := by exact_mod_cast hU
    omega

theorem normalized_log_window {n : ℕ} {z : ℤ}
    (lo : Real.logb 10 ((101:ℝ)/100) < Real.logb 10 (n.factorial:ℝ)-z)
    (hi : Real.logb 10 (n.factorial:ℝ)-z < Real.logb 10 ((102:ℝ)/100)) : ¬ZerosAtEnd n := by
  have hh : Real.logb 10 100=2 := by
    rw [show (100:ℝ)=10^2 by norm_num,Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1:ℝ)<10)]
    norm_num
  rw [Real.logb_div (by norm_num) (by norm_num),hh] at lo hi
  apply log_window_not_zero_free (z:=z-2) <;> push_cast <;> linarith

end Fact393

namespace Fact393
open OMA.S_mo_393993

theorem sum_decimal_logs (n : ℕ) :
    ∑ i ∈ Finset.range n,Real.logb 10 ((i:ℝ)+1)=Real.logb 10 (n.factorial:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Nat.factorial_succ,Nat.cast_mul,Real.logb_mul (by positivity) (by positivity)]
    push_cast
    ring

theorem log_prefix_excludes {w e n : ℕ} (hw : 0<w) (hu : ¬10∣w) (hd : 0∈Nat.digits 10 w)
    (lo : Real.logb 10 (w:ℝ)+e ≤ ∑ i ∈ Finset.range n,Real.logb 10 ((i:ℝ)+1))
    (hi : (∑ i ∈ Finset.range n,Real.logb 10 ((i:ℝ)+1)) < Real.logb 10 ((w:ℝ)+1)+e) :
    ¬ZerosAtEnd n := by
  rw [sum_decimal_logs] at lo hi
  have b : (1:ℝ)<10 := by norm_num
  have A (k : ℕ) (hk:0<k) : Real.logb 10 ((k:ℝ)*10^e)=Real.logb 10 (k:ℝ)+e := by
    rw [Real.logb_mul (by positivity) (by positivity),Real.logb_pow,Real.logb_self_eq_one b,mul_one]
  have l : w*10^e≤n.factorial := by
    by_contra! h
    have gt := Real.logb_lt_logb b (by positivity : 0<(n.factorial:ℝ)) (by exact_mod_cast h : (n.factorial:ℝ)<(w:ℝ)*10^e)
    rw [A w hw] at gt
    linarith
  have h : n.factorial<(w+1)*10^e := by
    exact_mod_cast (Real.logb_lt_logb_iff b (by positivity : 0<(n.factorial:ℝ))
      (by positivity : 0<((w+1:ℕ):ℝ)*10^e)).mp (by rw [A (w+1) (by omega)]; exact_mod_cast hi)
  have hp : 0<10^e := by positivity
  have hl := (Nat.le_div_iff_mul_le hp).mpr l
  have hh := (Nat.div_lt_iff_lt_mul hp).mpr h
  exact fun he => he (kept_digit_of_prefix (by omega : n.factorial/10^e=w) hu hd)

end Fact393

namespace Fact393
open Nat

theorem stripped_divisible {n k : ℕ} (hn : 4*(k+1)≤n) :
    2^k ∣ n.factorial / 10^(padicValNat 10 n.factorial) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let t := padicValNat 10 n.factorial
  have h10 : 10^t∣n.factorial := pow_padicValNat_dvd
  have h5 : 5^t∣n.factorial := (pow_dvd_pow_of_dvd (by decide : 5∣10) t).trans h10
  have ht := (pow_dvd_iff_le_padicValNat (by decide : 5≠1) (Nat.factorial_ne_zero _)).mp h5
  have h5u := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 5 (by omega : n≠0)
  norm_num only [Nat.reduceSub] at h5u
  have hn2 : padicValNat 2 n.factorial = padicValNat 2 ((n/2).factorial) + n/2 := by
    nth_rw 1 [←Nat.div_add_mod n 2]
    rw [padicValNat_factorial_mul_add (p:=2) _ (Nat.mod_lt _ (by decide)),padicValNat_factorial_mul]
  have h2 : 2^(t+k)∣n.factorial :=
    (pow_dvd_iff_le_padicValNat (by decide : 2≠1) (Nat.factorial_ne_zero _)).mpr (by omega)
  have pos : 0<2^t := by positivity
  have hsplit := Nat.div_mul_cancel h10
  let s := n.factorial / 10^t
  have H : 2^t * 2^k∣2^t*(5^t*s) := by
    rw [←pow_add,←mul_assoc,←mul_pow,show 2*5=10 by decide,Nat.mul_comm (10^t)]
    exact hsplit.symm ▸ h2
  have hh := Nat.dvd_of_mul_dvd_mul_left pos H
  exact (((show Nat.Coprime 2 5 by decide).pow_left k).pow_right t).dvd_of_dvd_mul_left hh

theorem stripped_size {n m : ℕ} (hn : 4*(7*m+1)≤n) :
    let X := n.factorial / 10^(padicValNat 10 n.factorial)
    4^m ∣ X ∧ 100^m ≤ X := by
  intro X
  have hp := stripped_divisible hn
  have hd : 10^(padicValNat 10 n.factorial)∣n.factorial := pow_padicValNat_dvd
  have hx : 0<X := Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hd) (by positivity)
  refine ⟨?_,?_⟩
  · rw [show (4:ℕ)=2^2 by decide]
    rw [←pow_mul]
    exact (pow_dvd_pow 2 (by omega : 2*m≤7*m)).trans hp
  · calc
      100^m ≤ 128^m := Nat.pow_le_pow_left (by decide) m
      _ = 2^(7*m) := by rw [pow_mul]; norm_num
      _ ≤ X := Nat.le_of_dvd hx hp

end Fact393

namespace Fact393

theorem discrete_window {x y δ : ℝ} {H W : ℕ} (F : ℕ → ℝ)
    (hδ : 0 < δ) (hH : 1 < (H : ℝ) * δ)
    (hW : (W + 1 : ℝ) * (2 * δ) < y - x)
    (step : ∀ j < H + W, δ ≤ F (j+1) - F j ∧ F (j+1) - F j ≤ 2*δ) :
    ∃ t ≤ H, ∃ z : ℤ, ∀ j ≤ W, x < F (t+j) - z ∧ F (t+j) - z < y := by
  classical
  have adv (i j : ℕ) (bd : i+j ≤ H+W) :
      (j : ℝ)*δ ≤ F (i+j)-F i ∧ F (i+j)-F i ≤ (j : ℝ)*(2*δ) := by
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨l,u⟩ := ih (by omega)
      obtain ⟨l',u'⟩ := step (i+j) (by omega)
      rw [Nat.cast_succ, Nat.add_succ, Nat.succ_eq_add_one]
      constructor <;> linarith
  let z : ℤ := ⌊F 0 - x⌋ + 1
  have z1 : F 0 < x + (z:ℝ) := by
    have h := Int.lt_floor_add_one (F 0 - x)
    dsimp [z]; push_cast; linarith
  have z2 : x + (z:ℝ) ≤ F 0 + 1 := by
    have h := Int.floor_le (F 0 - x)
    dsimp [z]; push_cast; linarith
  have endpt : x + (z:ℝ) < F H := by
    have h := (adv 0 H (by omega)).1
    simp only [zero_add] at h
    linarith
  have ex : ∃ i, x + (z:ℝ) < F i := ⟨H,endpt⟩
  let t := Nat.find ex
  have ht : t ≤ H := Nat.find_min' ex endpt
  have start : x + (z:ℝ) < F t := Nat.find_spec ex
  have ht0 : 0 < t := by
    by_contra! h
    have : t = 0 := by omega
    rw [this] at start
    linarith
  have prev : F (t-1) ≤ x + (z:ℝ) :=
    le_of_not_gt (Nat.find_min ex (show t-1 < t by omega))
  have next := (step (t-1) (by omega)).2
  rw [Nat.sub_add_cancel (by omega : 1≤t)] at next
  refine ⟨t,ht,z,?_⟩
  intro j hj
  obtain ⟨a,b⟩ := adv t j (by omega)
  have jd : 0 ≤ (j:ℝ)*δ := by positivity
  have mul := mul_le_mul_of_nonneg_right (show (j:ℝ) ≤ W by exact_mod_cast hj)
    (by positivity : 0≤2*δ)
  constructor <;> linarith

theorem factorial_log_slab {x y δ : ℝ} {n k H W : ℕ} (hδ : 0 < δ)
    (hH : 1 < (H:ℝ)*δ) (hW : (W+1:ℝ)*(2*δ)<y-x)
    (lo : (10:ℝ)^k * (10:ℝ)^δ ≤ (n:ℝ)+1)
    (hi : (n:ℝ)+H+W ≤ (10:ℝ)^k * (10:ℝ)^(2*δ)) :
    ∃ t ≤ H, ∀ j ≤ W, ∃ z : ℤ, x < Real.logb 10 ((n+t+j).factorial : ℝ) - z ∧
                          Real.logb 10 ((n+t+j).factorial : ℝ) - z < y := by
  let F (j : ℕ) := Real.logb 10 ((n+j).factorial : ℝ) - (k:ℝ)*j
  have scaled (d:ℝ) : Real.logb 10 ((10:ℝ)^k*(10:ℝ)^d) = (k:ℝ)+d := by
    rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
      Real.logb_self_eq_one (by norm_num), Real.logb_rpow (by norm_num) (by norm_num), mul_one]
  have step (j:ℕ) (hj:j<H+W) : δ ≤ F (j+1)-F j ∧ F (j+1)-F j ≤ 2*δ := by
    have h1 : (10:ℝ)^k*(10:ℝ)^δ ≤ (n:ℝ)+j+1 := by linarith
    have hj' : (j:ℝ)+1≤(H:ℝ)+W := by exact_mod_cast hj
    have h2 : (n:ℝ)+j+1 ≤ (10:ℝ)^k*(10:ℝ)^(2*δ) := by linarith
    have l := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<10) (by positivity) h1
    have u := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<10) (by positivity) h2
    rw [scaled] at l u
    have diff : F (j+1)-F j = Real.logb 10 ((n:ℝ)+j+1)-k := by
      dsimp [F]
      rw [← Nat.add_assoc, Nat.factorial_succ, Nat.cast_mul,
        Real.logb_mul (by positivity) (by positivity)]
      push_cast
      ring
    rw [diff]; constructor <;> linarith
  obtain ⟨t,ht,z,hz⟩ := discrete_window F hδ hH hW step
  refine ⟨t,ht,?_⟩
  intro j hj
  refine ⟨z + (k:ℤ)*(t+j),?_⟩
  obtain ⟨l,u⟩ := hz j hj
  dsimp [F] at l u
  rw [← Nat.add_assoc] at l u
  push_cast at *
  constructor <;> linarith

theorem factorial_log_runs (x y : ℝ) (hxy : x < y) (W K : ℕ) :
    ∃ n ≥ K, ∀ j ≤ W, ∃ z : ℤ, x < Real.logb 10 ((n+j).factorial : ℝ) - z ∧
                              Real.logb 10 ((n+j).factorial : ℝ) - z < y := by
  let δ : ℝ := (y-x) / (4*((W:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hW : ((W:ℝ)+1)*(2*δ)<y-x := by
    dsimp [δ]
    field_simp
    nlinarith [mul_pos (sub_pos.mpr hxy) (show 0<(W:ℝ)+1 by positivity)]
  obtain ⟨H,hH⟩ := exists_nat_gt (1/δ)
  have hH' := (div_lt_iff₀ hδ).mp hH
  let A : ℝ := (10:ℝ)^δ
  let B : ℝ := (10:ℝ)^(2*δ)
  have hA : 1<A := Real.one_lt_rpow (by norm_num) hδ
  have hAB : A<B := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt
    (max (K:ℝ) (((H:ℝ)+W+1)/(B-A))) (show (1:ℝ)<10 by norm_num)
  have kBig := lt_of_le_of_lt (le_max_right _ _) hk
  have margin := (div_lt_iff₀ (sub_pos.mpr hAB)).mp kBig
  have kK := lt_of_le_of_lt (le_max_left _ _) hk
  let n := ⌈(10:ℝ)^k*A⌉₊
  have nlo : (10:ℝ)^k*A ≤ (n:ℝ) := Nat.le_ceil _
  have nhi : (n:ℝ) < (10:ℝ)^k*A+1 := Nat.ceil_lt_add_one (by positivity)
  have hn : K≤n := by
    have hpow : (0:ℝ)<10^k := by positivity
    exact_mod_cast (show (K:ℝ) ≤ n by nlinarith [mul_pos hpow (sub_pos.mpr hA)])
  obtain ⟨t,ht,run⟩ := factorial_log_slab (n:=n) (k:=k) hδ hH' hW
    (show (10:ℝ)^k*A≤(n:ℝ)+1 by linarith)
    (show (n:ℝ)+H+W≤(10:ℝ)^k*B by nlinarith)
  exact ⟨n+t,by omega,run⟩

end Fact393

namespace Fact393

theorem factorial_log_run_count (x y : ℝ) (hxy : x < y) (W : ℕ) :
    ∃ C : ℕ, ∀ M : ℕ, ∃ S : Finset ℕ, S.card = M ∧
      ∀ n ∈ S, n < C*(M+1) ∧ ∀ j ≤ W, ∃ z : ℤ,
        x < Real.logb 10 ((n+j).factorial : ℝ)-z ∧
        Real.logb 10 ((n+j).factorial : ℝ)-z < y := by
  classical
  let δ : ℝ := (y-x)/(4*((W:ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hW : ((W:ℝ)+1)*(2*δ)<y-x := by
    dsimp [δ]
    field_simp
    nlinarith [mul_pos (sub_pos.mpr hxy) (show 0<(W:ℝ)+1 by positivity)]
  obtain ⟨H,hH⟩ := exists_nat_gt (1/δ)
  have hH' := (div_lt_iff₀ hδ).mp hH
  let A : ℝ := (10:ℝ)^δ
  let B : ℝ := (10:ℝ)^(2*δ)
  have hA : 1<A := Real.one_lt_rpow (by norm_num) hδ
  have hAB : A<B := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨K,hK⟩ := exists_nat_gt (max (1:ℝ) (((H:ℝ)+W+2)/(B-A)))
  have hK1 : (1:ℝ)<K := (le_max_left _ _).trans_lt hK
  have hKW := (div_lt_iff₀ (sub_pos.mpr hAB)).mp ((le_max_right _ _).trans_lt hK)
  obtain ⟨C,hC⟩ := exists_nat_gt ((10:ℝ)*K*B)
  refine ⟨C,?_⟩
  intro M
  have hM : (0:ℝ)<M+1 := by positivity
  have oneKM : 1 ≤ (K:ℝ)*(M+1) := one_le_mul_of_one_le_of_one_le hK1.le (by linarith)
  obtain ⟨k,klo,khi⟩ := exists_nat_pow_near oneKM (by norm_num : (1:ℝ)<10)
  let u := (10:ℝ)^(k+1)
  have ub : u ≤ 10*K*(M+1) := by
    dsimp [u]; rw [pow_succ]; linarith
  have width : ((H:ℝ)+W+2)*(M+1) < u*(B-A) := by
    calc
      _ < ((K:ℝ)*(B-A))*(M+1) := mul_lt_mul_of_pos_right hKW hM
      _ = ((K:ℝ)*(M+1))*(B-A) := by ring
      _ < _ := mul_lt_mul_of_pos_right khi (sub_pos.mpr hAB)
  let n := ⌈u*A⌉₊
  have nlo : u*A ≤ (n:ℝ) := Nat.le_ceil _
  have nhi : (n:ℝ) < u*A+1 := Nat.ceil_lt_add_one (by positivity)
  let base (i : Fin M) := n+i.val*(H+1)
  have hi (i : Fin M) : ((base i):ℝ)+H+W ≤ u*B := by
    have hiM : (i.val:ℝ)+1 ≤ M := by exact_mod_cast i.isLt
    have scale := mul_le_mul_of_nonneg_right hiM (by positivity : (0:ℝ)≤H+1)
    have spare : (0:ℝ) ≤ (W:ℝ)*M := by positivity
    dsimp [base]
    push_cast
    nlinarith only [width, nhi, scale, spare, Nat.cast_nonneg (α:=ℝ) M,
      Nat.cast_nonneg (α:=ℝ) H]
  have run (i : Fin M) := factorial_log_slab (n:=base i) (k:=k+1) hδ hH' hW
    (show u*A≤((base i):ℝ)+1 by
      have h : n ≤ base i := Nat.le_add_right _ _
      exact nlo.trans (by exact_mod_cast Nat.le_trans h (Nat.le_succ _)))
    (hi i)
  choose t ht good using run
  let f (i : Fin M) := base i + t i
  have mono : StrictMono f := by
    intro i j hij
    have ij : i.val+1 ≤ j.val := hij
    have mul := Nat.mul_le_mul_right (H+1) ij
    rw [Nat.add_mul, one_mul] at mul
    have h := ht i
    change n + i.val*(H+1) + t i < n + j.val*(H+1) + t j
    omega
  refine ⟨Finset.univ.image f,?_,?_⟩
  · rw [Finset.card_image_of_injective _ mono.injective]; simp
  intro m hm
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hm
  refine ⟨?_,good i⟩
  have h_upper := hi i
  have ht' : ((t i):ℝ) ≤ H := by exact_mod_cast ht i
  have uB := mul_le_mul_of_nonneg_right ub (le_of_lt (show 0<B by linarith))
  have cb := mul_lt_mul_of_pos_right hC hM
  dsimp [f]
  exact_mod_cast (show (base i:ℝ) + t i < (C:ℝ)*(M+1) by nlinarith)

end Fact393

namespace Fact393

theorem zero_runs (W K : ℕ) :
    ∃ n ≥ K, ∀ j ≤ W, ¬ OMA.S_mo_393993.ZerosAtEnd (n+j) := by
  obtain ⟨n,hn,h⟩ := factorial_log_runs _ _ (Real.logb_lt_logb
    (by norm_num : (1:ℝ)<10) (by norm_num : (0:ℝ)<101) (by norm_num : (101:ℝ)<102)) W K
  refine ⟨n,hn,fun j hj => ?_⟩
  obtain ⟨z,lo,hi⟩ := h j hj
  exact log_window_not_zero_free lo hi

theorem zero_run_count (W : ℕ) :
    ∃ C : ℕ, ∀ M : ℕ, ∃ S : Finset ℕ, S.card=M ∧ ∀ n ∈ S,
      n<C*(M+1) ∧ ∀ j ≤ W, ¬OMA.S_mo_393993.ZerosAtEnd (n+j) := by
  obtain ⟨C,hC⟩ := factorial_log_run_count _ _ (Real.logb_lt_logb
    (by norm_num : (1:ℝ)<10) (by norm_num : (0:ℝ)<101) (by norm_num : (101:ℝ)<102)) W
  refine ⟨C,fun M => ?_⟩
  obtain ⟨S,hs,good⟩ := hC M
  refine ⟨S,hs,fun n hn => ⟨(good n hn).1,fun j hj => ?_⟩⟩
  obtain ⟨z,lo,hi⟩ := (good n hn).2 j hj
  exact log_window_not_zero_free lo hi

end Fact393

namespace Fact393

theorem no_zero_digits_div_ten {X : ℕ} (h : 0 ∉ Nat.digits 10 X) :
    0 ∉ Nat.digits 10 (X / 10) := by
  by_cases hz : X=0
  · simp [hz]
  rw [Nat.digits_eq_cons_digits_div (by decide) hz] at h
  exact fun h' => h (List.mem_cons_of_mem _ h')

theorem no_zero_digits_div_hundred_pow {X : ℕ} (h : 0 ∉ Nat.digits 10 X) (m : ℕ) :
    0 ∉ Nat.digits 10 (X / 100^m) := by
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have h' := no_zero_digits_div_ten (no_zero_digits_div_ten ih)
    simpa only [Nat.div_div_eq_div_mul, Nat.mul_assoc, pow_succ] using h'

theorem suffix_residue_cover (m : ℕ) :
    ∃ A : Finset ℕ, A.card ≤ 23^m ∧ ∀ X : ℕ, 4^m ∣ X → 100^m ≤ X →
      0 ∉ Nat.digits 10 X → X % 25^m ∈ A := by
  let digits (c : ℕ) := (Finset.range 100).filter
    (fun d => d%10 ≠ 0 ∧ d/10 ≠ 0 ∧ (c+d)%4=0)
  have cards : ∀ c : Fin 4, (digits c.val).card ≤ 23 := by decide
  have cover (k : ℕ) : ∃ S : Finset ℕ, S.card ≤ 23^k ∧
      ∀ X : ℕ, 4^k ∣ X → 100^k ≤ X → 0 ∉ Nat.digits 10 X → X%100^k ∈ S := by
    induction k with
    | zero => exact ⟨{0},by simp,by intro X h1 h2 h3; simp [Nat.mod_one]⟩
    | succ k ih =>
      obtain ⟨S,hS,hcov⟩ := ih
      let layer (r : ℕ) := (digits ((r/4^k)%4)).image (fun d => r+100^k*d)
      refine ⟨S.biUnion layer,?_,?_⟩
      · calc
          _ ≤ ∑ r ∈ S, (layer r).card := Finset.card_biUnion_le
          _ ≤ ∑ _ ∈ S, 23 := Finset.sum_le_sum (fun r _ =>
            Finset.card_image_le.trans (cards ⟨(r/4^k)%4,Nat.mod_lt _ (by decide)⟩))
          _ = S.card * 23 := by simp
          _ ≤ _ := by rw [pow_succ]; gcongr
      intro X hfour hx hz
      let r := X%100^k
      let Y := X/100^k
      let d := Y%100
      have h4k : 4^k ∣ X := (Nat.pow_dvd_pow 4 (Nat.le_succ k)).trans hfour
      have hxk : 100^k ≤ X := (Nat.pow_le_pow_right (by decide) (Nat.le_succ k)).trans hx
      have rmem : r ∈ S := hcov X h4k hxk hz
      have rdiv : 4^k ∣ r := (Nat.dvd_mod_iff (pow_dvd_pow_of_dvd (by decide : 4∣100) k)).2 h4k
      have newres : X%100^(k+1) = r+100^k*d := by
        rw [pow_succ, Nat.mod_mul]
      have newdiv : 4^(k+1) ∣ r+100^k*d :=
        newres ▸ (Nat.dvd_mod_iff (pow_dvd_pow_of_dvd (by decide : 4∣100) (k+1))).2 hfour
      have split : r+100^k*d = 4^k*(r/4^k + 25^k*d) := by
        rw [Nat.mul_add, Nat.mul_div_cancel' rdiv, ← Nat.mul_assoc, ← mul_pow]
        norm_num
      rw [split, pow_succ, Nat.mul_dvd_mul_iff_left (by positivity)] at newdiv
      have h25 : 25^k*d ≡ d [MOD 4] := by
        simpa using ((show 25 ≡ 1 [MOD 4] by decide).pow k).mul_right d
      have congr := h25.add_left (r/4^k)
      have rem : ((r/4^k)%4 + d)%4=0 := by
        change (r / 4 ^ k + 25 ^ k * d) % 4 = (r / 4 ^ k + d) % 4 at congr
        rw [Nat.mod_add_mod, ← congr]
        exact Nat.mod_eq_zero_of_dvd newdiv
      have hY : 100 ≤ Y := (Nat.le_div_iff_mul_le (by positivity)).mpr (by
        simpa [pow_succ, Nat.mul_comm] using hx)
      have hYz := no_zero_digits_div_hundred_pow hz k
      change 0 ∉ Nat.digits 10 Y at hYz
      have hT := no_zero_digits_div_ten hYz
      rw [Nat.digits_eq_cons_digits_div (by decide) (by omega : Y ≠ 0)] at hYz
      rw [Nat.digits_eq_cons_digits_div (by decide) (by omega : Y/10 ≠ 0)] at hT
      have unit : Y%10 ≠ 0 := fun he => hYz (List.mem_cons.mpr (Or.inl he.symm))
      have tens : Y/10%10 ≠ 0 := fun he => hT (List.mem_cons.mpr (Or.inl he.symm))
      have hunits : d%10 ≠ 0 := by
        dsimp [d]; rwa [Nat.mod_mod_of_dvd Y (by decide : 10∣100)]
      have htens : d/10 ≠ 0 := by
        change Y%(10*10)/10 ≠ 0
        rwa [Nat.mod_mul_right_div_self]
      rw [newres]
      apply Finset.mem_biUnion.mpr ⟨r,rmem,?_⟩
      exact Finset.mem_image.mpr ⟨d,Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)),hunits,htens,rem⟩,rfl⟩
  obtain ⟨S,hS,hcov⟩ := cover m
  refine ⟨S.image (fun r => r%25^m),Finset.card_image_le.trans hS,?_⟩
  intro X hfour hx hz
  exact Finset.mem_image.mpr ⟨_,hcov X hfour hx hz,
    Nat.mod_mod_of_dvd _ (pow_dvd_pow_of_dvd (by decide : 25∣100) m)⟩

end Fact393

namespace Fact393

theorem suffix_residue_cover_take (m : ℕ) :
    ∃ A : Finset ℕ, A.card≤23^m ∧ ∀ X q : ℕ, 2*m≤q → 4^m∣X → 100^m≤X →
      0∉(Nat.digits 10 X).take q → X%25^m∈A := by
  obtain ⟨A,hA,cover⟩ := suffix_residue_cover m
  refine ⟨A,hA,?_⟩
  intro X q hq h4 hx hz
  let L := (Nat.digits 10 X).take (2*m)
  have h10 : (10:ℕ)^(2*m)=100^m := by rw [pow_mul]; rfl
  have hlen : 2*m≤(Nat.digits 10 X).length := by
    have hh := (Nat.lt_digits_length_iff (by decide : 1<10) X).mpr (h10 ▸ hx)
    omega
  have hL : L.length=2*m := by simp [L,hlen]
  have hom : Nat.ofDigits 10 (L++[1]) = X%100^m+100^m := by
    rw [Nat.ofDigits_append, Nat.ofDigits_singleton,hL,h10,mul_one]
    rw [←h10,Nat.self_mod_pow_eq_ofDigits_take _ _ (by decide : 2≤10)]
  have hd : Nat.digits 10 (Nat.ofDigits 10 (L++[1])) = L++[1] := by
    apply Nat.digits_ofDigits _ (by decide)
    · intro d hd
      rcases List.mem_append.mp hd with hd|hd
      · exact Nat.digits_lt_base (by decide : 1<10) ((List.take_prefix _ _).subset hd)
      · simp at hd; omega
    · simp
  have hnz : 0∉Nat.digits 10 (X%100^m+100^m) := by
    rw [←hom,hd]
    intro e
    rcases List.mem_append.mp e with h|h
    · exact hz ((List.take_prefix_take_left hq).subset h)
    · simp at h
  have h4p : 4^m∣100^m := pow_dvd_pow_of_dvd (by decide : 4∣100) _
  have hy4 := Nat.dvd_add ((Nat.dvd_mod_iff h4p).mpr h4) h4p
  have hy := cover (X%100^m+100^m) hy4 (by omega) hnz
  have h25 : 25^m∣100^m := pow_dvd_pow_of_dvd (by decide : 25∣100) _
  simpa only [Nat.add_mod, Nat.mod_eq_zero_of_dvd h25, Nat.add_zero,
    Nat.mod_mod, Nat.mod_mod_of_dvd _ h25] using hy

end Fact393

/-!
The distribution of the last nonzero factorial digits in arbitrary bases is studied in
B. Sobolewski, “On the last nonzero digits of n! in a given base”, Acta Arithmetica 191
(2019), 173–189. The proof here isolates a two-digit block in base five, calculates its
multiplier, and lifts its order at all powers of five.
-/

namespace Fact393

private lemma five_prime_instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

lemma corrected_one (k : ℕ) : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k 1 = 1 := by simp

lemma corrected_mul (k : ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (a*b) = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k a * (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k b := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  have h₁ : 5 ^ padicValNat 5 a ∣ a := pow_padicValNat_dvd
  have h₂ : 5 ^ padicValNat 5 b ∣ b := pow_padicValNat_dvd
  have h₃ : (a*b)/(5^padicValNat 5 a * 5^padicValNat 5 b) = (a/5^padicValNat 5 a)*(b/5^padicValNat 5 b) := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    calc
      a*b = (a / 5^padicValNat 5 a * 5^padicValNat 5 a) * (b / 5^padicValNat 5 b * 5^padicValNat 5 b) := by rw [Nat.div_mul_cancel h₁, Nat.div_mul_cancel h₂]
      _ = _ := by ring
  simp only [padicValNat.mul ha hb, pow_add, h₃, Nat.cast_mul]
  ring

lemma corrected_shift {k e A i : ℕ} (hk : 0 < k) (hi : 0 < i) (him : i ≤ 5^e)
    (hA : 5^(k+e) ∣ A) : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (A+i) = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k i := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  let v := padicValNat 5 i
  have hv : v ≤ e := by
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 5)).mp ((Nat.le_of_dvd hi (pow_padicValNat_dvd (p := 5))).trans him)
  obtain ⟨T, hT⟩ := hA
  let q := i / 5^v
  let z := 5^(e-v) * T
  have hq : q * 5^v = i := Nat.div_mul_cancel pow_padicValNat_dvd
  have hq' : q ≠ 0 := by rintro h; simp [h] at hq; omega
  have hqr : ¬5 ∣ q := by
    intro h
    apply pow_succ_padicValNat_not_dvd (p := 5) hi.ne'
    change 5^(v+1) ∣ i
    rw [pow_succ, ← hq, mul_comm q]
    exact Nat.mul_dvd_mul_left _ h
  have hz : A+i = (5^k*z+q)*5^v := by
    calc
      A+i = (5^k*5^(e-v)*5^v)*T + q*5^v := by rw [hq, ← pow_add, ← pow_add, show k+(e-v)+v=k+e by omega, ← hT]
      _ = _ := by dsimp [z]; ring
  have hzq : ¬5 ∣ 5^k*z+q := by
    have h : 5 ∣ 5^k*z := dvd_mul_of_dvd_left (dvd_pow_self _ hk.ne') _
    simpa [Nat.dvd_add_right h] using hqr
  have hv' : padicValNat 5 (A+i) = v := by
    rw [hz, padicValNat.mul (by omega) (by positivity), padicValNat.eq_zero_of_not_dvd hzq, padicValNat.prime_pow, zero_add]
  simp only [hv']
  change (((A+i)/5^v : ℕ) : ZMod (5^k)) * _ = (q : ZMod (5^k)) * _
  rw [hz, Nat.mul_div_cancel _ (by positivity)]
  push_cast
  have : (5 : ZMod (5^k))^k = 0 := by exact_mod_cast ZMod.natCast_self (5^k)
  simp [this, v]

theorem corrected_factorial_separate {k e A x : ℕ} (hk : 0 < k) (hx : x ≤ 5^e)
    (hA : 5^(k+e) ∣ A) : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (A+x).factorial = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k A.factorial * (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k x.factorial := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [← Nat.add_assoc, Nat.factorial_succ, Nat.factorial_succ x, corrected_mul _ (by omega) (Nat.factorial_ne_zero _),
      corrected_mul _ (by omega) (Nat.factorial_ne_zero _), ih (by omega), Nat.add_assoc A x 1, corrected_shift hk (by omega) hx hA]
    ring

lemma factorial_two_five (n : ℕ) : padicValNat 5 n.factorial ≤ padicValNat 2 n.factorial := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  by_cases hn : n=0
  · simp [hn]
  have hu := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 5 hn
  have hl := padicValNat_factorial_mul_add (p := 2) (n / 2) (Nat.mod_lt n (by decide : 0 < 2))
  rw [Nat.div_add_mod, padicValNat_factorial_mul] at hl
  omega

lemma factorial_ten (n : ℕ) : padicValNat 10 n.factorial = padicValNat 5 n.factorial := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  let a := n.factorial
  have ha : a ≠ 0 := Nat.factorial_ne_zero _
  apply le_antisymm
  · apply (padicValNat_dvd_iff_le ha).mp
    exact (pow_dvd_pow_of_dvd (by decide : 5 ∣ 10) _).trans pow_padicValNat_dvd
  · apply (padicValNat_dvd_iff_le_of_ne_one (by decide : 10 ≠ 1) ha).mp
    have h2 := (padicValNat_dvd_iff_le (p := 2) ha).mpr (factorial_two_five n)
    have h5 : 5^(padicValNat 5 a) ∣ a := pow_padicValNat_dvd
    have hc := ((show Nat.Coprime 2 5 by decide).pow (padicValNat 5 a) (padicValNat 5 a)).mul_dvd_of_dvd_of_dvd h2 h5
    simpa only [← mul_pow, show 2*5=10 by decide] using hc

lemma two_unit (k : ℕ) : IsUnit (2 : ZMod (5^k)) := by
  exact (ZMod.isUnit_iff_coprime 2 (5^k)).mpr ((show Nat.Coprime 2 5 by decide).pow_right _)

lemma inv_two_unit (k : ℕ) : IsUnit (2:ZMod (5^k))⁻¹ :=
  isUnit_iff_exists.mpr ⟨2, ZMod.inv_mul_of_unit _ (two_unit k), ZMod.mul_inv_of_unit _ (two_unit k)⟩

lemma corrected_factorial_eq (k n : ℕ) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k n.factorial = ((n.factorial / 10^(padicValNat 10 n.factorial) : ℕ) : ZMod (5^k)) := by
  rw [factorial_ten]
  let v := padicValNat 5 n.factorial
  have hd : 10^v ∣ n.factorial := by
    dsimp [v]; rw [← factorial_ten]; exact pow_padicValNat_dvd
  have he : n.factorial/5^v = (n.factorial/10^v)*2^v := by
    apply Nat.div_eq_of_eq_mul_left (by positivity)
    rw [mul_assoc, ← mul_pow, show 2*5=10 by decide, Nat.div_mul_cancel hd]
  change ((n.factorial/5^v : ℕ) : ZMod (5^k)) * _ = _
  rw [he, Nat.cast_mul, Nat.cast_pow, mul_assoc, ← mul_pow]
  norm_num only [Nat.cast_ofNat]; rw [ZMod.mul_inv_of_unit _ (two_unit k), one_pow, mul_one]

private lemma corrected_plain (k t : ℕ) (h : ¬5 ∣ t) : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k t = t := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  simp [padicValNat.eq_zero_of_not_dvd h]

private lemma corrected_five (k : ℕ) : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k 5 = (2:ZMod (5^k))⁻¹ := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  simp

lemma corrected_scale (k t : ℕ) : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (5*t).factorial =
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k t.factorial * (∏ i ∈ Finset.range t, (fun (k t : ℕ) => (5*(t:ZMod (5^k))+1)*(5*(t:ZMod (5^k))+2)*(5*(t:ZMod (5^k))+3)*(5*(t:ZMod (5^k))+4)) k i) * (2 : ZMod (5^k))⁻¹^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have id : 5*(t+1) = (5*t+4)+1 := by omega
    rw [id, Nat.factorial_succ, Nat.factorial_succ (5*t+3), Nat.factorial_succ (5*t+2), Nat.factorial_succ (5*t+1), Nat.factorial_succ (5*t)]
    repeat' rw [corrected_mul _ (by omega) (by positivity : _ ≠ 0)]
    rw [← id, corrected_mul _ (by decide) (by omega), corrected_five, corrected_plain _ _ (by omega : ¬ 5 ∣ 5*t+4),
      corrected_plain _ _ (by omega : ¬ 5 ∣ 5*t+3), corrected_plain _ _ (by omega : ¬ 5 ∣ 5*t+2), corrected_plain _ _ (by omega : ¬ 5 ∣ 5*t+1), ih, Nat.factorial_succ t,
      corrected_mul _ (by omega) (Nat.factorial_ne_zero _), Finset.prod_range_succ, pow_succ]
    dsimp only
    push_cast
    ring

private lemma periodic_prod {R : Type*} [CommMonoid R] (f : ℕ → R) (D : ℕ)
    (hf : ∀ c i, f (D*c+i) = f i) (c : ℕ) :
    (∏ i ∈ Finset.range (D*c), f i) = (∏ i ∈ Finset.range D, f i)^c := by
  induction c with
  | zero => simp
  | succ c ih => simp [Nat.mul_succ, Finset.prod_range_add, hf, ih, pow_succ]

private lemma window_unit (k t : ℕ) : IsUnit ((fun (k t : ℕ) => (5*(t:ZMod (5^k))+1)*(5*(t:ZMod (5^k))+2)*(5*(t:ZMod (5^k))+3)*(5*(t:ZMod (5^k))+4)) k t) := by
  have hz (i : ℕ) (h : ¬5 ∣ 5*t+i) : IsUnit ((5*t+i : ℕ) : ZMod (5^k)) :=
    (ZMod.isUnit_iff_coprime _ _).mpr (((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr h).symm.pow_right _)
  simpa  using ((((hz 1 (by omega)).mul (hz 2 (by omega))).mul (hz 3 (by omega))).mul (hz 4 (by omega)))

private lemma full_power {k : ℕ} {x : ZMod (5^k)} (hx : IsUnit x) {b : ℕ} (hb : (5^k).totient ∣ b) :
    x^b = 1 := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨z,hz⟩ := hb
  rw [hz, pow_mul, ← Units.val_pow_eq_pow_val, ← ZMod.card_units_eq_totient (5^k),
    pow_card_eq_one, Units.val_one, one_pow]

lemma stable_step {k j : ℕ} (hk : 0 < k) (hj : 2*k ≤ j) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^(j+1)).factorial = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^j).factorial := by
  have he (c : ℕ) (hc : k ≤ c) : (5^k).totient ∣ 8*5^c := by
    obtain ⟨w, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [Nat.totient_prime_pow_succ (by decide : Nat.Prime 5)]
    refine ⟨2*5^(c-w),?_⟩
    calc
      8*5^c = 8*(5^w*5^(c-w)) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
      _ = _ := by norm_num; ring
  have hz : 5^k*(8*5^(j-k)) = 8*5^j := by
    calc
      _ = 8*(5^k*5^(j-k)) := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  have hp (c i : ℕ) : (fun (k t : ℕ) => (5*(t:ZMod (5^k))+1)*(5*(t:ZMod (5^k))+2)*(5*(t:ZMod (5^k))+3)*(5*(t:ZMod (5^k))+4)) k (5^k*c+i) = (fun (k t : ℕ) => (5*(t:ZMod (5^k))+1)*(5*(t:ZMod (5^k))+2)*(5*(t:ZMod (5^k))+3)*(5*(t:ZMod (5^k))+4)) k i := by
    dsimp only
    push_cast
    have hh : (5:ZMod (5^k))^k = 0 := by exact_mod_cast ZMod.natCast_self (5^k)
    simp [hh]
  have hunit : IsUnit (∏ i ∈ Finset.range (5^k), (fun (k t : ℕ) => (5*(t:ZMod (5^k))+1)*(5*(t:ZMod (5^k))+2)*(5*(t:ZMod (5^k))+3)*(5*(t:ZMod (5^k))+4)) k i) :=
    IsUnit.prod_iff.mpr (fun i _ => window_unit k i)
  have hp' := periodic_prod ((fun (k t : ℕ) => (5*(t:ZMod (5^k))+1)*(5*(t:ZMod (5^k))+2)*(5*(t:ZMod (5^k))+3)*(5*(t:ZMod (5^k))+4)) k) (5^k) hp (8*5^(j-k))
  rw [hz, full_power hunit (he _ (by omega))] at hp'
  rw [show 8*5^(j+1)=5*(8*5^j) by ring, corrected_scale, hp', mul_one,
    full_power (inv_two_unit k) (he _ (by omega)), mul_one]

lemma stable_from {k j h : ℕ} (hk : 0 < k) (hh : 2*k ≤ h) (hj : h ≤ j) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^j).factorial = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^h).factorial := by
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j hj ih => rw [stable_step hk (by omega), ih]

lemma lift_order {t : ℕ} (ht : t%25=22) (k : ℕ) :
    orderOf (t : ZMod (5^(k+1))) = 4*5^k := by
  have hp : Nat.Prime 5 := by decide
  have ht4 : (t^4)%25 = 6 := by rw [Nat.pow_mod, ht]
  have hart : t^4 = 1 + 5*(t^4/5) := by omega
  have hnd : ¬(5:ℤ) ∣ ((t^4/5 : ℕ) : ℤ) := by
    exact_mod_cast (show ¬5 ∣ t^4/5 by omega)
  have hq := ZMod.orderOf_one_add_mul_prime hp (by decide) ((t^4/5 : ℕ) : ℤ) hnd k
  have hq' : orderOf ((t : ZMod (5^(k+1)))^4) = 5^k := by
    rw [← Nat.cast_pow]
    conv_lhs => rw [hart]
    simpa only [Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using hq
  have hcast : (t : ZMod 5) = 2 := by
    rw [← ZMod.natCast_mod t 5, show t % 5 = 2 by omega]; rfl
  have hOrder : orderOf (2:ZMod 5) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨by decide⟩
    apply orderOf_eq_prime_pow (p := 2) (n := 1) <;> decide
  let f := ZMod.castHom (dvd_pow_self 5 (by omega : k+1≠0)) (ZMod 5)
  have hd := orderOf_map_dvd f.toMonoidHom (t : ZMod (5^(k+1)))
  change orderOf (f (t : ZMod (5^(k+1)))) ∣ _ at hd
  rw [map_natCast, hcast, hOrder] at hd
  rw [orderOf_pow_of_dvd (by decide) hd] at hq'
  omega

lemma corrected_isUnit {k n : ℕ} (hn : n ≠ 0) : IsUnit ((fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k n) := by
  have : Fact (Nat.Prime 5) := five_prime_instance
  let v := padicValNat 5 n
  have hq : n / 5^v * 5^v = n := Nat.div_mul_cancel pow_padicValNat_dvd
  have hnd : ¬5 ∣ n/5^v := by
    intro hd
    apply pow_succ_padicValNat_not_dvd (p := 5) hn
    change 5^(v+1) ∣ n
    exact (show 5^(v+1) ∣ n/5^v *5^v by simpa [pow_succ, mul_comm] using (Nat.mul_dvd_mul_left (5^v) hd)).trans (dvd_of_eq hq)
  apply IsUnit.mul
  · exact (ZMod.isUnit_iff_coprime _ _).mpr (((show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr hnd).symm.pow_right _)
  · exact (inv_two_unit k).pow _

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
private lemma seed_mod : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) 2 (8*5^4).factorial = 22 := by decide +kernel

lemma generator_order {k j : ℕ} (hk : 0 < k) (hj : 4 ≤ j) :
    orderOf ((fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^j).factorial) = 4*5^(k-1) := by
  have eq25 := (stable_from (k := 2) (h := 4) (by decide) (by decide) hj).trans seed_mod
  rw [corrected_factorial_eq] at eq25 ⊢
  let t := (8*5^j).factorial / 10^padicValNat 10 (8*5^j).factorial
  have hval := congrArg ZMod.val eq25
  change (t : ZMod 25).val = (22 : ZMod 25).val at hval
  rw [ZMod.val_natCast] at hval
  have h22 : t%25=22 := hval
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact lift_order h22 l

private lemma word_succ (h i : ℕ) :
    (fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h (i+1) = 8*5^(h*(i+1))+(fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i := by
  simp [Finset.sum_range_succ]; ring

private lemma word_bound {h : ℕ} (hh : 2 ≤ h) (i : ℕ) : (fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i < 5^(h*i+2) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hu : h*i+2 ≤ h*(i+1) := by rw [Nat.mul_add]; omega
    have hb := ih.trans_le (Nat.pow_le_pow_right (by decide : 0 < 5) hu)
    rw [word_succ, pow_add]
    omega

private lemma word_div (h i : ℕ) : 5^h ∣ (fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [word_succ]
    exact dvd_add (dvd_mul_of_dvd_right (pow_dvd_pow _ (by rw [Nat.mul_add]; omega)) _) ih

private lemma word_value {k h : ℕ} (hk : 0 < k) (hh : 2*k+4 ≤ h) (i t : ℕ) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k ((fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i * 5^t).factorial = ((fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^h).factorial)^i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hi : h*i+2 ≤ h*(i+1) := by rw [Nat.mul_add]; omega
    have hn : (fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i * 5^t ≤ 5^(h*i+2+t) := by
      rw [pow_add (5:ℕ) (h*i+2) t]
      exact Nat.mul_le_mul_right _ (word_bound (by omega) i).le
    have hd : 5^(k+(h*i+2+t)) ∣ 8*5^(h*(i+1)+t) := by
      apply dvd_mul_of_dvd_right
      apply pow_dvd_pow
      rw [Nat.mul_add]; omega
    rw [word_succ, Nat.add_mul, mul_assoc, ← pow_add, corrected_factorial_separate hk hn hd, ih,
      stable_from hk (by omega : 2*k ≤ h) (by rw [Nat.mul_add]; omega), pow_succ']

private lemma combine_word {k h H i a t s : ℕ} (hk : 0<k) (hh : 2*k+4≤h)
    (hs : s < 5^t) (hH : k+h*i+2 ≤ H) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k ((a*5^H+(fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i)*5^t+s).factorial =
      (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (a*5^(H+t)).factorial * ((fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (8*5^h).factorial)^i * (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k s.factorial := by
  have left : 5^k ∣ a*5^H := dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _
  have right : 5^k ∣ (fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i := (pow_dvd_pow _ (by omega : k≤h)).trans (word_div h i)
  have hd : 5^(k+t) ∣ (a*5^H+(fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i)*5^t := by
    rw [pow_add]
    exact mul_dvd_mul (dvd_add left right) dvd_rfl
  have hc : 5^(k+(h*i+2+t)) ∣ a*5^(H+t) := dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _
  have hsm : (fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i * 5^t ≤ 5^(h*i+2+t) := by
    rw [pow_add (5:ℕ) (h*i+2) t]
    exact Nat.mul_le_mul_right _ (word_bound (by omega) i).le
  rw [corrected_factorial_separate hk hs.le hd, show (a*5^H+(fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i)*5^t=a*5^(H+t)+(fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i*5^t by rw [pow_add]; ring,
    corrected_factorial_separate hk hsm hc, word_value hk hh]

/-- A 5-adic digit block contains a fixed collection of equally many substitutes as there
are units. Replacing that block runs through distinct residues whatever the two surrounding
strings of digits are. -/
theorem decimal_factorial_gadget {k : ℕ} (hk : 0 < k) :
    ∃ B ≥ 2, ∃ w : Fin (4*5^(k-1)) → Fin B, Function.Injective w ∧
      ∀ (j a s : ℕ), s < B^j →
      Function.Injective (fun i : Fin (4*5^(k-1)) =>
        ((((a*B+(w i:ℕ))*B^j+s).factorial / 10^padicValNat 10 ((a*B+(w i:ℕ))*B^j+s).factorial : ℕ) : ZMod (5^k))) := by
  let h := 2*k+4
  let L := 4*5^(k-1)
  let H := k+h*L+2
  have hh : 2*k+4 ≤ h := le_rfl
  have hn (i : Fin L) : k+h*i.val+2 ≤ H := by
    have := Nat.mul_le_mul_left h i.isLt.le
    dsimp [H]; omega
  let w (i : Fin L) : Fin (5^H) :=
    ⟨(fun (h i : ℕ) => 8 * ∑ d ∈ Finset.range i, 5^(h*(d+1))) h i.val, (word_bound (by omega) _).trans_le (Nat.pow_le_pow_right (by decide) (by have := hn i; omega))⟩
  have hb : 2 ≤ 5^H := by
    have hz : 1 ≤ H := by dsimp [H]; omega
    exact (by decide : 2≤5^1).trans (Nat.pow_le_pow_right (by decide) hz)
  have sep (j a s : ℕ) (hs : s < (5^H)^j) : Function.Injective (fun i : Fin L =>
      (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k ((a*5^H+(w i:ℕ))*(5^H)^j+s).factorial) := by
    intro i z eq
    simp only [← pow_mul] at hs eq
    have si := combine_word (a := a) hk hh hs (hn i)
    have sz := combine_word (a := a) hk hh hs (hn z)
    have ee := si.symm.trans (eq.trans sz)
    have hu := corrected_isUnit (k := k) (Nat.factorial_ne_zero s)
    have hv := corrected_isUnit (k := k) (Nat.factorial_ne_zero (a*5^(H+H*j)))
    have same := hv.mul_left_cancel (hu.mul_right_cancel ee)
    apply Fin.ext
    apply pow_injOn_Iio_orderOf _ _ same
    · change i.val < _
      rw [generator_order hk (by dsimp [h]; omega)]
      exact i.isLt
    · change z.val < _
      rw [generator_order hk (by dsimp [h]; omega)]
      exact z.isLt
  refine ⟨5^H, hb, w, ?_, ?_⟩
  · intro i z eq
    apply sep 0 0 0 (by simp)
    exact congrArg (fun y : Fin (5^H) => (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k ((0*5^H+y.val)*(5^H)^0+0).factorial) eq
  · intro j a s hs
    simpa only [← corrected_factorial_eq] using sep j a s hs

theorem decimal_factorial_gadget_nat {k : ℕ} (hk : 0<k) :
    ∃ B ≥ 2, ∃ G : Finset ℕ, G ⊆ Finset.range B ∧ G.card=4*5^(k-1) ∧
    ∀ j a s : ℕ, s<B^j → Set.InjOn (fun i => (((a*B+i)*B^j+s).factorial /
      10^padicValNat 10 ((a*B+i)*B^j+s).factorial) % (5^k)) (G : Set ℕ) := by
  obtain ⟨B,hB,w,hw,uniq⟩ := decimal_factorial_gadget hk
  let f : Fin (4*5^(k-1)) ↪ ℕ := ⟨fun i => (w i).val, Fin.val_injective.comp hw⟩
  let G := Finset.univ.map f
  refine ⟨B,hB,G,?_,?_,?_⟩
  · intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp ht
    exact Finset.mem_range.mpr (w i).isLt
  · simp [G]
  · intro j a s hs x hx y hy eq
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨l,_,rfl⟩ := Finset.mem_map.mp hy
    apply congrArg f
    apply uniq j a s hs
    apply ZMod.val_injective
    simpa [f, ZMod.val_natCast] using eq

/-- Every admissible residue modulo a power of five occurs in every one of a fixed
system of equal-sized consecutive blocks, with a bound depending only on the modulus. -/
theorem stripped_syndetic {k : ℕ} (hk : 0 < k) :
    ∃ B ≥ 2, ∀ a : ℕ, ∀ r : (ZMod (5^k))ˣ, ∃ i < B,
      (((a*B+i).factorial / 10^padicValNat 10 (a*B+i).factorial : ℕ) : ZMod (5^k)) = r := by
  classical
  obtain ⟨B,hB,w,_,uniq⟩ := decimal_factorial_gadget hk
  refine ⟨B,hB,?_⟩
  intro a r
  let X (i : Fin (4*5^(k-1))) : ZMod (5^k) :=
    ((a*B+(w i : ℕ)).factorial / 10^padicValNat 10 (a*B+(w i : ℕ)).factorial : ℕ)
  have hu (i) : IsUnit (X i) := by
    dsimp [X]
    rw [← corrected_factorial_eq]
    exact corrected_isUnit (Nat.factorial_ne_zero _)
  let f (i) := (hu i).unit
  have hinj : Function.Injective f := by
    intro i l he
    apply uniq 0 a 0 (by simp)
    have := congrArg (fun x : (ZMod (5^k))ˣ => x.val) he
    simpa [f,X] using this
  have hc : Fintype.card (Fin (4*5^(k-1))) = Fintype.card (ZMod (5^k))ˣ := by
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simp [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_five, Nat.mul_comm]
  obtain ⟨i,hi⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj,hc⟩).2 r
  refine ⟨(w i).val,(w i).isLt,?_⟩
  have := congrArg (fun x : (ZMod (5^k))ˣ => x.val) hi
  simpa [f,X] using this

end Fact393

namespace Fact393
open Finset

theorem sum_blocks (a b : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (a*b), f i = ∑ j ∈ range a,∑ s ∈ range b,f (j*b+s) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul,sum_range_add,sum_range_succ,ih]

/-- If L digits give pairwise distinct outputs for every fixed choice of
surrounding digits, the contribution of words avoiding all those digits
is at most (B-L)^d in a block of length B^d. -/
theorem isolated_digit_count (B : ℕ) (G : Finset ℕ) (sub : G ⊆ range B)
    (F : ℕ → ℕ) (inj : ∀ j a s : ℕ, s<B^j →
      Set.InjOn (fun i => F ((a*B+i)*B^j+s)) (G : Set ℕ))
    (A : Finset ℕ) (d a : ℕ) :
    G.card * ((range (B^d)).filter (fun s => F (a*B^d+s) ∈ A)).card ≤
      A.card * B^d + G.card*(B-G.card)^d := by
  let V (a d : ℕ) := ∑ s ∈ range (B^d), if F (a*B^d+s)∈A then 1 else 0
  rw [card_filter]
  change G.card*V a d ≤ _
  have sep (j a s : ℕ) (hs : s<B^j) :
      (∑ i ∈ G, if F ((a*B+i)*B^j+s)∈A then 1 else 0) ≤ A.card := by
    rw [←card_filter]
    apply card_le_card_of_injOn (fun i => F ((a*B+i)*B^j+s))
    · intro i hi
      exact (mem_filter.mp hi).2
    · exact (inj j a s hs).mono (by intro i hi; exact (mem_filter.mp hi).1)
  have step (j a : ℕ) : V a (j+1)=∑ i ∈ range B,V (a*B+i) j := by
    unfold V
    rw [pow_succ',sum_blocks]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro s _
    rw [show a*(B*B^j)+(i*B^j+s)=(a*B+i)*B^j+s by ring]
  have hL := card_le_card sub
  rw [card_range] at hL
  induction d generalizing a with
  | zero =>
    by_cases u : F a ∈ A <;> simp [V, u, Finset.filter_singleton]
  | succ d ih =>
    have good : (∑ i ∈ G,V (a*B+i) d) ≤ B^d * A.card := by
      unfold V
      rw [sum_comm]
      calc
        _ ≤ ∑ _s ∈ range (B^d), A.card := sum_le_sum (fun s hs => sep d a s (mem_range.mp hs))
        _ = _ := by simp
    have bad : G.card*(∑ i ∈ range B \ G,V (a*B+i) d) ≤
        (B-G.card)*(A.card*B^d+G.card*(B-G.card)^d) := by
      rw [mul_sum]
      calc
        _ ≤ ∑ _i ∈ range B \ G,(A.card*B^d+G.card*(B-G.card)^d) :=
          sum_le_sum (fun i _ => ih (a*B+i))
        _ = _ := by simp [card_sdiff_of_subset sub]
    rw [step,←sum_sdiff sub,mul_add]
    have hx := Nat.add_sub_of_le hL
    have hh : G.card * (B^d*A.card)+(B-G.card)*(A.card*B^d+G.card*(B-G.card)^d) =
        A.card*B^(d+1)+G.card*(B-G.card)^(d+1) := by
      rw [pow_succ B, pow_succ (B-G.card)]
      linear_combination (A.card*B^d)*hx
    exact (Nat.add_le_add bad (Nat.mul_le_mul_left _ good)).trans (by rw [add_comm,hh])

end Fact393

namespace Fact393
open Finset

theorem power_ratio {u v : ℕ} (h : u<v) (K : ℕ) :
    ∃ d : ℕ, 0<d ∧ K*u^d≤v^d := by
  have grow (d : ℕ) : (u+d+1)*u^d≤(u+1)^(d+1) := by
    induction d with
    | zero => simp
    | succ d ih =>
      calc
        (u+(d+1)+1)*u^(d+1) = ((u+(d+1)+1)*u)*u^d := by rw [pow_succ]; ring
        _ ≤ ((u+d+1)*(u+1))*u^d := Nat.mul_le_mul_right _ (by nlinarith)
        _ = ((u+d+1)*u^d)*(u+1) := by ring
        _ ≤ _ := by rw [pow_succ (u+1) (d+1)]; exact Nat.mul_le_mul_right _ ih
  refine ⟨K*u+1,by omega,?_⟩
  calc
    K*u^(K*u+1) = (K*u)*u^(K*u) := by rw [pow_succ]; ring
    _ ≤ (u+K*u+1)*u^(K*u) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ (u+1)^(K*u+1) := grow _
    _ ≤ _ := Nat.pow_le_pow_left h _

theorem sparse_blocks (B : ℕ) (G : Finset ℕ) (sub : G ⊆ range B)
    (hL : 0<G.card) (F : ℕ → ℕ) (inj : ∀ j a s : ℕ, s<B^j →
      Set.InjOn (fun i => F ((a*B+i)*B^j+s)) (G : Set ℕ))
    (A : Finset ℕ) (K : ℕ) (small : 4*K*A.card≤G.card) :
    ∃ H : ℕ, 0<H ∧ ∀ a : ℕ, 2*K*((range H).filter (fun s => F (a*H+s)∈A)).card≤H := by
  have hB := card_le_card sub
  rw [card_range] at hB
  obtain ⟨d,_,hd⟩ := power_ratio (u:=B-G.card) (v:=B) (by omega) (4*K)
  refine ⟨B^d,pow_pos (by omega) _,?_⟩
  intro a
  let V := ((range (B^d)).filter (fun s => F (a*B^d+s)∈A)).card
  have hs : G.card*V≤A.card*B^d+G.card*(B-G.card)^d := isolated_digit_count B G sub F inj A d a
  have h : (2*G.card)*(2*K*V) ≤ (2*G.card)*B^d := calc
    _ = (4*K)*(G.card*V) := by ring
    _ ≤ (4*K)*(A.card*B^d+G.card*(B-G.card)^d) := Nat.mul_le_mul_left _ hs
    _ = (4*K*A.card)*B^d+G.card*(4*K*(B-G.card)^d) := by ring
    _ ≤ G.card*B^d+G.card*B^d := Nat.add_le_add (Nat.mul_le_mul_right _ small) (Nat.mul_le_mul_left _ hd)
    _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left h (by omega : 0<2*G.card)

/-- Every sufficiently long interval obeys the same density bound,
uniformly in the position of its left endpoint. -/
theorem density_from_blocks (E : ℕ → Prop) [DecidablePred E]
    (F : ℕ → ℕ) (A : Finset ℕ) (T K H : ℕ) (hH : 0<H)
    (event : ∀ n ≥ T, E n → F n∈A)
    (hb : ∀ a : ℕ, 2*K*((range H).filter (fun s => F (a*H+s)∈A)).card≤H) :
    ∀ n ≥ 2*K*T+2*H, ∀ a, K*((range n).filter (fun s => E (a+s))).card≤n := by
  intro n hn a
  let C := n/H+2
  let b := a/H
  let r := a%H
  have ha : a=b*H+r := by simpa [b,r,add_comm,mul_comm] using (Nat.mod_add_div a H).symm
  have hC : r+n≤C*H := by
    dsimp [C,r]
    have := Nat.mod_lt n hH
    have := Nat.mod_lt a hH
    have := Nat.mod_add_div n H
    rw [add_mul,mul_comm (n/H) H]; omega
  let good := (range n).filter (fun s => F (a+s)∈A)
  have split : (range n).filter (fun s => E (a+s)) ⊆ (range T) ∪ good := by
    intro i hi
    obtain ⟨hni,he⟩ := mem_filter.mp hi
    by_cases hit : i<T
    · exact mem_union_left _ (mem_range.mpr hit)
    · exact mem_union_right _ (mem_filter.mpr ⟨hni,event _ (by omega) he⟩)
  have s1 := (card_le_card split).trans (card_union_le _ _)
  rw [card_range] at s1
  let cover := (range (C*H)).filter (fun i => F (b*H+i)∈A)
  have embed : good.card≤cover.card := by
    apply card_le_card_of_injOn (fun s => r+s)
    · intro i hi
      obtain ⟨hin,hiF⟩ := mem_filter.mp hi
      have := mem_range.mp hin
      exact mem_filter.mpr ⟨mem_range.mpr (by change r+i<C*H; omega),by simpa only [←add_assoc,←ha] using hiF⟩
    · intro x _ y _ he
      exact Nat.add_left_cancel he
  have s2 : 2*K*cover.card≤C*H := by
    dsimp [cover]
    rw [card_filter,sum_blocks,mul_sum]
    calc
      _ ≤ ∑ _i ∈ range C,H := by
        apply sum_le_sum
        intro i _
        simpa only [card_filter,add_mul,add_assoc] using hb (b+i)
      _ = _ := by simp
  have s3 := Nat.mul_le_mul_left (2*K) (s1.trans (Nat.add_le_add_left embed T))
  rw [mul_add, Nat.mul_assoc 2 K] at s3
  have s4 : C*H≤n+2*H := by
    dsimp [C]
    rw [add_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  omega

end Fact393

namespace Fact393
open Finset Filter OMA.S_mo_393993
open scoped Classical Topology

/-- Reading any number of final digits that tends to infinity, however
slowly, leaves a candidate set of upper Banach density zero. -/
theorem suffix_uniform_density (q : ℕ → ℕ) (grow : ∀ d : ℕ, ∃ t, ∀ n ≥ t, d≤q n) (K : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ,
      K*((range n).filter (fun s => 0∉(Nat.digits 10 ((a+s).factorial /
        10^padicValNat 10 (a+s).factorial)).take (q (a+s)))).card≤n := by
  obtain ⟨m,hm,hr⟩ := power_ratio (u:=23) (v:=25) (by decide) (20*K)
  let k := 2*m
  have hk : 0<k := by dsimp [k]; omega
  have p5 : 5^k=25^m := by dsimp [k]; rw [pow_mul]; rfl
  have p' : 5^k=5*5^(k-1) := by nth_rw 1 [show k=k-1+1 by omega]; rw [pow_succ']
  obtain ⟨B,_,G,Gsub,Gcard,inj⟩ := decimal_factorial_gadget_nat hk
  obtain ⟨A,Ac,cover⟩ := suffix_residue_cover_take m
  let F (n : ℕ) := (n.factorial / 10^padicValNat 10 n.factorial) % (5^k)
  have small : 4*K*A.card≤G.card := by
    rw [←p5,p'] at hr
    have hA := Nat.mul_le_mul_left (20*K) Ac
    rw [Gcard]
    nlinarith only [hr,hA]
  obtain ⟨H,hH,hb⟩ := sparse_blocks B G Gsub (by rw [Gcard]; positivity) F inj A K small
  obtain ⟨t,ht⟩ := grow (2*m)
  let T := max t (4*(7*m+1))
  refine ⟨_,density_from_blocks (fun n => 0∉(Nat.digits 10 (n.factorial / 10^padicValNat 10 n.factorial)).take (q n)) F A T K H hH ?_ hb⟩
  intro n hn he
  obtain ⟨h₁,h₂⟩ := stripped_size (m:=m) ((le_max_right _ _).trans hn)
  simpa only [F,p5] using cover _ (q n) (ht _ ((le_max_left _ _).trans hn)) h₁ h₂ he

/-- For the residual problem we read 32 times as many final digits
of the stripped factorial as there are decimal digits in its index. -/
theorem growing_suffix_density (K : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ,
      K*((range n).filter (fun s => 0∉(Nat.digits 10 ((a+s).factorial /
        10^padicValNat 10 (a+s).factorial)).take (32*(Nat.log 10 (a+s)+1)))).card≤n := by
  apply suffix_uniform_density (fun n => 32*(Nat.log 10 n+1)) _ K
  intro d
  exact ⟨10^d,fun n hn => by have := Nat.le_log_of_pow_le (by decide : 1<10) hn; omega⟩

theorem zero_free_uniform_density (K : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ,
      K*((range n).filter (fun s => ZerosAtEnd (a+s))).card≤n := by
  obtain ⟨N,hN⟩ := growing_suffix_density K
  refine ⟨N,fun n hn a => (Nat.mul_le_mul_left K (card_le_card ?_)).trans (hN n hn a)⟩
  intro s hs
  obtain ⟨hi,hz⟩ := mem_filter.mp hs
  exact mem_filter.mpr ⟨hi,fun he => hz ((List.take_prefix _ _).subset he)⟩

/-- In particular the ordinary natural density exists and equals zero. -/
theorem zero_free_density :
    Tendsto (fun n : ℕ => (((range n).filter ZerosAtEnd).card:ℝ)/n) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε)
  have hKr : (0:ℝ)<K := lt_trans (by positivity : (0:ℝ)<1/ε) hK
  obtain ⟨N,hn⟩ := zero_free_uniform_density K
  refine ⟨max N 1,fun n h => ?_⟩
  have hn' : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hc : K*((range n).filter ZerosAtEnd).card≤n := by simpa using hn n (by omega) 0
  have hcr : (K:ℝ)*((range n).filter ZerosAtEnd).card≤n := by exact_mod_cast hc
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity),div_lt_iff₀ hn']
  have hke := (div_lt_iff₀ hε).mp hK
  nlinarith [mul_lt_mul_of_pos_right hke hn']

end Fact393

namespace Fact393
open Finset

/-- A frequency estimate for any set of outputs on a moving interval. The threshold
depends only on the block system and the requested precision. -/
private lemma uniform_upper (B : ℕ) (G : Finset ℕ) (sub : G ⊆ range B)
    (hL : 0<G.card) (F : ℕ → ℕ) (inj : ∀ j a s : ℕ, s<B^j →
      Set.InjOn (fun i => F ((a*B+i)*B^j+s)) (G : Set ℕ)) (K : ℕ) (hK : 0<K) :
    ∃ N : ℕ, 0<N ∧ ∀ n≥N, ∀ a, ∀ A : Finset ℕ, A.card ≤ G.card →
      K * (G.card * ((range n).filter (fun s => F (a+s)∈A)).card) ≤ K*(A.card*n)+n := by
  have hLB := card_le_card sub
  rw [card_range] at hLB
  obtain ⟨d,_,hd⟩ := power_ratio (u:=B-G.card) (v:=B) (by omega) (4*K*G.card)
  let H := B^d
  let E := (B-G.card)^d
  have Hpos : 0<H := pow_pos (by omega) _
  let N := 4*K*G.card*H+2*H
  refine ⟨N, by dsimp [N]; positivity,?_⟩
  intro n hn a A hA
  let C := n/H+2
  let b := a/H
  let r := a%H
  have ha : a=b*H+r := by simpa [b,r,add_comm,mul_comm] using (Nat.mod_add_div a H).symm
  have hC : r+n≤C*H := by
    dsimp [C,r]
    have := Nat.mod_lt n Hpos
    have := Nat.mod_lt a Hpos
    have := Nat.mod_add_div n H
    rw [add_mul,mul_comm (n/H) H]; omega
  have hC' : C*H≤n+2*H := by
    dsimp [C]; rw [add_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  let V := ((range n).filter fun s => F (a+s)∈A).card
  let W := ((range (C*H)).filter fun s => F (b*H+s)∈A).card
  have emb : V≤W := by
    apply card_le_card_of_injOn (fun s => r+s)
    · intro i hi
      obtain ⟨hin,he⟩ := mem_filter.mp hi
      have := mem_range.mp hin
      exact mem_filter.mpr ⟨mem_range.mpr (by change r+i<C*H; omega), by simpa only [←add_assoc,←ha] using he⟩
    · intro x _ y _ he
      exact Nat.add_left_cancel he
  have cap : G.card*W ≤ C*(A.card*H+G.card*E) := by
    dsimp [W]
    rw [card_filter, sum_blocks, mul_sum]
    calc
      _ ≤ ∑ _i ∈ range C, (A.card*H+G.card*E) := by
        apply sum_le_sum
        intro i _
        simpa only [card_filter, add_mul, add_assoc] using isolated_digit_count B G sub F inj A d (b+i)
      _ = _ := by simp
  have h1 : 4*K*A.card*H ≤ n := (Nat.mul_le_mul_right H (Nat.mul_le_mul_left (4*K) hA)).trans (by dsimp [N] at hn; omega)
  have h2 : C*H ≤ 2*n := by dsimp [N] at hn; omega
  have he : (4*K*G.card*E)*C ≤ 2*n := (Nat.mul_le_mul_right C hd).trans (by change H*C≤2*n; rwa [mul_comm H C])
  have final : 2*(K*(G.card*V)) ≤ 2*(K*(A.card*n)+n) := calc
    _ ≤ (2*K)*(C*(A.card*H+G.card*E)) := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ ((Nat.mul_le_mul_left G.card emb).trans cap)
    _ = (2*K*A.card)*(C*H) + (2*K*G.card*E)*C := by ring
    _ ≤ (2*K*A.card)*(n+2*H) + (2*K*G.card*E)*C :=
      Nat.add_le_add_right (Nat.mul_le_mul_left _ hC') _
    _ = 2*(K*(A.card*n)) + 4*K*A.card*H + (2*K*G.card*E)*C := by ring
    _ ≤ _ := by
      have last : (2*K*G.card*E)*C ≤ n := by
        have : 2*((2*K*G.card*E)*C) ≤ 2*n := by convert he using 1; ring
        omega
      omega
  change K*(G.card*V) ≤ _
  omega

private lemma frequency_error {K L n x : ℕ} (hK : 0<K) (hL : 0<L) (hn : 0<n)
    (lo : K*n ≤ K*(L*x)+n) (hi : K*(L*x) ≤ K*n+n) :
    |(x:ℝ)/n-1/(L:ℝ)| ≤ 1/(K:ℝ) := by
  have kpos : (0:ℝ)<K := by exact_mod_cast hK
  have lpos : (0:ℝ)<L := by exact_mod_cast hL
  have npos : (0:ℝ)<n := by exact_mod_cast hn
  have lb : (K:ℝ)*n ≤ K*(L*x)+n := by exact_mod_cast lo
  have ub : (K:ℝ)*(L*x) ≤ K*n+n := by exact_mod_cast hi
  have lex : (1:ℝ)≤L := by exact_mod_cast hL
  have exp := mul_le_mul_of_nonneg_right lex npos.le
  rw [abs_le]
  constructor <;> field_simp [kpos.ne',lpos.ne',npos.ne'] <;> nlinarith

/-- For each precision, every 5-adic unit has its uniform limiting frequency among
the stripped factorials. The interval's starting point and the choice of unit may
both vary with its length. -/
theorem stripped_equidistributed {k : ℕ} (hk : 0<k) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ, ∀ r : (ZMod (5^k))ˣ,
      |(((range n).filter (fun s => ((a+s).factorial /
          10^padicValNat 10 (a+s).factorial) % (5^k) = (r:ZMod (5^k)).val)).card : ℝ)/n -
        1/((4*5^(k-1):ℕ):ℝ)| ≤ ε := by
  obtain ⟨z,hz⟩ := exists_nat_one_div_lt hε
  let K := z+1
  let L := 4*5^(k-1)
  let D := 5^k
  let F (n : ℕ) := (n.factorial / 10^padicValNat 10 n.factorial)%D
  let U := (range D).filter (fun y => D.Coprime y)
  have Lpos : 0<L := by dsimp [L]; positivity
  have Kpos : 0<K := by dsimp [K]; omega
  have Ucard : U.card = L := by
    change D.totient=L
    obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    simp [D,L,Nat.totient_prime_pow_succ Nat.prime_five,Nat.mul_comm]
  have unit_in (v : (ZMod D)ˣ) : (v : ZMod D).val ∈ U :=
    mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt _), (ZMod.val_coe_unit_coprime v).symm⟩
  have falls (n : ℕ) : F n ∈ U := by
    let x := n.factorial / 10^padicValNat 10 n.factorial
    have hu : IsUnit (x:ZMod D) := by
      dsimp [x,D]; rw [← corrected_factorial_eq]
      exact corrected_isUnit (Nat.factorial_ne_zero _)
    have mem := unit_in hu.unit
    rw [hu.unit_spec, ZMod.val_natCast] at mem
    exact mem
  obtain ⟨B,_,G,sub,card,inj⟩ := decimal_factorial_gadget_nat hk
  change G.card=L at card
  obtain ⟨N,hN,est⟩ := uniform_upper B G sub (card ▸ Lpos) F inj K Kpos
  refine ⟨N,?_⟩
  intro n hn a r
  let v := (r:ZMod D).val
  have vin : v∈U := unit_in r
  let x := ((range n).filter (fun s => F (a+s)=v)).card
  let y := ((range n).filter (fun s => F (a+s)≠v)).card
  have pair : x+y=n := by
    simpa [x,y] using (card_filter_add_card_filter_not (s := range n) (fun s => F (a+s)=v))
  have hi : K*(L*x)≤K*n+n := by
    have hh := est n hn a {v} (by rw [card_singleton,card]; omega)
    simpa [card,x] using hh
  have upperY := est n hn a (U.erase v) (by rw [card_erase_of_mem vin,Ucard,card]; omega)
  have hy : K*(L*y)≤K*((L-1)*n)+n := by
    simpa only [card, card_erase_of_mem vin, Ucard, mem_erase, falls, and_true, y] using upperY
  have id1 : K*(L*x)+K*(L*y)=K*(L*n) := by rw [← mul_add, ← mul_add, pair]
  have id2 : K*((L-1)*n)+K*n=K*(L*n) := by
    rw [←mul_add, ←Nat.succ_mul, show (L-1).succ=L by omega]
  have lo : K*n≤K*(L*x)+n := by omega
  have err := frequency_error Kpos Lpos (hN.trans_le hn) lo hi
  exact err.trans (by simpa [K] using hz.le)

theorem stripped_frequency_tendsto {k : ℕ} (hk : 0<k) (a : ℕ → ℕ)
    (r : ℕ → (ZMod (5^k))ˣ) :
    Filter.Tendsto (fun n : ℕ =>
      (((range n).filter (fun s => ((a n+s).factorial / 10^padicValNat 10 (a n+s).factorial) %
        (5^k) = ((r n):ZMod (5^k)).val)).card : ℝ)/n) Filter.atTop
      (nhds (1 / ((4*5^(k-1):ℕ):ℝ))) := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  obtain ⟨N,hN⟩ := stripped_equidistributed hk (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact (hN n hn (a n) (r n)).trans_lt (half_lt_self hε)

end Fact393

namespace Fact393
open Finset Filter

/-- Above the explicit valuation threshold, the residue modulo 5^k
determines the entire k-digit decimal suffix for every admissible block. -/
theorem decimal_suffix_iff {k n r : ℕ} (hn : 4*(k+1)≤n)
    (hr : r<10^k) (hd : 2^k∣r) :
    (n.factorial/10^padicValNat 10 n.factorial)%10^k=r ↔
      (n.factorial/10^padicValNat 10 n.factorial)%5^k=r%5^k := by
  let X := n.factorial/10^padicValNat 10 n.factorial
  have eq : 2^k*5^k=10^k := by rw [←mul_pow]; rfl
  have hX : 2^k∣X := stripped_divisible hn
  have hb : X ≡ r [MOD 2^k] :=
    (Nat.modEq_zero_iff_dvd.mpr hX).trans (Nat.modEq_zero_iff_dvd.mpr hd).symm
  have h := Nat.modEq_and_modEq_iff_modEq_mul (a:=X) (b:=r)
    (((show Nat.Coprime 2 5 by decide).pow_left k).pow_right k)
  rw [eq] at h
  change X%10^k=r ↔ X ≡ r [MOD 5^k]
  constructor
  · intro ha
    exact (h.mpr (by simpa only [Nat.ModEq,Nat.mod_eq_of_lt hr] using ha)).2
  · intro ha
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hr] using h.mp ⟨hb,ha⟩

/-- Every admissible decimal block of length k has frequency 1/φ(5^k).
The chosen block and the starting point may both depend on interval length. -/
theorem decimal_suffix_frequency {k : ℕ} (hk : 0<k) (a r : ℕ → ℕ)
    (ha : ∀ n, 4*(k+1)≤a n) (hr : ∀ n, r n<10^k)
    (hd : ∀ n, 2^k∣r n) (h5 : ∀ n, (r n).Coprime (5^k)) :
    Tendsto (fun n : ℕ => (((range n).filter (fun s =>
      ((a n+s).factorial/10^padicValNat 10 (a n+s).factorial)%10^k=r n)).card : ℝ)/n)
      atTop (nhds (1 / ((4*5^(k-1):ℕ):ℝ))) := by
  let u (n : ℕ) : (ZMod (5^k))ˣ := ZMod.unitOfCoprime (r n) (h5 n)
  convert stripped_frequency_tendsto hk a u using 1
  ext n
  congr 2
  apply congrArg Finset.card
  apply filter_congr
  intro s _
  simpa [u, ZMod.val_natCast] using decimal_suffix_iff (n:=a n+s) ((ha n).trans (by omega)) (hr n) (hd n)

end Fact393

namespace Fact393

theorem low_scale {k : ℕ} (h125 : (125:ZMod (5^k))=0) (t : ℕ) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k (5*t).factorial = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k t.factorial * (12:ZMod (5^k))^t := by
  rw [corrected_scale]
  change _ * (∏ i ∈ Finset.range t, (5*(i:ZMod (5^k))+1)*(5*i+2)*(5*i+3)*(5*i+4)) * _ = _
  have w (z : ZMod (5^k)) :
      (5*z+1)*(5*z+2)*(5*z+3)*(5*z+4) = 24 := by
    calc
      _ = 24 + 125*(5*z^4+10*z^3+7*z^2+2*z) := by ring
      _ = _ := by rw [h125]; ring
  simp_rw [w]
  rw [Finset.prod_const, Finset.card_range,mul_assoc,←mul_pow]
  congr 2
  calc
    (24:ZMod (5^k))*2⁻¹ = 12*(2*2⁻¹) := by ring
    _ = 12 := by rw [ZMod.mul_inv_of_unit _ (two_unit k),mul_one]

theorem stable_mod_25 {a : ℕ} (h20 : 20 ∣ a) (j : ℕ) :
    (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) 2 (a*5^j).factorial = (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) 2 a.factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show a*5^(j+1)=5*(a*5^j) by ring, low_scale (by decide)]
    obtain ⟨t,ht⟩ := dvd_mul_of_dvd_left h20 (5^j)
    rw [ht,pow_mul,show (12:ZMod (5^2))^20=1 by decide,one_pow,mul_one,←ht]
    exact ih

theorem low_digits_exclude {k n r d : ℕ} (h : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) k n.factorial = (r:ℕ))
    (hr : r<10^k) (hr2 : 2^k ∣ r) (hd : d<k) (hdig : r/10^d%10=0)
    (hn : 4*(4*k+1) ≤ n) : ¬OMA.S_mo_393993.ZerosAtEnd n := by
  rw [corrected_factorial_eq] at h
  let X := n.factorial / 10^(padicValNat 10 n.factorial)
  have h5 : X ≡ r [MOD 5^k] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hX := stripped_divisible (n:=n) (k:=4*k) hn
  change 2^(4*k) ∣ X at hX
  have h2 := (pow_dvd_pow 2 (by omega : k≤4*k)).trans hX
  have he : X ≡ r [MOD 2^k] := (Nat.modEq_zero_iff_dvd.mpr h2).trans (Nat.modEq_zero_iff_dvd.mpr hr2).symm
  have E := (Nat.modEq_and_modEq_iff_modEq_mul ((show Nat.Coprime 2 5 by decide).pow k k)).mp ⟨he,h5⟩
  rw [←mul_pow,show 2*5=10 by decide] at E
  have suffix : X%10^k=r := Eq.trans E (Nat.mod_eq_of_lt hr)
  have hdiv := pow_dvd_pow 10 (by omega : d+1≤k)
  have eqdig : X/10^d%10=0 := by
    rw [←Nat.mod_mul_right_div_self,←pow_succ,←Nat.mod_mod_of_dvd X hdiv,suffix,
      pow_succ,Nat.mod_mul_right_div_self,hdig]
  have hxpos : 0 < X := Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) pow_padicValNat_dvd) (by positivity)
  have hxge : 10^d ≤ X := calc
    _ ≤ (16:ℕ)^d := Nat.pow_le_pow_left (by decide) d
    _ = 2^(4*d) := by rw [pow_mul]; norm_num
    _ ≤ 2^(4*k) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ X := Nat.le_of_dvd hxpos hX
  have hxq : 0 < X/10^d := Nat.div_pos hxge (by positivity)
  intro zeroFree
  change 0 ∉ Nat.digits 10 X at zeroFree
  apply zeroFree
  apply digit_in_quotient (by decide : 1<10) d
  rw [Nat.digits_eq_cons_digits_div (by decide) hxq.ne',eqdig]
  simp

theorem family_ending_08 (a : ℕ) (ha : 20 ∣ a) (ha2 : 36≤a)
    (hc : (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t) 2 a.factorial=8) (j : ℕ) : ¬OMA.S_mo_393993.ZerosAtEnd (a*5^j) := by
  have h := (stable_mod_25 ha j).trans hc
  have hn : a≤a*5^j := Nat.le_mul_of_pos_right _ (by positivity)
  exact low_digits_exclude (k:=2) (r:=8) (d:=1) h (by decide) (by decide) (by decide)
    (by decide) (by omega)

theorem pure_16_44 (j : ℕ) (a : ℕ) (ha : a=16 ∨ a=44) :
    ¬OMA.S_mo_393993.ZerosAtEnd (a*5^(j+1)) := by
  rw [pow_succ',←mul_assoc]
  rcases ha with rfl | rfl
  · exact family_ending_08 80 (by decide) (by decide) (by decide +kernel) j
  · exact family_ending_08 220 (by decide) (by decide) (by decide +kernel) j

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 6000 in
theorem pure_five_classification (J : ℕ) :
    OMA.S_mo_393993.ZerosAtEnd (5^J) ↔ J≤1 := by
  let corrected := (fun (k t : ℕ) => ((t / 5^(padicValNat 5 t) : ℕ) : ZMod (5^k)) * (2 : ZMod (5^k))⁻¹ ^ padicValNat 5 t)
  let peval (p : List (ZMod (5^37))) (x : ZMod (5^37)) :=
    p.foldr (fun c y => c+x*y) 0

  let padd (p q : List (ZMod (5^37))) : List (ZMod (5^37)) :=
    (List.rec (motive := fun _ : List (ZMod (5^37)) => List (ZMod (5^37)) → List (ZMod (5^37)))
      id (fun v vs tail l => match l with
        | [] => v::vs
        | t::ts => (v+t)::tail ts) p) q

  let pmul (p q : List (ZMod (5^37))) :=
    p.foldr (fun c acc => padd (q.map (c*·)) (0::acc)) []

  let pshift (p : List (ZMod (5^37))) (a : ZMod (5^37)) :=
    p.foldr (fun c acc => padd [c] (pmul [a,5] acc)) []

  let combine (p : List (ZMod (5^37))) :=
    pmul (pmul (pmul (pmul (pshift p 0) (pshift p 1)) (pshift p 2)) (pshift p 3)) (pshift p 4)

  have ev_add (p q : List (ZMod (5^37))) (x : ZMod (5^37)) :
      peval (padd p q) x = peval p x + peval q x := by
    induction p generalizing q with
    | nil => simp [peval,padd]
    | cons c p ih =>
      cases q with
      | nil => simp [peval,padd]
      | cons d q =>
        change c+d+x*peval (padd p q) x = (c+x*peval p x)+(d+x*peval q x)
        rw [ih]; ring

  have ev_mul (p q : List (ZMod (5^37))) (x : ZMod (5^37)) :
      peval (pmul p q) x = peval p x * peval q x := by
    have scal (c : ZMod (5^37)) : peval (q.map (c*·)) x = c*peval q x := by
      induction q with
      | nil => simp [peval]
      | cons d q ih =>
        change c*d+x*peval (q.map (c*·)) x = c*(d+x*peval q x)
        rw [ih]; ring
    induction p with
    | nil => simp [pmul,peval]
    | cons c p ih =>
      change peval (padd (q.map (c*·)) (0::pmul p q)) x = (c+x*peval p x)*peval q x
      rw [ev_add,scal]
      change c*peval q x+(0+x*peval (pmul p q) x)=_
      rw [ih]; ring

  have ev_shift (p : List (ZMod (5^37))) (a x : ZMod (5^37)) :
      peval (pshift p a) x = peval p (5*x+a) := by
    induction p with
    | nil => rfl
    | cons c p ih =>
      change peval (padd [c] (pmul [a,5] (pshift p a))) x = c+(5*x+a)*peval p (5*x+a)
      rw [ev_add [c] (pmul [a,5] (pshift p a)) x,ev_mul [a,5] (pshift p a) x,ih]
      simp [peval]; ring

  have ev_padding (p : List (ZMod (5^37))) (d : ℕ) (x : ZMod (5^37)) :
      peval (p ++ List.replicate d 0) x = peval p x := by
    have h : peval (List.replicate d 0) x = 0 := by
      induction d with
      | zero => rfl
      | succ d ih =>
        rw [List.replicate_succ]
        change 0 + x*peval (List.replicate d 0) x = 0
        rw [ih]; ring
    simp [peval,List.foldr_append,peval] at h ⊢
    rw [h]

  let unitBlock (j a : ℕ) : ZMod (5^37) :=
    ∏ i ∈ Finset.range (5^j), let z : ZMod (5^37) := (5^j*a+i : ℕ); (5*z+1)*(5*z+2)*(5*z+3)*(5*z+4)

  have prod_partition {R : Type} [CommMonoid R] (f : ℕ → R) (n b : ℕ) :
      (∏ i ∈ Finset.range (n*b), f i) =
        ∏ r ∈ Finset.range n, ∏ i ∈ Finset.range b, f (r*b+i) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.succ_mul,Finset.prod_range_add,Finset.prod_range_succ,ih]

  have unitBlock_succ (j a : ℕ) :
      unitBlock (j+1) a = ∏ r ∈ Finset.range 5, unitBlock j (5*a+r) := by
    unfold unitBlock
    rw [pow_succ' (5:ℕ) j,prod_partition]
    apply Finset.prod_congr rfl
    intro r hr
    apply Finset.prod_congr rfl
    intro i hi
    rw [show 5 * 5^j * a + (r * 5^j + i) = 5^j*(5*a+r)+i by ring]

  have unitBlock_refl {j : ℕ} {p q : List (ZMod (5^37))}
      (old : ∀ a : ℕ, unitBlock j a = peval p a)
      (norm : combine p = q ++ List.replicate ((combine p).length-q.length) 0)
      (a : ℕ) : unitBlock (j+1) a = peval q a := by
    rw [unitBlock_succ,←ev_padding q ((combine p).length-q.length),←norm]
    simp only [combine,ev_mul,ev_shift]
    norm_num [Finset.prod_range_succ,old]


  have block_0 (a : ℕ) : unitBlock 0 a = peval [24,250,875,1250,625] a := by
    simp [unitBlock,peval]
    ring

  have block_1 (a : ℕ) : unitBlock 1 a = peval [41363226782215962624,3473778415016448000000,125869081087064448000000,2660646033753471000000000,37240607014267360500000000,6423293663971868896484375,39572048426428021240234375,53855043846982574462890625,26407464276407623291015625,8353429639339447021484375,53428996722698211669921875,13770516812801361083984375,1504548490047454833984375,34658238291740417480468750,27569010853767395019531250,33993273973464965820312500,40628947317600250244140625] a :=
    unitBlock_refl block_0 (by decide +kernel) a

  have block_2 (a : ℕ) : unitBlock 2 a = peval [33333850217125232558250624,47530574805954030121093750,58588208990571345794921875,68205164047754833984375000,38844692576665197753906250,52220811286449432373046875,71208675814628601074218750,60983675718307495117187500,28633680939674377441406250,33178366720676422119140625,64843334257602691650390625] a :=
    unitBlock_refl block_1 (by decide +kernel) a

  have block_3 (a : ℕ) : unitBlock 3 a = peval [7663742675570036722893749,39869796131629711181640625,20216850378551250488281250,6504077799835205078125000,10092789474983215332031250,70491097867488861083984375,54541118443012237548828125,5820766091346740722656250,37834979593753814697265625] a :=
    unitBlock_refl block_2 (by decide +kernel) a

  have block_4 (a : ℕ) : unitBlock 4 a = peval [49670540634377239180874999,50533860179109100341796875,15518378528279785156250000,8549378931522369384765625,55206392765045166015625000,17462298274040222167968750,5820766091346740722656250] a :=
    unitBlock_refl block_3 (by decide +kernel) a

  have block_5 (a : ℕ) : unitBlock 5 a = peval [51710970138697350689531249,42453030010402679443359375,58206537624538421630859375,31507015228271484375000000,15753507614135742187500000] a :=
    unitBlock_refl block_4 (by decide +kernel) a

  have block_6 (a : ℕ) : unitBlock 6 a = peval [39621601337493803008203124,12095751904010772705078125,56333574198246002197265625,15716068446636199951171875,44237822294235229492187500] a :=
    unitBlock_refl block_5 (by decide +kernel) a

  have block_7 (a : ℕ) : unitBlock 7 a = peval [47733124546602163234374999,20968112170696258544921875,20968112170696258544921875] a :=
    unitBlock_refl block_6 (by decide +kernel) a

  have block_8 (a : ℕ) : unitBlock 8 a = peval [26238180224275159433593749,30773110687732696533203125,30773110687732696533203125] a :=
    unitBlock_refl block_7 (by decide +kernel) a

  have block_9 (a : ℕ) : unitBlock 9 a = peval [42055221076724765673828124,63140876591205596923828125,63140876591205596923828125] a :=
    unitBlock_refl block_8 (by decide +kernel) a

  have block_10 (a : ℕ) : unitBlock 10 a = peval [59552078202952136474609374,34575350582599639892578125,34575350582599639892578125] a :=
    unitBlock_refl block_9 (by decide +kernel) a

  have block_11 (a : ℕ) : unitBlock 11 a = peval [51688858050054261474609374,29103830456733703613281250,29103830456733703613281250] a :=
    unitBlock_refl block_10 (by decide +kernel) a

  have block_12 (a : ℕ) : unitBlock 12 a = peval [58389294534653173828124999] a :=
    unitBlock_refl block_11 (by decide +kernel) a

  have block_13 (a : ℕ) : unitBlock 13 a = peval [19944029002039367675781249] a :=
    unitBlock_refl block_12 (by decide +kernel) a

  have block_14 (a : ℕ) : unitBlock 14 a = peval [66299634420120391845703124] a :=
    unitBlock_refl block_13 (by decide +kernel) a

  have block_15 (a : ℕ) : unitBlock 15 a = peval [5302440341530609130859374] a :=
    unitBlock_refl block_14 (by decide +kernel) a

  have block_16 (a : ℕ) : unitBlock 16 a = peval [20691435616306304931640624] a :=
    unitBlock_refl block_15 (by decide +kernel) a

  have block_17 (a : ℕ) : unitBlock 17 a = peval [30697601939697265624999999] a :=
    unitBlock_refl block_16 (by decide +kernel) a

  have block_18 (a : ℕ) : unitBlock 18 a = peval [7968857414817810058593749] a :=
    unitBlock_refl block_17 (by decide +kernel) a

  have block_19 (a : ℕ) : unitBlock 19 a = peval [39844287074089050292968749] a :=
    unitBlock_refl block_18 (by decide +kernel) a

  have block_20 (a : ℕ) : unitBlock 20 a = peval [53702283086776733398437499] a :=
    unitBlock_refl block_19 (by decide +kernel) a

  have block_21 (a : ℕ) : unitBlock 21 a = peval [50232687008380889892578124] a :=
    unitBlock_refl block_20 (by decide +kernel) a

  have block_22 (a : ℕ) : unitBlock 22 a = peval [32884706616401672363281249] a :=
    unitBlock_refl block_21 (by decide +kernel) a

  have block_23 (a : ℕ) : unitBlock 23 a = peval [18904380798339843749999999] a :=
    unitBlock_refl block_22 (by decide +kernel) a

  have block_24 (a : ℕ) : unitBlock 24 a = peval [21762327849864959716796874] a :=
    unitBlock_refl block_23 (by decide +kernel) a

  have block_25 (a : ℕ) : unitBlock 25 a = peval [36052063107490539550781249] a :=
    unitBlock_refl block_24 (by decide +kernel) a

  have block_26 (a : ℕ) : unitBlock 26 a = peval [34741163253784179687499999] a :=
    unitBlock_refl block_25 (by decide +kernel) a

  have block_27 (a : ℕ) : unitBlock 27 a = peval [28186663985252380371093749] a :=
    unitBlock_refl block_26 (by decide +kernel) a

  have block_28 (a : ℕ) : unitBlock 28 a = peval [68173743784427642822265624] a :=
    unitBlock_refl block_27 (by decide +kernel) a

  have block_29 (a : ℕ) : unitBlock 29 a = peval [49830414354801177978515624] a :=
    unitBlock_refl block_28 (by decide +kernel) a

  have block_30 (a : ℕ) : unitBlock 30 a = peval [30873343348503112792968749] a :=
    unitBlock_refl block_29 (by decide +kernel) a

  have block_31 (a : ℕ) : unitBlock 31 a = peval [8847564458847045898437499] a :=
    unitBlock_refl block_30 (by decide +kernel) a

  have block_32 (a : ℕ) : unitBlock 32 a = peval [44237822294235229492187499] a :=
    unitBlock_refl block_31 (by decide +kernel) a

  have block_33 (a : ℕ) : unitBlock 33 a = peval [2910383045673370361328124] a :=
    unitBlock_refl block_32 (by decide +kernel) a

  have block_34 (a : ℕ) : unitBlock 34 a = peval [14551915228366851806640624] a :=
    unitBlock_refl block_33 (by decide +kernel) a

  have block_35 (a : ℕ) : unitBlock 35 a = peval [72759576141834259033203124] a :=
    unitBlock_refl block_34 (by decide +kernel) a

  have block_end {j : ℕ} (hj : 35 ≤ j) (a : ℕ) :
      unitBlock j a = -1 := by
    induction j, hj using Nat.le_induction generalizing a with
    | base =>
      rw [block_35]
      simp only [peval,List.foldr, mul_zero,add_zero]
      decide +kernel
    | succ j hj ih =>
      rw [unitBlock_succ]
      simp only [ih,Finset.prod_const,Finset.card_range]
      decide +kernel

  have logic (F : ℕ → ZMod (5^37)) (hF0 : F 0 = 1)
      (hFstep : ∀ j, F (j+1) = F j * unitBlock j 0 * (2:ZMod (5^37))⁻¹^(5^j))
      (hFkill : ∀ j r d : ℕ, F j = (r:ℕ) → r<10^37 → 2^37∣r → d<37 →
        r/10^d%10=0 → 4*(4*37+1)≤5^j → ¬OMA.S_mo_393993.ZerosAtEnd (5^j)) :
      OMA.S_mo_393993.ZerosAtEnd (5^J) ↔ J≤1 := by
    have state_step {j : ℕ} {u b w : ZMod (5^37)}
        (hu : F (j) = u) (hb : (2:ZMod (5^37))⁻¹^(5^j) = b)
        (hw : unitBlock j 0 = w) :
        F (j+1) = u*w*b ∧
          (2:ZMod (5^37))⁻¹^(5^(j+1)) = b^5 := by
      constructor
      · rw [hFstep,hu,hw,hb]
      · rw [pow_succ (5:ℕ) j,pow_mul,hb]

    have state_next {j : ℕ} {u b w v c : ZMod (5^37)}
        (old : F (j) = u ∧ (2:ZMod (5^37))⁻¹^(5^j) = b)
        (hw : unitBlock j 0 = w) (hv : u*w*b=v) (hc : b^5=c) :
        F (j+1) = v ∧ (2:ZMod (5^37))⁻¹^(5^(j+1)) = c :=
      ⟨(state_step (j:=j) old.1 old.2 hw).1.trans hv,(state_step (j:=j) old.1 old.2 hw).2.trans hc⟩

    have state_0 : F (0) = 1 ∧ (2:ZMod (5^37))⁻¹^(5^0) = 36379788070917129516601563 := ⟨hF0,by decide +kernel⟩

    have state_1 : F (1) = 12 ∧ (2:ZMod (5^37))⁻¹^(5^1) = 6821210263296961784362793 :=
      state_next (j:=0) state_0 (block_0 0) (by decide +kernel) (by decide +kernel)

    have state_2 : F (2) = 15511210043330985984 ∧ (2:ZMod (5^37))⁻¹^(5^2) = 54709229767996303550603443 :=
      state_next (j:=1) state_1 (block_1 0) (by decide +kernel) (by decide +kernel)

    have state_3 : F (3) = 25815192561491437236614588 ∧ (2:ZMod (5^37))⁻¹^(5^3) = 54573535661971940785700443 :=
      state_next (j:=2) state_2 (block_2 0) (by decide +kernel) (by decide +kernel)

    have state_4 : F (4) = 11298353343283839099181266 ∧ (2:ZMod (5^37))⁻¹^(5^4) = 33776335261749640708919818 :=
      state_next (j:=3) state_3 (block_3 0) (by decide +kernel) (by decide +kernel)

    have state_5 : F (5) = 23478304832998867215114162 ∧ (2:ZMod (5^37))⁻¹^(5^5) = 32967938972569134409001068 :=
      state_next (j:=4) state_4 (block_4 0) (by decide +kernel) (by decide +kernel)

    have state_6 : F (6) = 59160817443806186165387484 ∧ (2:ZMod (5^37))⁻¹^(5^6) = 26831117755476397635969818 :=
      state_next (j:=5) state_5 (block_5 0) (by decide +kernel) (by decide +kernel)

    have state_7 : F (7) = 62243115878813885075651463 ∧ (2:ZMod (5^37))⁻¹^(5^7) = 16392039676745161280579193 :=
      state_next (j:=6) state_6 (block_6 0) (by decide +kernel) (by decide +kernel)

    have state_8 : F (8) = 16179117313246354095393766 ∧ (2:ZMod (5^37))⁻¹^(5^8) = 12494962902404195568079193 :=
      state_next (j:=7) state_7 (block_7 0) (by decide +kernel) (by decide +kernel)

    have state_9 : F (9) = 16239629084456595985286037 ∧ (2:ZMod (5^37))⁻¹^(5^9) = 16160717138167781312219818 :=
      state_next (j:=8) state_8 (block_8 0) (by decide +kernel) (by decide +kernel)

    have state_10 : F (10) = 51554095377865371318668734 ∧ (2:ZMod (5^37))⁻¹^(5^10) = 7368241971389396556360443 :=
      state_next (j:=9) state_9 (block_9 0) (by decide +kernel) (by decide +kernel)

    have state_11 : F (11) = 25632072540667668995182713 ∧ (2:ZMod (5^37))⁻¹^(5^11) = 18226853527061986937219818 :=
      state_next (j:=10) state_10 (block_10 0) (by decide +kernel) (by decide +kernel)

    have state_12 : F (12) = 67261363751297212323909391 ∧ (2:ZMod (5^37))⁻¹^(5^12) = 62824540464398632689172943 :=
      state_next (j:=11) state_11 (block_11 0) (by decide +kernel) (by decide +kernel)

    have state_13 : F (13) = 36257337743701292430598537 ∧ (2:ZMod (5^37))⁻¹^(5^13) = 28876788897057355833704193 :=
      state_next (j:=12) state_12 (block_12 0) (by decide +kernel) (by decide +kernel)

    have state_14 : F (14) = 610849628543988847965609 ∧ (2:ZMod (5^37))⁻¹^(5^14) = 56854803616655903196985443 :=
      state_next (j:=13) state_13 (block_13 0) (by decide +kernel) (by decide +kernel)

    have state_15 : F (15) = 38650019571303340137760838 ∧ (2:ZMod (5^37))⁻¹^(5^15) = 46493861193873798704797943 :=
      state_next (j:=14) state_14 (block_14 0) (by decide +kernel) (by decide +kernel)

    have state_16 : F (16) = 16549537303820299482112516 ∧ (2:ZMod (5^37))⁻¹^(5^16) = 21911707935973713255579193 :=
      state_next (j:=15) state_15 (block_15 0) (by decide +kernel) (by decide +kernel)

    have state_17 : F (17) = 45974548558753575145442287 ∧ (2:ZMod (5^37))⁻¹^(5^17) = 70247880053894398070032318 :=
      state_next (j:=16) state_16 (block_16 0) (by decide +kernel) (by decide +kernel)

    have state_18 : F (18) = 1661889717425275469059359 ∧ (2:ZMod (5^37))⁻¹^(5^18) = 9248903893467304564172943 :=
      state_next (j:=17) state_17 (block_17 0) (by decide +kernel) (by decide +kernel)

    have state_19 : F (19) = 10139076871292506397526463 ∧ (2:ZMod (5^37))⁻¹^(5^19) = 68051903800503132200891693 :=
      state_next (j:=18) state_18 (block_18 0) (by decide +kernel) (by decide +kernel)

    have state_20 : F (20) = 8713722059174608564143766 ∧ (2:ZMod (5^37))⁻¹^(5^20) = 71028598768345234251672943 :=
      state_next (j:=19) state_19 (block_19 0) (by decide +kernel) (by decide +kernel)

    have state_21 : F (21) = 42211810214240635692317287 ∧ (2:ZMod (5^37))⁻¹^(5^21) = 13152497465721485472376068 :=
      state_next (j:=20) state_20 (block_20 0) (by decide +kernel) (by decide +kernel)

    have state_22 : F (22) = 22934288093165326738590609 ∧ (2:ZMod (5^37))⁻¹^(5^22) = 14810295519939777708704193 :=
      state_next (j:=21) state_21 (block_21 0) (by decide +kernel) (by decide +kernel)

    have state_23 : F (23) = 31447959342281733692448338 ∧ (2:ZMod (5^37))⁻¹^(5^23) = 23099285791031238890344818 :=
      state_next (j:=22) state_22 (block_22 0) (by decide +kernel) (by decide +kernel)

    have state_24 : F (24) = 58980371800347399091487516 ∧ (2:ZMod (5^37))⁻¹^(5^24) = 64544237146488544798547943 :=
      state_next (j:=23) state_23 (block_23 0) (by decide +kernel) (by decide +kernel)

    have state_25 : F (25) = 18806781432349766551692287 ∧ (2:ZMod (5^37))⁻¹^(5^25) = 53490265498272297239954193 :=
      state_next (j:=24) state_24 (block_24 0) (by decide +kernel) (by decide +kernel)

    have state_26 : F (26) = 3180838975027967119449984 ∧ (2:ZMod (5^37))⁻¹^(5^26) = 70979983399025318480188568 :=
      state_next (j:=25) state_25 (block_25 0) (by decide +kernel) (by decide +kernel)

    have state_27 : F (27) = 34497069754879389942448338 ∧ (2:ZMod (5^37))⁻¹^(5^27) = 12909420619121906614954193 :=
      state_next (j:=26) state_26 (block_26 0) (by decide +kernel) (by decide +kernel)

    have state_28 : F (28) = 43499566760941576337581266 ∧ (2:ZMod (5^37))⁻¹^(5^28) = 13594911286941883421594818 :=
      state_next (j:=27) state_27 (block_27 0) (by decide +kernel) (by decide +kernel)

    have state_29 : F (29) = 15338597259242619334895412 ∧ (2:ZMod (5^37))⁻¹^(5^29) = 17022364626041767454797943 :=
      state_next (j:=28) state_28 (block_28 0) (by decide +kernel) (by decide +kernel)

    have state_30 : F (30) = 26403084251002240801090609 ∧ (2:ZMod (5^37))⁻¹^(5^30) = 34159631321541187620813568 :=
      state_next (j:=29) state_29 (block_29 0) (by decide +kernel) (by decide +kernel)

    have state_31 : F (31) = 48442097940723811329167088 ∧ (2:ZMod (5^37))⁻¹^(5^31) = 47086388657204029417688568 :=
      state_next (j:=30) state_30 (block_30 0) (by decide +kernel) (by decide +kernel)

    have state_32 : F (32) = 45020043996258806562190641 ∧ (2:ZMod (5^37))⁻¹^(5^32) = 38960599193683979368860443 :=
      state_next (j:=31) state_31 (block_31 0) (by decide +kernel) (by decide +kernel)

    have state_33 : F (33) = 30510773322303379832942287 ∧ (2:ZMod (5^37))⁻¹^(5^33) = 71091228017917988157922943 :=
      state_next (j:=32) state_32 (block_32 0) (by decide +kernel) (by decide +kernel)

    have state_34 : F (34) = 61150729509905744219059359 ∧ (2:ZMod (5^37))⁻¹^(5^34) = 13465643713585255003626068 :=
      state_next (j:=33) state_33 (block_33 0) (by decide +kernel) (by decide +kernel)

    have state_35 : F (35) = 32935577073376094044010838 ∧ (2:ZMod (5^37))⁻¹^(5^35) = 16376026759258625364954193 :=
      state_next (j:=34) state_34 (block_34 0) (by decide +kernel) (by decide +kernel)

    have state_36 : F (36) = 49443826225682329511409391 ∧ (2:ZMod (5^37))⁻¹^(5^36) = 30927941987625477171594818 :=
      state_next (j:=35) state_35 (block_35 0) (by decide +kernel) (by decide +kernel)

    have late_states {j : ℕ} (hj : 36 ≤ j) :
        (F (j) = 49443826225682329511409391 ∨ F (j) = 54375914296825016795832912 ∨ F (j) = 23315749916151929521793734 ∨ F (j) = 18383661845009242237370213) ∧ (2:ZMod (5^37))⁻¹^(5^j) = 30927941987625477171594818 := by
      induction j, hj using Nat.le_induction with
      | base => exact ⟨Or.inl state_36.1,state_36.2⟩
      | succ j hj ih =>
        obtain ⟨hs,hb⟩ := ih
        rcases hs with h | h | h | h
        · have hnew := state_step (j:=j) h hb (block_end (by omega : 35≤j) 0)
          exact ⟨Or.inr (Or.inl (hnew.1.trans (by decide +kernel))),hnew.2.trans (by decide +kernel)⟩
        · have hnew := state_step (j:=j) h hb (block_end (by omega : 35≤j) 0)
          exact ⟨Or.inr (Or.inr (Or.inl (hnew.1.trans (by decide +kernel)))),hnew.2.trans (by decide +kernel)⟩
        · have hnew := state_step (j:=j) h hb (block_end (by omega : 35≤j) 0)
          exact ⟨Or.inr (Or.inr (Or.inr (hnew.1.trans (by decide +kernel)))),hnew.2.trans (by decide +kernel)⟩
        · have hnew := state_step (j:=j) h hb (block_end (by omega : 35≤j) 0)
          exact ⟨Or.inl (hnew.1.trans (by decide +kernel)),hnew.2.trans (by decide +kernel)⟩

    have classification (j : ℕ) :
        OMA.S_mo_393993.ZerosAtEnd (5^j) ↔ j≤1 := by
      by_cases h4 : 4≤j
      · have hn : 4*(4*37+1)≤5^j := (by decide : 4*(4*37+1)≤5^4).trans
          (Nat.pow_le_pow_right (by decide) h4)
        have kill (u r d : ℕ) (h : F (j) = (u:ℕ))
            (he : (u:ZMod (5^37))=r) (hr : r<10^37) (hd2 : 2^37∣r) (hd : d<37)
            (hh : r/10^d%10=0) : ¬OMA.S_mo_393993.ZerosAtEnd (5^j) :=
          hFkill j r d (h.trans he) hr hd2 hd hh hn
        suffices ¬OMA.S_mo_393993.ZerosAtEnd (5^j) by
          exact iff_of_false this (by omega)
        by_cases h36 : j<36
        · interval_cases j
          · exact kill 11298353343283839099181266 4383573517418356160192763514392150016 2 (state_4.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 23478304832998867215114162 7371988442487977107852522487820582912 6 (state_5.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 59160817443806186165387484 3071149756783641357004124179329449984 16 (state_6.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 62243115878813885075651463 5601082485362382639921420238835417088 2 (state_7.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 16179117313246354095393766 6874176784347390937558035477630550016 2 (state_8.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 16239629084456595985286037 245386243275657453531611594764582912 36 (state_9.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 51554095377865371318668734 3837847010778827395667973098369449984 11 (state_10.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 25632072540667668995182713 3887529406591222834142592565235417088 2 (state_11.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 67261363751297212323909391 4521798040799653473681812501630550016 2 (state_12.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 36257337743701292430598537 3316437210560129974002303434764582912 13 (state_13.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 610849628543988847965609 7633119586026324792573547498369449984 26 (state_14.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 38650019571303340137760838 1298232471056049822375296565235417088 2 (state_15.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 16549537303820299482112516 2216492063324218551042452501630550016 2 (state_16.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 45974548558753575145442287 7188081488539455268184703434764582912 13 (state_17.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 1661889717425275469059359 4948016702912197858557547498369449984 28 (state_18.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 10139076871292506397526463 2494069521572917467815296565235417088 2 (state_19.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 8713722059174608564143766 7939264141177391901442452501630550016 2 (state_20.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 42211810214240635692317287 5452155225617764132184703434764582912 13 (state_21.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 22934288093165326738590609 9878714756582864098557547498369449984 20 (state_22.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 31447959342281733692448338 5892226094615195867815296565235417088 2 (state_23.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 58980371800347399091487516 4671812799410735901442452501630550016 2 (state_24.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 18806781432349766551692287 498240899560804132184703434764582912 13 (state_25.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 3180838975027967119449984 1564998300749264098557547498369449984 20 (state_26.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 34497069754879389942448338 9740084246039195867815296565235417088 2 (state_27.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 43499566760941576337581266 2514724195250735901442452501630550016 2 (state_28.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 15338597259242619334895412 4301787113960804132184703434764582912 13 (state_29.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 26403084251002240801090609 5492213404749264098557547498369449984 20 (state_30.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 48442097940723811329167088 4651428886039195867815296565235417088 2 (state_31.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 45020043996258806562190641 4334346595250735901442452501630550016 2 (state_32.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 30510773322303379832942287 1518171113960804132184703434764582912 13 (state_33.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 61150729509905744219059359 1653404749264098557547498369449984 20 (state_34.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 32935577073376094044010838 4241828886039195867815296565235417088 2 (state_35.1) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        · rcases (late_states (by omega : 36≤j)).1 with h | h | h | h
          · exact kill 49443826225682329511409391 1598346595250735901442452501630550016 2 h (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 54375914296825016795832912 1758171113960804132184703434764582912 13 h (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 23315749916151929521793734 8401653404749264098557547498369449984 20 h (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
          · exact kill 18383661845009242237370213 8241828886039195867815296565235417088 2 h (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      · interval_cases j <;> unfold OMA.S_mo_393993.ZerosAtEnd <;> decide +kernel
    exact classification J

  refine logic (fun j => corrected 37 (5^j).factorial) ?_ ?_ ?_
  · decide +kernel
  · intro j
    rw [pow_succ' (5:ℕ) j]
    have h := corrected_scale 37 (5^j)
    simpa only [corrected,unitBlock, mul_zero, zero_add] using h
  · intro j r d he hr ht hd hh hn
    exact low_digits_exclude (k:=37) (n:=5^j) he hr ht hd hh hn

end Fact393

namespace Fact393
open OMA.S_mo_393993

theorem first_exact {n : ℕ} (hn : n ≤ 40) :
    ZerosAtEnd n ↔ n ∈ ([0,1,2,3,4,5,6,9,10,11,14,31,40] : List ℕ) := by
  interval_cases n <;> unfold ZerosAtEnd <;> decide +kernel

end Fact393

open OMA.S_mo_393993
namespace Fact393

private theorem factor_exact {x z m : ℕ} (hx : 0<x) (he : x=10^z*m) (hu : m%10≠0) :
    padicValNat 10 x=z ∧ x/10^z=m := by
  have hzp : 0<(10:ℕ)^z := by positivity
  have hz_le : z ≤ padicValNat 10 x :=
    (padicValNat_dvd_iff_le_of_ne_one (by decide : (10:ℕ)≠1) hx.ne').mp ⟨m,he⟩
  have hn : ¬ 10^(z+1) ∣ x := by
    rintro ⟨w,hw⟩
    have hm : m=10*w := by
      apply Nat.eq_of_mul_eq_mul_left hzp
      rw [←he,hw,pow_succ,mul_assoc]
    simp [hm] at hu
  have hz_lt := mt (padicValNat_dvd_iff_le_of_ne_one (p:=10) (n:=z+1) (by decide) hx.ne').mpr hn
  exact ⟨by omega,by rw [he,Nat.mul_div_cancel_left _ hzp]⟩

private theorem zero_digit {x j : ℕ} (hp : 0<x/10^j) (hz : x/10^j%10=0) :
    0 ∈ Nat.digits 10 x := by
  induction j generalizing x with
  | zero =>
    simp only [pow_zero,Nat.div_one] at hp hz
    rw [Nat.digits_eq_cons_digits_div (by decide) hp.ne',hz]
    simp
  | succ j ih =>
    have hne : x≠0 := by rintro rfl; simp at hp
    rw [Nat.digits_eq_cons_digits_div (by decide) hne]
    apply List.mem_cons_of_mem
    apply ih
    · simpa only [Nat.div_div_eq_div_mul, ←pow_succ'] using hp
    · simpa only [Nat.div_div_eq_div_mul, ←pow_succ'] using hz

private theorem suffix_fails {n z s p j K : ℕ}
    (he : n.factorial=10^z*s) (hr : s%(10^K)=p) (hj : j<K)
    (hu : p%10≠0) (hp : 0<p/10^j) (hz : p/10^j%10=0) : ¬ZerosAtEnd n := by
  have hD : 10^(j+1) ∣ (10:ℕ)^K := pow_dvd_pow _ (by omega)
  have hD1 : 10 ∣ (10:ℕ)^K := dvd_pow_self _ (by omega)
  have hmu : s%10=p%10 := by rw [←hr,Nat.mod_mod_of_dvd _ hD1]
  obtain ⟨hval,hrest⟩ := factor_exact (Nat.factorial_pos n) he (hmu ▸ hu)
  have hmd : s/10^j%10=p/10^j%10 := by
    rw [←Nat.mod_mul_right_div_self, ←Nat.mod_mul_right_div_self, ←hr, ←pow_succ,
      Nat.mod_mod_of_dvd _ hD]
  have hle : p ≤ s := by rw [←hr]; exact Nat.mod_le _ _
  intro h
  apply h
  rw [hval,hrest]
  exact zero_digit (hp.trans_le (Nat.div_le_div_right hle)) (hmd.trans hz)

theorem reserve_step {n K e r a b u j : ℕ}
    (hi : ∃ z H : ℕ, n.factorial=10^z*(2^e*H) ∧ H%(10^K)=r)
    (hfac : n+1=2^a*5^b*u) (hb : b≤e+a)
    (p : ℕ) (hpdef : p=(2^(e+a-b) * ((r*u)%(10^K)))%(10^K))
    (hj : j<K) (hu : p%10≠0) (hp : 0<p/10^j) (hz : p/10^j%10=0) :
    (∃ z H : ℕ, (n+1).factorial=10^z*(2^(e+a-b)*H) ∧ H%(10^K)=(r*u)%(10^K)) ∧
    ¬ZerosAtEnd (n+1) := by
  obtain ⟨z,H,h1,h2⟩ := hi
  have heq : (n+1).factorial=10^(z+b)*(2^(e+a-b)*(H*u)) := calc
    _ = (2^a*5^b*u)*(10^z*(2^e*H)) := by rw [Nat.factorial_succ,h1,hfac]
    _ = 10^z*(5^b*2^(e+a))*(H*u) := by rw [pow_add]; ring
    _ = _ := by
      conv_lhs => rw [←Nat.add_sub_of_le hb]
      rw [show (10:ℕ)^(z+b)=10^z*(2*5)^b by rw [pow_add],mul_pow]
      rw [pow_add]
      ring
  have hm : (H*u)%(10^K)=(r*u)%(10^K) := by rw [←h2,Nat.mod_mul_mod]
  constructor
  · exact ⟨z+b,H*u,heq,hm⟩
  · apply suffix_fails heq _ hj hu hp hz
    rw [hpdef,←hm,Nat.mul_mod_mod]

end Fact393

open OMA.S_mo_393993
namespace Fact393

/-- Check a supplied run of decimal-zero positions while carrying a small reserve of twos. -/
private theorem run_of_test (step : ℕ → ℕ → ℕ × ℕ × ℕ) (n K e r L e' r' bits : ℕ)
    (hi : ∃ z H : ℕ, n.factorial=10^z*(2^e*H) ∧ H%(10^K)=r)
    (check :
      let run := Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun (_ e r _ : ℕ) => e==e' && r==r')
        (fun _ rec n e r bits =>
          let (a,b,u) := step (n+1) e
          let f := e+a-b
          let s := (r*u)%(10^K)
          let p := (2^f*s)%(10^K)
          let j := bits%128
          decide ((n+1=2^a*5^b*u) ∧ b≤e+a ∧ j<K ∧ p%10≠0 ∧
              0<p/10^j ∧ p/10^j%10=0) && rec (n+1) f s (bits/128)) L
      run n e r bits=true) :
    (∃ z H : ℕ, (n+L).factorial=10^z*(2^e'*H) ∧ H%(10^K)=r') ∧
    ∀ m : ℕ, n < m → m ≤ n+L → ¬ZerosAtEnd m := by
  induction L generalizing n e r bits with
  | zero =>
    change (e==e' && r==r')=true at check
    simp only [Bool.and_eq_true, beq_iff_eq] at check
    obtain ⟨rfl,rfl⟩ := check
    exact ⟨by simpa using hi,by omega⟩
  | succ L ih =>
    dsimp only at check
    have hc := Bool.and_eq_true_iff.mp check
    simp only [decide_eq_true_eq] at hc
    obtain ⟨⟨hfac,hb,hj,hu,hp,hz⟩,hnext⟩ := hc
    obtain ⟨hentry,hone⟩ := reserve_step hi hfac hb _ rfl hj hu hp hz
    obtain ⟨hend,hall⟩ := ih _ _ _ _ hentry hnext
    constructor
    · simpa only [show n+(L+1)=(n+1)+L by omega] using hend
    · intro m hm hh
      rcases eq_or_lt_of_le (show n+1 ≤ m by omega) with h|h
      · exact h ▸ hone
      · exact hall m h (by omega)

theorem certified_run (n K e r L e' r' bits : ℕ)
    (hi : ∃ z H : ℕ, n.factorial=10^z*(2^e*H) ∧ H%(10^K)=r)
    (check :
      let step (i e : ℕ) :=
        let b := if i%5 ≠ 0 then 0 else if i%25 ≠ 0 then 1 else if i%125 ≠ 0 then 2 else
          if i%625 ≠ 0 then 3 else if i%3125 ≠ 0 then 4 else if i%15625 ≠ 0 then 5 else
          if i%78125 ≠ 0 then 6 else if i%390625 ≠ 0 then 7 else 8
        let a := if e<16 ∧ i%2=0 then 1 else 0
        (a,b,i/(2^a*5^b))
      let run := Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun (_ e r _ : ℕ) => e==e' && r==r')
        (fun _ rec n e r bits =>
          let (a,b,u) := step (n+1) e
          let f := e+a-b
          let s := (r*u)%(10^K)
          let p := (2^f*s)%(10^K)
          let j := bits%128
          decide ((n+1=2^a*5^b*u) ∧ b≤e+a ∧ j<K ∧ p%10≠0 ∧
              0<p/10^j ∧ p/10^j%10=0) && rec (n+1) f s (bits/128)) L
      run n e r bits=true) :
    (∃ z H : ℕ, (n+L).factorial=10^z*(2^e'*H) ∧ H%(10^K)=r') ∧
    ∀ m : ℕ, n < m → m ≤ n+L → ¬ZerosAtEnd m := by
  let step (i e : ℕ) :=
        let b := if i%5 ≠ 0 then 0 else if i%25 ≠ 0 then 1 else if i%125 ≠ 0 then 2 else
          if i%625 ≠ 0 then 3 else if i%3125 ≠ 0 then 4 else if i%15625 ≠ 0 then 5 else
          if i%78125 ≠ 0 then 6 else if i%390625 ≠ 0 then 7 else 8
        let a := if e<16 ∧ i%2=0 then 1 else 0
        (a,b,i/(2^a*5^b))
  exact run_of_test step n K e r L e' r' bits hi check

end Fact393
open OMA.S_mo_393993
namespace Fact393
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span0_6 (h : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952) :
    (∃ z H : ℕ, (1540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=69247804487672347832188403924773802774958495445040345423877492679298384542315382920202025675012349952234432549957402624) ∧
    ∀ m : ℕ, 40 < m → m ≤ 1540 → ¬ZerosAtEnd m := by
  let R1 : ℕ := 547227799980958260838027370259410458230756510258265234590682345309057120521585364754748280760509726232635038553207734272
  obtain ⟨h1,p0⟩ := certified_run 40 120 16 12449879199949611424951343835389952 250 15 R1 4008908499695745903441301086405450151798352112559555695822913307720040146671615524522293659061577924006520173807125758486482903933615866012183493033426459928986866772518368507384066448159785130652138862433796019631501287485743175532535521722581689844527559764628581913080278097094018582633592346580401798494026099718838822357711121845057961140241991831952524912892778699169984156844002369830026950212255533005813858492426938977051919051280580589505147163283876164368781198536209042682851594471387540961327816634713411774695433 h (by decide +kernel)
  let R2 : ℕ := 483068211814345235697859265554485148859896503055553370833117165168146534246288914188160042606994134513066945020507979776
  obtain ⟨h2,p1⟩ := certified_run 290 120 15 R1 250 15 R2 5000695352961116077763700049275721121848357341925618586562058823096712821274488081183259288854121072060291410590945934536129930986285098746038902084641120207803551253500864204462744005497657059919246310972038420239554104048255613049187480033817445901554944229494755473453632917781653219439373181804750536068814969470501160728325252330252458264966437556314088602454792484121123853332307693853153306241679839914141910770108665685905733243496854150629466333768110264548732486096490424672616833117059118632235680065843064016667408 h1 (by decide +kernel)
  let R3 : ℕ := 836370934073661661826581808553464138513692576780453551584669521266939972897109321672551432592164605175266687832977047552
  obtain ⟨h3,p2⟩ := certified_run 540 120 15 R2 250 15 R3 5980559711816118767226619260941714546472330080094625491191051199827990098546626049222635317631907268209535485091248156812663446461057482655990967863470470240646163579820391118714623913527286623221435676573758419176572192713584228559717118746886542028667003389457478277874569075708440594452570609068976302757621719799527177122216779411903791969804025210105424957305807549841822751105967471174043862103324015607455154134658164172159484582562649254221599917854787907380506774836273787351762448294103897581707790002937864258767505 h2 (by decide +kernel)
  let R4 : ℕ := 286650629044516601074094408408556971793037654114993574648506998655102728170423659093538468264830912435120786855121911808
  obtain ⟨h4,p3⟩ := certified_run 790 120 15 R3 250 15 R4 3528597403673355633427029855574459989971586678790867135935306016326996012052931124572456909293991543331169229458251710519041021320756170282142017746072106491391239224007678277875178717918653888989359279999772719276850175771949519486566135964916831661779877594336225419340447780409074308252742766238850012539472399169677128576248025140573140814971874618660021536778206516304614210643433575479591438468004363410430470079918299583031864052566694361426040673883049012493126544954784200732753610309423118862468160638858878850733329 h3 (by decide +kernel)
  let R5 : ℕ := 251420247887550656536565723929515785741710914549387731494239458707918986362026543354435848220043119859344785266073141248
  obtain ⟨h5,p4⟩ := certified_run 1040 120 15 R4 250 15 R5 9466248818457233295858781264424978078810609151135555573290990174380865737425305980291590496054138856701223125877803081845381937195955861942803680093430249660585061375380312100975817303014051653090526941449542884938797082245107292636631356850468217752460213466339935387248970660274972434755291210197176344469002452861275877224877020183446477666791072167476265855225721507350952340530635301392029206517845008758321002874527565807211188654117675263569098390718696180828007779902021713326096080499488928262274375918374963793396737 h4 (by decide +kernel)
  let R6 : ℕ := 69247804487672347832188403924773802774958495445040345423877492679298384542315382920202025675012349952234432549957402624
  obtain ⟨h6,p5⟩ := certified_run 1290 120 15 R5 250 15 R6 4961934497204347881530291454325835098010842621444992946830454300406544113910365903013811464635384008060883073036286899356505849490471671032195719524119470841580980032268502195212551701826026465550197052560698203736302495250378343895057773912863782441193913558690148263056426581978255956065786568690184525834874529729087474162670251794590328687686824743030493661040937916565063418968413512869135796057897853918811652304071242807456145447776509385588699251787461712988276932590547941450991717020740403438723952769922754419179650 h5 (by decide +kernel)
  refine ⟨h6,?_⟩
  intro m hm hh
  by_cases hx0 : m ≤ 290
  · exact p0 m (by omega) hx0
  by_cases hx1 : m ≤ 540
  · exact p1 m (by omega) hx1
  by_cases hx2 : m ≤ 790
  · exact p2 m (by omega) hx2
  by_cases hx3 : m ≤ 1040
  · exact p3 m (by omega) hx3
  by_cases hx4 : m ≤ 1290
  · exact p4 m (by omega) hx4
  exact p5 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span6_12 (h : ∃ z H : ℕ, (1540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=69247804487672347832188403924773802774958495445040345423877492679298384542315382920202025675012349952234432549957402624) :
    (∃ z H : ℕ, (3040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=621361779735508938333267871243261995601190371955090932786707051106534012040244436213603241730760198154990014955587108864) ∧
    ∀ m : ℕ, 1540 < m → m ≤ 3040 → ¬ZerosAtEnd m := by
  let R7 : ℕ := 654999850775698923057469201046186643276643374462968766040900453179167853153379284672557289103404728947388053950312742912
  obtain ⟨h7,p6⟩ := certified_run 1540 120 15 69247804487672347832188403924773802774958495445040345423877492679298384542315382920202025675012349952234432549957402624 250 15 R7 1491528364754063295334267684613102450680244090331766617165248379628369586987018557621424282827269223197374820669112368239527625027023585140653537311456645535109983087647904215489715323561947003037334923515038534324286282006508270127201904016316686683660215431949060800564632235053051150399657200813283435612046396409101727630946742971924090095787734157899958166628656592008738634784829412798947000148341993256011690640038274758893443017092415000352435449181032221750314896854155869526935089605274032246955918011885070196146307 h (by decide +kernel)
  let R8 : ℕ := 905097739052118917316763741850418409488811732147446506242104401375344502927403816595245464959027123015645066808201838592
  obtain ⟨h8,p7⟩ := certified_run 1790 120 15 R7 250 15 R8 13409460948074288158033431991716231371853002086177499441415333965600330002974705641643085054360883563020924372675712352019973414676392475393142442082979392952493416374828810388645989154549515239135843827050884552065643168661659183508436855080070464805731139148070456501235331715583207153648216121876356269583453146715748863234795295652596536103581533661394683385555009839317387931578090494267703967739866261275248025206231979693706997310093529654360947069329975786157026484310277111873901083787318627238774195435076510109778306 h7 (by decide +kernel)
  let R9 : ℕ := 151179923636053741610656019858304536890450220499548221204168338573167592876392759706797620660916245963935670600065875968
  obtain ⟨h9,p8⟩ := certified_run 2040 120 15 R8 250 15 R9 8486261522911352893199859111746511389642036092904539650580670353573583524945527768034549098707105518543346606667447306983363547486200637566753462731321850285898903299087034152109537471792884848081342362008412249015340892871097430463361628451838548228161702349555625448664307483054791135913496315776265320422352676797397345417205056459820399018654615585210005660279104656631035223901023915329870626559219002673852408565694375959901005722563218525127793062675428144076480517883371685869608899822119113838399001836559023139439235 h8 (by decide +kernel)
  let R10 : ℕ := 678199580488141670770563112627990762023144494621705714361583763382959442642835238794124333940046141180310150440242118656
  obtain ⟨h10,p9⟩ := certified_run 2290 120 15 R9 250 15 R10 562071908896511232700096501251908523417895153938890237613393668470776564581236191101796828682947086702283394785882501900050002859757547305393015713185661893048226829564699324787207346635269386270289502398714403296490280239766124124121105839260948003749176397680715853159843763159086390066492564496621018593453717101403593806860602988335008296605634340386930281230594415424375723770780597343286419103579154291490481628188744033467333817892303497387488597898172378304198689487614171916845154396583714368472547623596648533344643 h9 (by decide +kernel)
  let R11 : ℕ := 152034335749555517904310428673693850654120617351969983909557812570606149070449475375925195871144407972199604133348507648
  obtain ⟨h11,p10⟩ := certified_run 2540 120 15 R10 250 15 R11 2049425842449534413458987481618711340592026177471431782171692043855882582814429250848938081395191743462647328368846672454032517648056563997909277581972522393853321462783645572364323562753822368500113275143604226224643646471494958485066275948716493400183711221967349513659200102873728507705472444749169641803271398158252201272451956665516212402145540068745664275540406078402580074399696301052303085880340871763335295764855805147028540946712666615270785199138958382997406286184269355067483520253980292140903065475911732466697223 h10 (by decide +kernel)
  let R12 : ℕ := 621361779735508938333267871243261995601190371955090932786707051106534012040244436213603241730760198154990014955587108864
  obtain ⟨h12,p11⟩ := certified_run 2790 120 15 R11 250 15 R12 7057681805882724218473453647596352525675017186693482907014997657281730896246395819786646955123253202928148197449115840512866917908421861094179476302628249053753937172196339812369431123992476646842220942874903395808448380705147498719681946802892423109839904527733543752445954368689507685199296583293188026936646804624474142209439129064503758786869082009726349068712507249551740735853266038406786244759532177741428727520785630231745458286474426282395198527726621530136689413280816413986308460029268329684480399414504749177012360 h11 (by decide +kernel)
  refine ⟨h12,?_⟩
  intro m hm hh
  by_cases hx6 : m ≤ 1790
  · exact p6 m (by omega) hx6
  by_cases hx7 : m ≤ 2040
  · exact p7 m (by omega) hx7
  by_cases hx8 : m ≤ 2290
  · exact p8 m (by omega) hx8
  by_cases hx9 : m ≤ 2540
  · exact p9 m (by omega) hx9
  by_cases hx10 : m ≤ 2790
  · exact p10 m (by omega) hx10
  exact p11 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span0_12 (h : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952) :
    (∃ z H : ℕ, (3040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=621361779735508938333267871243261995601190371955090932786707051106534012040244436213603241730760198154990014955587108864) ∧
    ∀ m : ℕ, 40 < m → m ≤ 3040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span0_6 h
  obtain ⟨hend,hright⟩ := span6_12 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 1540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span12_18 (h : ∃ z H : ℕ, (3040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=621361779735508938333267871243261995601190371955090932786707051106534012040244436213603241730760198154990014955587108864) :
    (∃ z H : ℕ, (4540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=320764614566196572626288055530848345452375833874997119109222732017380371613060604743394293648584815344407423438991392768) ∧
    ∀ m : ℕ, 3040 < m → m ≤ 4540 → ¬ZerosAtEnd m := by
  let R13 : ℕ := 557973990935334696703386555777251746508598260275406515623590727210952107450725623620304134138738315112290768397474463744
  obtain ⟨h13,p12⟩ := certified_run 3040 120 15 621361779735508938333267871243261995601190371955090932786707051106534012040244436213603241730760198154990014955587108864 250 15 R13 12410021508557427477301327068994194962128326070025079960399501257588641864208430860271927902254778822584590933420102329637846611305638672860671844994919316991502589147667712891013965831045329371802030290876313727504300638082869909951433704272154924932724632350378421058357443520497996950867060388299876198077042153486994614338154921544223740837464596520252806838297019324980896442965772606916071459381827764201644776223011911069441985854003324838314394659708525453631178628556353899638694688176884432115572309695124504620401158 h (by decide +kernel)
  let R14 : ℕ := 717228946610967213132151055052538714976044160155438857596577461672651596422392931326928224291234208242186846461939941376
  obtain ⟨h14,p13⟩ := certified_run 3290 120 15 R13 250 15 R14 2037530999280269585280728478666375732789812364976069968371207083523192917144583666474614267615016128321960875788830412972936414992947332235523435642757026979224690169269045126295552969996650175028156449582433597659710715263680647887064355674792175558217008727687014856418817151450123224870344213309332530765693243936645128348149819858913589256595895340870566770478779304932912421103155649301869098417433998868214742186520043451573069221760424602454777469167982007677928076889162512382610848257635376508259607324057754272825602 h13 (by decide +kernel)
  let R15 : ℕ := 368798812430757560214399625353917634009292061040599985501954778218601988994378884593668753572063640336673117481581150208
  obtain ⟨h15,p14⟩ := certified_run 3540 120 15 R14 250 15 R15 2513784914424801616064407104733805370396271787420402283409632626839439506020297838667570762598548247047324582083354506525523363469451071721935071187498093763821820578905272140267253721573933491758486374982599193601388435120646422312290147100786096374963698172491716251688582569036199298302479674985987526085020936405024774183227187122340363705893207102496591099591647692734043440949322528430985354775704123187405571733357365615258354009766041121772062722523655859069209090863015387250632723117069800753142710356183790800847365 h14 (by decide +kernel)
  let R16 : ℕ := 392116411946015144250119047752248985158151395433026023346441936047998313481948772422643449809636488209060595144824193024
  obtain ⟨h16,p15⟩ := certified_run 3790 120 15 R15 250 15 R16 1491252237116870196626803183313028268882764548589688359460193442891815289002090708000685744149150297181104670659510855687607228491326332683319059609254686603979104490933168491329003864354141578228407967613055121308734967783379025725724647899456983656822890744776911655265279143507168833762492695238847320345940162097090352160764672522884291729380892258227820256988765655996599365997410429347529373940650885909345451110426964852900309970046921567029432814792039076783209943965428292105430387279253763233598768757777494238610689 h15 (by decide +kernel)
  let R17 : ℕ := 968934498529516818462321052965163811879469229799455396850933024925881178633079347843534218237967498509267223505012785152
  obtain ⟨h17,p16⟩ := certified_run 4040 120 15 R16 250 15 R17 1530166029180785730051936514537567815497406510060229463292654384707418903382951864464414528597308486001708070592675193138758468671638980935673916035836058610370422213464009912855703024669589921794445672281570853200367879289933804334315514763011993072662028971090376223260300913833645134696007049897637104543491184951225800689385904186440655657678565392956558590984429186893178169323330637294161313801799874016113395391250497850172375670239003586117055789136740207949303056758766747565764014021800407675258865697435236935499926 h16 (by decide +kernel)
  let R18 : ℕ := 320764614566196572626288055530848345452375833874997119109222732017380371613060604743394293648584815344407423438991392768
  obtain ⟨h18,p17⟩ := certified_run 4290 120 15 R17 250 15 R18 10922518646894935706159734757837315567290239441780968983951257079601331838930769282314862517924272329341497179816542831814878467818642434980165832364606357581892750092550942145589936534057851639318802160765930240473971732125038258943295871854778888438565965654534590696288306959041630028159592758086978564212407748685116894815454807792564409077617792467443599200514614436181915850559300215282604195419839512344826184708961264477191781785136001460127767273931296657432076264649087741483345306716947738037480161343587569893444359 h17 (by decide +kernel)
  refine ⟨h18,?_⟩
  intro m hm hh
  by_cases hx12 : m ≤ 3290
  · exact p12 m (by omega) hx12
  by_cases hx13 : m ≤ 3540
  · exact p13 m (by omega) hx13
  by_cases hx14 : m ≤ 3790
  · exact p14 m (by omega) hx14
  by_cases hx15 : m ≤ 4040
  · exact p15 m (by omega) hx15
  by_cases hx16 : m ≤ 4290
  · exact p16 m (by omega) hx16
  exact p17 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span18_25 (h : ∃ z H : ℕ, (4540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=320764614566196572626288055530848345452375833874997119109222732017380371613060604743394293648584815344407423438991392768) :
    (∃ z H : ℕ, (6290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152) ∧
    ∀ m : ℕ, 4540 < m → m ≤ 6290 → ¬ZerosAtEnd m := by
  let R19 : ℕ := 397468403678076692653418543615675707485382894609854922449447833005481571646666365211864709732666574851577785190996508672
  obtain ⟨h19,p18⟩ := certified_run 4540 120 15 320764614566196572626288055530848345452375833874997119109222732017380371613060604743394293648584815344407423438991392768 250 15 R19 1076937964126282320533246154156573979462110126478176091038072397964866232110384574104218976085230878057463560538879023211860503984167896364060996355431910759264044434604252047378050223728889798570630205055853759649655130916283398865451112505637699054505653238699814070845890429338872989194781657386246984687228296052520467703136146566388767532873732617230079426591219668504206698159436047442167875069639817220574354011679434079162711364055241380498273911632609637175783231938313430983066675768826204598073238894250865610213252 h (by decide +kernel)
  let R20 : ℕ := 169590993507890380900062796694183217233805957230148422363923212056880657347165671360810664909564267952240135013859852288
  obtain ⟨h20,p19⟩ := certified_run 4790 120 15 R19 250 15 R20 9440105532695260248637255104381991560837572427632235580165528339680558115201933885071532890662095748653593764068180935216860833062056944248335177681224631274416648794487813353468809676001254342802562549697892783674920041988555193247588120399175172466887776718966695166387084641051672046324378914304738019788114445916310624307688592793375265635817987686869004787633613429422304960559983168230860807778169360724365485561310039696009891809062226396992112346253087672337694964482015901650952358232257759411367148063246152949171083 h19 (by decide +kernel)
  let R21 : ℕ := 299878850823673571261291959507639104154328777862726497804421063710537697712366159544066439314761836298315593734028263424
  obtain ⟨h21,p20⟩ := certified_run 5040 120 15 R20 250 15 R21 9423826353673598814357626803619333024387551163305262452356577473704912843126131725699383405258291689565916488891259368629251044194651209484891252092190279444130000574409950636008088818641868596945128495584529678338201605626476029488867347888522280355166671926933429856579515046060477823660713474443059300531406966613611154172548545312823112613562513481696121948542637737140592718883483185790822021437765593896658076425699719288068820558707694290187409817731729297572037563438015840902977283540748013775906112932264933194793731 h20 (by decide +kernel)
  let R22 : ℕ := 700266879036789322469415453702928627704578996647290192872167756446618153382852169491617101766895250589924576798726684672
  obtain ⟨h22,p21⟩ := certified_run 5290 120 15 R21 250 15 R22 1046012930751210590867390048244458142480463548292565248836851796060824670816254816897660541259165154734235802549902380762258074190866360136960156967194425898417144952719079670807277610063902603587280582104778599881441732187597152186530461516245870092609830119304238800129194379426830164705604823364810546024731226592740263874804455204832958689664593297301358285889297753475162654792734162338209965882492662578552122438536835193815625969510923670625856345390778227266739472145855954408710618962428826339568780422903856659202179 h21 (by decide +kernel)
  let R23 : ℕ := 628934397993724690216072157155225071565842351882997682443427974206534639972484543526271212925054279019906971609895796736
  obtain ⟨h23,p22⟩ := certified_run 5540 120 15 R22 250 15 R23 5488387360667686445265581810089516492247608814504951987256709073207640355447437908367737581761686783239177794870370603145601169746737278708990891673086568697050934365253936591576811008787704387351958420542180129285411208779126044882860042044462543214982626402765772089497650407465232356684683269163784050213620930009106888520441175339269817889484515170955502388639576971668269540380299234968014377928133209978658455412791670776545124038460178909019370689545639139735974626172105941052930830824453584572500614453903026647287312 h22 (by decide +kernel)
  let R24 : ℕ := 174468740600002758735142038456838605160353902364412629146796051856440077916405095583957072297903293364063308806350700544
  obtain ⟨h24,p23⟩ := certified_run 5790 120 15 R23 250 15 R24 7982777556638239715163866113461687797941218818311123473841842031261391262193250724040838639760330507439547108484138211998401620346407700761322425293902065393750311393319668051969779923432982655820439848323979132258077429076514890810529789210300181448345111930024287041441673286652067837219213126083363825282646882611143169225263947247271963754759884044164506693678112822743245196534449168092999361745288865845940302098686212855965851891130509141163526566481735115035209344767033910065361342324387260458934313753442623357468946 h23 (by decide +kernel)
  let R25 : ℕ := 463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152
  obtain ⟨h25,p24⟩ := certified_run 6040 120 15 R24 250 15 R25 5000393226634407229283878689455693729101118108012277520516007668528294520902161106071257985603774432835595185532002153492964773181747976388378787800998266564849623137214352483328076648483041287051738463633537489655775969827724189481379885116774376274448288120745197109523764632691898348923617587840302297614119651914495021363169773971924617766238944837176415780950333531068883692500408377142747234861325354527993521529324882810718255542285038492175675782977983473391487584868207549094303680291649489524322097881721897211741444 h24 (by decide +kernel)
  refine ⟨h25,?_⟩
  intro m hm hh
  by_cases hx18 : m ≤ 4790
  · exact p18 m (by omega) hx18
  by_cases hx19 : m ≤ 5040
  · exact p19 m (by omega) hx19
  by_cases hx20 : m ≤ 5290
  · exact p20 m (by omega) hx20
  by_cases hx21 : m ≤ 5540
  · exact p21 m (by omega) hx21
  by_cases hx22 : m ≤ 5790
  · exact p22 m (by omega) hx22
  by_cases hx23 : m ≤ 6040
  · exact p23 m (by omega) hx23
  exact p24 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span12_25 (h : ∃ z H : ℕ, (3040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=621361779735508938333267871243261995601190371955090932786707051106534012040244436213603241730760198154990014955587108864) :
    (∃ z H : ℕ, (6290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152) ∧
    ∀ m : ℕ, 3040 < m → m ≤ 6290 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span12_18 h
  obtain ⟨hend,hright⟩ := span18_25 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 4540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span0_25 (h : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952) :
    (∃ z H : ℕ, (6290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152) ∧
    ∀ m : ℕ, 40 < m → m ≤ 6290 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span0_12 h
  obtain ⟨hend,hright⟩ := span12_25 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 3040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span25_31 (h : ∃ z H : ℕ, (6290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152) :
    (∃ z H : ℕ, (7790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=447462781164434193680054226284727828198206307240721752867312642829971077391380060485159179596525023087651374581459976192) ∧
    ∀ m : ℕ, 6290 < m → m ≤ 7790 → ¬ZerosAtEnd m := by
  let R26 : ℕ := 658880284615481884079642306418054821350286752900855313435347550074003002706013565630243702795571244218176333658441383936
  obtain ⟨h26,p25⟩ := certified_run 6290 120 15 463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152 250 15 R26 4969384266184079252655698440378120416115792817808869923968209743688404589695926789410297297193240937803632467212934567932952777068825049509259616867661226191102643506992268442389942897556398301259057479367243731260633724069036811732649108858734735238037727012281462934262928660544830095877194993800669633300641955765174436715502491802226255162839515087788359078715015481332511155964634323156596251467580368959386495144472170492656144228201883081876272981358617518217567505215842760392347594251224353838640805556632504642995859 h (by decide +kernel)
  let R27 : ℕ := 587388236588804873403805418815807605774600592360358421856974000632072275329278254232031372150930978303037814827214962688
  obtain ⟨h27,p26⟩ := certified_run 6540 120 15 R26 250 15 R27 1506956939365246892411009189059993665896076630261390116454937794353908977613564041950946359418321851745714328174740585865651122261118160358401095706043551501174574295798820016022668184343770999247097123334258005447762193198606317965651601476596487976135921713896933370150508849929610266417569222718847764807984411014752939334347734284786483839876587367692583272322162475550326678436896074583416796682359368676393437368980328222512825030687430306160564096239093818858899752425978052781156565678432280918292892654048571656521091 h26 (by decide +kernel)
  let R28 : ℕ := 233361016538698035892076689469741827371583616640833543382861299667552186863156553444835823046880489828593859679733415936
  obtain ⟨h28,p27⟩ := certified_run 6790 120 15 R27 250 15 R28 1526081924104256755652265934757534512116616882717122479302879769688235277402214649781468467508429354522779062583364377920189276158834350793146762301844822894626982346277330480852024658812239955786457966695857529115136342399128252998467363044216401250202988293352489938080860023674560769635065162133310429199983151301792611416893147179668427273861403374878744423422944673373929372135724121410988267738144885655542022318133344735945191633455229566276887119022519005403488819627806345033913312855149657736382660166218153466315664 h27 (by decide +kernel)
  let R29 : ℕ := 784967676963454188412339305820696278410040171598101205545866600789048065299827092039305841758154982064894518551635820544
  obtain ⟨h29,p28⟩ := certified_run 7040 120 15 R28 250 15 R29 4996524503268259938573911751092515407335737041042304913903859171198874254902727636405802664595622146367914659544227923402406100461533387211831596695125683749808836475623855118676728569806531137912258157212955836957689348145884347748765360583785106080231933678352651605267963030929400120756652408089149796951752782681831503225626093490773256079617725124848859058861907734862564874728382494512830085318464273056341239626373808266745110599292729590580217175233098173262812414649066436696746167688978069757624812953528758890939395 h28 (by decide +kernel)
  let R30 : ℕ := 141050947531110159175845373367161553518502357907786900651060816008813263895899079373743409510147247137634045550955331584
  obtain ⟨h30,p29⟩ := certified_run 7290 120 15 R29 250 15 R30 3520971554958306351390984715745395664710263134208257603043650116386161634713411966065127805297144048792787239852500002520020200404283229594074573797314583436023231656247992902604042090973661681814175477318990382657856959712077556570020488416782588151321249516079599423994369100326907257641435834106388440994815221299067638685771163589713745401748567215152612443273372229742244884548865871340175504828157371438772714826202215892707859359323742902755613374797902171268073478573223503072208447485164390446330641017389868766216836 h29 (by decide +kernel)
  let R31 : ℕ := 447462781164434193680054226284727828198206307240721752867312642829971077391380060485159179596525023087651374581459976192
  obtain ⟨h31,p30⟩ := certified_run 7540 120 15 R30 250 15 R31 4563171750203651747399382467730309206884427364452569139846448122649381661967661036004253586327125783494547760731983442234822597994711604798288920452972345564540747259216662277258856550054004851205245441948087231340860121800181721847183501759774052436907343626814387552195437093157693844355182846136816760960642486621995283399628552451973683601195649401823247905118928101870286535006009291005494432380800357355629821099375626121104523119925981314837392480738766589486482417355119380381001940438159570886080289289068897131218567 h30 (by decide +kernel)
  refine ⟨h31,?_⟩
  intro m hm hh
  by_cases hx25 : m ≤ 6540
  · exact p25 m (by omega) hx25
  by_cases hx26 : m ≤ 6790
  · exact p26 m (by omega) hx26
  by_cases hx27 : m ≤ 7040
  · exact p27 m (by omega) hx27
  by_cases hx28 : m ≤ 7290
  · exact p28 m (by omega) hx28
  by_cases hx29 : m ≤ 7540
  · exact p29 m (by omega) hx29
  exact p30 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span31_37 (h : ∃ z H : ℕ, (7790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=447462781164434193680054226284727828198206307240721752867312642829971077391380060485159179596525023087651374581459976192) :
    (∃ z H : ℕ, (9290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=768561924259763790362599598378945162019057361087237737435031305762041869901720537564190796946694626586296065606268485632) ∧
    ∀ m : ℕ, 7790 < m → m ≤ 9290 → ¬ZerosAtEnd m := by
  let R32 : ℕ := 917895675157299349749670356689574090286343257524598490843207426045724619100329082581567188556473750150593945419640733696
  obtain ⟨h32,p31⟩ := certified_run 7790 120 15 447462781164434193680054226284727828198206307240721752867312642829971077391380060485159179596525023087651374581459976192 250 15 R32 1526717607618993488371155217045282776446214241768602542285644853047249628579676006755271871065479348529165112793427509431364884663369838066434508562258118244967295631722338685154790123045944560960714956429956634079193273472505497927548593483378688462724781732369178335606663426433173407303562797510329765061440803284003525222866611651570169508011175570274046314047735418578033482207967315085336435662828016258073622913711182253595860231814040585265306010962166156327216799615426096467878022323551351291930715891913539847373445 h (by decide +kernel)
  let R33 : ℕ := 552309929161327835253166681628500197206209896126316949313015239337778504729275098794587587652018192636298777725874733056
  obtain ⟨h33,p32⟩ := certified_run 8040 120 15 R32 250 15 R33 674759904805759035771827271466426649092516503043144137563042457357921438886386757301124769318817523245404761250238311263829801871744369674875921618251640166675810052694231959951568121719598003112979532049703939441186686941383968794195418840133557814269421885191212946722103970172087673899034218207829515473985599415482395957920365931204963557845924188639760004783959527081066911780226560383134380387351806887122662224139175017692732523200657704573526922515198118085377259605321429797101833272832589149882684740066276538368520 h32 (by decide +kernel)
  let R34 : ℕ := 363405202891582521180287358136624846349359353554226202935281043042981268038607253677553346959531845000582441879180673024
  obtain ⟨h34,p33⟩ := certified_run 8290 120 15 R33 250 15 R34 1491343712530698571663489258126559645732346559024766818446575220105068867722227847161755196751778376966391275265262123532207719392341044587943002866244173081127850941611610542832127306930219205903166667620947076891823490987519250292815421556708125702807354059351440146457102111132944542112385920461180828406626968161875935165284710764082079289627237134605808564075066428810548659726233833302969640679525224921337743045847256636778459699965381268435645474976446460377254678589440955604726052396197002304803268355796258827457158 h33 (by decide +kernel)
  let R35 : ℕ := 996608997603388083703954838038190217596239910081454850695258986021124252366305025536371567106452252684682325148594864128
  obtain ⟨h35,p34⟩ := certified_run 8540 120 15 R34 250 15 R35 507489591335302001175239672984899795379530303234271076012485932000456934442885564203279913661824738290752346644279353063844591872717490366987181524516468926716705853259099125456389991066133515365233556907191101293561998730352912204864657300141311339589166362970878957591178593240023241659875916453520361836091339835680392144704076989077444705400959832120640030006734541079644998953698403521635809789037574717023434175598061804533691742580486020582274307270152798428216714539499953875272818650333324417088585135403965081583752 h34 (by decide +kernel)
  let R36 : ℕ := 689031628641478294948148316438801928982832486639309028051398124352825719955714440703020450450406076729660380155188609024
  obtain ⟨h36,p35⟩ := certified_run 8790 120 15 R35 250 15 R36 2978571665160408892888454491999903019437897697676199528522006002650933361963816040429117120083706163690498413067128464087322384198825374689946692726024337543572581234711416824321133930651851887540129467894622965778087849209703623515858010466466458059559390613747923948047831755475248832290321329628285684326588126556536428029423912219479495842306170067574396927650848238478086701430345745993459035959525012052695921608626027492319929643130924337828689849416457859722961037681214007359360522287102244204701314024993404282325401 h35 (by decide +kernel)
  let R37 : ℕ := 768561924259763790362599598378945162019057361087237737435031305762041869901720537564190796946694626586296065606268485632
  obtain ⟨h37,p36⟩ := certified_run 9040 120 15 R36 250 15 R37 5043118305887043291839654914005605932139881950183270320801049707788283454132487802150048222883087299508284283843647632576871775856565206050527184053063194097262780924874918296720618770186844179215769645878336338880237763005054606882939922426907197056868551822470468610033010647426655370501082339381526979112756903895436004155294631530322569505179336663471226152666150166247970621509164054504914846551277676338142998890609238816289521223000415519039035612873844285579401057270335889022637622798207731887057782628035167044829323 h36 (by decide +kernel)
  refine ⟨h37,?_⟩
  intro m hm hh
  by_cases hx31 : m ≤ 8040
  · exact p31 m (by omega) hx31
  by_cases hx32 : m ≤ 8290
  · exact p32 m (by omega) hx32
  by_cases hx33 : m ≤ 8540
  · exact p33 m (by omega) hx33
  by_cases hx34 : m ≤ 8790
  · exact p34 m (by omega) hx34
  by_cases hx35 : m ≤ 9040
  · exact p35 m (by omega) hx35
  exact p36 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span25_37 (h : ∃ z H : ℕ, (6290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152) :
    (∃ z H : ℕ, (9290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=768561924259763790362599598378945162019057361087237737435031305762041869901720537564190796946694626586296065606268485632) ∧
    ∀ m : ℕ, 6290 < m → m ≤ 9290 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span25_31 h
  obtain ⟨hend,hright⟩ := span31_37 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 7790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span37_43 (h : ∃ z H : ℕ, (9290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=768561924259763790362599598378945162019057361087237737435031305762041869901720537564190796946694626586296065606268485632) :
    (∃ z H : ℕ, (10790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=562039146105901433952266810075871886330671803081326901453554998206055433460008434218718556510689090163958078941620600832) ∧
    ∀ m : ℕ, 9290 < m → m ≤ 10790 → ¬ZerosAtEnd m := by
  let R38 : ℕ := 306362732380872793995102890164814422328022459689770717725986687402031648007797314669687624582209055539680871621398102016
  obtain ⟨h38,p37⟩ := certified_run 9290 120 15 768561924259763790362599598378945162019057361087237737435031305762041869901720537564190796946694626586296065606268485632 250 15 R38 1541725154434536455397098511811079060068562632335052173022143644057954385211548998933941011351558557178011586308752252010600983889987632427318791343789267319600015107342859734455704866292964766637322097089642049985837530944990894257565090041122099711643577097301471489185381973434097170333213136666024614044783238646221014181364794770997356049349214337855190484804204726516954426290266129916957759898567672633309838916244089585683525316144241166267357500362386333765720090340231309451596432398560562377880866464119384944282634 h (by decide +kernel)
  let R39 : ℕ := 432291041942402507549393205853938307578962221913042179081501787505643456606677329419642050592834685140137627830047473664
  obtain ⟨h39,p38⟩ := certified_run 9540 120 15 R38 250 15 R39 2490612956437285288293386353446468428070995931073300391926550268013569502299857691587424419893134637852546202599584227240066020392635593438862215017429864338794557863407525972822966116289303208639215983159790336170526159902916581383596645369840898575800284416472932757438736514657274180450016308934377312212635331362403228442673735067219346879245893632358155205438653973658101054898907295044984975977167912704007203574454215950614522928779887166241497657363792976111886332270536058887769385262987867878769809521289551004385793 h38 (by decide +kernel)
  let R40 : ℕ := 364507896699123513014719428626384597869015321868505686991337862293070814413544483748789381289225343895481122635259052032
  obtain ⟨h40,p39⟩ := certified_run 9790 120 15 R39 250 15 R40 12901917471687162209886165962785764684219798042681273521303452971496122460821675012268000091181840324183835113013068532341481523348058591852357009130827400095828473126071142308993677791437968825240035391946291824629392241292816375108963133433934473464573489189873719203756289828604727236963243255588381337955974532344426633067594536341194965942149252884120658235969015225261451096128706333990967459380067910440517314003358583666475097245616006378748353871508889224218203821983341280959900350682558732079381833666061883316242050 h39 (by decide +kernel)
  let R41 : ℕ := 67115288787972252011419494100005736902375061450860482531148244006281923451051869091155825621819425502898257122763472896
  obtain ⟨h41,p40⟩ := certified_run 10040 120 15 R40 250 15 R41 8439938644918015846480061965885352869870384548287472933851348784626597369036875961637052454510406793356237340187080482847975350262596441842581367498209319401265625519690965031494102986575850482268191593298467021018670522872832686861673605695921194418490753205902098377574433837080319126843158060677453019565420057641299871207287583309639475173950535594365289400106612181870086997345648297576434858099265950012609093190925699810080246009899873409568293755965589837420544804760427948196034311262467603343406288174898132436469387 h40 (by decide +kernel)
  let R42 : ℕ := 779900691704125681693775606888121373243756296468304393702766344135301779506207359538828267594304133565618907848174993408
  obtain ⟨h42,p41⟩ := certified_run 10290 120 15 R41 250 15 R42 9044247902557480717033848927734777798062464714123264443197584702523632538029487723093578809673687103733531424325213189175882598741271798865727161336522904611109540873969880069202540145115344542890409039968480392567087973626791847146995255602392269035698260707531999615023835175813635643473696543224773254664429252045945438016128801426021856936233349602732288996050534453141982298526399686805995484867283315955777879245150345613614039169718463134870718098989939154267545233364601353564630921266583733607183604445347798531016460 h41 (by decide +kernel)
  let R43 : ℕ := 562039146105901433952266810075871886330671803081326901453554998206055433460008434218718556510689090163958078941620600832
  obtain ⟨h43,p42⟩ := certified_run 10540 120 15 R42 250 15 R43 2498565074285706532889870331299991256169054142024127420424427804979012030270559011224101282041309484831892238436111939441985777681304221148655391186058980333631092049421111239527861661205335783514530453224890264499548526670749074587662960643338512535808947598119930765961211447118635026704503160599690495012668642787267353039296812851761074437928058011256381280726615172846057402542397031297651755900096123314613109315813419761487277549506852307834303450888477715194788642561289134855850801450424495248995773749531035153091841 h42 (by decide +kernel)
  refine ⟨h43,?_⟩
  intro m hm hh
  by_cases hx37 : m ≤ 9540
  · exact p37 m (by omega) hx37
  by_cases hx38 : m ≤ 9790
  · exact p38 m (by omega) hx38
  by_cases hx39 : m ≤ 10040
  · exact p39 m (by omega) hx39
  by_cases hx40 : m ≤ 10290
  · exact p40 m (by omega) hx40
  by_cases hx41 : m ≤ 10540
  · exact p41 m (by omega) hx41
  exact p42 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span43_50 (h : ∃ z H : ℕ, (10790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=562039146105901433952266810075871886330671803081326901453554998206055433460008434218718556510689090163958078941620600832) :
    (∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) ∧
    ∀ m : ℕ, 10790 < m → m ≤ 12540 → ¬ZerosAtEnd m := by
  let R44 : ℕ := 604776984581085884191330322370664906745459751589718183812624768578171979583277536257548223797738276250239034980437065728
  obtain ⟨h44,p43⟩ := certified_run 10790 120 15 562039146105901433952266810075871886330671803081326901453554998206055433460008434218718556510689090163958078941620600832 250 15 R44 558564395521897318507136007191149228847881479221082887879361470568574490998094053707259280281495512292051253491010135948650888181539755943089913018741124549822251121612385740381471963204613197330445374328708949336798110551491536552803035653837936689837552399023305445083313835458447439915777122533886348110649553966243508158436663114668523614306780055901564238770481674108658188102564938928094273075727115547296569949183752325265983565762029302748624504020413740072713158374405252100250704228455249203529429178805310158274946 h (by decide +kernel)
  let R45 : ℕ := 179006048414205942089332745612664668950374013941314943670111484774524256702040613427335766993556091825517100491815780352
  obtain ⟨h45,p44⟩ := certified_run 11040 120 15 R44 250 15 R45 3005712633341691272943954815167073633691547861324980624423541056408280043359688561035159617910625983429666909297615014666770057983808006215127436036791247740478037582318865609455889429948926318820756778762634425205187484276372240497189300505047315860366730450524960984708349064223310284262084233875711190173447698614733887018380580236261195840991113735558445438967142555656894028960052839440122587977899235076855232854890305572053483180069709918729359073286553462699559766623184419760150802310866870637986019801300678626967816 h44 (by decide +kernel)
  let R46 : ℕ := 848464329511113966911838944146714436523759994523410210189705262960168073955116479088770133865554741138536657988140138496
  obtain ⟨h46,p45⟩ := certified_run 11290 120 15 R45 250 15 R46 3974109981004667682139954336176420990088306292498035843590486034332411404507062560051734657971431560765301699410299053958842067068531762669257805112455070858765258704103995073146065194414873060140197943522264137450172881731813258508315372494511185701012038036778327202026559025062989209368353242092719564243366049197880251097081856237283173848847616502200993077493004581155473228359705245377961912582417279139861616873696866597006980666545476355044618909785721296896592794350820596293549825393287531730856555689227635803948168 h45 (by decide +kernel)
  let R47 : ℕ := 758559790861067542936342747549333192332204779977363454854402926365312032292621512497746887734074856966853882158134591488
  obtain ⟨h47,p46⟩ := certified_run 11540 120 15 R46 250 15 R47 7463766887891874689751741824851407636713877525163893169853711942988794020255806058202302592561038888695328851308529479923322834373024281367890096156742119751729752329719490726438948753220213357905660920697255084426551873445379143577397002882382684577575125352023921933804763897139792270295655668444177217241222103856600680631215962205790782215324973052904074829788975880442317286374934025424997537454286440318695174226124005216634632844098683202845468473059690103662984120692149877773124471729216821143923247136069679193440514 h46 (by decide +kernel)
  let R48 : ℕ := 556773479928228165825193427435562953684525487404270883409646087233400221550410678669074544173324506250986999770937032704
  obtain ⟨h48,p47⟩ := certified_run 11790 120 15 R47 250 15 R48 5465541653107029570704807525486889009917254476858274759229163138088927153836900428603538210288086615578677188145744769343466299671008570156645870517748615264666592343168222195469445932467514685896724387590909605992218918893934339617207456398468493651991481881572053831016632155978032142297556001249233298792654030465394525273468382502181485466750814840638327958429053690117923363341285061891319477033859589467718010079966917726157873249101561278140878404887279682783813078944096877834895297500554764965509001572830123852333324 h47 (by decide +kernel)
  let R49 : ℕ := 566631444697669758275673578052957255473898548631199915751449952545296431979549856828956400529642994619957112136024457216
  obtain ⟨h49,p48⟩ := certified_run 12040 120 15 R48 250 15 R49 2519323594542054501731055255567149802029978172796497024301835613485347501633816619662207530528852043315479663131374438446716683206345849675997373999444543123903093156535870763545965527401331904769726070634059593631659063385895263701006862280285495736212172476677757739762579154713325287098113947820840027125950809647438559146362483656581680972586700428833192496179325718003722128121669053091920142290610628578006162753269658947198174110964790920533682837381622141145294266582524342367669758290943891084627357440289387401250698 h48 (by decide +kernel)
  let R50 : ℕ := 266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056
  obtain ⟨h50,p49⟩ := certified_run 12290 120 15 R49 250 15 R50 527243893583706165435214617069491737990109608663159011970674102798597710253329454561472523604905045485323576795869141311824617906211230809578950067224796369159749879490481955283608985340189384154055185038005525437185267734096226960472740869604982946699999808543860025183834393064859534440611015063723984326800395001832296820430429438082754452175532011741375555776209970634300740605421882138340366303059971255377638190442301562217234663313849837382901890403665509070548093080460115497550140719796695985373236391259482152421889 h49 (by decide +kernel)
  refine ⟨h50,?_⟩
  intro m hm hh
  by_cases hx43 : m ≤ 11040
  · exact p43 m (by omega) hx43
  by_cases hx44 : m ≤ 11290
  · exact p44 m (by omega) hx44
  by_cases hx45 : m ≤ 11540
  · exact p45 m (by omega) hx45
  by_cases hx46 : m ≤ 11790
  · exact p46 m (by omega) hx46
  by_cases hx47 : m ≤ 12040
  · exact p47 m (by omega) hx47
  by_cases hx48 : m ≤ 12290
  · exact p48 m (by omega) hx48
  exact p49 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span37_50 (h : ∃ z H : ℕ, (9290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=768561924259763790362599598378945162019057361087237737435031305762041869901720537564190796946694626586296065606268485632) :
    (∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) ∧
    ∀ m : ℕ, 9290 < m → m ≤ 12540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span37_43 h
  obtain ⟨hend,hright⟩ := span43_50 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 10790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span25_50 (h : ∃ z H : ℕ, (6290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=463580668188648644231962665821830832719727742953591766649471054193330620958660527486313192981834812517464564808026161152) :
    (∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) ∧
    ∀ m : ℕ, 6290 < m → m ≤ 12540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span25_37 h
  obtain ⟨hend,hright⟩ := span37_50 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 9290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span0_50 (h : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952) :
    (∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) ∧
    ∀ m : ℕ, 40 < m → m ≤ 12540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span0_25 h
  obtain ⟨hend,hright⟩ := span25_50 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 6290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span50_56 (h : ∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) :
    (∃ z H : ℕ, (14040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=996630421701726236273114317138865560122109596800960366071247255617493617319857637005810923833968859358817803629615906816) ∧
    ∀ m : ℕ, 12540 < m → m ≤ 14040 → ¬ZerosAtEnd m := by
  let R51 : ℕ := 68325961316043340229045985720787560173114257809398179738555817938656831517363906578688896031876826657252933974473310208
  obtain ⟨h51,p50⟩ := certified_run 12540 120 15 266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056 250 15 R51 7491060053605568342780476017804510666553877062100138796037790892063357541633812684783080473778294607954268524344547159215533617029341124651514709015602818318839396741684329749339050885871562836157984309676426942697309780369705671864742444639185104331230347806162280787850588197694120943962678299689112855266943798136207458837835543358324618832316882360916931646050164517929681711603141175762527194425660181786953074706061415799526729021906149664825801800428699755442148342325431198930562289385122335772189587604962225709761417 h (by decide +kernel)
  let R52 : ℕ := 689500531300668438905389692799188056301104606556916609652923164710488384412753684659226599322662111795726563956924350464
  obtain ⟨h52,p51⟩ := certified_run 12790 120 15 R51 250 15 R52 2060828505746308576827460604877528208031503820001866723002552596986294001579768697327805965719699767378779338098875902933775904584691094924945644617196978488673481399981316424158150366441111771428612632483181605046759502940078579685102360931514664663226019030604882151122677332304061682815794264081623375914839756242939347052751958865603212875208619714472188413090297772143752910324513273292238456406126356420154524165884099801719971294913090846888787709283560186216325352440063929940480816688662918041273607937876974580781441 h51 (by decide +kernel)
  let R53 : ℕ := 223451492376316740444796246620338932940849012178965691093193995483923140222338370165768989801623991673101183202558476288
  obtain ⟨h53,p52⟩ := certified_run 13040 120 15 R52 250 15 R53 2002517403864264544114779434643620510322920572982602826836911999527266839551270607299358220044443468547681533408666219938371439675344934995682693904093736055730964317122164425871312651654746453802536186078273340281382913842342142457570168288207140429713922940013465694436379862461265790325199890594070603955356964542088372198070258363477001269859411383759421387985292617967788915511360855492983506364466351343384193677239409607259102128486090292725940921304425581387593775272982850673295394696047020856329753389792300099715602 h52 (by decide +kernel)
  let R54 : ℕ := 589693856485043788462865025091689862150689070988609195692008089864378265041424299002536546021686334280747660654833303552
  obtain ⟨h54,p53⟩ := certified_run 13290 120 15 R53 250 15 R54 3068138064369242116460803984661047643188562443339723813418315513799566514897241365436156629423548592150288562363792977970906174529538865201726865922104633502104974032516409615289308133264975283552554195152350943262681031245934840835136069243839446275954560890506251405796492829001997289672359704057800571843061836151397100745613939109676269732116734799740872280894554000064258801777531370639978301215937427203433136374817898876747477938734175106598211551694288612260513172162896429591290587654587519995446176222374591809536387 h53 (by decide +kernel)
  let R55 : ℕ := 777924884828700410943933600493025005295488282069658818867329212929444482931059595096602996571659700302892531930556792832
  obtain ⟨h55,p54⟩ := certified_run 13540 120 15 R54 250 15 R55 5976445339857777246494517568517586636586954979080716845239273958589214037854561191539784038202282438879211864847457870026988385973664311546796329229099212716299723779109759620289795170411627939012341853959343737411444026107715135511051575132792863141891472206381232616468786271490821296164751340825879103273500870565633309520498200616523802191544438032971585023349921525833159639094447214353323686260993292448574555318726160585706922240535037057861295463548651177552093643339249310246315125750074467388290782213673299856097796 h54 (by decide +kernel)
  let R56 : ℕ := 996630421701726236273114317138865560122109596800960366071247255617493617319857637005810923833968859358817803629615906816
  obtain ⟨h56,p55⟩ := certified_run 13790 120 15 R55 250 15 R56 4090491291786403255157306798262396975678391629152350051386420982380085152320497569994079775701177915183580278441385701728489751311802333133716088948119431905991675839924640792747560304688459150386570365848896829202301362322415397696168258424747090972386684365765234842647784481372523645264811217431569582587917900286072625588724023448134297756197931258363605782067335850312510369109808322553655824276056731488200706097255909353082645721805270899282606384614866126470842408424266043554604769736308438530155074583829312570606210 h55 (by decide +kernel)
  refine ⟨h56,?_⟩
  intro m hm hh
  by_cases hx50 : m ≤ 12790
  · exact p50 m (by omega) hx50
  by_cases hx51 : m ≤ 13040
  · exact p51 m (by omega) hx51
  by_cases hx52 : m ≤ 13290
  · exact p52 m (by omega) hx52
  by_cases hx53 : m ≤ 13540
  · exact p53 m (by omega) hx53
  by_cases hx54 : m ≤ 13790
  · exact p54 m (by omega) hx54
  exact p55 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span56_62 (h : ∃ z H : ℕ, (14040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=996630421701726236273114317138865560122109596800960366071247255617493617319857637005810923833968859358817803629615906816) :
    (∃ z H : ℕ, (15540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=713846788345728897524753705710276454058711830594400773941574662760132460019548532887749672955037852089813583466380394496) ∧
    ∀ m : ℕ, 14040 < m → m ≤ 15540 → ¬ZerosAtEnd m := by
  let R57 : ℕ := 769939122441984722195753425362578540728513634696564350899816303516491074563204312899723982699830320093234901489295556608
  obtain ⟨h57,p56⟩ := certified_run 14040 120 15 996630421701726236273114317138865560122109596800960366071247255617493617319857637005810923833968859358817803629615906816 250 15 R57 1545750147581875963448622844414217595350669689818237690792175082026453770636743083272402333839803210393309985161663869814654345496200003105171670175710395442496875398967151316488826890256281110739839901205166982110539742364801854346258857078693522634501827200528252056925158930519439037079308512331585022870549216962567098379473027673392995728669282040458692305048391199019501136723411517932754628971474385746038517601111994405565226105495114844003121987859158552654930235293593950087790746725024966446179985021067520817681537 h (by decide +kernel)
  let R58 : ℕ := 646642861511804561522233840040859187638722255691110466832673130553163945527714673235870914557071494383599249728678658048
  obtain ⟨h58,p57⟩ := certified_run 14290 120 15 R57 250 15 R58 6484077945580361251169295513876332606817224907281268509171155879790802396700380016248426659972222030650464752520001070680784911146970099559390926187714613092189451690617872198866055919197956101032092927504029928109965270076950243645025773075548706979444550589581227099023325121020831964309955090886996548304594464615048197600004658216305274166650857958422365770194935444890808552835912354992464104569318173538973148469531772470017182385054341234744376031416617619012237479476270565217500992547377083047860774038487846986301953 h57 (by decide +kernel)
  let R59 : ℕ := 423019296760869444010976493526689982826839608314795666668511966507045828801337112607189448963149198206327801489068654592
  obtain ⟨h59,p58⟩ := certified_run 14540 120 15 R58 250 15 R59 1495160196384371730185587118649952998029950946852083884866573764649618667859663831437513549128261346645913889888511631507414144493948761444399237096184648097078880283069169623880136418757151418294085420534993883528178456493146739445976146339989742199810801233492822924405243467587857083025155461064568562464612491864977662151037167835860332319775675169290026353016861146002849511780345163906458920884533149487865542261112405016774861376449473243683936528700648185994467245907629747205483576633608742902215784237348732367470730 h58 (by decide +kernel)
  let R60 : ℕ := 942591973464983658517762655612359349963737979034321971458961929494440792276111819515519578524456198249203382626532982784
  obtain ⟨h60,p59⟩ := certified_run 14790 120 15 R59 250 15 R60 6468403261042621736561787274921878923038886059093419255490048475055695645961640710083905458694653915058241982318703844673760775286049579677324382753332371471128131500464903018521759297674487233536032458217017179253740967008934170386803809041174722729844670365418581412001996558989137847068485686910189249877138655515569562781228185101043931716241638787478656358478498596058583167373685710026222579032334888351649650600036775850952189515533094750168280283306466069925567739408198732938953513086650611534462834098910878110893836 h59 (by decide +kernel)
  let R61 : ℕ := 63948076418121913828140561956308905875230347655431689727904379083160319865985512751216344678487892217453495502264860672
  obtain ⟨h61,p60⟩ := certified_run 15040 120 15 R60 250 15 R61 1034214561997847085733866049580828310624057847912786681987356315848410496572524700806084347662102535270227161067447502494229222745526781405898953130584072678145711092539340118793855743644003437816004437450716124474951579072265145340917011182051914724758649631786609156477068880466962450707052359444178453955987039998671326595508121227152297638111197283701404502808586661562205587486469458858787514695779875166315109639848518241687348253323650975867461238646297325790367168323549552901967898100627139153962715873500291468954243 h60 (by decide +kernel)
  let R62 : ℕ := 713846788345728897524753705710276454058711830594400773941574662760132460019548532887749672955037852089813583466380394496
  obtain ⟨h62,p61⟩ := certified_run 15290 120 15 R61 250 15 R62 6991652665828929770034316921008456748244609479604539484374932061824831899377707728048543086405940142055780309244143660785072302776344060828406070694535112459331191298972807684071542245300014644296322585088207010756010170674047673521649507866556079339107830931074853596618126848927095075086470738993394857801925941493566913083555409577811463402863457058090277602539539983608794271523373643565668956853773418464665713962524402265496595370057474918905947255288031999057047488742667442163320214391009142590741198769668118894757382 h61 (by decide +kernel)
  refine ⟨h62,?_⟩
  intro m hm hh
  by_cases hx56 : m ≤ 14290
  · exact p56 m (by omega) hx56
  by_cases hx57 : m ≤ 14540
  · exact p57 m (by omega) hx57
  by_cases hx58 : m ≤ 14790
  · exact p58 m (by omega) hx58
  by_cases hx59 : m ≤ 15040
  · exact p59 m (by omega) hx59
  by_cases hx60 : m ≤ 15290
  · exact p60 m (by omega) hx60
  exact p61 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span50_62 (h : ∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) :
    (∃ z H : ℕ, (15540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=713846788345728897524753705710276454058711830594400773941574662760132460019548532887749672955037852089813583466380394496) ∧
    ∀ m : ℕ, 12540 < m → m ≤ 15540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span50_56 h
  obtain ⟨hend,hright⟩ := span56_62 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 14040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span62_68 (h : ∃ z H : ℕ, (15540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=713846788345728897524753705710276454058711830594400773941574662760132460019548532887749672955037852089813583466380394496) :
    (∃ z H : ℕ, (17040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=862911342191330970988542897448872635438501660090573238094108461419860368676747798338521803672184000008952335903129337856) ∧
    ∀ m : ℕ, 15540 < m → m ≤ 17040 → ¬ZerosAtEnd m := by
  let R63 : ℕ := 277884509208971106475836921235446480262825200356867658119163289460906710784482726038066985559284203951332153478462046208
  obtain ⟨h63,p62⟩ := certified_run 15540 120 15 713846788345728897524753705710276454058711830594400773941574662760132460019548532887749672955037852089813583466380394496 250 15 R63 3021537843710874444057651896449867323115063902414860817325622215915492345288015245244341386301469337176619486700166964111865331548238481880038362381993969286543623497241359329605746235905411194355808647330928421657991425221013445541138019259110160002472916851730467872773703041695123893555467219350115887389336501183522222328154535995886591080055560732655101019052968076516430554765444495141054012889281560983005015286712311145603038340509212660990726066535334740477438951860165607357816339618905111243171684068463775345443074 h (by decide +kernel)
  let R64 : ℕ := 85603886738010233898111192592945983122266034995247640586148169624172944080901107942859250026515756191914936291800645632
  obtain ⟨h64,p63⟩ := certified_run 15790 120 15 R63 250 15 R64 2525409336505412831553225647633580602697266538062256887137526274685467189341004869759326121779873986280013152992044924001045560479842402445296140950274188946769999025185187795607934848928194455076750800628407045907568035262808720665759666047204899633991839855764750924984243898603346643409109545362609966704301029821674010028510767284860357609117000750058095387651536592951364201681820840840758090822700808822197117159728029293482185320309145817042122469558851884532391474803781279560556688009313883495012088311869806886588161 h63 (by decide +kernel)
  let R65 : ℕ := 919143870532140965563386821765634897778809794605379432128759773483380475646311268052927348250272268865063080046022885376
  obtain ⟨h65,p64⟩ := certified_run 16040 120 15 R64 250 15 R65 1541664402448185992504155791465632989045529010206527221093325880756838835606237923506385361714569739754413129306381725749132391818819965775354478477710616376232391699209755410031791196787638602892091539300844521350689295079199025609289052307704916506725649550759050750781465564218623066683268647669548038373321466846162537888599971316329995070516585577666925841951253852982799187906162595029993604344297936068161854075489642255493953833665427121567139294250997045386034637324906682603155027869822262176987071074075626040329731 h64 (by decide +kernel)
  let R66 : ℕ := 884505352618608854049429675004684835180586436543724325659988496956491419932523489700707637746472091000114226397737648128
  obtain ⟨h66,p65⟩ := certified_run 16290 120 15 R65 250 15 R66 516108599826481903709896341647112004983778997548195272299821549046851043064476899131728268980267792269208846997264986043669418912839657892519217963566466727729651697823837519734739520547154868584030550177429165437328339021753025640205166802572286005502288057743460521156967546726627676666796178104678810425712703696275778182127807086217341275278813169405703224840371154636136898508497256241584258383742200979415674001238866187141208312013854109510723158035791375256117431389623090257139953825734014441849053412713212881864070 h65 (by decide +kernel)
  let R67 : ℕ := 299292573841857816193578877542854509315866078543678764142733386719547541804133509145678261715285982645809544915838828544
  obtain ⟨h67,p66⟩ := certified_run 16540 120 15 R66 250 15 R67 5024084787000225784935602560267018745816095025022438547332356019988731569760603657099355210846454266842196610969544576579389045697110953592151201912173595704866230840360192370548081196963125190023424711279312220648956488168160619461703210707699559683617797176842947866568687276437533499663847010723128521663739621776203085968679865851049087774529877968906473337497432365781482838251768484676833473449882242122972418568305721940944675209691435056338563626939004373853543840834452894749837204878927298941818127151567363255764612 h66 (by decide +kernel)
  let R68 : ℕ := 862911342191330970988542897448872635438501660090573238094108461419860368676747798338521803672184000008952335903129337856
  obtain ⟨h68,p67⟩ := certified_run 16790 120 15 R67 250 15 R68 546369563146290292626394180520279687594522405721421104645886979094097255533619449247149489899721889954230638054118872891655929013031899242682377705242447410452220422870251604632749942186573515328364215317745876118274016144969224925347563971393417967040480768185456489643123020847734870898602999708711734552917113275952762326226939897792219089395293817413249637550713393843487515169518298499017288141150160939954356923311348756863844667575613442225013018664233811953852908691019896507952656046139237343828240822221278334288520 h67 (by decide +kernel)
  refine ⟨h68,?_⟩
  intro m hm hh
  by_cases hx62 : m ≤ 15790
  · exact p62 m (by omega) hx62
  by_cases hx63 : m ≤ 16040
  · exact p63 m (by omega) hx63
  by_cases hx64 : m ≤ 16290
  · exact p64 m (by omega) hx64
  by_cases hx65 : m ≤ 16540
  · exact p65 m (by omega) hx65
  by_cases hx66 : m ≤ 16790
  · exact p66 m (by omega) hx66
  exact p67 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span68_75 (h : ∃ z H : ℕ, (17040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=862911342191330970988542897448872635438501660090573238094108461419860368676747798338521803672184000008952335903129337856) :
    (∃ z H : ℕ, (18790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992) ∧
    ∀ m : ℕ, 17040 < m → m ≤ 18790 → ¬ZerosAtEnd m := by
  let R69 : ℕ := 957508108018367717178430358668590033592628618568412438848749702131653687848110807477841297556120107796123168486010650624
  obtain ⟨h69,p68⟩ := certified_run 17040 120 15 862911342191330970988542897448872635438501660090573238094108461419860368676747798338521803672184000008952335903129337856 250 15 R69 18347700560471900196358311730945096143485107883647511797481327702842974405539340264773218558238899892754080890606284066583161726413050268460033177616141180721224071244237764176689567812087599952809998959860042919545034425905498629502419197303306456773332071835584014468472666378247681646768698354231212270672410251707622969008297518189237344186904284078221715932111541392559969656102520579199151209862367951006896451435736964913388104377239988037609417324805471194447927717812471775694210189707166419400578682045484068791124376 h (by decide +kernel)
  let R70 : ℕ := 638875551576962971012649192644481092448746316819097141651037731167323883110616084206088451576174224997956846309485838336
  obtain ⟨h70,p69⟩ := certified_run 17290 120 15 R69 250 15 R70 1034182392842249621206859248315300644016112606955368755929140620751676997254124063447352429896827068719610296562884671839564291374983512284993207850493655635261086635490832111722235172048596046656966781166891477593416407643513252713414906662063914988061999656409098025716724612764917924123197141384695436520862233258822942953260277622253595099055183736829892486564736032235797590466051430377050422510717030028989636732777965813726390329369820895530052741965019853240725709826827934689501833142233875002646685355706106480017542 h69 (by decide +kernel)
  let R71 : ℕ := 336680294586943514190062715316259073502768977231960417911617774257976203465714411273570101400333853297189287248189718528
  obtain ⟨h71,p70⟩ := certified_run 17540 120 15 R70 250 15 R71 581106120488439925090833653750566671588016508989064777889850128170370339779369354229161452665109301239967382850197904585616785880926795891163813401184464149272559437776029936221223817191068489315477133740997937128096308360134294631531949557252222722730115048649191261879613580139917421532373575650162205886660304454134950201394212804096736471500514090292923469828980952716932525573569861088807548128871732089912229070899284500545530642343198946755361497913753418349074192775838178723177423859836633006312906672027829610234246 h70 (by decide +kernel)
  let R72 : ℕ := 998760790508831033853785771536023222009591582372418051529179666145189092417083995294285779947330701944541884692020854784
  obtain ⟨h72,p71⟩ := certified_run 17790 120 15 R71 250 15 R72 19900860774499154576737662968521942743126521740070137614709380915142692255314153342243293152069718769510942947559071857069559119315342659903990481202479065737183799324253591005062871985409671767457239915394774201202873883563023364238309136126160730735463323384328684472965078222693307039963799530629341084470212334456755838493019308340251234189743788153348337858676508726111441234648035459105512068736964825783045401566409417542149805488329207058038582281496925158752799516741010137608195486598589451068400897198721385984230051 h71 (by decide +kernel)
  let R73 : ℕ := 28494920866901646921775059415022149528733742316533484959363963290342888154866942546609984238478593161584503717365809152
  obtain ⟨h73,p72⟩ := certified_run 18040 120 15 R72 250 15 R73 6015267182462598140497947430608211452611288382581448350910067800491418369157610641683896653760662840527792497656745330816036593271427421982813573428677148155257928541106239436923770080142906681181511488237236229010425401714230902065033046926355346001228950164055060724587029412751619762977880831043482681335746536089512944193113265595121927209667359052524759784970424788594132373981470176156439705389983576177861051299430811265057149002230837619731587928828192201202272032363656941793434959614226095020968383066102417783328517 h72 (by decide +kernel)
  let R74 : ℕ := 473246769151954120231586103996499928110643914285019921436797521337125660964957585325369892845824083303580085690520567808
  obtain ⟨h74,p73⟩ := certified_run 18290 120 15 R73 250 15 R74 6464500239147848777484342973715482493205406416072655042714804527293625613704289700329374071266715151580136219061775437187194324467255595974664034508377924812304489013552643434995965277733506589863605793256640936353106450719554590810332719676386180578905251210989931067115112835423008156073436026304191312259432858903827794630078835200061786258968030791855975870616263919823455325450626083552509665944588276839670498878528411753713777207284467815088295777800635896017965760576142619759623780377626829233759168417516514980284296 h73 (by decide +kernel)
  let R75 : ℕ := 799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992
  obtain ⟨h75,p74⟩ := certified_run 18540 120 15 R74 250 15 R75 3981946264994488806169329594311765980705106792238212440465755456960700797663016292659442181647489974723521603232022211101574783113461365362666438400159693476105321470815285250599985112614115984846278198461798159900985131510191176463348215653056205062976692518056064617984798102401013438883076238890027829520505797026253448605899231778232386680696571424096669938464663742363148494152104745552187804420767292777811670278492027748439348159309723314651628226333090877967555961879068913408517311432474913794687480035216774452515201 h74 (by decide +kernel)
  refine ⟨h75,?_⟩
  intro m hm hh
  by_cases hx68 : m ≤ 17290
  · exact p68 m (by omega) hx68
  by_cases hx69 : m ≤ 17540
  · exact p69 m (by omega) hx69
  by_cases hx70 : m ≤ 17790
  · exact p70 m (by omega) hx70
  by_cases hx71 : m ≤ 18040
  · exact p71 m (by omega) hx71
  by_cases hx72 : m ≤ 18290
  · exact p72 m (by omega) hx72
  by_cases hx73 : m ≤ 18540
  · exact p73 m (by omega) hx73
  exact p74 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span62_75 (h : ∃ z H : ℕ, (15540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=713846788345728897524753705710276454058711830594400773941574662760132460019548532887749672955037852089813583466380394496) :
    (∃ z H : ℕ, (18790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992) ∧
    ∀ m : ℕ, 15540 < m → m ≤ 18790 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span62_68 h
  obtain ⟨hend,hright⟩ := span68_75 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 17040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span50_75 (h : ∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) :
    (∃ z H : ℕ, (18790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992) ∧
    ∀ m : ℕ, 12540 < m → m ≤ 18790 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span50_62 h
  obtain ⟨hend,hright⟩ := span62_75 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 15540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span75_81 (h : ∃ z H : ℕ, (18790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992) :
    (∃ z H : ℕ, (20290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=394882184137412879127249532574295625073028466207409436690414249383664074751702732133062839315112313638425143745804500992) ∧
    ∀ m : ℕ, 18790 < m → m ≤ 20290 → ¬ZerosAtEnd m := by
  let R76 : ℕ := 601530413820862760422230200636147398686910675204550322789097900426345904091971199948506656146651125159150552831236243456
  obtain ⟨h76,p75⟩ := certified_run 18790 120 15 799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992 250 15 R76 542649054797082422117920320309717844587001359127151821333666370354615968401915868398265598071610681598096768377172595291233069882524388406460148877860446471513567668248019787210833381640060898137220324679942206431432852647047575715054933092213935977211499921824914328195300436549791730088279925895084012535256458733449999432930531211155256027751272819499453612666354809869071480834325937386626655424872621129346444775240294938876041743143944865487371560414265304561847194344093585275446578751987465395365011552535716217045250 h (by decide +kernel)
  let R77 : ℕ := 111744126189174486804903517240690851086942714784833254958773694346761086253244550099510856366750358115290627256140955648
  obtain ⟨h77,p76⟩ := certified_run 19040 120 15 R76 250 15 R77 19385576048114228907322585225682442593128215069690505453454706700544385702355422889703003874869466262673926422692404574557653600745799869808859444178185595524296140956166812356347036420974875443755277144026871791689750878350487647468024371981770802653976658027525989086173975285400466851152497884890236869584606579752869564493527861350659397194534866810969181714243376974653416937554202622975751613910428940795183932088204623364357877516966631074435689729086576492098179279786187119066153329218239213302520093641905994920510087 h76 (by decide +kernel)
  let R78 : ℕ := 538798804292773699675615646482360882678952434649334126391243742633633421102741269461562235241154651105325630870651928576
  obtain ⟨h78,p77⟩ := certified_run 19290 120 15 R77 250 15 R78 8935616136141051905110659542317001361985831972103221242381984282300423679669548128155391866724035126848379612227312324565158655642342489491273946090136784001591095261006524177883499487657511519362274837768917643084922813258604410642770121821672822892708482999652662803745665144050208292387483510752723273811443955458464748145839136197634291723931046315967478392581318746070543568986804794748572362497646906171347885673565479256255427068463902372071585271227199433726203801371399352431942633853448040125270528457891347758874775 h77 (by decide +kernel)
  let R79 : ℕ := 760135507902208306859480560590440701997317383321256335078093884934290627796923025044804778383914694027720811843214639104
  obtain ⟨h79,p78⟩ := certified_run 19540 120 15 R78 250 15 R79 10424297234703397942036185230704507824369649130117144822800524448267556396588375369077581486750584687192400670006966503747033821201297019436229725371757481124330642343311885485228580818256203709064674138198921395833144101418633415309687108679815507243766267374862638890428749670064664398875682474939659124615314484538531297407371981571009188357407925201901215438781884423590371294573126926004142082384548523689305864682663277410877829290092414549153038530146083259757415457360350598772279143266809697802297542317699411810009986 h78 (by decide +kernel)
  let R80 : ℕ := 591093042174791252316312619385411817868061494455037075396096285806052095662470572063524311516827524807526847768988483584
  obtain ⟨h80,p79⟩ := certified_run 19790 120 15 R79 250 15 R80 1530074532280783616138029753156062835824614929173429171703044181333655823857290575430410513986383528419826559939246652422450000463848149359123514428296648891276462777334080676073480274405275720308315831287415683419343838389024359073593405939859112015026705617605627438686051264770093226005895169663474847255332611984605237879921645994678748057795265931538862091571405257692086416006315027423192104400682596837265465175530291594821001794842175801966595843306743286325737805608355209775117144009465361977011165140753628361248133 h79 (by decide +kernel)
  let R81 : ℕ := 394882184137412879127249532574295625073028466207409436690414249383664074751702732133062839315112313638425143745804500992
  obtain ⟨h81,p80⟩ := certified_run 20040 120 15 R80 250 15 R81 1991019466537048845847095416827391159990575675619722901453000506180005230005347699773430327227395974252090898430105079427026532778093454041892003123320771022792282372177398359899177220342392757157321227405496232370980581807637466833366004083178228783093267511573975197462339574715638030132533944806255820148628770741613885973584335634227603678274752088843473916737774556710940323633510124080767645360457263585146421143323991328979449826695456974817106267156317928530091980443676059547117811544889106512711821782339600786016643 h80 (by decide +kernel)
  refine ⟨h81,?_⟩
  intro m hm hh
  by_cases hx75 : m ≤ 19040
  · exact p75 m (by omega) hx75
  by_cases hx76 : m ≤ 19290
  · exact p76 m (by omega) hx76
  by_cases hx77 : m ≤ 19540
  · exact p77 m (by omega) hx77
  by_cases hx78 : m ≤ 19790
  · exact p78 m (by omega) hx78
  by_cases hx79 : m ≤ 20040
  · exact p79 m (by omega) hx79
  exact p80 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span81_87 (h : ∃ z H : ℕ, (20290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=394882184137412879127249532574295625073028466207409436690414249383664074751702732133062839315112313638425143745804500992) :
    (∃ z H : ℕ, (21790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=46570033588366873400328054747928404320872555223777712644921353617092448292931256716825155033419194432834172309127299072) ∧
    ∀ m : ℕ, 20290 < m → m ≤ 21790 → ¬ZerosAtEnd m := by
  let R82 : ℕ := 997339857604727926165336668190891827065263994334018108151452486451850276787635463557055000585581268204186574749429661696
  obtain ⟨h82,p81⟩ := certified_run 20290 120 15 394882184137412879127249532574295625073028466207409436690414249383664074751702732133062839315112313638425143745804500992 250 15 R82 29266616865016268667813458767475124741853189642704851383411796977677105250164601837279253831815189895533319768623794118606717232238222038677539090288905831638162652678880941953828080640530156255185679136502672904176956610572965063747064755319200105279623025825563057850277410746667538509333709867537185221369020780860711053765493122095785992663789929373805556558937900437361666394571060580137293102331117564085938065431719601542278581546332134861283853466014218093440052136385110467106257854866232137943444924834131850438099202 h (by decide +kernel)
  let R83 : ℕ := 304175303218905537911124746606436785049864330296935074455512798710545546046098629886682465301234164932694307902268112896
  obtain ⟨h83,p82⟩ := certified_run 20540 120 15 R82 250 15 R83 8447560737089529119001310310367371774973314041064355289586240160992235696561289482967170681579778951744346454501475598593194537724598633221554267063440939909659016204276564985798950006089313162601395622156810650922013197644985790011484461827791932770869067829479903602627508466307879318299339434073431751273174343258456884624712079392167747651273784637962075907377076492982832344560413905056213376501885328909300131066225376900190981067390093428106945518330502701785579156437576166078091865733741939003936170475925636483547782 h82 (by decide +kernel)
  let R84 : ℕ := 832574760060556401995661973472841975743982396413911406066294592929609125084865862104475262790841977183649664069097488384
  obtain ⟨h84,p83⟩ := certified_run 20790 120 15 R83 250 15 R84 12472080066618799259572559237903873582973452268223702616505235557795815171495677589510611240223999474595323502335416582239679327823457161121744467160414978535789931698978470309954410540287519460387214157848985643675689300448443654357553102957994813046653129826388182588936083303896598849240282245994954626220751808445026318798217501257608084047025615175797986614201453845445555300930929376122284091859443528258848007532952573121677802255607449059267981302595471667028676291748730060459126053048105154736346441932736635982692741 h83 (by decide +kernel)
  let R85 : ℕ := 232954235563407055351019644439477823424983172986277474228011006051356610295239557948334138351271250079829129838238629888
  obtain ⟨h85,p84⟩ := certified_run 21040 120 15 R84 250 15 R85 5031378543030664658376396117613611739153483024846471272529920029646617457692751200210283579365619112309024693538921479602781331632183489536547720733386485878572171553109495062140464767225087255660826598459153464664529022905233156414017282364739791686405032424274239835181170678369621236666809430204616921089437345041823537872056621271413133335307787646019528741730235403813702509081656331483950381539096818182838930718919291431783227531720819919112052951036178190305622530816722115466328523851383636581225043448870194863343756 h84 (by decide +kernel)
  let R86 : ℕ := 89536605956407390658658469101354131730963883769505956103506223588690926200860449640298043328459806066230473160292040704
  obtain ⟨h86,p85⟩ := certified_run 21290 120 15 R85 250 15 R86 8982791737512756638524723420002590718065773899113774227352567588611879527379589725996045229000319404278994582031393943633941902021428676088024169992406223389777456463359650711638770810457000364724804875439923800234193181251423790346003616315125364383344319389509564664871336540705991828147711541722498848749888201460248924684523033726042633531421168033805500524646463408650216198252491198995162184861676024628373231586361504636987475730006411858885885673397497604845809308203316554041705998614233963558466755720532067843639687 h85 (by decide +kernel)
  let R87 : ℕ := 46570033588366873400328054747928404320872555223777712644921353617092448292931256716825155033419194432834172309127299072
  obtain ⟨h87,p86⟩ := certified_run 21540 120 15 R86 250 15 R87 8931811481644037620928176421810546121735951161505327495654623132644366765789866180093441315779682508635909798622703202166795156386456773882577828160809446758670909514349267751974274988384549253504995821461784039986916568098285653307273922987360465397927340317844810071739773080717847339263927844164242323825858176456935177514610137096849001972060556004760140080729490090492649245960939406274634045284072155875752981369338526599977439880378923128003347107490667854997981879230194282087289782798847973146889515044360360046987916 h86 (by decide +kernel)
  refine ⟨h87,?_⟩
  intro m hm hh
  by_cases hx81 : m ≤ 20540
  · exact p81 m (by omega) hx81
  by_cases hx82 : m ≤ 20790
  · exact p82 m (by omega) hx82
  by_cases hx83 : m ≤ 21040
  · exact p83 m (by omega) hx83
  by_cases hx84 : m ≤ 21290
  · exact p84 m (by omega) hx84
  by_cases hx85 : m ≤ 21540
  · exact p85 m (by omega) hx85
  exact p86 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span75_87 (h : ∃ z H : ℕ, (18790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992) :
    (∃ z H : ℕ, (21790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=46570033588366873400328054747928404320872555223777712644921353617092448292931256716825155033419194432834172309127299072) ∧
    ∀ m : ℕ, 18790 < m → m ≤ 21790 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span75_81 h
  obtain ⟨hend,hright⟩ := span81_87 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 20290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span87_93 (h : ∃ z H : ℕ, (21790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=46570033588366873400328054747928404320872555223777712644921353617092448292931256716825155033419194432834172309127299072) :
    (∃ z H : ℕ, (23290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=53647994981087005270525331519288749037969600870398755929646440628970649984499497518733322511881561510531951400643985408) ∧
    ∀ m : ℕ, 21790 < m → m ≤ 23290 → ¬ZerosAtEnd m := by
  let R88 : ℕ := 519763238258005306205199405402323439329037409755592234556085219818941486928680458970101987825156777942154775575379574784
  obtain ⟨h88,p87⟩ := certified_run 21790 120 15 46570033588366873400328054747928404320872555223777712644921353617092448292931256716825155033419194432834172309127299072 250 15 R88 3483026077701256300835837375622233352153863474129580257995230011155612941966287306894202327097613617349822055116073349719960775290748336835788810097495902435362725226992510487512584443183005081157501575963543492332880640806709718776480923929318511208874219764046276168360276342746333880706802380043829544838758798443559240664477552329242881810388906323532157608541349290454234187505083629001981269368043560438525384016120402941581612500481656274921304078383083205640083139340308455145178638687847657385152965100030682955318925 h (by decide +kernel)
  let R89 : ℕ := 95675071788425181135375630452098041704461039866616100894056950482370891734286610487804252714318816373857199105335361536
  obtain ⟨h89,p88⟩ := certified_run 22040 120 15 R88 250 15 R89 7502465073282610912465546707452814063870688323968577265643092651791185495792994199915105247255447767084183687075078350820092215922724952164802405864441439742140034512066878286070011554211404091078928005223435615562166782855288069543027082170958614019789072575172376779143367301070449369672805817310344820091143540534857744583383910539383499282324035643136607461343974444342426541303455558059129247446760048887911639772142705921035934925763603909118021559459761659285250579007269184727680496991551509082433908442654656998688515 h88 (by decide +kernel)
  let R90 : ℕ := 368651522593205857812582021565258133934450099435170764918870532449650158723790066494848648985330820740106729897987145728
  obtain ⟨h90,p89⟩ := certified_run 22290 120 15 R89 250 15 R90 650831956780495041090932004285207108918773602207306337052009279198709135855395194904985128285101895061810279211017457122509125708782698268294803946753135875359278684090688267864589197310276480918579137815431058017513456917364200112800547692927074723039251895520262859610003376869797338288280839883157034629943656086468620523305944723627472133015493257916562642538420630912920289516330194007581405563485102427783812291242418794826146179166786928006526014520805228313706094954005969907620655802963003346263120696736735190598161 h89 (by decide +kernel)
  let R91 : ℕ := 464769803414899069004790037031139491851400472087711926014136089171621774082256180966388830403386779950111948987888041984
  obtain ⟨h91,p90⟩ := certified_run 22540 120 15 R90 250 15 R91 10918826961445763319099448509382161295626615833430571742831902119482450443771067827003616085106346307827730195006860247360216406110732693982612926251549817986055023517066037708445162253547013852918082855810143146519966055226712393553567661870880837098146343810520191217279995186389328899676403984295191834922845322049312679200844621788345881988370522514655175400151246867560440201205270483155299978707271304501925913637390509257841251572097257115681605002044313002756350836063802953847835579683844044951684138538972733342007576 h90 (by decide +kernel)
  let R92 : ℕ := 508636848271948049385895867259207115197234119364123538853069487291721676087663333152081175422205373600610756333280428032
  obtain ⟨h92,p91⟩ := certified_run 22790 120 15 R91 250 15 R92 4041620224747683138877099250120354293482341608369323431048481960122699093559549980328287259316019203783939408077481704641239678486226339018126632247250273962523334215346205857170418298470635666291348519355303495567503464652116428086129040495959285011717368059200997201308870447401688636559039053725310671962575873285782423651374269744430764492156442672816281727054592967017757523553151767386769790867473792586551253664775902885364467555194490422437981938662629426405749776883636171622799604956676884589015108152042116782129423 h91 (by decide +kernel)
  let R93 : ℕ := 53647994981087005270525331519288749037969600870398755929646440628970649984499497518733322511881561510531951400643985408
  obtain ⟨h93,p92⟩ := certified_run 23040 120 15 R92 250 15 R93 4992830442016001714859252427697129916328321432841468312370981549594783838421374668933273389439630132937051884006266562409122351051533968666314562538780814837374431961265343439639418804726305557467622886663871322022010227392566384849241906088749624159791534464963435248023233176202493314560208682650195942414396712290338448225523243690575846819107714468429886603724120755250917535109801423482417151013790598490549105487598759101610178818667602173501436417920283963567858677597797637112901565881909010269043538514559671021392132 h92 (by decide +kernel)
  refine ⟨h93,?_⟩
  intro m hm hh
  by_cases hx87 : m ≤ 22040
  · exact p87 m (by omega) hx87
  by_cases hx88 : m ≤ 22290
  · exact p88 m (by omega) hx88
  by_cases hx89 : m ≤ 22540
  · exact p89 m (by omega) hx89
  by_cases hx90 : m ≤ 22790
  · exact p90 m (by omega) hx90
  by_cases hx91 : m ≤ 23040
  · exact p91 m (by omega) hx91
  exact p92 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span93_100 (h : ∃ z H : ℕ, (23290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=53647994981087005270525331519288749037969600870398755929646440628970649984499497518733322511881561510531951400643985408) :
    (∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) ∧
    ∀ m : ℕ, 23290 < m → m ≤ 25040 → ¬ZerosAtEnd m := by
  let R94 : ℕ := 868153568795525599738918588727312759241192057987818103849459453633990628257576511378735705001090071443698161866854367232
  obtain ⟨h94,p93⟩ := certified_run 23290 120 15 53647994981087005270525331519288749037969600870398755929646440628970649984499497518733322511881561510531951400643985408 250 15 R94 3493802713399438493493542092407766415523419076767180887047735667029475463559137710594189020468582879522178831473623520794925985157428431254554278624814706563267700126797001851902082787826115496321947740217316276085578207856258434770845815612663803090240060650421303984779984553831332644640959467103572428683371044283250785512807558313176691442634907931050862306614860636204251763482726155675155532012015251986959124307432546531040870960500823286265391249516217954008240720263763766053534928456031885020384846442002071410738945 h (by decide +kernel)
  let R95 : ℕ := 337229697535236738572127379757384983210968004255297600837128380636594113095100659450113690316143997575624861843411959808
  obtain ⟨h95,p94⟩ := certified_run 23540 120 15 R94 250 15 R95 4012901307305973848782151005622783493418241203738870950198266818706847002183670177775126052339307492558573220378540423480919633119033012180329413413037143538908799196042465887967250824216134275595941549580343231964901067069244591075576454720827730428225444414234996453257101684837486789464819859056866188697733865982779375968211867743791444790174711818387165931239091216273171479368527329154059628826751306487670928622051794586036979048445605128714381030792141826251023237321941374427276158831765652060446995695689949606084870 h94 (by decide +kernel)
  let R96 : ℕ := 723315386259076445071473645662211993616352675686486947686758640718077070423716739708950248827290480011808092163391094784
  obtain ⟨h96,p95⟩ := certified_run 23790 120 15 R95 250 15 R96 6473032981612800775198351852109717199750997955313699229632889239349431637487572735368044398664337178895740608685964874445449037461959120797897399795230569113131659267126911428228773107718372350885838975657034760624299336067952685926566744262875417233200842966400179120599614158600850314929897467057199681064014344103973588206902434418436213878987283375384111791333555391480755176129454811538739027250511993153558268127439763364663666836710861708411746940973961073189136451205208913246111254867647055761929053544264039810500353 h95 (by decide +kernel)
  let R97 : ℕ := 764401087970282804032556608192478404878931759932433578848413517942862643155460996190717098014712563027941078709989015552
  obtain ⟨h97,p96⟩ := certified_run 24040 120 15 R96 250 15 R97 1998646772366007954955783361046178276178137844204114934265602805967103426460422771724617548607319778412779124861803455532819245448758445350261745991608851486047465709763688947405387955616851302181741903278134731331075973014325553630487943084834076629815462901042672851200809121172842336727506273510920857023783311470331935804321550752397038336349950102513854497350072334087067037025540595748773318736059138956924962015999652526136400584904170393921623086554148647837847111386724021418264202133255837940095811023329480763589018 h96 (by decide +kernel)
  let R98 : ℕ := 378857907319642550511436503119750004804821061263698585923541150123686710355269121145578695136159588572435822291500138496
  obtain ⟨h98,p97⟩ := certified_run 24290 120 15 R97 250 15 R98 8443839076338769273391661082722740943710540302291991767710768074888707929944799456895660028733294187240484081568658141129081555567280014568681785449337386807971535964202215233190021112192904949928890611054731647841217240179103618556139532356252635746896657218092499987628106233247483437382035479237674803165703748978336039150208044357492238218400579337079051215480633166627487422213400047259625494957237907199800480289087330677197153876174117020353962646016731777898934921635389110425380336592207761661113055325783371861230223 h97 (by decide +kernel)
  let R99 : ℕ := 142551178014051362649928892568314616475797569538278006266715874001417128381820303253827365504552596842203743395810115584
  obtain ⟨h99,p98⟩ := certified_run 24540 120 15 R98 250 15 R99 5063089113713016097522132805128076662570633720800009811462253202704474406913327392569093521147766453575371233576018866580578202081520673639893064805936880559018286489629837723483540401667906441055448038775931522980919816366126354685195219365778692251019561622502149061945202936393591396901835008924816747403782755585533251275032027582210643485633603357236633981350108508709124965480964213421032964216257542875658327228496972320538077593368873442494802845843153577014363864074146700766320904456772455934124341753155501586727170 h98 (by decide +kernel)
  let R100 : ℕ := 129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688
  obtain ⟨h100,p99⟩ := certified_run 24790 120 15 R99 250 15 R100 3478489019346685189206122203211628881382979439734824300045754471430581522306250789783069526426381523125885987185642671458867756593474712688118163228404781567405470688360800799927898912645957815978018084813746428148369935841216676134573698174087616050826732274192556771567501876158550999272190005973233641904736156448138572696655018272719412801034641025462198442860701845654224540961549591365414102800190776818292779025252303054541035317869584892151895082409611139580629201160374919100401962882671333793458643294578677832061065 h99 (by decide +kernel)
  refine ⟨h100,?_⟩
  intro m hm hh
  by_cases hx93 : m ≤ 23540
  · exact p93 m (by omega) hx93
  by_cases hx94 : m ≤ 23790
  · exact p94 m (by omega) hx94
  by_cases hx95 : m ≤ 24040
  · exact p95 m (by omega) hx95
  by_cases hx96 : m ≤ 24290
  · exact p96 m (by omega) hx96
  by_cases hx97 : m ≤ 24540
  · exact p97 m (by omega) hx97
  by_cases hx98 : m ≤ 24790
  · exact p98 m (by omega) hx98
  exact p99 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span87_100 (h : ∃ z H : ℕ, (21790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=46570033588366873400328054747928404320872555223777712644921353617092448292931256716825155033419194432834172309127299072) :
    (∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) ∧
    ∀ m : ℕ, 21790 < m → m ≤ 25040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span87_93 h
  obtain ⟨hend,hright⟩ := span93_100 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 23290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span75_100 (h : ∃ z H : ℕ, (18790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=799823605262764452571480794353188809828173488119834196991834436726902279202745500587619509316740041111978598019463380992) :
    (∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) ∧
    ∀ m : ℕ, 18790 < m → m ≤ 25040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span75_87 h
  obtain ⟨hend,hright⟩ := span87_100 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 21790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span50_100 (h : ∃ z H : ℕ, (12540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=266977368450566817993593018436583727915609251881142878134187928205117762788218151590044174917817491310834428273340973056) :
    (∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) ∧
    ∀ m : ℕ, 12540 < m → m ≤ 25040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span50_75 h
  obtain ⟨hend,hright⟩ := span75_100 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 18790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span0_100 (h : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952) :
    (∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) ∧
    ∀ m : ℕ, 40 < m → m ≤ 25040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span0_50 h
  obtain ⟨hend,hright⟩ := span50_100 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 12540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span100_106 (h : ∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) :
    (∃ z H : ℕ, (26540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=193266893970209154240066489298122651083245605265056376897909522769807979608401076236370254682762232642914689159169835008) ∧
    ∀ m : ℕ, 25040 < m → m ≤ 26540 → ¬ZerosAtEnd m := by
  let R101 : ℕ := 880917523564697731252787917055066158119365131039661395006140333851068411626856693812498878887760655012847727546239811584
  obtain ⟨h101,p100⟩ := certified_run 25040 120 15 129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688 250 15 R101 10450076231899119528735032956017105092838525463192626340207256836088701637257720071373772062152582795894147446889900000206465516656725299463448980785474941524264827896321790368911491364843777143627975183591218639095147216909972975211303646763848774193756077198030650370768052910029800507493572615618143679177913505259346965830625080803204526177712919587220556531584367114076288842202867781809159529312306967958101509953360538670079141441879051327715669138797031068450760521584084886124248423991537910668816529572467531707483407 h (by decide +kernel)
  let R102 : ℕ := 241130938871026822750673419448702229075720569248677083423991752614246326261410243507277217260617870140992141186167734272
  obtain ⟨h102,p101⟩ := certified_run 25290 120 15 R101 250 15 R102 8958946253244563037901403529626873648690033310587708411207728314951326534482731504784061746955388412340675521523850490314617691262888664959687933082722756176712267960335612988992350046520807684488213354250065098627086847724787596120000581225725712408500852836746221234320067847339460202961030315491871736258091847596256788518417990726618749248749116426784042777871992775872497481572351361291872574595262790535607681985550895022089103023255486439384521190365485388544919804006155293786967110423830376737174013276788381393765512 h101 (by decide +kernel)
  let R103 : ℕ := 140276670350312242020805176484443298532888811301094615781302157369195971158810727860217401873410252158531331745439023104
  obtain ⟨h103,p102⟩ := certified_run 25540 120 15 R102 250 15 R103 2534177555984235007024264133145050048122577502061293444855017685498408985785013801430687522628542301283464378551726146908364022673126919892707420395745704250011788539779024611237695129451413627536125603602120428952446375120023714202178876083941338832681171607866735454064811552630170603766936955241602547313637252734712130448342943150390495304601693988044308216514084579624474972402594089991319435332513004518076449759701480509324796869864685214355277197130934746024152910452126969656103710441998222439375337321789293475317257 h102 (by decide +kernel)
  let R104 : ℕ := 309622183738147805222498251302889675135843097407320280355402922361945070965043749527393827273803031080436011385661423616
  obtain ⟨h104,p103⟩ := certified_run 25790 120 15 R103 250 15 R104 1007129637889782339186606736004356336671583360742545213292786873001242061156554648278640023973256238285150803685582287506217992326647419919238443261031517889478673686238938347154545283947494309603255597083675310314842032929488597824016299742946271509972855745441359600784748822411056310816447914608639379337192233875434090099705094416897648913772740580394638613327374967625119559722011608611522243944829857938380806866917403491001146973138523733942583143928290602665962926668915142311104687437539655528095318762465582876328835 h103 (by decide +kernel)
  let R105 : ℕ := 85748532316934864441569404191208504262741222391662819555067357069635469794363834916805358562478615074740303413920137216
  obtain ⟨h105,p104⟩ := certified_run 26040 120 15 R104 250 15 R105 4001134123572774012431212291837579766566135760412976376251140607635749774242621391234811113231584009002116994221631770535878179028441051666109478363723438356925738571853647823188655354174334975242033289895862361219250464693983326216923797258959081751875976088943865769882876141945050112838459803158195922168737075071159782649069756411683691543435413700956973524699891243198206181607234704321031351375343876425720879967988295946702589282265968230779920086227168498039128115413994385220199545067624601874617740989164109617465857 h104 (by decide +kernel)
  let R106 : ℕ := 193266893970209154240066489298122651083245605265056376897909522769807979608401076236370254682762232642914689159169835008
  obtain ⟨h106,p105⟩ := certified_run 26290 120 15 R105 250 15 R106 9946497219985469202529594459462020206102332921782409099289498084453548817855132889699199008004304580856434948516007667349086040316219870520558881378497634113395956408377284157117708660298208083195186886372730728730448246388373711348399590718756874070697830638690087461142476881822578831583123088634980730805412912534158384149125884990642812117634775779197670426101544857551392693013241165097017465275850085917596501331535774827179109387383647136575218823968092481449801144207103557583880696351152431216595051663083932735294721 h105 (by decide +kernel)
  refine ⟨h106,?_⟩
  intro m hm hh
  by_cases hx100 : m ≤ 25290
  · exact p100 m (by omega) hx100
  by_cases hx101 : m ≤ 25540
  · exact p101 m (by omega) hx101
  by_cases hx102 : m ≤ 25790
  · exact p102 m (by omega) hx102
  by_cases hx103 : m ≤ 26040
  · exact p103 m (by omega) hx103
  by_cases hx104 : m ≤ 26290
  · exact p104 m (by omega) hx104
  exact p105 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span106_112 (h : ∃ z H : ℕ, (26540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=193266893970209154240066489298122651083245605265056376897909522769807979608401076236370254682762232642914689159169835008) :
    (∃ z H : ℕ, (28040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=344894840489828223760484136496104980387243581163009534796292322156212278724100564226200431796725222885259622918345719808) ∧
    ∀ m : ℕ, 26540 < m → m ≤ 28040 → ¬ZerosAtEnd m := by
  let R107 : ℕ := 11266378600765983596206949930790890615390521996795290760625838782936275740387698535430405181648711809987378294768533504
  obtain ⟨h107,p106⟩ := certified_run 26540 120 15 193266893970209154240066489298122651083245605265056376897909522769807979608401076236370254682762232642914689159169835008 250 15 R107 1085143260090687821403646393879559333464708511576392702464133524407090850467995708786961159645281034286203422660696288663255463078653636399045577170698666508499822141602125540053211858316085017541741050320615911083113004801706251938243249001160286373288360560715071668206409437062902997929988819153375720216942906576248145547541787513007182195735918715976780681723974306795405608362766310176992751296003577165662032525168672622762206606727701734762674016705760097901220003870247242962362361836543259765804188423237191117884289 h (by decide +kernel)
  let R108 : ℕ := 606672003215308687111108304595132958187125481339718832904733222361958521245267446877144774781646003028439823233406992384
  obtain ⟨h108,p107⟩ := certified_run 26790 120 15 R107 250 15 R108 4566620635406235012638824830563461170448007272070330722527680394423528253334185801464444482299338174375425997948572167292859812356051664713886269022371150873031717438394935092774877716200058229415289453932099141004567446108114656265392875472876221633635360386835493824831018460383272060089929138265468539801064407681422260185786270569462077014565859014146226507976795589849318334256753104891017096121964071758634055197063764738832771328671232262324600895115099616156093179995306919347967015679072654006884662886468291678782342 h107 (by decide +kernel)
  let R109 : ℕ := 247598506389205119566744126689319484578803285372186971706676242677459149925298029973047524627451955604211383909520244736
  obtain ⟨h109,p108⟩ := certified_run 27040 120 15 R108 250 15 R109 2037346137896126302078250937966067220398094292720495072728242369655268020624829557973624664805551663025969895672324323517822590369012218210779576177158975466172853032149475627077767345291112793838710856013210881379402487512173050025746083558675352591967803245233887770168622445783216108017732047235567126671911538236902040934517928164557225050831868634286860465141101980414298250381271175353370358959516435214490167840750230468797764745784288508756361843042351399725931160236328565873971003818641159984290577664889835997383178 h108 (by decide +kernel)
  let R110 : ℕ := 117740830855842432275209132869331989959521697321033219837032798035942362321752403357202265814629157214141849927923269632
  obtain ⟨h110,p109⟩ := certified_run 27290 120 15 R109 250 15 R110 1999158813316706028477336456453873459359171820293530225419882427101996944083099751621668228077746194646008913125477297704459850823020820999780733495114322387576899480881175167295819597223201143769164584131517766718681313483564055879431027927856527427829884618796534721623372289681509226561090745887040900507980306609889509255463677914797840556735940293767213683225571032035554477190367725542311012667199709275384184225163576400120698757142125275590485870530795212299833933721883878407279390348482115857916645549930167213768976 h109 (by decide +kernel)
  let R111 : ℕ := 103051588767057751372639027324540967030266012746166996804789977443234158259220258451814729771072863460856208213625798656
  obtain ⟨h111,p110⟩ := certified_run 27540 120 15 R110 250 15 R111 507847495915244795909997020835061705189378371796338016193022948305848888537393131153349229991203886381666839497959096631204503895466562609344782531995868070416315262328207721919451029552025479091193873394447237599061189110358749736084267819164310308202717400850036980805758296791775083537225137668622462543487973615538535701642897904282126367710152755419132524276924155302623772347005071514077764943928188390804231359073542515639634511111359349461336243824548026471334132057781720643650287543040537777271563878042772810434954 h110 (by decide +kernel)
  let R112 : ℕ := 344894840489828223760484136496104980387243581163009534796292322156212278724100564226200431796725222885259622918345719808
  obtain ⟨h112,p111⟩ := certified_run 27790 120 15 R111 250 15 R112 10976774467938209460486536720613623453760789619708708395382711211478256723993654260646178716371229853885205648458716406043057669723516200609349172426499111662314915358136933796190455603934542094669131257980985292283745963708470724370329645568831635932209673729780230427353847287676825779382993722032239009752402625233775044183293294719899975029312029734521992792051701541835454914242916571638613113064433294835959114465822623816445245637825644458919313750630531484162871613650975480229067983859044521358836737110437163721410061 h111 (by decide +kernel)
  refine ⟨h112,?_⟩
  intro m hm hh
  by_cases hx106 : m ≤ 26790
  · exact p106 m (by omega) hx106
  by_cases hx107 : m ≤ 27040
  · exact p107 m (by omega) hx107
  by_cases hx108 : m ≤ 27290
  · exact p108 m (by omega) hx108
  by_cases hx109 : m ≤ 27540
  · exact p109 m (by omega) hx109
  by_cases hx110 : m ≤ 27790
  · exact p110 m (by omega) hx110
  exact p111 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span100_112 (h : ∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) :
    (∃ z H : ℕ, (28040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=344894840489828223760484136496104980387243581163009534796292322156212278724100564226200431796725222885259622918345719808) ∧
    ∀ m : ℕ, 25040 < m → m ≤ 28040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span100_106 h
  obtain ⟨hend,hright⟩ := span106_112 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 26540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span112_118 (h : ∃ z H : ℕ, (28040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=344894840489828223760484136496104980387243581163009534796292322156212278724100564226200431796725222885259622918345719808) :
    (∃ z H : ℕ, (29540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=440177157623880884063621577401962262551227041020447630781306522521356192927613660955828263947543583403172827332350050304) ∧
    ∀ m : ℕ, 28040 < m → m ≤ 29540 → ¬ZerosAtEnd m := by
  let R113 : ℕ := 961842690193260669085338333666559964007449630961425902534280402825141634682564288949434124122048627658234792237347110912
  obtain ⟨h113,p112⟩ := certified_run 28040 120 15 344894840489828223760484136496104980387243581163009534796292322156212278724100564226200431796725222885259622918345719808 250 15 R113 2979144472627020669913397847646833496665349822044172626035306055640922034698943780791683325803562843483535542507155469652584371490086284976007162769140292512429185861689552123909879136600433807697382794894445264284483795036287166532028803238524158073733242677324875134353870093316364571931431616962728574407907906648847581463093412566035591799015345948136623746358074729007176776256012496806750776328640810002345426122297962079986437030659182466594288166019334273738874972040622507927829537019286135040761260756258249049671809 h (by decide +kernel)
  let R114 : ℕ := 946013810453706085155511926315193147593627695746965511445649575833968609299916870660140449704715256147571816652863438848
  obtain ⟨h114,p113⟩ := certified_run 28290 120 15 R113 250 15 R114 5489416205666645194277568745004418168521451412912673596376222277022295055327336949959410338923730703735094282391128450067007846659623066061909985067688679508241055748918866194108754023356094847616540781937773783093937141737484321528850983799329431895729863107974446618550864155150704398974589177905048058210267765804955510045402429490310321714540156978078751406896287277854222327380376473189369299300781164442828729942829426736773118048056590110254691008250843372876801053837364529389835963668287368164022390128008786264293762 h113 (by decide +kernel)
  let R115 : ℕ := 143224742963441250060737277188459314507659564489354812914153185943045039796291698373397936670052376853050501446861062144
  obtain ⟨h115,p114⟩ := certified_run 28540 120 15 R114 250 15 R115 6131494881518432637532011708538414103228598188674021184738788833508855049610635583467206272572591481780579714051860537558996589684329073418830620338402767129333260786244994085649058213469371750989181564244121442540274721123890965592805240736649858097069036490798811411142570780504472627958306606033444353178277759491294387675427827315492091868303809586232152414222386604996813992899825213657743900460912206183917410870929293353379233141022305163449171716166906590367186245724184678039287225589777037594220427955678264747475077 h114 (by decide +kernel)
  let R116 : ℕ := 129289940059168639915816429235200897203467936394554779170171902845942403963745862095460666541831595943364419864317919232
  obtain ⟨h116,p115⟩ := certified_run 28790 120 15 R115 250 15 R116 7456529892345386116146416575424893556495827662358532870081594551995521307762742405783492701164700011963056619325999036104828489351688739604563820157862945416607004092947422189365511370216588905018123550552159454425422327781286795542637342836791656728996937237043307204530219889808072983320658068496879900943302809436207864751985279049114968919987131160348575020545183665488965605088676421215248663666235881553456569982428034022545228551212422461827734235952672369377702937308441203543236857537998499327568434588942926224721037 h115 (by decide +kernel)
  let R117 : ℕ := 823874530467463186741051262285800861889301749243851132854721536697812976367124195477797998313419806599058317661842702336
  obtain ⟨h117,p116⟩ := certified_run 29040 120 15 R116 250 15 R117 1018689036300122589303177026271657950576802940257164108521457685594276318657351100614029479421200137089090271232455797293948373311261711831766676182532569932525399567752967104409688529460181416831770850167020425575191809711790826094516348048705757415952226009617320905230857536507278877439199613027333787894715998572424756361661837321781817598739808737090094303557376081899531741060164108065456738162880898714197111130816255583559508216250711739520766153045488852315666441221371090031852822012064150949166945091758707942916359 h116 (by decide +kernel)
  let R118 : ℕ := 440177157623880884063621577401962262551227041020447630781306522521356192927613660955828263947543583403172827332350050304
  obtain ⟨h118,p117⟩ := certified_run 29290 120 15 R117 250 15 R118 6991262110039533320681921564045724746571286364129803589674943659176434381199912897975160886670872955717095341691612360070062227950799913725690493513257017798857692097681282080505658022076473889927084886632616717392755483087557534150283146082605797801527529223804950834858926737335318574208233159615302877007756857456980826825486613230153795232679918684591918212620589955626937699223935486687117537259148405169509762564626633454557645014138601284545035236559724655029720713776652704757145802193227719203372767727706166593078793 h117 (by decide +kernel)
  refine ⟨h118,?_⟩
  intro m hm hh
  by_cases hx112 : m ≤ 28290
  · exact p112 m (by omega) hx112
  by_cases hx113 : m ≤ 28540
  · exact p113 m (by omega) hx113
  by_cases hx114 : m ≤ 28790
  · exact p114 m (by omega) hx114
  by_cases hx115 : m ≤ 29040
  · exact p115 m (by omega) hx115
  by_cases hx116 : m ≤ 29290
  · exact p116 m (by omega) hx116
  exact p117 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span118_125 (h : ∃ z H : ℕ, (29540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=440177157623880884063621577401962262551227041020447630781306522521356192927613660955828263947543583403172827332350050304) :
    (∃ z H : ℕ, (31290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848) ∧
    ∀ m : ℕ, 29540 < m → m ≤ 31290 → ¬ZerosAtEnd m := by
  let R119 : ℕ := 849908554546245091379221325503488211949899648673888914919366621062559640024814479219421803737497671358120503223848534016
  obtain ⟨h119,p118⟩ := certified_run 29540 120 15 440177157623880884063621577401962262551227041020447630781306522521356192927613660955828263947543583403172827332350050304 250 15 R119 5511747727735979517887891069971101550694236260589891728748287050680553324945364952722157064721386259539749933215163504810868441229866935908566354662679949915531360531880695987430414982966735262272860319363165989261627164573291902471693029787053485766832671640423269365815767014277647149894465858911841124983599685725829091415326041552462867977646315762732607118545327319534374534188381262370780293647892677754802715319060436409361043672827755167117691146874890816086998764852241511917395567939089856769721517302660369744134920 h (by decide +kernel)
  let R120 : ℕ := 504193134231297199940295306220064395254963012928372924820768634082306108070382225195609526811480192987097729714444304384
  obtain ⟨h120,p119⟩ := certified_run 29790 120 15 R119 250 15 R120 2510030144189537296178225193017514503903214380423363565105117670821241582970753950914944269632694047233612949034871905961249938713170337003502005343375430111904945734517838773211179487968946941874255749473222730544520581707987209429758860877585602143477291313900869893539000356957073034081180704230828498710669185135253940602451135614879424742368941725890844861630218341714039066551565319416284319298879202130762055731579593381824964593730295630477483575971121403497172989438775384596661174323178016326012252394539719470616193 h119 (by decide +kernel)
  let R121 : ℕ := 330807464936364553872300044050953947852646317511479187309418067953534415160917147789978536297741897730909344964733304832
  obtain ⟨h121,p120⟩ := certified_run 30040 120 15 R120 250 15 R121 4559669675939305105527436541424459076381500034273481934681922843709572163784729304827302462834074442534051434251340101813383386565024054530596194257462182025005890689281445821296164139487719047836141385466900309564921018116661410167068402429434050930918936958462375109603358303085963861184436921501401434697595142721184553631024823107602781087602801943149334132578952503297891616708620082136908315598640565530213243422108035704096707402718531518996714044970725959540687215658658838640678663475634523254309729924627255471014934 h120 (by decide +kernel)
  let R122 : ℕ := 678061948913884629745303092679971553505438855440350542680251445751757166914419659535238939045454961694043234560058064896
  obtain ⟨h122,p121⟩ := certified_run 30290 120 15 R121 250 15 R122 3044604382750623609748888614464489426990253750485303789961361086213652869986378700940994198473199254703945768019667578572387825949349621142772176887471756559525315790421807129511098090070370174073853842987040163249898083398342181755064009383599677216925184289814073773963687636583998075936487516989077103429496507800675083447556436117809245675161231226691553751041120800799637164453852417253373480611295364023441037599010595780099858764012210605393114578113744123782631402941066739974967503005332221421313805067125813923627394 h121 (by decide +kernel)
  let R123 : ℕ := 167137657284006521738617650053415427885995345388448252052062735302354560826551955881381128096526112215593310644368048128
  obtain ⟨h123,p122⟩ := certified_run 30540 120 15 R122 250 15 R123 663018012704393669501529262326113531647453674205940281987707917578699050913806473023819823813642299461201001553944829220355749307340013976159023619389168090979110147139241424536698667974572529843635916717711532273523178407700220296745741292647229326880124782176898653718111441479057425470584609933590931794494268588560096377274782867559653862363599100853987547127460042894674833035507344591281809747291003752275684000964583469072905271009379745575446337991859199721244759908760537542563506156494033481045877646415217417079428 h122 (by decide +kernel)
  let R124 : ℕ := 12564534707709837074503532222017704296113698583366937532886713676815107888276657737064743140227548244463598355519373312
  obtain ⟨h124,p123⟩ := certified_run 30790 120 15 R123 250 15 R124 7441165842614402593580038425037664861670313777874671416064137485693182752618261396463713992067413956205454409439455788702640594070726854148183042879166149259278249578205239166547387923656782758948155076728250918796420937676336371794004547321108132457973160777684798860766381970646111446871686604744122735160369089882672160678762265995049841746689612927277766269024052295679115159863886319093299808897981281715569064983503288352170823503294448256914782626797468371264720305379872411773817368743628736032255790980389158032395678 h123 (by decide +kernel)
  let R125 : ℕ := 397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848
  obtain ⟨h125,p124⟩ := certified_run 31040 120 15 R124 250 15 R125 2998148635315331714345572713675506497975244791463902548662953554912243422012534696420186563722842446799195470686629956882135371962972730250475493425385113355281621542966220661452392622187552728023748849183814139696838617746054582332712294500086331470536602431009067097975724300749174366056468685831749804650410618880820023031195445603547436896270975010247947593459019373897826985112157347117871095406143891401707448529706132180869561595056709690410154978083021150674392538762653176104709052289840685231273190180494792059830927 h124 (by decide +kernel)
  refine ⟨h125,?_⟩
  intro m hm hh
  by_cases hx118 : m ≤ 29790
  · exact p118 m (by omega) hx118
  by_cases hx119 : m ≤ 30040
  · exact p119 m (by omega) hx119
  by_cases hx120 : m ≤ 30290
  · exact p120 m (by omega) hx120
  by_cases hx121 : m ≤ 30540
  · exact p121 m (by omega) hx121
  by_cases hx122 : m ≤ 30790
  · exact p122 m (by omega) hx122
  by_cases hx123 : m ≤ 31040
  · exact p123 m (by omega) hx123
  exact p124 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span112_125 (h : ∃ z H : ℕ, (28040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=344894840489828223760484136496104980387243581163009534796292322156212278724100564226200431796725222885259622918345719808) :
    (∃ z H : ℕ, (31290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848) ∧
    ∀ m : ℕ, 28040 < m → m ≤ 31290 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span112_118 h
  obtain ⟨hend,hright⟩ := span118_125 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 29540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span100_125 (h : ∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) :
    (∃ z H : ℕ, (31290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848) ∧
    ∀ m : ℕ, 25040 < m → m ≤ 31290 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span100_112 h
  obtain ⟨hend,hright⟩ := span112_125 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 28040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span125_131 (h : ∃ z H : ℕ, (31290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848) :
    (∃ z H : ℕ, (32790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=85084864865252179409791775551453902123280924697606121332761419035202312157803263492372078241819680117139594636938969088) ∧
    ∀ m : ℕ, 31290 < m → m ≤ 32790 → ¬ZerosAtEnd m := by
  let R126 : ℕ := 21669216210817914162209226293209005902024184821109832015704953862344278092379714640468517013323399848260651576683659264
  obtain ⟨h126,p125⟩ := certified_run 31290 120 15 397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848 250 15 R126 4559389104681610109153050356993672115462455044773940406401111885329945426312294233380907353695379136668389316967091389420208441858258187108074812515515850002299221058451007058549487201959151890573861803587716418386509485940783858228034475321843001117419910122939167065392139760374692779323887853919819295537572423510955659489849827877833393752307636785600436955682982723896278089285153063177177652722771476483170899303762342652228500535777696275183709097722975158306203235251488204092884903529877630642943516118445903363342481 h (by decide +kernel)
  let R127 : ℕ := 639378808559360876446308745165891093471793308590892396773265158803625059433985956586150390940674523207733815016331149312
  obtain ⟨h127,p126⟩ := certified_run 31540 120 15 R126 250 15 R127 2978993178761214047078140313028769604556803378938883608189821901461194816606628328471690199857971451662838745413444527287934853465079385633383172291355407389492569654951216814458598915066430267563995020054657357455223277774711424703159600464284696550523043929471775051396419688184146666486622422062151182917707642973695522925317078845247640681482515904333242267931052927779817602067333559118047013259457334075238395285761600699658446225847947226011864887841912699209458187678093063113430786870278400432216643201832226572600963 h126 (by decide +kernel)
  let R128 : ℕ := 476758576059030270051974240688745454374876027681313761207989852681112925811225499404545708406123448685435863297974861824
  obtain ⟨h128,p127⟩ := certified_run 31790 120 15 R127 250 15 R128 4465887774140732568581886809642145367471434035371461422739186850440910772203969423020870715272094021966088061383158335382675057543568758901093588524650663299846300459076783818718243502966767598932684081820803376802720181232945159801143490325055926688953373249009204649298734499743548995134258222228693456017700285416807686569487522466030764023505422694991399208520058246441743796067961162499131336852937299054081013566094607708913082080614813323777627570762958114035610961383158778758581637287397801298360472208186172818637464 h127 (by decide +kernel)
  let R129 : ℕ := 244637597807506167141376893657771489947955996839740897803356159066095835182834638384318274639580652095403581058104426496
  obtain ⟨h129,p128⟩ := certified_run 32040 120 15 R128 250 15 R129 1545478550440144710193517302215010570525872968632155859186690880097299080981073350474344552633227763785183449073714473370711390405790598703015664776159809080258967400977538601435863163271008120267098770863017411577886784542280639368815059359924954567718414416756607339878776441376062581662524573999308981148539809718408344829740331468479894497426285817667850582829805977979007601948222023846038919721454655235522831842696489375285605719958642498308241297349777279023488585778015827488958536241714825857921803824230943418581138 h128 (by decide +kernel)
  let R130 : ℕ := 53898561178951504693213768994169790524291054447226861991025814007559010623007056803210993688748862189487958938066354176
  obtain ⟨h130,p129⟩ := certified_run 32290 120 15 R129 250 15 R130 24831837586148265984706474647295272739163518605685858894202655522325634859707755129890612658516378308114755528119967371196895148453237382942936271392221775979313763608047605602901830547084530301698865341245191619804742269963518735799847128766553640213725175715646066394198018132522914989514467937587260554953790707960666716812235752656840781303445981401174327860083870483943851027686158284700964040935320779052385120436715165226675455649888133529020621737571836916761918136969182299797804397888109909466681815299138258705924354 h129 (by decide +kernel)
  let R131 : ℕ := 85084864865252179409791775551453902123280924697606121332761419035202312157803263492372078241819680117139594636938969088
  obtain ⟨h131,p130⟩ := certified_run 32540 120 15 R130 250 15 R131 2513935048572515566255352955258754328738015703745086518293687315066913472844372976368580039468174004512666593262449817227268771609916347260437441075543195972962279922052238949002931426709645142484387182106293178152647471062755579279463383691727223571838917536361367856417613364674651606349356132134581395825898793153281685098950090912970241150171421554560588356595458938663476235739152969031037099211525369049534710618431845217526000994216218774124699508456515193705531367623368774665996205813275193770441439947370390964372367 h130 (by decide +kernel)
  refine ⟨h131,?_⟩
  intro m hm hh
  by_cases hx125 : m ≤ 31540
  · exact p125 m (by omega) hx125
  by_cases hx126 : m ≤ 31790
  · exact p126 m (by omega) hx126
  by_cases hx127 : m ≤ 32040
  · exact p127 m (by omega) hx127
  by_cases hx128 : m ≤ 32290
  · exact p128 m (by omega) hx128
  by_cases hx129 : m ≤ 32540
  · exact p129 m (by omega) hx129
  exact p130 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span131_137 (h : ∃ z H : ℕ, (32790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=85084864865252179409791775551453902123280924697606121332761419035202312157803263492372078241819680117139594636938969088) :
    (∃ z H : ℕ, (34290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=93205212859047142992833235841472750369066416318628371951002983662220227441435747217886626073639099570482384856697274368) ∧
    ∀ m : ℕ, 32790 < m → m ≤ 34290 → ¬ZerosAtEnd m := by
  let R132 : ℕ := 196831333414806295372824052500800986225650857763888109260654088496850440903031515794435633225864098021974137231055519744
  obtain ⟨h132,p131⟩ := certified_run 32790 120 15 85084864865252179409791775551453902123280924697606121332761419035202312157803263492372078241819680117139594636938969088 250 15 R132 3021183254353821620974851000964090345888030036671300911046664221173345790878136258694191666979996752445974816745401347386044671175676484257968071144933644956805399911076131011345938923874519716685559514730584566317301676808059101309858381776470351665209543725130328265892064498823518406562977527432146823983623953186287033132654194209011081136199553173618923600353063375742282555068436740636128995937689036318576545707610419726721086355161681310227193075330895657959038548747742832461382777122160611205479591466552443334100876 h (by decide +kernel)
  let R133 : ℕ := 756573001402325902205066927077241348052784468319327358564749337658116681444092843520926548560025270640887059728306274304
  obtain ⟨h133,p132⟩ := certified_run 33040 120 15 R132 250 15 R133 10438458699841074699179422326775157164130834964195722613435108868130752044628524763504637803896828341121596904741830652831798422155382314089210030721403397241230952286504600242531538860633346951439105608375292858828121977901559427810345858443079576798223556643881594873996053313329848713065760769647696549528576106360619102434237662975465294861671809405930589151634378291444371252343912285967704739166422554497369175072299847296507018276560034208070932961495605855751914468266336263178089890254073465645184506393416046766752002 h132 (by decide +kernel)
  let R134 : ℕ := 397633268819358803386271502063921012677984348413984303060779832234802240736231907811550520726985190113662662805255356416
  obtain ⟨h134,p133⟩ := certified_run 33290 120 15 R133 250 15 R134 2487275418777719154131109404827069025387258338195168310360942937370404274147312868914919818875205992151300750833445082830383163306885380833505610887333022713634060796504150486926097859655641733806371330066340417682644037252863020843032176808006700770852485989749400671983682673782505329845656034916907176244459665292908011376587338428468290117539887513380718760555340164768982599265709101120086988777940918161522472639237546484783397441749366338832139496969470040062731829729990057852436892986125322906501213159206144119636357 h133 (by decide +kernel)
  let R135 : ℕ := 63733011169708046008695614711407653235921010995716393335492091673159032908462661736710277115477454679430445340790095872
  obtain ⟨h135,p134⟩ := certified_run 33540 120 15 R134 250 15 R135 4985261780764701775641217143502303417026474070082358561170077952695821027588360663122019504033147759586205246530501836165891500666124849830981102303664796443462687810739234425998385630766395036929189386993813715077028224245211286227312260255886524740805474757915104889140842680828193006746751910324859297679359986406843505347934376814038833431621860277566993289875926511655543196001561948370456162702053370352587924818621343722826719459146667334730017383734722457998015304469857896046032204876314637367582200123426139827028737 h134 (by decide +kernel)
  let R136 : ℕ := 73648671713328092188345218618428715222314364768969564049547072135584491776801961731467550529929771143367440103716683776
  obtain ⟨h136,p135⟩ := certified_run 33790 120 15 R135 250 15 R136 12073353245607532887907911930500257929255301474361429157656212103906907035064878355895799776358424957395681942253722473882840717614288213826091305308914257795403037553590170966359371132208019424525906835449603875506632282480678120013875857056384716521448931271232299855418074209701290868720539089025308449152175526992017776509725683794119463561416414323532868324676786806246514720885618863132066616248645795574127210293826606912710973362271773040743261161416542812652180890223404391364137285589632338032923475934202050067334920 h135 (by decide +kernel)
  let R137 : ℕ := 93205212859047142992833235841472750369066416318628371951002983662220227441435747217886626073639099570482384856697274368
  obtain ⟨h137,p136⟩ := certified_run 34040 120 15 R136 250 15 R137 1529953499524723461433133139477840250529181025018814215839246314683436273021198599517985917455843818710381325720971979131850534014124685332906922731194127674245513800331711793339480890657663262459497149402244634479391869275021782659400652884243194510996223254967715220219692250982790076049971083957171481646023292664878727060263681864992214504731064815062756468253123597280063051743273597586068346172849259014783627937408391955330378442175970299150151055830444640392047371845049632600356151144431067825397601610109809854858888 h136 (by decide +kernel)
  refine ⟨h137,?_⟩
  intro m hm hh
  by_cases hx131 : m ≤ 33040
  · exact p131 m (by omega) hx131
  by_cases hx132 : m ≤ 33290
  · exact p132 m (by omega) hx132
  by_cases hx133 : m ≤ 33540
  · exact p133 m (by omega) hx133
  by_cases hx134 : m ≤ 33790
  · exact p134 m (by omega) hx134
  by_cases hx135 : m ≤ 34040
  · exact p135 m (by omega) hx135
  exact p136 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span125_137 (h : ∃ z H : ℕ, (31290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848) :
    (∃ z H : ℕ, (34290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=93205212859047142992833235841472750369066416318628371951002983662220227441435747217886626073639099570482384856697274368) ∧
    ∀ m : ℕ, 31290 < m → m ≤ 34290 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span125_131 h
  obtain ⟨hend,hright⟩ := span131_137 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 32790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span137_143 (h : ∃ z H : ℕ, (34290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=93205212859047142992833235841472750369066416318628371951002983662220227441435747217886626073639099570482384856697274368) :
    (∃ z H : ℕ, (35790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=208984940841241241430562485876047678609559681290243128978619065440252254574317352626894590619815721402959262215701528576) ∧
    ∀ m : ℕ, 34290 < m → m ≤ 35790 → ¬ZerosAtEnd m := by
  let R138 : ℕ := 3487169770779420594168020101419132406954651698375970330961783865703428268125602959295218144550487673603791929326174208
  obtain ⟨h138,p137⟩ := certified_run 34290 120 15 93205212859047142992833235841472750369066416318628371951002983662220227441435747217886626073639099570482384856697274368 250 15 R138 3982157601553952814626982024280212738076643692652865241706685041348924440010854533344714644542557360290081503464875017864526934984596563208735309339957176063459728072995690931559178564074581804035130400780496522286602425678273008081626276014308953756459793415965572599199761309978846038481572095510501609304360628024791093201792209505196961832400106087029239719742550189110888844382394015673882590517819559604480116008384938527993872049682624767382571176536884156396182344226859772842393887203558271581245982594457974102573448 h (by decide +kernel)
  let R139 : ℕ := 603947040080450615587066443037735658353095385414527634289411265173336641944056796897790583579327678465005961501455941632
  obtain ⟨h139,p138⟩ := certified_run 34540 120 15 R138 250 15 R139 4981028280486796591926059725362721444939076284005681361248010164855319136798981897546335359301568712231872197679882514206179518916174255951395223679562497391521894888547913643824431369656038234490835831773926894569939316895311023433694174728275057857016534957065729396979422109963880747653118404706103299398866850897806680915303824883498686825513060069183566831327402702195167835111730432516255877722173032543861701081022465008154964119638647301620453746164142735805400163541152125874854682325497764182634057861151086721680385 h138 (by decide +kernel)
  let R140 : ℕ := 9299607480919759465428550379465034372174652017866747326132742364555692181589050503960273675351475586250796923151712256
  obtain ⟨h140,p139⟩ := certified_run 34790 120 15 R139 250 15 R140 523098792440213327656484372513799883121624040215124437632910273566703966402073454556444023632300221595801258953857433813465500616562809272074341687666330719270242086194665762171241482259198833706102184183600906722476442601739136588185625385705086096133408454616245788919485096915249888287597718909038272519419414030089690083103538149245940539790808329554530620925474364400744105977163879970144180314487044319454724679097833634729490525580875038471518751749904860423870197132356850642792774022362824216229834083015273222373892 h139 (by decide +kernel)
  let R141 : ℕ := 128915450932694029796173057363997654798978622800328128291945145832911676667030517279495235577945704881033438157569261568
  obtain ⟨h141,p140⟩ := certified_run 35040 120 15 R140 250 15 R141 1599671503156801709802494500296697173764826119004288910334469015372348978794419631594350436395944912024385841373451036605909432657284833588456274936974232202315624106579036654733525257562792487920519634966949497367608169051059547940963093385498637900092085003326006284616427114653093594587642848879965520689265881074051755637532416180861806696261078353881546624278782590812397341109580496649378614300832194266592858428255063571971885259249910484241018769501350677903524031370969556366122114456865696085742206061405099752802831 h140 (by decide +kernel)
  let R142 : ℕ := 145098225364177924940089145719270211190962608580348263446616486202678456928801219170353634366085258268190124783660171264
  obtain ⟨h142,p141⟩ := certified_run 35290 120 15 R141 250 15 R142 5957111417835248613374176010192860012738259495927519051707553293998277499241417789338758062838294003917344248974014047840142068996968391483920705928237493800054253284478036287313069677642507835792260680345270559838200577606632114433724068214040626928383795353320822699736630323187685289615879206301697956296369879144437095184841745756405317719983599806246688543397384417872348158349143833736431091211494385085010039523115418528848043095966563274970218739285033825302282480786882846774356290556570796110587653000480116942324362 h141 (by decide +kernel)
  let R143 : ℕ := 208984940841241241430562485876047678609559681290243128978619065440252254574317352626894590619815721402959262215701528576
  obtain ⟨h143,p142⟩ := certified_run 35540 120 15 R142 250 15 R143 5001057274497138725455553156699818851750759753586059158730191267833198906569003446432679478300089712130868580228746343349969474667384249517580911186743973862841814965801333857705680740282743853708454682010241743588494075993565395954834636666383090958426170270327259030959736376820276444992486435202360422533661114907839275066078908827701903248637341772206754433363162600338936512337101909034415653067735025634168303188666692277056249777239627783849654769633336229944916402515587394837402816702542956243827807814257065922201482 h142 (by decide +kernel)
  refine ⟨h143,?_⟩
  intro m hm hh
  by_cases hx137 : m ≤ 34540
  · exact p137 m (by omega) hx137
  by_cases hx138 : m ≤ 34790
  · exact p138 m (by omega) hx138
  by_cases hx139 : m ≤ 35040
  · exact p139 m (by omega) hx139
  by_cases hx140 : m ≤ 35290
  · exact p140 m (by omega) hx140
  by_cases hx141 : m ≤ 35540
  · exact p141 m (by omega) hx141
  exact p142 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span143_150 (h : ∃ z H : ℕ, (35790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=208984940841241241430562485876047678609559681290243128978619065440252254574317352626894590619815721402959262215701528576) :
    (∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) ∧
    ∀ m : ℕ, 35790 < m → m ≤ 37540 → ¬ZerosAtEnd m := by
  let R144 : ℕ := 871204186500583976693303687230364901006425100012254992962832698991035894823329439373083532975759306632180098474394517504
  obtain ⟨h144,p143⟩ := certified_run 35790 120 15 208984940841241241430562485876047678609559681290243128978619065440252254574317352626894590619815721402959262215701528576 250 15 R144 1019142220597715373756497839158456221587444736909548900209218411318233458401834025221018283076613015013823203469353504326515953123174564165328483391262902818197120354354888564482334760586131179327245674593198476954196260133028967021006797729009908544344789617626140650297681178643906675542155861101847068823776527631186638228827627845155858355089671642633199148158203283999698531086115901620885594584520717366440903961944199215124178623370398234802600065582585581176124681905624615993222460638800987930842029066982414946272258 h (by decide +kernel)
  let R145 : ℕ := 335183148081952665190710792694300315712864574589776944363447908487066283359733327256010051672311729182981214835432226816
  obtain ⟨h145,p144⟩ := certified_run 36040 120 15 R144 250 15 R145 2002916906123110989359284042813574396599245738413269020289004276997481693909186976176787127939750287079383519005713962962474339935909677225335266318872478085903368765356031220603406511634271994253300514407391496409760175298947716660658163877997201045762314378561765675860938482587281652766801520478621034151487734090967890062232587008862533149734497249667747298391198735989085781779494628579894525361598826103677113911565294228666689619990574886055780542518207663013298240838491115197903433821419846342497522710971552108872708 h144 (by decide +kernel)
  let R146 : ℕ := 318401453203090698206698284220253505560004231638877290591142629668644501110530909637881104560879567608989207552084410368
  obtain ⟨h146,p145⟩ := certified_run 36290 120 15 R145 250 15 R146 4965502052838868914449395586548336364234437945834782985662892854925344767136632193071368943496241594704559890477773438928254445822396432784510007114277877890141812226867418931648975034347481269288888836345252984313142674271093673010662310706399159284505261354639910569377733787830247472137327174404353038053382914059860682972808487533936026083312204919411141860491895244322830713903601466894330271573212333247422878107567005708981939682345716806542192368128964016179743205708864064836340436758543697146142170283193608723055873 h145 (by decide +kernel)
  let R147 : ℕ := 215220800558269183579102664688302643358302711863481280378216567541001009742489838986611336574222841623419019687209467904
  obtain ⟨h147,p146⟩ := certified_run 36540 120 15 R146 250 15 R147 6011999130284654192880428942111515366209150643405131177717236323878151124076377959089848317010818276672739076310252208108385560075520155981914763983701329197005547771568582297960790833239373338066204207173691269987620533540525789829867151031828605763015699251453066702381164135999423019056818322232355670559406873933542970847077978427758798366179590535451660479074106270779145038044421274214573101802975653225189796248567375408295202932663020428411490699544271056454746708749091449143982253305913472274765358876654707616533775 h146 (by decide +kernel)
  let R148 : ℕ := 773536242309524347650896355932549990998089267557870950887995750712742673017797353457116681748341699760948186008258609152
  obtain ⟨h148,p147⟩ := certified_run 36790 120 15 R147 250 15 R148 3509268196636959441966652545296523189513506938647755677330854081544318779053818434356365781612645573382518471177961870660263258946658087234985570273906294037731124607454916988488314466401630817355849277847020691443032293191815534885328751378915489190047457905969380224097435645215065486039916323609353826353567974965755602972941049573243399328552810075296892012223353306806678137377468516137778025453428974778523942197453004550872387095156574547702396445446319660464820290168222254390783351048912763317621035702346140115781380 h147 (by decide +kernel)
  let R149 : ℕ := 560544668359892175761167527313690648065405405612977627452398362267532991855937139528046537137784892243749432635642871808
  obtain ⟨h149,p148⟩ := certified_run 37040 120 15 R148 250 15 R149 1994954624976380906764427430164129001572069782349573481838786952339457465897569742314664896942941885771872088601464029582085551486547584360573485000878203061785237395130265468553973113574956348857821537150284860173976000271490862037468537818233345878636380119315634267564127691819038604901808451659172316418731706709099042568967515095816138030082720334550204771040792652882006940530544827939695353871801813640829529453141702622222848378249150879257076833944685085680629430067438187978211690124901880250105086973091355140656539 h148 (by decide +kernel)
  let R150 : ℕ := 660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384
  obtain ⟨h150,p149⟩ := certified_run 37290 120 15 R149 250 15 R150 1526292097233231795223683763790662664638279698966495644164396326025787871218131059031867071593147090388085609835575742708571535767002326577301110643879879250982439586055543619675009296972225694534405525434877954846107069168885852346158652074173143765491179570024239953082836822821838364854527212609736334436866489316885421310860184348556485012616230283235756233306484707310395681817303275131961320341643370002338142127814321451965402754390145558898170623123986722414354764457835323750201748888007768850628577230245317711004673 h149 (by decide +kernel)
  refine ⟨h150,?_⟩
  intro m hm hh
  by_cases hx143 : m ≤ 36040
  · exact p143 m (by omega) hx143
  by_cases hx144 : m ≤ 36290
  · exact p144 m (by omega) hx144
  by_cases hx145 : m ≤ 36540
  · exact p145 m (by omega) hx145
  by_cases hx146 : m ≤ 36790
  · exact p146 m (by omega) hx146
  by_cases hx147 : m ≤ 37040
  · exact p147 m (by omega) hx147
  by_cases hx148 : m ≤ 37290
  · exact p148 m (by omega) hx148
  exact p149 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span137_150 (h : ∃ z H : ℕ, (34290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=93205212859047142992833235841472750369066416318628371951002983662220227441435747217886626073639099570482384856697274368) :
    (∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) ∧
    ∀ m : ℕ, 34290 < m → m ≤ 37540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span137_143 h
  obtain ⟨hend,hright⟩ := span143_150 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 35790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span125_150 (h : ∃ z H : ℕ, (31290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=397271324421287985029509813922910404195175945871279938807058400853796076922579846993870970939832997788444684352485326848) :
    (∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) ∧
    ∀ m : ℕ, 31290 < m → m ≤ 37540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span125_137 h
  obtain ⟨hend,hright⟩ := span137_150 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 34290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span100_150 (h : ∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) :
    (∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) ∧
    ∀ m : ℕ, 25040 < m → m ≤ 37540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span100_125 h
  obtain ⟨hend,hright⟩ := span125_150 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 31290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span150_156 (h : ∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) :
    (∃ z H : ℕ, (39040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=787821891505669876199390911688787503202499669522179040694863081127120280111882960132968086662114771021949787017643556864) ∧
    ∀ m : ℕ, 37540 < m → m ≤ 39040 → ¬ZerosAtEnd m := by
  let R151 : ℕ := 288506546831643033961452223807985328568858082898681733473005133355291631263225813309464277058696653376950623630432141312
  obtain ⟨h151,p150⟩ := certified_run 37540 120 15 660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384 250 15 R151 3474771584321330615303219103942062667731474349917013292562194195224187539079451441351033770830950366722569416670302761314530888029405792450424636822568863273872561069503408621515775190350627656400731663204453913718408704732358143923634973356319886986817247001565945921134145996380455764262066637649888945684866393924466970971510407453217473194640410599744771464051174416302069411405751063809881467625478896673973654829566287799687041558474609800133121556052301697402021491766906580920850444557180416956802591097136355083354516 h (by decide +kernel)
  let R152 : ℕ := 285405206386818519721818347700599926014683627483805784536044424050443568277827109345613866293694729545063950599267024896
  obtain ⟨h152,p151⟩ := certified_run 37790 120 15 R151 250 15 R152 16384127690362574968001004716125163618955662764871369137959963246587654194701238088768409937045000727416795517764518256159816525433888250924766641194145940294231592584997193507054987807937791551332983876433478900989289515665389880210200025039382900785911558780191733202266679206472968571380688987286072749372950553144425738880562122675316723148861823724264070690859459963256008229592290629660316881097652012372834691826654967238449085852809131281159744658265089008027469945356965135029029729617109773647731769180813871064253315 h151 (by decide +kernel)
  let R153 : ℕ := 509512475156872395826684348359453174271210250884111792170364910023789978445515671297527725275990456774250674289914150912
  obtain ⟨h153,p152⟩ := certified_run 38040 120 15 R152 250 15 R153 2483251668390641830428679287889531668469428870323571816451871225823085195468994025541541863020860101132933504889184231325677251165798715256223544063041308710024475481755445745040096897430517922960450394835961253167521977741936658264626557452115519373655470745600219068302812966959138580704259490833610913415809287240448785276601046889056999069474116626188360982055701354745330523095511318306611378507969966014954657243955541278808797890884763455370081563229792164215175054036698910573243934815947783429844867465144537184536719 h152 (by decide +kernel)
  let R154 : ℕ := 893966861679238390148519340922556659049237615621519278296712353297452436483971078520820796200250936056926014954692149248
  obtain ⟨h154,p153⟩ := certified_run 38290 120 15 R153 250 15 R154 7073297160933997499624660992376397784092283024369858049253629948305382470788065150454276493050479179814841265582173546708117962220451569287153557140266054509573373927354927606961258301761228060648049166207517771290756706011909049063267658238534769323948995356023505386730964414262945269799426057520101962445335316808567254640487315664227245754149228482939140346486127507236870100623487506157600099054012636006585253168307786037937215848849613250159706316785458145791965972595607298577319419233656774200113345922289167486763394 h153 (by decide +kernel)
  let R155 : ℕ := 302041266049433022736202086076937739652309487135640598192869413936835743732529270662832374832610167516058448428561072128
  obtain ⟨h155,p154⟩ := certified_run 38540 120 15 R154 250 15 R155 515383784839103411750502027801605179029141201078829755296246732968418603143290418237590210977039924082679296006495298421463537630170899110005193545000313267317567823410778391295053268715243616872433491142584397704853180376647341086785187398173546681822212885145816292655315322632993773886066732130461840084341265935776948425808973725183797991329378406337445701936976070174816063397286821920314647864664825167597935975368698099942878258294806004527473350828340152762012704570553311171067165273632596818347973342975265280737410 h154 (by decide +kernel)
  let R156 : ℕ := 787821891505669876199390911688787503202499669522179040694863081127120280111882960132968086662114771021949787017643556864
  obtain ⟨h156,p155⟩ := certified_run 38790 120 15 R155 250 15 R156 3974082131579380898673191916334091742139857363348093109372683918263492012183913431308323901102185556384570642567932528963027199919270122626683574573758577674502431081104749283039123789371910447003369961180555983011453653139960494309052647960422395578827439873197538652974598803926131684113873208975259067547752990493378436635766196299079019389781210294593780485952548166791672241376701953656711360931956105538676731561137901830040167921499092961257780873114402615058275468617102967554670331749179724001392464912236872590395270 h155 (by decide +kernel)
  refine ⟨h156,?_⟩
  intro m hm hh
  by_cases hx150 : m ≤ 37790
  · exact p150 m (by omega) hx150
  by_cases hx151 : m ≤ 38040
  · exact p151 m (by omega) hx151
  by_cases hx152 : m ≤ 38290
  · exact p152 m (by omega) hx152
  by_cases hx153 : m ≤ 38540
  · exact p153 m (by omega) hx153
  by_cases hx154 : m ≤ 38790
  · exact p154 m (by omega) hx154
  exact p155 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span156_162 (h : ∃ z H : ℕ, (39040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=787821891505669876199390911688787503202499669522179040694863081127120280111882960132968086662114771021949787017643556864) :
    (∃ z H : ℕ, (40540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=180202345806684336421535478646159300011794491614205516967176647344871185584574995415418982542846493229950158000351084544) ∧
    ∀ m : ℕ, 39040 < m → m ≤ 40540 → ¬ZerosAtEnd m := by
  let R157 : ℕ := 616050532752777856122471291775143048993116012641013650544565794526113059862637441382227121928734678875451839718078021632
  obtain ⟨h157,p156⟩ := certified_run 39040 120 15 787821891505669876199390911688787503202499669522179040694863081127120280111882960132968086662114771021949787017643556864 250 15 R157 4473882450010972955538580910874691760568670345265486190059361796059173427446135482904769783467692288271955143358369796220090750426249325747689167568946675842376124514563140630979312746916899255016200872460018290129211140469294981193997632327998627767830985410497391233570231372118994871396581603231302634891937284271083633795847818315824018790334813569836484964371384581322284547179410355788891588891425777610883242275471804554279727436495012658858117476658235113788101909193168643401891535078656369746635991601839140359127708 h (by decide +kernel)
  let R158 : ℕ := 889960077830376653286634472481795110165069341349144775040595831059230792671941400353070536457859914518134648045360381952
  obtain ⟨h158,p157⟩ := certified_run 39290 120 15 R157 250 15 R158 2002642945010871547067040149931348399329266298405926077433551564753021397132207792210550834383609078829576063253414934164929805262085758372769817775728871941867159567596045129440256247595303854576288205735885009779760110428938424037228646676944559681400785716077209273618143315278580748442939175158133233849208105392866884957659873012205554496318869640152537633022774340223756065026055171566236843620045177704828297974653594329388906677607684344989797318632108155114111004918775868895400508516750955647732363911660007198133763 h157 (by decide +kernel)
  let R159 : ℕ := 378250039846261233690830534771489702852263098459234270440504426079888064084261719638462154128571896017653227237207441408
  obtain ⟨h159,p158⟩ := certified_run 39540 120 15 R158 250 15 R159 2606740842412162291724963332047739674269450341308169992250831644781336895865471398303819062842170805005567371874750543293302198283457446431027173333958086796332840984588266887423343370718169863421943409033465610294641988008432810507137102404247301617457495951668734313461684417391742104727704403730897823230270730732247628816461242150765455803459406007709459496094525244896685299397095857042314719105443564274555978468510124107055149865489948164602810766672980206362687483408343016470639122766296326332264906686619288055367683 h158 (by decide +kernel)
  let R160 : ℕ := 84471773657216929313572843056906328846571732587298306721141234050593843401413551725216850190600028301138719823548645376
  obtain ⟨h160,p159⟩ := certified_run 39790 120 15 R159 250 15 R160 1542850207902013401725085739769354855086604106254609313573953254971169322977846457399436646793421164869407895697872323778097897235805547632695897747356314577732213013113770067520675727078311779510640751768691258145542287172344467924304711420253956056238204417317450793096185604245181204008957132728430815898048483441213150598347425374688871667354454683192251442452047491517244179692633451447857874787047718383597532657096547460629535156564963518444644529142421897398093144202068445117074766307698089072154455463713739311809537 h159 (by decide +kernel)
  let R161 : ℕ := 160623340789027942075899791809170071568087456082403001580597683489135745361539831412164394094671709604708333680756523008
  obtain ⟨h161,p160⟩ := certified_run 40040 120 15 R160 250 15 R161 5569755999375744665019642366369505369444231547322808098244709611147551404140870972950613706130713461095684483182413382664413294283009679076040208098072135688023359675903068973783511631715990740170775450749706023587962818622252334139680001290410140614753528716576326817592182600555315277223573732223851066730627164270819918707303158037342891217860037662228669341220896667679604823776620581762182297158698686154526520773858697480458271814975533169090924674196668175547267672943596956255077175062233205923707473764239993150505607 h160 (by decide +kernel)
  let R162 : ℕ := 180202345806684336421535478646159300011794491614205516967176647344871185584574995415418982542846493229950158000351084544
  obtain ⟨h162,p161⟩ := certified_run 40290 120 15 R161 250 15 R162 4969708365096328785713125122673978816167688309788224653051779273998488136585047574080011638228769632325317071241260716381853464841141403065357536065773617940947934196008161508606016260836826281193511485850548577719035537519584472519421274332186802378754337743586805249577352154725684854963684470848647116843499706901506695414080227868152338516691260749750278488707662420301130382265907348654142234833477467308500988169017680741663787544237434802132772547962813756519886544275820298930954952968229953618440340203000984957586177 h161 (by decide +kernel)
  refine ⟨h162,?_⟩
  intro m hm hh
  by_cases hx156 : m ≤ 39290
  · exact p156 m (by omega) hx156
  by_cases hx157 : m ≤ 39540
  · exact p157 m (by omega) hx157
  by_cases hx158 : m ≤ 39790
  · exact p158 m (by omega) hx158
  by_cases hx159 : m ≤ 40040
  · exact p159 m (by omega) hx159
  by_cases hx160 : m ≤ 40290
  · exact p160 m (by omega) hx160
  exact p161 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span150_162 (h : ∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) :
    (∃ z H : ℕ, (40540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=180202345806684336421535478646159300011794491614205516967176647344871185584574995415418982542846493229950158000351084544) ∧
    ∀ m : ℕ, 37540 < m → m ≤ 40540 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span150_156 h
  obtain ⟨hend,hright⟩ := span156_162 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 39040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span162_168 (h : ∃ z H : ℕ, (40540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=180202345806684336421535478646159300011794491614205516967176647344871185584574995415418982542846493229950158000351084544) :
    (∃ z H : ℕ, (42040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=923666816528196948691844491926173562966929174976339138514663005722837825037083451632670723233342405761378070677604532224) ∧
    ∀ m : ℕ, 40540 < m → m ≤ 42040 → ¬ZerosAtEnd m := by
  let R163 : ℕ := 2171145010457006512150873365036104749818421599475126736395730837343231168091146379921827076522137181257810259226918912
  obtain ⟨h163,p162⟩ := certified_run 40540 120 15 180202345806684336421535478646159300011794491614205516967176647344871185584574995415418982542846493229950158000351084544 250 15 R163 1987393051939783135352603191271412837263331543694049623643429646703196317158030966356349294456656431879234527374542566247975436397027723464419997390385068420374525456943804318940010521260393597964867461223077737906028048741418246803310798773659487297111986076703818299623595613282173106433089770548118849216066821476411275269499083923683572693008955472033157342735009005502265302360600223389176276138698520396462210342783288002856023902859226030541821146011259143518329111558079345102953703132592236449131959954043592708916745 h (by decide +kernel)
  let R164 : ℕ := 898470154285247307886196807607868732779349692919030048157523077626995584361464880137878535632559630542362452954445774848
  obtain ⟨h164,p163⟩ := certified_run 40790 120 15 R163 250 15 R164 3029042233125143683298489419097645137407117797584866083996649249805650364566506409754073495883453722989559432459948698298347743891065071767636807364448628318555901775380273886302554867695586009699980135383159479576103238744015882226043373804204042287468782926481699384421919512644794408291063266520459112003353221620568604618344111955426465797440612323074955190124239272129766945253678469517483007718217248088634666392308485782906949576836165940888023970243374867493397211940511759924083747258480165756697398099072260109304322 h163 (by decide +kernel)
  let R165 : ℕ := 244979652141062071932422489540502188791205944293123266601360682026542634771850620187232365784403677803409751545189761024
  obtain ⟨h165,p164⟩ := certified_run 41040 120 15 R164 250 15 R165 3970235829423421254850272684064686828803395976630868781334669371603356849401819903142898068429012305647238633434395389698805918663225584006610492668249877647403705769521959404657508466670371900160019740042714383601667320702152613135418663115948616476344124639287888513821651244285531120812980124636899057122353657905819851284469442956064422122902505202980388432926459408707581891218896941626679141157900380524443993365545867058582988582975384749074371861958317901812663049036398952725186819057663455521851411236330288042803338 h164 (by decide +kernel)
  let R166 : ℕ := 407382570372992417378163377074982352772060207376751355872775823376899783542638778519107031825778531332484524157458972672
  obtain ⟨h166,p165⟩ := certified_run 41290 120 15 R165 250 15 R166 1007100569716025880377656075423748625310739424400471905654480702644430709537585114003603739478377836521053023079413695485476313880091006064395657877295160921647767248473703788626344817726540802109558139265004579679813993611259460429623882853676749580039372985818666913673305627687003778075870714176407343415288573243013238739749671977277808567005455120746486497023695339647392394950564979139164976283238461399951304918709663042435552633951589254450054354232658521520534408548069969154079015861362239773740766642659177456074891 h165 (by decide +kernel)
  let R167 : ℕ := 410481835017184724463416507475713856237039961277781940979536042707938784813646327515986264211115676850362204718740013056
  obtain ⟨h167,p166⟩ := certified_run 41540 120 15 R166 250 15 R167 523016297127864313623497056615429671495465417498464514676536447398088777941963037105622093721103556329830788250366703872179186356728538369446729910403401631885787665767816357478198562360058569832554217770193018933112791456728864994556723844715035866217466485791662845728744941267008827748140920507443185391531505289864035847045491563499272704798363992062171629019888876289785622146802750359174770922011002432593468169160963357288787484568283288060383361712211236805888345866270078384051321539624723394270009299709079421289869 h166 (by decide +kernel)
  let R168 : ℕ := 923666816528196948691844491926173562966929174976339138514663005722837825037083451632670723233342405761378070677604532224
  obtain ⟨h168,p167⟩ := certified_run 41790 120 15 R167 250 15 R168 995813754793175511122194795920290409780462210000906757591931418097249641440529794309541671193904460786011029011101975859699803718165860436401504762642680136956155375252992269828191836045799956907481010050767196108507199212097207947398019638427646882303379881911372596937924694062451932869722503038998409085326942672449722977894740224834287454657597079837466512717938377245108457991839517094450118807020961478108071829790296796702920993902419135025528324654888703431900710910489652455540149677842446212822308293890714395263495 h167 (by decide +kernel)
  refine ⟨h168,?_⟩
  intro m hm hh
  by_cases hx162 : m ≤ 40790
  · exact p162 m (by omega) hx162
  by_cases hx163 : m ≤ 41040
  · exact p163 m (by omega) hx163
  by_cases hx164 : m ≤ 41290
  · exact p164 m (by omega) hx164
  by_cases hx165 : m ≤ 41540
  · exact p165 m (by omega) hx165
  by_cases hx166 : m ≤ 41790
  · exact p166 m (by omega) hx166
  exact p167 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span168_175 (h : ∃ z H : ℕ, (42040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=923666816528196948691844491926173562966929174976339138514663005722837825037083451632670723233342405761378070677604532224) :
    (∃ z H : ℕ, (43790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672) ∧
    ∀ m : ℕ, 42040 < m → m ≤ 43790 → ¬ZerosAtEnd m := by
  let R169 : ℕ := 53934867830669501715368790772785008462610153027636373874845043834127657453671484307702526699512500495586822195769245696
  obtain ⟨h169,p168⟩ := certified_run 42040 120 15 923666816528196948691844491926173562966929174976339138514663005722837825037083451632670723233342405761378070677604532224 250 15 R169 5973115379856825438599708024856655071223704912127512261881887941965505811981173217158540999570715122587348837643513291385016284680239707863871466085508619258024583201079754839010482138340343977499995295483295284435272742585890511910066847242694898263976388426519401137658901535801459575823934133232860279023616647433223000131632747820821786188439083693324100675123304143919132919595949956061373984170724515843014431618295115841472680390178585868654463418022282612625891075073292764842169682307225413109894174770770556687024260 h (by decide +kernel)
  let R170 : ℕ := 841805611674032977417139379836190095613923858664756089404294974304360544735348356457852721173843041354961359785651339264
  obtain ⟨h170,p169⟩ := certified_run 42290 120 15 R169 250 15 R170 2030386671752192875859052269242278371138773777364604958220598460749189449829548338891733347526369023922420260421032378532721789488717720321276446154999048331587290599461570984614721668186141545411293610385863250598966071860161059423195317773062313119153701866415111770671820245236189143956317795996472150062689419633237194353482307563880819434261081080603125665966498079013148660510704186136429957098364520491999292343535946570981378432081105489198732983739584686174385440189557513924515494411825767424009386169852344597005836 h169 (by decide +kernel)
  let R171 : ℕ := 757529492785498014846422902930841372197453168296391551734060223083046971692759561678502496454331790309979826417012047872
  obtain ⟨h171,p170⟩ := certified_run 42540 120 15 R170 250 15 R171 4470217721431703919774892441223522689184061444865151532362103815333838514727063472101145369784114325223872523494983768229408000829986410858270490329607022666916752353149260853495870419902637598626834002210646205006997001118322647934979254039213293110460816432992044764137228590095873327378601249323373026746716036061771234793490720066903675515240432354068612299959727430969046889316654431706421964371922180631567493124867339399716511801585334570885378218874648581093977086853072864765966657071862796688950393659206117477270661 h170 (by decide +kernel)
  let R172 : ℕ := 191730937738501946120230700948813879528343006279249510839502967283087283932405437993725614436282249348352455173646319616
  obtain ⟨h172,p171⟩ := certified_run 42790 120 15 R171 250 15 R172 1010973546829800316179322287759851188584985717323574770982359873942721281532787668424490524841395135076526743095309081942839632947181455495331389320398503954077441771383055916372928986283151479636388217725501926086265415572555750037013404040916256499300648815725393930690502747529033420225174323574921232331038257014465674051351122286334083112438308632651207173003210252434818931435067247156433498573141501785969254823126997028375845812909751943091631501606027602068798583905943849818565347364275001792421411143486206849876614 h171 (by decide +kernel)
  let R173 : ℕ := 597849581321931962302913462037829140710815098922781341826006957435277369216712679877795266740972638976595659181290160128
  obtain ⟨h173,p172⟩ := certified_run 43040 120 15 R172 250 15 R173 542526853086366751198775492870060145651834091253495942458405181232493113911876931943734360497290221519394576972491963865718590906853746190419169613935223046692377147966927400225150182238448944972037532151476977388866508200047242084566922261265077868107677805277815200110963215730007840403355523486178794703111464124323973903829115532581849267898817672996764921960607476697995078396845369996204140927579583839556151958533971439611430414534721402516956846999766483031216623750043769481971636669720342128350106801559309469647489 h172 (by decide +kernel)
  let R174 : ℕ := 486843622137759336532790644056216174136945100311407077801625461205402520664526017535304073205021398797512271467550605312
  obtain ⟨h174,p173⟩ := certified_run 43290 120 15 R173 250 15 R174 16365487820500220129312943414317879124191922269577254212307504426170852296836608783866237092906419801868126033765841694520700811269938397527708033357212114531551614159187029045268870202239277668976329633697639209065808956798619913746767214647974771759099304071920026545648610095380169687916763305808957876054145096184370770744825655159515015775881878604238806677768972296942668392444736791468596971942345734986862056193745337902184201644266080332628926590078540875616757304440677386818932770018380583224925863895723251628999433 h173 (by decide +kernel)
  let R175 : ℕ := 580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672
  obtain ⟨h175,p174⟩ := certified_run 43540 120 15 R174 250 15 R175 999777754371192051434410490066310517501862122551400917293961872716355334062156791845783098282081156325049346034897769746976467079810050346182699927961318917679481227431407981282877849728214308927082616135725066902138696789033807260673979170794577023376039628577148194454757573195492950061813689109097066051374992788605314872416274995087165809825674706171067926929902123040884824498123067518287617797290876789357531421944266114224605052341935772423385436292861811620019204799162809269067601852442683944587374535887129675924868 h174 (by decide +kernel)
  refine ⟨h175,?_⟩
  intro m hm hh
  by_cases hx168 : m ≤ 42290
  · exact p168 m (by omega) hx168
  by_cases hx169 : m ≤ 42540
  · exact p169 m (by omega) hx169
  by_cases hx170 : m ≤ 42790
  · exact p170 m (by omega) hx170
  by_cases hx171 : m ≤ 43040
  · exact p171 m (by omega) hx171
  by_cases hx172 : m ≤ 43290
  · exact p172 m (by omega) hx172
  by_cases hx173 : m ≤ 43540
  · exact p173 m (by omega) hx173
  exact p174 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span162_175 (h : ∃ z H : ℕ, (40540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=180202345806684336421535478646159300011794491614205516967176647344871185584574995415418982542846493229950158000351084544) :
    (∃ z H : ℕ, (43790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672) ∧
    ∀ m : ℕ, 40540 < m → m ≤ 43790 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span162_168 h
  obtain ⟨hend,hright⟩ := span168_175 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 42040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span150_175 (h : ∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) :
    (∃ z H : ℕ, (43790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672) ∧
    ∀ m : ℕ, 37540 < m → m ≤ 43790 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span150_162 h
  obtain ⟨hend,hright⟩ := span162_175 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 40540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span175_181 (h : ∃ z H : ℕ, (43790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672) :
    (∃ z H : ℕ, (45290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580404203722387442320829216071035699552679326679293122890244964618047245530959590422218486843178107033020810181520392192) ∧
    ∀ m : ℕ, 43790 < m → m ≤ 45290 → ¬ZerosAtEnd m := by
  let R176 : ℕ := 84991402216550174956008447735103418723197657553645078229148568661075831285099172840851824318870876779354636783238250496
  obtain ⟨h176,p175⟩ := certified_run 43790 120 15 580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672 250 15 R176 4470215109949559552098050669393871876834525821515308675974211551461163703064647447533282414340957532272164946250080333266264741115478530357725456053306013552871483260959549882353449422159348078182200929548071287089855379821398667882158127320557197251602214915706584550555046967223026367519518399603494619413886154150532181950332473484997087940266455481057885841935402587973510449073826442155375989280784352690231666881854134092254696856110864536578769376297061345180156449352334195149461944983700715400243512574958145080838681 h (by decide +kernel)
  let R177 : ℕ := 650652960355884174675619277370084515785026426394931617183479053007933598998124419194747222468756252450589381540936941568
  obtain ⟨h177,p176⟩ := certified_run 44040 120 15 R176 250 15 R177 1510587369476503129067106226614643288251639443339449355771608058624245270929468635327979445932885668330142129464920374018414912861075547480678214083016908038420778186728953359285022852922722165368468050585507796035343004420161366909810682768624917427255629244548555198751245477461233054722453369072869275183106133652200985868055105134835616819011556709987112433372596176553813401666105668578572590147097888365844877525688780795962854965880108340007501966649976495369823221499939826434647566456269178003519720157698157692797186 h176 (by decide +kernel)
  let R178 : ℕ := 802003353316907372799111184574991524575302416645545846226592742277930348915687315017238249500656719777450652874106208256
  obtain ⟨h178,p177⟩ := certified_run 44290 120 15 R177 250 15 R178 600562580501583111643222726897976859625048305342095739535097401858404961495494757935999733933256852664186102234057173396352198600346006190453413142159323782174986135250062762871296700235983959436468228633052567096691617455872777662722804097877385674881922568114276008844175290075919479980236126537238618715146212726478518993961672383880694076042363887985032115406284213183214557830344285463561291387262060687244772498527941006648408517106591851885161643082433334980332325119103150013266303396009956118428290198021347186067084 h177 (by decide +kernel)
  let R179 : ℕ := 172481133037636976960436865023207298716768465781800767622796434352345687792012684816359442423281562373580744349999693824
  obtain ⟨h179,p178⟩ := certified_run 44540 120 15 R178 250 15 R179 5953573857217333386284044905122758885528899886266759583453474846032816018164166814296661713427116169187369734411071739515798037863134857521155339411386266843161003012061650816375083927679139565877855362266519063187211509639108502051277190388767139702802731706682937080223455672312678747682582923961749497663191222950796408716300781440964936781377533446034117281357523499083191655823422267690996759854176943943950656077809218689760165583487380130874942196790227830909910204661380089250509280498530070705539235137118056812219409 h178 (by decide +kernel)
  let R180 : ℕ := 544719492967748098041508489121537681080470308904359912576890587758614597419866093751294053307360255776929461932375670784
  obtain ⟨h180,p179⟩ := certified_run 44790 120 15 R179 250 15 R180 1518757474313156861252453183878871151737397003606450369589717960947838529898238668362531162081845328245190584106307875877329674955073758132357667446335014057062588139892309344723700851361856880666340973304506283162033084552370459516188366419775795006970878032326262629536851187214754425683263032189729566224443882692174097921621997225084967005334159527174152374372285570722329741027295825299536267901088307490018940558478788488968125726077676519312457653866585136037739018766036131763626346250420576304313919317696114847744131 h179 (by decide +kernel)
  let R181 : ℕ := 580404203722387442320829216071035699552679326679293122890244964618047245530959590422218486843178107033020810181520392192
  obtain ⟨h181,p180⟩ := certified_run 45040 120 15 R180 250 15 R181 4494333161057031956920159936419643705756781365441804349506786511557368642300044330335965707388015890823964002499213820057121751852225714904538411519717515879642562388041707833059190285639140559304457605046825617786089298384143570573819604897206595546613925831262897479832017892643804799138094598922420276007996096250566983471811202243610155732824769832773905107707336851860759294933682716887799795688554298965895792379067346771559687611610580850916188517295450890472855244444572928622210594941758616855659641201365381783110305 h180 (by decide +kernel)
  refine ⟨h181,?_⟩
  intro m hm hh
  by_cases hx175 : m ≤ 44040
  · exact p175 m (by omega) hx175
  by_cases hx176 : m ≤ 44290
  · exact p176 m (by omega) hx176
  by_cases hx177 : m ≤ 44540
  · exact p177 m (by omega) hx177
  by_cases hx178 : m ≤ 44790
  · exact p178 m (by omega) hx178
  by_cases hx179 : m ≤ 45040
  · exact p179 m (by omega) hx179
  exact p180 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span181_187 (h : ∃ z H : ℕ, (45290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580404203722387442320829216071035699552679326679293122890244964618047245530959590422218486843178107033020810181520392192) :
    (∃ z H : ℕ, (46790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=615272128001951748474619617420572843086488444403763108550604003813335186085308652302804957314661375078360755448894717952) ∧
    ∀ m : ℕ, 45290 < m → m ≤ 46790 → ¬ZerosAtEnd m := by
  let R182 : ℕ := 90207573622604278162621990883519509015346354227744228851587663563323454687707361469452985711760880594154980088527978496
  obtain ⟨h182,p181⟩ := certified_run 45290 120 15 580404203722387442320829216071035699552679326679293122890244964618047245530959590422218486843178107033020810181520392192 250 15 R182 5976598765446512060270870018400370760700982075301170894303438960013700496060634187974263556731675573300446580341011423603996545719504569402996242415716004465031580492018201963442179911480464868477470440312082351655044759958310879065024145621956612350652967197461846452905925543947746868729948840148898593642793000851661080202125640126273274699480932216689739843527544277963258687395656918376955291103975969356822628625698511720465218002867295663421735466270239717523416726106704312411151317352727161198094397341469152997591179 h (by decide +kernel)
  let R183 : ℕ := 398350827987429279896878090064211281614505398684335891879042379701145336831755056840367420490111489630987316533317861376
  obtain ⟨h183,p182⟩ := certified_run 45540 120 15 R182 250 15 R183 21333953900112859592902034270415890898330723197384496217981497062123024034349675894343170089225184327794334393785445286222388536303933410205228546199144048929617255608243199953286637687105643698068915756509281122948066214295262253129106661683094194584082118069988866268105159788098156549318690768930087447721234553482981233173258480062075600520006735940394100508406475862783626307697096303270289517730900570227045805583530906923290513173086715667208804813945660880621465217666669986810036695824630469654591861954981107163300098 h182 (by decide +kernel)
  let R184 : ℕ := 384565142031783317996232134483245780302477574890249919799649639077929395206961386860473084669481512364214996390383714304
  obtain ⟨h184,p183⟩ := certified_run 45790 120 15 R183 250 15 R184 3067899281023717667939979740392511367465349219393558790270262238325281203401339972063991604705735817267136765750350197611186195990357560463784859424415028681937892830237047041084672587490931466901298563932064840240262404982507155512636312894205184894185562785724317210442859695189520465005626209142197471921414807222958658940496172561059235482235862217307561218319860035551936874339577074714991577053045340237474654268815597162933625753704249907523931292468965570749306500326164674380220769381444589730934353977642395988345360 h183 (by decide +kernel)
  let R185 : ℕ := 664288525829809376178660474427006117347002449859861008788682057007296493121415630017232589004152814209921845984816529408
  obtain ⟨h185,p184⟩ := certified_run 46040 120 15 R184 250 15 R185 4001131286725273984675366136375283841424271629225828866358346201573521303360444603184403512450019824349443953862836431519951702445533802020749530058222651447579634399048707905868797739024095254961969747928717490925706601284535805102973834173936466493037307440569814526285438798529436323479011745697725177558674200037731757038305093083911139443852448400442729169400686013935093327338595265894257512564297794111666773745318418538510866074641478038547877092632247143203603855817418534954397195810296293073199256338416633295080088 h184 (by decide +kernel)
  let R186 : ℕ := 556123458246255616181582061691691936108213740674823867312526907429884450512951126217158720590032239377066099412842840064
  obtain ⟨h186,p185⟩ := certified_run 46290 120 15 R185 250 15 R186 5480975436023466061656195059016740908513809144826992768405029580566252424117136918757638649837019595738233392877214655841351251322511893720158916570078415757624472549224293441970831553250632315235774054820221205519791177311093706908905924773393954751706508550498004572797213743641789103179645966756888964135187650041138241044814951155407126379120992350861795404845307934920939525965942389479786724538362420010942591307990346059470281739472410612666246570146083910754051773834854399876525386435162417421303165078171194384126209 h185 (by decide +kernel)
  let R187 : ℕ := 615272128001951748474619617420572843086488444403763108550604003813335186085308652302804957314661375078360755448894717952
  obtain ⟨h187,p186⟩ := certified_run 46540 120 15 R186 250 15 R187 34367471837636444907918514062155264036562193366228561382597069850323394354142368045362906558573182253794918643479136176242646743679741067380408370614539299742601259762137394424952180856049948290388979998759560180740854965756752894958619136984974683697780177180208031065880022528417723957236942468878843051340949289667545718985605127799438879621843949214068862773430514780364039109560417917351620218085541954649779392063265701509327319892515414033263909112663330850233542282843387096398458109233544273936477656469706700918768263 h186 (by decide +kernel)
  refine ⟨h187,?_⟩
  intro m hm hh
  by_cases hx181 : m ≤ 45540
  · exact p181 m (by omega) hx181
  by_cases hx182 : m ≤ 45790
  · exact p182 m (by omega) hx182
  by_cases hx183 : m ≤ 46040
  · exact p183 m (by omega) hx183
  by_cases hx184 : m ≤ 46290
  · exact p184 m (by omega) hx184
  by_cases hx185 : m ≤ 46540
  · exact p185 m (by omega) hx185
  exact p186 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span175_187 (h : ∃ z H : ℕ, (43790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672) :
    (∃ z H : ℕ, (46790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=615272128001951748474619617420572843086488444403763108550604003813335186085308652302804957314661375078360755448894717952) ∧
    ∀ m : ℕ, 43790 < m → m ≤ 46790 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span175_181 h
  obtain ⟨hend,hright⟩ := span181_187 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 45290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span187_193 (h : ∃ z H : ℕ, (46790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=615272128001951748474619617420572843086488444403763108550604003813335186085308652302804957314661375078360755448894717952) :
    (∃ z H : ℕ, (48290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=356696987260472562282766055961220264490065920629914401430210720575234820328503363622607900652526948680637859750547030016) ∧
    ∀ m : ℕ, 46790 < m → m ≤ 48290 → ¬ZerosAtEnd m := by
  let R188 : ℕ := 428676567853788602487651295811855492670593833324409454299876183691832040005589737133580200282048124038371131755738431488
  obtain ⟨h188,p187⟩ := certified_run 46790 120 15 615272128001951748474619617420572843086488444403763108550604003813335186085308652302804957314661375078360755448894717952 250 15 R188 5546607450786741910455346318939336318892820412205014188118115807536104988899849001280076705527869726400813594342057471234648377504295561042017525116607089953876767773461900864004681350444429083032156494344717347175055817319148434045761022560317379826149803624007023549050494396524851409971105874073833211442983082263442156313836129005412742027875827310170873377610437345464827804243733386696598308079376045332710179213177431613035649346064389125030969190743006709315203640036014141349075585801973272065693101588160553506996612 h (by decide +kernel)
  let R189 : ℕ := 991414460412783527958323285871586616489969724478142397967520718218069261609474576506766145853369483139597091373162954752
  obtain ⟨h189,p188⟩ := certified_run 47040 120 15 R188 250 15 R189 3702954133458485870304608192494229609406526302944464120097642456806993351921723335939290383574567437149541237230448033523198167157421561429360545114468636846085124305258142056771746183069912463649884205339346119716647226503794382035728920617725574636816939728007011458263305212436895979817126577272276842976399763730989139732816716407063619636241901156984812800692733396761803224248216511832008001247738679408616943489482740133818145425437689182579555948268308184364856581963412069446351733401254836705773661980007552589529370 h188 (by decide +kernel)
  let R190 : ℕ := 640866049953007792605092434484307474147277379957348225839947680836880033398985532544103517877438375414343164505500942336
  obtain ⟨h190,p189⟩ := certified_run 47290 120 15 R189 250 15 R190 1007071017379924515107176900829933247635396409533792087012322942965638489740093538851991516034657960796078893758805974436587407419288191293493860913335685443246063229207905685985131795069844081239645504392173364435810595149468707005827015160371389571089092692572999031047134313493962426627248432772361453886139814716180807941476057007609959520091387399833595943082978406889188325265554573002087016151056521721159287051524754493141735605623509110443167783973254578661477527314892711166353975698914405582252454096662614021047555 h189 (by decide +kernel)
  let R191 : ℕ := 372522141108974054359278359792649440635575035969898046636939049086042170469285431368259399045724034676029052234925867008
  obtain ⟨h191,p190⟩ := certified_run 47540 120 15 R190 250 15 R191 3028922593071527837288463695032343869916870713776910345417865103623708900334213399736955439794086475646259970000960966160653544327352647594732278567088852618694850389095282314673926989162760987581050446653582043949157729003023813473470934525099188182954532183403644208350191896375356379193622000861435578800654352768255239303372605826072431191747947440440203631124751216890022742833068449358994448597261133991400049521732011492019607837615983643193747870202610461367191154862228373791931883362800306871436780116199513899681818 h190 (by decide +kernel)
  let R192 : ℕ := 233469324045417760326125122848149703493531408189225131488506422818731618599310983798279449237149092272213496778702454784
  obtain ⟨h192,p191⟩ := certified_run 47790 120 15 R191 250 15 R192 4020556754400294034440180865676640037446775753057057221454372698194108028514671026726470378332207750105996804832219829562831269398265271269115484259878481102033801744509413118855919461851903790129802420313786778289933815854990760921707056953953294694638085375544605172067064063887062815319507288274262035823856673577472133876775529700679484747930025115392752975109603089156110722232882080766905031124378328026824706373485760070739698543273154212318045182694910888484856048667573811860177611843427553159353320525770776075374465 h191 (by decide +kernel)
  let R193 : ℕ := 356696987260472562282766055961220264490065920629914401430210720575234820328503363622607900652526948680637859750547030016
  obtain ⟨h193,p192⟩ := certified_run 48040 120 15 R192 250 15 R193 4051819819978443801790262252067873113211359795846139693160350939787008666473800674179656809107467523646296624883026175243001795538000505028006615580665718440844305653733688285338703166203555635219754205197537926110650767888261725663880255764749933558590587363101758827906783979567022671574912355981131202449208751143486987745063626971961391242724995771783173270336978152584874421262379271144330423286183794593398783323957431589632815947409518591289621337954368143274475230041685737363734897993310174238450009742524675692692629 h192 (by decide +kernel)
  refine ⟨h193,?_⟩
  intro m hm hh
  by_cases hx187 : m ≤ 47040
  · exact p187 m (by omega) hx187
  by_cases hx188 : m ≤ 47290
  · exact p188 m (by omega) hx188
  by_cases hx189 : m ≤ 47540
  · exact p189 m (by omega) hx189
  by_cases hx190 : m ≤ 47790
  · exact p190 m (by omega) hx190
  by_cases hx191 : m ≤ 48040
  · exact p191 m (by omega) hx191
  exact p192 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span193_200 (h : ∃ z H : ℕ, (48290:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=356696987260472562282766055961220264490065920629914401430210720575234820328503363622607900652526948680637859750547030016) :
    (∃ z H : ℕ, (50040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232) ∧
    ∀ m : ℕ, 48290 < m → m ≤ 50040 → ¬ZerosAtEnd m := by
  let R194 : ℕ := 843457999367870599975146884769836335515291216693762150634467637958201199733820173312735696711548295547701878422203531264
  obtain ⟨h194,p193⟩ := certified_run 48290 120 15 356696987260472562282766055961220264490065920629914401430210720575234820328503363622607900652526948680637859750547030016 250 15 R194 10036248240484393544754724958683580107042534460358193844577251590097335655880250535436425101998373844690264791851462218935729861729861266953908408463358798873422499675357196369939953466451049599750602642939959467572388588647326413271825399400006272884278835395621357930108985509388988746463693933348818741592132029368724526185452573914162792399259036907136913533715636254876213102688222766713672864784961792547914341297586053371192684040027972094749965679317256684643750380581198650200621396693002414165569888051534149315527297 h (by decide +kernel)
  let R195 : ℕ := 16712419717986306982243883028484113606343552114423727198378771406019927641793169954992155586897863357891780540048080896
  obtain ⟨h195,p194⟩ := certified_run 48540 120 15 R194 250 15 R195 1495276979604933231254532148800441610851312015013547545566324542554341659660767838120087669606512203539187666308056213639823394219586512723400381477782028206419305085759312197666533802795989657307460316030999576692515243705824094555709298334620732965703478363246518287504037721401329291430356388113890444309572841076223152538127349364658803581560082352074636599954476406714479589880636795491782930184483732806937782200471760664243480302865688122681939562552066340683821017049473756771996054437603381406976485013931370129458307 h194 (by decide +kernel)
  let R196 : ℕ := 182063364495070764588247532154809122373703591940505031790396182011972142685128637849724889749515173199782935925681553408
  obtain ⟨h196,p195⟩ := certified_run 48790 120 15 R195 250 15 R196 2507217173043042655760305967897025815292271715154687327081218523756569633504603720937254149189288034646349817709523854498909036283883361719428558974022043594573055150713338843282406431779046441869077876835893668172675051645753094965787152763601986333689437876379970502956569403696175091839396565543812248437716131624044517902747692653129923015297041360780699219928973774529066547395949603127389415477210151565246313288275811548327860739579573116067519237073487732389935883266560664419036774456068585677440182324035115450220933 h195 (by decide +kernel)
  let R197 : ℕ := 39931327057105514589951643246404684471901518032053988560520928435238693691779876843403004098038551643295574232005607424
  obtain ⟨h197,p196⟩ := certified_run 49040 120 15 R196 250 15 R197 2482797248808627412482293776428671418106821261425626461769627711679276118840036759599192822188952619257347885912253747387040054947946939767457735643091507761943136482277131590389467997596270623717087548541280855693801751132503687978226699954258563551856935516425951438835237586824355103395332369329210065353058404148513462784822155570953605925436648886930859528375765259341744412940397223383455598029471147873696766824127904843611901366741056892013854126929224549040519174859987198563035124394169317050500469225457795648211457 h196 (by decide +kernel)
  let R198 : ℕ := 217713758818887233902862469427109232326757171076653582651235892216156001754715446756426819926468953103625714568079081472
  obtain ⟨h198,p197⟩ := certified_run 49290 120 15 R197 250 15 R198 9439225856098599698797004828020656519032466393483211155119264656096142494781100421588190225274192227002430295331826441029645565941408405666726787553117190488011697751847667999394226949864839261888673359912192181151423554106768022206637672018683538557154736689995950984790773609310899993030409141123021858713036162372778051817330538435715461372007579673982385666277267500742301564656850250402075320333931473236543531056642265622812913993695078010433615676651286391868397341083540606760454298250226658980844208775031990784131203 h197 (by decide +kernel)
  let R199 : ℕ := 305970638745003454668328678363644822352404365868087207899044101520788537841183977761867029630822955386005580687068889088
  obtain ⟨h199,p198⟩ := certified_run 49540 120 15 R198 250 15 R199 8954953174135252311993474023802828203595416045437849642060125671049507616292258521186507002941278430849133680120865024957063296546432759056755501542593248351151739779313184623330853386562104273581217813577109886758624757600784453467482652961508925687647243629306171586824159263278495174159046403970332195159672821458315243647950916271727741966040850943489250971986551632208197405837741393368598337444843414634688502073793662350066211177591785357026380255609238307147127093493092064692596578764370128066589719553687033527666820 h198 (by decide +kernel)
  let R200 : ℕ := 618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232
  obtain ⟨h200,p199⟩ := certified_run 49790 120 15 R199 250 15 R200 4973553465327465380640153568314986441229059725177569931542257856270392502823097051555776377845541315586441259136493791068275249321751214482897039343592979780941683199446767922354790874954209340047604656047558220294957539798536681892108437292740314052062359496990812243637308736389160100298208763239367860017040178690805620546411011424421138859978454457599341524217608069037661071056817856586558324757790114633944327916678717881732838894629327662248040894521901131865795334764186030778727451823570535006724329650224349063823880 h199 (by decide +kernel)
  refine ⟨h200,?_⟩
  intro m hm hh
  by_cases hx193 : m ≤ 48540
  · exact p193 m (by omega) hx193
  by_cases hx194 : m ≤ 48790
  · exact p194 m (by omega) hx194
  by_cases hx195 : m ≤ 49040
  · exact p195 m (by omega) hx195
  by_cases hx196 : m ≤ 49290
  · exact p196 m (by omega) hx196
  by_cases hx197 : m ≤ 49540
  · exact p197 m (by omega) hx197
  by_cases hx198 : m ≤ 49790
  · exact p198 m (by omega) hx198
  exact p199 m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span187_200 (h : ∃ z H : ℕ, (46790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=615272128001951748474619617420572843086488444403763108550604003813335186085308652302804957314661375078360755448894717952) :
    (∃ z H : ℕ, (50040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232) ∧
    ∀ m : ℕ, 46790 < m → m ≤ 50040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span187_193 h
  obtain ⟨hend,hright⟩ := span193_200 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 48290
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span175_200 (h : ∃ z H : ℕ, (43790:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=580476737658662987925167394974324033944817722540531300172253784094862377665824415518548909386061196931406193290926620672) :
    (∃ z H : ℕ, (50040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232) ∧
    ∀ m : ℕ, 43790 < m → m ≤ 50040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span175_187 h
  obtain ⟨hend,hright⟩ := span187_200 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 46790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span150_200 (h : ∃ z H : ℕ, (37540:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=660534249656157285370913893007709784246195809807158755482330621402372870310641859907463263549548780583945547854469136384) :
    (∃ z H : ℕ, (50040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232) ∧
    ∀ m : ℕ, 37540 < m → m ≤ 50040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span150_175 h
  obtain ⟨hend,hright⟩ := span175_200 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 43790
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span100_200 (h : ∃ z H : ℕ, (25040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=129846156138959279265663025760251457006183812835129974621332359267915810555710913344901883842214635345100251201628274688) :
    (∃ z H : ℕ, (50040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232) ∧
    ∀ m : ℕ, 25040 < m → m ≤ 50040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span100_150 h
  obtain ⟨hend,hright⟩ := span150_200 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 37540
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
private theorem span0_200 (h : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952) :
    (∃ z H : ℕ, (50040:ℕ).factorial=10^z*(2^15*H) ∧ H%(10^120)=618257184811448598781268187115529581007258610150083173331529481141553553232222527389320106868859152837425375713513439232) ∧
    ∀ m : ℕ, 40 < m → m ≤ 50040 → ¬ZerosAtEnd m := by
  obtain ⟨hmid,hleft⟩ := span0_100 h
  obtain ⟨hend,hright⟩ := span100_200 hmid
  refine ⟨hend,?_⟩
  intro m hm hh
  by_cases hx : m ≤ 25040
  · exact hleft m hm hx
  · exact hright m (by omega) hh
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem finite_bound {n : ℕ} (hn : n ≤ 50040) (h : ZerosAtEnd n) : n≤40 := by
  have hi : ∃ z H : ℕ, (40:ℕ).factorial=10^z*(2^16*H) ∧ H%(10^120)=12449879199949611424951343835389952 :=
    ⟨9,12449879199949611424951343835389952,by decide +kernel,by decide +kernel⟩
  have hall := (span0_200 hi).2
  by_contra! hgt
  exact hall n hgt hn h
end Fact393
namespace Fact393
open OMA.S_mo_393993

theorem finite_exact {n : ℕ} (hn : n≤50040) :
    ZerosAtEnd n ↔ n ∈ ([0,1,2,3,4,5,6,9,10,11,14,31,40] : List ℕ) := by
  constructor
  · intro h
    exact (first_exact (finite_bound hn h)).mp h
  · intro h
    have h40 : n≤40 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at h; omega
    exact (first_exact h40).mpr h
end Fact393

namespace OMA.R_mo_393993_R1
open OMA.S_mo_393993

/-- Finite verification by the positions of zero digits in a fixed suffix.
An independent modular scan has already found a witness for every index
in this range. The smaller initial range is proved in this file. -/
def H1 : Prop := ∀ n : ℕ, 50040<n → n≤100000000 →
  0∈(Nat.digits 10 (n.factorial/10^padicValNat 10 n.factorial)).take 256

/-- For the sparse surviving indices, approximate the sum of logarithms
well enough to see a zero followed by a nonzero digit in a leading block.
Both the inspected prefix and suffix use only logarithmically many digits
as functions of n. The powers of five have already been settled. -/
def H2 : Prop := ∀ n : ℕ, 100000000<n → (∀ j : ℕ, n≠5^j) →
  let q := 32*(Nat.log 10 n+1)
  0∉(Nat.digits 10 (n.factorial/10^padicValNat 10 n.factorial)).take q →
  ∃ w e : ℕ, 0<w ∧ (Nat.digits 10 w).length≤q ∧ ¬10∣w ∧ 0∈Nat.digits 10 w ∧
    Real.logb 10 (w:ℝ)+e ≤ ∑ i ∈ Finset.range n,Real.logb 10 ((i:ℝ)+1) ∧
    (∑ i ∈ Finset.range n,Real.logb 10 ((i:ℝ)+1)) < Real.logb 10 ((w:ℝ)+1)+e

theorem main : H1 → H2 → type_of% @OMA.S_mo_393993.main := by
  intro h₁ h₂
  refine ⟨(Fact393.first_exact (n:=40) (by decide)).mpr (by decide),?_⟩
  intro n hn
  change ZerosAtEnd n at hn
  by_cases small : n≤50040
  · exact Fact393.finite_bound small hn
  by_cases finite : n≤100000000
  · exact False.elim (hn ((List.take_prefix _ _).subset (h₁ n (by omega) finite)))
  have hp : ∀ j : ℕ, n≠5^j := by
    rintro j rfl
    have hj := (Fact393.pure_five_classification j).mp hn
    have := Nat.pow_le_pow_right (by decide : 0<5) hj
    omega
  obtain ⟨w,e,hw,_,hu,hd,lo,hi⟩ := h₂ n (by omega) hp
    (fun he => hn ((List.take_prefix _ _).subset he))
  exact False.elim (Fact393.log_prefix_excludes hw hu hd lo hi hn)

end OMA.R_mo_393993_R1
