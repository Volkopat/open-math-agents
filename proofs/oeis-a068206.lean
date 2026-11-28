import OMAStatements.S_oeis_a068206

/-! The congruence conjecture of Václav Kotěšovec in OEIS A068206.
We derive the local Bernoulli congruences directly from Faulhaber's formula.
The classical context is the denominator theorem of von Staudt–Clausen
and Kummer's congruences. -/


namespace SevenLocal

private theorem seven_prime : Nat.Prime 7 := by decide

/-- The subring of rational numbers with denominator prime to seven. -/
def localRing : Subring ℚ where
  carrier := {q | ¬ 7 ∣ q.den}
  one_mem' := by norm_num
  zero_mem' := by norm_num
  add_mem' := fun {a b} ha hb h =>
    (seven_prime.dvd_mul.mp (h.trans (Rat.add_den_dvd a b))).elim ha hb
  mul_mem' := fun {a b} ha hb h =>
    (seven_prime.dvd_mul.mp (h.trans (Rat.mul_den_dvd a b))).elim ha hb
  neg_mem' := fun {a} ha => by simpa [Rat.den_neg_eq_den] using ha

def multiple (e : ℕ) (x : ℚ) : Prop := ∃ y ∈ localRing, x = (7:ℚ)^e*y

theorem multiple_zero (e : ℕ) : multiple e 0 := ⟨0, localRing.zero_mem, by ring⟩

theorem multiple_mem {e : ℕ} {x : ℚ} (h : multiple e x) : x ∈ localRing := by
  obtain ⟨y,h,rfl⟩ := h
  exact localRing.mul_mem (localRing.pow_mem (natCast_mem localRing 7) _) h

theorem multiple_add {e : ℕ} {x y : ℚ} (hx : multiple e x) (hy : multiple e y) :
    multiple e (x+y) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact ⟨a+b, localRing.add_mem ha hb, by ring⟩

theorem multiple_sub {e : ℕ} {x y : ℚ} (hx : multiple e x) (hy : multiple e y) :
    multiple e (x-y) := by
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  exact ⟨a-b,localRing.sub_mem ha hb, by ring⟩

theorem multiple_mul_local {e : ℕ} {x y : ℚ} (hx : multiple e x) (hy : y ∈ localRing) :
    multiple e (x*y) := by
  obtain ⟨a,ha,rfl⟩ := hx
  exact ⟨a*y,localRing.mul_mem ha hy,by ring⟩

theorem multiple_sum {ι : Type*} (s : Finset ι) {e : ℕ} (f : ι → ℚ)
    (hf : ∀ i ∈ s, multiple e (f i)) : multiple e (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using multiple_zero e
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact multiple_add (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

theorem inv_nat_mem {n : ℕ} (hn : ¬ 7 ∣ n) : (n:ℚ)⁻¹ ∈ localRing := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  change ¬ 7 ∣ ((n:ℚ)⁻¹).den
  simpa [Rat.den_inv_of_ne_zero (Nat.cast_ne_zero.mpr hn0),Rat.num_natCast] using hn

theorem multiple_of_num {q : ℚ} (h : 7 ∣ q.num.natAbs) : multiple 1 q := by
  have hden : ¬7 ∣ q.den := seven_prime.coprime_iff_not_dvd.mp
    (Nat.Coprime.of_dvd_left h q.reduced)
  have hnum : (7:ℤ) ∣ q.num := Int.natCast_dvd.mpr h
  obtain ⟨b,hb⟩ := hnum
  refine ⟨(b:ℚ)*(q.den:ℚ)⁻¹,localRing.mul_mem (intCast_mem localRing b) (inv_nat_mem hden),?_⟩
  calc
    q = (q.num:ℚ)/(q.den:ℚ) := q.num_div_den.symm
    _ = _ := by rw [hb]; push_cast; ring

theorem seven_mul_multiple {q : ℚ} (h : multiple 1 q) : multiple 2 (7*q) := by
  obtain ⟨y,hy,rfl⟩ := h
  exact ⟨y,hy,by ring⟩

theorem mem_of_seven_multiple {q : ℚ} (h : multiple 1 (7*q)) : q ∈ localRing := by
  obtain ⟨y,hy,h⟩ := h
  norm_num at h
  exact (show q = y by linarith) ▸ hy

theorem multiple_one_of_int_dvd {z : ℤ} (h : (7:ℤ) ∣ z) : multiple 1 (z:ℚ) := by
  obtain ⟨b,rfl⟩ := h
  exact ⟨(b:ℚ),intCast_mem localRing b,by push_cast; ring⟩

theorem int_dvd_of_multiple_two {z : ℤ} (h : multiple 2 (z:ℚ)) : (49:ℤ) ∣ z := by
  obtain ⟨y,hy,hz⟩ := h
  have hden : ¬ 7 ∣ y.den := hy
  have hc : Nat.Coprime 49 y.den := (seven_prime.coprime_iff_not_dvd.mpr hden).pow_left 2
  have dyd : y*(y.den:ℚ) = (y.num:ℚ) := (div_eq_iff (Nat.cast_ne_zero.mpr y.den_ne_zero)).mp y.num_div_den |>.symm
  have hq : (z:ℚ)*(y.den:ℚ) = 49*(y.num:ℚ) := by rw [hz,← dyd]; ring
  have hi : z*(y.den:ℤ) = 49*y.num := by exact_mod_cast hq
  exact hc.isCoprime.dvd_of_dvd_mul_right ⟨y.num,hi⟩

private theorem exp_bound (k : ℕ) : k+4 ≤ 7^(k+1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ]
    omega

private theorem powers_over (j e : ℕ) (he : e ≤ 2) (hj : e+1 ≤ j) :
    multiple e ((7:ℚ)^(j-1)/j) := by
  have hj0 : j ≠ 0 := by omega
  let v := j.factorization 7
  let b := j / 7^v
  have cop : ¬7∣b := Nat.not_dvd_ordCompl seven_prime hj0
  have hn : 7^v * b = j := Nat.ordProj_mul_ordCompl_eq_self j 7
  have hr : (7:ℚ)^v * (b:ℚ) = (j:ℚ) := by exact_mod_cast hn
  have hv : v+e+1 ≤ j := by
    have h := Nat.ordProj_le 7 hj0
    change 7^v ≤ j at h
    by_cases hz : v=0
    · omega
    · obtain ⟨k, heq⟩ := Nat.exists_eq_succ_of_ne_zero hz
      rw [heq] at h ⊢
      have hk : k+4 ≤ j := (exp_bound k).trans h
      omega
  let w := j-1-e-v
  have hw : j-1 = e+w+v := by dsimp [w]; omega
  refine ⟨(7:ℚ)^w * (b:ℚ)⁻¹,
    localRing.mul_mem (localRing.pow_mem (natCast_mem localRing 7) _) (inv_nat_mem cop),?_⟩
  have bn : b ≠ 0 := by rintro h; rw [h] at cop; simp at cop
  rw [hw,pow_add,pow_add,← hr]
  field_simp

theorem powers_over_one (j : ℕ) (hj : 2 ≤ j) : multiple 1 ((7:ℚ)^(j-1)/j) :=
  powers_over j 1 (by decide) hj

theorem powers_over_two (j : ℕ) (hj : 3 ≤ j) : multiple 2 ((7:ℚ)^(j-1)/j) :=
  powers_over j 2 (by decide) hj

end SevenLocal


namespace A68206Faulhaber
open Finset SevenLocal

private def tailTerm (k i : ℕ) : ℚ :=
  (7 ^ (k + 1 - i - 1) / ((k + 1 - i : ℕ) : ℚ)) *
    (k.choose i * (7 * bernoulli i))

private theorem tailTerm_eq (k i : ℕ) (hi : i < k) :
    bernoulli i * ((k + 1).choose i) * (7 : ℚ) ^ (k + 1 - i) / (k + 1) =
      tailTerm k i := by
  have hx : (k.choose i : ℚ) * (k + 1) =
      ((k + 1).choose i : ℚ) * ((k + 1 - i : ℕ) : ℚ) := by
    exact_mod_cast Nat.choose_mul_succ_eq k i
  have hj : (0 : ℚ) < ((k + 1 - i : ℕ) : ℚ) := by exact_mod_cast (show 0 < k + 1 - i by omega)
  have hp : (7 : ℚ) ^ (k + 1 - i) = 7 ^ (k + 1 - i - 1) * 7 := by
    simpa only [show k + 1 - i - 1 + 1 = k + 1 - i by omega] using
      pow_succ (7 : ℚ) (k + 1 - i - 1)
  unfold tailTerm
  rw [hp]
  field_simp [hj.ne']
  linear_combination -(bernoulli i) * hx

private theorem faulhaber_split (k : ℕ) :
    (∑ a ∈ range 7, (a : ℚ)^k) =
      (∑ i ∈ range k, tailTerm k i) + 7 * bernoulli k := by
  rw [sum_range_pow, Finset.sum_range_succ]
  congr 1
  · refine sum_congr rfl fun i hi => ?_
    simpa using tailTerm_eq k i (mem_range.mp hi)
  · rw [Nat.choose_succ_self_right, show k + 1 - k = 1 by omega]
    push_cast
    field_simp



private theorem tail_one_of_induction (k i : ℕ) (hi : i < k)
    (hB : 7 * bernoulli i ∈ localRing) : multiple 1 (tailTerm k i) :=
  multiple_mul_local (powers_over_one _ (by omega))
    (localRing.mul_mem (natCast_mem localRing _) hB)

private theorem scaled_local (k : ℕ) : 7 * bernoulli k ∈ localRing := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have ht := multiple_sum (range k) (tailTerm k) (fun i hi =>
      tail_one_of_induction k i (mem_range.mp hi) (ih i (mem_range.mp hi)))
    have hs : (∑ a ∈ range 7, (a : ℚ)^k) ∈ localRing :=
      localRing.sum_mem fun a _ => localRing.pow_mem (natCast_mem localRing a) k
    rw [faulhaber_split] at hs
    have hx := localRing.sub_mem hs (multiple_mem ht)
    simpa using hx

private theorem tail_multiple_two (k i : ℕ) (hi : i < k) (hk : 2 < k)
    (he : Even k) : multiple 2 (tailTerm k i) := by
  by_cases h : i + 1 = k
  · have hOdd : Odd i := by obtain ⟨u,hu⟩ := he; exact ⟨u-1,by omega⟩
    simpa [tailTerm, bernoulli_eq_zero_of_odd hOdd (by omega)] using multiple_zero 2
  · exact multiple_mul_local (powers_over_two _ (by omega))
      (localRing.mul_mem (natCast_mem localRing _) (scaled_local i))

theorem seven_sum_sq (k : ℕ) (hk : 2 ≤ k) (he : Even k)
    (hd : 7 ∣ (bernoulli k).num.natAbs) :
    (49 : ℤ) ∣ ∑ a ∈ range 7, (a : ℤ)^k := by
  by_cases h2 : k = 2
  · subst k
    norm_num [bernoulli_two] at hd
  apply int_dvd_of_multiple_two
  push_cast
  rw [faulhaber_split]
  exact multiple_add
    (multiple_sum (range k) (tailTerm k) fun i hi =>
      tail_multiple_two k i (mem_range.mp hi) (by omega) he)
    (seven_mul_multiple (multiple_of_num hd))

theorem bernoulli_den_sum (k : ℕ) (_hk : 0 < k) (hd : 7 ∣ (bernoulli k).den) :
    ¬ (7 : ℤ) ∣ ∑ a ∈ range 7, (a : ℤ)^k := by
  intro hz
  have hs := multiple_one_of_int_dvd hz
  push_cast at hs
  rw [faulhaber_split] at hs
  have ht := multiple_sum (range k) (tailTerm k) fun i hi =>
    tail_one_of_induction k i (mem_range.mp hi) (scaled_local i)
  have hm : multiple 1 (7 * bernoulli k) := by
    simpa using multiple_sub hs ht
  exact (mem_of_seven_multiple hm) hd

end A68206Faulhaber


namespace A68206Residues

open Finset

private theorem rangeSum_to_interval {R : Type*} [Semiring R] (f : ℕ → R) (h : f 0 = 0) :
    (∑ a ∈ range 7, f a) = ∑ a ∈ Icc (1:ℕ) 6, f a := by
  have disjoint : 0 ∉ Icc (1:ℕ) 6 := by decide
  rw [show range 7 = insert 0 (Icc (1:ℕ) 6) by decide, sum_insert disjoint, h, zero_add]

private theorem exponent_period {M : Type*} [Monoid M] (a : M) (k d : ℕ)
    (h : a^d = 1) : a^k = a^(k % d) := by
  calc
    a^k = a^(k % d + d * (k / d)) := by rw [Nat.mod_add_div]
    _ = a^(k % d) := by rw [pow_add, pow_mul, h, one_pow, mul_one]

private theorem cast_power_sum (q k : ℕ) (hk : 0 < k) :
    ((∑ a ∈ range 7, (a:ℤ)^k : ℤ) : ZMod q) =
      ∑ a ∈ Icc (1:ℕ) 6, (a:ZMod q) ^ k := by
  push_cast
  apply rangeSum_to_interval
  simp [Nat.ne_of_gt hk]

private theorem table_seven (r : ℕ) (h0 : 0 < r) (h6 : r < 6) :
    (∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 7)^r) = 0 := by
  interval_cases r <;> decide +kernel

private theorem table_forty_nine (r : ℕ) (hr : r < 42) (hm : r % 6 = 2)
    (hz : (∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 49)^r) = 0) : r = 14 := by
  have cases : r = 2 ∨ r = 8 ∨ r = 14 ∨ r = 20 ∨ r = 26 ∨ r = 32 ∨ r = 38 := by omega
  rcases cases with he | he | he | he | he | he | he <;> subst r <;>
    first | rfl | (exfalso; exact (by decide +kernel : (∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 49)^_) ≠ 0) hz)

theorem multiple_of_six (k : ℕ) (hk : 0 < k)
    (h : ¬ (7:ℤ) ∣ ∑ a ∈ range 7, (a:ℤ)^k) : k % 6 = 0 := by
  have nc : ((∑ a ∈ range 7, (a:ℤ)^k : ℤ) : ZMod 7) ≠ 0 := by
    intro hz
    exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
  rw [cast_power_sum 7 k hk] at nc
  have power (a : ℕ) (ha : a ∈ Icc (1:ℕ) 6) : (a : ZMod 7)^6 = 1 := by
    obtain ⟨h1,h6⟩ := mem_Icc.mp ha
    interval_cases a <;> decide +kernel
  have e : (∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 7)^k) = ∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 7)^(k%6) :=
    sum_congr rfl fun a ha => exponent_period _ _ _ (power a ha)
  rw [e] at nc
  by_contra nonzero
  exact nc (table_seven _ (Nat.pos_of_ne_zero nonzero) (Nat.mod_lt _ (by decide)))

theorem residue_fourteen (k : ℕ) (h2 : k % 6 = 2)
    (h : (49:ℤ) ∣ ∑ a ∈ range 7, (a:ℤ)^k) : k % 42 = 14 := by
  have hz : ((∑ a ∈ range 7, (a:ℤ)^k : ℤ) : ZMod 49) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
  rw [cast_power_sum 49 k (by omega)] at hz
  have power (a : ℕ) (ha : a ∈ Icc (1:ℕ) 6) : (a : ZMod 49)^42 = 1 := by
    obtain ⟨h1,h6⟩ := mem_Icc.mp ha
    interval_cases a <;> decide +kernel
  have e : (∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 49)^k) = ∑ a ∈ Icc (1:ℕ) 6, (a:ZMod 49)^(k%42) :=
    sum_congr rfl fun a ha => exponent_period _ _ _ (power a ha)
  rw [e] at hz
  apply table_forty_nine _ (Nat.mod_lt _ (by decide)) _ hz
  rwa [Nat.mod_mod_of_dvd _ (by decide : 6 ∣ 42)]

end A68206Residues

namespace A68206Integration

open Finset

theorem from_local
    (denominator : ∀ k : ℕ, 0 < k → 7 ∣ (bernoulli k).den →
      ¬ (7:ℤ) ∣ ∑ a ∈ range 7, (a:ℤ)^k)
    (numerator : ∀ k : ℕ, 2 ≤ k → Even k → 7 ∣ (bernoulli k).num.natAbs →
      (49:ℤ) ∣ ∑ a ∈ range 7, (a:ℤ)^k) :
    type_of% @OMA.S_oeis_a068206.main := by
  intro n hn isTerm
  unfold OMA.S_oeis_a068206.IsTerm at isTerm
  have hd : 7 ∣ (bernoulli (2*n-2)).den := isTerm ▸ Nat.gcd_dvd_right _ _
  have hn' : 7 ∣ (bernoulli (2*n)).num.natAbs := isTerm ▸ Nat.gcd_dvd_left _ _
  have above : 1 < n := by
    by_contra! bad
    have eq : n = 1 := by omega
    subst n
    norm_num [bernoulli_zero] at hd
  have onSix := A68206Residues.multiple_of_six (2*n-2) (by omega)
    (denominator (2*n-2) (by omega) hd)
  have atTwo : (2*n)%6 = 2 := by omega
  have evenK : Even (2*n) := ⟨n, by omega⟩
  have congr := A68206Residues.residue_fourteen (2*n) atTwo
    (numerator (2*n) (by omega) evenK hn')
  exact ⟨n/21, by omega⟩

end A68206Integration

theorem OMA.solution : type_of% @OMA.S_oeis_a068206.main :=
  A68206Integration.from_local A68206Faulhaber.bernoulli_den_sum A68206Faulhaber.seven_sum_sq
