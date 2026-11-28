import OMAStatements.S_oeis_a294515

namespace OMA.S_oeis_a294515





namespace LangPadic

/-- Sum_{i=1..N} 1/(i(mi - s)), indexed by i - 1 in `range N`. -/
def Vs (m s N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, (1 : ℚ) / (((i + 1 : ℕ) : ℚ) * ((m * (i + 1) - s : ℕ) : ℚ))

/-- p-integral rationals. -/
def PInt (p : ℕ) (x : ℚ) : Prop := ¬ p ∣ x.den

section PInt

variable {p : ℕ}

theorem pint_add (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x + y) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp (Nat.dvd_trans h (Rat.add_den_dvd x y)) with h1 | h1
  · exact hx h1
  · exact hy h1

theorem pint_mul (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x * y) := by
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp (Nat.dvd_trans h (Rat.mul_den_dvd x y)) with h1 | h1
  · exact hx h1
  · exact hy h1

theorem pint_neg {x : ℚ} (hx : PInt p x) : PInt p (-x) := by
  unfold PInt at *
  rwa [Rat.den_neg_eq_den]

theorem pint_sub (hp : p.Prime) {x y : ℚ} (hx : PInt p x) (hy : PInt p y) : PInt p (x - y) := by
  rw [sub_eq_add_neg]; exact pint_add hp hx (pint_neg hy)

theorem pint_int (hp : p.Prime) (a : ℤ) : PInt p (a : ℚ) := by
  unfold PInt; simpa using hp.not_dvd_one

theorem pint_nat (hp : p.Prime) (a : ℕ) : PInt p (a : ℚ) := by
  unfold PInt; simpa using hp.not_dvd_one

theorem pint_zero (hp : p.Prime) : PInt p 0 := by
  unfold PInt; simpa using hp.not_dvd_one

theorem pint_inv_nat {a : ℕ} (ha : ¬ p ∣ a) : PInt p (1 / (a : ℚ)) := by
  unfold PInt
  rw [one_div, Rat.inv_natCast_den]
  split_ifs with h
  · subst h; exact absurd (dvd_zero p) ha
  · exact ha

theorem pint_div_nat (hp : p.Prime) (b : ℕ) {a : ℕ} (ha : ¬ p ∣ a) :
    PInt p ((b : ℚ) / (a : ℚ)) := by
  rw [div_eq_mul_one_div]; exact pint_mul hp (pint_nat hp b) (pint_inv_nat ha)

/-- Removing a p-integral summand does not change p-integrality. -/
theorem pint_add_iff (hp : p.Prime) {x y : ℚ} (hy : PInt p y) : PInt p (x + y) ↔ PInt p x := by
  constructor
  · intro h
    have := pint_sub hp h hy
    rwa [add_sub_cancel_right] at this
  · intro h; exact pint_add hp h hy

/-- Multiplying by a p-adic unit `a/b` does not change p-integrality. -/
theorem pint_mul_unit_iff (hp : p.Prime) {a : ℕ} (ha : ¬ p ∣ a) (x : ℚ) :
    PInt p ((a : ℚ) * x) ↔ PInt p x := by
  have ha0 : (a : ℚ) ≠ 0 := by
    intro h; apply ha; rw [Nat.cast_eq_zero.mp h]; exact dvd_zero p
  constructor
  · intro h
    have := pint_mul hp (pint_inv_nat ha) h
    rwa [← mul_assoc, one_div_mul_cancel ha0, one_mul] at this
  · intro h; exact pint_mul hp (pint_nat hp a) h

/-- `0 <= v_p(x)` iff x is p-integral. -/
theorem zero_le_val_iff (hp : p.Prime) {x : ℚ} (hx : x ≠ 0) : 0 ≤ padicValRat p x ↔ PInt p x := by
  haveI := Fact.mk hp
  have hv : padicValRat p x = padicValNat p x.num.natAbs - padicValNat p x.den := rfl
  constructor
  · intro h hd
    have hnd : ¬ p ∣ x.num.natAbs := by
      intro hn
      have := Nat.dvd_gcd hn hd
      rw [x.reduced] at this
      exact hp.not_dvd_one this
    have h1 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero hd
    rw [hv, padicValNat.eq_zero_of_not_dvd hnd] at h
    omega
  · intro h
    rw [hv, padicValNat.eq_zero_of_not_dvd h]
    simp

/-- `k <= v_p(x)` iff `x / p^k` is p-integral. -/
theorem le_val_iff (hp : p.Prime) {x : ℚ} (hx : x ≠ 0) (k : ℕ) :
    (k : ℤ) ≤ padicValRat p x ↔ PInt p (x / (p : ℚ) ^ k) := by
  haveI := Fact.mk hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpk : (p : ℚ) ^ k ≠ 0 := pow_ne_zero k hp0
  rw [← zero_le_val_iff hp (div_ne_zero hx hpk), padicValRat.div hx hpk, padicValRat.pow,
    padicValRat.self hp.one_lt]
  omega

end PInt

section ZModCast

variable {p : ℕ} [hpf : Fact p.Prime]

theorem den_cast_ne_zero {x : ℚ} (hx : PInt p x) : ((x.den : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact hx

/-- Casting a finite sum of p-integral rationals into ZMod p. -/
theorem cast_sum (S : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ i ∈ S, PInt p (f i)) :
    PInt p (∑ i ∈ S, f i) ∧ ((∑ i ∈ S, f i : ℚ) : ZMod p) = ∑ i ∈ S, ((f i : ℚ) : ZMod p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨by unfold PInt; simp [hpf.out.not_dvd_one], by simp⟩
  | insert a S ha ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hfa := hf a (Finset.mem_insert_self a S)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine ⟨pint_add hpf.out hfa h1, ?_⟩
    rw [Rat.cast_add_of_ne_zero (den_cast_ne_zero hfa) (den_cast_ne_zero h1), h2]

/-- A p-integral rational whose image in ZMod p vanishes is p times a p-integral rational. -/
theorem pint_div_p {x : ℚ} (hx : PInt p x) (h0 : ((x : ℚ) : ZMod p) = 0) : PInt p (x / p) := by
  have hp := hpf.out
  have hd := den_cast_ne_zero hx
  rw [Rat.cast_def] at h0
  have hnum : ((x.num : ℤ) : ZMod p) = 0 := by
    rcases div_eq_zero_iff.mp h0 with h | h
    · exact h
    · exact absurd h hd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hnum
  obtain ⟨t, ht⟩ := hnum
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : x / p = (t : ℚ) * (1 / (x.den : ℚ)) := by
    conv_lhs => rw [← Rat.num_div_den x, ht]
    push_cast
    field_simp
  rw [e]
  exact pint_mul hp (pint_int hp t) (pint_inv_nat hx)

/-- Sums over `range p` of a function of the residue equal sums over ZMod p. -/
theorem sum_range_eq_sum_zmod (F : ZMod p → ZMod p) :
    ∑ j ∈ Finset.range p, F (j : ZMod p) = ∑ x : ZMod p, F x := by
  symm
  apply Finset.sum_nbij' (fun x : ZMod p => x.val) (fun j : ℕ => (j : ZMod p))
  · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
  · intro j _; exact Finset.mem_univ _
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro j hj; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hj)
  · intro x _; rw [ZMod.natCast_zmod_val]

theorem sum_inv_zmod (hp3 : 3 ≤ p) : ∑ y : ZMod p, y⁻¹ = 0 := by
  have h1 : ∑ y : ZMod p, y⁻¹ = ∑ y : ZMod p, y :=
    Fintype.sum_equiv (Equiv.inv (ZMod p)) _ _ (fun x => rfl)
  have h2 : ∑ y : ZMod p, y = ∑ y : ZMod p, -y :=
    Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => by simp)
  rw [Finset.sum_neg_distrib] at h2
  have h3 : (2 : ZMod p) * ∑ y : ZMod p, y = 0 := by rw [two_mul]; nth_rewrite 1 [h2]; ring
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [h1]
  exact (mul_eq_zero.mp h3).resolve_left h2ne

theorem sum_affine_inv (hp3 : 3 ≤ p) (a b : ZMod p) (ha : a ≠ 0) :
    ∑ x : ZMod p, (a * x + b)⁻¹ = 0 := by
  rw [← sum_inv_zmod hp3]
  exact Fintype.sum_equiv ((Equiv.mulLeft₀ a ha).trans (Equiv.addRight b)) _ _
    (fun x => by simp)

end ZModCast

/-- The unit part of one term: [p ∤ mx - s] m/(mx - s) - [p ∤ x]/x. -/
def g (m s p x : ℕ) : ℚ :=
  (if p ∣ m * x - s then 0 else (m : ℚ) / ((m * x - s : ℕ) : ℚ)) - (if p ∣ x then 0 else 1 / (x : ℚ))

section Block

variable {m s p : ℕ} [hpf : Fact p.Prime]

theorem g_pint (x : ℕ) : PInt p (g m s p x) := by
  have hp := hpf.out
  unfold g
  apply pint_sub hp
  · split_ifs with h
    · exact pint_zero hp
    · exact pint_div_nat hp m h
  · split_ifs with h
    · exact pint_zero hp
    · exact pint_inv_nat h

theorem g_cast (x : ℕ) :
    ((g m s p x : ℚ) : ZMod p) = (m : ZMod p) * ((m * x - s : ℕ) : ZMod p)⁻¹ - ((x : ℕ) : ZMod p)⁻¹ := by
  have hp := hpf.out
  have hA : PInt p (if p ∣ m * x - s then 0 else (m : ℚ) / ((m * x - s : ℕ) : ℚ)) := by
    split_ifs with h
    · exact pint_zero hp
    · exact pint_div_nat hp m h
  have hB : PInt p (if p ∣ x then 0 else 1 / (x : ℚ)) := by
    split_ifs with h
    · exact pint_zero hp
    · exact pint_inv_nat h
  unfold g
  rw [Rat.cast_sub_of_ne_zero (den_cast_ne_zero hA) (den_cast_ne_zero hB)]
  congr 1
  · split_ifs with h
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr h]; simp
    · have h' : ((m * x - s : ℕ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      rw [Rat.cast_div_of_ne_zero (by simp) (by simpa using h')]
      simp [div_eq_mul_inv]
  · split_ifs with h
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr h]; simp
    · have h' : ((x : ℕ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
      rw [one_div, Rat.cast_inv_of_ne_zero (by simpa using h')]
      simp

/-- One block of p consecutive terms has unit part divisible by p. -/
theorem block_pint (hp3 : 3 ≤ p) (hpm : ¬ p ∣ m) (hsm : s ≤ m) (M : ℕ) :
    PInt p ((∑ j ∈ Finset.range p, g m s p (p * M + j + 1)) / p) := by
  have hp := hpf.out
  obtain ⟨h1, h2⟩ := cast_sum (Finset.range p) (fun j => g m s p (p * M + j + 1))
    (fun j _ => g_pint _)
  apply pint_div_p h1
  rw [h2]
  simp only [g_cast]
  have hm0 : (m : ZMod p) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  have e1 : ∀ j : ℕ, ((m * (p * M + j + 1) - s : ℕ) : ZMod p) =
      (m : ZMod p) * (j : ZMod p) + ((m : ZMod p) - (s : ZMod p)) := by
    intro j
    rw [Nat.cast_sub (Nat.le_trans hsm (Nat.le_mul_of_pos_right m (by omega)))]
    push_cast
    rw [ZMod.natCast_self]
    ring
  have e2 : ∀ j : ℕ, (((p * M + j + 1 : ℕ) : ℕ) : ZMod p) = 1 * (j : ZMod p) + 1 := by
    intro j
    push_cast
    rw [ZMod.natCast_self]
    ring
  simp only [e1, e2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_range_eq_sum_zmod (fun x => ((m : ZMod p) * x + ((m : ZMod p) - (s : ZMod p)))⁻¹),
    sum_range_eq_sum_zmod (fun x => (1 * x + 1)⁻¹), sum_affine_inv hp3 _ _ hm0,
    sum_affine_inv hp3 _ _ one_ne_zero]
  simp

/-- The unit part of the first pM terms. -/
def C (m s p M : ℕ) : ℚ := ∑ i ∈ Finset.range (p * M), g m s p (i + 1)

theorem C_pint (hp3 : 3 ≤ p) (hpm : ¬ p ∣ m) (hsm : s ≤ m) (M : ℕ) : PInt p (C m s p M / p) := by
  have hp := hpf.out
  induction M with
  | zero => simpa [C] using pint_zero hp
  | succ M ih =>
    have e : C m s p (M + 1) = C m s p M + ∑ j ∈ Finset.range p, g m s p (p * M + j + 1) := by
      unfold C
      rw [show p * (M + 1) = p * M + p by ring, Finset.sum_range_add]
    rw [e, add_div]
    exact pint_add hp ih (block_pint hp3 hpm hsm M)

end Block

/-- The term 1/(x(mx - s)). -/
def t (m s x : ℕ) : ℚ := 1 / ((x : ℚ) * ((m * x - s : ℕ) : ℚ))

theorem Vs_eq (m s N : ℕ) : Vs m s N = ∑ i ∈ Finset.range N, t m s (i + 1) := rfl

theorem term_split (m s p x : ℕ) (hx : 1 ≤ x) (hsm : s < m) :
    (s : ℚ) * t m s x = g m s p x + (if p ∣ m * x - s then (m : ℚ) / ((m * x - s : ℕ) : ℚ) else 0)
      - (if p ∣ x then 1 / (x : ℚ) else 0) := by
  have hle : s ≤ m * x := Nat.le_trans hsm.le (Nat.le_mul_of_pos_right m hx)
  have hpos : 0 < m * x - s := by
    have : m ≤ m * x := Nat.le_mul_of_pos_right m hx
    omega
  have hx0 : (x : ℚ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hy0 : ((m * x - s : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hcast : ((m * x - s : ℕ) : ℚ) = (m : ℚ) * x - s := by rw [Nat.cast_sub hle]; push_cast; ring
  have key : (s : ℚ) * t m s x = (m : ℚ) / ((m * x - s : ℕ) : ℚ) - 1 / (x : ℚ) := by
    unfold t
    field_simp
    rw [hcast]
    ring
  rw [key]
  unfold g
  split_ifs <;> ring

section Thm2

variable {m s p d0 : ℕ}

/-- In a block of p consecutive x, only x = pM + d0 has p | mx - s. -/
theorem uniq_s (hp : p.Prime) (hpm : ¬ p ∣ m) (hsm : s < m) (hd1 : 1 ≤ d0) (hd2 : d0 ≤ p)
    (hd : p ∣ m * d0 - s) (M j : ℕ) (hj : j < p) (h : p ∣ m * (p * M + j + 1) - s) :
    j = d0 - 1 := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, hb⟩ := hd
  have h1 : s ≤ m * d0 := Nat.le_trans hsm.le (Nat.le_mul_of_pos_right m hd1)
  have h2 : s ≤ m * (p * M + j + 1) := Nat.le_trans hsm.le (Nat.le_mul_of_pos_right m (by omega))
  have hz : (m : ℤ) * ((j : ℤ) + 1 - d0) = (p : ℤ) * ((a : ℤ) - b - m * M) := by
    have ea : ((m * (p * M + j + 1) - s : ℕ) : ℤ) = ((p * a : ℕ) : ℤ) := by rw [ha]
    have eb : ((m * d0 - s : ℕ) : ℤ) = ((p * b : ℕ) : ℤ) := by rw [hb]
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at ea eb
    linear_combination ea - eb
  have hpz : (p : ℤ) ∣ (m : ℤ) * ((j : ℤ) + 1 - d0) := ⟨_, hz⟩
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpr.dvd_or_dvd hpz with hm | hk
  · exact absurd (Int.natCast_dvd_natCast.mp hm) hpm
  · obtain ⟨k, hk⟩ := hk
    have hp1 : (1 : ℤ) ≤ p := by exact_mod_cast hp.one_lt.le
    have hlo : -(p : ℤ) < (j : ℤ) + 1 - d0 := by push_cast; omega
    have hhi : (j : ℤ) + 1 - d0 < p := by omega
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hk' | hk' | hk'
      · nlinarith
      · exact hk'
      · nlinarith
    rw [hk0, mul_zero] at hk
    omega

/-- In a block of p consecutive x, only x = p(M+1) is a multiple of p. -/
theorem uniq_p (hp : p.Prime) (M j : ℕ) (hj : j < p) (h : p ∣ p * M + j + 1) : j = p - 1 := by
  have h1 : p ∣ j + 1 := by
    have : p * M + j + 1 = p * M + (j + 1) := by ring
    rw [this] at h
    exact (Nat.dvd_add_right (dvd_mul_right p M)).mp h
  have := Nat.le_of_dvd (by omega) h1
  omega

/-- The identity s V(pM) = s'' W(M)/p + C(M). -/
theorem identity (hp : p.Prime) (hpm : ¬ p ∣ m) (hs : 1 ≤ s) (hsm : s < m) (hd1 : 1 ≤ d0)
    (hd2 : d0 ≤ p) (hd : p ∣ m * d0 - s) (M : ℕ) :
    (s : ℚ) * Vs m s (p * M) =
      ((m - (m * d0 - s) / p : ℕ) : ℚ) * Vs m (m - (m * d0 - s) / p) M / p + C m s p M := by
  set c := (m * d0 - s) / p with hc
  have hpc : p * c = m * d0 - s := Nat.mul_div_cancel' hd
  have h1 : s ≤ m * d0 := Nat.le_trans hsm.le (Nat.le_mul_of_pos_right m hd1)
  have hc1 : 1 ≤ c := by
    have : m ≤ m * d0 := Nat.le_mul_of_pos_right m hd1
    have : 0 < p * c := by omega
    exact Nat.pos_of_mul_pos_left this
  have hcm : c < m := by
    have : m * d0 ≤ m * p := Nat.mul_le_mul_left m hd2
    have : p * c < p * m := by rw [mul_comm p m]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction M with
  | zero => simp [Vs, C]
  | succ M ih =>
    have eV : Vs m s (p * (M + 1)) = Vs m s (p * M) + ∑ j ∈ Finset.range p, t m s (p * M + j + 1) := by
      rw [Vs_eq, Vs_eq, show p * (M + 1) = p * M + p by ring, Finset.sum_range_add]
    have eW : Vs m (m - c) (M + 1) = Vs m (m - c) M + t m (m - c) (M + 1) := by
      rw [Vs_eq, Vs_eq, Finset.sum_range_succ]
    have eC : C m s p (M + 1) = C m s p M + ∑ j ∈ Finset.range p, g m s p (p * M + j + 1) := by
      unfold C
      rw [show p * (M + 1) = p * M + p by ring, Finset.sum_range_add]
    -- the block
    have hblock : (s : ℚ) * ∑ j ∈ Finset.range p, t m s (p * M + j + 1) =
        ∑ j ∈ Finset.range p, g m s p (p * M + j + 1)
          + (m : ℚ) / ((m * (p * M + d0) - s : ℕ) : ℚ) - 1 / ((p * M + p : ℕ) : ℚ) := by
      rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun j _ => term_split m s p (p * M + j + 1) (by omega) hsm)]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have e1 : ∑ j ∈ Finset.range p, (if p ∣ m * (p * M + j + 1) - s
          then (m : ℚ) / ((m * (p * M + j + 1) - s : ℕ) : ℚ) else 0) =
          (m : ℚ) / ((m * (p * M + d0) - s : ℕ) : ℚ) := by
        rw [Finset.sum_eq_single (d0 - 1)]
        · rw [show p * M + (d0 - 1) + 1 = p * M + d0 by omega, if_pos]
          rw [show m * (p * M + d0) - s = p * (m * M) + (m * d0 - s) by
            rw [mul_add, show m * (p * M) = p * (m * M) by ring]; omega]
          exact dvd_add (dvd_mul_right p _) hd
        · intro j hj hne
          rw [if_neg]
          intro hdv
          exact hne (uniq_s hp hpm hsm hd1 hd2 hd M j (Finset.mem_range.mp hj) hdv)
        · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      have e2 : ∑ j ∈ Finset.range p, (if p ∣ p * M + j + 1 then 1 / ((p * M + j + 1 : ℕ) : ℚ)
          else 0) = 1 / ((p * M + p : ℕ) : ℚ) := by
        rw [Finset.sum_eq_single (p - 1)]
        · rw [show p * M + (p - 1) + 1 = p * M + p by have := hp.one_lt; omega, if_pos]
          exact dvd_add (dvd_mul_right p M) (dvd_refl p)
        · intro j hj hne
          rw [if_neg]
          intro hdv
          exact hne (uniq_p hp M j (Finset.mem_range.mp hj) hdv)
        · intro h; exact absurd (Finset.mem_range.mpr (by have := hp.one_lt; omega)) h
      rw [e1, e2]
    -- the two special terms give s'' t(M+1) / p
    have hspec : (m : ℚ) / ((m * (p * M + d0) - s : ℕ) : ℚ) - 1 / ((p * M + p : ℕ) : ℚ) =
        ((m - c : ℕ) : ℚ) * t m (m - c) (M + 1) / p := by
      have n1 : m * (p * M + d0) - s = p * (m * M + c) := by
        rw [mul_add, mul_add, show m * (p * M) = p * (m * M) by ring]; omega
      have n2 : m * (M + 1) - (m - c) = m * M + c := by rw [mul_add]; omega
      unfold t
      rw [n1, n2, Nat.cast_sub hcm.le]
      push_cast
      have hM : ((M : ℚ) + 1) ≠ 0 := by positivity
      have hmc : ((m : ℚ) * M + c) ≠ 0 := by
        have : (1 : ℚ) ≤ c := by exact_mod_cast hc1
        positivity
      field_simp
      ring
    rw [eV, eW, eC, mul_add, ih, hblock]
    rw [show ((m - c : ℕ) : ℚ) * (Vs m (m - c) M + t m (m - c) (M + 1)) / p =
      ((m - c : ℕ) : ℚ) * Vs m (m - c) M / p + ((m - c : ℕ) : ℚ) * t m (m - c) (M + 1) / p by ring]
    rw [← hspec]
    ring

theorem Vs_pos (m s N : ℕ) (hsm : s < m) (hN : 1 ≤ N) : 0 < Vs m s N := by
  rw [Vs_eq]
  apply Finset.sum_pos
  · intro i _
    unfold t
    have : 0 < m * (i + 1) - s := by
      have : m ≤ m * (i + 1) := Nat.le_mul_of_pos_right m (by omega)
      omega
    positivity
  · exact ⟨0, Finset.mem_range.mpr hN⟩

/-- Theorem 2: v_p(V(pM)) >= 1 iff v_p(W(M)) >= 2, with W = Vs m s'' and s'' = m - (m d0 - s)/p. -/
theorem thm2 (hp : p.Prime) (hp3 : 3 ≤ p) (hpm : ¬ p ∣ m) (hps : ¬ p ∣ s) (hs : 1 ≤ s)
    (hsm : s < m) (hd1 : 1 ≤ d0) (hd2 : d0 ≤ p) (hd : p ∣ m * d0 - s)
    (hps2 : ¬ p ∣ (m - (m * d0 - s) / p)) (M : ℕ) (hM : 1 ≤ M) :
    1 ≤ padicValRat p (Vs m s (p * M)) ↔
      2 ≤ padicValRat p (Vs m (m - (m * d0 - s) / p) M) := by
  haveI := Fact.mk hp
  set s2 := m - (m * d0 - s) / p with hs2
  have hs2m : s2 < m := by
    have : 1 ≤ (m * d0 - s) / p := by
      have hpc : p * ((m * d0 - s) / p) = m * d0 - s := Nat.mul_div_cancel' hd
      have : m ≤ m * d0 := Nat.le_mul_of_pos_right m hd1
      have : 0 < p * ((m * d0 - s) / p) := by omega
      exact Nat.pos_of_mul_pos_left this
    omega
  have hV := Vs_pos m s (p * M) hsm (by nlinarith [hp.one_lt])
  have hW := Vs_pos m s2 M hs2m hM
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h1 := le_val_iff hp hV.ne' 1
  have h2 := le_val_iff hp hW.ne' 2
  push_cast at h1 h2
  rw [pow_one] at h1
  rw [h1, h2, ← pint_mul_unit_iff hp hps]
  have e : (s : ℚ) * (Vs m s (p * M) / p) =
      (s2 : ℚ) * (Vs m s2 M / p ^ 2) + C m s p M / p := by
    rw [← mul_div_assoc, identity hp hpm hs hsm hd1 hd2 hd M]
    field_simp
    ring
  rw [e, pint_add_iff hp (C_pint hp3 hpm hsm.le M), pint_mul_unit_iff hp hps2]

/-- The variant for p | s with s = p s', p ∤ s': v_p(V(pM)) >= 0 iff v_p(W(M)) >= 2. -/
theorem thm2_ps (hp : p.Prime) (hp3 : 3 ≤ p) (hpm : ¬ p ∣ m) {s' : ℕ} (hss : s = p * s')
    (hps' : ¬ p ∣ s') (hs : 1 ≤ s) (hsm : s < m) (hd1 : 1 ≤ d0) (hd2 : d0 ≤ p)
    (hd : p ∣ m * d0 - s) (hps2 : ¬ p ∣ (m - (m * d0 - s) / p)) (M : ℕ) (hM : 1 ≤ M) :
    0 ≤ padicValRat p (Vs m s (p * M)) ↔
      2 ≤ padicValRat p (Vs m (m - (m * d0 - s) / p) M) := by
  haveI := Fact.mk hp
  set s2 := m - (m * d0 - s) / p with hs2
  have hs2m : s2 < m := by
    have : 1 ≤ (m * d0 - s) / p := by
      have hpc : p * ((m * d0 - s) / p) = m * d0 - s := Nat.mul_div_cancel' hd
      have : m ≤ m * d0 := Nat.le_mul_of_pos_right m hd1
      have : 0 < p * ((m * d0 - s) / p) := by omega
      exact Nat.pos_of_mul_pos_left this
    omega
  have hV := Vs_pos m s (p * M) hsm (by nlinarith [hp.one_lt])
  have hW := Vs_pos m s2 M hs2m hM
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h2 := le_val_iff hp hW.ne' 2
  push_cast at h2
  rw [zero_le_val_iff hp hV.ne', h2, ← pint_mul_unit_iff hp hps']
  have e : (s' : ℚ) * Vs m s (p * M) = (s2 : ℚ) * (Vs m s2 M / p ^ 2) + C m s p M / p := by
    have hid := identity hp hpm hs hsm hd1 hd2 hd M
    have hsq : (s : ℚ) = (p : ℚ) * s' := by exact_mod_cast hss
    rw [hsq] at hid
    have e1 : (s' : ℚ) * Vs m s (p * M) = ((p : ℚ) * s' * Vs m s (p * M)) / p := by
      field_simp
    rw [e1, hid]
    field_simp
    ring
  rw [e, pint_add_iff hp (C_pint hp3 hpm hsm.le M), pint_mul_unit_iff hp hps2]

end Thm2

end LangPadic

namespace LangPadic

/-- For q > 0, p divides the numerator of q iff v_p(q) >= 1. -/
theorem dvd_num_iff {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : 0 < q) :
    p ∣ q.num.natAbs ↔ 1 ≤ padicValRat p q := by
  haveI := Fact.mk hp
  have hv : padicValRat p q = padicValNat p q.num.natAbs - padicValNat p q.den := rfl
  have hn0 : q.num.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (Rat.num_pos.mpr hq).ne'
  constructor
  · intro h
    have hd : ¬ p ∣ q.den := by
      intro hd
      have := Nat.dvd_gcd h hd
      rw [q.reduced] at this
      exact hp.not_dvd_one this
    have h1 : 1 ≤ padicValNat p q.num.natAbs := one_le_padicValNat_of_dvd hn0 h
    rw [hv, padicValNat.eq_zero_of_not_dvd hd]
    omega
  · intro h
    by_contra hc
    rw [hv, padicValNat.eq_zero_of_not_dvd hc] at h
    omega

end LangPadic

namespace LangCriterion

/-- The numerator of `A / B` for natural numbers `A` and `B > 0`. -/
theorem num_div_nat (A B : ℕ) (hB : 0 < B) :
    ((A : ℚ) / B).num = ((A / Nat.gcd A B : ℕ) : ℤ) := by
  have hg0 : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_right A hB
  have hA : Nat.gcd A B ∣ A := Nat.gcd_dvd_left A B
  have hB' : Nat.gcd A B ∣ B := Nat.gcd_dvd_right A B
  have hcop : Nat.Coprime (A / Nat.gcd A B) (B / Nat.gcd A B) := Nat.coprime_div_gcd_div_gcd hg0
  have hBg : 0 < B / Nat.gcd A B := Nat.div_pos (Nat.le_of_dvd hB hB') hg0
  have hg' : ((Nat.gcd A B : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have e : (A : ℚ) / B =
      (((A / Nat.gcd A B : ℕ) : ℤ) : ℚ) / (((B / Nat.gcd A B : ℕ) : ℤ) : ℚ) := by
    simp only [Int.cast_natCast]
    rw [Nat.cast_div hA hg', Nat.cast_div hB' hg']
    field_simp
  rw [e, Rat.num_div_eq_of_coprime (by exact_mod_cast hBg)]
  rw [Int.natAbs_natCast, Int.natAbs_natCast]
  exact hcop

/-- For `q > 0`, `N / q = (N * q.den) / q.num` as a quotient of natural numbers. -/
theorem div_eq (q : ℚ) (hq : 0 < q) (N : ℕ) :
    (N : ℚ) / q = ((N * q.den : ℕ) : ℚ) / (q.num.natAbs : ℕ) := by
  have hnum : ((q.num.natAbs : ℕ) : ℤ) = q.num := by
    rw [Int.natCast_natAbs, abs_of_nonneg (Rat.num_nonneg.mpr hq.le)]
  have hnum' : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by rw [← Int.cast_natCast, hnum]
  have hn0 : (q.num : ℚ) ≠ 0 := by exact_mod_cast (Rat.num_pos.mpr hq).ne'
  have hd0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [hnum']
  conv_lhs => rw [← Rat.num_div_den q]
  push_cast
  field_simp

/-- For `q > 0` and `N > 0`, `q.den = (N / q).num / N` iff `N` is coprime to the numerator. -/
theorem hm_criterion (q : ℚ) (hq : 0 < q) (N : ℕ) (hN : 0 < N) :
    ((q.den : ℚ) = (((N : ℚ) / q).num : ℚ) / N) ↔ Nat.Coprime N q.num.natAbs := by
  have hP : 0 < q.num.natAbs := Int.natAbs_pos.mpr (Rat.num_pos.mpr hq).ne'
  have hQ : 0 < q.den := q.den_pos
  have hcop : Nat.Coprime q.den q.num.natAbs := q.reduced.symm
  rw [div_eq q hq N, num_div_nat _ _ hP, Nat.Coprime.gcd_mul_right_cancel N hcop]
  have hgN : Nat.gcd N q.num.natAbs ∣ N := Nat.gcd_dvd_left N _
  have hg0 : 0 < Nat.gcd N q.num.natAbs := Nat.gcd_pos_of_pos_left _ hN
  have hg' : ((Nat.gcd N q.num.natAbs : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hg0.ne'
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hQ' : (q.den : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
  have e : ((((N * q.den / Nat.gcd N q.num.natAbs : ℕ) : ℤ) : ℚ)) / N =
      (q.den : ℚ) / Nat.gcd N q.num.natAbs := by
    rw [Int.cast_natCast, Nat.cast_div (Dvd.dvd.mul_right hgN _) hg']
    push_cast
    field_simp
  rw [e]
  constructor
  · intro h
    have h1 : ((Nat.gcd N q.num.natAbs : ℕ) : ℚ) = 1 := by
      field_simp at h
      linarith
    exact_mod_cast h1
  · intro h
    rw [Nat.Coprime] at h
    rw [h]
    simp

end LangCriterion

namespace Pairs

/-- The summand 1/((k+1)(4k+3)) = 1/(u(4u-1)) with u = k+1 of the shorter sum. -/
def term (k : ℕ) : ℚ := 1 / ((k + 1) * (4 * k + 3))

/-- Addition of fractions given as (numerator, denominator), without reduction. -/
def pairAdd (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

/-- Sum of `term` over [lo, lo + len) as an unreduced fraction, split in halves `d` times. -/
def bsumN : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, 0 => (0, 1)
  | 0, lo, _ + 1 => (1, (lo + 1) * (4 * lo + 3))
  | d + 1, lo, len => pairAdd (bsumN d lo (len / 2)) (bsumN d (lo + len / 2) (len - len / 2))

theorem bsumN_spec (d lo len : ℕ) (h : len ≤ 2 ^ d) :
    (bsumN d lo len).2 ≠ 0 ∧
      ((bsumN d lo len).1 : ℚ) / (bsumN d lo len).2 = ∑ k ∈ Finset.range len, term (lo + k) := by
  induction d generalizing lo len with
  | zero =>
    rcases len with _ | _ | len
    · simp [bsumN]
    · refine ⟨by simp [bsumN], ?_⟩
      simp [bsumN, term]
    · simp at h
  | succ d ih =>
    rw [pow_succ] at h
    obtain ⟨hA, eA⟩ := ih lo (len / 2) (by omega)
    obtain ⟨hB, eB⟩ := ih (lo + len / 2) (len - len / 2) (by omega)
    refine ⟨by simp [bsumN, pairAdd, hA, hB], ?_⟩
    have hlen : len = len / 2 + (len - len / 2) := by omega
    conv_rhs => rw [hlen, Finset.sum_range_add]
    simp only [← add_assoc] at eB ⊢
    rw [← eA, ← eB]
    have hA' : ((bsumN d lo (len / 2)).2 : ℚ) ≠ 0 := by exact_mod_cast hA
    have hB' : ((bsumN d (lo + len / 2) (len - len / 2)).2 : ℚ) ≠ 0 := by exact_mod_cast hB
    simp only [bsumN, pairAdd]
    push_cast
    field_simp

/-- The pair for W = Sum_{u=1..25855} 1/(u(4u-1)). -/
def S : ℕ × ℕ := bsumN 15 0 25855

/-- The kernel computation: v_19(Y) = 2870 and 19^2872 divides X. -/
theorem S_spec : 19 ^ 2870 ∣ S.2 ∧ ¬ 19 ∣ S.2 / 19 ^ 2870 ∧ 19 ^ 2872 ∣ S.1 := by
  decide +kernel

end Pairs

theorem V_pos (n : ℕ) : 0 < V n := by
  unfold V
  apply Finset.sum_pos
  · intro k _
    positivity
  · exact ⟨0, by simp⟩

theorem harmonic_eq (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 (n + 1), (1 : ℚ) / ((k : ℚ) * (4 * k - 3)) = V n := by
  have hI : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 1 + 1) := rfl
  rw [hI, Finset.sum_Ico_eq_sum_range, V]
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  have e : (4 * ((1 : ℚ) + k) - 3) = 4 * k + 1 := by ring
  rw [e, add_comm (1 : ℚ) (k : ℚ)]

theorem V_eq_Vs (n : ℕ) : V n = LangPadic.Vs 4 3 (n + 1) := by
  unfold V LangPadic.Vs
  apply Finset.sum_congr rfl
  intro k _
  have e : 4 * (k + 1) - 3 = 4 * k + 1 := by omega
  rw [e]
  push_cast
  ring

theorem W_eq : LangPadic.Vs 4 1 25855 = (Pairs.S.1 : ℚ) / Pairs.S.2 := by
  rw [Pairs.S, (Pairs.bsumN_spec 15 0 25855 (by norm_num)).2]
  unfold LangPadic.Vs Pairs.term
  apply Finset.sum_congr rfl
  intro k _
  have e : 4 * (k + 1) - 1 = 4 * k + 3 := by omega
  rw [e]
  push_cast
  ring

/-- 19^2 divides the numerator of the shorter sum: v_19(W) >= 2. -/
theorem two_le_W : 2 ≤ padicValRat 19 (LangPadic.Vs 4 1 25855) := by
  have hp : Nat.Prime 19 := by norm_num
  have hW := LangPadic.Vs_pos 4 1 25855 (by norm_num) (by norm_num)
  obtain ⟨h1, h2, h3⟩ := Pairs.S_spec
  obtain ⟨Y', hY⟩ := h1
  obtain ⟨X', hX⟩ := h3
  have hY'0 : ¬ 19 ∣ Y' := by
    have : Pairs.S.2 / 19 ^ 2870 = Y' := by
      rw [hY]; exact Nat.mul_div_cancel_left Y' (by positivity)
    rw [← this]; exact h2
  have h := (LangPadic.le_val_iff hp hW.ne' 2).mpr
  push_cast at h
  apply h
  rw [W_eq, hX, hY]
  have e : (((19 ^ 2872 * X' : ℕ) : ℚ) / ((19 ^ 2870 * Y' : ℕ) : ℚ)) / (19 : ℚ) ^ 2 =
      (X' : ℚ) / (Y' : ℚ) := by
    have hY0 : (Y' : ℚ) ≠ 0 := by
      have : Y' ≠ 0 := by intro h0; rw [h0] at hY'0; exact hY'0 (dvd_zero 19)
      exact_mod_cast this
    have hpow : (19 : ℚ) ^ 2872 = (19 : ℚ) ^ 2870 * (19 : ℚ) ^ 2 := by rw [← pow_add]
    push_cast
    rw [hpow]
    field_simp
  rw [e]
  exact LangPadic.pint_div_nat hp X' hY'0

/-- 19 divides the numerator of V(4,1;491244). -/
theorem nineteen_dvd : 19 ∣ (V 491244).num.natAbs := by
  rw [LangPadic.dvd_num_iff (by norm_num) (V_pos 491244), V_eq_Vs,
    show 491244 + 1 = 19 * 25855 by norm_num]
  have h2 := two_le_W
  rw [show (1 : ℕ) = 4 - (4 * 15 - 3) / 19 by norm_num] at h2
  exact (LangPadic.thm2 (m := 4) (s := 3) (p := 19) (d0 := 15) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) 25855 (by norm_num)).mpr h2

/-- Lang's conjecture in A294515 is false: it fails at n = 491244. -/
theorem disproof : ¬ ∀ n : ℕ, (a n : ℚ) = (b (n + 1) : ℚ) / ((n : ℚ) + 1) := by
  intro h
  have h1 := h 491244
  have hc := (LangCriterion.hm_criterion (V 491244) (V_pos 491244) (491244 + 1)
    (by norm_num)).mp (by
      rw [a, b, harmonic_eq] at h1
      push_cast at h1 ⊢
      convert h1 using 2
      norm_num)
  have hg := Nat.dvd_gcd (show 19 ∣ 491244 + 1 by norm_num) nineteen_dvd
  rw [hc] at hg
  exact absurd hg (by norm_num)

end OMA.S_oeis_a294515

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a294515.main) :=
  OMA.S_oeis_a294515.disproof
