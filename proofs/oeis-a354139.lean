import OMAStatements.S_oeis_a354139
import Mathlib

namespace OMA.A354139Proof

/-- The `n`-th power map `ℕ → ZMod q`. -/
def F (q n x : ℕ) : ZMod q := (x : ZMod q) ^ n

theorem icc_eq_range (n k m : ℕ) :
    ∑ i ∈ Finset.Icc 1 m, (k + i) ^ n = ∑ i ∈ Finset.range m, (k + 1 + i) ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 m), ih, Finset.sum_range_succ,
      show k + (m + 1) = k + 1 + m by omega]

theorem cast_window (q n k m : ℕ) :
    ((∑ i ∈ Finset.Icc 1 m, (k + i) ^ n : ℕ) : ZMod q) =
      ∑ i ∈ Finset.range m, F q n (k + 1 + i) := by
  rw [icc_eq_range, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [F, Nat.cast_pow]

theorem shift_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a m : ℕ) :
    (∑ i ∈ Finset.range m, f (a + i)) + f (a + m) =
      f a + ∑ i ∈ Finset.range m, f (a + 1 + i) := by
  have h1 : ∑ i ∈ Finset.range (m + 1), f (a + i) =
      (∑ i ∈ Finset.range m, f (a + i)) + f (a + m) := Finset.sum_range_succ _ _
  have h2 : ∑ i ∈ Finset.range (m + 1), f (a + i) =
      (∑ i ∈ Finset.range m, f (a + (i + 1))) + f (a + 0) := Finset.sum_range_succ' _ _
  have h3 : ∑ i ∈ Finset.range m, f (a + (i + 1)) = ∑ i ∈ Finset.range m, f (a + 1 + i) :=
    Finset.sum_congr rfl fun i _ => by rw [show a + (i + 1) = a + 1 + i by omega]
  rw [← h1, h2, add_zero, h3]
  exact add_comm _ _

/-- `x ≡ y (mod p)` gives `x ^ n ≡ y ^ n (mod p ^ e)` when `p ^ (e - 1) ∣ n`. -/
theorem F_congr {p e n x y : ℕ} (_hp : p.Prime) (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n)
    (hxy : x ≡ y [MOD p]) : F (p ^ e) n x = F (p ^ e) n y := by
  obtain ⟨c, rfl⟩ := hn
  have h1 : (p : ℤ) ∣ (x : ℤ) - (y : ℤ) := Nat.modEq_iff_dvd.mp hxy.symm
  have h2 := dvd_sub_pow_of_dvd_sub h1 (e - 1)
  rw [Nat.sub_add_cancel he] at h2
  have h3 : (((x : ℤ) ^ p ^ (e - 1) : ℤ) : ZMod (p ^ e)) =
      (((y : ℤ) ^ p ^ (e - 1) : ℤ) : ZMod (p ^ e)) := by
    rw [eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact_mod_cast h2
  push_cast at h3
  simp only [F, pow_mul, h3]

theorem F_mod {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n) (x : ℕ) :
    F (p ^ e) n (x % p) = F (p ^ e) n x :=
  F_congr hp he hn (Nat.mod_modEq x p)

theorem F_val_cast {p e n : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n) (x : ℕ) :
    F (p ^ e) n ((x : ZMod p).val) = F (p ^ e) n x := by
  rw [ZMod.val_natCast]
  exact F_mod hp he hn x

theorem F_eq_zero {p e n x : ℕ} (hen : e ≤ n) (hx : p ∣ x) : F (p ^ e) n x = 0 := by
  show ((x : ZMod (p ^ e)) ^ n) = 0
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact (pow_dvd_pow p hen).trans (pow_dvd_pow_of_dvd hx n)

theorem sum_range_zmod {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M] (G : ZMod p → M) :
    ∑ i ∈ Finset.range p, G (i : ZMod p) = ∑ y : ZMod p, G y := by
  refine Finset.sum_nbij' (fun i => (i : ZMod p)) (fun y => y.val) ?_ ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_univ _
  · intro y _
    exact Finset.mem_range.mpr (ZMod.val_lt y)
  · intro i hi
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · intro y _
    exact ZMod.natCast_zmod_val y
  · intro i _
    rfl

/-- Any `p` consecutive terms sum to the full period sum. -/
theorem block {p e n : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n) (b : ℕ) :
    ∑ i ∈ Finset.range p, F (p ^ e) n (b + i) = ∑ y : ZMod p, F (p ^ e) n y.val := by
  calc ∑ i ∈ Finset.range p, F (p ^ e) n (b + i)
      = ∑ i ∈ Finset.range p, F (p ^ e) n (((b : ZMod p) + (i : ZMod p)).val) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Nat.cast_add, F_val_cast hp.out he hn]
    _ = ∑ y : ZMod p, F (p ^ e) n (((b : ZMod p) + y).val) :=
        sum_range_zmod (fun y : ZMod p => F (p ^ e) n (((b : ZMod p) + y).val))
    _ = ∑ y : ZMod p, F (p ^ e) n y.val :=
        Equiv.sum_comp (Equiv.addLeft (b : ZMod p)) (fun y : ZMod p => F (p ^ e) n y.val)

theorem window_mul {p e n : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n) (b t : ℕ) :
    ∑ i ∈ Finset.range (p * t), F (p ^ e) n (b + i) =
      (t : ZMod (p ^ e)) * ∑ y : ZMod p, F (p ^ e) n y.val := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h2 : ∑ x ∈ Finset.range p, F (p ^ e) n (b + (p * t + x)) =
        ∑ y : ZMod p, F (p ^ e) n y.val := by
      rw [← block he hn (b + p * t)]
      exact Finset.sum_congr rfl fun i _ => by rw [add_assoc]
    rw [mul_add_one, Finset.sum_range_add, ih, h2]
    push_cast
    ring

/-- The period sum when `(p - 1) ∣ n`: every unit contributes `1`. -/
theorem S_caseA {p e n : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n)
    (hpn : (p - 1) ∣ n) (hn0 : n ≠ 0) :
    ∑ y : ZMod p, F (p ^ e) n y.val = ((p - 1 : ℕ) : ZMod (p ^ e)) := by
  have hp2 := hp.out.two_le
  have hcop1 : Nat.Coprime p (p - 1) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  have htot : Nat.totient (p ^ e) ∣ n := by
    rw [Nat.totient_prime_pow hp.out (by omega)]
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left _ hcop1) hn hpn
  obtain ⟨c, hc⟩ := htot
  have h0 : F (p ^ e) n (0 : ZMod p).val = 0 := by
    show ((((0 : ZMod p).val : ℕ) : ZMod (p ^ e)) ^ n) = 0
    rw [ZMod.val_zero, Nat.cast_zero, zero_pow hn0]
  have h1 : ∀ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, F (p ^ e) n y.val = 1 := by
    intro y hy
    have hy0 : y ≠ 0 := Finset.ne_of_mem_erase hy
    have hcop : Nat.Coprime y.val (p ^ e) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
      exact Nat.not_dvd_of_pos_of_lt (ZMod.val_pos.mpr hy0) (ZMod.val_lt y)
    have hmod : y.val ^ n ≡ 1 [MOD p ^ e] := by
      rw [hc, pow_mul]
      have := (Nat.ModEq.pow_totient hcop).pow c
      rwa [one_pow] at this
    have h := (ZMod.natCast_eq_natCast_iff (y.val ^ n) 1 (p ^ e)).mpr hmod
    rw [Nat.cast_pow, Nat.cast_one] at h
    exact h
  calc ∑ y : ZMod p, F (p ^ e) n y.val
      = F (p ^ e) n (0 : ZMod p).val +
          ∑ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, F (p ^ e) n y.val :=
        (Finset.add_sum_erase Finset.univ (fun y : ZMod p => F (p ^ e) n y.val)
          (Finset.mem_univ 0)).symm
    _ = 0 + ∑ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, (1 : ZMod (p ^ e)) := by
        rw [h0, Finset.sum_congr rfl h1]
    _ = ((p - 1 : ℕ) : ZMod (p ^ e)) := by
        rw [zero_add, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

/-- The period sum when `(p - 1)` does not divide `n` vanishes modulo `p ^ e`. -/
theorem S_caseB {p e n : ℕ} [hp : Fact p.Prime] (he : 1 ≤ e) (hn : p ^ (e - 1) ∣ n)
    (hpn : ¬ (p - 1) ∣ n) :
    ∑ y : ZMod p, F (p ^ e) n y.val = 0 := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_units, Nat.card_zmod] at hζ
  have hζn : (ζ : ZMod p) ^ n ≠ 1 := by
    intro h
    apply hpn
    rw [← hζ, orderOf_dvd_iff_pow_eq_one]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  have hmul : ∀ y : ZMod p, F (p ^ e) n ((ζ : ZMod p) * y).val =
      F (p ^ e) n (ζ : ZMod p).val * F (p ^ e) n y.val := by
    intro y
    rw [ZMod.val_mul, F_mod hp.out he hn]
    simp only [F, Nat.cast_mul, mul_pow]
  have hsum : ∑ y : ZMod p, F (p ^ e) n y.val =
      F (p ^ e) n (ζ : ZMod p).val * ∑ y : ZMod p, F (p ^ e) n y.val := by
    rw [Finset.mul_sum]
    calc ∑ y : ZMod p, F (p ^ e) n y.val
        = ∑ y : ZMod p, F (p ^ e) n ((ζ : ZMod p) * y).val :=
          (Equiv.sum_comp (Units.mulLeft ζ) (fun y : ZMod p => F (p ^ e) n y.val)).symm
      _ = ∑ y : ZMod p, F (p ^ e) n (ζ : ZMod p).val * F (p ^ e) n y.val :=
          Finset.sum_congr rfl fun y _ => hmul y
  have hval : (ζ : ZMod p).val ≠ 0 := fun h => Units.ne_zero ζ ((ZMod.val_eq_zero _).mp h)
  have hpos : 1 ≤ (ζ : ZMod p).val ^ n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hval)
  have hunit : IsUnit (F (p ^ e) n (ζ : ZMod p).val - 1) := by
    have heq : F (p ^ e) n (ζ : ZMod p).val - 1 =
        (((ζ : ZMod p).val ^ n - 1 : ℕ) : ZMod (p ^ e)) := by
      rw [F, Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one]
    rw [heq, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
    intro hdvd
    apply hζn
    have h1 : (((ζ : ZMod p).val ^ n - 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub hpos, Nat.cast_pow, Nat.cast_one, ZMod.natCast_zmod_val, sub_eq_zero] at h1
    exact h1
  have h2 : (F (p ^ e) n (ζ : ZMod p).val - 1) * ∑ y : ZMod p, F (p ^ e) n y.val = 0 := by
    rw [sub_mul, one_mul, ← hsum, sub_self]
  exact hunit.mul_right_eq_zero.mp h2

/-- Validity modulo `p ^ e` forces `p ∣ m` (compare the windows at `k = p - 1` and `k = p`). -/
theorem dvd_of_valid {n p e m : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hen : e ≤ n)
    (hV : ∀ k, 0 < k → ∑ i ∈ Finset.range m, F (p ^ e) n (k + 1 + i) = 0) : p ∣ m := by
  have h1 := hV (p - 1) (by have := hp.two_le; omega)
  have h2 := hV p hp.pos
  rw [Nat.sub_add_cancel hp.one_le] at h1
  have h3 := shift_sum (F (p ^ e) n) p m
  have h4 : F (p ^ e) n p = 0 := F_eq_zero hen (dvd_refl p)
  simp only [h1, h2, h4, zero_add, add_zero] at h3
  have h5 : p ^ e ∣ (p + m) ^ n := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_pow]
    exact h3
  have h6 : p ∣ (p + m) ^ n := (dvd_pow_self p (by omega : e ≠ 0)).trans h5
  exact (Nat.dvd_add_right (dvd_refl p)).mp (hp.dvd_of_dvd_pow h6)

/-- The valid window lengths modulo a prime power `p ^ e ∣ n`. -/
theorem valid_p_iff {n p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hpe : p ^ e ∣ n) (hn0 : n ≠ 0)
    (m : ℕ) :
    (∀ k, 0 < k → p ^ e ∣ ∑ i ∈ Finset.Icc 1 m, (k + i) ^ n) ↔
      p ^ (if (p - 1) ∣ n then e + 1 else 1) ∣ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hpe1 : p ^ (e - 1) ∣ n := (pow_dvd_pow p (Nat.sub_le e 1)).trans hpe
  have hen : e ≤ n := by
    have h1 : e < p ^ e := Nat.lt_pow_self hp.one_lt
    have h2 : p ^ e ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpe
    omega
  have hcop : Nat.Coprime (p ^ e) (p - 1) := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr
      (Nat.not_dvd_of_pos_of_lt (by have := hp.two_le; omega) (by have := hp.two_le; omega))
  have hconv : ∀ k, (p ^ e ∣ ∑ i ∈ Finset.Icc 1 m, (k + i) ^ n) ↔
      ∑ i ∈ Finset.range m, F (p ^ e) n (k + 1 + i) = 0 := by
    intro k
    rw [← ZMod.natCast_eq_zero_iff, cast_window]
  simp only [hconv]
  constructor
  · intro hV
    obtain ⟨t, rfl⟩ := dvd_of_valid hp he hen hV
    split_ifs with hpn
    · have h1 := hV 1 Nat.one_pos
      rw [window_mul he hpe1, S_caseA he hpe1 hpn hn0, ← Nat.cast_mul,
        ZMod.natCast_eq_zero_iff] at h1
      rw [pow_succ']
      exact mul_dvd_mul_left p ((Nat.Coprime.dvd_mul_right hcop).mp h1)
    · rw [pow_one]
      exact dvd_mul_right p t
  · intro hd k _
    split_ifs at hd with hpn
    · obtain ⟨s, rfl⟩ := hd
      rw [show p ^ (e + 1) * s = p * (p ^ e * s) by ring, window_mul he hpe1,
        S_caseA he hpe1 hpn hn0, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
      exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
    · rw [pow_one] at hd
      obtain ⟨t, rfl⟩ := hd
      rw [window_mul he hpe1, S_caseB he hpe1 hpn, mul_zero]

/-- CRT step: validity modulo `n` is validity modulo each `p ^ e ∥ n`. -/
theorem valid_iff {n : ℕ} (hn0 : n ≠ 0) (m : ℕ) :
    (∀ k, 0 < k → n ∣ ∑ i ∈ Finset.Icc 1 m, (k + i) ^ n) ↔
      ∀ p ∈ n.primeFactors, p ^ (if (p - 1) ∣ n then n.factorization p + 1 else 1) ∣ m := by
  constructor
  · intro hV p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have he : 1 ≤ n.factorization p :=
      (hpp.pow_dvd_iff_le_factorization hn0).mp
        (by rw [pow_one]; exact Nat.dvd_of_mem_primeFactors hp)
    exact (valid_p_iff hpp he (Nat.ordProj_dvd n p) hn0 m).mp
      (fun k hk => (Nat.ordProj_dvd n p).trans (hV k hk))
  · intro hD k hk
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p j hpp hpj
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    have hjle : j ≤ n.factorization p := (hpp.pow_dvd_iff_le_factorization hn0).mp hpj
    have hpn : p ∈ n.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, (dvd_pow_self p hj.ne').trans hpj, hn0⟩
    have he : 1 ≤ n.factorization p := by omega
    exact (pow_dvd_pow p hjle).trans
      ((valid_p_iff hpp he (Nat.ordProj_dvd n p) hn0 m).mpr (hD p hpn) k hk)

/-- A product of powers of distinct primes divides `m` iff each factor does. -/
theorem prod_dvd_iff {n : ℕ} (c : ℕ → ℕ) (m : ℕ) :
    (∏ p ∈ n.primeFactors, p ^ c p) ∣ m ↔ ∀ p ∈ n.primeFactors, p ^ c p ∣ m := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun p => p ^ c p) hp).trans h
  · intro h
    have key : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → (∀ p ∈ s, p ^ c p ∣ m) →
        (∏ p ∈ s, p ^ c p) ∣ m := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro _ _
        simp
      | insert a s ha ih =>
        intro hpr hdv
        rw [Finset.prod_insert ha]
        refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (hdv a (Finset.mem_insert_self a s))
          (ih (fun q hq => hpr q (Finset.mem_insert_of_mem hq))
            (fun q hq => hdv q (Finset.mem_insert_of_mem hq)))
        apply Nat.Coprime.prod_right
        intro q hq
        apply Nat.Coprime.pow
        rw [Nat.coprime_primes (hpr a (Finset.mem_insert_self a s))
          (hpr q (Finset.mem_insert_of_mem hq))]
        rintro rfl
        exact ha hq
    exact key _ (fun p hp => Nat.prime_of_mem_primeFactors hp) h

theorem D_eq (n : ℕ) :
    UniqueFactorizationMonoid.radical n * OMA.S_oeis_a354139.A193267 n =
      ∏ p ∈ n.primeFactors, p ^ (if (p - 1) ∣ n then n.factorization p + 1 else 1) := by
  rw [Nat.radical_eq_prod_primeFactors, OMA.S_oeis_a354139.A193267, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  split_ifs <;> ring

end OMA.A354139Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a354139.main := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hiff : ∀ m, (∀ k, 0 < k → n ∣ ∑ i ∈ Finset.Icc 1 m, (k + i) ^ n) ↔
      (∏ p ∈ n.primeFactors, p ^ (if (p - 1) ∣ n then n.factorization p + 1 else 1)) ∣ m :=
    fun m => (OMA.A354139Proof.valid_iff hn0 m).trans (OMA.A354139Proof.prod_dvd_iff _ m).symm
  have hDpos : 0 < ∏ p ∈ n.primeFactors,
      p ^ (if (p - 1) ∣ n then n.factorization p + 1 else 1) :=
    Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  rw [OMA.S_oeis_a354139.a, OMA.S_oeis_a354139.A007947, OMA.A354139Proof.D_eq]
  apply le_antisymm
  · exact Nat.sInf_le ⟨hDpos, (hiff _).mpr dvd_rfl⟩
  · refine le_csInf ⟨_, hDpos, (hiff _).mpr dvd_rfl⟩ ?_
    rintro m ⟨hm, hV⟩
    exact Nat.le_of_dvd hm ((hiff m).mp hV)
