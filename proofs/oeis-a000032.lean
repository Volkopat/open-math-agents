import OMAStatements.S_oeis_a000032
import Mathlib

namespace OMA.A000032Proof

open OMA.S_oeis_a000032

theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas (n + 1) + lucas n := rfl

theorem fib2 (n : ℕ) : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
  exact_mod_cast Nat.fib_add_two

theorem lucas_int : ∀ n, (lucas n : ℤ) = 2 * Nat.fib (n + 1) - Nat.fib n
  | 0 => by simp [lucas]
  | 1 => by simp [lucas, Nat.fib_two]
  | n + 2 => by
    rw [lucas_add_two]; push_cast [lucas_int n, lucas_int (n + 1), Nat.fib_add_two]; ring

theorem cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => simp [Nat.fib_two]
  | succ n ih =>
    have f0 := fib2 n
    have f1 := fib2 (n + 1)
    rw [show n + 1 + 2 = n + 3 from rfl, show n + 1 + 1 = n + 2 from rfl] at f1
    show (Nat.fib (n + 2) : ℤ) ^ 2 - Nat.fib (n + 1) * Nat.fib (n + 3) = (-1) ^ (n + 1)
    rw [f1, pow_succ]
    linear_combination (-1 : ℤ) * ih + (Nat.fib (n + 2) : ℤ) * f0

theorem dbl1 (n : ℕ) : (Nat.fib (2 * n + 1) : ℤ) = Nat.fib n ^ 2 + Nat.fib (n + 1) ^ 2 := by
  have := Nat.fib_two_mul_add_one n
  push_cast [this]
  ring

theorem dbl2 (n : ℕ) : (Nat.fib (2 * n + 2) : ℤ) =
    Nat.fib (n + 1) * Nat.fib n + Nat.fib (n + 2) * Nat.fib (n + 1) := by
  have := Nat.fib_add (n + 1) n
  rw [show n + 1 + n + 1 = 2 * n + 2 by ring] at this
  push_cast [this]
  ring

theorem dbl0 (n : ℕ) : (Nat.fib (2 * n) : ℤ) = Nat.fib n * lucas n := by
  rw [Nat.fib_two_mul, lucas_int, Nat.cast_mul, Nat.cast_sub (by linarith [@Nat.fib_le_fib_succ n])]
  push_cast; ring

theorem dbl0_nat (n : ℕ) : Nat.fib (2 * n) = Nat.fib n * lucas n := by
  exact_mod_cast dbl0 n

theorem lucas_fib_nat (n : ℕ) : lucas n + Nat.fib n = 2 * Nat.fib (n + 1) := by
  have := lucas_int n
  omega

theorem LA (n : ℕ) : (lucas (2 * n) : ℤ) = (lucas n : ℤ) ^ 2 - 2 * (-1) ^ n := by
  have hc := cassini n
  rw [fib2 n] at hc
  rw [lucas_int (2 * n), dbl1, dbl0, lucas_int n]
  linear_combination (-2 : ℤ) * hc

theorem LB (n : ℕ) : (lucas (2 * n + 1) : ℤ) = lucas n * lucas (n + 1) - (-1) ^ n := by
  have hc := cassini n
  rw [fib2 n] at hc
  rw [lucas_int (2 * n + 1), show 2 * n + 1 + 1 = 2 * n + 2 from rfl, dbl2, dbl1, lucas_int n,
    lucas_int (n + 1), show n + 1 + 1 = n + 2 from rfl, fib2 n]
  linear_combination (-1 : ℤ) * hc

theorem lucas_add_two_int (k : ℕ) : (lucas (k + 2) : ℤ) = lucas (k + 1) + lucas k := by
  rw [lucas_add_two]; push_cast; ring

theorem Q (n : ℕ) : ∀ m : ℕ, (lucas (m + 2 * n) : ℤ) = lucas n * lucas (m + n) - (-1) ^ n * lucas m := by
  have H : ∀ m : ℕ, ((lucas (m + 2 * n) : ℤ) = lucas n * lucas (m + n) - (-1) ^ n * lucas m) ∧
      ((lucas (m + 1 + 2 * n) : ℤ) = lucas n * lucas (m + 1 + n) - (-1) ^ n * lucas (m + 1)) := by
    intro m
    induction m with
    | zero =>
      constructor
      · rw [zero_add, zero_add, LA]; simp [lucas]; ring
      · simp only [zero_add]
        rw [show 1 + 2 * n = 2 * n + 1 by ring, LB, show 1 + n = n + 1 by ring]
        simp [lucas]
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have e1 := lucas_add_two_int (m + 2 * n)
      have e2 := lucas_add_two_int (m + n)
      have e3 := lucas_add_two_int m
      rw [show m + 2 * n + 2 = m + 1 + 1 + 2 * n by ring, show m + 2 * n + 1 = m + 1 + 2 * n by ring]
        at e1
      rw [show m + n + 2 = m + 1 + 1 + n by ring, show m + n + 1 = m + 1 + n by ring] at e2
      rw [e1, e2, show m + 2 = m + 1 + 1 from rfl] at *
      rw [e3]
      linear_combination ih.1 + ih.2
  exact fun m => (H m).1

theorem dick (n j : ℕ) :
    (∃ u : ℤ, (lucas (2 * j * n) : ℤ) - 2 * (-(-1) ^ n) ^ j = (lucas n : ℤ) ^ 2 * u) ∧
    (∃ v : ℤ, (lucas ((2 * j + 1) * n) : ℤ) - (2 * j + 1) * (-(-1) ^ n) ^ j * lucas n =
      (lucas n : ℤ) ^ 2 * v) := by
  induction j with
  | zero => exact ⟨⟨0, by simp [lucas]⟩, ⟨0, by simp⟩⟩
  | succ j ih =>
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := ih
    have q1 := Q n (2 * j * n)
    have q2 := Q n ((2 * j + 1) * n)
    rw [show 2 * j * n + 2 * n = 2 * (j + 1) * n by ring,
      show 2 * j * n + n = (2 * j + 1) * n by ring] at q1
    rw [show (2 * j + 1) * n + 2 * n = (2 * (j + 1) + 1) * n by ring,
      show (2 * j + 1) * n + n = 2 * (j + 1) * n by ring] at q2
    have h1 : (lucas (2 * (j + 1) * n) : ℤ) - 2 * (-(-1) ^ n) ^ (j + 1) =
        (lucas n : ℤ) ^ 2 * (lucas n * v + (2 * j + 1) * (-(-1) ^ n) ^ j - (-1) ^ n * u) := by
      rw [pow_succ]
      linear_combination q1 + (lucas n : ℤ) * hv - (-1) ^ n * hu
    refine ⟨⟨_, h1⟩, ⟨lucas n * (lucas n * v + (2 * j + 1) * (-(-1) ^ n) ^ j - (-1) ^ n * u)
      - (-1) ^ n * v, ?_⟩⟩
    push_cast
    rw [pow_succ] at h1 ⊢
    linear_combination q2 + (lucas n : ℤ) * h1 - (-1) ^ n * hv

theorem geom (q : ℕ) : ∀ t : ℕ,
    1 + (q + 1 - 1) * ∑ j ∈ Finset.Icc 1 t, (q + 1) ^ (j - 1) = (q + 1) ^ t := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ t + 1), mul_add, ← add_assoc, ih,
      Nat.add_sub_cancel, Nat.add_sub_cancel, pow_succ]
    simp only [Nat.add_sub_cancel] at ih
    ring

theorem forberg : Forberg := by
  intro p hp hp2 he m i hm
  have hpe : p ∣ lucas (lucasEntry p) := Nat.sInf_mem (Nat.nonempty_of_pos_sInf he)
  set e := lucasEntry p with he_def
  obtain ⟨J, hJ⟩ : ∃ J, p = 2 * J + 1 := ⟨p / 2, by have := hp.eq_two_or_odd; omega⟩
  have hpJ : (2 * (J : ℤ) + 1) = p := by rw [hJ]; push_cast; ring
  have key : ∀ t : ℕ, (p : ℤ) ^ (t + 1) ∣ lucas (e * p ^ t) := by
    intro t
    induction t with
    | zero => simpa using Int.natCast_dvd_natCast.mpr hpe
    | succ t ih =>
      obtain ⟨v, hv⟩ := (dick (e * p ^ t) J).2
      rw [show (2 * J + 1) * (e * p ^ t) = e * p ^ (t + 1) by rw [pow_succ, ← hJ]; ring] at hv
      have h1 : (p : ℤ) ^ (t + 1 + 1) ∣ (lucas (e * p ^ t) : ℤ) ^ 2 := by
        have : (p : ℤ) ^ ((t + 1) * 2) ∣ (lucas (e * p ^ t) : ℤ) ^ 2 := by
          rw [pow_mul]; exact pow_dvd_pow_of_dvd ih 2
        exact (pow_dvd_pow _ (by omega)).trans this
      obtain ⟨w, hw⟩ := ih
      have h2 : (p : ℤ) ^ (t + 1 + 1) ∣
          (2 * J + 1) * (-(-1) ^ (e * p ^ t)) ^ J * (lucas (e * p ^ t) : ℤ) :=
        ⟨(-(-1) ^ (e * p ^ t)) ^ J * w, by rw [hpJ, hw]; ring⟩
      have h3 := dvd_add (h1.trans ⟨v, hv⟩) h2
      simpa using h3
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hidx : e + e * (q + 1 - 1) * (∑ j ∈ Finset.Icc 1 (t + 1 - 1), (q + 1) ^ (j - 1))
      + 2 * i * e * (q + 1) ^ (t + 1 - 1) = (2 * i + 1) * (e * (q + 1) ^ t) := by
    have hg := geom q t
    simp only [Nat.add_sub_cancel] at *
    rw [← hg]; ring
  rw [hidx]
  obtain ⟨v, hv⟩ := (dick (e * (q + 1) ^ t) i).2
  have hs : (lucas (e * (q + 1) ^ t) : ℤ) ∣ lucas ((2 * i + 1) * (e * (q + 1) ^ t)) := by
    have : (lucas ((2 * i + 1) * (e * (q + 1) ^ t)) : ℤ) = lucas (e * (q + 1) ^ t) *
        (lucas (e * (q + 1) ^ t) * v + (2 * i + 1) * (-(-1) ^ (e * (q + 1) ^ t)) ^ i) := by
      linear_combination hv
    exact ⟨_, this⟩
  have := (key t).trans hs
  exact_mod_cast this

section ZM

variable (p : ℕ) [hp : Fact p.Prime]

def T : Equiv.Perm (ZMod p × ZMod p) where
  toFun x := (x.2, x.1 + x.2)
  invFun x := (x.2 - x.1, x.1)
  left_inv x := by simp
  right_inv x := by simp

theorem T_pow (n : ℕ) : (T p ^ n) (0, 1) = ((Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    simp only [T, Equiv.coe_fn_mk, Prod.mk.injEq]
    refine ⟨by trivial, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, Nat.fib_add_two]
    push_cast; ring

theorem exists_fib_dvd : ∃ n, 0 < n ∧ p ∣ Nat.fib n := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine ⟨orderOf (T p), orderOf_pos _, ?_⟩
  have h := T_pow p (orderOf (T p))
  rw [pow_orderOf_eq_one] at h
  simp only [Equiv.Perm.coe_one, id_eq, Prod.mk.injEq] at h
  exact (ZMod.natCast_eq_zero_iff _ _).mp h.1.symm

def alpha : ℕ := Nat.find (exists_fib_dvd p)

theorem alpha_pos : 0 < alpha p := (Nat.find_spec (exists_fib_dvd p)).1

theorem dvd_fib_alpha : p ∣ Nat.fib (alpha p) := (Nat.find_spec (exists_fib_dvd p)).2

theorem fib_dvd_iff (n : ℕ) : p ∣ Nat.fib n ↔ alpha p ∣ n := by
  constructor
  · intro h
    have g := Nat.fib_gcd (alpha p) n
    have h1 : p ∣ Nat.fib (Nat.gcd (alpha p) n) := by
      rw [g]; exact Nat.dvd_gcd (dvd_fib_alpha p) h
    have h2 : alpha p ≤ Nat.gcd (alpha p) n :=
      Nat.find_min' (exists_fib_dvd p) ⟨Nat.gcd_pos_of_pos_left _ (alpha_pos p), h1⟩
    rw [← le_antisymm (Nat.gcd_le_left _ (alpha_pos p)) h2]; exact Nat.gcd_dvd_right _ _
  · intro h
    exact (dvd_fib_alpha p).trans (Nat.fib_dvd _ _ h)

theorem fib_zmod_iff (n : ℕ) : (Nat.fib n : ZMod p) = 0 ↔ alpha p ∣ n := by
  rw [ZMod.natCast_eq_zero_iff, fib_dvd_iff]

theorem lucas_dvd_iff (h2 : p ≠ 2) (n : ℕ) : p ∣ lucas n ↔ alpha p ∣ 2 * n ∧ ¬ alpha p ∣ n := by
  have hpr := hp.out
  constructor
  · intro h
    refine ⟨(fib_dvd_iff p _).mp (by rw [dbl0_nat]; exact Dvd.dvd.mul_left h _), ?_⟩
    intro ha
    have hf : p ∣ Nat.fib n := (fib_dvd_iff p n).mpr ha
    have h3 : p ∣ 2 * Nat.fib (n + 1) := by rw [← lucas_fib_nat]; exact dvd_add h hf
    rcases (Nat.Prime.dvd_mul hpr).mp h3 with h4 | h4
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp h4)
    · have h5 := Nat.dvd_gcd hf h4
      rw [(Nat.fib_coprime_fib_succ n).gcd_eq_one] at h5
      exact hpr.not_dvd_one h5
  · rintro ⟨h1, h3⟩
    have h4 : p ∣ Nat.fib (2 * n) := (fib_dvd_iff p _).mpr h1
    rw [dbl0_nat] at h4
    rcases (Nat.Prime.dvd_mul hpr).mp h4 with h5 | h5
    · exact absurd ((fib_dvd_iff p n).mp h5) h3
    · exact h5

theorem exists_lucas_iff (h2 : p ≠ 2) : (∃ n, p ∣ lucas n) ↔ 2 ∣ alpha p := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨h1, h3⟩ := (lucas_dvd_iff p h2 n).mp hn
    by_contra hodd
    have hc : Nat.Coprime (alpha p) 2 :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
    apply h3
    exact hc.dvd_of_dvd_mul_left h1
  · rintro ⟨m, hm⟩
    refine ⟨m, (lucas_dvd_iff p h2 m).mpr ⟨by rw [hm], ?_⟩⟩
    intro hd
    have := alpha_pos p
    have := Nat.le_of_dvd (by omega) hd
    omega

theorem ne2_of_noLucas (h : DividesNoLucas p) : p ≠ 2 := by
  rintro rfl
  exact h.2 0 (dvd_refl _)

theorem cass_alpha :
    (Nat.fib (alpha p - 1) : ZMod p) ^ 2 = (-1) ^ alpha p := by
  have ha := alpha_pos p
  obtain ⟨t, ht⟩ : ∃ t, alpha p = t + 1 := ⟨alpha p - 1, by omega⟩
  rw [ht, Nat.add_sub_cancel]
  have hc := congrArg (Int.cast : ℤ → ZMod p) (cassini t)
  have h0 : (Nat.fib (t + 1) : ZMod p) = 0 := by rw [fib_zmod_iff, ht]
  have hf : (Nat.fib (t + 2) : ZMod p) = Nat.fib t + Nat.fib (t + 1) := by
    rw [Nat.fib_add_two]; push_cast; ring
  push_cast at hc
  rw [hf, h0] at hc
  rw [pow_succ]
  linear_combination (-1 : ZMod p) * hc

theorem shift (n : ℕ) :
    (Nat.fib (n + alpha p) : ZMod p) = (Nat.fib (alpha p - 1) : ZMod p) * Nat.fib n := by
  have ha := alpha_pos p
  obtain ⟨t, ht⟩ : ∃ t, alpha p = t + 1 := ⟨alpha p - 1, by omega⟩
  have h0 : (Nat.fib (t + 1) : ZMod p) = 0 := by rw [fib_zmod_iff, ht]
  rw [ht, Nat.add_sub_cancel, ← add_assoc, Nat.fib_add]
  push_cast
  rw [h0]; ring

theorem shift_iter (n j : ℕ) :
    (Nat.fib (n + j * alpha p) : ZMod p) = (Nat.fib (alpha p - 1) : ZMod p) ^ j * Nat.fib n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show n + (j + 1) * alpha p = (n + j * alpha p) + alpha p by ring, shift, ih]
    ring

theorem pisano_eq :
    pisano p = alpha p * orderOf (Nat.fib (alpha p - 1) : ZMod p) := by
  set c := (Nat.fib (alpha p - 1) : ZMod p) with hc
  have ha := alpha_pos p
  have h4 : c ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hc, cass_alpha, ← pow_mul, mul_comm, pow_mul]; simp
  have ho : 0 < orderOf c := orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩)
  have hmem : alpha p * orderOf c ∈ {k : ℕ | 0 < k ∧ ∀ n : ℕ, Nat.fib (n + k) ≡ Nat.fib n [MOD p]} := by
    refine ⟨Nat.mul_pos ha ho, fun n => ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff, mul_comm, shift_iter, pow_orderOf_eq_one, one_mul]
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨_, hmem⟩
  rintro k ⟨hk, hper⟩
  have e0 := hper 0
  rw [← ZMod.natCast_eq_natCast_iff, zero_add, Nat.fib_zero, Nat.cast_zero, fib_zmod_iff] at e0
  obtain ⟨j, rfl⟩ := e0
  have e1 := hper 1
  rw [← ZMod.natCast_eq_natCast_iff, mul_comm, shift_iter, Nat.fib_one, Nat.cast_one, mul_one] at e1
  have := orderOf_dvd_of_pow_eq_one e1
  exact Nat.le_of_dvd hk (Nat.mul_dvd_mul_left _ this)

theorem two_ne (h2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := fun h => h2
  ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast h)))

theorem neg_one_ne (h2 : p ≠ 2) : (-1 : ZMod p) ≠ 1 := by
  intro h
  apply two_ne p h2
  linear_combination -h

theorem qa_pow (r : ZMod p) (k : ℕ) :
    (⟨r, 0⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ k = ⟨r ^ k, 0⟩ := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ k ih =>
    rw [pow_succ, ih]
    ext <;> simp [pow_succ]

theorem w_pow (n : ℕ) : (⟨0, 1⟩ : QuadraticAlgebra (ZMod p) 1 1) ^ (n + 1) =
    ⟨(Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)⟩ := by
  induction n with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    · simp
    · simp only [QuadraticAlgebra.im_mul]
      rw [show n + 1 + 1 = n + 2 from rfl, Nat.fib_add_two]
      push_cast; ring

theorem frob (h2 : p ≠ 2) :
    2 * (Nat.fib (p - 1) : ZMod p) = 1 - 5 ^ (p / 2) ∧
      2 * (Nat.fib p : ZMod p) = 2 * 5 ^ (p / 2) := by
  have hpr := hp.out
  have hchar : CharP (QuadraticAlgebra (ZMod p) 1 1) p := by
    constructor
    intro x
    rw [QuadraticAlgebra.ext_iff, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
      QuadraticAlgebra.re_zero, QuadraticAlgebra.im_zero]
    simp [ZMod.natCast_eq_zero_iff]
  have hodd : p = 2 * (p / 2) + 1 := by have := hpr.eq_two_or_odd; omega
  set s : QuadraticAlgebra (ZMod p) 1 1 := ⟨-1, 2⟩ with hs
  have hss : s * s = ⟨5, 0⟩ := by ext <;> simp [hs] <;> norm_num
  have hsp : s ^ p = ⟨-(5 : ZMod p) ^ (p / 2), 2 * 5 ^ (p / 2)⟩ := by
    rw [show s ^ p = s ^ (2 * (p / 2) + 1) from congrArg (s ^ ·) hodd, pow_succ, pow_mul, sq, hss,
      qa_pow]
    ext <;> simp [hs] <;> ring
  have h1s : (1 + s) = (⟨2, 0⟩ : QuadraticAlgebra (ZMod p) 1 1) * ⟨0, 1⟩ := by
    ext <;> simp [hs, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hfr := add_pow_char (1 : QuadraticAlgebra (ZMod p) 1 1) s p
  have hw := w_pow p (p - 1)
  rw [Nat.sub_add_cancel hpr.one_le] at hw
  rw [h1s, mul_pow, qa_pow, ZMod.pow_card, one_pow, hsp, hw] at hfr
  have hre := congrArg QuadraticAlgebra.re hfr
  have him := congrArg QuadraticAlgebra.im hfr
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at hre him
  refine ⟨by linear_combination hre, ?_⟩
  rcases him with h | h
  · linear_combination 2 * h
  · exact absurd h (two_ne p h2)

theorem five_ne (h5 : p ≠ 5) : (5 : ZMod p) ≠ 0 := fun h => h5
  ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp ((ZMod.natCast_eq_zero_iff _ _).mp (by exact_mod_cast h)))

theorem sq5_1 : IsSquare ((1 : ℕ) : ZMod 5) := ⟨1, by decide⟩
theorem sq5_4 : IsSquare ((4 : ℕ) : ZMod 5) := ⟨2, by decide⟩
theorem nsq5_2 : ¬ IsSquare ((2 : ℕ) : ZMod 5) := by
  rintro ⟨r, hr⟩; revert r; decide
theorem nsq5_3 : ¬ IsSquare ((3 : ℕ) : ZMod 5) := by
  rintro ⟨r, hr⟩; revert r; decide

theorem chi (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ((p % 5 = 1 ∨ p % 5 = 4) → (5 : ZMod p) ^ (p / 2) = 1) ∧
    ((p % 5 = 2 ∨ p % 5 = 3) → (5 : ZMod p) ^ (p / 2) = -1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hqr := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p) (by norm_num) h2
  have heu := ZMod.euler_criterion p (five_ne p h5)
  have hor := ZMod.pow_div_two_eq_neg_one_or_one p (five_ne p h5)
  have hmod : ((p : ℕ) : ZMod 5) = ((p % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod p 5).symm
  push_cast at hqr
  constructor
  · intro h
    apply heu.mp
    apply hqr.mp
    rw [hmod]
    rcases h with h | h <;> rw [h]
    · exact sq5_1
    · exact sq5_4
  · intro h
    rcases hor with h' | h'
    · exfalso
      have := hqr.mpr (heu.mpr h')
      rw [hmod] at this
      obtain ⟨r, hr⟩ := this
      rcases h with h | h <;> rw [h] at hr
      · exact nsq5_2 ⟨r, hr⟩
      · exact nsq5_3 ⟨r, hr⟩
    · exact h'

theorem alpha_odd (h : DividesNoLucas p) : ¬ 2 ∣ alpha p := fun h2a =>
  ((exists_lucas_iff p (ne2_of_noLucas p h)).mpr h2a).elim h.2

theorem c_sq_noLucas (h : DividesNoLucas p) : (Nat.fib (alpha p - 1) : ZMod p) ^ 2 = -1 := by
  have hao := alpha_odd p h
  rw [cass_alpha]
  exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))

end ZM

theorem purathFirst : PurathFirst := by
  intro p h _
  have : Fact p.Prime := ⟨h.1⟩
  have hao := alpha_odd p h
  exact ⟨alpha p, Nat.odd_iff.mpr (by omega), dvd_fib_alpha p⟩

theorem purathSecond : PurathSecond := by
  intro p h h5
  have : Fact p.Prime := ⟨h.1⟩
  have h2 := ne2_of_noLucas p h
  have hao := alpha_odd p h
  have hc2 := c_sq_noLucas p h
  have hpo : p % 2 = 1 := h.1.eq_two_or_odd.resolve_left h2
  have h4 : p % 4 = 1 := by
    have : IsSquare (-1 : ZMod p) := ⟨_, by rw [← hc2, sq]⟩
    have := ZMod.exists_sq_eq_neg_one_iff.mp this
    omega
  have hcop2 : Nat.Coprime (alpha p) 2 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hao)
  have hcop4 : Nat.Coprime (alpha p) 4 := by
    simpa using Nat.Coprime.pow_right 2 hcop2
  have hm5 : p % 5 ≠ 0 := fun h0 =>
    h5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) h.1).mp (Nat.dvd_of_mod_eq_zero h0)).symm
  obtain ⟨hA, hB⟩ := frob p h2
  obtain ⟨cA, cB⟩ := chi p h2 h5
  have hp1 : 1 ≤ p := h.1.one_le
  by_cases hc : p % 5 = 1 ∨ p % 5 = 4
  · right
    have hx := cA hc
    rw [hx] at hA
    have hF : (Nat.fib (p - 1) : ZMod p) = 0 := by
      have : (2 : ZMod p) * Nat.fib (p - 1) = 0 := by rw [hA]; ring
      exact (mul_eq_zero.mp this).resolve_left (two_ne p h2)
    rw [fib_zmod_iff] at hF
    have hq : alpha p ∣ (p - 1) / 4 := by
      apply hcop4.dvd_of_dvd_mul_left
      rwa [show 4 * ((p - 1) / 4) = p - 1 by omega]
    refine ⟨hc, ?_, 2, le_refl _, ?_, ?_⟩
    · rw [fib_dvd_iff]; exact hq.trans ⟨2, by omega⟩
    · exact ⟨(p - 1) / 4, by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; omega⟩
    · rw [fib_dvd_iff, show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hq
  · left
    have hc' : p % 5 = 2 ∨ p % 5 = 3 := by omega
    have hx := cB hc'
    rw [hx] at hA hB
    have e1 : (Nat.fib (p - 1) : ZMod p) = 1 :=
      mul_left_cancel₀ (two_ne p h2) (by linear_combination hA)
    have e2 : (Nat.fib p : ZMod p) = -1 :=
      mul_left_cancel₀ (two_ne p h2) (by linear_combination hB)
    have hF : (Nat.fib (p + 1) : ZMod p) = 0 := by
      have := Nat.fib_add_two (n := p - 1)
      rw [show p - 1 + 2 = p + 1 by omega, show p - 1 + 1 = p by omega] at this
      rw [this]; push_cast; rw [e1, e2]; ring
    rw [fib_zmod_iff] at hF
    have hq : alpha p ∣ (p + 1) / 2 := by
      apply hcop2.dvd_of_dvd_mul_left
      rwa [show 2 * ((p + 1) / 2) = p + 1 by omega]
    refine ⟨hc', ?_, ?_⟩
    · rw [fib_dvd_iff]; exact hF
    · rw [fib_dvd_iff]; exact hq

theorem purathThird : PurathThird := by
  constructor
  · intro p h
    have : Fact p.Prime := ⟨h.1⟩
    have h2 := ne2_of_noLucas p h
    have hc2 := c_sq_noLucas p h
    have ho : orderOf (Nat.fib (alpha p - 1) : ZMod p) = 2 ^ (1 + 1) := by
      apply orderOf_eq_prime_pow
      · rw [pow_one, hc2]; exact neg_one_ne p h2
      · rw [show 2 ^ (1 + 1) = 2 * 2 from rfl, pow_mul, hc2]; norm_num
    have hao := alpha_odd p h
    rw [pisano_eq, ho]
    constructor
    · exact Dvd.intro_left _ rfl
    · omega
  · intro p hp h2 hex
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, hm⟩ := (exists_lucas_iff p h2).mp hex
    have ha := alpha_pos p
    have hm1 : 1 ≤ m := by omega
    have hc : (Nat.fib (alpha p - 1) : ZMod p) = -(-1) ^ m := by
      have hL : p ∣ lucas m := (lucas_dvd_iff p h2 m).mpr ⟨by rw [hm], fun hd => by
        have := Nat.le_of_dvd (by omega) hd; omega⟩
      have hL' : (((lucas m : ℤ)) : ZMod p) = 0 := by exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).mpr hL
      rw [lucas_int] at hL'
      push_cast at hL'
      have hcas := congrArg (Int.cast : ℤ → ZMod p) (cassini m)
      push_cast at hcas
      have f2 : (Nat.fib (m + 2) : ZMod p) = Nat.fib m + Nat.fib (m + 1) := by
        rw [Nat.fib_add_two]; push_cast; ring
      rw [f2] at hcas
      have hF2m : (Nat.fib (2 * m) : ZMod p) = 0 := by rw [fib_zmod_iff, hm]
      have e : (Nat.fib (2 * m + 1) : ZMod p) = Nat.fib (2 * m - 1) + Nat.fib (2 * m) := by
        have := Nat.fib_add_two (n := 2 * m - 1)
        rw [show 2 * m - 1 + 2 = 2 * m + 1 by omega, show 2 * m - 1 + 1 = 2 * m by omega] at this
        rw [this]; push_cast; ring
      have d : (Nat.fib (2 * m + 1) : ZMod p) = Nat.fib (m + 1) ^ 2 + Nat.fib m ^ 2 := by
        rw [Nat.fib_two_mul_add_one]; push_cast; ring
      rw [hm]
      linear_combination (-1 : ZMod p) * e - hF2m + d + (Nat.fib (m + 1) : ZMod p) * hL' - hcas
    rcases Nat.even_or_odd m with he | hodd
    · have hc1 : (Nat.fib (alpha p - 1) : ZMod p) = -1 := by rw [hc, he.neg_one_pow]
      have ho : orderOf (Nat.fib (alpha p - 1) : ZMod p) = 2 := by
        apply orderOf_eq_prime
        · rw [hc1]; norm_num
        · rw [hc1]; exact neg_one_ne p h2
      rw [pisano_eq, ho, hm]
      right
      obtain ⟨k, rfl⟩ := he
      exact ⟨k, by ring⟩
    · have hc1 : (Nat.fib (alpha p - 1) : ZMod p) = 1 := by rw [hc, hodd.neg_one_pow, neg_neg]
      rw [pisano_eq, hc1, orderOf_one, hm]
      left
      obtain ⟨k, rfl⟩ := hodd
      constructor
      · exact ⟨2 * k + 1, by ring⟩
      · omega

end OMA.A000032Proof

open OMA.A000032Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a000032.main :=
  ⟨forberg, purathFirst, purathSecond, purathThird⟩
