import OMAStatements.S_oeis_a122869
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic

namespace OMA.P_oeis_a122869

open OMA.S_oeis_a122869

/-- Quadratic extension `(ZMod p)[√5]` represented as pairs `(a, b)` with `(0, 1)^2 = (5, 0)`. -/
private structure Q5 (p : ℕ) where
  re : ZMod p
  im : ZMod p

private lemma Q5.ext {p : ℕ} {x y : Q5 p} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x; cases y; simp only [mk.injEq]; exact ⟨h1, h2⟩

private instance (p : ℕ) : Zero (Q5 p) := ⟨⟨0, 0⟩⟩
private instance (p : ℕ) : One (Q5 p) := ⟨⟨1, 0⟩⟩
private instance (p : ℕ) : Add (Q5 p) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
private instance (p : ℕ) : Neg (Q5 p) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
private instance (p : ℕ) : Sub (Q5 p) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
private instance (p : ℕ) : Mul (Q5 p) :=
  ⟨fun x y => ⟨x.re * y.re + 5 * x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
private instance (p : ℕ) : NatCast (Q5 p) := ⟨fun n => ⟨n, 0⟩⟩
private instance (p : ℕ) : IntCast (Q5 p) := ⟨fun n => ⟨n, 0⟩⟩

private instance (p : ℕ) : CommRing (Q5 p) where
  add_assoc a b c := Q5.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add a := Q5.ext (zero_add _) (zero_add _)
  add_zero a := Q5.ext (add_zero _) (add_zero _)
  add_comm a b := Q5.ext (add_comm _ _) (add_comm _ _)
  neg_add_cancel a := Q5.ext (neg_add_cancel _) (neg_add_cancel _)
  sub_eq_add_neg a b := Q5.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc a b c := Q5.ext
    (by change (a.re * b.re + 5 * a.im * b.im) * c.re + 5 * (a.re * b.im + a.im * b.re) * c.im =
          a.re * (b.re * c.re + 5 * b.im * c.im) + 5 * a.im * (b.re * c.im + b.im * c.re); ring)
    (by change (a.re * b.re + 5 * a.im * b.im) * c.im + (a.re * b.im + a.im * b.re) * c.re =
          a.re * (b.re * c.im + b.im * c.re) + a.im * (b.re * c.re + 5 * b.im * c.im); ring)
  one_mul a := Q5.ext (by change 1 * a.re + 5 * 0 * a.im = a.re; ring)
    (by change 1 * a.im + 0 * a.re = a.im; ring)
  mul_one a := Q5.ext (by change a.re * 1 + 5 * a.im * 0 = a.re; ring)
    (by change a.re * 0 + a.im * 1 = a.im; ring)
  left_distrib a b c := Q5.ext
    (by change a.re * (b.re + c.re) + 5 * a.im * (b.im + c.im) =
          (a.re * b.re + 5 * a.im * b.im) + (a.re * c.re + 5 * a.im * c.im); ring)
    (by change a.re * (b.im + c.im) + a.im * (b.re + c.re) =
          (a.re * b.im + a.im * b.re) + (a.re * c.im + a.im * c.re); ring)
  right_distrib a b c := Q5.ext
    (by change (a.re + b.re) * c.re + 5 * (a.im + b.im) * c.im =
          (a.re * c.re + 5 * a.im * c.im) + (b.re * c.re + 5 * b.im * c.im); ring)
    (by change (a.re + b.re) * c.im + (a.im + b.im) * c.re =
          (a.re * c.im + a.im * c.re) + (b.re * c.im + b.im * c.re); ring)
  zero_mul a := Q5.ext (by change 0 * a.re + 5 * 0 * a.im = 0; ring)
    (by change 0 * a.im + 0 * a.re = 0; ring)
  mul_zero a := Q5.ext (by change a.re * 0 + 5 * a.im * 0 = 0; ring)
    (by change a.re * 0 + a.im * 0 = 0; ring)
  mul_comm a b := Q5.ext
    (by change a.re * b.re + 5 * a.im * b.im = b.re * a.re + 5 * b.im * a.im; ring)
    (by change a.re * b.im + a.im * b.re = b.re * a.im + b.im * a.re; ring)
  natCast_zero := Q5.ext (by change ((0 : ℕ) : ZMod p) = 0; simp) rfl
  natCast_succ n := Q5.ext (by change ((n + 1 : ℕ) : ZMod p) = (n : ZMod p) + 1; push_cast; rfl)
    (by change (0 : ZMod p) = 0 + 0; ring)
  intCast_ofNat n := Q5.ext (by change ((n : ℤ) : ZMod p) = (n : ZMod p); simp) rfl
  intCast_negSucc n := Q5.ext (by change (Int.negSucc n : ZMod p) = -((n + 1 : ℕ) : ZMod p); push_cast; rfl)
    (by change (0 : ZMod p) = -0; ring)

private lemma Q5_charP (p : ℕ) : CharP (Q5 p) p := by
  constructor
  intro n
  constructor
  · intro h
    have hre : (n : ZMod p) = 0 := congr_arg Q5.re h
    exact (ZMod.natCast_eq_zero_iff n p).mp hre
  · intro h
    exact Q5.ext ((ZMod.natCast_eq_zero_iff n p).mpr h) rfl

private lemma Q5_embed_pow {p : ℕ} (a : ZMod p) (n : ℕ) :
    (⟨a, 0⟩ : Q5 p) ^ n = ⟨a ^ n, 0⟩ := by
  induction n with
  | zero => exact Q5.ext (by simp [pow_zero]; rfl) (by simp [pow_zero]; rfl)
  | succ n ih =>
    rw [pow_succ, pow_succ, ih]
    exact Q5.ext (by change a ^ n * a + 5 * 0 * 0 = a ^ n * a; ring)
      (by change a ^ n * 0 + 0 * a = 0; ring)

private lemma Q5_imag_pow_two_mul {p : ℕ} (b : ZMod p) (m : ℕ) :
    (⟨0, b⟩ : Q5 p) ^ (2 * m) = ⟨(5 * b ^ 2) ^ m, 0⟩ := by
  induction m with
  | zero => exact Q5.ext (by simp [pow_zero]; rfl) (by simp [pow_zero]; rfl)
  | succ m ih =>
    have hsq : (⟨0, b⟩ : Q5 p) ^ 2 = ⟨5 * b ^ 2, 0⟩ := by
      rw [sq]
      exact Q5.ext (by change 0 * 0 + 5 * b * b = 5 * b ^ 2; ring)
        (by change 0 * b + b * 0 = 0; ring)
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add, ih, hsq]
    rw [pow_succ (5 * b ^ 2) m]
    exact Q5.ext (by change (5 * b ^ 2) ^ m * (5 * b ^ 2) + 5 * 0 * 0 = (5 * b ^ 2) ^ m * (5 * b ^ 2); ring)
      (by change (5 * b ^ 2) ^ m * 0 + 0 * (5 * b ^ 2) = 0; ring)

private lemma Q5_frobenius {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (a b : ZMod p) :
    (⟨a, b⟩ : Q5 p) ^ p = ⟨a, (5 : ZMod p) ^ ((p - 1) / 2) * b⟩ := by
  have : CharP (Q5 p) p := Q5_charP p
  have hsplit : (⟨a, b⟩ : Q5 p) = ⟨a, 0⟩ + ⟨0, b⟩ :=
    Q5.ext (by change a = a + 0; ring) (by change b = 0 + b; ring)
  rw [hsplit, add_pow_char]
  rw [Q5_embed_pow, ZMod.pow_card]
  have hp_eq : p = 2 * ((p - 1) / 2) + 1 := by
    obtain ⟨m, rfl⟩ := hpodd; omega
  have him : (⟨0, b⟩ : Q5 p) ^ p = ⟨0, (5 : ZMod p) ^ ((p - 1) / 2) * b⟩ := by
    have hpow : (⟨0, b⟩ : Q5 p) ^ p = (⟨0, b⟩ : Q5 p) ^ (2 * ((p - 1) / 2) + 1) := congr_arg _ hp_eq
    rw [hpow, pow_succ, Q5_imag_pow_two_mul]
    have hbp : (b ^ 2) ^ ((p - 1) / 2) * b = b ^ p := by
      rw [← pow_mul, ← pow_succ, ← hp_eq]
    rw [mul_pow]
    refine Q5.ext (by change _ * 0 + 5 * 0 * b = 0; ring) ?_
    change (5 : ZMod p) ^ ((p - 1) / 2) * (b ^ 2) ^ ((p - 1) / 2) * b + 0 * 0 =
      (5 : ZMod p) ^ ((p - 1) / 2) * b
    rw [mul_zero, add_zero, mul_assoc, hbp, ZMod.pow_card]
  rw [him]
  exact Q5.ext (by change a + 0 = a; ring) (by change 0 + _ = _; ring)

private lemma lucas_binet {p : ℕ} [Fact p.Prime] (hpodd : Odd p) :
    let inv2 : ZMod p := (2 : ZMod p)⁻¹
    let α : Q5 p := ⟨inv2, inv2⟩
    let β : Q5 p := ⟨inv2, -inv2⟩
    ∀ n : ℕ, α ^ n + β ^ n = ⟨(lucas n : ZMod p), 0⟩ := by
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hprime := (Fact.out : p.Prime)
    have hp2 : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    obtain ⟨m, hm⟩ := hpodd
    have := hprime.two_le
    omega
  intro inv2 α β
  have h2inv : (2 : ZMod p) * inv2 = 1 := mul_inv_cancel₀ h2ne
  have hsum : α + β = 1 :=
    Q5.ext (by change inv2 + inv2 = 1; linear_combination h2inv)
      (by change inv2 + -inv2 = 0; ring)
  have hprod : α * β = -1 :=
    Q5.ext (by
      have h4 : (4 : ZMod p) * (inv2 * inv2) = 1 := by linear_combination (2 * inv2 + 1) * h2inv
      change inv2 * inv2 + 5 * inv2 * -inv2 = -1
      linear_combination -h4)
      (by change inv2 * -inv2 + inv2 * inv2 = -0; ring)
  have hrec : ∀ n : ℕ, α ^ (n + 2) + β ^ (n + 2) = (α ^ (n + 1) + β ^ (n + 1)) + (α ^ n + β ^ n) := by
    intro n
    have hα : α ^ 2 = α + 1 := by linear_combination α * hsum - hprod
    have hβ : β ^ 2 = β + 1 := by linear_combination β * hsum - hprod
    calc α ^ (n + 2) + β ^ (n + 2)
        = α ^ n * α ^ 2 + β ^ n * β ^ 2 := by rw [pow_add, pow_add]
      _ = α ^ n * (α + 1) + β ^ n * (β + 1) := by rw [hα, hβ]
      _ = (α ^ (n + 1) + β ^ (n + 1)) + (α ^ n + β ^ n) := by rw [pow_succ, pow_succ]; ring
  have hpair : ∀ n : ℕ,
      (α ^ n + β ^ n = ⟨(lucas n : ZMod p), 0⟩) ∧
      (α ^ (n + 1) + β ^ (n + 1) = ⟨(lucas (n + 1) : ZMod p), 0⟩) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · exact Q5.ext (by change (1 : ZMod p) + 1 = ((2 : ℕ) : ZMod p); push_cast; ring)
          (by change (0 : ZMod p) + 0 = 0; ring)
      · rw [pow_one, pow_one, hsum]
        exact Q5.ext (by change (1 : ZMod p) = ((1 : ℕ) : ZMod p); simp) rfl
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [hrec n, ih.2, ih.1]
      exact Q5.ext (by change (lucas (n + 1) : ZMod p) + (lucas n : ZMod p) = (lucas (n + 2) : ZMod p); simp [lucas])
        (by change (0 : ZMod p) + 0 = 0; ring)
  exact fun n => (hpair n).1

private lemma leg5_four : @legendreSym 5 ⟨by decide⟩ 4 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h4 : ((4 : ℤ) : ZMod 5) ≠ 0 := by
    intro h
    have hdvd : (5 : ℕ) ∣ 4 := (ZMod.natCast_eq_zero_iff 4 5).mp (by simpa using h)
    omega
  exact (legendreSym.eq_one_iff 5 h4).mpr ⟨2, by ring⟩

private lemma leg5_two : @legendreSym 5 ⟨by decide⟩ 2 = -1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [legendreSym.eq_neg_one_iff]
  rintro ⟨x, hx⟩
  fin_cases x <;> exact absurd hx (by decide)

private lemma leg5_three : @legendreSym 5 ⟨by decide⟩ 3 = -1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [legendreSym.eq_neg_one_iff]
  rintro ⟨x, hx⟩
  fin_cases x <;> exact absurd hx (by decide)

private lemma five_pow_half_eq_legendre {p : ℕ} [Fact p.Prime] (hp5 : p ≠ 5) (hpodd : Odd p) :
    ((5 : ZMod p) ^ ((p - 1) / 2) = 1 ↔ p % 5 = 1 ∨ p % 5 = 4) ∧
    ((5 : ZMod p) ^ ((p - 1) / 2) = -1 ↔ p % 5 = 2 ∨ p % 5 = 3) := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hp2 : p ≠ 2 := by obtain ⟨m, rfl⟩ := hpodd; omega
  have hpdiv : p / 2 = (p - 1) / 2 := by obtain ⟨m, rfl⟩ := hpodd; omega
  have hleg : (legendreSym p 5 : ZMod p) = (5 : ZMod p) ^ ((p - 1) / 2) := by
    rw [← hpdiv]; simpa using legendreSym.eq_pow p 5
  have hq5 : legendreSym p 5 = legendreSym 5 p := by
    have hmul : legendreSym 5 p * legendreSym p 5 = 1 := by
      have h := legendreSym.quadratic_reciprocity hp2 (by decide : (5 : ℕ) ≠ 2)
      simpa [hp5] using h
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hmod5 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
    have hndvd : ¬ 5 ∣ p := by
      intro hd
      have hprime := (Fact.out : p.Prime)
      rcases (Nat.dvd_prime hprime).mp hd with h1 | h5
      · omega
      · exact hp5 h5.symm
    omega
  have hval : (p % 5 = 1 ∨ p % 5 = 4 → legendreSym 5 p = 1) ∧
      (p % 5 = 2 ∨ p % 5 = 3 → legendreSym 5 p = -1) := by
    constructor
    · intro h
      rw [legendreSym.mod 5 p]
      have hcast : (p : ℤ) % ((5 : ℕ) : ℤ) = (p % 5 : ℕ) := by omega
      rw [hcast]
      rcases h with h1 | h4
      · rw [h1]; simp
      · rw [h4]; exact leg5_four
    · intro h
      rw [legendreSym.mod 5 p]
      have hcast : (p : ℤ) % ((5 : ℕ) : ℤ) = (p % 5 : ℕ) := by omega
      rw [hcast]
      rcases h with h2 | h3
      · rw [h2]; exact leg5_two
      · rw [h3]; exact leg5_three
  have h1ne : (1 : ZMod p) ≠ -1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by linear_combination h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
    have hp2' : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    have := (Fact.out : p.Prime).two_le
    omega
  constructor
  · constructor
    · intro heq
      rcases hmod5 with h | h | h | h
      · exact Or.inl h
      · exfalso
        have hl : legendreSym p 5 = -1 := by rw [hq5]; exact hval.2 (Or.inl h)
        rw [hl] at hleg; push_cast at hleg; exact h1ne (heq.symm.trans hleg.symm)
      · exfalso
        have hl : legendreSym p 5 = -1 := by rw [hq5]; exact hval.2 (Or.inr h)
        rw [hl] at hleg; push_cast at hleg; exact h1ne (heq.symm.trans hleg.symm)
      · exact Or.inr h
    · intro h
      have hl : legendreSym p 5 = 1 := by rw [hq5]; exact hval.1 h
      rw [← hleg, hl]; simp
  · constructor
    · intro heq
      rcases hmod5 with h | h | h | h
      · exfalso
        have hl : legendreSym p 5 = 1 := by rw [hq5]; exact hval.1 (Or.inl h)
        rw [hl] at hleg; push_cast at hleg; exact h1ne (hleg.trans heq)
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hl : legendreSym p 5 = 1 := by rw [hq5]; exact hval.1 (Or.inr h)
        rw [hl] at hleg; push_cast at hleg; exact h1ne (hleg.trans heq)
    · intro h
      have hl : legendreSym p 5 = -1 := by rw [hq5]; exact hval.2 h
      rw [← hleg, hl]; simp

private lemma prove_a122869 :
    ∀ p : ℕ, p.Prime → Odd p →
      (p ∣ lucas ((p - 1) / 2) ↔ p % 20 = 11 ∨ p % 20 = 19) := by
  intro p hp hpodd
  by_cases hp5 : p = 5
  · subst hp5
    constructor
    · intro h; exfalso; norm_num [lucas] at h
    · intro h; omega
  have : Fact p.Prime := ⟨hp⟩
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have hp2 : p ≤ 2 := Nat.le_of_dvd (by decide) hdvd
    obtain ⟨m, hm⟩ := hpodd
    have := hp.two_le
    omega
  let inv2 : ZMod p := (2 : ZMod p)⁻¹
  let α : Q5 p := ⟨inv2, inv2⟩
  let β : Q5 p := ⟨inv2, -inv2⟩
  have h2inv : (2 : ZMod p) * inv2 = 1 := mul_inv_cancel₀ h2ne
  have hprod : α * β = -1 :=
    Q5.ext (by
      have h4 : (4 : ZMod p) * (inv2 * inv2) = 1 := by linear_combination (2 * inv2 + 1) * h2inv
      change inv2 * inv2 + 5 * inv2 * -inv2 = -1
      linear_combination -h4)
      (by change inv2 * -inv2 + inv2 * inv2 = -0; ring)
  have hbinet := lucas_binet (p := p) hpodd ((p - 1) / 2)
  have h5leg := five_pow_half_eq_legendre hp5 hpodd
  have hp_eq : 2 * ((p - 1) / 2) = p - 1 := by obtain ⟨m, rfl⟩ := hpodd; omega
  have h1ne : (1 : ZMod p) ≠ -1 := by
    intro h
    have h2 : (2 : ZMod p) = 0 := by linear_combination h
    exact h2ne h2
  have hmod5 : (p % 5 = 1 ∨ p % 5 = 4) ∨ (p % 5 = 2 ∨ p % 5 = 3) := by
    have hndvd : ¬ 5 ∣ p := by
      intro hd
      rcases (Nat.dvd_prime hp).mp hd with h1 | h5
      · omega
      · exact hp5 h5.symm
    omega
  rcases hmod5 with hqr | hqnr
  · -- Case (5/p) = 1: p ≡ 1 or 4 (mod 5)
    have hε : (5 : ZMod p) ^ ((p - 1) / 2) = 1 := h5leg.1.mpr hqr
    have hfrob : α ^ p = α := by
      have := Q5_frobenius hpodd inv2 inv2
      rw [hε, one_mul] at this
      exact this
    have hα_pm1 : α ^ (p - 1) = 1 := by
      have h1 : α ^ p * (-β) = α * (-β) := congr_arg (· * (-β)) hfrob
      have hαp : α ^ p = α ^ (p - 1) * α := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le]
      have hmul : α * (-β) = 1 := by linear_combination -hprod
      rw [hαp, mul_assoc, hmul, mul_one] at h1
      exact h1
    have hmul_binet : α ^ ((p - 1) / 2) * ⟨(lucas ((p - 1) / 2) : ZMod p), 0⟩ =
        1 + (-1 : Q5 p) ^ ((p - 1) / 2) := by
      rw [← hbinet, mul_add, ← pow_add, ← two_mul, hp_eq, hα_pm1, ← mul_pow, hprod]
    have hdvd_iff : p ∣ lucas ((p - 1) / 2) ↔ (1 : Q5 p) + (-1 : Q5 p) ^ ((p - 1) / 2) = 0 := by
      constructor
      · intro hd
        have hz : (lucas ((p - 1) / 2) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
        rw [hz] at hmul_binet
        have hzero : (⟨0, 0⟩ : Q5 p) = 0 := rfl
        rw [hzero, mul_zero] at hmul_binet
        exact hmul_binet.symm
      · intro h0
        rw [h0] at hmul_binet
        have h1 : (-β) ^ ((p - 1) / 2) * (α ^ ((p - 1) / 2) * ⟨(lucas ((p - 1) / 2) : ZMod p), 0⟩) = 0 := by
          rw [hmul_binet, mul_zero]
        have hinv : (-β) ^ ((p - 1) / 2) * α ^ ((p - 1) / 2) = 1 := by
          rw [← mul_pow]
          have : (-β) * α = 1 := by linear_combination -hprod
          rw [this, one_pow]
        rw [← mul_assoc, hinv, one_mul] at h1
        have hre : (lucas ((p - 1) / 2) : ZMod p) = 0 := congr_arg Q5.re h1
        exact (ZMod.natCast_eq_zero_iff _ p).mp hre
    rw [hdvd_iff]
    constructor
    · intro h0
      have hodd_half : Odd ((p - 1) / 2) := by
        rcases Nat.even_or_odd ((p - 1) / 2) with hev | hod
        · exfalso
          rw [hev.neg_one_pow] at h0
          have hre : (1 : ZMod p) + 1 = 0 := congr_arg Q5.re h0
          exact h2ne (by linear_combination hre)
        · exact hod
      obtain ⟨r, hr⟩ := hodd_half
      omega
    · intro hmod20
      have hodd_half : Odd ((p - 1) / 2) := ⟨(p - 3) / 4, by omega⟩
      rw [hodd_half.neg_one_pow]
      ring
  · -- Case (5/p) = -1: p ≡ 2 or 3 (mod 5)
    have hε : (5 : ZMod p) ^ ((p - 1) / 2) = -1 := h5leg.2.mpr hqnr
    have hfrob : α ^ p = β := by
      have := Q5_frobenius hpodd inv2 inv2
      rw [hε] at this
      simpa [α, β] using this
    have hα_pp1 : α ^ (p + 1) = -1 := by
      rw [pow_succ, hfrob, mul_comm, hprod]
    constructor
    · intro hd
      exfalso
      have hz : (lucas ((p - 1) / 2) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      have hsum0 : α ^ ((p - 1) / 2) + β ^ ((p - 1) / 2) = 0 := by
        rw [hbinet, hz]; rfl
      have hpm1 : α ^ (p - 1) + (-1 : Q5 p) ^ ((p - 1) / 2) = 0 := by
        have h1 : α ^ ((p - 1) / 2) * (α ^ ((p - 1) / 2) + β ^ ((p - 1) / 2)) = 0 := by
          rw [hsum0, mul_zero]
        rw [mul_add, ← pow_add, ← two_mul, hp_eq, ← mul_pow, hprod] at h1
        exact h1
      have hmul2 : α ^ 2 * (α ^ (p - 1) + (-1 : Q5 p) ^ ((p - 1) / 2)) = 0 := by
        rw [hpm1, mul_zero]
      have hpow : α ^ 2 * α ^ (p - 1) = -1 := by
        rw [← pow_add, show 2 + (p - 1) = p + 1 by have := hp.two_le; omega, hα_pp1]
      rw [mul_add, hpow] at hmul2
      have hα2_im : (α ^ 2).im = inv2 := by
        rw [pow_two]
        change inv2 * inv2 + inv2 * inv2 = inv2
        linear_combination inv2 * h2inv
      rcases Nat.even_or_odd ((p - 1) / 2) with hev | hod
      · rw [hev.neg_one_pow, mul_one] at hmul2
        have hα2 : α ^ 2 = 1 := by linear_combination hmul2
        have him0 : (α ^ 2).im = 0 := congr_arg Q5.im hα2
        rw [hα2_im] at him0
        exact h2ne (by have := h2inv; rw [him0, mul_zero] at this; exact absurd this.symm one_ne_zero)
      · rw [hod.neg_one_pow] at hmul2
        have hα2 : α ^ 2 = -1 := by linear_combination -hmul2
        have him0 : (α ^ 2).im = 0 := by
          have h := congr_arg Q5.im hα2
          change (α ^ 2).im = -0 at h
          simpa using h
        rw [hα2_im] at him0
        exact h2ne (by have := h2inv; rw [him0, mul_zero] at this; exact absurd this.symm one_ne_zero)
    · intro hmod20
      omega

end OMA.P_oeis_a122869

theorem OMA.solution : type_of% @OMA.S_oeis_a122869.main :=
  OMA.P_oeis_a122869.prove_a122869
