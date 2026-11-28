import OMAReductions.R_arxiv_2604_17847_R1
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

-- Reduction arxiv-2604.17847.R1.H2.R1 of the exceptional square step.
-- Credit: @wispiANt

namespace OMA.R_arxiv_2604_17847_R1_H2_R1

open OMA.S_arxiv_2604_17847
open OMA.R_arxiv_2604_17847_R1 (rank_dvd_index pisano_eq_of_certificate)

-- Exclude exceptional square divisibility away from the necessary companion residue.
def H1 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 ≠ 8 →
    ¬ q ^ 2 ∣ Nat.fib (if q % 5 = 1 ∨ q % 5 = 4 then q-1 else q+1)

-- On the remaining class, the square test uses a single quarter-period factor.
def H2 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 = 8 →
    let t := pisano q/4
    q ^ 2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) → (2*q+1).Prime

def H3 : Prop :=
  ∀ q : ℕ, q.Prime → 1000 < q → 96 < pisano q →
    let h := pisano q / 2
    (¬ (q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
        q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient)) → q % 15 = 8 →
    let t := pisano q/4
    q ^ 2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) → (2*q+1).Prime →
    let c := 2*(q+1)/pisano q
    ¬ (rankOfApparition (2*q+1)).Coprime c →
    ¬ (3 ∣ c ∧ (rankOfApparition (2*q+1)).Coprime (c/3) ∧
      ∃ x : ZMod (2*q+1), x^3 + 3*x = 1) →
    (if Even t then 1 else 5) * ((if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t)/q^2)^2 ≡ 32 [MOD (2*q+1)]

-- Consecutive values form a finite reversible orbit for every positive modulus.
lemma fib_pair_iterate (q n : ℕ) :
    (fun x : ZMod q × ZMod q => (x.2, x.1 + x.2))^[n] (0, 1) =
      ((Nat.fib n : ZMod q), (Nat.fib (n + 1) : ZMod q)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [Nat.fib_add_two]

lemma period_and_returns (q : ℕ) [NeZero q] :
    0 < pisano q ∧ ∀ n : ℕ, pisano q ∣ n ↔
      (q ∣ Nat.fib n ∧ Nat.fib (n + 1) ≡ 1 [MOD q]) := by
  let T := fun x : ZMod q × ZMod q => (x.2, x.1 + x.2)
  let x : ZMod q × ZMod q := (0, 1)
  have inj : Function.Injective T := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    obtain ⟨rfl, he⟩ : b = d ∧ a + b = c + d := Prod.mk.inj h
    exact Prod.ext (add_right_cancel he) rfl
  have ret (n : ℕ) : Function.IsPeriodicPt T n x ↔
      q ∣ Nat.fib n ∧ Nat.fib (n + 1) ≡ 1 [MOD q] := by
    change T^[n] x = x ↔ _
    rw [show T^[n] x = _ from fib_pair_iterate q n]
    change (_, _) = (0, 1) ↔ _
    rw [Prod.mk.injEq, ZMod.natCast_eq_zero_iff, ← Nat.cast_one (R := ZMod q),
      ZMod.natCast_eq_natCast_iff]
  let P := Function.minimalPeriod T x
  have pos : 0 < P := Function.minimalPeriod_pos_of_mem_periodicPts (inj.mem_periodicPts x)
  have starts := (ret P).mp (Function.isPeriodicPt_minimalPeriod T x)
  have eq : pisano q = P := by
    apply pisano_eq_of_certificate pos ⟨Nat.modEq_zero_iff_dvd.mpr starts.1, starts.2⟩
    intro j hj h
    have hd := ((ret j).mpr ⟨Nat.modEq_zero_iff_dvd.mp h.1, h.2⟩).minimalPeriod_dvd
    exact (Nat.not_le_of_lt j.isLt) (Nat.le_of_dvd hj hd)
  rw [eq]
  exact ⟨pos, fun n => Function.isPeriodicPt_iff_minimalPeriod_dvd.symm.trans (ret n)⟩

-- Cassini gives the determinant of the Fibonacci recurrence after k steps.
lemma cassini_signed (q n : ℕ) :
    let a : ZMod q := Nat.fib n
    let b : ZMod q := Nat.fib (n + 1)
    b ^ 2 - a * b - a ^ 2 = (-1) ^ n := by
  dsimp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two, Nat.cast_add, pow_succ]
    linear_combination -ih

-- The odd half-index test uses the Lucas number L_k = 2 F_(k+1) - F_k.
lemma period_dvd_double_iff (m k : ℕ) [NeZero m] :
    pisano m ∣ 2 * k ↔ m ∣ (if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k) := by
  let a : ZMod m := Nat.fib k
  let b : ZMod m := Nat.fib (k+1)
  have le : Nat.fib k ≤ 2 * Nat.fib (k+1) := by have := Nat.fib_le_fib_succ (n := k); omega
  have pair : pisano m ∣ 2 * k ↔ a * (2*b-a) = 0 ∧ b^2 + a^2 = 1 := by
    rw [(period_and_returns m).2, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff,
      Nat.fib_two_mul, Nat.fib_two_mul_add_one, Nat.cast_mul, Nat.cast_sub le]
    simp [a, b]
  rw [pair]
  by_cases he : Even k
  · rw [if_pos he, ← ZMod.natCast_eq_zero_iff]
    change _ ↔ a = 0
    have det : b^2 - a*b - a^2 = 1 := by simpa only [he.neg_one_pow] using cassini_signed m k
    constructor
    · rintro ⟨hy, hx⟩
      linear_combination (b-a) * hx - a * hy - b * det
    · intro h
      exact ⟨by rw [h, zero_mul], by simpa [h] using det⟩
  · rw [if_neg he, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub le, Nat.cast_mul, Nat.cast_ofNat]
    change _ ↔ 2*b-a = 0
    have odd : Odd k := Nat.not_even_iff_odd.mp he
    have det : b^2 - a*b - a^2 = -1 := by simpa only [odd.neg_one_pow] using cassini_signed m k
    constructor
    · rintro ⟨hy,hx⟩
      linear_combination (a-b) * hx + a * hy + b * det
    · intro h
      exact ⟨by rw [h, mul_zero], by linear_combination b * h - det⟩

-- The gcd of the two return coordinates has the same closed form as the period test.
lemma double_return_gcd (k : ℕ) :
    (Nat.fib (2*k)).gcd (Nat.fib (2*k+1) - 1) =
      (if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k) := by
  by_cases hk : k = 0
  · subst k; decide
  let G := (Nat.fib (2*k)).gcd (Nat.fib (2*k+1) - 1)
  let C := if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k
  have first : 0 < Nat.fib (2*k) := Nat.fib_pos.mpr (by omega)
  have next : 1 ≤ Nat.fib (2*k+1) := Nat.fib_pos.mpr (by omega)
  have hg : 0 < G := Nat.gcd_pos_of_pos_left _ first
  have hc : 0 < C := by
    have pos := Nat.fib_pos.mpr (Nat.pos_of_ne_zero hk)
    have le := Nat.fib_le_fib_succ (n := k)
    dsimp [C]
    split <;> omega
  have equiv (m : ℕ) (hm : 0 < m) : m ∣ G ↔ m ∣ C := by
    let : NeZero m := ⟨hm.ne'⟩
    rw [show m ∣ C ↔ pisano m ∣ 2*k from (period_dvd_double_iff m k).symm,
      (period_and_returns m).2]
    change m ∣ (Nat.fib (2*k)).gcd _ ↔ _
    rw [Nat.dvd_gcd_iff, ← Nat.modEq_iff_dvd' next]
    exact and_congr_right fun _ => Nat.ModEq.comm
  exact Nat.dvd_antisymm ((equiv G hg).mp (dvd_refl _)) ((equiv C hc).mpr (dvd_refl _))

lemma even_period {m : ℕ} (hm : 2 < m) : Even (pisano m) := by
  let : NeZero m := ⟨by omega⟩
  by_contra he
  have odd := Nat.not_even_iff_odd.mp he
  have ret := ((period_and_returns m).2 _).mp (dvd_refl (pisano m))
  have zero := (ZMod.natCast_eq_zero_iff ..).mpr ret.1
  have one : (Nat.fib (pisano m + 1) : ZMod m) = 1 := by
    simpa only [Nat.cast_one] using (ZMod.natCast_eq_natCast_iff _ 1 m).mpr ret.2
  have bad : (1 : ZMod m) = -1 := by simpa [zero, one, odd.neg_one_pow] using cassini_signed m (pisano m)
  have two : ((2 : ℕ) : ZMod m) = 0 := by push_cast; linear_combination bad
  exact (Nat.not_le_of_lt hm) (Nat.le_of_dvd (by decide) ((ZMod.natCast_eq_zero_iff ..).mp two))

-- Each Fibonacci step negates the Cassini expression and preserves its square.
lemma cassini_square (q n : ℕ) :
    let a : ZMod q := Nat.fib n
    let b : ZMod q := Nat.fib (n + 1)
    (b ^ 2 - a * b - a ^ 2) ^ 2 = 1 := by
  have h := congrArg (fun x : ZMod q => x ^ 2) (cassini_signed q n)
  apply h.trans
  rw [← pow_mul, Nat.mul_comm n 2, pow_mul, neg_one_sq, one_pow]

lemma fourfold_return {q n : ℕ} [NeZero q] (hz : q ∣ Nat.fib n) :
    pisano q ∣ 2 * (2 * n) := by
  apply ((period_and_returns q).2 _).mpr
  have twice := hz.trans (Nat.fib_dvd _ _ (dvd_mul_left n 2))
  have four := twice.trans (Nat.fib_dvd _ _ (dvd_mul_left (2 * n) 2))
  refine ⟨four, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  have a := (ZMod.natCast_eq_zero_iff _ _).mpr hz
  have b := (ZMod.natCast_eq_zero_iff _ _).mpr twice
  have inv := cassini_square q n
  simpa [Nat.fib_two_mul_add_one, Nat.cast_add, Nat.cast_pow, b, a] using
    (show (((Nat.fib (n + 1) : ZMod q) ^ 2) ^ 2) = 1 by simpa [a] using inv)

lemma power_at_double (k : ℕ) {q n : ℕ} (hq : q.Prime) (hodd : 2 < q) (hz : q ∣ Nat.fib n) :
    q ^ k ∣ Nat.fib (2 * n) ↔ q ^ k ∣ Nat.fib n := by
  rw [Nat.fib_two_mul]
  have hc : q.Coprime (2 * Nat.fib (n + 1) - Nat.fib n) := by
    apply hq.coprime_iff_not_dvd.mpr
    intro h
    have le : Nat.fib n ≤ 2 * Nat.fib (n + 1) := by
      have := Nat.fib_le_fib_succ (n := n)
      omega
    have hd := Nat.dvd_add h hz
    rw [Nat.sub_add_cancel le] at hd
    rcases hq.dvd_mul.mp hd with htwo | hnext
    · exact (Nat.not_le_of_lt hodd) (Nat.le_of_dvd (by decide) htwo)
    · have hone := Nat.dvd_gcd hz hnext
      rw [Nat.fib_coprime_fib_succ n] at hone
      exact hq.not_dvd_one hone
  exact ⟨(hc.pow_left k).dvd_of_dvd_mul_right, fun h => dvd_mul_of_dvd_left h _⟩

-- The period and the first zero give the same divisibility test for every power of q.
lemma power_at_rank_iff (k : ℕ) {q : ℕ} (hq : q.Prime) (hodd : 2 < q) :
    q ^ k ∣ Nat.fib (pisano q) ↔ q ^ k ∣ Nat.fib (rankOfApparition q) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨hP, returns⟩ := period_and_returns q
  have hz := ((returns _).mp (dvd_refl (pisano q))).1
  have first : 0 < rankOfApparition q ∧ q ∣ Nat.fib (rankOfApparition q) :=
    Nat.sInf_mem (s := {j : ℕ | 0 < j ∧ q ∣ Nat.fib j}) ⟨_, hP, hz⟩
  have twice := first.2.trans (Nat.fib_dvd _ _ (dvd_mul_left _ 2))
  constructor
  · intro h
    exact (power_at_double k hq hodd first.2).mp ((power_at_double k hq hodd twice).mp
      (h.trans (Nat.fib_dvd _ _ (fourfold_return first.2))))
  · exact fun h => h.trans (Nat.fib_dvd _ _ (rank_dvd_index hP hz))

-- A return modulo b is also a return modulo every positive divisor of b.
lemma period_dvd_of_dvd {a b : ℕ} [NeZero a] [NeZero b] (h : a ∣ b) :
    pisano a ∣ pisano b := by
  have ret := ((period_and_returns b).2 _).mp (dvd_refl (pisano b))
  exact ((period_and_returns a).2 _).mpr ⟨h.trans ret.1, ret.2.of_dvd h⟩

lemma fourth_root_at_zero {m n : ℕ} (hz : m ∣ Nat.fib n) :
    Nat.fib (n + 1) ^ 4 ≡ 1 [MOD m] := by
  have zero := (ZMod.natCast_eq_zero_iff ..).mpr hz
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  simpa [zero, ← pow_mul] using cassini_square m n

-- The cofactor in u^4 - 1 reduces to 4 modulo q and is a unit at every odd prime q.
lemma lift_fourth_root {q u : ℕ} (k : ℕ) (hq : q.Prime) (hodd : 2 < q)
    (hu : 0 < u) (hone : u ≡ 1 [MOD q]) (hfour : u ^ 4 ≡ 1 [MOD q ^ k]) :
    u ≡ 1 [MOD q ^ k] := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hu.ne'
  let u := v + 1
  let c := u ^ 3 + u ^ 2 + u + 1
  have hc : c ≡ 4 [MOD q] := by
    simpa [c, u] using (((hone.pow 3).add (hone.pow 2)).add hone).add
      (Nat.ModEq.refl (n := q) 1)
  have cop : q.Coprime c := by
    apply hq.coprime_iff_not_dvd.mpr
    intro hd
    have four := (hc.dvd_iff (dvd_refl q)).mp hd
    have two := hq.dvd_of_dvd_pow (show q ∣ 2 ^ 2 from four)
    exact (Nat.not_le_of_lt hodd) (Nat.le_of_dvd (by decide) two)
  have factor : v * c + 1 = u ^ 4 := by dsimp [u, c]; ring
  have prod : v * c ≡ 0 [MOD q ^ k] := by
    apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl (n := q ^ k) 1)
    rw [factor]
    exact hfour
  have hd := (cop.pow_left k).dvd_of_dvd_mul_right (Nat.modEq_zero_iff_dvd.mp prod)
  exact (Nat.modEq_zero_iff_dvd.mpr hd).add (Nat.ModEq.refl 1)

-- The first zero supplies the first return at the old period as soon as its
-- Fibonacci value is divisible by the higher power.
lemma period_power_eq_iff_at_period {q k : ℕ} (hq : q.Prime) (hodd : 2 < q) (hk : 0 < k) :
    pisano (q ^ k) = pisano q ↔ q ^ k ∣ Nat.fib (pisano q) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have returns := (period_and_returns (q ^ k)).2
  have lower := period_dvd_of_dvd (dvd_pow_self q hk.ne')
  have old := ((period_and_returns q).2 _).mp (dvd_refl (pisano q))
  constructor
  · intro heq
    exact ((returns _).mp (heq ▸ dvd_refl (pisano q))).1
  · intro hz
    have hpos : 0 < Nat.fib (pisano q + 1) := Nat.fib_pos.mpr (by omega)
    exact Nat.dvd_antisymm ((returns _).mpr
      ⟨hz, lift_fourth_root k hq hodd hpos old.2 (fourth_root_at_zero hz)⟩) lower

lemma period_power_eq_iff {q k : ℕ} (hq : q.Prime) (hodd : 2 < q) (hk : 0 < k) :
    pisano (q ^ k) = pisano q ↔ q ^ k ∣ Nat.fib (rankOfApparition q) :=
  (period_power_eq_iff_at_period hq hodd hk).trans (power_at_rank_iff k hq hodd)

-- Over ZMod (q²), a return modulo q has an error divisible by q. Repetition
-- adds these errors, since all products of two errors vanish.
lemma period_square_dvd_mul (q : ℕ) [NeZero q] : pisano (q ^ 2) ∣ q * pisano q := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (period_and_returns q).1.ne'
  let n := k + 1
  have ret := ((period_and_returns q).2 _).mp (dvd_refl (pisano q))
  rw [hk] at ret
  obtain ⟨c, hc⟩ := ret.1
  have hu : 1 ≤ Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos _)
  obtain ⟨d, hd⟩ := (Nat.modEq_iff_dvd' hu).mp ret.2.symm
  have hu' : Nat.fib (n + 1) = 1 + q * d := by omega
  have zero : (q : ZMod (q ^ 2)) * q = 0 := by
    rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_eq_zero_iff]
  have a : (Nat.fib n : ZMod (q ^ 2)) = q * (c : ZMod (q ^ 2)) := by
    rw [← Nat.cast_mul, show Nat.fib n = q * c from hc]
  have b : (Nat.fib (n + 1) : ZMod (q ^ 2)) = 1 + q * (d : ZMod (q ^ 2)) := by
    rw [hu', Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  have prev : (Nat.fib k : ZMod (q ^ 2)) = 1 + q * ((d : ZMod (q ^ 2)) - c) := by
    change (Nat.fib (k + 2) : ZMod (q ^ 2)) = _ at b
    rw [Nat.fib_add_two, Nat.cast_add, a] at b
    linear_combination b
  have linear (t : ℕ) :
      (Nat.fib (t * n) : ZMod (q ^ 2)) = t * (q * (c : ZMod (q ^ 2))) ∧
      (Nat.fib (t * n + 1) : ZMod (q ^ 2)) = 1 + t * (q * (d : ZMod (q ^ 2))) := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul, Nat.cast_succ]
      constructor
      · change (Nat.fib (t * n + (k + 1)) : ZMod (q ^ 2)) = _
        rw [← Nat.add_assoc, Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ih.1, ih.2, a, prev]
        linear_combination (t : ZMod (q ^ 2)) * c * (2 * d - c) * zero
      · rw [Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, ih.1, ih.2, a, b]
        linear_combination (t : ZMod (q ^ 2)) * ((c : ZMod (q ^ 2)) ^ 2 + d ^ 2) * zero
  apply ((period_and_returns _).2 _).mpr
  rw [hk]
  obtain ⟨h0, h1⟩ := linear q
  constructor
  · apply (ZMod.natCast_eq_zero_iff ..).mp
    simpa [← mul_assoc, zero] using h0
  · apply (ZMod.natCast_eq_natCast_iff ..).mp
    simpa [← mul_assoc, zero] using h1

lemma period_square_dichotomy {q : ℕ} (hq : q.Prime) :
    pisano (q ^ 2) = pisano q ∨ pisano (q ^ 2) = q * pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨t, ht⟩ := period_dvd_of_dvd (dvd_pow_self q (by decide : 2 ≠ 0))
  have hd := period_square_dvd_mul q
  rw [ht, Nat.mul_comm q] at hd
  rcases (Nat.dvd_prime hq).mp (Nat.dvd_of_mul_dvd_mul_left (period_and_returns q).1 hd) with h | h
  · exact Or.inl (by simpa [h] using ht)
  · exact Or.inr (by simpa [h, Nat.mul_comm] using ht)

lemma period_square_formula {q : ℕ} (hq : q.Prime) (hodd : 2 < q) :
    pisano (q ^ 2) = if q ^ 2 ∣ Nat.fib (rankOfApparition q) then pisano q else q * pisano q := by
  have stable := period_power_eq_iff (k := 2) hq hodd (by decide)
  split_ifs with h
  · exact stable.mpr h
  · exact (period_square_dichotomy hq).resolve_left (mt stable.mp h)

-- No primality is needed: the old modulus divides its positive powers.
lemma stable_half_period_iff {m j : ℕ} (hm : 2 < m) (hj : 0 < j) :
    pisano (m ^ j) = pisano m ↔
    let k := pisano m / 2
    m ^ j ∣ (if Even k then Nat.fib k else 2 * Nat.fib (k+1) - Nat.fib k) := by
  let : NeZero m := ⟨by omega⟩
  have lower := period_dvd_of_dvd (dvd_pow_self m hj.ne')
  have half : 2 * (pisano m / 2) = pisano m := Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period hm))
  dsimp only
  rw [← period_dvd_double_iff, half]
  exact ⟨fun h => h ▸ dvd_refl _, fun h => Nat.dvd_antisymm h lower⟩

-- For a prime above 53, no half-index value through k=48 contains its square.
-- The product bound certifies that the table includes every possible prime divisor.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 3000000 in
lemma large_period_of_stability {q : ℕ} (hq : q.Prime) (hl : 53 < q)
    (stable : pisano (q ^ 2) = pisano q) : 96 < pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let k := pisano q / 2
  let value (i : ℕ) := if Even i then Nat.fib i else 2 * Nat.fib (i+1) - Nat.fib i
  have square : q ^ 2 ∣ value k := (stable_half_period_iff (by omega : 2 < q) (by decide : 0 < 2)).mp stable
  have half : 2 * k = pisano q := Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period (by omega : 2 < q)))
  have pos := (period_and_returns q).1
  by_contra! short
  have hk : 0 < k := by omega
  let factors : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
     31, 37, 41, 43, 47, 59, 61, 71, 79, 89,
     101, 107, 113, 139, 151, 181, 199, 211, 233, 281,
     307, 421, 461, 521, 541, 859, 911, 1103, 1597, 2161,
     2207, 3571, 5779, 6709, 9349, 9901, 19489, 28657, 144481, 3010349,
     54018521, 370248451, 6643838879]
  have primes : ∀ p ∈ factors, Nat.Prime p := by norm_num [factors, List.forall_mem_cons]
  have bound : ∀ i : Fin 49, 0 < i.val → value i.val ∣ factors.prod ^ 8 := by decide
  have j : k < 49 := by omega
  have member := OMA.R_arxiv_2604_17847_R1.prime_mem_of_dvd_product hq factors primes
    (hq.dvd_of_dvd_pow (((dvd_pow_self q (by decide : 2 ≠ 0)).trans square).trans (bound ⟨k,j⟩ hk)))
  have test : ∀ p ∈ factors, 53 < p → ∀ i : Fin 49, 0 < i.val → ¬ p ^ 2 ∣ value i.val := by decide
  exact test q member hl ⟨k,j⟩ hk square

lemma period_square_through_96 {q : ℕ} (hq : q.Prime) (hl : 53 < q) (hs : pisano q ≤ 96) :
    pisano (q ^ 2) = q * pisano q :=
  (period_square_dichotomy hq).resolve_left (fun h => (Nat.not_lt_of_ge hs) (large_period_of_stability hq hl h))

-- This form of Binet's identity avoids division by the difference of the two roots.
lemma fib_root_difference {K : Type*} [Field K] {a b : K}
    (ha : a ^ 2 = a + 1) (hb : b ^ 2 = b + 1) (n : ℕ) :
    (Nat.fib n : K) * (a - b) = a ^ n - b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    rw [Nat.fib_add_two, Nat.cast_add, add_mul, h0, h1, pow_add a n 2, pow_add b n 2, ha, hb, pow_succ, pow_succ]
    ring

lemma five_symbol_eq_one {q : ℕ} [Fact q.Prime] (large : 5 < q) :
    legendreSym q 5 = 1 ↔ q % 5 = 1 ∨ q % 5 = 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hq : q.Prime := Fact.out
  have nonzero : q % 5 ≠ 0 := fun h => (by omega : 5 ≠ q)
    ((Nat.dvd_prime_two_le hq (by decide : 2 ≤ 5)).mp (Nat.dvd_of_mod_eq_zero h))
  have hs := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := q) (by decide) (by omega)
  have nz : (5 : ZMod q) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime (ZMod q) (by decide : Nat.Prime 5) (show q ≠ 5 by omega)
  rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) by decide, legendreSym.eq_one_iff' q (by simpa using nz : ((5 : ℕ) : ZMod q) ≠ 0)]
  rw [← hs, ← ZMod.natCast_mod q 5]
  have table : ∀ j : Fin 5, (∃ r : ZMod 5, (j.val : ZMod 5) = r*r) ↔
      j.val = 0 ∨ j.val = 1 ∨ j.val = 4 := by decide
  exact (table ⟨q%5, Nat.mod_lt _ (by decide)⟩).trans (by simp [nonzero])

lemma selected_neighbor_pair {p : ℕ} (hp : p.Prime) (large : 5 < p) :
    if p % 5 = 1 ∨ p % 5 = 4 then
      p ∣ Nat.fib (p-1) ∧ (Nat.fib p : ZMod p) = 1 else
      p ∣ Nat.fib (p+1) ∧ (Nat.fib (p+2) : ZMod p) = -1 := by
  have h2 : p ≠ 2 := by omega
  have h5 : p ≠ 5 := by omega
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  have two : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two h2
  have five : (5 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (by decide : Nat.Prime 5) h5
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (5 : K) (by decide : 0 < 2)
  let a := (1 + s) / 2
  let b := 1 - a
  have twice : a * 2 = 1 + s := div_mul_cancel₀ _ two
  have ha : a ^ 2 = a + 1 := by
    have h : (2 : K)^2 * (a ^ 2 - (a + 1)) = 0 := by
      linear_combination (2 * a - 1 + s) * twice + hs
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (pow_ne_zero _ two))
  have hb : b ^ 2 = b + 1 := by dsimp [b]; linear_combination ha
  have diff : a - b ≠ 0 := by
    intro h
    have ab : a - b = s := by dsimp only [b]; linear_combination twice
    rw [ab] at h
    exact five (by simpa [h] using hs.symm)
  have zero_of_equal (n : ℕ) (h : a ^ n = b ^ n) : p ∣ Nat.fib n := by
    apply (CharP.cast_eq_zero_iff K p _).mp
    apply (mul_eq_zero.mp ?_).resolve_right diff
    rw [fib_root_difference ha hb, h, sub_self]
  have euler : (legendreSym p 5 : K) = (5 : K) ^ (p / 2) := by
    have h := congrArg (algebraMap (ZMod p) K) (legendreSym.eq_pow p 5)
    push_cast at h
    simpa [map_ofNat] using h
  have odd := hp.eq_two_or_odd.resolve_left (by omega)
  have power : s ^ p = (legendreSym p 5 : K) * s := by
    calc s ^ p = s ^ (2 * (p / 2) + 1) := by congr 1; omega
         _ = _ := by rw [pow_succ, pow_mul, hs, euler]
  have ab : a-b = s := by dsimp only [b]; linear_combination twice
  have conjugate : b ^ p = 1 - a ^ p := by simp [b, sub_pow_char]
  have difference : a ^ p - b ^ p = (legendreSym p 5 : K) * s := by
    rw [← sub_pow_char, ab, power]
  rw [conjugate] at difference
  split
  · rename_i split
    rw [(five_symbol_eq_one large).mpr split, Int.cast_one, one_mul, ← ab] at difference
    have fix : a ^ p = a := by
      apply mul_left_cancel₀ two
      dsimp only [b] at difference
      linear_combination difference
    have fixb : b ^ p = b := by rw [conjugate, fix]
    have unit (x : K) (hx : x ^ 2 = x + 1) (hf : x ^ p = x) : x ^ (p - 1) = 1 := by
      have hn : x ≠ 0 := by rintro rfl; simp at hx
      apply mul_right_cancel₀ hn
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hf]
    refine ⟨zero_of_equal _ ((unit a ha fix).trans (unit b hb fixb).symm), ?_⟩
    have coord : (Nat.fib p : K) = 1 := by
      apply mul_right_cancel₀ diff
      rw [fib_root_difference ha hb, fix, fixb, one_mul]
    apply (algebraMap (ZMod p) K).injective
    simpa using coord
  · rename_i nonsplit
    have nz : ((5 : ℤ) : ZMod p) ≠ 0 := by
      simpa using (CharP.cast_ne_zero_of_ne_of_prime (ZMod p) (by decide : Nat.Prime 5) h5)
    have neg := (legendreSym.eq_neg_one_iff_not_one p nz).mpr
      (fun h => nonsplit ((five_symbol_eq_one large).mp h))
    rw [neg, Int.cast_neg, Int.cast_one, neg_one_mul, ← ab] at difference
    have swap : a ^ p = b := by
      apply mul_left_cancel₀ two
      dsimp only [b] at difference ⊢
      linear_combination difference
    have swapb : b ^ p = a := by rw [conjugate, swap]; dsimp [b]; ring
    have prod : a*b = -1 := by dsimp only [b]; linear_combination -ha
    have powers : a ^ (p+1) = -1 ∧ b ^ (p+1) = -1 := by
      rw [pow_succ, pow_succ, swap, swapb, mul_comm b a]
      exact ⟨prod, prod⟩
    refine ⟨zero_of_equal _ (powers.1.trans powers.2.symm), ?_⟩
    have coord : (Nat.fib (p+2) : K) = -1 := by
      apply mul_right_cancel₀ diff
      rw [fib_root_difference ha hb, pow_succ a (p+1), pow_succ b (p+1), powers.1, powers.2]
      ring
    apply (algebraMap (ZMod p) K).injective
    simpa using coord

lemma zero_at_selected_neighbor {p : ℕ} (hp : p.Prime) (large : 5 < p) :
    if p % 5 = 1 ∨ p % 5 = 4 then p ∣ Nat.fib (p-1) else p ∣ Nat.fib (p+1) := by
  have h := selected_neighbor_pair hp large
  split <;> rename_i branch
  · rw [if_pos branch] at h
    exact h.1
  · rw [if_neg branch] at h
    exact h.1

-- The case p=3 is the small prime below the reciprocity test's range.
lemma zero_at_neighbor {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    p ∣ Nat.fib (p - 1) ∨ p ∣ Nat.fib (p + 1) := by
  by_cases large : 5 < p
  · have selected := zero_at_selected_neighbor hp large
    split at selected
    · exact Or.inl selected
    · exact Or.inr selected
  · have odd := hp.eq_two_or_odd.resolve_left h2
    have := hp.two_le
    have : p = 3 := by omega
    subst p
    decide

-- Both neighbors cannot be zeros: the gcd of the two indices divides their difference, two.
lemma neighbors_not_both {q : ℕ} (hq : q.Prime) :
    ¬ (q ∣ Nat.fib (q-1) ∧ q ∣ Nat.fib (q+1)) := by
  rintro ⟨hlo,hhi⟩
  let g := (q-1).gcd (q+1)
  have hd : g ∣ 2 := by
    have h := Nat.dvd_sub (Nat.gcd_dvd_right (q-1) (q+1)) (Nat.gcd_dvd_left (q-1) (q+1))
    have eq : q+1-(q-1) = 2 := by have := hq.two_le; omega
    rwa [eq] at h
  have hf : q ∣ Nat.fib g := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd hlo hhi
  exact hq.not_dvd_one (by simpa using hf.trans (Nat.fib_dvd _ _ hd))

-- At any positive zero index prime to q, the square test detects period stability.
lemma stable_iff_at_coprime_zero {q n : ℕ} (hq : q.Prime) (ho : 2 < q) (hn : 0 < n)
    (hz : q ∣ Nat.fib n) (hc : ¬ q ∣ n) :
    pisano (q^2) = pisano q ↔ q^2 ∣ Nat.fib n := by
  constructor
  · intro stable
    exact ((period_power_eq_iff hq ho (by decide : 0 < 2)).mp stable).trans
      (Nat.fib_dvd _ _ (rank_dvd_index hn hz))
  · intro hs
    let : NeZero q := ⟨hq.ne_zero⟩
    rcases period_square_dichotomy hq with eq | growth
    · exact eq
    · have ret := fourfold_return hs
      rw [growth] at ret
      have hd := (dvd_mul_right q (pisano q)).trans ret
      have two : ¬ q ∣ 2 := fun h => (Nat.not_le_of_lt ho) (Nat.le_of_dvd (by decide) h)
      exact (hc ((hq.dvd_mul.mp ((hq.dvd_mul.mp hd).resolve_left two)).resolve_left two)).elim

lemma stable_neighbor_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) :
    pisano (q^2) = pisano q ↔ q^2 ∣ Nat.fib (q-1) ∨ q^2 ∣ Nat.fib (q+1) := by
  have left : ¬ q ∣ q-1 := by
    intro h
    have := Nat.le_of_dvd (show 0 < q-1 by omega) h
    omega
  have right : ¬ q ∣ q+1 := fun h => hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl q)).mpr h)
  have lo := stable_iff_at_coprime_zero (q := q) (n := q-1) hq (by omega) (by omega)
  have hi := stable_iff_at_coprime_zero (q := q) (n := q+1) hq (by omega) (by omega)
  have base : q ∣ q^2 := dvd_pow_self q (by decide)
  constructor
  · intro stable
    rcases zero_at_neighbor hq (by omega) (by omega) with h | h
    · exact Or.inl ((lo h left).mp stable)
    · exact Or.inr ((hi h right).mp stable)
  · rintro (h | h)
    · exact (lo (base.trans h) left).mpr h
    · exact (hi (base.trans h) right).mpr h

lemma prime_not_dvd_period {q : ℕ} (hq : q.Prime) (hl : 5 < q) : ¬ q ∣ pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  intro hd
  have transfer (n : ℕ) (hz : q ∣ Nat.fib n) : q ∣ n := by
    have h := hd.trans (fourfold_return hz)
    have two : ¬ q ∣ 2 := fun h => (Nat.not_le_of_lt (by omega : 2 < q)) (Nat.le_of_dvd (by decide) h)
    exact (hq.dvd_mul.mp ((hq.dvd_mul.mp h).resolve_left two)).resolve_left two
  rcases zero_at_neighbor hq (by omega) (by omega) with h | h
  · have := Nat.le_of_dvd (show 0 < q-1 by omega) (transfer _ h)
    omega
  · exact hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl q)).mpr (transfer _ h))

-- The p-1 branch for p=2q+1 can only share a rank dividing 2 with the period.
lemma companion_alignment_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) (hp : (2*q+1).Prime) :
    2*q+1 ∣ Nat.fib (pisano q) ↔ 2*q+1 ∣ Nat.fib ((pisano q).gcd (2*(q+1))) := by
  constructor
  · intro aligned
    have plus : 2*q+1 ∣ Nat.fib (2*(q+1)) := by
      rcases zero_at_neighbor hp (by omega) (by omega) with lo | hi
      · simp only [Nat.add_sub_cancel] at lo
        let d := (pisano q).gcd (2*q)
        have zero : 2*q+1 ∣ Nat.fib d := by rw [Nat.fib_gcd]; exact Nat.dvd_gcd aligned lo
        have cop : d.Coprime q := (hq.coprime_iff_not_dvd.mpr
          (fun h => prime_not_dvd_period hq hl (h.trans (Nat.gcd_dvd_left _ _)))).symm
        have small : d ∣ 2 := cop.dvd_of_dvd_mul_right (Nat.gcd_dvd_right _ _)
        exact (hp.not_dvd_one (by simpa using zero.trans (Nat.fib_dvd _ _ small))).elim
      · rwa [show 2*(q+1) = 2*q+1+1 by omega]
    rw [Nat.fib_gcd]
    exact Nat.dvd_gcd aligned plus
  · exact fun h => h.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_left _ _))

-- Even the companion's upper branch cannot align if q itself has a lower-neighbor zero.
lemma aligned_companion_forces_upper {q : ℕ} (hq : q.Prime) (hl : 53 < q)
    (hp : (2*q+1).Prime) (ha : 2*q+1 ∣ Nat.fib (pisano q)) : q ∣ Nat.fib (q+1) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  rcases zero_at_neighbor hq (by omega) (by omega) with lo | hi
  · let d := (pisano q).gcd (2*(q+1))
    have zero : 2*q+1 ∣ Nat.fib d := (companion_alignment_iff hq (by omega) hp).mp ha
    have below : d ∣ 2*(2*(q-1)) := (Nat.gcd_dvd_left _ _).trans (fourfold_return lo)
    have above : d ∣ 2*(2*(q+1)) :=
      (Nat.gcd_dvd_right _ _).trans (dvd_mul_left _ 2)
    have small : d ∣ 8 := by
      have diff := Nat.dvd_sub above below
      rwa [show 2*(2*(q+1))-2*(2*(q-1)) = 8 by omega] at diff
    have h := Nat.le_of_dvd (by decide : 0 < Nat.fib 8) (zero.trans (Nat.fib_dvd _ _ small))
    have : Nat.fib 8 = 21 := by decide
    omega
  · exact hi

-- A stable prime has a single square-divisibility test chosen by reciprocity.
lemma stable_selected_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) :
    pisano (q^2) = pisano q ↔ q^2 ∣ Nat.fib (if q%5 = 1 ∨ q%5 = 4 then q-1 else q+1) := by
  have selected := zero_at_selected_neighbor hq hl
  split <;> rename_i branch
  · rw [if_pos branch] at selected
    apply stable_iff_at_coprime_zero hq (by omega) (by omega) selected
    intro h
    have := Nat.le_of_dvd (show 0 < q-1 by omega) h
    omega
  · rw [if_neg branch] at selected
    exact stable_iff_at_coprime_zero hq (by omega) (by omega) selected
      (fun h => hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_refl q)).mpr h))

-- For a prime companion, an upper-neighbor zero already determines q modulo 15.
lemma upper_companion_residue {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (hp : (2*q+1).Prime) (upper : q ∣ Nat.fib (q+1)) : q % 15 = 8 := by
  have avoid (p d : ℕ) (prime : p.Prime) (hd : 2 ≤ d) (lt : d < p) : p % d ≠ 0 :=
    fun h => (Nat.ne_of_lt lt) ((Nat.dvd_prime_two_le prime hd).mp (Nat.dvd_of_mod_eq_zero h))
  have q5 := avoid q 5 hq (by decide) hl
  have p5 := avoid (2*q+1) 5 hp (by decide) (by omega)
  have q3 := avoid q 3 hq (by decide) (by omega)
  have p3 := avoid (2*q+1) 3 hp (by decide) (by omega)
  have outside : ¬ (q%5 = 1 ∨ q%5 = 4) := by
    intro h
    have lower := zero_at_selected_neighbor hq hl
    rw [if_pos h] at lower
    exact neighbors_not_both hq ⟨lower,upper⟩
  have table : ∀ j : Fin 15, j.val % 5 ≠ 0 → (2*j.val+1) % 5 ≠ 0 →
      j.val % 3 ≠ 0 → (2*j.val+1) % 3 ≠ 0 →
      ¬ (j.val % 5 = 1 ∨ j.val % 5 = 4) → j.val = 8 := by decide
  have modEq (d : ℕ) (hd : d ∣ 15) : q % 15 ≡ q [MOD d] :=
    (Nat.mod_modEq q 15).of_dvd hd
  have m5 := modEq 5 (by decide)
  have m3 := modEq 3 (by decide)
  have pair (d : ℕ) (h : q%15 ≡ q [MOD d]) : 2*(q%15)+1 ≡ 2*q+1 [MOD d] :=
    (h.mul_left 2).add_right 1
  apply table ⟨q%15, Nat.mod_lt _ (by decide)⟩
  · exact fun h => q5 (Eq.trans (Eq.symm (show (q%15)%5 = q%5 from m5)) h)
  · exact fun h => p5 (Eq.trans (Eq.symm (show (2*(q%15)+1)%5 = (2*q+1)%5 from pair 5 m5)) h)
  · exact fun h => q3 (Eq.trans (Eq.symm (show (q%15)%3 = q%3 from m3)) h)
  · exact fun h => p3 (Eq.trans (Eq.symm (show (2*(q%15)+1)%3 = (2*q+1)%3 from pair 3 m3)) h)
  · change ¬ ((q%15)%5 = 1 ∨ (q%15)%5 = 4)
    rwa [show (q%15)%5 = q%5 from m5]

lemma aligned_companion_residue {q : ℕ} (hq : q.Prime) (hl : 53 < q)
    (hp : (2*q+1).Prime) (aligned : 2*q+1 ∣ Nat.fib (pisano q)) : q % 15 = 8 :=
  upper_companion_residue hq (by omega) hp (aligned_companion_forces_upper hq hl hp aligned)

-- In the nonsplit case the return at q+1 has scalar -1, so exactly doubling
-- that index gives a return and the cofactor of the minimal period is odd.
lemma nonsplit_period_cofactor {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (ns : ¬ (q%5 = 1 ∨ q%5 = 4)) :
    pisano q ∣ 2*(q+1) ∧ ¬ pisano q ∣ q+1 ∧ Odd (2*(q+1) / pisano q) := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have pair := selected_neighbor_pair hq hl
  rw [if_neg ns] at pair
  have odd := hq.eq_two_or_odd.resolve_left (by omega)
  have even : Even (q+1) := even_iff_two_dvd.mpr (by omega)
  have full : pisano q ∣ 2*(q+1) := (period_dvd_double_iff q (q+1)).mpr (by simpa [even] using pair.1)
  have half : ¬ pisano q ∣ q+1 := by
    intro h
    have ret := ((period_and_returns q).2 _ |>.mp h).2
    have one : (Nat.fib (q+2) : ZMod q) = 1 := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ q).mpr ret
    have two : (2 : ZMod q) = 0 := by linear_combination pair.2 - one
    exact (CharP.cast_ne_zero_of_ne_of_prime (ZMod q) Nat.prime_two (show q ≠ 2 by omega)) two
  refine ⟨full, half, Nat.not_even_iff_odd.mp ?_⟩
  rintro ⟨t, ht⟩
  apply half
  refine ⟨t, ?_⟩
  have prod := Nat.div_mul_cancel full
  rw [ht, add_mul] at prod
  rw [Nat.mul_comm (pisano q) t]
  omega

-- Comparing valuations is necessary only at primes of the missing cofactor.
lemma dvd_iff_at_cofactor_primes {r a c : ℕ} (hr : r ≠ 0) (ha : a ≠ 0)
    (hc : c ≠ 0) (odd : Odd c) (fits : r ∣ a*c) :
    r ∣ a ↔ ∀ l : ℕ, l.Prime → 2 < l → l ∣ c →
      r.factorization l ≤ a.factorization l := by
  constructor
  · intro h l _ _ _
    exact (Nat.factorization_le_iff_dvd hr ha).mpr h l
  · intro localTests
    apply (Nat.factorization_le_iff_dvd hr ha).mp
    intro l
    by_cases prime : l.Prime
    · by_cases divides : l ∣ c
      · have big : 2 < l := by
          have := prime.two_le
          have noTwo : ¬ 2 ∣ c := fun h => (Nat.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr h)
          by_contra! small
          exact noTwo (by rwa [show l = 2 by omega] at divides)
        exact localTests l prime big divides
      · have h := (Nat.factorization_le_iff_dvd hr (mul_ne_zero ha hc)).mpr fits l
        simpa [Nat.factorization_mul ha hc, Nat.factorization_eq_zero_of_not_dvd divides] using h
    · simp [Nat.factorization_eq_zero_of_not_prime _ prime]

lemma companion_odd_tests_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15 = 8) (hp : (2*q+1).Prime) :
    2*q+1 ∣ Nat.fib (pisano q) ↔ ∀ l : ℕ, l.Prime → 2 < l →
      l ∣ (2*(q+1) / pisano q) →
      (rankOfApparition (2*q+1)).factorization l ≤ (pisano q).factorization l := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let c := 2*(q+1) / pisano q
  obtain ⟨full, _, odd⟩ := nonsplit_period_cofactor hq hl (by omega)
  have whole : pisano q * c = 2*(q+1) := Nat.mul_div_cancel' full
  have nz : c ≠ 0 := by intro h; rw [h, mul_zero] at whole; omega
  have neighbor := zero_at_selected_neighbor hp (by omega)
  rw [if_neg (by omega)] at neighbor
  have zero : 2*q+1 ∣ Nat.fib (2*(q+1)) := by convert neighbor using 2; omega
  have first : 0 < rankOfApparition (2*q+1) ∧ 2*q+1 ∣ Nat.fib (rankOfApparition (2*q+1)) :=
    Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ 2*q+1 ∣ Nat.fib k}) ⟨2*(q+1), by omega, zero⟩
  have pos := (period_and_returns q).1
  have rankFits := rank_dvd_index (show 0 < 2*(q+1) by omega) zero
  rw [← whole] at rankFits
  rw [← dvd_iff_at_cofactor_primes first.1.ne' pos.ne' nz odd rankFits]
  exact ⟨rank_dvd_index pos, fun h => first.2.trans (Nat.fib_dvd _ _ h)⟩


-- If the cofactor and the companion rank are coprime, alignment is automatic.
lemma alignment_of_coprime_cofactor {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15 = 8) (hp : (2*q+1).Prime)
    (cop : (rankOfApparition (2*q+1)).Coprime (2*(q+1) / pisano q)) :
    2*q+1 ∣ Nat.fib (pisano q) := by
  apply (companion_odd_tests_iff hq hl residue hp).mpr
  intro l prime _ divides
  have unit : ¬ l ∣ rankOfApparition (2*q+1) := by
    intro hr
    exact prime.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd hr divides)
  simp [Nat.factorization_eq_zero_of_not_dvd unit]

-- The rank must divide a short index determined by the two Frobenius actions.
lemma witness_short_index {q k : ℕ} (hq : q.Prime) (hl : 5 < q)
    (hk : 2 ≤ k) (even : Even k) (hp : (k*q+1).Prime)
    (aligned : rankOfApparition (k*q+1) ∣ pisano q) :
    rankOfApparition (k*q+1) ∣
      (if (k*q+1)%5 = 1 ∨ (k*q+1)%5 = 4 then k
       else if q%5 = 1 ∨ q%5 = 4 then k+2 else k-2) := by
  let r := rankOfApparition (k*q+1)
  have lp : 5 < k*q+1 := by nlinarith
  have zero := zero_at_selected_neighbor hp lp
  split <;> rename_i ps
  · rw [if_pos ps, Nat.add_sub_cancel] at zero
    have rd := rank_dvd_index (show 0 < k*q by positivity) zero
    have cop : r.Coprime q := (hq.coprime_iff_not_dvd.mpr
      (fun h => prime_not_dvd_period hq hl (h.trans aligned))).symm
    exact cop.dvd_of_dvd_mul_right rd
  · rw [if_neg ps] at zero
    have rd : r ∣ k*q+2 := rank_dvd_index (by omega) zero
    split <;> rename_i qs
    · have pair := selected_neighbor_pair hq hl
      rw [if_pos qs] at pair
      let : NeZero q := ⟨hq.ne_zero⟩
      have ret : pisano q ∣ q-1 := ((period_and_returns q).2 _).mpr
        ⟨pair.1, (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa [Nat.sub_add_cancel hq.one_lt.le] using pair.2)⟩
      have lower := (aligned.trans ret).trans (dvd_mul_left (q-1) k)
      have sub := Nat.dvd_sub rd lower
      rwa [Nat.mul_sub, Nat.mul_one, show k*q+2-(k*q-k) = k+2 by
        have : k ≤ k*q := Nat.le_mul_of_pos_right _ hq.pos
        omega] at sub
    · have twice := aligned.trans (nonsplit_period_cofactor hq hl qs).1
      have mult : 2*(q+1) ∣ k*(q+1) := mul_dvd_mul_right (even_iff_two_dvd.mp even) _
      have sub := Nat.dvd_sub (twice.trans mult) rd
      rwa [Nat.mul_add, Nat.mul_one, show k*q+k-(k*q+2) = k-2 by omega] at sub

lemma witness_multiplier {q p : ℕ} (hq : q.Prime) (hl : 5 < q) (hp : p.Prime)
    (cong : p ≡ 1 [MOD q]) : ∃ k : ℕ, 2 ≤ k ∧ Even k ∧ p = k*q+1 := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hp.one_lt.le).mp cong.symm
  have eq : p = k*q+1 := by rw [Nat.mul_comm] at hk; have := hp.two_le; omega
  have pos : k ≠ 0 := by rintro rfl; simp at eq; exact hp.ne_one eq
  have big : 2 < p := by have := Nat.le_mul_of_pos_left q (Nat.pos_of_ne_zero pos); omega
  have po := hp.eq_two_or_odd.resolve_left (by omega)
  have qo := hq.eq_two_or_odd.resolve_left (by omega)
  have even : Even k := by
    apply even_iff_two_dvd.mpr
    have hd : 2 ∣ k*q := by omega
    exact (Nat.prime_two.dvd_mul.mp hd).resolve_right (by omega)
  obtain ⟨j,hj⟩ := even
  exact ⟨k, by omega, ⟨j,hj⟩, eq⟩

-- Every prime has a positive zero index, so testing the rank is reversible.
lemma rank_test_at_period {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    rankOfApparition p ∣ pisano q ↔ p ∣ Nat.fib (pisano q) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have r : 0 < rankOfApparition p ∧ p ∣ Nat.fib (rankOfApparition p) :=
    Nat.sInf_mem (s := {k : ℕ | 0 < k ∧ p ∣ Nat.fib k})
      ⟨pisano p, (period_and_returns p).1, (((period_and_returns p).2 _).mp (dvd_refl _)).1⟩
  exact ⟨fun h => r.2.trans (Nat.fib_dvd _ _ h), rank_dvd_index (period_and_returns q).1⟩

lemma witness_gcd_test {q k : ℕ} (hq : q.Prime) (hl : 5 < q)
    (hk : 2 ≤ k) (he : Even k) (hp : (k*q+1).Prime) :
    rankOfApparition (k*q+1) ∣ pisano q ↔
      k*q+1 ∣ Nat.fib ((pisano q).gcd
        (if (k*q+1)%5 = 1 ∨ (k*q+1)%5 = 4 then k
         else if q%5 = 1 ∨ q%5 = 4 then k+2 else k-2)) := by
  constructor
  · intro aligned
    have short := witness_short_index hq hl hk he hp aligned
    have r := Nat.dvd_gcd aligned short
    let : NeZero (k*q+1) := ⟨hp.ne_zero⟩
    have first : 0 < rankOfApparition (k*q+1) ∧ k*q+1 ∣ Nat.fib (rankOfApparition (k*q+1)) :=
      Nat.sInf_mem (s := {j : ℕ | 0 < j ∧ k*q+1 ∣ Nat.fib j})
        ⟨pisano (k*q+1), (period_and_returns _).1, (((period_and_returns _).2 _).mp (dvd_refl _)).1⟩
    exact first.2.trans (Nat.fib_dvd _ _ r)
  · intro h
    exact (rank_test_at_period hp hq).mpr (h.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_left _ _)))

-- Finite certificate for the large-prime range of the parent reduction.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 24000 in
lemma unique_witness_through_100 {q k : ℕ} (hq : q.Prime) (hl : 53 < q) (hk : 2 ≤ k)
    (he : Even k) (small : k ≤ 100) (hp : (k*q+1).Prime)
    (aligned : rankOfApparition (k*q+1) ∣ pisano q) : k = 2 := by
  by_contra different
  obtain ⟨t, ht⟩ := he
  have four : 4 ≤ k := by omega
  let n := if (k*q+1)%5 = 1 ∨ (k*q+1)%5 = 4 then k
           else if q%5 = 1 ∨ q%5 = 4 then k+2 else k-2
  have casesN : n = k ∨ n = k+2 ∨ n = k-2 := by
    dsimp only [n]
    split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have test := (witness_gcd_test hq (by omega) hk ⟨t,ht⟩ hp).mp aligned
  have short : k*q+1 ∣ Nat.fib n := test.trans (Nat.fib_dvd _ _ (Nat.gcd_dvd_right _ _))
  rw [Nat.fib_eq_fastFib] at short
  let factors : List ℕ :=
    [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
     97, 101, 107, 109, 113, 139, 149, 151, 181, 199, 211, 233, 263, 281, 307, 401, 421, 461, 521,
     541, 557, 769, 859, 881, 911, 919, 967, 1087, 1103, 1427, 1597, 1601, 2161, 2207, 2221, 2417,
     2521, 2789, 3001, 3041, 3167, 3469, 3571, 4481, 4969, 5779, 6709, 9349, 9901, 14503, 19489,
     19801, 28657, 59369, 63443, 90481, 103681, 109441, 135721, 141961, 144481, 275449, 514229,
     570601, 3010349, 6168709, 6376021, 29134601, 54018521, 370248451, 433494437, 599786069,
     2971215073, 6643838879]
  have primes : ∀ p ∈ factors, Nat.Prime p := by norm_num [factors, List.forall_mem_cons]
  have bound : ∀ i : Fin 103, 0 < i.val → 2 ∣ i.val → Nat.fastFib i.val ∣ factors.prod ^ 8 := by decide
  have member := OMA.R_arxiv_2604_17847_R1.prime_mem_of_dvd_product hp factors primes
    (hp.dvd_of_dvd_pow (short.trans (bound ⟨n, by omega⟩ (show 0 < n by omega) (show 2 ∣ n by omega))))
  have candidates : ∀ p ∈ factors, ∀ j : Fin 101, 4 ≤ j.val → 2 ∣ j.val → j.val ∣ p-1 →
      53 < (p-1)/j.val → (p ∣ Nat.fastFib j.val ∨ p ∣ Nat.fastFib (j.val+2) ∨ p ∣ Nat.fastFib (j.val-2)) →
      ¬ 2 ∣ (p-1)/j.val → ¬ 3 ∣ (p-1)/j.val → (p-1)/j.val ≠ 70679137 → p = 5779 ∧ (p-1)/j.val = 107 := by decide
  have hit : k*q+1 ∣ Nat.fastFib k ∨ k*q+1 ∣ Nat.fastFib (k+2) ∨ k*q+1 ∣ Nat.fastFib (k-2) := by
    rcases casesN with h | h | h
    · exact Or.inl (h ▸ short)
    · exact Or.inr (Or.inl (h ▸ short))
    · exact Or.inr (Or.inr (h ▸ short))
  have reduce : (k*q+1-1)/k = q := by simp [Nat.mul_div_cancel_left _ (by omega : 0 < k)]
  have avoid (d : ℕ) (hd : 2 ≤ d) (lt : d < q) : ¬ d ∣ q :=
    fun h => (Nat.ne_of_lt lt) ((Nat.dvd_prime_two_le hq hd).mp h)
  have composite : q ≠ 70679137 := by
    intro eq
    subst q
    exact (by decide : 139 ≠ 70679137) ((Nat.dvd_prime_two_le hq (by decide : 2 ≤ 139)).mp (by decide))
  have classify := candidates _ member ⟨k,by omega⟩ four (show 2 ∣ k by omega)
    (show k ∣ k*q+1-1 by simp)
  change 53 < (k*q+1-1)/k → _ at classify
  simp only [reduce] at classify
  obtain ⟨pval,qval⟩ := classify hl hit (avoid 2 (by decide) (by omega)) (avoid 3 (by decide) (by omega)) composite
  have hz := (rank_test_at_period hp hq).mp aligned
  rw [pval, qval] at hz
  have ret : pisano 107 ∣ 72 := ((period_and_returns 107).2 _).mpr (by decide)
  exact (by decide : ¬ 5779 ∣ Nat.fastFib 72) (by simpa [Nat.fib_eq_fastFib] using hz.trans (Nat.fib_dvd _ _ ret))

-- This also covers the small odd primes allowed in Theorem 4.2 of the paper.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
lemma bounded_witness_uniqueness {p q : ℕ} (hq : q.Prime) (odd : q ≠ 2) (unramified : q ≠ 5)
    (hp : p.Prime) (cong : p ≡ 1 [MOD q]) (aligned : rankOfApparition p ∣ pisano q)
    (bounded : p ≤ 100*q+1) : p = 2*q+1 := by
  by_cases large : 53 < q
  · obtain ⟨k,hk,he,rfl⟩ := witness_multiplier hq (by omega) hp cong
    have bound : k ≤ 100 := by
      by_contra! above
      have := Nat.mul_lt_mul_of_pos_right above hq.pos
      omega
    rw [unique_witness_through_100 hq large hk he bound hp aligned]
  · let T := fun m : ℕ => if m%5 = 1 ∨ m%5 = 4 then m-1 else 2*(m+1)
    have ret : ∀ i : Fin 54, i.val.Prime → i.val ≠ 2 → i.val ≠ 5 →
        i.val ∣ Nat.fastFib (T i.val) ∧ Nat.fastFib (T i.val+1) ≡ 1 [MOD i.val] := by decide
    have test : ∀ i : Fin 54, i.val.Prime → i.val ≠ 2 → i.val ≠ 5 →
        ∀ j : Fin 101, j.val*i.val+1 ∣ Nat.fastFib (T i.val) →
        j.val = 0 ∨ 3 ∣ j.val*i.val+1 ∨ j.val = 2 := by decide
    let : NeZero q := ⟨hq.ne_zero⟩
    have pair := ret ⟨q,by omega⟩ hq odd unramified
    have full : pisano q ∣ T q := ((period_and_returns q).2 _).mpr (by simpa [Nat.fib_eq_fastFib] using pair)
    have zero := ((rank_test_at_period hp hq).mp aligned).trans (Nat.fib_dvd _ _ full)
    obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hp.one_lt.le).mp cong.symm
    have eq : p = k*q+1 := by rw [Nat.mul_comm] at hk; have := hp.two_le; omega
    have small : k < 101 := by
      by_contra! above
      have := Nat.mul_lt_mul_of_pos_right (show 100 < k by omega) hq.pos
      omega
    have possibilities := test ⟨q,by omega⟩ hq odd unramified ⟨k,small⟩
      (by simpa only [eq, Nat.fib_eq_fastFib] using zero)
    change k = 0 ∨ 3 ∣ k*q+1 ∨ k = 2 at possibilities
    rcases possibilities with zeroK | multiple | two
    · subst k; simp at eq; exact (hp.ne_one eq).elim
    · have three := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 3)).mp (eq.symm ▸ multiple)
      have := hq.two_le
      have positive : 0 < k := by by_contra! h; simp [show k = 0 by omega] at eq; exact hp.ne_one eq
      have := Nat.le_mul_of_pos_left q positive
      omega
    · rwa [two] at eq

-- The bounded test uses Mathlib's proven binary Fibonacci evaluator.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2000000 in
lemma large_prime_of_stability {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (stable : pisano (q^2) = pisano q) : 1000 < q := by
  by_contra! small
  have test : ∀ j : Fin 1001, 5 < j.val →
      ¬ (j.val ^ 2 ∣ Nat.fastFib (j.val-1) ∨ j.val ^ 2 ∣ Nat.fastFib (j.val+1)) := by decide
  have hz := (stable_neighbor_iff hq hl).mp stable
  rw [Nat.fib_eq_fastFib] at hz
  exact test ⟨q, Nat.lt_succ_of_le small⟩ hl hz

lemma square_period_through_1000 {q : ℕ} (hq : q.Prime) (hl : 5 < q) (small : q ≤ 1000) :
    pisano (q^2) = q * pisano q :=
  (period_square_dichotomy hq).resolve_left (fun h => (Nat.not_lt_of_ge small) (large_prime_of_stability hq hl h))

-- Removing one prime power separates its entire contribution to the totient.
lemma totient_remove_prime {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (divides : p ∣ n) :
    n.totient = p^(n.factorization p - 1) * (p-1) * (ordCompl[p] n).totient := by
  have cop := (Nat.coprime_ordCompl hp hn).pow_left (n.factorization p)
  calc n.totient = ((ordProj[p] n) * (ordCompl[p] n)).totient :=
        congrArg Nat.totient (Nat.ordProj_mul_ordCompl_eq_self n p).symm
       _ = _ := by rw [Nat.totient_mul cop, Nat.totient_prime_pow hp (hp.factorization_pos_of_dvd hn divides)]

lemma totient_valuation_remove_self {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) (divides : q ∣ n) :
    n.totient.factorization q = n.factorization q - 1 + (ordCompl[q] n).totient.factorization q := by
  have predPos : 0 < q-1 := by have := hq.one_lt; omega
  have predFree : ¬ q ∣ q-1 := fun h => (Nat.not_le_of_lt (Nat.sub_lt hq.pos (by decide : 0 < 1))) (Nat.le_of_dvd predPos h)
  have unit := (Nat.totient_pos.mpr (Nat.ordCompl_pos q hn)).ne'
  rw [totient_remove_prime hq hn divides, Nat.factorization_mul (mul_ne_zero (pow_ne_zero _ hq.ne_zero) predPos.ne') unit,
    Finsupp.add_apply, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero) predPos.ne', Finsupp.add_apply,
    Nat.factorization_pow_self hq, Nat.factorization_eq_zero_of_not_dvd predFree, add_zero]

-- For coprime inputs the prime-power factor in Euler's product cannot supply q.
lemma coprime_totient_witness {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) (free : ¬ q ∣ n) :
    q ∣ n.totient ↔ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ n := by
  constructor
  · intro divides
    rw [Nat.totient_eq_prod_factorization hn, Finsupp.prod, Nat.support_factorization] at divides
    obtain ⟨p, mem, term⟩ := (hq.prime.dvd_finsetProd_iff _).mp divides
    have prime := Nat.prime_of_mem_primeFactors mem
    have divisor := Nat.dvd_of_mem_primeFactors mem
    have pred := (hq.dvd_mul.mp term).resolve_left (fun h => free ((hq.dvd_of_dvd_pow h).trans divisor))
    exact ⟨p, prime, ((Nat.modEq_iff_dvd' prime.one_lt.le).mpr pred).symm, divisor⟩
  · rintro ⟨p, prime, cong, divisor⟩
    have pred := (Nat.modEq_iff_dvd' prime.one_lt.le).mp cong.symm
    rw [← Nat.totient_prime prime] at pred
    exact pred.trans (Nat.totient_dvd_of_dvd divisor)

-- A divisor congruent to one is prime to q and survives removal of q.
lemma stripped_totient_witness {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    q ∣ (ordCompl[q] n).totient ↔ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ n := by
  rw [coprime_totient_witness hq (Nat.ordCompl_pos q hn).ne' (Nat.not_dvd_ordCompl hq hn)]
  constructor
  · rintro ⟨p,hp,hc,hd⟩
    exact ⟨p,hp,hc,hd.trans (Nat.ordCompl_dvd _ _)⟩
  · rintro ⟨p,hp,hc,hd⟩
    have nq : ¬ q ∣ p := fun d => hq.not_dvd_one ((hc.dvd_iff (dvd_refl q)).mp d)
    exact ⟨p,hp,hc,Nat.dvd_ordCompl_of_dvd_not_dvd hd nq⟩

lemma companion_removed_witness {n q : ℕ} (hq : q.Prime) (hn : n ≠ 0) :
    q ∣ (ordCompl[q] (ordCompl[2*q+1] n)).totient ↔
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ n ∧ p ≠ 2*q+1 := by
  rw [stripped_totient_witness hq (Nat.ordCompl_pos _ hn).ne']
  constructor
  · rintro ⟨p,hp,hc,hd⟩
    refine ⟨p,hp,hc,hd.trans (Nat.ordCompl_dvd _ _), ?_⟩
    rintro rfl
    exact Nat.not_dvd_ordCompl hp hn hd
  · rintro ⟨p,hp,hc,hd,other⟩
    have nc : ¬ 2*q+1 ∣ p := by
      intro divides
      exact other ((Nat.dvd_prime_two_le hp (by have := hq.two_le; omega)).mp divides).symm
    exact ⟨p,hp,hc,Nat.dvd_ordCompl_of_dvd_not_dvd hd nc⟩

-- The exponent supplied by the canonical companion is one, regardless of its multiplicity.
lemma totient_valuation_remove_companion {n q : ℕ} (hq : q.Prime) (odd : 2 < q) (hn : n ≠ 0) :
    n.totient.factorization q =
      (if (2*q+1).Prime ∧ 2*q+1 ∣ n then 1 else 0) + (ordCompl[2*q+1] n).totient.factorization q := by
  split
  · rename_i yes
    obtain ⟨hp,hd⟩ := yes
    have nq : ¬ q ∣ 2*q+1 := fun h => hq.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_left q 2)).mpr h)
    have nt : ¬ q ∣ 2 := fun h => (Nat.not_le_of_lt odd) (Nat.le_of_dvd (by decide : 0 < 2) h)
    have power := Nat.factorization_eq_zero_of_not_dvd (fun h => nq (hq.dvd_of_dvd_pow h) :
      ¬ q ∣ (2*q+1)^(n.factorization (2*q+1)-1))
    have pos := (Nat.totient_pos.mpr (Nat.ordCompl_pos (2*q+1) hn)).ne'
    rw [totient_remove_prime hp hn hd, Nat.add_sub_cancel, Nat.factorization_mul (by positivity) pos,
      Finsupp.add_apply, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
      power, zero_add, Nat.factorization_mul (by decide : 2 ≠ 0) hq.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd nt, hq.factorization_self, zero_add]
  · rename_i no
    by_cases hp : (2*q+1).Prime
    · rw [(Nat.ordCompl_eq_self_iff_zero_or_not_dvd n hp).mpr (Or.inr (fun h => no ⟨hp,h⟩)), zero_add]
    · rw [Nat.ordCompl_of_not_prime _ _ hp, zero_add]

lemma period_totient_witness_iff {q : ℕ} (hq : q.Prime) :
    (Nat.fib (pisano q)).factorization q ≤ (Nat.fib (pisano q)).totient.factorization q ↔
      ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q := by
  let : NeZero q := ⟨hq.ne_zero⟩
  have pos := (period_and_returns q).1
  have nz := (Nat.fib_pos.mpr pos).ne'
  have divides := (((period_and_returns q).2 _).mp (dvd_refl _)).1
  have e := hq.factorization_pos_of_dvd nz divides
  rw [totient_valuation_remove_self hq nz divides]
  have totpos := (Nat.totient_pos.mpr (Nat.ordCompl_pos q nz)).ne'
  have cut : (Nat.fib (pisano q)).factorization q ≤ (Nat.fib (pisano q)).factorization q - 1 +
      (ordCompl[q] (Nat.fib (pisano q))).totient.factorization q ↔
      1 ≤ (ordCompl[q] (Nat.fib (pisano q))).totient.factorization q := by omega
  rw [cut, ← Nat.Prime.dvd_iff_one_le_factorization hq totpos, stripped_totient_witness hq nz]
  exact exists_congr fun p => and_congr_right fun hp => and_congr_right fun _ => (rank_test_at_period hp hq).symm

-- One exponent comes from each copy of q after the first. An aligned prime
-- 2q+1 contributes one further exponent, even if it occurs many times.
lemma totient_valuation_two_primes {n q : ℕ} (hq : q.Prime) (hl : 2 < q)
    (hn : n ≠ 0) (divides : q ∣ n) :
    n.totient.factorization q = (n.factorization q - 1) +
      (if (2*q+1).Prime ∧ 2*q+1 ∣ n then 1 else 0) +
      (ordCompl[q] (ordCompl[2*q+1] n)).totient.factorization q := by
  have nq : ¬ 2*q+1 ∣ q := fun d => (Nat.not_le_of_lt (by omega : q < 2*q+1)) (Nat.le_of_dvd hq.pos d)
  have survives := Nat.dvd_ordCompl_of_dvd_not_dvd divides nq
  rw [totient_valuation_remove_companion hq hl hn, totient_valuation_remove_self hq (Nat.ordCompl_pos _ hn).ne' survives,
    Nat.factorization_ordCompl, Finsupp.erase_ne (by omega : q ≠ 2*q+1)]
  omega

lemma zero_residue_iff_period_totient {q : ℕ} (hq : q.Prime) :
    0 ∈ S q ↔ q ∣ (Nat.fib (pisano q)).totient := by
  let : NeZero q := ⟨hq.ne_zero⟩
  constructor
  · intro h
    exact h.2 _ (Nat.modEq_zero_iff_dvd.mpr (dvd_refl _))
  · intro h
    exact ⟨(period_and_returns q).1, fun m hm =>
      h.trans (Nat.totient_dvd_of_dvd (Nat.fib_dvd _ _ (Nat.modEq_zero_iff_dvd.mp hm)))⟩

-- The two failure cases are disjoint: square divisibility itself puts zero in S.
lemma converse_failure_iff {q : ℕ} (hq : q.Prime) :
    ((S q).Nonempty ∧ ¬ ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ rankOfApparition p ∣ pisano q) ↔
    ((S q).Nonempty ∧ 0 ∉ S q) ∨
      (2 ≤ (Nat.fib (pisano q)).factorization q ∧
       (Nat.fib (pisano q)).totient.factorization q + 1 = (Nat.fib (pisano q)).factorization q) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  let n := Nat.fib (pisano q)
  have pn : 0 < n := Nat.fib_pos.mpr (period_and_returns q).1
  have divides : q ∣ n := (((period_and_returns q).2 _).mp (dvd_refl _)).1
  have e := hq.factorization_pos_of_dvd pn.ne' divides
  have lower : n.factorization q - 1 ≤ n.totient.factorization q := by
    rw [totient_valuation_remove_self hq pn.ne' divides]
    omega
  have zero : 0 ∈ S q ↔ 1 ≤ n.totient.factorization q :=
    (zero_residue_iff_period_totient hq).trans (Nat.Prime.dvd_iff_one_le_factorization hq (Nat.totient_pos.mpr pn).ne')
  rw [← period_totient_witness_iff hq]
  change ((S q).Nonempty ∧ ¬ n.factorization q ≤ n.totient.factorization q) ↔
    ((S q).Nonempty ∧ 0 ∉ S q) ∨ (2 ≤ n.factorization q ∧ n.totient.factorization q + 1 = n.factorization q)
  constructor
  · rintro ⟨someResidue, deficit⟩
    by_cases h : 0 ∈ S q
    · have := zero.mp h
      exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inl ⟨someResidue,h⟩
  · rintro (⟨someResidue,missing⟩ | ⟨square,deficit⟩)
    · have := mt zero.mpr missing
      exact ⟨someResidue, by omega⟩
    · exact ⟨⟨0, zero.mpr (by omega)⟩, by omega⟩

-- At the level of the original reduction, H1 asks whether a good residue forces zero to be good.
lemma descent_iff_zero_residue : OMA.R_arxiv_2604_17847_R1.H1 ↔
    ∀ q : ℕ, q.Prime → 53 < q → (S q).Nonempty → 0 ∈ S q := by
  constructor
  · rintro descent q hq hl ⟨r,good⟩
    apply (zero_residue_iff_period_totient hq).mpr
    by_contra absent
    have recurring := OMA.R_arxiv_2604_17847_R1.fixed_rank_family hq good absent
    exact absent ((OMA.R_arxiv_2604_17847_R1.finite_prime_cover_iff hq (Nat.zero_lt_of_lt good.1)).mp
      (descent q r hq hl good recurring))
  · intro zero q r hq hl good _
    apply (OMA.R_arxiv_2604_17847_R1.finite_prime_cover_iff hq (Nat.zero_lt_of_lt good.1)).mpr
    exact (zero_residue_iff_period_totient hq).mp (zero q hq hl ⟨r,good⟩)

lemma exceptional_iff_totient_valuation : OMA.R_arxiv_2604_17847_R1.H2 ↔
    ∀ q : ℕ, q.Prime → 53 < q → let n := Nat.fib (pisano q)
      2 ≤ n.factorization q → n.factorization q ≤ n.totient.factorization q := by
  constructor
  · intro parent q hq hl
    let : NeZero q := ⟨hq.ne_zero⟩
    dsimp only
    intro square
    exact (period_totient_witness_iff hq).mpr (parent q hq hl
      ((hq.pow_dvd_iff_le_factorization (Nat.fib_pos.mpr (period_and_returns q).1).ne').mpr square))
  · intro growth q hq hl square
    let : NeZero q := ⟨hq.ne_zero⟩
    exact (period_totient_witness_iff hq).mp (growth q hq hl
      ((hq.pow_dvd_iff_le_factorization (Nat.fib_pos.mpr (period_and_returns q).1).ne').mp square))


lemma stripped_period_large_iff {q : ℕ} (hq : q.Prime) (hl : 53 < q) :
    q ∣ (ordCompl[q] (ordCompl[2*q+1] (Nat.fib (pisano q)))).totient ↔
    ∃ k : ℕ, 100 < k ∧ Even k ∧ (k*q+1).Prime ∧
      k*q+1 ∣ Nat.fib ((pisano q).gcd (if (k*q+1)%5 = 1 ∨ (k*q+1)%5 = 4 then k
        else if q%5 = 1 ∨ q%5 = 4 then k+2 else k-2)) := by
  let : NeZero q := ⟨hq.ne_zero⟩
  rw [companion_removed_witness hq (Nat.fib_pos.mpr (period_and_returns q).1).ne']
  constructor
  · rintro ⟨p,hp,cong,divides,other⟩
    have aligned := (rank_test_at_period hp hq).mpr divides
    obtain ⟨k,hk,he,rfl⟩ := witness_multiplier hq (by omega) hp cong
    have large : 100 < k := by
      by_contra! small
      exact other (by rw [unique_witness_through_100 hq hl hk he small hp aligned])
    exact ⟨k,large,he,hp,(witness_gcd_test hq (by omega) hk he hp).mp aligned⟩
  · rintro ⟨k,large,he,hp,test⟩
    have aligned := (witness_gcd_test hq (by omega) (by omega) he hp).mpr test
    refine ⟨k*q+1,hp,by simp [Nat.ModEq, Nat.add_mod],(rank_test_at_period hp hq).mp aligned,?_⟩
    have := Nat.mul_lt_mul_of_pos_right (show 2 < k by omega) hq.pos
    omega

-- An aligned prime companion cannot occur in the Fibonacci factor at the half period.
lemma companion_not_in_fibonacci_half {q : ℕ} (hq : q.Prime) (hl : 53 < q)
    (hp : (2*q+1).Prime) : ¬ 2*q+1 ∣ Nat.fib (pisano q / 2) := by
  intro half
  have twice : 2*(pisano q / 2) = pisano q :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period (by omega : 2 < q)))
  have aligned := half.trans (Nat.fib_dvd _ _ (twice ▸ dvd_mul_left (pisano q / 2) 2))
  have residue := aligned_companion_residue hq hl hp aligned
  have full := (nonsplit_period_cofactor hq (by omega) (by omega)).1
  have dh : pisano q / 2 ∣ q+1 := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2)
    (show 2*(pisano q/2) ∣ 2*(q+1) by rwa [twice])
  have next := half.trans (Nat.fib_dvd _ _ dh)
  have odd := hq.eq_two_or_odd.resolve_left (by omega)
  have even : Even (q+1) := even_iff_two_dvd.mpr (by omega)
  let : NeZero (2*q+1) := ⟨hp.ne_zero⟩
  have ret := (period_dvd_double_iff (2*q+1) (q+1)).mpr (by simpa [even] using next)
  have no := (nonsplit_period_cofactor hp (by omega) (by omega)).2.1
  exact no (by rwa [show 2*q+1+1 = 2*(q+1) by omega])

lemma companion_in_lucas_half_iff {q : ℕ} (hq : q.Prime) (hl : 53 < q) (hp : (2*q+1).Prime) :
    let h := pisano q / 2
    2*q+1 ∣ Nat.fib (pisano q) ↔ 2*q+1 ∣ 2*Nat.fib (h+1) - Nat.fib h := by
  dsimp only
  have twice : 2*(pisano q / 2) = pisano q :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period (by omega : 2 < q)))
  have prod := Nat.fib_two_mul (pisano q/2)
  rw [twice] at prod
  rw [prod]
  exact ⟨fun d => (hp.dvd_mul.mp d).resolve_left (companion_not_in_fibonacci_half hq hl hp),
    fun d => dvd_mul_of_dvd_right d _⟩

lemma other_witness_half_tests {q : ℕ} (hq : q.Prime) (hl : 53 < q) :
    let h := pisano q / 2
    q ∣ (ordCompl[q] (ordCompl[2*q+1] (Nat.fib (pisano q)))).totient ↔
      q ∣ (ordCompl[q] (Nat.fib h)).totient ∨
      q ∣ (ordCompl[q] (ordCompl[2*q+1] (2*Nat.fib (h+1) - Nat.fib h))).totient := by
  dsimp only
  let h := pisano q / 2
  let a := Nat.fib h
  let b := 2*Nat.fib (h+1) - a
  let : NeZero q := ⟨hq.ne_zero⟩
  have pos := (period_and_returns q).1
  have twice : 2*h = pisano q :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period (by omega : 2 < q)))
  have prod : Nat.fib (pisano q) = a*b := twice ▸ Nat.fib_two_mul h
  have nz := (Nat.fib_pos.mpr pos).ne'
  have both : a*b ≠ 0 := prod ▸ nz
  rw [companion_removed_witness hq nz, stripped_totient_witness hq (left_ne_zero_of_mul both),
    companion_removed_witness hq (right_ne_zero_of_mul both)]
  change (∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ Nat.fib (pisano q) ∧ p ≠ 2*q+1) ↔
    (∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ a) ∨
    (∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD q] ∧ p ∣ b ∧ p ≠ 2*q+1)
  rw [prod]
  constructor
  · rintro ⟨p,hp,cong,divides,other⟩
    rcases hp.dvd_mul.mp divides with left | right
    · exact Or.inl ⟨p,hp,cong,left⟩
    · exact Or.inr ⟨p,hp,cong,right,other⟩
  · rintro (⟨p,hp,cong,left⟩ | ⟨p,hp,cong,right,other⟩)
    · refine ⟨p,hp,cong,dvd_mul_of_dvd_left left _,?_⟩
      rintro rfl
      exact companion_not_in_fibonacci_half hq hl hp left
    · exact ⟨p,hp,cong,dvd_mul_of_dvd_right right _,other⟩

-- On the remaining residue class the half period is even. Hence the square
-- test lies in the Fibonacci factor, while the companion test lies in Lucas.
lemma even_half_in_companion_class {q : ℕ} (hq : q.Prime) (hl : 5 < q) (residue : q%15 = 8) :
    Even (pisano q/2) := by
  obtain ⟨full, _, odd⟩ := nonsplit_period_cofactor hq hl (by omega)
  let c := 2*(q+1)/pisano q
  have twice : 2*(pisano q/2) = pisano q :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period (by omega : 2 < q)))
  have product : 2*((pisano q/2)*c) = 2*(q+1) := by
    rw [← Nat.mul_assoc, twice]
    exact Nat.mul_div_cancel' full
  have half : (pisano q/2)*c = q+1 := by omega
  have qo := hq.eq_two_or_odd.resolve_left (by omega)
  have evenprod : 2 ∣ (pisano q/2)*c := by rw [half]; omega
  exact even_iff_two_dvd.mpr ((Nat.prime_two.dvd_mul.mp evenprod).resolve_right odd.not_two_dvd_nat)

lemma stable_residue_half_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) (residue : q%15 = 8) :
    pisano (q^2) = pisano q ↔ q^2 ∣ Nat.fib (pisano q/2) := by
  simpa only [if_pos (even_half_in_companion_class hq hl residue)] using stable_half_period_iff (m := q) (j := 2) (by omega) (by decide)

-- Cassini doubles the precision on the Lucas side of a square-zero half period.
lemma lucas_half_lift {q : ℕ} (hq : q.Prime) (hl : 2 < q)
    (even : Even (pisano q/2)) (square : q^2 ∣ Nat.fib (pisano q/2)) :
    let h := pisano q/2
    q^4 ∣ (2*Nat.fib (h+1) - Nat.fib h) + 2 := by
  let h := pisano q/2
  let a := Nat.fib h
  let b := Nat.fib (h+1)
  let L := 2*b-a
  let : NeZero q := ⟨hq.ne_zero⟩
  have pos := (period_and_returns q).1
  have twice : 2*h = pisano q := Nat.mul_div_cancel' (even_iff_two_dvd.mp (even_period hl))
  have hp : 0 < h := by omega
  have h2 : 2 ≤ h := by obtain ⟨t,ht⟩ := even; change h = t+t at ht; omega
  have ab : a ≤ b := Nat.fib_le_fib_succ
  have bound : a ≤ 2*b := by omega
  have b2 : 2 ≤ b := (Nat.fib_mono (show 3 ≤ h+1 by omega) : Nat.fib 3 ≤ b)
  have L2 : 2 ≤ L := by dsimp [L]; omega
  have zd := (dvd_pow_self q (by decide : 2 ≠ 0)).trans square
  have no : ¬ q ∣ L-2 := by
    intro d
    let : Fact q.Prime := ⟨hq⟩
    have zero : (a : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr zd
    have rel := (ZMod.natCast_eq_zero_iff ..).mpr d
    change (((2*b-a-2 : ℕ) : ZMod q)) = 0 at rel
    rw [Nat.cast_sub L2, Nat.cast_sub bound, Nat.cast_mul, Nat.cast_ofNat, zero, sub_zero] at rel
    have two : (2 : ZMod q) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime (ZMod q) Nat.prime_two (show q ≠ 2 by omega)
    have one : (b : ZMod q) = 1 := by
      apply mul_left_cancel₀ two
      linear_combination rel
    have ret : pisano q ∣ h := ((period_and_returns q).2 _).mpr
      ⟨zd, (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using one)⟩
    have := Nat.le_of_dvd hp ret
    omega
  have prod : q^4 ∣ (L+2)*(L-2) := by
    apply (ZMod.natCast_eq_zero_iff ..).mp
    have sqzero : (a : ZMod (q^4))^2 = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
      simpa only [← pow_mul] using (pow_dvd_pow_of_dvd square 2)
    have det := cassini_signed (q^4) h
    change (b : ZMod (q^4))^2 - a*b - a^2 = (-1)^h at det
    rw [show (-1 : ZMod (q^4))^h = 1 from even.neg_one_pow] at det
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub L2]
    dsimp only [L]
    rw [Nat.cast_sub bound, Nat.cast_mul, Nat.cast_ofNat]
    linear_combination 4*det + 5*sqzero
  exact ((hq.coprime_iff_not_dvd.mpr no).pow_left 4).dvd_of_dvd_mul_right prod

-- Since 16*q^4 is 1 modulo 2q+1, the companion test on a lifted Lucas
-- number is the residue 32 test on its smaller quotient.
lemma companion_quotient_test {q L : ℕ} (hq : 2 < q) (prime : (2*q+1).Prime)
    (lift : q^4 ∣ L+2) :
    2*q+1 ∣ L ↔ (L+2)/q^4 ≡ 32 [MOD (2*q+1)] := by
  let c := 2*q+1
  let : Fact c.Prime := ⟨prime⟩
  let T := (L+2)/q^4
  have product : q^4*T = L+2 := Nat.mul_div_cancel' lift
  have modulus : (2 : ZMod c)*(q : ZMod c)+1 = 0 := by
    calc (2 : ZMod c)*(q : ZMod c)+1 = ((2*q+1 : ℕ) : ZMod c) := by push_cast; rfl
         _ = 0 := ZMod.natCast_self c
  have inv : (16 : ZMod c)*(q : ZMod c)^4 = 1 := by
    calc (16 : ZMod c)*(q : ZMod c)^4 = (2*(q : ZMod c))^4 := by ring
         _ = 1 := by rw [show 2*(q : ZMod c) = -1 by linear_combination modulus]; norm_num
  have eq := congrArg (fun n : ℕ => (n : ZMod c)) product
  push_cast at eq
  have relation : (T : ZMod c) = 16*(L : ZMod c)+32 := by
    linear_combination 16*eq - (T : ZMod c)*inv
  have two : (2 : ZMod c) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime (ZMod c) Nat.prime_two (by dsimp [c]; omega)
  have unit : (16 : ZMod c) ≠ 0 := by rw [show (16 : ZMod c) = 2^4 by norm_num]; exact pow_ne_zero _ two
  change c ∣ L ↔ T ≡ 32 [MOD c]
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_natCast_iff, relation, Nat.cast_ofNat]
  constructor
  · intro z; simp [z]
  · intro e
    exact (mul_eq_zero.mp (show (16 : ZMod c)*(L : ZMod c) = 0 by linear_combination e)).resolve_left unit


lemma stable_companion_quotient_iff {q : ℕ} (hq : q.Prime) (hl : 53 < q) (residue : q%15 = 8)
    (square : q^2 ∣ Nat.fib (pisano q/2)) (prime : (2*q+1).Prime) :
    let h := pisano q/2
    2*q+1 ∣ Nat.fib (pisano q) ↔ ((2*Nat.fib (h+1) - Nat.fib h) + 2)/q^4 ≡ 32 [MOD (2*q+1)] :=
  (companion_in_lucas_half_iff hq hl prime).trans
    (companion_quotient_test (by omega) prime
      (lucas_half_lift hq (by omega) (even_half_in_companion_class hq (by omega) residue) square))

lemma integer_cassini (n : ℕ) :
    (Nat.fib (n+1) : ℤ)^2 - (Nat.fib n : ℤ)*Nat.fib (n+1) - (Nat.fib n : ℤ)^2 = (-1)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.fib_add_two, Nat.cast_add, pow_succ]
    linear_combination -ih

-- Lucas doubling selects a single square at the quarter-period.
lemma quarter_factorization (t : ℕ) :
    (2*Nat.fib (2*t+1)-Nat.fib (2*t))+2 =
      (if Even t then 1 else 5) * (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t)^2 := by
  have bound (n : ℕ) : Nat.fib n ≤ 2*Nat.fib (n+1) := by
    have := Nat.fib_le_fib_succ (n := n)
    omega
  have det := integer_cassini t
  by_cases even : Even t
  · simp only [if_pos even, one_mul]
    rw [even.neg_one_pow] at det
    zify [bound (2*t), bound t]
    rw [Nat.fib_two_mul_add_one, Nat.fib_two_mul]
    push_cast [Nat.cast_sub (bound t)]
    linear_combination -2*det
  · simp only [if_neg even]
    rw [(Nat.not_even_iff_odd.mp even).neg_one_pow] at det
    zify [bound (2*t)]
    rw [Nat.fib_two_mul_add_one, Nat.fib_two_mul]
    push_cast [Nat.cast_sub (bound t)]
    linear_combination 2*det

lemma quarter_square_of_lift {q t : ℕ} (hq : q.Prime) (hl : 5 < q)
    (lift : q^4 ∣ (2*Nat.fib (2*t+1)-Nat.fib (2*t))+2) :
    q^2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) := by
  rw [quarter_factorization] at lift
  have bound : (if Even t then 1 else 5) < q := by split <;> omega
  have pos : 0 < (if Even t then 1 else 5) := by split <;> decide
  have cop := hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos bound)
  apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
  simpa only [← pow_mul] using (cop.pow_left 4).dvd_of_dvd_mul_left lift

lemma half_square_of_quarter {q t : ℕ}
    (square : q^2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t)) :
    q^2 ∣ Nat.fib (2*t) := by
  rw [Nat.fib_two_mul]
  split at square
  · exact dvd_mul_of_dvd_right square _
  · exact dvd_mul_of_dvd_left square _

lemma quarter_quotient {q t : ℕ} (pos : 0 < q)
    (square : q^2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t)) :
    ((2*Nat.fib (2*t+1)-Nat.fib (2*t))+2)/q^4 =
      (if Even t then 1 else 5) * ((if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t)/q^2)^2 := by
  rw [quarter_factorization]
  apply Nat.div_eq_of_eq_mul_left (pow_pos pos 4)
  let B := if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t
  let w := if Even t then 1 else 5
  change w*B^2 = w*(B/q^2)^2*q^4
  calc w*B^2 = w*(q^2*(B/q^2))^2 := by rw [Nat.mul_div_cancel' square]
       _ = _ := by ring


lemma half_eq_twice_quarter {q : ℕ} (hq : q.Prime) (hl : 5 < q) (residue : q%15 = 8) :
    pisano q/2 = 2*(pisano q/4) := by
  obtain ⟨k,hk⟩ := even_half_in_companion_class hq hl residue
  omega

lemma half_quarter_square_iff {q : ℕ} (hq : q.Prime) (hl : 5 < q) (residue : q%15 = 8) :
    let t := pisano q/4
    q^2 ∣ Nat.fib (pisano q/2) ↔ q^2 ∣ (if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t) := by
  dsimp only
  have twice := half_eq_twice_quarter hq hl residue
  constructor
  · intro square
    have lift := lucas_half_lift hq (by omega) (even_half_in_companion_class hq hl residue) square
    dsimp only at lift
    rw [twice] at lift
    exact quarter_square_of_lift hq hl lift
  · intro square
    rw [twice]
    exact half_square_of_quarter square

lemma companion_quarter_iff {q : ℕ} (hq : q.Prime) (hl : 53 < q) (residue : q%15 = 8)
    (square : q^2 ∣ Nat.fib (pisano q/2)) (hp : (2*q+1).Prime) :
    let t := pisano q/4
    2*q+1 ∣ Nat.fib (pisano q) ↔
      (if Even t then 1 else 5) * ((if Even t then 2*Nat.fib (t+1)-Nat.fib t else Nat.fib t)/q^2)^2 ≡ 32 [MOD (2*q+1)] := by
  have test := stable_companion_quotient_iff hq hl residue square hp
  dsimp only at test ⊢
  rw [half_eq_twice_quarter hq (by omega) residue,
      quarter_quotient hq.pos ((half_quarter_square_iff hq (by omega) residue).mp square)] at test
  exact test

-- Cubing the two roots of Y²-xY-1 recovers the Fibonacci roots.
lemma cubic_rank_descent {p : ℕ} (hp : p.Prime) (hl : 5 < p) (three : 3 ∣ p+1)
    (zero : p ∣ Nat.fib (p+1)) (x : ZMod p) (cubic : x^3+3*x=1) :
    rankOfApparition p ∣ (p+1)/3 := by
  let : Fact p.Prime := ⟨hp⟩
  let K := AlgebraicClosure (ZMod p)
  let X : K := algebraMap (ZMod p) K x
  have trace : X^3+3*X=1 := by
    simpa [X, map_ofNat] using congrArg (algebraMap (ZMod p) K) cubic
  have fixed : X^p=X := by
    simp [X, ← map_pow, ZMod.pow_card]
  have two : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K Nat.prime_two (show p ≠ 2 by omega)
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (X^2+4) (by decide : 0 < 2)
  let u := (X+s)/2
  let v := X-u
  have twice : u*2=X+s := div_mul_cancel₀ _ two
  have quad : u^2=X*u+1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 two)
    linear_combination (2*u+ s-X)*twice + hs
  have prod : u*v = -1 := by dsimp [v]; linear_combination -quad
  have sum : u^3+v^3=1 := by
    dsimp [v]
    linear_combination trace + 3*X*quad
  have cubeprod : u^3*v^3 = -1 := by rw [←mul_pow, prod]; norm_num
  have a : (u^3)^2=u^3+1 := by linear_combination u^3*sum - cubeprod
  have b : (v^3)^2=v^3+1 := by linear_combination v^3*sum - cubeprod
  have diff : u^3-v^3 ≠ 0 := by
    intro same
    have five : (5 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (by decide : Nat.Prime 5) (show p ≠ 5 by omega)
    apply five
    linear_combination (2*u^3-1)*sum + (2*u^3-1)*same - 4*a
  have conj : v^p = X-u^p := by simp [v, sub_pow_char, fixed]
  have roots : (u^p-u)*(u^p-v)=0 := by
    have h := congrArg (fun z : K => z^p) quad
    simp only [add_pow_char, mul_pow, one_pow, fixed] at h
    rw [←pow_mul, Nat.mul_comm, pow_mul] at h
    dsimp only [v]
    linear_combination h - quad
  have swap : u^p=v := by
    rcases mul_eq_zero.mp roots with fix | swap
    · have fu := sub_eq_zero.mp fix
      have fv : v^p=v := by rw [conj, fu]
      have hz : (Nat.fib (p+1) : K) = 0 := (CharP.cast_eq_zero_iff K p _).mpr zero
      have eq := fib_root_difference a b (p+1)
      have cube_fixed (z : K) (fz : z^p=z) : (z^3)^p=z^3 := by
        rw [←pow_mul, Nat.mul_comm 3 p, pow_mul, fz]
      rw [hz, zero_mul, pow_succ (u^3) p, pow_succ (v^3) p,
          cube_fixed u fu, cube_fixed v fv] at eq
      exact (diff (by linear_combination -eq - a + b)).elim
    · exact sub_eq_zero.mp swap
  have swapv : v^p=u := by rw [conj,swap]; dsimp [v]; ring
  have eq : u^(p+1)=v^(p+1) := by rw [pow_succ, pow_succ, swap, swapv, mul_comm]
  have third : 3*((p+1)/3)=p+1 := Nat.mul_div_cancel' three
  have h := fib_root_difference a b ((p+1)/3)
  rw [← pow_mul, ← pow_mul, third, eq, sub_self] at h
  exact rank_dvd_index (by omega) ((CharP.cast_eq_zero_iff K p _).mp ((mul_eq_zero.mp h).resolve_right diff))

-- A cubic root certificate strips one factor of three even if three divides the rank.
lemma alignment_of_cubic_cofactor {q : ℕ} (hq : q.Prime) (hl : 5 < q)
    (residue : q%15 = 8) (hp : (2*q+1).Prime) :
    let c := 2*(q+1)/pisano q
    3 ∣ c → (rankOfApparition (2*q+1)).Coprime (c/3) →
      (∃ x : ZMod (2*q+1), x^3 + 3*x = 1) → 2*q+1 ∣ Nat.fib (pisano q) := by
  intro c three cop root
  obtain ⟨x, hx⟩ := root
  have full := (nonsplit_period_cofactor hq hl (by omega)).1
  have whole : pisano q*c = 2*(q+1) := Nat.mul_div_cancel' full
  have times : 3*(pisano q*(c/3)) = 2*q+1+1 := by
    calc 3*(pisano q*(c/3)) = pisano q*(3*(c/3)) := by ring
         _ = 2*q+1+1 := by rw [Nat.mul_div_cancel' three, whole]; omega
  have zero := zero_at_selected_neighbor hp (by omega)
  rw [if_neg (by omega)] at zero
  have rank := cubic_rank_descent hp (by omega) (by rw [←times]; exact dvd_mul_right ..) zero x hx
  rw [←times, Nat.mul_div_cancel_left _ (by decide : 0 < 3)] at rank
  exact (rank_test_at_period hp hq).mp (cop.dvd_of_dvd_mul_right rank)

-- When the reduced totient is prime to q, only the canonical witness can work.
lemma canonical_companion_iff : (H1 ∧ H2 ∧ H3) ↔
    ∀ q : ℕ, q.Prime → 53 < q → pisano (q^2) = pisano q →
    (¬ q ∣ (ordCompl[q] (ordCompl[2*q+1] (Nat.fib (pisano q)))).totient) →
      (2*q+1).Prime ∧ 2*q+1 ∣ Nat.fib (pisano q) := by
  constructor
  · rintro ⟨exclude, prime, align⟩ q hq hl stable noLarge
    have halves := mt (other_witness_half_tests hq hl).mpr noLarge
    have large := large_prime_of_stability hq (by omega) stable
    have long := large_period_of_stability hq hl stable
    have square := (stable_selected_iff hq (by omega)).mp stable
    have residue : q % 15 = 8 := by
      by_contra h
      exact exclude q hq large long halves h square
    have halfSquare := (stable_residue_half_iff hq (by omega) residue).mp stable
    have quarter := (half_quarter_square_iff hq (by omega) residue).mp halfSquare
    have hp := prime q hq large long halves residue quarter
    refine ⟨hp, ?_⟩
    by_cases cop : (rankOfApparition (2*q+1)).Coprime (2*(q+1)/pisano q)
    · exact alignment_of_coprime_cofactor hq (by omega) residue hp cop
    · let c := 2*(q+1)/pisano q
      by_cases certificate : 3 ∣ c ∧ (rankOfApparition (2*q+1)).Coprime (c/3) ∧
          ∃ x : ZMod (2*q+1), x^3 + 3*x = 1
      · exact alignment_of_cubic_cofactor hq (by omega) residue hp
          certificate.1 certificate.2.1 certificate.2.2
      · exact (companion_quarter_iff hq hl residue halfSquare hp).mpr
          (align q hq large long halves residue quarter hp cop certificate)
  · intro canonical
    refine ⟨?_, ?_, ?_⟩
    · intro q hq large _ h noLarge outside square
      have noFull := mt (other_witness_half_tests hq (by omega)).mp noLarge
      have stable := (stable_selected_iff hq (by omega)).mpr square
      obtain ⟨hp, aligned⟩ := canonical q hq (by omega) stable noFull
      exact outside (aligned_companion_residue hq (by omega) hp aligned)
    · intro q hq large _ h noLarge residue t quarter
      have noFull := mt (other_witness_half_tests hq (by omega)).mp noLarge
      have square := (half_quarter_square_iff hq (by omega) residue).mpr quarter
      exact (canonical q hq (by omega) ((stable_residue_half_iff hq (by omega) residue).mpr square) noFull).1
    · intro q hq large _ h noLarge residue t quarter hp c _ _
      have noFull := mt (other_witness_half_tests hq (by omega)).mp noLarge
      have square := (half_quarter_square_iff hq (by omega) residue).mpr quarter
      have stable := (stable_residue_half_iff hq (by omega) residue).mpr square
      exact (companion_quarter_iff hq (by omega) residue square hp).mp (canonical q hq (by omega) stable noFull).2

lemma parent_iff : (H1 ∧ H2 ∧ H3) ↔ OMA.R_arxiv_2604_17847_R1.H2 := by
  rw [canonical_companion_iff]
  constructor
  · intro canonical q hq hl square
    let : NeZero q := ⟨hq.ne_zero⟩
    have stable := (period_power_eq_iff_at_period hq (by omega) (by decide : 0 < 2)).mpr square
    by_cases other : q ∣ (ordCompl[q] (ordCompl[2*q+1] (Nat.fib (pisano q)))).totient
    · have nz := (Nat.fib_pos.mpr (period_and_returns q).1).ne'
      obtain ⟨p,hp,cong,divides,_⟩ := (companion_removed_witness hq nz).mp other
      exact ⟨p,hp,cong,(rank_test_at_period hp hq).mpr divides⟩
    · obtain ⟨hp,divides⟩ := canonical q hq hl stable other
      exact ⟨2*q+1,hp,by simp [Nat.ModEq, Nat.add_mod],(rank_test_at_period hp hq).mpr divides⟩
  · intro parent q hq hl stable noOther
    let : NeZero q := ⟨hq.ne_zero⟩
    have square := (period_power_eq_iff_at_period hq (by omega) (by decide : 0 < 2)).mp stable
    obtain ⟨p,hp,cong,aligned⟩ := parent q hq hl square
    have divides := (rank_test_at_period hp hq).mp aligned
    by_cases canonical : p = 2*q+1
    · exact canonical ▸ And.intro hp divides
    · have nz := (Nat.fib_pos.mpr (period_and_returns q).1).ne'
      exact (noOther ((companion_removed_witness hq nz).mpr ⟨p,hp,cong,divides,canonical⟩)).elim

theorem main : H1 → H2 → H3 → OMA.R_arxiv_2604_17847_R1.H2 :=
  fun first second third => parent_iff.mp ⟨first,second,third⟩

end OMA.R_arxiv_2604_17847_R1_H2_R1
