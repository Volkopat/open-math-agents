import OMAStatements.S_oeis_a049997
import Mathlib

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a049997_R1

open Nat (fib)

/-- A square quotient of two different positive-index Fibonacci terms at
divisible indices has upper index at most 12 (Ribenboim's square classes). -/
def H1 : Prop := ∀ d n y : ℕ, 0 < d → d < n → d ∣ n →
  fib n / fib d = y ^ 2 → n ≤ 12

/-- Odd-prime part of the Bugeaud–Mignotte–Siksek single-term classification. -/
def H2 : Prop := ∀ j p y : ℕ, 2 < j → p.Prime → 2 < p → fib j = y ^ p → j = 6

/-- For an odd prime p, only consider pairs of terms that are individually
p-th powers away from the primes of T. Find a prime of T where their
multiplicities fail to cancel modulo p. -/
def H3 : Prop := ∀ m n p : ℕ, 2 < m → m < n → p.Prime → 2 < p →
  let d := m.gcd n
  let T := (fib d).gcd ((m / d) * (n / d))
  1 < T →
  (∀ q : ℕ, q.Prime → ¬ q ∣ T →
    p ∣ (fib m).factorization q ∧ p ∣ (fib n).factorization q) →
  ∃ q : ℕ, q.Prime ∧ q ∣ T ∧ ¬ p ∣ (fib m).factorization q + (fib n).factorization q

/-- The gcd of the common Fibonacci term and a normalized multiple can be
computed from the index multiplier alone. -/
theorem gcd_fib_quotient (d t : ℕ) (hd : 0 < d) :
    (fib d).gcd (fib (t * d) / fib d) = (fib d).gcd t := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  let D := fib (j + 1)
  let C := fib (j + 1 + 1)
  let Q := fun k => fib (k * (j + 1)) / D
  have hD : 0 < D := Nat.fib_pos.mpr (by omega)
  have hQ (k : ℕ) : D * Q k = fib (k * (j+1)) :=
    Nat.mul_div_cancel' (Nat.fib_dvd _ _ (dvd_mul_left _ _))
  have hstep (k : ℕ) : Q (k+1) = Q k * fib j + fib (k*(j+1)+1) := by
    apply Nat.mul_left_cancel hD
    rw [hQ, Nat.succ_mul, ← Nat.add_assoc, Nat.fib_add, mul_add D, ← mul_assoc, hQ]
    change _ + _ * D = _ + D * _
    ac_rfl
  have hC : (fib j : ZMod D) = (C : ZMod D) := by
    dsimp [C]
    rw [show j + 1 + 1 = j + 2 by omega, Nat.fib_add_two, Nat.cast_add]
    change _ = _ + (D : ZMod D)
    simp
  have hcong (k : ℕ) :
      (Q k : ZMod D) * C = k * (C : ZMod D)^k ∧
      (fib (k*(j+1)+1) : ZMod D) = (C : ZMod D)^k := by
    induction k with
    | zero => simp [Q]
    | succ k ih =>
      constructor
      · rw [hstep, Nat.cast_add, Nat.cast_mul, hC, ih.1, ih.2, Nat.cast_succ, pow_succ]
        ring
      · rw [Nat.succ_mul, Nat.fib_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
        change _ * (D : ZMod D) + _ * (C : ZMod D) = _
        rw [ZMod.natCast_self, mul_zero, zero_add, ih.2, pow_succ]
  have hc : C.Coprime D := (Nat.fib_coprime_fib_succ _).symm
  have he : Q t * C ≡ t * C^t [MOD D] := by
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_pow] using (hcong t).1
  calc
    D.gcd (Q t) = D.gcd (Q t * C) := (hc.gcd_mul_right_cancel_right _).symm
    _ = D.gcd (t * C^t) := by simpa only [Nat.gcd_comm D] using he.gcd_eq
    _ = D.gcd t := (hc.pow_left _).gcd_mul_right_cancel_right _

/-- A prime dividing the common term gains no multiplicity at an index
multiple whose multiplier it does not divide. -/
theorem factorization_fib_of_not_dvd_multiplier {d i q : ℕ} (hd : 0 < d) (hi : d ∣ i)
    (hf : fib i ≠ 0) (hq : q ∣ fib d) (hidx : ¬ q ∣ i/d) :
    (fib i).factorization q = (fib d).factorization q := by
  have hmul : fib d * (fib i / fib d) = fib i := Nat.mul_div_cancel' (Nat.fib_dvd _ _ hi)
  have hquot : ¬ q ∣ fib i / fib d := by
    intro hqQ
    have hcommon := Nat.dvd_gcd hq hqQ
    have hindex := gcd_fib_quotient d (i/d) hd
    rw [Nat.div_mul_cancel hi] at hindex
    rw [hindex] at hcommon
    exact hidx (hcommon.trans (Nat.gcd_dvd_right _ _))
  have hnz : fib i / fib d ≠ 0 := right_ne_zero_of_mul (hmul ▸ hf)
  have hval := congrArg (fun z : ℕ => z.factorization q) hmul
  simpa [Nat.factorization_mul (Nat.fib_pos.mpr hd).ne' hnz,
    Nat.factorization_eq_zero_of_not_dvd hquot] using hval.symm

private theorem extract_power {a b c p : ℕ} (hcop : a.Coprime b) (h : a*b = c^p) :
    ∃ u, a = u^p :=
  exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr hcop) h

/-- Extract a square from each coprime quotient after cancelling the square
of the common divisor. -/
private theorem square_quotient {g u v b : ℕ} (hg : 0 < g) (huv : u.Coprime v)
    (h : (g*u)*(g*v) = b^2) : ∃ w, v = w^2 := by
  have he : g^2 * (u*v) = b^2 := by rw [← h]; ring
  have hd : g ∣ b := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp ⟨_, he.symm⟩
  obtain ⟨c, rfl⟩ := hd
  rw [mul_pow] at he
  exact extract_power huv.symm (by rw [mul_comm]; exact Nat.mul_left_cancel (pow_pos hg _) he)

private theorem small_squares {m n b : ℕ} (hm : 2 < m) (hmn : m < n)
    (hn : n ≤ 12) (he : fib m * fib n = b^2) : m = 3 ∧ n = 6 := by
  have table : ∀ i j : Fin 13, 2 < i.val → i.val < j.val →
      (fib i.val * fib j.val).sqrt ^ 2 = fib i.val * fib j.val → i.val = 3 ∧ j.val = 6 := by
    decide +kernel
  apply table ⟨m, by omega⟩ ⟨n, by omega⟩ hm hmn
  change (fib m * fib n).sqrt ^ 2 = fib m * fib n
  rw [he, Nat.sqrt_eq']

/-- In the coprime case all three factors g², u, v split as powers.
For odd prime p, extracting a p-th power from g² also extracts it from g. -/
private theorem odd_split {g u v y p : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hgu : g.Coprime u) (hgv : g.Coprime v) (huv : u.Coprime v)
    (h : (g*u)*(g*v) = y^p) :
    (∃ a, g*u = a^p) ∧ (∃ b, g*v = b^p) := by
  have he : g^2 * (u*v) = y^p := by rw [← h]; ring
  obtain ⟨c, hc⟩ := extract_power ((hgu.mul_right hgv).pow_left 2) he
  obtain ⟨z, hz, _⟩ := Nat.exists_eq_pow_of_exponent_coprime_of_pow_eq_pow
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)) hc
  obtain ⟨a, ha⟩ := extract_power ((hgu.symm.pow_right 2).mul_right huv)
    (show u*(g^2*v) = y^p by rw [← he]; ring)
  obtain ⟨b, hb⟩ := extract_power ((hgv.symm.pow_right 2).mul_right huv.symm)
    (show v*(g^2*u) = y^p by rw [← he]; ring)
  exact ⟨⟨z*a, by rw [hz, ha, mul_pow]⟩, ⟨z*b, by rw [hz, hb, mul_pow]⟩⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a049997.main := by
  intro hsquare hsingle hremaining m n hm hmn
  constructor
  · rintro ⟨b, k, hk, hpow⟩
    let p := k.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨s, hs⟩ := Nat.minFac_dvd k
    let y := b^s
    have he : fib m * fib n = y^p := by
      dsimp [y]
      rw [← pow_mul, mul_comm s, ← hs, hpow]
    let d := m.gcd n
    let g := fib d
    let u := fib m / g
    let v := fib n / g
    have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
    have hg : 0 < g := Nat.fib_pos.mpr hd
    have hdm : d ∣ m := Nat.gcd_dvd_left _ _
    have hdn : d ∣ n := Nat.gcd_dvd_right _ _
    have hgu : g*u = fib m := Nat.mul_div_cancel' (Nat.fib_dvd _ _ hdm)
    have hgv : g*v = fib n := Nat.mul_div_cancel' (Nat.fib_dvd _ _ hdn)
    have huv : u.Coprime v := by
      dsimp [u,v,g,d]
      rw [Nat.fib_gcd]
      exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ (Nat.fib_pos.mpr (by omega)))
    have hprod : (g*u)*(g*v) = y^p := by rwa [hgu, hgv]
    by_cases htwo : p = 2
    · rw [htwo] at hprod he
      obtain ⟨w, hw⟩ := square_quotient hg huv hprod
      have hlt := (Nat.le_of_dvd (by omega : 0 < m) hdm).trans_lt hmn
      exact small_squares hm hmn (hsquare d n w hd hlt hdn hw) he
    · have hp2 : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm htwo)
      by_cases hind : g.Coprime ((m/d)*(n/d))
      · have of_index (i : ℕ) (hi : d ∣ i) (hc : g.Coprime (i/d)) :
            g.Coprime (fib i / g) := by
          change g.gcd (fib i / g) = 1
          have h := gcd_fib_quotient d (i/d) hd
          rw [Nat.div_mul_cancel hi] at h
          exact h.trans hc
        obtain ⟨hmidx, hnidx⟩ := Nat.coprime_mul_iff_right.mp hind
        obtain ⟨⟨a, ha⟩, ⟨c, hc⟩⟩ := odd_split hp hp2
          (of_index m hdm hmidx) (of_index n hdn hnidx) huv hprod
        have hm6 := hsingle m p a hm hp hp2 (hgu.symm.trans ha)
        have hn6 := hsingle n p c (by omega) hp hp2 (hgv.symm.trans hc)
        omega
      · let R := (m/d)*(n/d)
        let T := g.gcd R
        have hfm : fib m ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
        have hfn : fib n ≠ 0 := (Nat.fib_pos.mpr (by omega)).ne'
        have total (q : ℕ) : p ∣ (fib m).factorization q + (fib n).factorization q := by
          refine ⟨y.factorization q, ?_⟩
          have e := congrArg (fun z : ℕ => z.factorization q) he
          simpa [Nat.factorization_mul hfm hfn, Nat.factorization_pow,
            Finsupp.smul_apply, smul_eq_mul] using e
        have outside (q : ℕ) (_ : q.Prime) (hq : ¬ q ∣ T) :
            p ∣ (fib m).factorization q ∧ p ∣ (fib n).factorization q := by
          have ht := total q
          by_cases hqg : q ∣ g
          · have hqR : ¬ q ∣ R := fun h => hq (Nat.dvd_gcd hqg h)
            have em := factorization_fib_of_not_dvd_multiplier hd hdm hfm hqg
              (fun h => hqR (h.trans (dvd_mul_right _ _)))
            have en := factorization_fib_of_not_dvd_multiplier hd hdn hfn hqg
              (fun h => hqR (h.trans (dvd_mul_left _ _)))
            rw [em, en, ← two_mul] at ht
            have hc := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
            have hpg := hc.dvd_of_dvd_mul_left ht
            exact ⟨em ▸ hpg, en ▸ hpg⟩
          · have hnot : ¬ (q ∣ fib m ∧ q ∣ fib n) := by
              rintro ⟨h1, h2⟩
              apply hqg
              simpa [g,d,Nat.fib_gcd] using Nat.dvd_gcd h1 h2
            by_cases hqm : q ∣ fib m
            · have ez := Nat.factorization_eq_zero_of_not_dvd (fun h => hnot ⟨hqm,h⟩)
              rw [ez, add_zero] at ht
              exact ⟨ht, ez ▸ dvd_zero _⟩
            · have ez := Nat.factorization_eq_zero_of_not_dvd hqm
              rw [ez, zero_add] at ht
              exact ⟨ez ▸ dvd_zero _, ht⟩
        have hTpos : 0 < T := Nat.gcd_pos_of_pos_left _ hg
        have hTne : T ≠ 1 := hind
        obtain ⟨q, _, _, hbad⟩ := hremaining m n p hm hmn hp hp2 (by omega : 1 < T) outside
        exact (hbad (total q)).elim
  · rintro ⟨rfl, rfl⟩
    exact ⟨2, 4, by decide, by decide +kernel⟩

end OMA.R_oeis_a049997_R1
