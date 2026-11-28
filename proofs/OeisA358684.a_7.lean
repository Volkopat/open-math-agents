import FormalConjectures.OEIS.«358684»
import Mathlib.NumberTheory.LucasPrimality

/-! Check the Fermat factor certificates by radix-16 modular exponentiation,
as in Mathlib's Lucas certificates. The first proof is credited to
@RhizomeSlopGenerator. -/

namespace OMA.Fermat7

def residue (a e p : ℕ) : ℕ :=
  if e = 0 then 1 % p else Nat.pow (residue a (e / 16) p) 16 * Nat.pow a (e % 16) % p
termination_by e
decreasing_by omega

lemma residue_eq (a e p : ℕ) : residue a e p = a ^ e % p := by
  fun_induction residue a e p with
  | case1 => simp
  | case2 e _ ih =>
    simp [ih, ← ZMod.natCast_eq_natCast_iff', ← pow_mul, ← pow_add, Nat.div_add_mod']

theorem certify (p a : ℕ) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime)
    (h : 1 < p ∧ l.prod ^ 99 % (p - 1) = 0 ∧ residue a (p - 1) p = 1 ∧
      l.all (fun q => residue a ((p - 1) / q) p ≠ 1) := by decide +kernel) : p.Prime := by
  obtain ⟨hp, hprod, hpow, hall⟩ := h
  have k (e : ℕ) : (a : ZMod p)^e = 1 ↔ residue a e p = 1 := by
    rw [residue_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
      Nat.one_mod_eq_one.mpr (by omega)]
  refine lucas_primality p a ((k _).mpr hpow) fun q hq hd => ?_
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_prod_iff hq.prime).mp
    (hq.dvd_of_dvd_pow (hd.trans (Nat.dvd_of_mod_eq_zero hprod)))
  rw [(Nat.prime_dvd_prime_iff_eq hq (hl r hr)).mp hqr, Ne, k]
  simpa using List.all_eq_true.mp hall r hr

lemma prime_18533742247 : Nat.Prime 18533742247 := certify _ 6 [2, 3, 181, 1896229] (by norm_num)
lemma prime_116503103764643 : Nat.Prime 116503103764643 :=
  certify _ 2 [2, 7, 449, 18533742247] (by simp [prime_18533742247]; norm_num)
lemma prime_59649589127497217 : Nat.Prime 59649589127497217 :=
  certify _ 3 [2, 116503103764643] (by simp [prime_116503103764643]; norm_num)
lemma prime_733803839347 : Nat.Prime 733803839347 := certify _ 2 [2, 3, 2203, 55515497] (by norm_num)
lemma prime_5704689200685129054721 : Nat.Prime 5704689200685129054721 :=
  certify _ 21 [2, 3, 5, 12497, 733803839347] (by simp [prime_733803839347]; norm_num)

end OMA.Fermat7

open OMA.Fermat7 in
theorem OMA.solution : type_of% @OeisA358684.a_7 := by
  let n := Nat.fermatNumber 7
  have hprod : n = 59649589127497217 * 5704689200685129054721 := by decide
  have hp : n.minFac.Prime := Nat.minFac_prime (by rw [hprod]; decide)
  have hd := Nat.minFac_dvd n
  have hle : n.minFac ≤ 59649589127497217 :=
    Nat.minFac_le_of_dvd (by decide) (by rw [hprod]; exact dvd_mul_right _ _)
  rw [hprod] at hd
  have heq : n.minFac = 59649589127497217 := by
    rcases hp.dvd_mul.mp hd with h | h
    · exact (Nat.prime_dvd_prime_iff_eq hp prime_59649589127497217).mp h
    · have := (Nat.prime_dvd_prime_iff_eq hp prime_5704689200685129054721).mp h
      omega
  change 2 ^ 7 - Nat.log2 n.minFac = 73
  rw [heq]
  decide
