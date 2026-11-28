import FormalConjectures.ErdosProblems.«279»
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Erdős problem 279

For each threshold k ≥ 3, the construction chooses one residue class for
each prime and covers every sufficiently large integer at quotient ≥ k.

The construction uses a hub prime, an old controller set, and a periodic
prime reservoir. The prime number theorem for fixed progressions provides
the densities and the prime enumerations. A two-residue Selberg sieve
bounds the remaining targets at each geometric scale so that the
available controllers suffice. The resulting schedule gives a single
residue assignment with the required eventual coverage.

This is an adaptation of Wanfang Chen's complete proof and Lean formalization,
https://github.com/WanfangChen/Erdos/tree/97cf619ff3621df225fce2918ff0adaa0d208275 .
The port targets Lean 4.33.1 and the Formal Conjectures statement, replacing
duplicate sieve lemmas with Mathlib results and shortening the count, CRT,
and logarithm arguments.

Third-party sources from the original formalization include the Apache-2.0
PrimeNumberTheoremAnd project (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd,
tag v4.27.0-rc1) for the PNT and Wiener–Ikehara code and the Apache-2.0 Mathlib
project (https://github.com/leanprover-community/mathlib4) for the sieve code.
The sieve adaptations retain the copyright notice: Copyright (c) 2023
Arend Mellendijk. All rights reserved. The original project also uses
LeanArchitect as a dependency (https://github.com/hanwenzhu/LeanArchitect).
The Wiener–Ikehara compatibility changes draw on the port submitted by
BetAdmin237 (https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3062).
The Apache-2.0 license is reproduced at the end of this file.
-/

section

namespace Erdos279

def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

abbrev Prime := {p : Nat // IsPrime p}

abbrev ResidueAssignment := (p : Prime) → Fin p.1

def Covers (k n : Nat) (r : ResidueAssignment) : Prop :=
  ∃ p : Prime, ∃ t : Nat, k ≤ t ∧ n = (r p : Nat) + t * p.1

def MatureCovers (k n : Nat) (r : ResidueAssignment) : Prop :=
  ∃ p : Prime, k * p.1 ≤ n ∧ n % p.1 = (r p : Nat)

def CoversTail (k : Nat) (r : ResidueAssignment) : Prop :=
  ∃ N : Nat, 1 ≤ N ∧ ∀ n : Nat, N ≤ n → Covers k n r

def P (k : Nat) : Prop := ∃ r : ResidueAssignment, CoversTail k r

def GlobalAffirmative : Prop := ∀ k : Nat, 3 ≤ k → P k

end Erdos279
end

section

namespace Erdos279

theorem isPrime_iff_natPrime (p : Nat) : IsPrime p ↔ Nat.Prime p := by
  simp only [IsPrime, Nat.prime_def]

theorem Prime.natPrime (p : Prime) : Nat.Prime p.1 := (isPrime_iff_natPrime p.1).mp p.2

end Erdos279
end

section

namespace Erdos279

theorem Prime.two_le (p : Prime) : 2 ≤ p.1 := p.2.1

theorem Prime.pos (p : Prime) : 0 < p.1 := Nat.lt_of_lt_of_le Nat.zero_lt_two p.two_le

theorem covers_iff_matureCovers (k n : Nat) (r : ResidueAssignment) :
    Covers k n r ↔ MatureCovers k n r := by
  constructor
  · rintro ⟨p, t, hkt, rfl⟩
    refine ⟨p, ?_, ?_⟩
    · exact Nat.le_trans (Nat.mul_le_mul_right p.1 hkt)
        (Nat.le_add_left (t * p.1) (r p : Nat))
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (r p).isLt]
  · rintro ⟨p, hkn, hmod⟩
    have ht : k ≤ n / p.1 := (Nat.le_div_iff_mul_le p.pos).mpr hkn
    refine ⟨p, n / p.1, ht, ?_⟩
    calc
      n = n % p.1 + p.1 * (n / p.1) := (Nat.mod_add_div n p.1).symm
      _ = (r p : Nat) + (n / p.1) * p.1 := by
        rw [hmod, Nat.mul_comm]

end Erdos279
end

section

namespace Erdos279

abbrev ShiftedAssignment := ResidueAssignment

def unshiftAssignment (a : ShiftedAssignment) : ResidueAssignment := fun p =>
    ⟨((a p : Nat) + 1) % p.1, Nat.mod_lt _ p.pos⟩

def ShiftedMatureCovers (k m : Nat) (a : ShiftedAssignment) : Prop :=
  ∃ p : Prime, k * p.1 ≤ m + 1 ∧ m % p.1 = (a p : Nat)

theorem shiftedMatureCovers_implies_original {k m : Nat} {a : ShiftedAssignment}
    (hcover : ShiftedMatureCovers k m a) :
    MatureCovers k (m + 1) (unshiftAssignment a) := by
  rcases hcover with ⟨p, hkp, hmod⟩
  refine ⟨p, hkp, ?_⟩
  change (m + 1) % p.1 = ((a p : Nat) + 1) % p.1
  calc
    (m + 1) % p.1 = (m % p.1 + 1) % p.1 := (Nat.mod_add_mod m p.1 1).symm
    _ = ((a p : Nat) + 1) % p.1 := by rw [hmod]

def ShiftedCoversTail (k : Nat) (a : ShiftedAssignment) : Prop :=
  ∃ M₀ : Nat, ∀ m : Nat, M₀ ≤ m → ShiftedMatureCovers k m a

theorem P_of_shiftedCoversTail {k : Nat} {a : ShiftedAssignment}
    (hshifted : ShiftedCoversTail k a) :
    P k := by
  rcases hshifted with ⟨M₀, htail⟩
  refine ⟨unshiftAssignment a, M₀ + 1, ?_, ?_⟩
  · exact Nat.succ_le_succ (Nat.zero_le M₀)
  · intro n hn
    have hn1 : 1 ≤ n := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le M₀)) hn
    have hm : M₀ ≤ n - 1 := Nat.le_sub_of_add_le hn
    have hm1 : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    apply (covers_iff_matureCovers k n (unshiftAssignment a)).mpr
    rw [← hm1]
    exact shiftedMatureCovers_implies_original (htail (n - 1) hm)

end Erdos279
end

section

namespace Erdos279

def InControllerProgression (h p : Prime) : Prop := p.1 % h.1 = 1

def SmoothFor (h : Prime) (m : Nat) : Prop := ∀ q : Prime, q.1 ∣ m →
    q = h ∨ InControllerProgression h q

def HardTarget (h : Prime) (m : Nat) : Prop := SmoothFor h m ∧ h.1 ∣ m

def HasSmallOutsideFactor (k : Nat) (h : Prime) (m : Nat) : Prop := ∃ q : Prime,
    q.1 ∣ m ∧ q ≠ h ∧
    ¬ InControllerProgression h q ∧
    k * q.1 ≤ m

structure CompletionData (k : Nat) where
  hub : Prime
  shifted : ShiftedAssignment
  threshold : Nat
  smooth_noHub : ∀ m : Nat, threshold ≤ m → SmoothFor hub m → ¬ hub.1 ∣ m →
      ShiftedMatureCovers k m shifted
  hard : ∀ m : Nat, threshold ≤ m → HardTarget hub m → ShiftedMatureCovers k m shifted
  smallOutside : ∀ m : Nat, threshold ≤ m → HasSmallOutsideFactor k hub m →
      ShiftedMatureCovers k m shifted
  outsideLarge_isPrime : ∀ m : Nat, threshold ≤ m → ¬ SmoothFor hub m →
      ¬ HasSmallOutsideFactor k hub m →
      IsPrime m
  primeTarget : ∀ m : Nat, threshold ≤ m → IsPrime m → ShiftedMatureCovers k m shifted

theorem CompletionData.shiftedCoversTail {k : Nat} (D : CompletionData k) :
    ShiftedCoversTail k D.shifted := by
  refine ⟨D.threshold, ?_⟩
  intro m hm
  by_cases hsmooth : SmoothFor D.hub m
  · by_cases hhub : D.hub.1 ∣ m
    · exact D.hard m hm ⟨hsmooth, hhub⟩
    · exact D.smooth_noHub m hm hsmooth hhub
  · by_cases houtside : HasSmallOutsideFactor k D.hub m
    · exact D.smallOutside m hm houtside
    · exact D.primeTarget m hm
        (D.outsideLarge_isPrime m hm hsmooth houtside)

theorem P_of_completionData {k : Nat} (D : CompletionData k) : P k :=
  P_of_shiftedCoversTail D.shiftedCoversTail

end Erdos279
end

section

namespace Erdos279

theorem Prime.one_lt (p : Prime) : 1 < p.1 := Nat.lt_of_lt_of_le Nat.one_lt_two p.two_le

inductive ControllerSemigroup (h : Prime) : Nat → Prop
  | one : ControllerSemigroup h 1
  | mul (p : Prime) {u : Nat} :
      InControllerProgression h p →
      ControllerSemigroup h u →
      ControllerSemigroup h (p.1 * u)

theorem ControllerSemigroup.mod_h_eq_one {h : Prime} {u : Nat} (hu : ControllerSemigroup h u) :
    u % h.1 = 1 := by
  induction hu with
  | one =>
      exact Nat.mod_eq_of_lt h.one_lt
  | mul p hp hu ih =>
      rw [Nat.mul_mod, hp, ih]
      simp [Nat.mod_eq_of_lt h.one_lt]

theorem controllerSemigroup_covered_by_hub {k u : Nat} {h : Prime} {a : ShiftedAssignment}
    (hu : ControllerSemigroup h u)
    (ha : (a h : Nat) = 1)
    (hmature : k * h.1 ≤ u + 1) :
    ShiftedMatureCovers k u a := by
  refine ⟨h, hmature, ?_⟩
  rw [hu.mod_h_eq_one, ha]

def HasHardForm (h : Prime) (m : Nat) : Prop := ∃ e u : Nat, 1 ≤ e ∧ ControllerSemigroup h u ∧
    m = h.1 ^ e * u

end Erdos279
end

section

namespace Erdos279

def controllerResidue (p : Prime) (m : Nat) : Fin p.1 := ⟨m % p.1, Nat.mod_lt m p.pos⟩

theorem controllerResidue_ne_zero {h p : Prime} {m : Nat} (hpLower : m / h.1 < p.1)
    (hcofactor : p.1 ∣ m → h.1 ≤ m / p.1) :
    (controllerResidue p m : Nat) ≠ 0 := by
  intro hzero
  change m % p.1 = 0 at hzero
  have hpdiv : p.1 ∣ m := Nat.dvd_of_mod_eq_zero hzero
  have hq : h.1 ≤ m / p.1 := hcofactor hpdiv
  have heq : p.1 * (m / p.1) = m := by
    have := Nat.mod_add_div m p.1
    simpa [hzero] using this
  have hle : p.1 * h.1 ≤ m := by
    rw [← heq]
    exact Nat.mul_le_mul_left p.1 hq
  have hlt : m < p.1 * h.1 := (Nat.div_lt_iff_lt_mul h.pos).mp hpLower
  exact Nat.not_lt_of_ge hle hlt

theorem controller_mature_from_annulus {k X m : Nat} {p : Prime} (hk : 0 < k)
    (hpUpper : p.1 ≤ X / k)
    (hXm : X < m) :
    k * p.1 ≤ m + 1 := by
  have hpkX : p.1 * k ≤ X := (Nat.le_div_iff_mul_le hk).mp hpUpper
  have hkpX : k * p.1 ≤ X := by
    simpa [Nat.mul_comm] using hpkX
  exact Nat.le_trans hkpX
    (Nat.le_trans (Nat.le_of_lt hXm) (Nat.le_add_right m 1))

theorem controller_pair_covers {k m : Nat} {p : Prime} {a : ShiftedAssignment}
    (hmature : k * p.1 ≤ m + 1)
    (ha : (a p : Nat) = (controllerResidue p m : Nat)) :
    ShiftedMatureCovers k m a := by
  refine ⟨p, hmature, ?_⟩
  exact ha.symm

end Erdos279
end

section

namespace Erdos279

theorem isPrime_coprime_of_not_dvd {p n : Nat} (hp : IsPrime p) (hpn : ¬ p ∣ n) :
    Nat.Coprime p n := by
  rw [Nat.coprime_iff_gcd_eq_one]
  rcases hp.2 (Nat.gcd p n) (Nat.gcd_dvd_left p n) with hgcd | hgcd
  · exact hgcd
  · exfalso
    apply hpn
    rw [← hgcd]
    exact Nat.gcd_dvd_right p n

theorem isPrime_dvd_mul {p a b : Nat} (hp : IsPrime p) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · exact Or.inr ((isPrime_coprime_of_not_dvd hp hpa).dvd_of_dvd_mul_left hab)

theorem isPrime_dvd_pow {p a e : Nat} (hp : IsPrime p) (hpow : p ∣ a ^ e) : p ∣ a := by
  induction e with
  | zero =>
      have hpone : p = 1 := Nat.dvd_one.mp (by simpa using hpow)
      have hp2 : 2 ≤ p := hp.1
      omega
  | succ e ih =>
      rw [Nat.pow_succ] at hpow
      rcases isPrime_dvd_mul hp hpow with hrest | hbase
      · exact ih hrest
      · exact hbase

theorem exists_isPrime_dvd {n : Nat} (hn : 1 < n) : ∃ p : Prime, p.1 ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hp : IsPrime n
      · exact ⟨⟨n, hp⟩, Nat.dvd_refl n⟩
      · have hn2 : 2 ≤ n := hn
        have hproper : ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
          apply Classical.byContradiction
          intro hnone
          apply hp
          refine ⟨hn2, ?_⟩
          intro d hd
          by_cases hd1 : d = 1
          · exact Or.inl hd1
          · by_cases hdn : d = n
            · exact Or.inr hdn
            · exfalso
              apply hnone
              exact ⟨d, hd, hd1, hdn⟩
        rcases hproper with ⟨d, hdn, hd1, hdne⟩
        have hnpos : 0 < n := by omega
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
        have hdlt : d < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd hnpos hdn) hdne
        have hdgt : 1 < d := by omega
        rcases ih d hdlt hdgt with ⟨q, hqd⟩
        exact ⟨q, Nat.dvd_trans hqd hdn⟩

theorem inControllerProgression_ne_hub {h p : Prime} (hp : InControllerProgression h p) :
    p ≠ h := by
  intro hph
  subst p
  simp [InControllerProgression] at hp

theorem hub_lt_of_inControllerProgression {h p : Prime} (hp : InControllerProgression h p) :
    h.1 < p.1 := by
  have hpne : p ≠ h := inControllerProgression_ne_hub hp
  have hnotlt : ¬ p.1 < h.1 := by
    intro hplt
    have hpone : p.1 = 1 := by
      have := hp
      rw [InControllerProgression, Nat.mod_eq_of_lt hplt] at this
      exact this
    have hp2 := p.two_le
    omega
  have hle : h.1 ≤ p.1 := Nat.le_of_not_gt hnotlt
  have hvalne : p.1 ≠ h.1 := by
    intro heq
    apply hpne
    exact Subtype.ext heq
  exact Nat.lt_of_le_of_ne hle (Ne.symm hvalne)

theorem ControllerSemigroup.pos {h : Prime} {u : Nat} (hu : ControllerSemigroup h u) : 0 < u := by
  induction hu with
  | one => omega
  | mul p hp hu ih =>
      exact Nat.mul_pos p.pos ih

theorem prime_dvd_prime_eq {p q : Prime} (hpq : p.1 ∣ q.1) : p = q := by
  rcases q.2.2 p.1 hpq with hpone | hpqeq
  · have hp2 := p.two_le
    omega
  · exact Subtype.ext hpqeq

theorem prime_mod_prime_ne_zero_of_lt {p q : Prime} (hpq : p.1 < q.1) : q.1 % p.1 ≠ 0 := by
  intro hzero
  have hpdivq : p.1 ∣ q.1 := Nat.dvd_of_mod_eq_zero hzero
  have hpEq : p = q := prime_dvd_prime_eq hpdivq
  subst q
  exact Nat.lt_irrefl p.1 hpq

theorem hasHardForm_controller_cofactor_ge_hub {h p : Prime} {m : Nat} (hm : HasHardForm h m)
    (hpG : InControllerProgression h p)
    (hpm : p.1 ∣ m) :
    h.1 ≤ m / p.1 := by
  rcases hm with ⟨e, u, he, hu, rfl⟩
  have hpne : p ≠ h := inControllerProgression_ne_hub hpG
  have hpnotdivh : ¬ p.1 ∣ h.1 := by
    intro hph
    exact hpne (prime_dvd_prime_eq hph)
  have hpnotpow : ¬ p.1 ∣ h.1 ^ e := by
    intro hppow
    exact hpnotdivh (isPrime_dvd_pow p.2 hppow)
  have hpu : p.1 ∣ u := by
    rcases isPrime_dvd_mul p.2 hpm with hppow | hpu
    · exact False.elim (hpnotpow hppow)
    · exact hpu
  have hupos : 0 < u := hu.pos
  have hp_le_u : p.1 ≤ u := Nat.le_of_dvd hupos hpu
  have hquotpos : 0 < u / p.1 := Nat.div_pos hp_le_u p.pos
  have hhubpow : h.1 ≤ h.1 ^ e := Nat.le_pow (by omega)
  calc
    h.1 ≤ h.1 ^ e := hhubpow
    _ ≤ h.1 ^ e * (u / p.1) := Nat.le_mul_of_pos_right (h.1 ^ e) hquotpos
    _ = (h.1 ^ e * u) / p.1 := (Nat.mul_div_assoc (h.1 ^ e) hpu).symm

theorem outsideLarge_isPrime {k m : Nat} {h : Prime} (hk : 3 ≤ k) (hkh : k < h.1)
    (hlarge : k * k < m)
    (hnonsmooth : ¬ SmoothFor h m)
    (hnosmall : ¬ HasSmallOutsideFactor k h m) :
    IsPrime m := by
  have houtside : ∃ q : Prime,
        q.1 ∣ m ∧ q ≠ h ∧ ¬ InControllerProgression h q := by
    apply Classical.byContradiction
    intro hnone
    apply hnonsmooth
    intro q hqm
    by_cases hqh : q = h
    · exact Or.inl hqh
    · right
      apply Classical.byContradiction
      intro hqG
      apply hnone
      exact ⟨q, hqm, hqh, hqG⟩
  rcases houtside with ⟨q, hqm, hqne, hqout⟩
  have hmpos : 0 < m := by omega
  have hqle : q.1 ≤ m := Nat.le_of_dvd hmpos hqm
  let c : Nat := m / q.1
  have hcpos : 0 < c := Nat.div_pos hqle q.pos
  have hmc : m = q.1 * c := by
    exact (Nat.mul_div_cancel' hqm).symm
  have hnotmature : ¬ k * q.1 ≤ m := by
    intro hkq
    apply hnosmall
    exact ⟨q, hqm, hqne, hqout, hkq⟩
  have hmlt : m < k * q.1 := Nat.lt_of_not_ge hnotmature
  have hclt : c < k := by
    apply (Nat.mul_lt_mul_left q.pos).mp
    simpa [hmc, Nat.mul_comm] using hmlt
  have hkltq : k < q.1 := by
    apply Classical.byContradiction
    intro hnlt
    have hqk : q.1 ≤ k := Nat.le_of_not_gt hnlt
    have hmkk : m < k * k := by
      rw [hmc]
      exact Nat.mul_lt_mul_of_le_of_lt hqk hclt (by omega)
    exact (Nat.not_lt_of_ge (Nat.le_of_lt hlarge)) hmkk
  have hc1 : c = 1 := by
    apply Classical.byContradiction
    intro hcne
    have hcgt : 1 < c := by omega
    rcases exists_isPrime_dvd hcgt with ⟨r, hrc⟩
    have hrle : r.1 ≤ c := Nat.le_of_dvd hcpos hrc
    have hrltk : r.1 < k := Nat.lt_of_le_of_lt hrle hclt
    have hrneh : r ≠ h := by
      intro hrh
      have : h.1 < h.1 := by
        simpa [hrh] using Nat.lt_trans hrltk hkh
      exact Nat.lt_irrefl _ this
    have hrout : ¬ InControllerProgression h r := by
      intro hrG
      have hhlt := hub_lt_of_inControllerProgression hrG
      exact (Nat.not_lt_of_ge (Nat.le_of_lt (Nat.lt_trans hrltk hkh))) hhlt
    have hcm : c ∣ m := by
      rw [hmc]
      exact Nat.dvd_mul_left c q.1
    have hrm : r.1 ∣ m := Nat.dvd_trans hrc hcm
    have hkrm : k * r.1 ≤ m := by
      rw [hmc]
      exact Nat.mul_le_mul (Nat.le_of_lt hkltq) hrle
    apply hnosmall
    exact ⟨r, hrm, hrneh, hrout, hkrm⟩
  have hmq : m = q.1 := by
    simpa [hc1] using hmc
  rw [hmq]
  exact q.2

theorem hardForm_controllerResidue_ne_zero {h p : Prime} {m : Nat} (hm : HasHardForm h m)
    (hpG : InControllerProgression h p)
    (hpLower : m / h.1 < p.1) :
    (controllerResidue p m : Nat) ≠ 0 :=
  controllerResidue_ne_zero hpLower
    (fun hpm => hasHardForm_controller_cofactor_ge_hub hm hpG hpm)

end Erdos279
end

section

namespace Erdos279

theorem smoothFor_controllerSemigroup_of_not_dvd {h : Prime} {m : Nat} (hsmooth : SmoothFor h m)
    (hnotHub : ¬ h.1 ∣ m) :
    ControllerSemigroup h m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      have hmpos : 0 < m := by
        apply Nat.pos_of_ne_zero
        intro hmzero
        apply hnotHub
        rw [hmzero]
        exact Nat.dvd_zero h.1
      by_cases hmone : m = 1
      · simpa [hmone] using ControllerSemigroup.one (h := h)
      · have hmgt : 1 < m := by omega
        rcases exists_isPrime_dvd hmgt with ⟨q, hqm⟩
        have hqG : InControllerProgression h q := by
          rcases hsmooth q hqm with hqh | hqG
          · exfalso
            apply hnotHub
            simpa [hqh] using hqm
          · exact hqG
        let u : Nat := m / q.1
        have hqu : q.1 * u = m := by
          exact Nat.mul_div_cancel' hqm
        have hult : u < m := by
          dsimp [u]
          exact Nat.div_lt_self hmpos q.one_lt
        have hudivm : u ∣ m := by
          rw [← hqu]
          exact Nat.dvd_mul_left u q.1
        have husmooth : SmoothFor h u := by
          intro r hru
          exact hsmooth r (Nat.dvd_trans hru hudivm)
        have hunotHub : ¬ h.1 ∣ u := by
          intro hhu
          exact hnotHub (Nat.dvd_trans hhu hudivm)
        have huSemigroup : ControllerSemigroup h u := ih u hult husmooth hunotHub
        rw [← hqu]
        exact ControllerSemigroup.mul q hqG huSemigroup

theorem ControllerSemigroup.primeDivisor_mem {h q : Prime} {u : Nat} (hu : ControllerSemigroup h u)
    (hqu : q.1 ∣ u) :
    InControllerProgression h q := by
  induction hu with
  | one =>
      have hqone : q.1 = 1 := Nat.dvd_one.mp hqu
      have hq2 := q.two_le
      omega
  | mul p hp hu ih =>
      rcases isPrime_dvd_mul q.2 hqu with hqp | hqu'
      · have hEq : q = p := prime_dvd_prime_eq (p := q) (q := p) hqp
        simpa [hEq] using hp
      · exact ih hqu'

theorem HasHardForm.pos {h : Prime} {m : Nat} (hm : HasHardForm h m) : 0 < m := by
  rcases hm with ⟨e, u, _he, hu, rfl⟩
  exact Nat.mul_pos (Nat.pow_pos h.pos) hu.pos

theorem smoothFor_hasHardForm_of_dvd {h : Prime} {m : Nat} (hmpos : 0 < m) (hsmooth : SmoothFor h m)
    (hhub : h.1 ∣ m) :
    HasHardForm h m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
      let v : Nat := m / h.1
      have hhv : h.1 * v = m := by
        exact Nat.mul_div_cancel' hhub
      have hhle : h.1 ≤ m := Nat.le_of_dvd hmpos hhub
      have hvpos : 0 < v := by
        dsimp [v]
        exact Nat.div_pos hhle h.pos
      have hvlt : v < m := by
        dsimp [v]
        exact Nat.div_lt_self hmpos h.one_lt
      have hvdivm : v ∣ m := by
        rw [← hhv]
        exact Nat.dvd_mul_left v h.1
      have hvsmooth : SmoothFor h v := by
        intro q hqv
        exact hsmooth q (Nat.dvd_trans hqv hvdivm)
      by_cases hhubv : h.1 ∣ v
      · rcases ih v hvlt hvpos hvsmooth hhubv with
          ⟨e, u, he, hu, hveq⟩
        refine ⟨e + 1, u, ?_, hu, ?_⟩
        · omega
        · rw [← hhv, hveq]
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      · have hvSemigroup : ControllerSemigroup h v :=
          smoothFor_controllerSemigroup_of_not_dvd hvsmooth hhubv
        refine ⟨1, v, by omega, hvSemigroup, ?_⟩
        simpa using hhv.symm

theorem hardTarget_hasHardForm {h : Prime} {m : Nat} (hmpos : 0 < m) (hm : HardTarget h m) :
    HasHardForm h m :=
  smoothFor_hasHardForm_of_dvd hmpos hm.1 hm.2

theorem smoothFor_noHub_covered_by_hub {k m : Nat} {h : Prime} {a : ShiftedAssignment}
    (hsmooth : SmoothFor h m)
    (hnotHub : ¬ h.1 ∣ m)
    (hah : (a h : Nat) = 1)
    (hmature : k * h.1 ≤ m + 1) :
    ShiftedMatureCovers k m a :=
  controllerSemigroup_covered_by_hub
    (smoothFor_controllerSemigroup_of_not_dvd hsmooth hnotHub)
    hah hmature

end Erdos279
end

section

namespace Erdos279

open Finset

namespace ControllerSemigroup

theorem coprime_hub {h : Prime} {u : Nat} (hu : ControllerSemigroup h u) : u.Coprime h.1 := by
  rw [Nat.coprime_comm, h.natPrime.coprime_iff_not_dvd]
  intro hdiv
  have hzero : u % h.1 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hone : u % h.1 = 1 := hu.mod_h_eq_one
  omega

end ControllerSemigroup

def natIoc (Y Z : Nat) : Finset Nat := Finset.Ioc Y Z

structure OldPrimeClasses (h : Prime) (z : Nat) where
  residue : (p : Prime) → Fin p.1
  nonzero : ∀ p : Prime, InControllerProgression h p → p.1 ≤ z → (residue p : Nat) ≠ 0

def AvoidsOldClasses {h : Prime} {z : Nat} (a : OldPrimeClasses h z) (m : Nat) : Prop :=
  ∀ p : Prime,
    InControllerProgression h p →
    p.1 ≤ z →
    m % p.1 ≠ (a.residue p : Nat)

noncomputable def hardSurvivors (h : Prime) (z : Nat) (a : OldPrimeClasses h z)
    (X Z : Nat) : Finset Nat := by
  classical
  exact (natIoc X Z).filter fun m => HasHardForm h m ∧ AvoidsOldClasses a m

@[simp]
theorem mem_hardSurvivors {h : Prime} {z : Nat} {a : OldPrimeClasses h z} {X Z m : Nat} :
    m ∈ hardSurvivors h z a X Z ↔ X < m ∧ m ≤ Z ∧ HasHardForm h m ∧ AvoidsOldClasses a m := by
  classical
  simp [hardSurvivors, natIoc, and_assoc]

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

end Erdos279
end

section

namespace Erdos279

theorem hubPower_coprime_controllerPrime {h p : Prime} (e : Nat)
    (hp : InControllerProgression h p) :
    (h.1 ^ e).Coprime p.1 := by
  have hnotdvd : ¬p.1 ∣ h.1 := Nat.not_dvd_of_pos_of_lt h.pos
      (hub_lt_of_inControllerProgression hp)
  have hcop : h.1.Coprime p.1 := by
    rw [Nat.coprime_comm, p.natPrime.coprime_iff_not_dvd]
    exact hnotdvd
  exact hcop.pow_left e

noncomputable def translatedPrimeClassZMod (h p : Prime) (e : Nat) (a : Fin p.1) : ZMod p.1 :=
  ((a : Nat) : ZMod p.1) * (((h.1 ^ e : Nat) : ZMod p.1)⁻¹)

theorem hubPower_mul_translatedPrimeClassZMod {h p : Prime} (e : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p) :
    (((h.1 ^ e : Nat) : ZMod p.1) *
        translatedPrimeClassZMod h p e a) =
      ((a : Nat) : ZMod p.1) := by
  have hinv : (((h.1 ^ e : Nat) : ZMod p.1) *
          (((h.1 ^ e : Nat) : ZMod p.1)⁻¹)) = 1 :=
    ZMod.coe_mul_inv_eq_one (h.1 ^ e)
      (hubPower_coprime_controllerPrime e hp)
  calc
    ((h.1 ^ e : Nat) : ZMod p.1) *
          translatedPrimeClassZMod h p e a =
        ((a : Nat) : ZMod p.1) *
          (((h.1 ^ e : Nat) : ZMod p.1) *
            (((h.1 ^ e : Nat) : ZMod p.1)⁻¹)) := by
      simp only [translatedPrimeClassZMod]
      ac_rfl
    _ = ((a : Nat) : ZMod p.1) * 1 := by rw [hinv]
    _ = ((a : Nat) : ZMod p.1) := mul_one _

noncomputable def translatedPrimeClass (h p : Prime) (e : Nat) (a : Fin p.1) : Fin p.1 := by
  letI : NeZero p.1 := ⟨Nat.ne_of_gt p.pos⟩
  exact ⟨(translatedPrimeClassZMod h p e a).val,
      ZMod.val_lt (translatedPrimeClassZMod h p e a)⟩

theorem hubPower_mul_translatedPrimeClass_modEq {h p : Prime} (e : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p) :
    h.1 ^ e * (translatedPrimeClass h p e a : Nat) ≡
      (a : Nat) [MOD p.1] := by
  letI : NeZero p.1 := ⟨Nat.ne_of_gt p.pos⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [Nat.cast_mul]
  simp only [translatedPrimeClass]
  rw [ZMod.natCast_zmod_val]
  exact hubPower_mul_translatedPrimeClassZMod e a hp

theorem translatedPrimeClass_ne_zero {h p : Prime} (e : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p)
    (ha : (a : Nat) ≠ 0) :
    (translatedPrimeClass h p e a : Nat) ≠ 0 := by
  letI : NeZero p.1 := ⟨Nat.ne_of_gt p.pos⟩
  intro hz
  have hzval : (translatedPrimeClassZMod h p e a).val = 0 := by
    simpa [translatedPrimeClass] using hz
  have hzmod : translatedPrimeClassZMod h p e a = 0 :=
    (ZMod.val_eq_zero (translatedPrimeClassZMod h p e a)).mp hzval
  have hacast : ((a : Nat) : ZMod p.1) = 0 := by
    rw [← hubPower_mul_translatedPrimeClassZMod e a hp, hzmod, mul_zero]
  have hadiv : p.1 ∣ (a : Nat) := (ZMod.natCast_eq_zero_iff (a : Nat) p.1).mp hacast
  have ha0 : (a : Nat) = 0 := Nat.eq_zero_of_dvd_of_lt hadiv a.isLt
  exact ha ha0

theorem hubPower_mul_modEq_old_iff {h p : Prime} (e u : Nat) (a : Fin p.1)
    (hp : InControllerProgression h p) :
    h.1 ^ e * u ≡ (a : Nat) [MOD p.1] ↔ u ≡ (translatedPrimeClass h p e a : Nat) [MOD p.1] := by
  have htranslated := hubPower_mul_translatedPrimeClass_modEq e a hp
  have hgcd : Nat.gcd p.1 (h.1 ^ e) = 1 := by
    rw [Nat.gcd_comm]
    exact (hubPower_coprime_controllerPrime e hp).gcd_eq_one
  constructor
  · intro hu
    exact Nat.ModEq.cancel_left_of_coprime hgcd
      (hu.trans htranslated.symm)
  · intro hu
    exact (hu.mul_left (h.1 ^ e)).trans htranslated

noncomputable def translatedOldPrimeClasses {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) :
    OldPrimeClasses h z where
  residue p := translatedPrimeClass h p e (a.residue p)
  nonzero p hp hpz := translatedPrimeClass_ne_zero e (a.residue p) hp
      (a.nonzero p hp hpz)

theorem avoidsOldClasses_hubPower_mul_iff {h : Prime} {z e u : Nat} (a : OldPrimeClasses h z) :
    AvoidsOldClasses a (h.1 ^ e * u) ↔ AvoidsOldClasses (translatedOldPrimeClasses e a) u := by
  constructor
  · intro hav p hp hpz
    intro heq
    apply hav p hp hpz
    have heq' : u ≡ (translatedPrimeClass h p e (a.residue p) : Nat)
          [MOD p.1] := by
      change u % p.1 = (translatedPrimeClass h p e (a.residue p) : Nat) % p.1
      simpa [translatedOldPrimeClasses,
        Nat.mod_eq_of_lt
          (translatedPrimeClass h p e (a.residue p)).isLt] using heq
    have hout := (hubPower_mul_modEq_old_iff e u (a.residue p) hp).mpr heq'
    change (h.1 ^ e * u) % p.1 = (a.residue p : Nat) % p.1 at hout
    simpa [Nat.mod_eq_of_lt (a.residue p).isLt] using hout
  · intro hav p hp hpz
    intro heq
    apply hav p hp hpz
    have heq' : h.1 ^ e * u ≡ (a.residue p : Nat) [MOD p.1] := by
      change (h.1 ^ e * u) % p.1 = (a.residue p : Nat) % p.1
      simpa [Nat.mod_eq_of_lt (a.residue p).isLt] using heq
    have hout := (hubPower_mul_modEq_old_iff e u (a.residue p) hp).mp heq'
    change u % p.1 = (translatedPrimeClass h p e (a.residue p) : Nat) % p.1 at hout
    simpa [translatedOldPrimeClasses,
      Nat.mod_eq_of_lt
        (translatedPrimeClass h p e (a.residue p)).isLt] using hout

end Erdos279
end

section

namespace Erdos279

open Finset

end Erdos279
end

section

namespace Erdos279

open Finset

noncomputable def oldControllerPrimes (h : Prime) (z : Nat) : Finset Prime := by
  classical
  exact ((Finset.range (z + 1)).subtype IsPrime).filter
      (InControllerProgression h)

@[simp]
theorem mem_oldControllerPrimes {h p : Prime} {z : Nat} : p ∈ oldControllerPrimes h z ↔
      InControllerProgression h p ∧ p.1 ≤ z := by
  classical
  simp [oldControllerPrimes, Nat.lt_succ_iff, and_comm]

noncomputable def controllerElements (h : Prime) (Y Z : Nat) : Finset Nat := by
  classical
  exact (natIoc Y Z).filter (ControllerSemigroup h)

@[simp]
theorem mem_controllerElements {h : Prime} {Y Z u : Nat} : u ∈ controllerElements h Y Z ↔
      Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u := by
  classical
  simp [controllerElements, natIoc, and_assoc]

noncomputable def hardLayerUnits (h : Prime) (z e : Nat) (a : OldPrimeClasses h z)
    (Y Z : Nat) : Finset Nat := by
  classical
  exact (controllerElements h Y Z).filter fun u => AvoidsOldClasses a (h.1 ^ e * u)

end Erdos279
end

section

namespace Erdos279

open Finset

def primeSubsetModulus (d : Finset Prime) : Nat := ∏ p ∈ d, p.1

theorem primeValues_ne_zero (d : Finset Prime) : ∀ p ∈ d, p.1 ≠ 0 := by
  intro p _hp
  exact Nat.ne_of_gt p.pos

theorem primeValues_pairwise_coprime (d : Finset Prime) : Set.Pairwise (d : Set Prime)
      (fun p q : Prime => p.1.Coprime q.1) := by
  intro p _hp q _hq hpq
  exact (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval => hpq (Subtype.ext hpqval)

theorem modEq_primeSubsetModulus_iff (u b : Nat) (d : Finset Prime) :
    u ≡ b [MOD primeSubsetModulus d] ↔ ∀ p ∈ d, u ≡ b [MOD p.1] := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus, Nat.modEq_one]
  | @insert p d hpd ih =>
      have hcop : p.1.Coprime (∏ q ∈ d, q.1) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hqd
        exact (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval => hpd (by
              have hpq : p = q := Subtype.ext hpqval
              simpa [hpq] using hqd)
      rw [primeSubsetModulus, Finset.prod_insert hpd,
        ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
      change
        (u ≡ b [MOD p.1] ∧ u ≡ b [MOD primeSubsetModulus d]) ↔ ∀ q ∈ insert p d, u ≡ b [MOD q.1]
      rw [ih]
      simp [hpd]

end Erdos279
end

section

namespace Erdos279

open Finset

end Erdos279
end

section

namespace Erdos279

open Finset

theorem primeSubsetModulus_ne_zero (d : Finset Prime) : primeSubsetModulus d ≠ 0 := by
  classical
  rw [primeSubsetModulus]
  exact Finset.prod_ne_zero_iff.mpr fun p _hp => Nat.ne_of_gt p.pos

theorem primeSubsetModulus_pos (d : Finset Prime) : 0 < primeSubsetModulus d :=
  Nat.pos_of_ne_zero (primeSubsetModulus_ne_zero d)

theorem totient_primeSubsetModulus (d : Finset Prime) : Nat.totient (primeSubsetModulus d) =
      ∏ p ∈ d, (p.1 - 1) := by
  classical
  induction d using Finset.induction_on with
  | empty =>
      simp [primeSubsetModulus]
  | @insert p d hpd ih =>
      have hcop : p.1.Coprime (∏ q ∈ d, q.1) := by
        rw [Nat.coprime_prod_right_iff]
        intro q hqd
        exact (Nat.coprime_primes p.natPrime q.natPrime).mpr fun hpqval => hpd (by
              have hpq : p = q := Subtype.ext hpqval
              simpa [hpq] using hqd)
      rw [primeSubsetModulus, Finset.prod_insert hpd,
        Nat.totient_mul hcop, Nat.totient_prime p.natPrime,
        Finset.prod_insert hpd]
      simpa [primeSubsetModulus] using congrArg (fun n => (p.1 - 1) * n) ih

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

end Erdos279
end

section

namespace Erdos279

open Finset
open scoped ArithmeticFunction.Moebius

end Erdos279
end

section

namespace Erdos279

noncomputable def controllerDensity (h : Prime) : Real := 1 / ((h.1 : Real) - 1)

theorem controllerDensity_pos (h : Prime) : 0 < controllerDensity h := by
  rw [controllerDensity]
  apply one_div_pos.mpr
  exact sub_pos.mpr (by exact_mod_cast h.one_lt)

end Erdos279
end

section

namespace Erdos279

open Finset

noncomputable def allPrimesUpTo (z : Nat) : Finset Prime := by
  classical
  exact (Finset.range (z + 1)).subtype IsPrime

@[simp]
theorem mem_allPrimesUpTo {p : Prime} {z : Nat} : p ∈ allPrimesUpTo z ↔ p.1 ≤ z := by
  classical
  simp [allPrimesUpTo, Nat.lt_succ_iff]

end Erdos279
end

section

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace ArithmeticFunction.IsMultiplicative

variable {R : Type*}

end ArithmeticFunction.IsMultiplicative

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm

theorem inv_sub_antitoneOn_gt
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (c : R) :
    AntitoneOn (fun x:R ↦ (x-c)⁻¹) (Set.Ioi c) := by
  refine antitoneOn_iff_forall_lt.mpr ?_
  intro a ha b hb hab
  rw [Set.mem_Ioi] at ha hb
  gcongr

theorem inv_sub_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c : R) (ha : c < a) :
    AntitoneOn (fun x ↦ (x-c)⁻¹) (Set.Icc a b) := by
  by_cases hab : a ≤ b
  · exact inv_sub_antitoneOn_gt c |>.mono <| (Set.Icc_subset_Ioi_iff hab).mpr ha
  · simp [hab, Set.Subsingleton.antitoneOn]

theorem inv_antitoneOn_Icc {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (ha : 0 < a) :
    AntitoneOn (fun x ↦ x⁻¹) (Set.Icc a b) := by
  convert inv_sub_antitoneOn_Icc a b 0 ha; ring

theorem log_add_one_le_sum_inv (n : ℕ) : Real.log ↑(n+1) ≤ ∑ d ∈ Finset.Icc 1 n, (d:ℝ)⁻¹ := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ _ := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc
    norm_num

theorem log_le_sum_inv (y : ℝ) (hy : 1 ≤ y) : Real.log y ≤ ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ := by
  calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
       _ ≤ _ := ?_
  · gcongr
    apply (le_ceil y).trans
    norm_cast
    exact ceil_le_floor_add_one y
  · apply log_add_one_le_sum_inv

theorem sum_inv_le_log (n : ℕ) (hn : 1 ≤ n) : ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ ≤ 1 + Real.log ↑n :=
  by
  rw [← Finset.sum_erase_add (Icc 1 n) _ (by simp [hn] : 1 ∈ Icc 1 n), add_comm]
  gcongr
  · norm_num
  simp only [Icc_erase_left]
  calc
    ∑ d ∈ Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d ∈ Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply inv_sub_antitoneOn_Icc; norm_num
  rw [intervalIntegral.integral_comp_sub_right _ 1, integral_inv]
  · norm_num
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem sum_inv_le_log_real (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 (⌊y⌋₊), (d:ℝ)⁻¹ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply sum_inv_le_log (⌊y⌋₊)
    apply le_floor; norm_cast
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply le_floor; norm_cast
  · apply floor_le; linarith

theorem sum_pow_cardDistinctFactors_div_self_le_log_pow {P k : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if d ≤ x then (k:ℝ) ^ (ω d) / (d : ℝ) else (0 : ℝ))
    ≤ (1 + Real.log x) ^ k := by
  have hx_pos : 0 < x := by
    linarith
  calc
    _ = ∑ d ∈ P.divisors,
          ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
            if ∏ i, a i = d ∧ d ∣ P then if ↑d ≤ x then (d : ℝ)⁻¹ else 0 else 0 := ?_
    _ = ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ∏ i, a i ∣ P then if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          if ↑(∏ i, a i) ≤ x then ∏ i, (a i : ℝ)⁻¹ else 0 := ?_
    _ ≤ ∑ a ∈ Fintype.piFinset fun _i : Fin k => P.divisors,
          ∏ i, if ↑(a i) ≤ x then (a i : ℝ)⁻¹ else 0 := ?_
    _ = ∏ _i : Fin k, ∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0 := by rw [prod_univ_sum]
    _ = (∑ d ∈ P.divisors, if ↑d ≤ x then (d : ℝ)⁻¹ else 0) ^ k := by
      rw [prod_const, Finset.card_fin]
    _ ≤ (1 + Real.log x) ^ k := ?_

  · apply sum_congr rfl; intro d hd
    rw [mem_divisors] at hd
    simp_rw [ite_and];
    rw [← sum_filter, Finset.sum_const, ← finMulAntidiag_eq_piFinset_divisors_filter hd.1 hd.2,
      card_finMulAntidiag_of_squarefree <| hP.squarefree_of_dvd hd.1, if_pos hd.1]
    simp only [div_eq_mul_inv, nsmul_eq_mul, cast_pow, mul_ite, mul_zero]
  · rw [sum_comm]; apply sum_congr rfl; intro a _; rw [sum_eq_single (∏ i, a i)]
    · apply if_ctx_congr _ _ (fun _ => rfl)
      · rw [Iff.comm, iff_and_self]; exact fun _ => rfl
      · intro; rw [cast_prod, ← prod_inv_distrib]
    · exact fun d _ hd_ne ↦ if_neg fun h => hd_ne.symm h.1
    · exact fun h ↦ if_neg fun h' => h (mem_divisors.mpr ⟨h'.2, hP.ne_zero⟩)
  · apply sum_le_sum; intro a _
    by_cases h : (∏ i, a i ∣ P)
    · rw [if_pos h]
    rw [if_neg h]
    split_ifs with h'
    · apply prod_nonneg; intro i _; norm_num
    · rfl
  · apply sum_le_sum; intro a ha
    split_ifs with h
    · gcongr with i hi
      rw [if_pos]
      apply le_trans _ h
      norm_cast
      rw [←prod_erase_mul (a:=i) (h:= hi)]
      apply Nat.le_mul_of_pos_left
      rw [Fintype.mem_piFinset] at ha
      apply prod_pos; intro j _; apply pos_of_mem_divisors (ha j)
    · apply prod_nonneg; intro j _
      split_ifs
      · norm_num
      · rfl
  · rw [←sum_filter]
    gcongr
    trans (∑ d ∈ Icc 1 (floor x), (d:ℝ)⁻¹)
    · apply sum_le_sum_of_subset_of_nonneg
      · intro d; rw[mem_filter, mem_Icc]
        intro hd
        constructor
        · rw [Nat.succ_le_iff]; exact pos_of_mem_divisors hd.1
        · rw [le_floor_iff hx_pos.le]
          exact hd.2
      · norm_num
    apply sum_inv_le_log_real
    linarith

theorem sum_pow_cardDistinctFactors_le_self_mul_log_pow {P h : ℕ} (x : ℝ) (hx : 1 ≤ x)
    (hP : Squarefree P) :
    (∑ d ∈ P.divisors, if ↑d ≤ x then (h : ℝ) ^ ω d else (0 : ℝ)) ≤ x * (1 + Real.log x) ^ h := by
  trans (∑ d ∈ P.divisors, x * if ↑d ≤ x then (h : ℝ) ^ ω d / d else (0 : ℝ))
  · simp_rw [mul_ite, mul_zero, ←sum_filter]
    gcongr with i hi
    rw [div_eq_mul_inv, mul_comm _ (i:ℝ)⁻¹, ←mul_assoc]
    trans (1*(h:ℝ)^ω i)
    · rw [one_mul]
    gcongr
    rw [mem_filter] at hi
    rw [←div_eq_mul_inv]
    apply one_le_div (by norm_cast; apply Nat.pos_of_mem_divisors hi.1) |>.mpr hi.2
  rw [←mul_sum];
  gcongr
  apply sum_pow_cardDistinctFactors_div_self_le_log_pow x hx hP

end Aux
end

section

noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)

/- Use the Mathlib Selberg identities in the sieve construction. -/
abbrev selbergTerms : ArithmeticFunction ℝ := BoundingSieve.selbergTerms (s := s)

theorem selbergTerms_apply (d : ℕ) :
    selbergTerms s d = s.nu d * ∏ p ∈ d.primeFactors, 1 / (1 - s.nu p) := by
  simpa only [one_div] using BoundingSieve.selbergTerms_apply (s := s) d

section UpperBoundSieve

structure UpperBoundSieve where mk ::
  μPlus : ℕ → ℝ
  hμPlus : IsUpperMoebius μPlus

instance ubToμPlus : CoeFun UpperBoundSieve fun _ => ℕ → ℝ where coe ub := ub.μPlus

end UpperBoundSieve

section SieveLemmas

theorem selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < selbergTerms s l :=
  BoundingSieve.selbergTerms_pos hl

theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative (selbergTerms s) :=
  BoundingSieve.selbergTerms_isMultiplicative

theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then selbergTerms s l else 0) =
      selbergTerms s d * (s.nu d)⁻¹ :=
  BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd

theorem siftedSum_le_mainSum_errSum_of_UpperBoundSieve (μPlus : UpperBoundSieve) :
    siftedSum (s := s) ≤ s.totalMass * mainSum (s := s) μPlus + errSum (s := s) μPlus := by
  apply siftedSum_le_mainSum_errSum_of_upperMoebius _ μPlus.hμPlus

end SieveLemmas

section LambdaSquared

abbrev lambdaSquared := BoundingSieve.lambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared, BoundingSieve.lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push_neg at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem upperMoebius_of_lambda_sq (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius (lambdaSquared weights) :=
  BoundingSieve.upperMoebius_lambdaSquared weights hw

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) : mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes, 1 / selbergTerms s l *
        (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 := by
  simpa only [one_div] using BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (s := s) w

end LambdaSquared

end SelbergSieve
end

section

noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat SelbergSieve.UpperBoundSieve ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.toBoundingSieve.prodPrimes, if l ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) l else 0

theorem selbergBoundingSum_pos : 0 < (selbergBoundingSum s) := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : (selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ (selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d => if d ∣ s.toBoundingSieve.prodPrimes then
    (s.toBoundingSieve.nu d)⁻¹ * (selbergTerms s.toBoundingSieve) d * μ d * (selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.toBoundingSieve.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (selbergTerms s.toBoundingSieve) m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.toBoundingSieve.prodPrimes) :
    (selbergWeights s) d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ s.level) : (selbergWeights s) d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.toBoundingSieve.prodPrimes) :
    0 ≤ (selbergWeights s) d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.toBoundingSieve.nu d)⁻¹ * (selbergTerms s.toBoundingSieve) d * (selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors s.toBoundingSieve.prodPrimes,
          if (d * m) ^ 2 ≤ s.level ∧ Coprime m d then (selbergTerms s.toBoundingSieve) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

theorem selbergWeights_eq_dvds_sum (d : ℕ) : s.toBoundingSieve.nu d * (selbergWeights s) d =
      (selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.toBoundingSieve.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) l else 0 := by
  by_cases h_dvd : d ∣ s.toBoundingSieve.prodPrimes
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push_neg; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]

  apply symm
  rw [sum_mul_subst d s.toBoundingSieve.prodPrimes]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.toBoundingSieve.nu d)⁻¹ * (s.toBoundingSieve.nu d) * (selbergTerms s.toBoundingSieve) d * μ d / (selbergBoundingSum s) * (selbergTerms s.toBoundingSieve) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push_neg; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.toBoundingSieve.prodPrimes) :
    (∑ d ∈ divisors s.toBoundingSieve.prodPrimes, if l ∣ d then s.toBoundingSieve.nu d * (selbergWeights s) d else 0) =
      if l ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) l * μ l * (selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.toBoundingSieve.prodPrimes, if l ∣ d then s.toBoundingSieve.nu d * (selbergWeights s) d else 0) =
        ∑ d ∈ divisors s.toBoundingSieve.prodPrimes, ∑ k ∈ divisors s.toBoundingSieve.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) k * (selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.toBoundingSieve.prodPrimes, if k ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.toBoundingSieve.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (selbergTerms s.toBoundingSieve) k * (selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) l * μ l * (selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.toBoundingSieve.prodPrimes) l (fun _ => if l^2 ≤ s.level then (selbergTerms s.toBoundingSieve) l * μ l * (selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ := lambdaSquared (selbergWeights s)

theorem weight_one_of_selberg : (selbergWeights s) 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd s.toBoundingSieve.prodPrimes), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  exact s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ s.level) : (selbergMuPlus s) d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ s.level _ d hd
  apply s.selbergWeights_eq_zero

def selbergUbSieve : UpperBoundSieve :=
  ⟨(selbergMuPlus s), upperMoebius_of_lambda_sq (selbergWeights s) (s.weight_one_of_selberg)⟩

theorem mainSum_eq_diag_quad_form : mainSum (s := s.toBoundingSieve) (selbergMuPlus s) =
      ∑ l ∈ divisors s.toBoundingSieve.prodPrimes,
        1 / (selbergTerms s.toBoundingSieve) l *
          (∑ d ∈ divisors s.toBoundingSieve.prodPrimes, if l ∣ d then s.toBoundingSieve.nu d * (selbergWeights s) d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (selbergMuPlus s) = (selbergBoundingSum s)⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.toBoundingSieve.prodPrimes, (if l ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) l * ((selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(selbergTerms s.toBoundingSieve) l * (selbergTerms s.toBoundingSieve) l * (selbergTerms s.toBoundingSieve) l * (μ l:ℝ)^2  * ((selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

lemma eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private lemma _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.toBoundingSieve.prodPrimes) (hm : m ∈ divisors s.toBoundingSieve.prodPrimes) :
    k * m ∣ s.toBoundingSieve.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ s.level ↔
    (k * m) ^ 2 ≤ s.level ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.toBoundingSieve.prodPrimes) :
    (selbergBoundingSum s) ≥ (selbergWeights s) d * ↑(μ d) * (selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors s.toBoundingSieve.prodPrimes, ∑ l ∈ divisors s.toBoundingSieve.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ s.level then (selbergTerms s.toBoundingSieve) l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.toBoundingSieve.prodPrimes,
          if k ∣ d then
            (selbergTerms s.toBoundingSieve) k * ∑ m ∈ divisors s.toBoundingSieve.prodPrimes, if (k * m) ^ 2 ≤ s.level ∧ m.Coprime d then (selbergTerms s.toBoundingSieve) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push_neg; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k s.toBoundingSieve.prodPrimes, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push_neg; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.toBoundingSieve.prodPrimes, if k ∣ d
          then (selbergTerms s.toBoundingSieve) k * ∑ m ∈ divisors s.toBoundingSieve.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (selbergTerms s.toBoundingSieve) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((selbergBoundingSum s) * (selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * (s.toBoundingSieve.nu d)⁻¹ * (selbergTerms s.toBoundingSieve) d * (∑ m ∈ divisors s.toBoundingSieve.prodPrimes, if (d*m) ^ 2 ≤ s.level ∧
      Coprime m d then (selbergTerms s.toBoundingSieve) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |(selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ s.toBoundingSieve.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(selbergBoundingSum s) ≥ (selbergWeights s) d * ↑(μ d) * (selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.toBoundingSieve.prodPrimes) :
    |(selbergMuPlus s) n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared, BoundingSieve.lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (selbergWeights s) d1 * (selbergWeights s) d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (selbergWeights s) d1 * (selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then (selbergWeights s) d1 * (selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| (selbergWeights s) d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num

theorem selberg_bound_simple_errSum : errSum (s := s.toBoundingSieve) (selbergMuPlus s) ≤
      ∑ d ∈ divisors s.toBoundingSieve.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.toBoundingSieve.rem d| else 0 := by
  dsimp only [errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul _ le_rfl (abs_nonneg <| s.toBoundingSieve.rem d) (pow_nonneg _ <| ω d)
    · apply s.selberg_bound_muPlus d hd
    · norm_num
  · rw [s.selbergμPlus_eq_zero d h, abs_zero, zero_mul]

theorem selberg_bound_simple : siftedSum (s := s.toBoundingSieve) ≤
      s.toBoundingSieve.totalMass / (selbergBoundingSum s) +
        ∑ d ∈ divisors s.toBoundingSieve.prodPrimes, if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |s.toBoundingSieve.rem d| else 0 := by
  let μPlus := s.selbergUbSieve
  calc
    siftedSum ≤ s.toBoundingSieve.totalMass * mainSum μPlus + errSum μPlus :=
      siftedSum_le_mainSum_errSum_of_UpperBoundSieve _ μPlus
    _ ≤ _ := ?_
  gcongr
  · erw [s.selberg_bound_simple_mainSum, div_eq_mul_inv]
  · apply s.selberg_bound_simple_errSum

end SelbergSieve
end

section

open scoped Nat ArithmeticFunction BigOperators Classical ArithmeticFunction.zeta
  ArithmeticFunction.omega
open BoundingSieve SelbergSieve

noncomputable section
namespace Sieve

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [←Finset.mul_prod_erase (a:=p) (h := hps), mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)]
      at h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| symm <| (Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := hp.prime.exists_mem_finset_dvd this
    have heq : p = q := by
      rw [←Nat.prime_dvd_prime_iff_eq hp (h q hq.1)]
      exact hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter];
  exact fun _ h => h.2

theorem zeta_pos_of_prime : ∀ (p : ℕ), Nat.Prime p → (0:ℝ) < (↑ζ:ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime : ∀ (p : ℕ), Nat.Prime p → (↑ζ:ArithmeticFunction ℝ) p < (p:ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num;
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) : p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    obtain ⟨q, hq⟩ : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      hp.prime.exists_mem_finset_dvd h
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a*b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  simp_rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, one_ne_zero, ite_false,
    mul_eq_zero, Nat.cast_ite, Nat.cast_one, CharP.cast_eq_zero, mul_ite, mul_zero, mul_one,
    true_and, ← ite_or, or_comm, implies_true]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
    constructor <;> simp

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simp_rw [pow_zero, hf.1]
  | succ n' ih => simp_rw [pow_succ, hf.2, ih]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ) (hd : Squarefree d)
    (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n) := by
  calc f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    = ∏ p ∈ d.primeFactors, f p / (1 - f p)                 := by
        conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
        rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
          ←Finset.prod_mul_distrib]
        simp_rw[one_div, div_eq_mul_inv]
  _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p)^n  := by
    gcongr with p hp
    · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
    rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
    rw [← Finset.Ico_add_one_right_eq_Icc, geom_sum_Ico,
      ← mul_div_mul_left (c := (-1 : ℝ)) (f p ^ (M + 1) - f p ^ 1)]
    · gcongr
      · apply hf_nonneg
      · linarith [hf_size p hp.1 hp.2]
      · rw [pow_one]
        have : 0 ≤ f p ^ (M + 1) := by
          apply pow_nonneg
          apply hf_nonneg
        linarith only [this]
      · linarith only
    · norm_num
    · apply ne_of_lt <| hf_size p hp.1 hp.2
    · apply Nat.succ_le_iff.mpr (Nat.succ_pos _)

  _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)  := by
     simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (d : ℕ) (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p^n)
    = ∑ m ∈ (d^M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a:_) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p , Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
        Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]; right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq, ← exists_eq_subtype_mk_iff]
        · push_neg
          exact fun _ => hq
        · exact Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp q.2
        · exact (Nat.prime_of_mem_primeFactorsList <| List.mem_toFinset.mp hp).ne_one
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
          (List.mem_toFinset.mp q.2)))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      refine ⟨?_, hd.ne_zero⟩
      trans q
      · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
      · apply Nat.dvd_of_mem_primeFactorsList <| List.mem_toFinset.mp hq

  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactorsList
      (List.mem_toFinset.mp p.property)))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d^M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors, ←Nat.factorization_le_iff_dvd hd.ne_zero
      (hi_ne_zero a ha),← Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1

  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp x.2)
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp <| Nat.prime_of_mem_primeFactorsList
      (List.mem_toFinset.mp y.2)]
    exact fun hc => hxy (Subtype.ext hc)

  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp

  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => b.factorization p) ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]; intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push_neg at hp
      by_cases hpp : p.Prime
      · right; intro h
        apply absurd (hp hpp)
        push_neg
        exact ⟨hpp.dvd_of_dvd_pow (h.trans hb.1.1), hd.ne_zero⟩
      · left; exact hpp

  exact Finset.sum_bij i hi i_inj i_surj h

theorem prod_primes_dvd_of_dvd (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  refine le_self_pow₀ hx ?right.h
  norm_num

lemma Nat.squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) : a ∣ b := by
  by_cases hN : N=0
  · rw [hN, pow_zero, Nat.dvd_one] at hab
    rw [hab]; simp
  rw [Squarefree.dvd_pow_iff_dvd ha hN] at hab
  exact hab

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve) (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)
  (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n) (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1):
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m := by
  unfold selbergBoundingSum
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then selbergTerms _ l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun (l:ℕ) => l^2 ≤ s.level),
        ∑ m ∈ (l^(Nat.floor s.level)).divisors.filter (l ∣ ·), s.nu m         := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), s.nu m           := ?_
  · rw [←Finset.sum_filter]; apply Finset.sum_le_sum; intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p^n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    rw [selbergTerms_apply _ l]
    apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
    · intro p hpp hpl
      apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
    · exact hnu_nonneg

  rw [←Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hnu_nonneg _)
    intro m hm
    have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
      apply Finset.prod_pos;
      intro p hp; exact Nat.pos_of_mem_primeFactorsList <| List.mem_toFinset.mp hp
    have hprod_ne_zero :  (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 := by
      apply pow_ne_zero; apply ne_of_gt; apply hprod_pos
    rw [Finset.mem_biUnion]; simp_rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Finset.mem_Icc, Nat.le_floor_iff] at hm
    · have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor; constructor; constructor
      · apply prod_primes_dvd_of_dvd <;> intro p hp
        · apply hP p <| Nat.prime_of_mem_primeFactors hp
          trans (m:ℝ)
          · exact_mod_cast Nat.le_of_mem_primeFactors hp
          trans (Real.sqrt s.level)
          · exact hm.2
          apply sqrt_le_self s.level s.one_le_level
        exact Nat.prime_of_mem_primeFactors hp
      · exact prodPrimes_ne_zero
      · rw [←Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Real.sqrt_sq]
        · trans (m:ℝ)
          · norm_cast; apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
            exact Nat.prod_primeFactors_dvd m
          exact hm.2
        apply le_of_lt; norm_cast
      constructor; constructor
      · rw [←Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
        · intro p
          have hy_mul_prod_nonneg : 0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p := by
            apply mul_nonneg
            · apply Nat.le_floor; norm_cast; linarith only [s.one_le_level]
            · norm_num
          trans (Nat.factorization m) p * 1
          · rw [mul_one]
          rw [Finsupp.smul_apply, smul_eq_mul]
          by_cases hpp : p.Prime
          swap
          · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]; exact hy_mul_prod_nonneg
          by_cases hpdvd : p ∣ m
          swap
          · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]; exact hy_mul_prod_nonneg
          apply mul_le_mul
          · trans m
            · apply le_of_lt <| Nat.factorization_lt _ _
              apply hm_ne_zero
            apply Nat.le_floor
            refine le_trans hm.2 ?_
            apply sqrt_le_self _ s.one_le_level
          · rw [←Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos, pow_one]
            apply Finset.dvd_prod_of_mem
            rw [Nat.mem_primeFactors]
            exact ⟨hpp, hpdvd, hm_ne_zero⟩
          · norm_num
          · norm_num
        exact hm_ne_zero
      · exact hprod_ne_zero
      · exact Nat.prod_primeFactors_dvd m
    · apply Real.sqrt_nonneg
  · intro i hi j hj hij t hti htj x hx
    simp only [Finset.bot_eq_empty, Finset.notMem_empty]
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply Nat.squarefree_dvd_pow i j n (squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw[←hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw[hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw[hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp[h]
      simp
    · intro p hpp _
      rw[hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [if_neg, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply];

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
  (hP : ∀ p:ℕ, p.Prime → (p:ℝ) ≤ s.level → p ∣ s.prodPrimes)  :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor <| Real.sqrt s.level), 1 / (m:ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log <| Real.sqrt s.level)
  · rw [ge_iff_le]; simp_rw[one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith[s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith[s.one_le_level]

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |rem (s := s.toBoundingSieve) d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors, (if (d : ℝ) ≤ s.level then (3:ℝ) ^ ω d * |rem (s := s.toBoundingSieve) d| else 0)
      ≤ C * s.level * (1+Real.log s.level)^3 := by
  rw [←Finset.sum_filter]
  trans (∑ d ∈  Finset.filter (fun d:ℕ => ↑d ≤ s.level) (s.prodPrimes.divisors),  3 ^ ω d * C )
  · gcongr with d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [←Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| rem (s := s.toBoundingSieve) 1, hrem 1 (by norm_num)]
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply prodPrimes_squarefree

end Sieve
end
end

section

namespace Erdos279

open Finset Real Nat
open scoped BigOperators ArithmeticFunction
open BoundingSieve

noncomputable def shiftedIntervalSelbergSieve (C N z : Nat) (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.range (N + 1)).image fun n => C + n
  prodPrimes := primorial z
  prodPrimes_squarefree := Sieve.primorial_squarefree z
  weights := fun _ => 1
  weights_nonneg := by
    intro n
    norm_num
  totalMass := (N + 1 : Nat)
  nu := (ArithmeticFunction.zeta : ArithmeticFunction Real).pdiv
      ArithmeticFunction.id
  nu_mult := by
    exact Sieve.CompletelyMultiplicative.zeta.pdiv
        Sieve.CompletelyMultiplicative.id
        |>.isMultiplicative
  nu_pos_of_prime := by
    intro p hp _hpP
    rw [ArithmeticFunction.pdiv_apply]
    apply _root_.div_pos
    · exact Sieve.zeta_pos_of_prime p hp
    · rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.id_apply]
      exact_mod_cast hp.pos
  nu_lt_one_of_prime := by
    intro p hp _hpP
    rw [ArithmeticFunction.pdiv_apply]
    apply (div_lt_one (by
      rw [ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.id_apply]
      exact_mod_cast hp.pos)).2
    simpa [ArithmeticFunction.natCoe_apply,
      ArithmeticFunction.id_apply] using Sieve.zeta_lt_self_of_prime p hp
  level := z
  one_le_level := by
    exact_mod_cast hz

@[simp]
theorem shiftedIntervalSelbergSieve_nu (C N z : Nat) (hz : 1 ≤ z) (d : Nat) :
    (shiftedIntervalSelbergSieve C N z hz).nu d = if d = 0 then 0 else 1 / (d : Real) := by
  by_cases hd : d = 0
  · simp [shiftedIntervalSelbergSieve, hd,
      ArithmeticFunction.pdiv_apply,
      ArithmeticFunction.zeta_apply]
  · simp [shiftedIntervalSelbergSieve, hd,
      ArithmeticFunction.pdiv_apply,
      ArithmeticFunction.zeta_apply, one_div]

theorem shiftedIntervalSelbergSieve_siftedSum_eq (C N z : Nat) (hz : 1 ≤ z) :
    (shiftedIntervalSelbergSieve C N z hz).siftedSum = (((Finset.range (N + 1)).filter fun n =>
        (C + n).Coprime (primorial z)).card : Real) := by
  classical
  unfold BoundingSieve.siftedSum
  simp only [shiftedIntervalSelbergSieve]
  rw [Finset.sum_image]
  · change (∑ x ∈ Finset.range (N + 1),
        if (primorial z).Coprime (C + x) then (1 : ℝ) else 0) = _
    rw [Finset.sum_boole]
    apply congrArg (fun A : Finset ℕ => (A.card : ℝ))
    ext x
    simp only [Finset.mem_filter, Nat.coprime_comm]
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

theorem shiftedIntervalSelbergSieve_multSum_eq (C N z : Nat) (hz : 1 ≤ z) (d : Nat) :
    (shiftedIntervalSelbergSieve C N z hz).multSum d = (((Finset.range (N + 1)).filter fun n =>
        d ∣ C + n).card : Real) := by
  classical
  unfold BoundingSieve.multSum
  simp only [shiftedIntervalSelbergSieve]
  rw [Finset.sum_image]
  · rw [← Finset.sum_filter]
    simp
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

theorem shiftedIntervalSelbergSieve_rem_abs_le_one (C N z : Nat) (hz : 1 ≤ z)
    (d : Nat) (hd : 0 < d) :
    |(shiftedIntervalSelbergSieve C N z hz).rem d| ≤ 1 := by
  classical
  letI : NeZero d := ⟨hd.ne'⟩
  let v : Nat := (-(C : ZMod d)).val
  have hv : ∀ n : Nat, d ∣ C + n ↔ n ≡ v [MOD d] := by
    intro n
    constructor
    · intro h
      have hzero : ((C + n : Nat) : ZMod d) = 0 := (ZMod.natCast_eq_zero_iff (C + n) d).2 h
      apply (ZMod.natCast_eq_natCast_iff n v d).1
      rw [show (v : ZMod d) = -(C : ZMod d) by
        simp [v]]
      calc
        (n : ZMod d) = -(C : ZMod d) + ((C + n : Nat) : ZMod d) := by
          push_cast
          ring
        _ = -(C : ZMod d) := by rw [hzero, add_zero]
    · intro h
      apply (ZMod.natCast_eq_zero_iff (C + n) d).1
      have heq : (n : ZMod d) = (v : ZMod d) := (ZMod.natCast_eq_natCast_iff n v d).2 h
      rw [show (v : ZMod d) = -(C : ZMod d) by
        simp [v]] at heq
      calc
        ((C + n : Nat) : ZMod d) = (C : ZMod d) + (n : ZMod d) := by simp
        _ = (C : ZMod d) + (-(C : ZMod d)) := by rw [heq]
        _ = 0 := add_neg_cancel _
  have hcount : ((Finset.range (N + 1)).filter fun n => d ∣ C + n).card = (N + 1) / d +
          if v % d < (N + 1) % d then 1 else 0 := by
    rw [← Nat.count_eq_card_filter_range]
    simpa only [hv] using Nat.count_modEq_card (N + 1) hd v
  have hfloor : ((N + 1) / d : Nat) ≤ (N + 1 : Real) / d := by
    simpa using Nat.cast_div_le (α := Real)
        (m := N + 1) (n := d)
  have hdecomp : (((N + 1) / d : Nat) : Real) * (d : Real) +
          (((N + 1) % d : Nat) : Real) =
        (N + 1 : Real) := by
    exact_mod_cast
      (by
        simpa [Nat.mul_comm] using Nat.div_add_mod (N + 1) d)
  have hmod : (((N + 1) % d : Nat) : Real) < (d : Real) := by
    exact_mod_cast Nat.mod_lt (N + 1) hd
  have hdReal : (0 : Real) < (d : Real) := by
    exact_mod_cast hd
  have hceil : (N + 1 : Real) / d < ((N + 1) / d : Nat) + 1 := by
    rw [div_lt_iff₀ hdReal]
    push_cast
    nlinarith
  rw [BoundingSieve.rem,
    shiftedIntervalSelbergSieve_multSum_eq,
    shiftedIntervalSelbergSieve_nu]
  simp only [hd.ne', ↓reduceIte,
    shiftedIntervalSelbergSieve]
  rw [hcount]
  push_cast
  have hmain : 1 / (d : Real) * ((N : Real) + 1) = ((N : Real) + 1) / d := by
    ring
  rw [hmain]
  split_ifs <;> rw [abs_le] <;>
    constructor <;> linarith

theorem shiftedIntervalSelbergSieve_siftedSum_le (C N z : Nat) (hz : 2 ≤ z) :
    (shiftedIntervalSelbergSieve C N z (by omega)).siftedSum ≤
      2 * ((N + 1 : Nat) : Real) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 := by
  have hz1 : 1 ≤ z := by omega
  let s : SelbergSieve := shiftedIntervalSelbergSieve C N z hz1
  have hnu : s.nu = (ArithmeticFunction.zeta : ArithmeticFunction Real).pdiv
          ArithmeticFunction.id := rfl
  have hP : ∀ p : Nat, p.Prime → (p : Real) ≤ s.level → p ∣ s.prodPrimes := by
    intro p hp hpz
    rw [show s.prodPrimes = primorial z by rfl,
      Sieve.prime_dvd_primorial_iff z p hp]
    change (p : Real) ≤ (z : Real) at hpz
    exact_mod_cast hpz
  have hbounding : Real.log z / 2 ≤ s.selbergBoundingSum := Sieve.boundingSum_ge_log s hnu hP
  have hlogPos : 0 < Real.log (z : Real) := by
    exact Real.log_pos (by exact_mod_cast hz)
  have hmain : s.totalMass / s.selbergBoundingSum ≤ 2 * ((N + 1 : Nat) : Real) / Real.log z := by
    calc
      s.totalMass / s.selbergBoundingSum ≤ s.totalMass / (Real.log z / 2) := by
        apply div_le_div_of_nonneg_left
        · change (0 : Real) ≤ ((N + 1 : Nat) : Real)
          positivity
        · exact _root_.div_pos hlogPos (by norm_num)
        · exact hbounding
      _ = 2 * ((N + 1 : Nat) : Real) / Real.log z := by
        dsimp [s, shiftedIntervalSelbergSieve]
        field_simp [hlogPos.ne']
  have herror : (∑ d ∈ s.prodPrimes.divisors,
          if (d : Real) ≤ s.level then
            (3 : Real) ^ ArithmeticFunction.cardDistinctFactors d *
              |s.rem d|
          else 0) ≤
        (z : Real) * (1 + Real.log z) ^ 3 := by
    have hraw := Sieve.rem_sum_le_of_const s 1
        (fun d hd => shiftedIntervalSelbergSieve_rem_abs_le_one
            C N z hz1 d hd)
    simpa [s, shiftedIntervalSelbergSieve] using hraw
  exact (s.selberg_bound_simple).trans
      (add_le_add hmain herror)

theorem shiftedInterval_sifted_card_le (C N z : Nat) (hz : 2 ≤ z) :
    ((((Finset.range (N + 1)).filter fun n => (C + n).Coprime (primorial z)).card : Nat) : Real) ≤
      2 * ((N + 1 : Nat) : Real) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 := by
  have hz1 : 1 ≤ z := by omega
  rw [← shiftedIntervalSelbergSieve_siftedSum_eq
    C N z hz1]
  exact shiftedIntervalSelbergSieve_siftedSum_le C N z hz

end Erdos279
end

section

namespace Erdos279

noncomputable def extendedUnitBadClassZMod {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (q : Prime) :
    ZMod q.1 := by
  classical
  exact if InControllerProgression h q then
      ((translatedPrimeClass h q e (a.residue q) : Nat) : ZMod q.1)
    else
      0

noncomputable def unitQuotientBadClassZMod {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) (q : Prime) :
    ZMod q.1 :=
  if q = h then
    (j : ZMod q.1)
  else
    (extendedUnitBadClassZMod e a q - 1) *
      ((h.1 : Nat) : ZMod q.1)⁻¹

noncomputable def unitSieveShiftResidue {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) (q : Prime) :
    Nat :=
  (-unitQuotientBadClassZMod e a j q).val

noncomputable def unitSieveShift {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j : Nat) :
    Nat :=
  (Nat.chineseRemainderOfFinset
    (unitSieveShiftResidue e a j)
    (fun q : Prime => q.1)
    (allPrimesUpTo z)
    (primeValues_ne_zero (allPrimesUpTo z))
    (primeValues_pairwise_coprime (allPrimesUpTo z))).1

theorem unitSieveShift_modEq {h : Prime} {z e j : Nat} (a : OldPrimeClasses h z) {q : Prime}
    (hqz : q.1 ≤ z) :
    unitSieveShift e a j ≡
      unitSieveShiftResidue e a j q [MOD q.1] := by
  exact (Nat.chineseRemainderOfFinset
      (unitSieveShiftResidue e a j)
      (fun r : Prime => r.1)
      (allPrimesUpTo z)
      (primeValues_ne_zero (allPrimesUpTo z))
      (primeValues_pairwise_coprime (allPrimesUpTo z))).2
        q (mem_allPrimesUpTo.mpr hqz)

@[simp]
theorem unitSieveShiftResidue_cast {h : Prime} {z e j : Nat} (a : OldPrimeClasses h z) (q : Prime) :
    ((unitSieveShiftResidue e a j q : Nat) : ZMod q.1) = -unitQuotientBadClassZMod e a j q := by
  letI : NeZero q.1 := ⟨Nat.ne_of_gt q.pos⟩
  exact ZMod.natCast_zmod_val _

theorem prime_dvd_unitSieveShift_add_iff {h : Prime} {z e j n : Nat}
    (a : OldPrimeClasses h z) {q : Prime}
    (hqz : q.1 ≤ z) :
    q.1 ∣ unitSieveShift e a j + n ↔ ((n : Nat) : ZMod q.1) = unitQuotientBadClassZMod e a j q := by
  have hshift : ((unitSieveShift e a j : Nat) : ZMod q.1) = -unitQuotientBadClassZMod e a j q := by
    have hmod := unitSieveShift_modEq a (e := e) (j := j) hqz
    rw [← ZMod.natCast_eq_natCast_iff] at hmod
    simpa using hmod.trans (unitSieveShiftResidue_cast a q)
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [hshift]
  constructor <;> intro hn
  · apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_comm] using hn
  · rw [hn, neg_add_cancel]

theorem hub_coprime_prime_of_ne {h q : Prime} (hqh : q ≠ h) : h.1.Coprime q.1 := by
  exact (Nat.coprime_primes h.natPrime q.natPrime).mpr
      (fun hv => hqh (Subtype.ext hv.symm))

theorem hub_mul_unitQuotientBadClass_add_one {h : Prime} {z e j : Nat}
    (a : OldPrimeClasses h z) {q : Prime}
    (hqh : q ≠ h) :
    ((h.1 : Nat) : ZMod q.1) *
          unitQuotientBadClassZMod e a j q + 1 =
        extendedUnitBadClassZMod e a q := by
  have hinv : ((h.1 : Nat) : ZMod q.1) *
          ((h.1 : Nat) : ZMod q.1)⁻¹ = 1 :=
    ZMod.coe_mul_inv_eq_one h.1
      (hub_coprime_prime_of_ne hqh)
  rw [unitQuotientBadClassZMod, if_neg hqh]
  calc
    ((h.1 : Nat) : ZMod q.1) *
          ((extendedUnitBadClassZMod e a q - 1) *
            ((h.1 : Nat) : ZMod q.1)⁻¹) + 1 =
        (extendedUnitBadClassZMod e a q - 1) *
            (((h.1 : Nat) : ZMod q.1) *
              ((h.1 : Nat) : ZMod q.1)⁻¹) + 1 := by ring
    _ = extendedUnitBadClassZMod e a q := by
      rw [hinv]
      ring

theorem unitSieveShift_add_coprime {h : Prime} {z e j u n : Nat} (a : OldPrimeClasses h z)
    (hu : ControllerSemigroup h u)
    (hun : u = h.1 * n + 1)
    (hav : AvoidsOldClasses (translatedOldPrimeClasses e a) u)
    (hhub : ((n : Nat) : ZMod h.1) ≠ (j : ZMod h.1)) :
    (unitSieveShift e a j + n).Coprime (primorial z) := by
  refine Nat.coprime_of_dvd ?_
  intro p hp hpShift hpPrimorial
  let q : Prime := ⟨p, (isPrime_iff_natPrime p).mpr hp⟩
  have hqz : q.1 ≤ z := (Sieve.prime_dvd_primorial_iff z p hp).mp hpPrimorial
  have hnotBad : ((n : Nat) : ZMod q.1) ≠
        unitQuotientBadClassZMod e a j q := by
    by_cases hqh : q = h
    · subst h
      simpa [unitQuotientBadClassZMod] using hhub
    · intro hnBad
      have huBad : ((u : Nat) : ZMod q.1) = extendedUnitBadClassZMod e a q := by
        calc
          ((u : Nat) : ZMod q.1) = ((h.1 : Nat) : ZMod q.1) *
                  ((n : Nat) : ZMod q.1) + 1 := by
            rw [hun]
            push_cast
            rfl
          _ = ((h.1 : Nat) : ZMod q.1) *
                  unitQuotientBadClassZMod e a j q + 1 := by
            rw [hnBad]
          _ = extendedUnitBadClassZMod e a q := hub_mul_unitQuotientBadClass_add_one a hqh
      by_cases hqG : InControllerProgression h q
      · apply hav q hqG hqz
        change
          u % q.1 = (translatedPrimeClass h q e (a.residue q) : Nat)
        have heqmod := (ZMod.natCast_eq_natCast_iff' u
            (translatedPrimeClass h q e (a.residue q) : Nat)
            q.1).mp
            (by
              simpa [extendedUnitBadClassZMod, hqG] using huBad)
        simpa [Nat.mod_eq_of_lt
          (translatedPrimeClass h q e (a.residue q)).isLt] using heqmod
      · apply hqG
        apply hu.primeDivisor_mem
        apply (ZMod.natCast_eq_zero_iff u q.1).mp
        simpa [extendedUnitBadClassZMod, hqG] using huBad
  exact hnotBad
    ((prime_dvd_unitSieveShift_add_iff a hqz).mp hpShift)

theorem ControllerSemigroup.eq_hub_mul_div_add_one {h : Prime} {u : Nat}
    (hu : ControllerSemigroup h u) :
    u = h.1 * (u / h.1) + 1 := by
  have hdivmod := Nat.div_add_mod u h.1
  rw [hu.mod_h_eq_one] at hdivmod
  omega

theorem controllerSemigroup_div_hub_injective {h : Prime} : Set.InjOn (fun u : Nat => u / h.1)
      {u | ControllerSemigroup h u} := by
  intro u hu v hv huv
  change u / h.1 = v / h.1 at huv
  rw [hu.eq_hub_mul_div_add_one,
    hv.eq_hub_mul_div_add_one, huv]

noncomputable def unitQuotientSiftedSet {h : Prime} {z : Nat}
    (e : Nat) (a : OldPrimeClasses h z) (j Z : Nat) :
    Finset Nat := by
  classical
  exact (Finset.range (Z / h.1 + 1)).filter fun n =>
      (unitSieveShift e a j + n).Coprime (primorial z)

theorem hardLayerUnit_div_mem_dualSieve {h : Prime} {z e Y Z u : Nat} {a : OldPrimeClasses h z}
    (huMem : u ∈ hardLayerUnits h z e a Y Z) :
    u / h.1 ∈ unitQuotientSiftedSet e a 0 Z ∪
        unitQuotientSiftedSet e a 1 Z := by
  classical
  have huData : Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u ∧ AvoidsOldClasses a (h.1 ^ e * u) := by
    simpa [hardLayerUnits, mem_controllerElements, and_assoc] using huMem
  rcases huData with ⟨_hYu, huZ, huG, huAvoid⟩
  have huAvoidTranslated : AvoidsOldClasses (translatedOldPrimeClasses e a) u :=
    (avoidsOldClasses_hubPower_mul_iff a).mp huAvoid
  have hnRange : u / h.1 < Z / h.1 + 1 := by
    exact Nat.lt_succ_of_le (Nat.div_le_div_right huZ)
  have huEq : u = h.1 * (u / h.1) + 1 := huG.eq_hub_mul_div_add_one
  letI : NeZero h.1 := ⟨Nat.ne_of_gt h.pos⟩
  by_cases hnZero : (((u / h.1 : Nat) : ZMod h.1) = 0)
  · rw [Finset.mem_union]
    right
    rw [unitQuotientSiftedSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hnRange, ?_⟩
    apply unitSieveShift_add_coprime a huG huEq huAvoidTranslated
    intro hnOne
    have hnZeroMod : (u / h.1) % h.1 = 0 % h.1 := by
      apply (ZMod.natCast_eq_natCast_iff'
        (u / h.1) 0 h.1).mp
      simpa using hnZero
    have hnOneMod : (u / h.1) % h.1 = 1 % h.1 := by
      apply (ZMod.natCast_eq_natCast_iff'
        (u / h.1) 1 h.1).mp
      simpa using hnOne
    simp only [Nat.zero_mod] at hnZeroMod
    rw [Nat.mod_eq_of_lt h.one_lt] at hnOneMod
    omega
  · rw [Finset.mem_union]
    left
    rw [unitQuotientSiftedSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hnRange,
        unitSieveShift_add_coprime a huG huEq huAvoidTranslated ?_⟩
    simpa only [Nat.cast_zero] using hnZero

theorem hardLayerUnits_card_le_dualSieve (h : Prime) (z e : Nat) (a : OldPrimeClasses h z)
    (Y Z : Nat) :
    (hardLayerUnits h z e a Y Z).card ≤ (unitQuotientSiftedSet e a 0 Z).card +
        (unitQuotientSiftedSet e a 1 Z).card := by
  classical
  calc
    (hardLayerUnits h z e a Y Z).card ≤ (unitQuotientSiftedSet e a 0 Z ∪
          unitQuotientSiftedSet e a 1 Z).card := by
      apply Finset.card_le_card_of_injOn (fun u : Nat => u / h.1)
      · intro u hu
        exact hardLayerUnit_div_mem_dualSieve hu
      · intro u hu v hv huv
        have huData : (Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u) ∧
              AvoidsOldClasses a (h.1 ^ e * u) := by
          simpa [hardLayerUnits, mem_controllerElements] using hu
        have hvData : (Y < v ∧ v ≤ Z ∧ ControllerSemigroup h v) ∧
              AvoidsOldClasses a (h.1 ^ e * v) := by
          simpa [hardLayerUnits, mem_controllerElements] using hv
        exact controllerSemigroup_div_hub_injective
            (h := h) huData.1.2.2 hvData.1.2.2 huv
    _ ≤ (unitQuotientSiftedSet e a 0 Z).card +
          (unitQuotientSiftedSet e a 1 Z).card :=
      Finset.card_union_le _ _

theorem hardLayerUnits_card_real_le (h : Prime) (z e : Nat) (a : OldPrimeClasses h z)
    (Y Z : Nat) (hz : 2 ≤ z) :
    ((hardLayerUnits h z e a Y Z).card : Real) ≤ 4 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        2 * ((z : Real) * (1 + Real.log z) ^ 3) := by
  have hcard : ((hardLayerUnits h z e a Y Z).card : Real) ≤
        ((unitQuotientSiftedSet e a 0 Z).card : Real) +
          ((unitQuotientSiftedSet e a 1 Z).card : Real) := by
    exact_mod_cast hardLayerUnits_card_le_dualSieve h z e a Y Z
  have hzero := shiftedInterval_sifted_card_le
      (unitSieveShift e a 0) (Z / h.1) z hz
  have hone := shiftedInterval_sifted_card_le
      (unitSieveShift e a 1) (Z / h.1) z hz
  change
    ((unitQuotientSiftedSet e a 0 Z).card : Real) ≤
      2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 at hzero
  change
    ((unitQuotientSiftedSet e a 1 Z).card : Real) ≤
      2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        (z : Real) * (1 + Real.log z) ^ 3 at hone
  calc
    ((hardLayerUnits h z e a Y Z).card : Real) ≤ ((unitQuotientSiftedSet e a 0 Z).card : Real) +
          ((unitQuotientSiftedSet e a 1 Z).card : Real) := hcard
    _ ≤ (2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
          (z : Real) * (1 + Real.log z) ^ 3) +
        (2 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
          (z : Real) * (1 + Real.log z) ^ 3) :=
      add_le_add hzero hone
    _ = 4 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
          2 * ((z : Real) * (1 + Real.log z) ^ 3) := by ring

theorem hardLayerUnits_card_real_le_simpler (h : Prime) (z e : Nat) (a : OldPrimeClasses h z)
    (Y Z : Nat) (hz : 2 ≤ z) :
    ((hardLayerUnits h z e a Y Z).card : Real) ≤ 4 * (((Z / h.1 + 1 : Nat) : Real)) / Real.log z +
        2 * (z : Real) * (1 + Real.log z) ^ 3 := by
  simpa [mul_assoc] using hardLayerUnits_card_real_le h z e a Y Z hz

end Erdos279
end

section

namespace Erdos279

def hardExponent (h : Prime) (m : Nat) : Nat := m.factorization h.1

def hardCofactor (h : Prime) (m : Nat) : Nat := ordCompl[h.1] m

theorem hard_pow_mul_cofactor (h : Prime) (m : Nat) :
    h.1 ^ hardExponent h m * hardCofactor h m = m := by
  simpa [hardExponent, hardCofactor] using Nat.ordProj_mul_ordCompl_eq_self m h.1

theorem hardExponent_eq_of_decomposition {h : Prime} {m e u : Nat} (hm : m = h.1 ^ e * u)
    (hu : ControllerSemigroup h u) :
    hardExponent h m = e := by
  have hhne : h.1 ^ e ≠ 0 := (Nat.pow_pos h.pos).ne'
  have hune : u ≠ 0 := hu.pos.ne'
  have hnot : ¬h.1 ∣ u := by
    rw [← h.natPrime.coprime_iff_not_dvd]
    exact hu.coprime_hub.symm
  rw [hardExponent, hm, Nat.factorization_mul hhne hune]
  change (h.1 ^ e).factorization h.1 + u.factorization h.1 = e
  rw [Nat.factorization_pow_self h.natPrime,
    Nat.factorization_eq_zero_of_not_dvd hnot]
  omega

theorem hardCofactor_eq_of_decomposition {h : Prime} {m e u : Nat} (hm : m = h.1 ^ e * u)
    (hu : ControllerSemigroup h u) :
    hardCofactor h m = u := by
  have he : hardExponent h m = e := hardExponent_eq_of_decomposition hm hu
  have hcanonical : h.1 ^ e * hardCofactor h m = h.1 ^ e * u := by
    calc
      h.1 ^ e * hardCofactor h m = h.1 ^ hardExponent h m * hardCofactor h m := by rw [he]
      _ = m := hard_pow_mul_cofactor h m
      _ = h.1 ^ e * u := hm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos h.pos) hcanonical

theorem HasHardForm.one_le_hardExponent {h : Prime} {m : Nat} (hm : HasHardForm h m) :
    1 ≤ hardExponent h m := by
  rcases hm with ⟨e, u, he, hu, hdecomp⟩
  simpa [hardExponent_eq_of_decomposition hdecomp hu] using he

theorem HasHardForm.hardCofactor_mem {h : Prime} {m : Nat} (hm : HasHardForm h m) :
    ControllerSemigroup h (hardCofactor h m) := by
  rcases hm with ⟨e, u, _he, hu, hdecomp⟩
  simpa [hardCofactor_eq_of_decomposition hdecomp hu] using hu

theorem HasHardForm.canonical_decomposition {h : Prime} {m : Nat} (_hm : HasHardForm h m) :
    m = h.1 ^ hardExponent h m * hardCofactor h m :=
  (hard_pow_mul_cofactor h m).symm

end Erdos279
end

section

namespace Erdos279

open Finset

noncomputable def hardSurvivorLayer (h : Prime) (z e : Nat) (a : OldPrimeClasses h z)
    (X Z : Nat) : Finset Nat := by
  classical
  exact (hardSurvivors h z a X Z).filter fun m => hardExponent h m = e

@[simp]
theorem mem_hardSurvivorLayer {h : Prime} {z e X Z m : Nat} {a : OldPrimeClasses h z} :
    m ∈ hardSurvivorLayer h z e a X Z ↔ m ∈ hardSurvivors h z a X Z ∧ hardExponent h m = e := by
  classical
  simp [hardSurvivorLayer]

@[simp]
theorem mem_hardLayerUnits {h : Prime} {z e Y Z u : Nat} {a : OldPrimeClasses h z} :
    u ∈ hardLayerUnits h z e a Y Z ↔ Y < u ∧ u ≤ Z ∧ ControllerSemigroup h u ∧
      AvoidsOldClasses a (h.1 ^ e * u) := by
  classical
  simp [hardLayerUnits, and_assoc]

theorem hardLayerUnits_card_eq_survivorLayer (h : Prime) (z e : Nat) (a : OldPrimeClasses h z)
    (X Z : Nat)
    (he : 1 ≤ e) :
    (hardLayerUnits h z e a
        (X / h.1 ^ e) (Z / h.1 ^ e)).card =
      (hardSurvivorLayer h z e a X Z).card := by
  classical
  have hpowpos : 0 < h.1 ^ e := Nat.pow_pos h.pos
  refine Finset.card_bij'
    (fun u _hu => h.1 ^ e * u)
    (fun m _hm => hardCofactor h m)
    ?_ ?_ ?_ ?_
  · intro u hu
    rcases mem_hardLayerUnits.mp hu with
      ⟨huLower, huUpper, huG, huAvoids⟩
    apply mem_hardSurvivorLayer.mpr
    refine ⟨mem_hardSurvivors.mpr ⟨?_, ?_, ?_, huAvoids⟩, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hpowpos).mp at huLower
      simpa [Nat.mul_comm] using huLower
    · apply (Nat.le_div_iff_mul_le hpowpos).mp at huUpper
      simpa [Nat.mul_comm] using huUpper
    · exact ⟨e, u, he, huG, rfl⟩
    · exact hardExponent_eq_of_decomposition rfl huG
  · intro m hm
    rcases mem_hardSurvivorLayer.mp hm with ⟨hmSurvivor, hmExponent⟩
    rcases mem_hardSurvivors.mp hmSurvivor with
      ⟨hmLower, hmUpper, hmForm, hmAvoids⟩
    have hmDecomp : m = h.1 ^ e * hardCofactor h m := by
      simpa [hmExponent] using hmForm.canonical_decomposition
    apply mem_hardLayerUnits.mpr
    refine ⟨?_, ?_, hmForm.hardCofactor_mem, ?_⟩
    · apply (Nat.div_lt_iff_lt_mul hpowpos).mpr
      have hproduct : X < h.1 ^ e * hardCofactor h m := by
        rw [← hmDecomp]
        exact hmLower
      simpa only [Nat.mul_comm] using hproduct
    · apply (Nat.le_div_iff_mul_le hpowpos).mpr
      have hproduct : h.1 ^ e * hardCofactor h m ≤ Z := by
        rw [← hmDecomp]
        exact hmUpper
      simpa only [Nat.mul_comm] using hproduct
    · rw [← hmDecomp]
      exact hmAvoids
  · intro u hu
    have huG := (mem_hardLayerUnits.mp hu).2.2.1
    exact hardCofactor_eq_of_decomposition rfl huG
  · intro m hm
    have hmExponent := (mem_hardSurvivorLayer.mp hm).2
    change h.1 ^ e * hardCofactor h m = m
    calc
      h.1 ^ e * hardCofactor h m = h.1 ^ hardExponent h m * hardCofactor h m := by
            rw [hmExponent]
      _ = m := hard_pow_mul_cofactor h m

end Erdos279
end

section

namespace Erdos279

open Finset

end Erdos279
end

section

namespace Erdos279

open Finset

def hardLogExponentRange (h : Prime) (Z : Nat) : Finset Nat := Finset.Icc 1 (Nat.log h.1 Z)

theorem hardExponent_le_log_of_mem {h : Prime} {z X Z m : Nat} {a : OldPrimeClasses h z}
    (hm : m ∈ hardSurvivors h z a X Z) :
    hardExponent h m ≤ Nat.log h.1 Z := by
  have hmData := mem_hardSurvivors.mp hm
  have hmForm : HasHardForm h m := hmData.2.2.1
  have hpowDvd : h.1 ^ hardExponent h m ∣ m := by
    refine ⟨hardCofactor h m, ?_⟩
    exact hmForm.canonical_decomposition
  have hpowLeM : h.1 ^ hardExponent h m ≤ m := Nat.le_of_dvd hmForm.pos hpowDvd
  exact Nat.le_log_of_pow_le h.one_lt
    (hpowLeM.trans hmData.2.1)

theorem hardExponent_mem_logRange_of_mem {h : Prime} {z X Z m : Nat} {a : OldPrimeClasses h z}
    (hm : m ∈ hardSurvivors h z a X Z) :
    hardExponent h m ∈ hardLogExponentRange h Z := by
  exact Finset.mem_Icc.mpr
    ⟨(mem_hardSurvivors.mp hm).2.2.1.one_le_hardExponent,
      hardExponent_le_log_of_mem hm⟩

theorem hardSurvivors_card_eq_sum_logLayers (h : Prime) (z : Nat) (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card = ∑ e ∈ hardLogExponentRange h Z,
        (hardSurvivorLayer h z e a X Z).card := by
  classical
  have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (hardSurvivors h z a X Z)
      (hardLogExponentRange h Z)
      (hardExponent h)
  have hfilter : (hardSurvivors h z a X Z).filter
          (fun m => hardExponent h m ∈ hardLogExponentRange h Z) =
        hardSurvivors h z a X Z := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact hardExponent_mem_logRange_of_mem hm
  rw [hfilter] at hsum
  simpa [hardSurvivorLayer] using hsum.symm

theorem hardSurvivors_card_eq_sum_logLayerUnits (h : Prime) (z : Nat) (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card = ∑ e ∈ hardLogExponentRange h Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card := by
  rw [hardSurvivors_card_eq_sum_logLayers]
  apply Finset.sum_congr rfl
  intro e he
  exact (hardLayerUnits_card_eq_survivorLayer
    h z e a X Z (Finset.mem_Icc.mp he).1).symm

def hardMainExponentRange (h : Prime) (X Z : Nat) : Finset Nat :=
  (hardLogExponentRange h Z).filter fun e => Nat.sqrt X ≤ X / h.1 ^ e

def hardTailExponentRange (h : Prime) (X Z : Nat) : Finset Nat :=
  (hardLogExponentRange h Z).filter fun e => X / h.1 ^ e < Nat.sqrt X

theorem hardSurvivors_card_eq_main_add_tail (h : Prime) (z : Nat) (a : OldPrimeClasses h z)
    (X Z : Nat) :
    (hardSurvivors h z a X Z).card = (∑ e ∈ hardMainExponentRange h X Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card) +
      ∑ e ∈ hardTailExponentRange h X Z,
        (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card := by
  classical
  rw [hardSurvivors_card_eq_sum_logLayerUnits]
  simpa only [hardMainExponentRange, hardTailExponentRange, not_le] using
    (Finset.sum_filter_add_sum_filter_not
      (hardLogExponentRange h Z)
      (fun e => Nat.sqrt X ≤ X / h.1 ^ e)
      (fun e => (hardLayerUnits h z e a
          (X / h.1 ^ e) (Z / h.1 ^ e)).card)).symm

theorem hardLayerUnits_card_le_upper (h : Prime) (z e : Nat) (a : OldPrimeClasses h z) (Y Z : Nat) :
    (hardLayerUnits h z e a Y Z).card ≤ Z := by
  classical
  have hsubset : hardLayerUnits h z e a Y Z ⊆ natIoc Y Z := by
    intro u hu
    exact Finset.mem_Ioc.mpr
      ⟨(mem_hardLayerUnits.mp hu).1,
        (mem_hardLayerUnits.mp hu).2.1⟩
  calc
    (hardLayerUnits h z e a Y Z).card ≤ (natIoc Y Z).card := Finset.card_le_card hsubset
    _ = Z - Y := by simp [natIoc]
    _ ≤ Z := Nat.sub_le _ _

theorem hardTailLayer_card_le (h : Prime) (z e B X : Nat) (a : OldPrimeClasses h z) (hB : 0 < B)
    (heTail : X / h.1 ^ e < Nat.sqrt X) :
    (hardLayerUnits h z e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card ≤ B * Nat.sqrt X := by
  have hpowPos : 0 < h.1 ^ e := Nat.pow_pos h.pos
  have hXlt : X < Nat.sqrt X * h.1 ^ e := (Nat.div_lt_iff_lt_mul hpowPos).mp heTail
  have hBXlt : B * X < (B * Nat.sqrt X) * h.1 ^ e := by
    calc
      B * X < B * (Nat.sqrt X * h.1 ^ e) := Nat.mul_lt_mul_of_pos_left hXlt hB
      _ = (B * Nat.sqrt X) * h.1 ^ e := by
        ac_rfl
  have hquotient : (B * X) / h.1 ^ e < B * Nat.sqrt X := (Nat.div_lt_iff_lt_mul hpowPos).mpr hBXlt
  exact (hardLayerUnits_card_le_upper h z e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).trans
      hquotient.le

theorem sum_hardTailLayers_card_le (h : Prime) (z B X : Nat) (a : OldPrimeClasses h z)
    (hB : 0 < B) :
    (∑ e ∈ hardTailExponentRange h X (B * X),
      (hardLayerUnits h z e a
        (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card) ≤
      (Nat.log h.1 (B * X) + 1) * (B * Nat.sqrt X) := by
  classical
  calc
    (∑ e ∈ hardTailExponentRange h X (B * X),
      (hardLayerUnits h z e a
        (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card) ≤
        ∑ _e ∈ hardTailExponentRange h X (B * X),
          B * Nat.sqrt X := by
      apply Finset.sum_le_sum
      intro e he
      exact hardTailLayer_card_le h z e B X a hB
        (Finset.mem_filter.mp he).2
    _ = (hardTailExponentRange h X (B * X)).card *
          (B * Nat.sqrt X) := by
      simp
    _ ≤ (Nat.log h.1 (B * X) + 1) *
          (B * Nat.sqrt X) := by
      apply Nat.mul_le_mul_right
      have hsubset : hardTailExponentRange h X (B * X) ⊆
            hardLogExponentRange h (B * X) := by
        intro e he
        exact (Finset.mem_filter.mp he).1
      calc
        (hardTailExponentRange h X (B * X)).card ≤ (hardLogExponentRange h (B * X)).card :=
          Finset.card_le_card hsubset
        _ ≤ Nat.log h.1 (B * X) + 1 := by
          simp [hardLogExponentRange]

end Erdos279
end

section

namespace Erdos279

theorem exists_prime_sqrt_div_sub_one_lt (D : Real) (hD : 0 ≤ D) (k : Nat) : ∃ h : Prime,
      k < h.1 ∧ D * Real.sqrt (h.1 : Real) /
            ((h.1 : Real) - 1) < 1 := by
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt
      (max (k : Real) (max 4 (4 * D ^ 2)))
  obtain ⟨p, hpPrime, hNp, _hpmod⟩ := Nat.exists_prime_gt_modEq_one
      (k := 1) N one_ne_zero
  let h : Prime := ⟨p, (isPrime_iff_natPrime p).2 hpPrime⟩
  have hkN : (k : Real) < (N : Real) := lt_of_le_of_lt (le_max_left _ _) hN
  have hfourN : (4 : Real) < (N : Real) := lt_of_le_of_lt
      (le_trans (le_max_left 4 (4 * D ^ 2))
        (le_max_right (k : Real) _))
      hN
  have hDN : 4 * D ^ 2 < (N : Real) := lt_of_le_of_lt
      (le_trans (le_max_right 4 (4 * D ^ 2))
        (le_max_right (k : Real) _))
      hN
  have hNpR : (N : Real) < (p : Real) := by
    exact_mod_cast hNp
  have hkp : k < p := by
    exact_mod_cast hkN.trans hNpR
  have hpFour : (4 : Real) < (p : Real) := hfourN.trans hNpR
  have hpD : 4 * D ^ 2 < (p : Real) := hDN.trans hNpR
  have htwoD : 0 ≤ 2 * D := mul_nonneg (by norm_num) hD
  have hsquare : (2 * D) ^ 2 < (p : Real) := by
    nlinarith [sq_nonneg D]
  have hsqrt : 2 * D < Real.sqrt (p : Real) := by
    have hs := Real.sqrt_lt_sqrt (sq_nonneg (2 * D)) hsquare
    simpa [Real.sqrt_sq htwoD] using hs
  have hsqrtPos : 0 < Real.sqrt (p : Real) := by positivity
  have hsqrtMul := mul_lt_mul_of_pos_right hsqrt hsqrtPos
  have hsqrtSq : Real.sqrt (p : Real) *
          Real.sqrt (p : Real) = (p : Real) :=
    Real.mul_self_sqrt (by positivity)
  rw [mul_assoc, hsqrtSq] at hsqrtMul
  have hnum : D * Real.sqrt (p : Real) < (p : Real) - 1 := by
    nlinarith
  have hden : 0 < (p : Real) - 1 := by linarith
  refine ⟨h, hkp, ?_⟩
  exact (div_lt_one hden).mpr hnum

end Erdos279
end

section

namespace Erdos279

open Finset Filter

noncomputable def controllerPrimeReciprocalSum (h : Prime) (z : Nat) : Real :=
  ∑ p ∈ oldControllerPrimes h z, 1 / (p.1 : Real)

def ControllerPrimeReciprocalDiverges (h : Prime) : Prop :=
  Tendsto (controllerPrimeReciprocalSum h) atTop atTop

noncomputable def controllerExclusionProduct (H : Finset Prime) : Real :=
  ∏ p ∈ H, (1 - 1 / ((p.1 : Real) - 1))

noncomputable def controllerComplementDensity (h : Prime) (H : Finset Prime) : Real :=
  (1 - 1 / ((h.1 : Real) - 1)) *
    controllerExclusionProduct H

theorem prod_one_sub_le_exp_neg_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → Real)
    (hx0 : ∀ i ∈ s, 0 ≤ x i)
    (hx1 : ∀ i ∈ s, x i ≤ 1) :
    (∏ i ∈ s, (1 - x i)) ≤ Real.exp (-(∑ i ∈ s, x i)) := by
  calc
    (∏ i ∈ s, (1 - x i)) ≤ ∏ i ∈ s, Real.exp (-x i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hx1 i hi)
      · intro i _hi
        exact Real.one_sub_le_exp_neg (x i)
    _ = Real.exp (∑ i ∈ s, -x i) := by
      exact (Real.exp_sum s (fun i => -x i)).symm
    _ = Real.exp (-(∑ i ∈ s, x i)) := by
      rw [Finset.sum_neg_distrib]

theorem controllerExclusionFactor_mem_unitInterval {h p : Prime} (hh : 3 ≤ h.1)
    (hp : InControllerProgression h p) :
    (0 : Real) ≤ 1 - 1 / ((p.1 : Real) - 1) ∧ 1 - 1 / ((p.1 : Real) - 1) ≤ 1 := by
  have hhp : h.1 < p.1 := hub_lt_of_inControllerProgression hp
  have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
    exact_mod_cast (by omega : 4 ≤ p.1)
  have hpden : (1 : Real) ≤ (p.1 : Real) - 1 := by
    linarith
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_one (by linarith)).mpr hpden
  · have hinv : 0 ≤ 1 / ((p.1 : Real) - 1) := by
      positivity
    linarith

theorem controllerExclusionProduct_le_exp (h : Prime) (hh : 3 ≤ h.1) (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    controllerExclusionProduct H ≤ Real.exp
        (-(∑ p ∈ H, 1 / ((p.1 : Real) - 1))) := by
  unfold controllerExclusionProduct
  apply prod_one_sub_le_exp_neg_sum
  · intro p hp
    have hhp := hub_lt_of_inControllerProgression (hH p hp)
    have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
      exact_mod_cast (by omega : 4 ≤ p.1)
    exact (one_div_pos.mpr (by linarith)).le
  · intro p hp
    have hmem := controllerExclusionFactor_mem_unitInterval
        hh (hH p hp)
    linarith [hmem.1]

theorem controllerExclusionProduct_le_exp_reciprocal (h : Prime) (hh : 3 ≤ h.1) (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    controllerExclusionProduct H ≤ Real.exp (-(∑ p ∈ H, 1 / (p.1 : Real))) := by
  refine (controllerExclusionProduct_le_exp h hh H hH).trans ?_
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro p hp
  have hpPos : (0 : Real) < (p.1 : Real) - 1 := by
    have hhp := hub_lt_of_inControllerProgression (hH p hp)
    have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
      exact_mod_cast (by omega : 4 ≤ p.1)
    linarith
  apply one_div_le_one_div_of_le hpPos
  norm_num

theorem hubComplementFactor_mem_unitInterval (h : Prime) (hh : 3 ≤ h.1) :
    (0 : Real) ≤ 1 - 1 / ((h.1 : Real) - 1) ∧ 1 - 1 / ((h.1 : Real) - 1) ≤ 1 := by
  have hden : (1 : Real) ≤ (h.1 : Real) - 1 := by
    have hhR : (3 : Real) ≤ (h.1 : Real) := by
      exact_mod_cast hh
    linarith
  constructor
  · apply sub_nonneg.mpr
    exact (div_le_one (by linarith)).mpr hden
  · have : 0 ≤ 1 / ((h.1 : Real) - 1) := by positivity
    linarith

theorem exists_oldControllerPrimes_complementDensity_lt (h : Prime) (hh : 3 ≤ h.1)
    (hdiv : ControllerPrimeReciprocalDiverges h)
    {ε : Real} (hε : 0 < ε) :
    ∃ z : Nat,
      controllerComplementDensity h
        (oldControllerPrimes h z) < ε := by
  let B : Real := -Real.log ε + 1
  have hevent : ∀ᶠ z in atTop,
        B ≤ controllerPrimeReciprocalSum h z :=
    tendsto_atTop.1 hdiv B
  obtain ⟨z, hz⟩ := hevent.exists
  have hH : ∀ p ∈ oldControllerPrimes h z,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hprod : controllerExclusionProduct
          (oldControllerPrimes h z) <
        ε := by
    have hupper := controllerExclusionProduct_le_exp_reciprocal
        h hh (oldControllerPrimes h z) hH
    have hsum : B ≤ ∑ p ∈ oldControllerPrimes h z,
            1 / (p.1 : Real) := by
      simpa [controllerPrimeReciprocalSum] using hz
    have hexp : Real.exp
            (-(∑ p ∈ oldControllerPrimes h z,
              1 / (p.1 : Real))) < ε := by
      have harg : -(∑ p ∈ oldControllerPrimes h z,
              1 / (p.1 : Real)) <
            Real.log ε := by
        dsimp [B] at hsum
        linarith
      have := Real.exp_lt_exp.mpr harg
      simpa [Real.exp_log hε] using this
    exact hupper.trans_lt hexp
  refine ⟨z, ?_⟩
  unfold controllerComplementDensity
  have hhub := hubComplementFactor_mem_unitInterval h hh
  have hprodNonneg : 0 ≤ controllerExclusionProduct
        (oldControllerPrimes h z) := by
    unfold controllerExclusionProduct
    apply Finset.prod_nonneg
    intro p hp
    exact (controllerExclusionFactor_mem_unitInterval
        hh (hH p hp)).1
  exact (mul_le_of_le_one_left hprodNonneg hhub.2).trans_lt hprod

end Erdos279
end

section

namespace Erdos279

open Finset

theorem controllerExclusionFactor_pos {h p : Prime} (hh : 3 ≤ h.1)
    (hp : InControllerProgression h p) :
    0 < (1 : Real) - 1 / ((p.1 : Real) - 1) := by
  have hhp : h.1 < p.1 := hub_lt_of_inControllerProgression hp
  have hpLower : 4 ≤ p.1 := by omega
  have hpLowerR : (4 : Real) ≤ (p.1 : Real) := by
    exact_mod_cast hpLower
  have hpdenPos : (0 : Real) < (p.1 : Real) - 1 := by
    linarith
  have hpdenOne : (1 : Real) < (p.1 : Real) - 1 := by
    linarith
  exact sub_pos.mpr ((div_lt_one hpdenPos).mpr hpdenOne)

theorem hubComplementFactor_pos (h : Prime) (hh : 3 ≤ h.1) :
    0 < (1 : Real) - 1 / ((h.1 : Real) - 1) := by
  have hhR : (3 : Real) ≤ (h.1 : Real) := by
    exact_mod_cast hh
  have hdenPos : (0 : Real) < (h.1 : Real) - 1 := by
    linarith
  have hdenOne : (1 : Real) < (h.1 : Real) - 1 := by
    linarith
  exact sub_pos.mpr ((div_lt_one hdenPos).mpr hdenOne)

theorem controllerComplementDensity_pos (h : Prime) (hh : 3 ≤ h.1) (H : Finset Prime)
    (hH : ∀ p ∈ H, InControllerProgression h p) :
    0 < controllerComplementDensity h H := by
  unfold controllerComplementDensity controllerExclusionProduct
  apply mul_pos (hubComplementFactor_pos h hh)
  exact Finset.prod_pos fun p hp => controllerExclusionFactor_pos hh (hH p hp)

theorem exists_density_window {δ Δ : Real} {k h : Nat} (hΔ : 0 < Δ) (hkh : k < h)
    (hsmall : Δ < δ / ((k + h : Nat) : Real)) :
    ∃ τ : Real,
      0 < τ ∧
      (k : Real) * Δ < τ ∧
      τ < (h : Real) * Δ ∧
      τ < δ / 2 := by
  have hkR : (k : Real) < (h : Real) := by
    exact_mod_cast hkh
  have hhpos : 0 < h := lt_of_le_of_lt (Nat.zero_le k) hkh
  have hsumPos : (0 : Real) < (k : Real) + (h : Real) := by
    positivity
  have hsmall' : Δ < δ / ((k : Real) + (h : Real)) := by
    simpa [Nat.cast_add] using hsmall
  have hmul : Δ * ((k : Real) + (h : Real)) < δ := (lt_div_iff₀ hsumPos).mp hsmall'
  refine ⟨((k : Real) + (h : Real)) * Δ / 2, ?_⟩
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exists_nat_mul_mem_Ioo_of_step_lt {a b step : Real} (ha : 0 ≤ a) (hstep : 0 < step)
    (hmesh : step < b - a) :
    ∃ m : Nat,
      a < (m : Real) * step ∧
      (m : Real) * step < b := by
  let q : Real := a / step
  let m : Nat := ⌊q⌋₊ + 1
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt : q < (m : Nat) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hfloor_le : ((⌊q⌋₊ : Nat) : Real) ≤ q := Nat.floor_le hq
  have hm_le : (m : Real) ≤ q + 1 := by
    dsimp [m]
    push_cast
    linarith
  have hq_mul : q * step = a := by
    dsimp [q]
    field_simp
  have hlower : a < (m : Real) * step := by
    have := mul_lt_mul_of_pos_right hq_lt hstep
    rwa [hq_mul] at this
  have hupperWeak : (m : Real) * step ≤ a + step := by
    have := mul_le_mul_of_nonneg_right hm_le hstep.le
    rw [add_mul, hq_mul, one_mul] at this
    exact this
  exact ⟨m, hlower, hupperWeak.trans_lt (by linarith)⟩

theorem auxiliaryPrime_coprime_of_gt (L : Prime) {M : Nat} (hM : 0 < M) (hML : M < L.1) :
    L.1.Coprime M := by
  rw [L.natPrime.coprime_iff_not_dvd]
  intro hdiv
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd hM hdiv)) hML

theorem exists_auxiliary_prime_with_fine_mesh {δ gap : Real} (_hδ : 0 < δ) (hgap : 0 < gap)
    (avoid : Nat) (havoid : 0 < avoid) :
    ∃ L : Prime,
      max avoid 2 < L.1 ∧
      L.1.Coprime avoid ∧
      δ / ((L.1 : Real) - 1) < gap := by
  obtain ⟨N : Nat, hN⟩ := exists_nat_gt
      (max (max avoid 2 : Real) (δ / gap + 1))
  obtain ⟨p, hpPrime, hNp, _hpmod⟩ := Nat.exists_prime_gt_modEq_one
      (k := 1) N one_ne_zero
  let L : Prime := ⟨p, (isPrime_iff_natPrime p).2 hpPrime⟩
  have hboundN : (max avoid 2 : Real) < (N : Real) := (le_max_left _ _).trans_lt hN
  have hratioN : δ / gap + 1 < (N : Real) := (le_max_right _ _).trans_lt hN
  have hNpR : (N : Real) < (p : Real) := by
    exact_mod_cast hNp
  have hlarge : max avoid 2 < p := by
    exact_mod_cast hboundN.trans hNpR
  have hratio : δ / gap < (p : Real) - 1 := by
    linarith
  have hmul : δ < ((p : Real) - 1) * gap := by
    have := (div_lt_iff₀ hgap).mp hratio
    simpa [mul_comm] using this
  have hpden : (0 : Real) < (p : Real) - 1 := by
    have : (2 : Real) < (p : Real) := by
      exact_mod_cast (lt_of_le_of_lt (le_max_right avoid 2) hlarge)
    linarith
  have havoidp : avoid < p := (le_max_left avoid 2).trans_lt hlarge
  have hcoprime : L.1.Coprime avoid := @auxiliaryPrime_coprime_of_gt
      L avoid havoid havoidp
  refine ⟨L, hlarge, hcoprime, ?_⟩
  exact (div_lt_iff₀ hpden).mpr
      (by simpa [mul_comm] using hmul)

theorem exists_oldControllerPrimes_density_window (h : Prime) (hh : 3 ≤ h.1)
    (k : Nat) (hkh : k < h.1)
    (hdiv : ControllerPrimeReciprocalDiverges h) :
    ∃ z : Nat, ∃ τ : Real,
      0 < controllerComplementDensity h
          (oldControllerPrimes h z) ∧
      0 < τ ∧
      (k : Real) *
          controllerComplementDensity h
            (oldControllerPrimes h z) < τ ∧
      τ < (h.1 : Real) *
            controllerComplementDensity h
              (oldControllerPrimes h z) ∧
      τ < controllerDensity h / 2 := by
  have hsumPosNat : 0 < k + h.1 := by
    omega
  have hsumPosReal : (0 : Real) < ((k + h.1 : Nat) : Real) := by
    exact_mod_cast hsumPosNat
  have heps : 0 < controllerDensity h /
          ((k + h.1 : Nat) : Real) :=
    div_pos (controllerDensity_pos h) hsumPosReal
  obtain ⟨z, hzsmall⟩ := exists_oldControllerPrimes_complementDensity_lt
      h hh hdiv heps
  have hH : ∀ p ∈ oldControllerPrimes h z,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hΔ : 0 < controllerComplementDensity h
          (oldControllerPrimes h z) :=
    controllerComplementDensity_pos
      h hh (oldControllerPrimes h z) hH
  obtain ⟨τ, hτpos, hkτ, hτh, hτδ⟩ := exists_density_window hΔ hkh hzsmall
  exact ⟨z, τ, hΔ, hτpos, hkτ, hτh, hτδ⟩

def reducedResidues (L : Prime) : Finset Nat := (Finset.range L.1).filter fun a => L.1.Coprime a

@[simp]
theorem mem_reducedResidues {L : Prime} {a : Nat} : a ∈ reducedResidues L ↔
      a < L.1 ∧ L.1.Coprime a := by
  simp [reducedResidues]

theorem card_reducedResidues (L : Prime) : (reducedResidues L).card = L.1 - 1 := by
  rw [reducedResidues, ← Nat.totient_eq_card_coprime]
  exact Nat.totient_prime L.natPrime

private theorem reducedResidueSubset_exists (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    ∃ R : Finset Nat,
      R ⊆ reducedResidues L ∧ R.card = m := by
  have hm' : m ≤ (reducedResidues L).card := by
    simpa [card_reducedResidues] using hm
  exact Finset.exists_subset_card_eq hm'

noncomputable def selectedReducedResidues (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) : Finset Nat :=
  Classical.choose (reducedResidueSubset_exists L m hm)

theorem selectedReducedResidues_subset (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    selectedReducedResidues L m hm ⊆
      reducedResidues L :=
  (Classical.choose_spec
    (reducedResidueSubset_exists L m hm)).1

theorem selectedReducedResidues_card (L : Prime) (m : Nat) (hm : m ≤ L.1 - 1) :
    (selectedReducedResidues L m hm).card = m :=
  (Classical.choose_spec
    (reducedResidueSubset_exists L m hm)).2

structure NumericalDensityMesh
    (δ Δ : Real) (k h avoid : Nat) where
  modulus : Prime
  index : Nat
  large : max avoid 2 < modulus.1
  coprime : modulus.1.Coprime avoid
  index_le : index ≤ modulus.1 - 1
  lower : (k : Real) * Δ < (index : Real) *
        (δ / ((modulus.1 : Real) - 1))
  upper_hub : (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      (h : Real) * Δ
  upper_half : (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      δ / 2

theorem numericalDensityMesh_nonempty {δ Δ : Real} {k h avoid : Nat} (L : Prime) (m : Nat)
    (hlarge : max avoid 2 < L.1)
    (hcoprime : L.1.Coprime avoid)
    (hm : m ≤ L.1 - 1)
    (hlower : (k : Real) * Δ < (m : Real) *
          (δ / ((L.1 : Real) - 1)))
    (hupper : (m : Real) *
          (δ / ((L.1 : Real) - 1)) <
        (h : Real) * Δ)
    (hhalf : (m : Real) *
          (δ / ((L.1 : Real) - 1)) <
        δ / 2) :
    Nonempty (NumericalDensityMesh δ Δ k h avoid) :=
  ⟨{
    modulus := L
    index := m
    large := hlarge
    coprime := hcoprime
    index_le := hm
    lower := hlower
    upper_hub := hupper
    upper_half := hhalf
  }⟩

structure ReducedClassDensityMesh
    (δ Δ : Real) (k h avoid : Nat) where
  modulus : Prime
  index : Nat
  classes : Finset Nat
  large : max avoid 2 < modulus.1
  coprime : modulus.1.Coprime avoid
  classes_reduced : classes ⊆ reducedResidues modulus
  card_classes : classes.card = index
  lower : (k : Real) * Δ < (index : Real) *
        (δ / ((modulus.1 : Real) - 1))
  upper_hub : (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      (h : Real) * Δ
  upper_half : (index : Real) *
        (δ / ((modulus.1 : Real) - 1)) <
      δ / 2

theorem exists_numerical_density_mesh {δ Δ τ : Real} {k h : Nat} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hkτ : (k : Real) * Δ < τ)
    (hτh : τ < (h : Real) * Δ)
    (hτδ : τ < δ / 2)
    (avoid : Nat) (havoid : 0 < avoid) :
    Nonempty (NumericalDensityMesh δ Δ k h avoid) := by
  classical
  let a : Real := (k : Real) * Δ
  let b : Real := min ((h : Real) * Δ) (δ / 2)
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hτb : τ < b := by
    dsimp [b]
    exact lt_min hτh hτδ
  have hab : a < b := by
    exact hkτ.trans hτb
  have hgap : 0 < b - a := sub_pos.mpr hab
  obtain ⟨L, hLlarge, hLcoprime, hmesh⟩ := exists_auxiliary_prime_with_fine_mesh
      hδ hgap avoid havoid
  have hLtwo : 2 < L.1 := (le_max_right avoid 2).trans_lt hLlarge
  have hden : (0 : Real) < (L.1 : Real) - 1 := by
    have hLtwoR : (2 : Real) < (L.1 : Real) := by
      exact_mod_cast hLtwo
    linarith
  let step : Real := δ / ((L.1 : Real) - 1)
  have hstep : 0 < step := by
    dsimp [step]
    exact div_pos hδ hden
  obtain ⟨m, hma, hmb⟩ := exists_nat_mul_mem_Ioo_of_step_lt
      ha hstep hmesh
  dsimp [step, a, b] at hma hmb
  have hbδ : b < δ := by
    calc
      b ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith
  have hmδ : (m : Real) *
          (δ / ((L.1 : Real) - 1)) < δ :=
    hmb.trans hbδ
  have hmdiv : (m : Real) * δ /
          ((L.1 : Real) - 1) < δ := by
    simpa [div_eq_mul_inv, mul_assoc] using hmδ
  have hmmul : (m : Real) * δ < δ * ((L.1 : Real) - 1) := by
    have := (div_lt_iff₀ hden).mp hmdiv
    simpa [mul_comm] using this
  have hmR : (m : Real) < (L.1 : Real) - 1 := by
    nlinarith
  have hmSuccR : (m : Real) + 1 < (L.1 : Real) := by
    linarith
  have hmSucc : m + 1 < L.1 := by
    exact_mod_cast hmSuccR
  have hmle : m ≤ L.1 - 1 := by
    omega
  have hmbSplit := (lt_min_iff.mp hmb)
  rcases hmbSplit with ⟨hupper, hhalf⟩
  refine @numericalDensityMesh_nonempty
      δ Δ k h avoid
      L m hLlarge hLcoprime hmle
      ?_ ?_ ?_
  · exact hma
  · exact hupper
  · assumption

theorem exists_reducedClasses_in_density_window {δ Δ τ : Real} {k h : Nat} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hkτ : (k : Real) * Δ < τ)
    (hτh : τ < (h : Real) * Δ)
    (hτδ : τ < δ / 2)
    (avoid : Nat) (havoid : 0 < avoid) :
    Nonempty (ReducedClassDensityMesh δ Δ k h avoid) := by
  obtain ⟨M⟩ := exists_numerical_density_mesh
      hδ hΔ hkτ hτh hτδ avoid havoid
  exact
    ⟨{
      modulus := M.modulus
      index := M.index
      classes :=
        selectedReducedResidues
          M.modulus M.index M.index_le
      large := M.large
      coprime := M.coprime
      classes_reduced :=
        selectedReducedResidues_subset
          M.modulus M.index M.index_le
      card_classes :=
        selectedReducedResidues_card
          M.modulus M.index M.index_le
      lower := M.lower
      upper_hub := M.upper_hub
      upper_half := M.upper_half
    }⟩

structure OldControllerPrimeDensityMesh
    (h : Prime) (k : Nat) where
  cutoff : Nat
  modulus : Prime
  index : Nat
  classes : Finset Nat
  large : max
        (h.1 *
          primeSubsetModulus
            (oldControllerPrimes h cutoff)) 2 <
      modulus.1
  coprime : modulus.1.Coprime
      (h.1 *
        primeSubsetModulus
          (oldControllerPrimes h cutoff))
  classes_reduced : classes ⊆ reducedResidues modulus
  card_classes : classes.card = index
  lower : (k : Real) *
        controllerComplementDensity h
          (oldControllerPrimes h cutoff) <
      (index : Real) *
        (controllerDensity h /
          ((modulus.1 : Real) - 1))
  upper_hub : (index : Real) *
        (controllerDensity h /
          ((modulus.1 : Real) - 1)) <
      (h.1 : Real) *
        controllerComplementDensity h
          (oldControllerPrimes h cutoff)
  upper_half : (index : Real) *
        (controllerDensity h /
          ((modulus.1 : Real) - 1)) <
      controllerDensity h / 2

theorem exists_oldControllerPrime_reducedClass_mesh (h : Prime) (hh : 3 ≤ h.1)
    (k : Nat) (hkh : k < h.1)
    (hdiv : ControllerPrimeReciprocalDiverges h) :
    Nonempty (OldControllerPrimeDensityMesh h k) := by
  obtain ⟨z, τ, hΔ, _hτpos, hkτ, hτh, hτδ⟩ := exists_oldControllerPrimes_density_window
      h hh k hkh hdiv
  let avoid : Nat := h.1 *
      primeSubsetModulus
        (oldControllerPrimes h z)
  have havoid : 0 < avoid := by
    dsimp [avoid]
    exact Nat.mul_pos h.natPrime.pos
        (primeSubsetModulus_pos
          (oldControllerPrimes h z))
  obtain ⟨M⟩ := exists_reducedClasses_in_density_window
      (controllerDensity_pos h) hΔ
      hkτ hτh hτδ avoid havoid
  exact
    ⟨{
      cutoff := z
      modulus := M.modulus
      index := M.index
      classes := M.classes
      large := M.large
      coprime := M.coprime
      classes_reduced := M.classes_reduced
      card_classes := M.card_classes
      lower := M.lower
      upper_hub := M.upper_hub
      upper_half := M.upper_half
    }⟩

end Erdos279
end

section

namespace Erdos279

noncomputable def periodicCrtClass (h L : Prime) (hcop : h.1.Coprime L.1) (c : Nat) : Nat :=
  (Nat.chineseRemainder hcop 1 c).1

theorem periodicCrtClass_modEq_h (h L : Prime) (hcop : h.1.Coprime L.1) (c : Nat) :
    periodicCrtClass h L hcop c ≡ 1 [MOD h.1] := by
  simpa [periodicCrtClass] using (Nat.chineseRemainder hcop 1 c).2.1

theorem periodicCrtClass_modEq_aux (h L : Prime) (hcop : h.1.Coprime L.1) (c : Nat) :
    periodicCrtClass h L hcop c ≡ c [MOD L.1] := by
  simpa [periodicCrtClass] using (Nat.chineseRemainder hcop 1 c).2.2

theorem periodicCrtClass_coprime_h (h L : Prime) (hcop : h.1.Coprime L.1) (c : Nat) :
    (periodicCrtClass h L hcop c).Coprime h.1 := by
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd (periodicCrtClass h L hcop c) h.1 = Nat.gcd h.1 (periodicCrtClass h L hcop c) :=
      Nat.gcd_comm _ _
    _ = Nat.gcd
          ((periodicCrtClass h L hcop c) % h.1)
          h.1 :=
      Nat.gcd_rec h.1
        (periodicCrtClass h L hcop c)
    _ = Nat.gcd (1 % h.1) h.1 := by
      rw [periodicCrtClass_modEq_h]
    _ = Nat.gcd 1 h.1 := by
      rw [Nat.mod_eq_of_lt h.one_lt]
    _ = 1 := Nat.gcd_one_left h.1

theorem periodicCrtClass_coprime_aux (h L : Prime) (hcop : h.1.Coprime L.1)
    {c : Nat} (hc : c ∈ reducedResidues L) :
    (periodicCrtClass h L hcop c).Coprime L.1 := by
  have hcCoprime : c.Coprime L.1 := (mem_reducedResidues.mp hc).2.symm
  rw [Nat.coprime_iff_gcd_eq_one]
  calc
    Nat.gcd (periodicCrtClass h L hcop c) L.1 = Nat.gcd L.1 (periodicCrtClass h L hcop c) :=
      Nat.gcd_comm _ _
    _ = Nat.gcd
          ((periodicCrtClass h L hcop c) % L.1)
          L.1 :=
      Nat.gcd_rec L.1
        (periodicCrtClass h L hcop c)
    _ = Nat.gcd (c % L.1) L.1 := by
      rw [periodicCrtClass_modEq_aux]
    _ = Nat.gcd L.1 c := (Nat.gcd_rec L.1 c).symm
    _ = Nat.gcd c L.1 := Nat.gcd_comm _ _
    _ = 1 := hcCoprime.gcd_eq_one

theorem periodicCrtClass_coprime_modulus (h L : Prime) (hcop : h.1.Coprime L.1)
    {c : Nat} (hc : c ∈ reducedResidues L) :
    (periodicCrtClass h L hcop c).Coprime
      (h.1 * L.1) := by
  exact Nat.coprime_mul_iff_right.mpr
    ⟨periodicCrtClass_coprime_h h L hcop c,
      periodicCrtClass_coprime_aux h L hcop hc⟩

theorem modEq_periodicCrtClass_iff (h L : Prime) (hcop : h.1.Coprime L.1) (c n : Nat) :
    n ≡ periodicCrtClass h L hcop c
        [MOD h.1 * L.1] ↔
      n ≡ 1 [MOD h.1] ∧ n ≡ c [MOD L.1] := by
  constructor
  · intro hn
    constructor
    · exact (hn.of_mul_right L.1).trans
          (periodicCrtClass_modEq_h h L hcop c)
    · exact (hn.of_mul_left h.1).trans
          (periodicCrtClass_modEq_aux h L hcop c)
  · rintro ⟨hnh, hnL⟩
    exact Nat.chineseRemainder_modEq_unique
        hcop hnh hnL

def InPeriodicPrimePool (h L : Prime) (R : Finset Nat) (p : Prime) : Prop :=
  InControllerProgression h p ∧ p.1 % L.1 ∈ R

def InPeriodicReservoir (h L : Prime) (R : Finset Nat) (H : Finset Prime) (p : Prime) : Prop :=
  InPeriodicPrimePool h L R p ∧ p ∉ H

def InControllerReservoir (h L : Prime) (R : Finset Nat) (H : Finset Prime) (p : Prime) : Prop :=
  InControllerProgression h p ∧ p ∉ H ∧ ¬ InPeriodicPrimePool h L R p

theorem inPeriodicPrimePool_iff_exists_modEq (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (p : Prime) :
    InPeriodicPrimePool h L R p ↔ ∃ c ∈ R,
        p.1 ≡ periodicCrtClass h L hcop c
          [MOD h.1 * L.1] := by
  constructor
  · rintro ⟨hph, hpR⟩
    refine ⟨p.1 % L.1, hpR, ?_⟩
    apply (modEq_periodicCrtClass_iff h L hcop _ _).2
    constructor
    · simpa [InControllerProgression, Nat.ModEq,
        Nat.mod_eq_of_lt h.one_lt] using hph
    · simp [Nat.ModEq]
  · rintro ⟨c, hcR, hpc⟩
    have hcRed : c ∈ reducedResidues L := hR hcR
    have hcLt : c < L.1 := (mem_reducedResidues.mp hcRed).1
    have hpair := (modEq_periodicCrtClass_iff h L hcop c p.1).1 hpc
    constructor
    · simpa [InControllerProgression, Nat.ModEq,
        Nat.mod_eq_of_lt h.one_lt] using hpair.1
    · have hmod : p.1 % L.1 = c := by
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hcLt] using hpair.2
      simpa [hmod] using hcR

theorem inPeriodicReservoir_iff (h L : Prime) (R : Finset Nat) (H : Finset Prime) (p : Prime) :
    InPeriodicReservoir h L R H p ↔ InControllerProgression h p ∧ p ∉ H ∧ p.1 % L.1 ∈ R := by
  constructor
  · rintro ⟨⟨hpG, hpR⟩, hpH⟩
    exact ⟨hpG, hpH, hpR⟩
  · rintro ⟨hpG, hpH, hpR⟩
    exact ⟨⟨hpG, hpR⟩, hpH⟩

theorem inControllerReservoir_iff (h L : Prime) (R : Finset Nat) (H : Finset Prime) (p : Prime) :
    InControllerReservoir h L R H p ↔ InControllerProgression h p ∧ p ∉ H ∧ p.1 % L.1 ∉ R := by
  constructor
  · rintro ⟨hpG, hpH, hpNotT⟩
    refine ⟨hpG, hpH, ?_⟩
    intro hpR
    exact hpNotT ⟨hpG, hpR⟩
  · rintro ⟨hpG, hpH, hpR⟩
    refine ⟨hpG, hpH, ?_⟩
    rintro ⟨_hpG, hpInR⟩
    exact hpR hpInR

theorem not_inPeriodic_and_inControllerReservoir (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (p : Prime) :
    ¬ (InPeriodicReservoir h L R H p ∧ InControllerReservoir h L R H p) := by
  rintro ⟨hpT, hpS⟩
  have hpR := ((inPeriodicReservoir_iff h L R H p).1 hpT).2.2
  have hpNotR := ((inControllerReservoir_iff h L R H p).1 hpS).2.2
  exact hpNotR hpR

theorem InPeriodicReservoir.inControllerProgression {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InPeriodicReservoir h L R H p) :
    InControllerProgression h p :=
  (inPeriodicReservoir_iff h L R H p).1 hp |>.1

theorem InControllerReservoir.inControllerProgression {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InControllerReservoir h L R H p) :
    InControllerProgression h p :=
  (inControllerReservoir_iff h L R H p).1 hp |>.1

theorem InPeriodicReservoir.not_mem_old {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InPeriodicReservoir h L R H p) :
    p ∉ H :=
  (inPeriodicReservoir_iff h L R H p).1 hp |>.2.1

theorem InControllerReservoir.not_mem_old {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {p : Prime}
    (hp : InControllerReservoir h L R H p) :
    p ∉ H :=
  (inControllerReservoir_iff h L R H p).1 hp |>.2.1

theorem OldControllerPrimeDensityMesh.hub_coprime_modulus {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    h.1.Coprime M.modulus.1 := by
  have hLh : M.modulus.1.Coprime h.1 := (Nat.coprime_mul_iff_right.mp M.coprime).1
  exact hLh.symm

end Erdos279
end

section

namespace Erdos279

structure PrimeTargetPair where
  controller : Prime
  target : Prime

namespace PrimeTargetPair

def residue (s : PrimeTargetPair) : Fin s.controller.1 := controllerResidue s.controller s.target.1

def Admissible (k : Nat) (s : PrimeTargetPair) : Prop := k * s.controller.1 < s.target.1

theorem controller_lt_target {k : Nat} {s : PrimeTargetPair} (hk : 0 < k) (hs : s.Admissible k) :
    s.controller.1 < s.target.1 := by
  have hp_le_kp : s.controller.1 ≤ k * s.controller.1 := by
    have hkone : 1 ≤ k := hk
    simpa using Nat.mul_le_mul_right s.controller.1 hkone
  exact Nat.lt_of_le_of_lt hp_le_kp hs

theorem residue_ne_zero {k : Nat} {s : PrimeTargetPair} (hk : 0 < k) (hs : s.Admissible k) :
    (s.residue : Nat) ≠ 0 :=
  prime_mod_prime_ne_zero_of_lt (s.controller_lt_target hk hs)

theorem mature {k : Nat} {s : PrimeTargetPair} (hs : s.Admissible k) :
    k * s.controller.1 ≤ s.target.1 + 1 :=
  Nat.le_trans (Nat.le_of_lt hs) (Nat.le_add_right _ _)

theorem covers_of_assignment {k : Nat} {s : PrimeTargetPair} {a : ShiftedAssignment}
    (hs : s.Admissible k)
    (ha : (a s.controller : Nat) = (s.residue : Nat)) :
    ShiftedMatureCovers k s.target.1 a :=
  controller_pair_covers (s.mature hs) ha

end PrimeTargetPair

structure PrimeTargetMatching (ι : Type) (k : Nat) where
  pair : ι → PrimeTargetPair
  controller_injective : Function.Injective (fun i => (pair i).controller)
  target_injective : Function.Injective (fun i => (pair i).target)
  admissible : ∀ i : ι, (pair i).Admissible k

namespace PrimeTargetMatching

abbrev Sequence (k : Nat) := PrimeTargetMatching Nat k

def ControllersIn {ι : Type} {k : Nat} (M : PrimeTargetMatching ι k) (h : Prime) : Prop :=
  ∀ i : ι, InControllerProgression h (M.pair i).controller

noncomputable def assignment {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p => if h : ∃ i : ι, (M.pair i).controller = p then
      controllerResidue p (M.pair (Classical.choose h)).target.1
    else
      base p

theorem assignment_at_controller {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (i : ι) :
    M.assignment base (M.pair i).controller = (M.pair i).residue := by
  let hex : ∃ j : ι, (M.pair j).controller = (M.pair i).controller := ⟨i, rfl⟩
  rw [assignment]
  simp only [dif_pos hex]
  have hchosen : (M.pair (Classical.choose hex)).controller = (M.pair i).controller :=
    Classical.choose_spec hex
  have hindex : Classical.choose hex = i := M.controller_injective hchosen
  rw [hindex]
  rfl

theorem assignment_of_unmatched {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (p : Prime)
    (hp : ∀ i : ι, (M.pair i).controller ≠ p) :
    M.assignment base p = base p := by
  have hnone : ¬ ∃ i : ι, (M.pair i).controller = p := by
    intro hex
    rcases hex with ⟨i, hi⟩
    exact hp i hi
  rw [assignment]
  simp only [dif_neg hnone]

theorem assignment_at_hub {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (h : Prime) (hcontrollers : M.ControllersIn h) :
    M.assignment base h = base h := by
  apply M.assignment_of_unmatched
  intro i hi
  have hne : (M.pair i).controller ≠ h := inControllerProgression_ne_hub (hcontrollers i)
  exact hne hi

theorem assignment_of_not_in_progression {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    {h q : Prime}
    (hcontrollers : M.ControllersIn h)
    (hqout : ¬ InControllerProgression h q) :
    M.assignment base q = base q := by
  apply M.assignment_of_unmatched
  intro i hi
  apply hqout
  rw [← hi]
  exact hcontrollers i

theorem assignment_at_controller_ne_zero {ι : Type} {k : Nat}
    (M : PrimeTargetMatching ι k) (base : ShiftedAssignment)
    (hk : 0 < k) (i : ι) :
    (M.assignment base (M.pair i).controller : Nat) ≠ 0 := by
  rw [M.assignment_at_controller base i]
  exact (M.pair i).residue_ne_zero hk (M.admissible i)

end PrimeTargetMatching

end Erdos279
end

section

namespace Erdos279

open Filter

def IsComplementaryPrimeTarget (h : Prime) (H : Finset Prime) (q : Prime) : Prop :=
  ¬ InControllerProgression h q ∧ ∀ ℓ ∈ H, q.1 % ℓ.1 ≠ 1

theorem eventually_controller_target_gap {p q : Nat → Prime} {k h : Nat} {r : Real}
    (hk : 0 < k) (hh : 0 < h)
    (hratio : Tendsto
        (fun i => ((p i).1 : Real) / ((q i).1 : Real))
        atTop (nhds r))
    (hlower : 1 / (h : Real) < r)
    (hupper : r < 1 / (k : Real)) :
    ∀ᶠ i in atTop,
      k * (p i).1 < (q i).1 ∧ (q i).1 < h * (p i).1 := by
  have heventLower : ∀ᶠ i in atTop,
        1 / (h : Real) < ((p i).1 : Real) / ((q i).1 : Real) :=
    hratio.eventually_const_lt hlower
  have heventUpper : ∀ᶠ i in atTop,
        ((p i).1 : Real) / ((q i).1 : Real) < 1 / (k : Real) :=
    hratio.eventually_lt_const hupper
  filter_upwards [heventLower, heventUpper] with i hiLower hiUpper
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast hk
  have hhR : (0 : Real) < (h : Real) := by
    exact_mod_cast hh
  have hqR : (0 : Real) < ((q i).1 : Real) := by
    exact_mod_cast (q i).pos
  have hcrossUpper : ((p i).1 : Real) * (k : Real) < (1 : Real) * ((q i).1 : Real) :=
    (div_lt_div_iff₀ hqR hkR).mp hiUpper
  have hcrossLower : (1 : Real) * ((q i).1 : Real) < ((p i).1 : Real) * (h : Real) :=
    (div_lt_div_iff₀ hhR hqR).mp hiLower
  have hcrossUpper' : (k : Real) * ((p i).1 : Real) < ((q i).1 : Real) := by
    simpa [mul_comm] using hcrossUpper
  have hcrossLower' : ((q i).1 : Real) < (h : Real) * ((p i).1 : Real) := by
    simpa [mul_comm] using hcrossLower
  constructor
  · exact_mod_cast hcrossUpper'
  · exact_mod_cast hcrossLower'

structure TailPrimeTargetMatching
    (p q : Nat → Prime) (k : Nat) where
  offset : Nat
  matching : PrimeTargetMatching.Sequence k
  pair_eq : ∀ i,
      matching.pair i =
        { controller := p (offset + i)
          target := q (offset + i) }

theorem exists_tailPrimeTargetMatching_of_ratio {p q : Nat → Prime} {k h : Nat} {r : Real}
    (hpInjective : Function.Injective p)
    (hqInjective : Function.Injective q)
    (hk : 0 < k) (hh : 0 < h)
    (hratio : Tendsto
        (fun i => ((p i).1 : Real) / ((q i).1 : Real))
        atTop (nhds r))
    (hlower : 1 / (h : Real) < r)
    (hupper : r < 1 / (k : Real)) :
    Nonempty (TailPrimeTargetMatching p q k) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
      (eventually_controller_target_gap
        hk hh hratio hlower hupper)
  let M : PrimeTargetMatching.Sequence k :=
    { pair := fun i =>
        { controller := p (N + i)
          target := q (N + i) }
      controller_injective := by
        intro i j hij
        dsimp at hij
        exact Nat.add_left_cancel (hpInjective hij)
      target_injective := by
        intro i j hij
        dsimp at hij
        exact Nat.add_left_cancel (hqInjective hij)
      admissible := by
        intro i
        exact (hN (N + i) (Nat.le_add_right N i)).1 }
  exact ⟨
      { offset := N
        matching := M
        pair_eq := fun _ => rfl }⟩

structure PeriodicComplementaryEnumerations
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) where
  periodic : Nat → Prime
  complementary : Nat → Prime
  periodic_injective : Function.Injective periodic
  complementary_injective : Function.Injective complementary
  periodic_mem : ∀ i, InPeriodicReservoir h L R H (periodic i)
  complementary_mem : ∀ i, IsComplementaryPrimeTarget h H (complementary i)
  complementary_surjective : ∀ q, IsComplementaryPrimeTarget h H q → ∃ i, complementary i = q
  ratio : Real
  ratio_tendsto : Tendsto
      (fun i => ((periodic i).1 : Real) /
          ((complementary i).1 : Real))
      atTop (nhds ratio)

namespace PeriodicComplementaryEnumerations

def primePrefixBound (q : Nat → Prime) (N : Nat) : Nat := (Finset.range N).sup fun i => (q i).1 + 1

theorem index_ge_of_primePrefixBound_le (q : Nat → Prime) (N i : Nat) (hi :
      primePrefixBound q N ≤ (q i).1) :
    N ≤ i := by
  by_contra hnot
  have hiN : i < N := Nat.lt_of_not_ge hnot
  have hle : (q i).1 + 1 ≤ primePrefixBound q N := by
    simpa [primePrefixBound] using (Finset.le_sup
        (s := Finset.range N)
        (f := fun j : Nat => (q j).1 + 1)
        (Finset.mem_range.mpr hiN))
  omega

theorem exists_tailMatching {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat} (hk : 0 < k)
    (hlower : 1 / (h.1 : Real) < E.ratio)
    (hupper : E.ratio < 1 / (k : Real)) :
    Nonempty
      (TailPrimeTargetMatching
        E.periodic E.complementary k) := by
  exact exists_tailPrimeTargetMatching_of_ratio
      (p := E.periodic) (q := E.complementary)
      (k := k) (h := h.1) (r := E.ratio)
      E.periodic_injective E.complementary_injective
      hk h.pos E.ratio_tendsto hlower hupper

theorem tailMatching_controllersIn {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    T.matching.ControllersIn h := by
  intro i
  rw [T.pair_eq i]
  exact (E.periodic_mem (T.offset + i)).inControllerProgression

end PeriodicComplementaryEnumerations

end Erdos279
end

section

namespace Erdos279

def hubOldPrimeAssignment (h : Prime) (H : Finset Prime) : ShiftedAssignment := fun p =>
    if _hp : p = h ∨ p ∈ H then
      ⟨1, p.one_lt⟩
    else
      ⟨0, p.pos⟩

@[simp]
theorem hubOldPrimeAssignment_hub (h : Prime) (H : Finset Prime) :
    (hubOldPrimeAssignment h H h : Nat) = 1 := by
  simp [hubOldPrimeAssignment]

@[simp]
theorem hubOldPrimeAssignment_old (h : Prime) (H : Finset Prime) {p : Prime} (hp : p ∈ H) :
    (hubOldPrimeAssignment h H p : Nat) = 1 := by
  simp [hubOldPrimeAssignment, hp]

theorem hubOldPrimeAssignment_zero (h : Prime) (H : Finset Prime)
    {p : Prime} (hph : p ≠ h) (hpH : p ∉ H) :
    (hubOldPrimeAssignment h H p : Nat) = 0 := by
  simp [hubOldPrimeAssignment, hph, hpH]

def oldPrimeMaturityBound (k : Nat) (H : Finset Prime) : Nat := H.sup fun ℓ => k * ℓ.1

theorem oldPrimeMaturity_le (k : Nat) (H : Finset Prime) {ℓ : Prime} (hℓ : ℓ ∈ H) :
    k * ℓ.1 ≤ oldPrimeMaturityBound k H := by
  simpa [oldPrimeMaturityBound] using (Finset.le_sup
      (s := H) (f := fun q : Prime => k * q.1) hℓ)

namespace PeriodicComplementaryEnumerations

noncomputable def primeTargetAssignment {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    ShiftedAssignment :=
  T.matching.assignment (hubOldPrimeAssignment h H)

theorem primeTargetAssignment_hub {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k) :
    (E.primeTargetAssignment T h : Nat) = 1 := by
  rw [primeTargetAssignment,
    T.matching.assignment_at_hub
      (hubOldPrimeAssignment h H) h
      (E.tailMatching_controllersIn T)]
  exact hubOldPrimeAssignment_hub h H

theorem primeTargetAssignment_old {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    {ℓ : Prime} (hℓ : ℓ ∈ H) :
    (E.primeTargetAssignment T ℓ : Nat) = 1 := by
  rw [primeTargetAssignment]
  rw [T.matching.assignment_of_unmatched
    (hubOldPrimeAssignment h H) ℓ]
  · exact hubOldPrimeAssignment_old h H hℓ
  · intro i hi
    have hnotOld := (E.periodic_mem (T.offset + i)).not_mem_old
    rw [T.pair_eq i] at hi
    change E.periodic (T.offset + i) = ℓ at hi
    exact hnotOld (hi.symm ▸ hℓ)

theorem primeTargetAssignment_outside_zero {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    (E : PeriodicComplementaryEnumerations h L R H)
    (hH : ∀ ℓ ∈ H, InControllerProgression h ℓ)
    {k : Nat}
    (T : TailPrimeTargetMatching
      E.periodic E.complementary k)
    (q : Prime) (hqh : q ≠ h)
    (hqG : ¬ InControllerProgression h q) :
    (E.primeTargetAssignment T q : Nat) = 0 := by
  rw [primeTargetAssignment,
    T.matching.assignment_of_not_in_progression
      (hubOldPrimeAssignment h H)
      (E.tailMatching_controllersIn T) hqG]
  apply hubOldPrimeAssignment_zero h H hqh
  intro hqH
  exact hqG (hH q hqH)

end PeriodicComplementaryEnumerations

end Erdos279
end

section

namespace Erdos279

theorem zero_class_covers_factor {k m : Nat} {q : Prime} {a : ShiftedAssignment} (hqdiv : q.1 ∣ m)
    (hqMature : k * q.1 ≤ m)
    (haq : (a q : Nat) = 0) :
    ShiftedMatureCovers k m a := by
  refine ⟨q, Nat.le_trans hqMature (Nat.le_add_right m 1), ?_⟩
  rw [haq]
  exact Nat.mod_eq_zero_of_dvd hqdiv

theorem smallOutside_covered_by_zero_classes {k m : Nat} {h : Prime} {a : ShiftedAssignment}
    (hzero : ∀ q : Prime, q ≠ h → ¬ InControllerProgression h q → (a q : Nat) = 0)
    (houtside : HasSmallOutsideFactor k h m) :
    ShiftedMatureCovers k m a := by
  rcases houtside with ⟨q, hqdiv, hqne, hqG, hqMature⟩
  exact zero_class_covers_factor hqdiv hqMature (hzero q hqne hqG)

end Erdos279
end

section

namespace Erdos279

def elementaryCompletionThreshold (k constructionThreshold : Nat) (h : Prime) : Nat :=
  max constructionThreshold (max 1 (max (k * h.1) (k * k + 1)))

theorem constructionThreshold_le_elementary (k constructionThreshold : Nat) (h : Prime) :
    constructionThreshold ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_max_left _ _

theorem one_le_elementaryCompletionThreshold (k constructionThreshold : Nat) (h : Prime) :
    1 ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_trans
    (Nat.le_max_left 1 (max (k * h.1) (k * k + 1)))
    (Nat.le_max_right constructionThreshold
      (max 1 (max (k * h.1) (k * k + 1))))

theorem hubMaturity_le_elementaryThreshold (k constructionThreshold : Nat) (h : Prime) :
    k * h.1 ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_trans
    (Nat.le_max_left (k * h.1) (k * k + 1))
    (Nat.le_trans
      (Nat.le_max_right 1 (max (k * h.1) (k * k + 1)))
      (Nat.le_max_right constructionThreshold
        (max 1 (max (k * h.1) (k * k + 1)))))

theorem squareSucc_le_elementaryThreshold (k constructionThreshold : Nat) (h : Prime) :
    k * k + 1 ≤ elementaryCompletionThreshold k constructionThreshold h :=
  Nat.le_trans
    (Nat.le_max_right (k * h.1) (k * k + 1))
    (Nat.le_trans
      (Nat.le_max_right 1 (max (k * h.1) (k * k + 1)))
      (Nat.le_max_right constructionThreshold
        (max 1 (max (k * h.1) (k * k + 1)))))

def completionData_of_hardForm_and_prime {k : Nat} (hk : 3 ≤ k) (h : Prime) (hkh : k < h.1)
    (a : ShiftedAssignment)
    (constructionThreshold : Nat)
    (hhub : (a h : Nat) = 1)
    (hzero : ∀ q : Prime, q ≠ h → ¬ InControllerProgression h q → (a q : Nat) = 0)
    (hhard : ∀ m : Nat, constructionThreshold ≤ m → HasHardForm h m → ShiftedMatureCovers k m a)
    (hprime : ∀ m : Nat, constructionThreshold ≤ m → IsPrime m → ShiftedMatureCovers k m a) :
    CompletionData k where
  hub := h
  shifted := a
  threshold := elementaryCompletionThreshold k constructionThreshold h
  smooth_noHub := by
    intro m hm hsmooth hnotHub
    apply smoothFor_noHub_covered_by_hub hsmooth hnotHub hhub
    have hhubBound : k * h.1 ≤ elementaryCompletionThreshold
          k constructionThreshold h :=
      hubMaturity_le_elementaryThreshold k constructionThreshold h
    exact Nat.le_trans hhubBound
      (Nat.le_trans hm (Nat.le_add_right m 1))
  hard := by
    intro m hm htarget
    apply hhard m
    · exact Nat.le_trans
        (constructionThreshold_le_elementary k constructionThreshold h)
        hm
    · apply hardTarget_hasHardForm
      · have hmone : 1 ≤ m := Nat.le_trans
            (one_le_elementaryCompletionThreshold
              k constructionThreshold h)
            hm
        omega
      · exact htarget
  smallOutside := by
    intro m _ houtside
    exact smallOutside_covered_by_zero_classes hzero houtside
  outsideLarge_isPrime := by
    intro m hm hnonsmooth hnosmall
    apply Erdos279.outsideLarge_isPrime hk hkh _ hnonsmooth hnosmall
    have hbound : k * k + 1 ≤ elementaryCompletionThreshold
          k constructionThreshold h :=
      squareSucc_le_elementaryThreshold k constructionThreshold h
    omega
  primeTarget := by
    intro m hm hp
    apply hprime m _ hp
    exact Nat.le_trans
      (constructionThreshold_le_elementary k constructionThreshold h)
      hm

end Erdos279
end

section

namespace Erdos279

structure PaperConstructionCore (k : Nat) where
  hub : Prime
  hub_gt_level : k < hub.1
  shifted : ShiftedAssignment
  threshold : Nat
  hub_residue : (shifted hub : Nat) = 1
  outside_zero : ∀ q : Prime, q ≠ hub → ¬ InControllerProgression hub q → (shifted q : Nat) = 0
  hardForm : ∀ m : Nat, threshold ≤ m → HasHardForm hub m → ShiftedMatureCovers k m shifted
  primeTarget : ∀ m : Nat, threshold ≤ m → IsPrime m → ShiftedMatureCovers k m shifted

def PaperConstructionCore.toCompletionData {k : Nat} (D : PaperConstructionCore k) (hk : 3 ≤ k) :
    CompletionData k :=
  completionData_of_hardForm_and_prime
    hk D.hub D.hub_gt_level D.shifted D.threshold
    D.hub_residue D.outside_zero D.hardForm D.primeTarget

theorem P_of_paperConstructionCore {k : Nat} (hk : 3 ≤ k) (D : PaperConstructionCore k) : P k :=
  P_of_completionData (D.toCompletionData hk)

end Erdos279
end

section

namespace Erdos279

def finiteCapacityInjection {survivorCount reservoirCount : Nat}
    (h : survivorCount ≤ reservoirCount) :
    Fin survivorCount → Fin reservoirCount :=
  Fin.castLE h

theorem finiteCapacityInjection_injective {survivorCount reservoirCount : Nat}
    (h : survivorCount ≤ reservoirCount) :
    Function.Injective (finiteCapacityInjection h) := by
  intro i₁ i₂ heq
  apply Fin.ext
  simpa [finiteCapacityInjection] using congrArg (fun x : Fin reservoirCount => x.val) heq

end Erdos279
end

section

namespace Erdos279

noncomputable def controllerReservoirAnnulus (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) :
    Finset Prime := by
  classical
  exact ((Finset.Ioc Y Z).subtype IsPrime).filter
      (InControllerReservoir h L R H)

@[simp]
theorem mem_controllerReservoirAnnulus {h L : Prime} {R : Finset Nat} {H : Finset Prime} {Y Z : Nat}
    {p : Prime} :
    p ∈ controllerReservoirAnnulus h L R H Y Z ↔ Y < p.1 ∧ p.1 ≤ Z ∧
        InControllerReservoir h L R H p := by
  classical
  simp [controllerReservoirAnnulus, and_assoc]

noncomputable def enumeratePrimeFinset (s : Finset Prime) : Fin s.card → Prime :=
  fun i => (s.equivFin.symm i).1

theorem enumeratePrimeFinset_injective (s : Finset Prime) :
    Function.Injective (enumeratePrimeFinset s) := by
  intro i j hij
  apply s.equivFin.symm.injective
  apply Subtype.ext
  exact hij

theorem enumeratePrimeFinset_mem (s : Finset Prime) (i : Fin s.card) :
    enumeratePrimeFinset s i ∈ s :=
  (s.equivFin.symm i).2

theorem controllerReservoirAnnulus_disjoint (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    {Y₁ Z₁ Y₂ Z₂ : Nat}
    (hsep : Z₁ ≤ Y₂) :
    Disjoint
      (controllerReservoirAnnulus h L R H Y₁ Z₁)
      (controllerReservoirAnnulus h L R H Y₂ Z₂) := by
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  have hp₁' := (mem_controllerReservoirAnnulus.mp hp₁).2.1
  have hp₂' := (mem_controllerReservoirAnnulus.mp hp₂).1
  omega

noncomputable def hardStageControllerAnnulus (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (k X Xnext : Nat) : Finset Prime :=
  controllerReservoirAnnulus h L R H
    (Xnext / h.1) (X / k)

@[simp]
theorem mem_hardStageControllerAnnulus {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {k X Xnext : Nat} {p : Prime} :
    p ∈ hardStageControllerAnnulus
        h L R H k X Xnext ↔
      Xnext / h.1 < p.1 ∧ p.1 ≤ X / k ∧ InControllerReservoir h L R H p := by
  simp [hardStageControllerAnnulus]

theorem hardStageControllerAnnulus_in_progression {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {k X Xnext : Nat} {p : Prime}
    (hp : p ∈ hardStageControllerAnnulus
      h L R H k X Xnext) :
    InControllerProgression h p :=
  (mem_hardStageControllerAnnulus.mp hp).2.2
    |>.inControllerProgression

theorem hardStageControllerAnnulus_upper {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {k X Xnext : Nat} {p : Prime}
    (hp : p ∈ hardStageControllerAnnulus
      h L R H k X Xnext) :
    p.1 ≤ X / k :=
  (mem_hardStageControllerAnnulus.mp hp).2.1

theorem hardStageControllerAnnulus_above_target_div_hub {h L : Prime} {R : Finset Nat}
    {H : Finset Prime}
    {k X Xnext m : Nat} {p : Prime}
    (hp : p ∈ hardStageControllerAnnulus
      h L R H k X Xnext)
    (hm : m ≤ Xnext) :
    m / h.1 < p.1 := by
  exact (Nat.div_le_div_right hm).trans_lt
      (mem_hardStageControllerAnnulus.mp hp).1

theorem hardStageControllerAnnuli_pairwise_disjoint (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (k : Nat)
    (scale : Nat → Nat)
    (hmono : Monotone scale)
    (hsep : ∀ i,
        scale i / k ≤ scale (i + 2) / h.1) :
    ∀ i j, i ≠ j → Disjoint
        (hardStageControllerAnnulus
          h L R H k (scale i) (scale (i + 1)))
        (hardStageControllerAnnulus
          h L R H k (scale j) (scale (j + 1))) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hijScale : scale (i + 2) ≤ scale (j + 1) := by
      apply hmono
      omega
    have hbound : scale i / k ≤ scale (j + 1) / h.1 :=
      (hsep i).trans (Nat.div_le_div_right hijScale)
    exact controllerReservoirAnnulus_disjoint
        h L R H hbound
  · have hjiScale : scale (j + 2) ≤ scale (i + 1) := by
      apply hmono
      omega
    have hbound : scale j / k ≤ scale (i + 1) / h.1 :=
      (hsep j).trans (Nat.div_le_div_right hjiScale)
    exact (controllerReservoirAnnulus_disjoint
        h L R H hbound).symm

end Erdos279
end

section

namespace Erdos279

noncomputable def enumerateNatFinset (s : Finset Nat) : Fin s.card → Nat :=
  fun i => (s.equivFin.symm i).1

theorem enumerateNatFinset_injective (s : Finset Nat) :
    Function.Injective (enumerateNatFinset s) := by
  intro i j hij
  apply s.equivFin.symm.injective
  apply Subtype.ext
  exact hij

theorem enumerateNatFinset_mem (s : Finset Nat) (i : Fin s.card) : enumerateNatFinset s i ∈ s :=
  (s.equivFin.symm i).2

structure HardStagePairing
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z k X Xnext : Nat)
    (a : OldPrimeClasses h z) where
  target : Fin (hardSurvivors h z a X Xnext).card → Nat
  controller : Fin (hardSurvivors h z a X Xnext).card → Prime
  target_injective : Function.Injective target
  controller_injective : Function.Injective controller
  target_mem : ∀ i, target i ∈ hardSurvivors h z a X Xnext
  target_surjective : ∀ m ∈ hardSurvivors h z a X Xnext,
      ∃ i, target i = m
  controller_mem : ∀ i, controller i ∈ hardStageControllerAnnulus h L R H k X Xnext

noncomputable def hardStagePairingOfCardLe (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z k X Xnext : Nat)
    (a : OldPrimeClasses h z)
    (hcapacity : (hardSurvivors h z a X Xnext).card ≤ (hardStageControllerAnnulus
          h L R H k X Xnext).card) :
    HardStagePairing h L R H z k X Xnext a := by
  let survivors := hardSurvivors h z a X Xnext
  let annulus := hardStageControllerAnnulus h L R H k X Xnext
  exact
    { target := enumerateNatFinset survivors
      controller := fun i =>
        enumeratePrimeFinset annulus
          (finiteCapacityInjection hcapacity i)
      target_injective :=
        enumerateNatFinset_injective survivors
      controller_injective := by
        apply Function.Injective.comp
          (enumeratePrimeFinset_injective annulus)
        exact finiteCapacityInjection_injective hcapacity
      target_mem := enumerateNatFinset_mem survivors
      target_surjective := by
        intro m hm
        let x : survivors := ⟨m, hm⟩
        refine ⟨survivors.equivFin x, ?_⟩
        change
          (survivors.equivFin.symm
            (survivors.equivFin x)).1 = m
        rw [Equiv.symm_apply_apply]
      controller_mem := by
        intro i
        exact enumeratePrimeFinset_mem annulus
          (finiteCapacityInjection hcapacity i) }

namespace HardStagePairing

theorem target_above_scale {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    X < B.target i :=
  (mem_hardSurvivors.mp (B.target_mem i)).1

theorem target_at_most_next {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    B.target i ≤ Xnext :=
  (mem_hardSurvivors.mp (B.target_mem i)).2.1

theorem target_hard {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    HasHardForm h (B.target i) :=
  (mem_hardSurvivors.mp (B.target_mem i)).2.2.1

theorem controller_in_progression {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    InControllerProgression h (B.controller i) :=
  hardStageControllerAnnulus_in_progression
    (B.controller_mem i)

theorem controller_lower {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    B.target i / h.1 < (B.controller i).1 :=
  hardStageControllerAnnulus_above_target_div_hub
    (B.controller_mem i) (B.target_at_most_next i)

theorem controller_upper {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (B.controller i).1 ≤ X / k :=
  hardStageControllerAnnulus_upper (B.controller_mem i)

theorem residue_ne_zero {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (controllerResidue (B.controller i) (B.target i) : Nat) ≠ 0 :=
  hardForm_controllerResidue_ne_zero
    (B.target_hard i)
    (B.controller_in_progression i)
    (B.controller_lower i)

theorem controller_mature {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (hk : 0 < k)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    k * (B.controller i).1 ≤ B.target i + 1 :=
  controller_mature_from_annulus
    hk (B.controller_upper i) (B.target_above_scale i)

theorem assignment_covers {h L : Prime} {R : Finset Nat} {H : Finset Prime} {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (hk : 0 < k)
    (assignment : ShiftedAssignment)
    (hrecorded : ∀ i,
        (assignment (B.controller i) : Nat) = (controllerResidue
            (B.controller i) (B.target i) : Nat))
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    ShiftedMatureCovers k (B.target i) assignment :=
  controller_pair_covers
    (B.controller_mature hk i) (hrecorded i)

end HardStagePairing

end Erdos279
end

section

namespace Erdos279

theorem exists_oldPrimeClass_of_not_avoids {h : Prime} {z m : Nat} (a : OldPrimeClasses h z)
    (hm : ¬ AvoidsOldClasses a m) :
    ∃ p : Prime,
      InControllerProgression h p ∧ p.1 ≤ z ∧ m % p.1 = (a.residue p : Nat) := by
  classical
  unfold AvoidsOldClasses at hm
  push_neg at hm
  obtain ⟨p, hpG, hpz, hpClass⟩ := hm
  exact ⟨p, hpG, hpz, hpClass⟩

theorem covered_of_not_avoidsOldClasses {h : Prime} {z k m : Nat} (a : OldPrimeClasses h z)
    (assignment : ShiftedAssignment)
    (hmatch : ∀ p : Prime, InControllerProgression h p → p.1 ≤ z →
        (assignment p : Nat) = (a.residue p : Nat))
    (hmLarge : k * z ≤ m)
    (hm : ¬ AvoidsOldClasses a m) :
    ShiftedMatureCovers k m assignment := by
  obtain ⟨p, hpG, hpz, hpClass⟩ := exists_oldPrimeClass_of_not_avoids a hm
  refine ⟨p, ?_, ?_⟩
  · exact (Nat.mul_le_mul_left k hpz).trans hmLarge
        |>.trans (Nat.le_add_right m 1)
  · exact hpClass.trans (hmatch p hpG hpz).symm

end Erdos279
end

section

namespace Erdos279

open Filter

theorem exists_adjacent_scale_interval (scale : Nat → Nat) (_hmono : Monotone scale)
    (hunbounded : Tendsto scale atTop atTop)
    {m : Nat} (hm : scale 0 < m) :
    ∃ j, scale j < m ∧ m ≤ scale (j + 1) := by
  have hevent : ∀ᶠ n in atTop, m ≤ scale n := (tendsto_atTop.1 hunbounded) m
  obtain ⟨n, hn⟩ := hevent.exists
  have hex : ∃ n : Nat, m ≤ scale n := ⟨n, hn⟩
  let first : Nat := Nat.find hex
  have hfirst : m ≤ scale first := Nat.find_spec hex
  have hfirstPos : 0 < first := by
    by_contra hnot
    have hzero : first = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero] at hfirst
    omega
  let j : Nat := first - 1
  have hjSucc : j + 1 = first := by
    dsimp [j]
    omega
  have hjLt : j < first := by
    dsimp [j]
    omega
  have hnotAtJ : ¬ m ≤ scale j := Nat.find_min hex hjLt
  exact ⟨j, Nat.lt_of_not_ge hnotAtJ, by simpa [hjSucc] using hfirst⟩

theorem adjacent_scale_intervals_cover_tail (scale : Nat → Nat) (hmono : Monotone scale)
    (hunbounded : Tendsto scale atTop atTop) :
    ∀ m, scale 0 + 1 ≤ m → ∃ j, scale j < m ∧ m ≤ scale (j + 1) := by
  intro m hm
  apply exists_adjacent_scale_interval
    scale hmono hunbounded
  omega

end Erdos279
end

section

namespace Erdos279

noncomputable def OldControllerPrimeDensityMesh.periodicDensity {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) : Real :=
  (M.index : Real) *
    (controllerDensity h /
      ((M.modulus.1 : Real) - 1))

theorem OldControllerPrimeDensityMesh.periodicDensity_pos {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    0 < M.periodicDensity := by
  have hH : ∀ p ∈ oldControllerPrimes h M.cutoff,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hDelta : 0 < controllerComplementDensity h
          (oldControllerPrimes h M.cutoff) :=
    controllerComplementDensity_pos
      h hh (oldControllerPrimes h M.cutoff) hH
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast hk
  have hleft : 0 < (k : Real) *
          controllerComplementDensity h
            (oldControllerPrimes h M.cutoff) :=
    mul_pos hkR hDelta
  exact hleft.trans M.lower

theorem OldControllerPrimeDensityMesh.densityRatio_mem_Ioo {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    1 / (h.1 : Real) < controllerComplementDensity h
            (oldControllerPrimes h M.cutoff) /
          M.periodicDensity ∧
      controllerComplementDensity h
            (oldControllerPrimes h M.cutoff) /
          M.periodicDensity <
        1 / (k : Real) := by
  have hTau : 0 < M.periodicDensity := M.periodicDensity_pos hh hk
  have hhR : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hkR : (0 : Real) < (k : Real) := by
    exact_mod_cast hk
  constructor
  · apply (div_lt_div_iff₀ hhR hTau).2
    simpa [OldControllerPrimeDensityMesh.periodicDensity,
      mul_comm] using M.upper_hub
  · apply (div_lt_div_iff₀ hTau hkR).2
    simpa [OldControllerPrimeDensityMesh.periodicDensity,
      mul_comm] using M.lower

structure MeshPrimeEnumerations
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  enumerations : PeriodicComplementaryEnumerations
      h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
  ratio_eq : enumerations.ratio = controllerComplementDensity h
          (oldControllerPrimes h M.cutoff) /
        M.periodicDensity

namespace MeshPrimeEnumerations

theorem exists_tailMatching {h : Prime} {k : Nat} {M : OldControllerPrimeDensityMesh h k}
    (E : MeshPrimeEnumerations M)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    Nonempty
      (TailPrimeTargetMatching
        E.enumerations.periodic
        E.enumerations.complementary k) := by
  have hwindow := M.densityRatio_mem_Ioo hh hk
  apply E.enumerations.exists_tailMatching hk
  · simpa [E.ratio_eq] using hwindow.1
  · simpa [E.ratio_eq] using hwindow.2

end MeshPrimeEnumerations

end Erdos279
end

section

namespace Erdos279

open Filter

end Erdos279
end

section

namespace Erdos279

open Filter

def primeNatPredicate (P : Prime → Prop) (n : Nat) : Prop := ∃ hn : IsPrime n, P ⟨n, hn⟩

noncomputable def enumeratePrimePredicate (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (i : Nat) : Prime := by
  have hmem : primeNatPredicate P
        (Nat.nth (primeNatPredicate P) i) :=
    Nat.nth_mem_of_infinite hInf i
  exact ⟨Nat.nth (primeNatPredicate P) i,
      Classical.choose hmem⟩

@[simp]
theorem enumeratePrimePredicate_val (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (i : Nat) :
    (enumeratePrimePredicate P hInf i).1 = Nat.nth (primeNatPredicate P) i :=
  rfl

theorem enumeratePrimePredicate_mem (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (i : Nat) :
    P (enumeratePrimePredicate P hInf i) := by
  have hmem : primeNatPredicate P
        (Nat.nth (primeNatPredicate P) i) :=
    Nat.nth_mem_of_infinite hInf i
  exact (Classical.choose_spec hmem)

theorem enumeratePrimePredicate_injective (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P))) :
    Function.Injective (enumeratePrimePredicate P hInf) := by
  intro i j hij
  apply (Nat.nth_injective hInf)
  exact congrArg Subtype.val hij

theorem enumeratePrimePredicate_surjective (P : Prime → Prop)
    (hInf : Set.Infinite (setOf (primeNatPredicate P))) :
    ∀ p, P p → ∃ i, enumeratePrimePredicate P hInf i = p := by
  intro p hp
  have hpNat : primeNatPredicate P p.1 := ⟨p.2, hp⟩
  have hpRange : p.1 ∈ Set.range (Nat.nth (primeNatPredicate P)) := by
    rw [Nat.range_nth_of_infinite hInf]
    exact hpNat
  obtain ⟨i, hi⟩ := hpRange
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi

noncomputable def periodicComplementaryEnumerationsOfNth (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (hPeriodic : Set.Infinite
        (setOf
          (primeNatPredicate
            (InPeriodicReservoir h L R H))))
    (hComplementary : Set.Infinite
        (setOf
          (primeNatPredicate
            (IsComplementaryPrimeTarget h H))))
    (ratio : Real)
    (hratio : Tendsto
        (fun i => ((enumeratePrimePredicate
            (InPeriodicReservoir h L R H)
            hPeriodic i).1 : Real) /
          ((enumeratePrimePredicate
            (IsComplementaryPrimeTarget h H)
            hComplementary i).1 : Real))
        atTop (nhds ratio)) :
    PeriodicComplementaryEnumerations h L R H where
  periodic := enumeratePrimePredicate
      (InPeriodicReservoir h L R H) hPeriodic
  complementary := enumeratePrimePredicate
      (IsComplementaryPrimeTarget h H) hComplementary
  periodic_injective := enumeratePrimePredicate_injective _ hPeriodic
  complementary_injective := enumeratePrimePredicate_injective _ hComplementary
  periodic_mem := enumeratePrimePredicate_mem _ hPeriodic
  complementary_mem := enumeratePrimePredicate_mem _ hComplementary
  complementary_surjective := enumeratePrimePredicate_surjective _ hComplementary
  ratio := ratio
  ratio_tendsto := hratio

end Erdos279
end

section

namespace Erdos279

open Filter

noncomputable def nthPrimeScale (n : Nat) : Real := ((n + 2 : Nat) : Real) *
    Real.log ((n + 2 : Nat) : Real)

theorem nthPrimeScale_pos (n : Nat) : 0 < nthPrimeScale n := by
  unfold nthPrimeScale
  have hn : (1 : Real) < ((n + 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 1 < n + 2)
  exact mul_pos (by positivity) (Real.log_pos hn)

theorem nthPrimeScale_ne_zero (n : Nat) : nthPrimeScale n ≠ 0 := (nthPrimeScale_pos n).ne'

def HasNthPrimeAsymptotic (P : Prime → Prop) (hInf : Set.Infinite (setOf (primeNatPredicate P)))
    (density : Real) : Prop :=
  Tendsto
    (fun n => ((enumeratePrimePredicate P hInf n).1 : Real) /
        nthPrimeScale n)
    atTop (nhds (1 / density))

theorem ratio_tendsto_of_nthPrimeAsymptotics (P Q : Prime → Prop)
    (hP : Set.Infinite (setOf (primeNatPredicate P)))
    (hQ : Set.Infinite (setOf (primeNatPredicate Q)))
    {densityP densityQ : Real}
    (hdP : 0 < densityP) (hdQ : 0 < densityQ)
    (hAsymP : HasNthPrimeAsymptotic P hP densityP)
    (hAsymQ : HasNthPrimeAsymptotic Q hQ densityQ) :
    Tendsto
      (fun n => ((enumeratePrimePredicate P hP n).1 : Real) /
          ((enumeratePrimePredicate Q hQ n).1 : Real))
      atTop (nhds (densityQ / densityP)) := by
  have hlimit : Tendsto
        (fun n => (((enumeratePrimePredicate P hP n).1 : Real) /
              nthPrimeScale n) /
            (((enumeratePrimePredicate Q hQ n).1 : Real) /
              nthPrimeScale n))
        atTop
        (nhds ((1 / densityP) / (1 / densityQ))) :=
    hAsymP.div hAsymQ (by
      exact one_div_ne_zero hdQ.ne')
  have hsource : (fun n => ((enumeratePrimePredicate P hP n).1 : Real) /
          ((enumeratePrimePredicate Q hQ n).1 : Real)) =ᶠ[atTop]
      (fun n => (((enumeratePrimePredicate P hP n).1 : Real) /
            nthPrimeScale n) /
          (((enumeratePrimePredicate Q hQ n).1 : Real) /
            nthPrimeScale n)) := by
    apply Eventually.of_forall
    intro n
    have hscale := nthPrimeScale_ne_zero n
    have hq : ((enumeratePrimePredicate Q hQ n).1 : Real) ≠ 0 := by
      exact_mod_cast
        (Nat.ne_of_gt
          (enumeratePrimePredicate Q hQ n).pos)
    field_simp
  have hratio : Tendsto
        (fun n => ((enumeratePrimePredicate P hP n).1 : Real) /
            ((enumeratePrimePredicate Q hQ n).1 : Real))
        atTop
        (nhds ((1 / densityP) / (1 / densityQ))) :=
    Tendsto.congr' hsource.symm hlimit
  simpa [div_eq_mul_inv, mul_comm] using hratio

structure MeshNthPrimeInputs
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  periodic_infinite : Set.Infinite
      (setOf
        (primeNatPredicate
          (InPeriodicReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff))))
  complementary_infinite : Set.Infinite
      (setOf
        (primeNatPredicate
          (IsComplementaryPrimeTarget h
            (oldControllerPrimes h M.cutoff))))
  periodic_asymptotic : HasNthPrimeAsymptotic
      (InPeriodicReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      periodic_infinite M.periodicDensity
  complementary_asymptotic : HasNthPrimeAsymptotic
      (IsComplementaryPrimeTarget h
        (oldControllerPrimes h M.cutoff))
      complementary_infinite
      (controllerComplementDensity h
        (oldControllerPrimes h M.cutoff))

namespace MeshNthPrimeInputs

noncomputable def toMeshPrimeEnumerations {h : Prime} {k : Nat}
    {M : OldControllerPrimeDensityMesh h k}
    (A : MeshNthPrimeInputs M)
    (hh : 3 ≤ h.1) (hk : 0 < k) :
    MeshPrimeEnumerations M := by
  have hPeriodic : 0 < M.periodicDensity := M.periodicDensity_pos hh hk
  have hH : ∀ p ∈ oldControllerPrimes h M.cutoff,
        InControllerProgression h p := by
    intro p hp
    exact (mem_oldControllerPrimes.mp hp).1
  have hComplementary : 0 < controllerComplementDensity h
          (oldControllerPrimes h M.cutoff) :=
    controllerComplementDensity_pos
      h hh (oldControllerPrimes h M.cutoff) hH
  let ratio := controllerComplementDensity h
        (oldControllerPrimes h M.cutoff) /
      M.periodicDensity
  have hratio : Tendsto
        (fun n => ((enumeratePrimePredicate
            (InPeriodicReservoir
              h M.modulus M.classes
              (oldControllerPrimes h M.cutoff))
            A.periodic_infinite n).1 : Real) /
          ((enumeratePrimePredicate
            (IsComplementaryPrimeTarget h
              (oldControllerPrimes h M.cutoff))
            A.complementary_infinite n).1 : Real))
        atTop (nhds ratio) := by
    exact ratio_tendsto_of_nthPrimeAsymptotics
        _ _ A.periodic_infinite A.complementary_infinite
        hPeriodic hComplementary
        A.periodic_asymptotic
        A.complementary_asymptotic
  exact
    { enumerations :=
        periodicComplementaryEnumerationsOfNth
          h M.modulus M.classes
          (oldControllerPrimes h M.cutoff)
          A.periodic_infinite
          A.complementary_infinite
          ratio hratio
      ratio_eq := rfl }

end MeshNthPrimeInputs

end Erdos279
end

section

namespace Erdos279

open Filter

noncomputable def primeCountingScale (x : Nat) : Real := ((x + 2 : Nat) : Real) /
    Real.log ((x + 2 : Nat) : Real)

theorem primeCountingScale_pos (x : Nat) : 0 < primeCountingScale x := by
  unfold primeCountingScale
  have hx : (1 : Real) < ((x + 2 : Nat) : Real) := by
    exact_mod_cast (by omega : 1 < x + 2)
  exact div_pos (by positivity) (Real.log_pos hx)

theorem primeCountingScale_ne_zero (x : Nat) : primeCountingScale x ≠ 0 :=
  (primeCountingScale_pos x).ne'

theorem primeCountingScale_tendsto_atTop : Tendsto primeCountingScale atTop atTop := by
  have hShift : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hReciprocal : Tendsto (fun n => (primeCountingScale n)⁻¹) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => inv_pos.mpr (primeCountingScale_pos n)⟩
    simpa [primeCountingScale, inv_div, Function.comp_def] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hShift
  simpa only [Function.comp_def, inv_inv] using tendsto_inv_nhdsGT_zero.comp hReciprocal

noncomputable def predicateCount (P : Nat → Prop) (x : Nat) : Nat := by
  classical
  exact Nat.count P x

theorem predicateCount_add (P : Nat → Prop) (a b : Nat) : predicateCount P (a + b) =
      predicateCount P a +
        predicateCount (fun k => P (a + k)) b := by
  classical
  unfold predicateCount
  exact Nat.count_add P a b

def HasPrimeCountingAsymptotic (P : Nat → Prop) (density : Real) : Prop := Tendsto (fun x =>
      ((predicateCount P x : Nat) : Real) /
        primeCountingScale x)
    atTop (nhds density)

/-- Positive counting density implies that the counted set is infinite. -/
theorem infinite_of_counting {P : ℕ → Prop} {density : ℝ} (hd : 0 < density)
    (hc : HasPrimeCountingAsymptotic P density) : (Set.ofPred P).Infinite := by
  classical
  have h : Tendsto (fun n : ℕ => (predicateCount P n : ℝ)) atTop atTop := by
    change Tendsto (fun n : ℕ => (predicateCount P n : ℝ) / primeCountingScale n)
      atTop (nhds density) at hc
    refine (Tendsto.pos_mul_atTop hd hc primeCountingScale_tendsto_atTop).congr' ?_
    exact Eventually.of_forall fun n => div_mul_cancel₀ _ (primeCountingScale_ne_zero n)
  by_contra hInf
  let S := (Set.not_infinite.mp hInf).toFinset
  have hUpper (n : ℕ) : predicateCount P n ≤ S.card := by
    rw [predicateCount, Nat.count_eq_card_filter_range]
    refine Finset.card_le_card fun a ha => ?_
    simpa [S] using (Finset.mem_filter.mp ha).2
  obtain ⟨n, hn⟩ := (h.eventually_gt_atTop (S.card : ℝ)).exists
  exact (not_lt_of_ge (by exact_mod_cast hUpper n)) hn

def HasProjectPrimeCountingAsymptotic (P : Prime → Prop) (density : Real) : Prop :=
  HasPrimeCountingAsymptotic
    (primeNatPredicate P) density

theorem count_or_of_pointwise_disjoint (P Q : Nat → Prop) (hdisjoint : ∀ n, ¬ (P n ∧ Q n))
    (x : Nat) :
    predicateCount (fun n => P n ∨ Q n) x = predicateCount P x + predicateCount Q x := by
  classical
  unfold predicateCount
  induction x with
  | zero =>
      simp
  | succ x ih =>
      rw [Nat.count_succ, Nat.count_succ,
        Nat.count_succ, ih]
      by_cases hp : P x <;>
        by_cases hq : Q x <;>
        simp [hp, hq, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm]
      exact (hdisjoint x ⟨hp, hq⟩).elim

theorem count_exists_mem_finset {ι : Type*} [DecidableEq ι] (R : Finset ι) (A : ι → Nat → Prop)
    (hdisjoint : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ∀ n, ¬ (A a n ∧ A b n))
    (x : Nat) :
    predicateCount (fun n => ∃ a ∈ R, A a n) x = ∑ a ∈ R, predicateCount (A a) x := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      simp [predicateCount]
  | @insert a R ha ih =>
      have hhead : ∀ n, ¬ (A a n ∧ ∃ b ∈ R, A b n) := by
        intro n hn
        rcases hn with ⟨han, b, hbR, hbn⟩
        exact hdisjoint a (Finset.mem_insert_self a R)
            b (Finset.mem_insert_of_mem hbR)
            (by
              intro hab
              subst b
              exact ha hbR)
            n ⟨han, hbn⟩
      have htail : ∀ b ∈ R, ∀ c ∈ R, b ≠ c → ∀ n, ¬ (A b n ∧ A c n) := by
        intro b hb c hc hbc n
        exact hdisjoint b (Finset.mem_insert_of_mem hb)
            c (Finset.mem_insert_of_mem hc)
            hbc n
      have hor : predicateCount
              (fun n => A a n ∨ ∃ b ∈ R, A b n) x =
            predicateCount (A a) x +
              predicateCount (fun n => ∃ b ∈ R, A b n) x :=
        count_or_of_pointwise_disjoint
          (A a) (fun n => ∃ b ∈ R, A b n)
          hhead x
      calc
        predicateCount
            (fun n => ∃ b ∈ insert a R, A b n) x =
          predicateCount
            (fun n => A a n ∨ ∃ b ∈ R, A b n) x := by
              apply congrArg (fun P => predicateCount P x)
              funext n
              apply propext
              simp only [Finset.mem_insert]
              constructor
              · rintro ⟨b, hb, hbn⟩
                rcases hb with rfl | hbR
                · exact Or.inl hbn
                · exact Or.inr ⟨b, hbR, hbn⟩
              · rintro (han | ⟨b, hbR, hbn⟩)
                · exact ⟨a, Or.inl rfl, han⟩
                · exact ⟨b, Or.inr hbR, hbn⟩
        _ = predicateCount (A a) x +
            predicateCount (fun n => ∃ b ∈ R, A b n) x := hor
        _ = predicateCount (A a) x +
            ∑ b ∈ R, predicateCount (A b) x := by
              rw [ih htail]
        _ = ∑ b ∈ insert a R, predicateCount (A b) x := by
              simp [ha]

theorem hasPrimeCountingAsymptotic_exists_mem_finset {ι : Type*} [DecidableEq ι]
    (R : Finset ι) (A : ι → Nat → Prop)
    (density : ι → Real)
    (hdisjoint : ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ∀ n, ¬ (A a n ∧ A b n))
    (hAsymptotic : ∀ a ∈ R,
        HasPrimeCountingAsymptotic
          (A a) (density a)) :
    HasPrimeCountingAsymptotic
      (fun n => ∃ a ∈ R, A a n)
      (∑ a ∈ R, density a) := by
  classical
  unfold HasPrimeCountingAsymptotic
  have hsum : Tendsto
        (fun x => ∑ a ∈ R,
            ((predicateCount (A a) x : Nat) : Real) /
              primeCountingScale x)
        atTop
        (nhds (∑ a ∈ R, density a)) := by
    exact tendsto_finset_sum R
        (fun a ha => by
          simpa [HasPrimeCountingAsymptotic] using hAsymptotic a ha)
  have heq : (fun x => ((predicateCount
          (fun n => ∃ a ∈ R, A a n) x : Nat) : Real) /
            primeCountingScale x) =
      (fun x => ∑ a ∈ R,
          ((predicateCount (A a) x : Nat) : Real) /
            primeCountingScale x) := by
    funext x
    rw [count_exists_mem_finset R A hdisjoint x]
    push_cast
    rw [Finset.sum_div]
  rw [heq]
  exact hsum

theorem HasPrimeCountingAsymptotic.congr_of_eventually_iff {P Q : Nat → Prop} {density : Real}
    (N : Nat)
    (hPQ : ∀ n, N ≤ n → (P n ↔ Q n))
    (hQ : HasPrimeCountingAsymptotic Q density) :
    HasPrimeCountingAsymptotic P density := by
  unfold HasPrimeCountingAsymptotic at hQ ⊢
  let cP : Real := predicateCount P N
  let cQ : Real := predicateCount Q N
  have hdiffEventually : (fun x => ((predicateCount P x : Nat) : Real) /
            primeCountingScale x -
          ((predicateCount Q x : Nat) : Real) /
            primeCountingScale x) =ᶠ[atTop]
      (fun x => (cP - cQ) /
          primeCountingScale x) := by
    filter_upwards [eventually_ge_atTop N] with x hx
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hx
    have htail : (fun k => P (N + k)) = (fun k => Q (N + k)) := by
      funext k
      apply propext
      exact hPQ (N + k) (Nat.le_add_right N k)
    have htailCount : predicateCount (fun k => P (N + k)) t =
          predicateCount (fun k => Q (N + k)) t :=
      congrArg (fun S => predicateCount S t) htail
    unfold cP cQ
    rw [predicateCount_add,
      predicateCount_add, htailCount]
    push_cast
    field_simp [primeCountingScale_ne_zero]
    ring
  have hdiffLimit : Tendsto
        (fun x => ((predicateCount P x : Nat) : Real) /
              primeCountingScale x -
            ((predicateCount Q x : Nat) : Real) /
              primeCountingScale x)
        atTop (nhds 0) := by
    apply Tendsto.congr' hdiffEventually.symm
    exact primeCountingScale_tendsto_atTop
        |>.const_div_atTop (cP - cQ)
  simpa only [sub_add_cancel, zero_add] using hdiffLimit.add hQ

end Erdos279
end

section

namespace Erdos279

open Filter

theorem natLog_cast_le_realLog_div {b n : Nat} (hb : 1 < b) (hn : n ≠ 0) : (Nat.log b n : Real) ≤
      Real.log (n : Real) / Real.log (b : Real) := by
  have hpowNat : b ^ Nat.log b n ≤ n := Nat.pow_log_le_self b hn
  have hpowReal : (b : Real) ^ Nat.log b n ≤ (n : Real) := by
    exact_mod_cast hpowNat
  have hbasePos : (0 : Real) < (b : Real) := by
    exact_mod_cast (Nat.zero_lt_one.trans hb)
  have hlog := Real.log_le_log (by positivity : 0 < (b : Real) ^ Nat.log b n)
      hpowReal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hb))).2
    (by simpa using hlog)

theorem log_sq_div_sqrt_shift_tendsto_zero : Tendsto (fun X : Nat =>
        Real.log (((X + 2 : Nat) : Real)) ^ 2 /
          Real.sqrt (((X + 2 : Nat) : Real)))
      atTop (nhds 0) := by
  have hReal : Tendsto
        (fun x : Real => Real.log x ^ 2 / Real.sqrt x)
        atTop (nhds 0) := by
    have h := ((isLittleO_log_rpow_rpow_atTop
        (s := (1 / 2 : Real)) (2 : Real)
        (by norm_num)).tendsto_div_nhds_zero)
    apply h.congr'
    exact Eventually.of_forall fun x => by
      change
        Real.log x ^ (2 : Real) / x ^ (1 / 2 : Real) = Real.log x ^ (2 : Nat) / Real.sqrt x
      rw [Real.sqrt_eq_rpow, Real.rpow_two]
  have hShift : Tendsto
        (fun X : Nat => (((X + 2 : Nat) : Real)))
        atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 2)
  exact hReal.comp hShift

noncomputable def hardTailRealBound (h : Prime) (B X : Nat) : Real := (((Nat.log h.1 (B * X) + 1) *
    (B * Nat.sqrt X) : Nat) : Real)

theorem hardTailRealBound_normalized_tendsto_zero (h : Prime) (B : Nat) (hB : 0 < B) : Tendsto
      (fun X : Nat => hardTailRealBound h B X /
          primeCountingScale X)
      atTop (nhds 0) := by
  let c : Real := Real.log (h.1 : Real)
  let C : Real := (1 / c) + Real.log (B : Real) / c + 1
  have hcPos : 0 < c := by
    dsimp [c]
    exact Real.log_pos (by exact_mod_cast h.one_lt)
  have hlogBNonneg : 0 ≤ Real.log (B : Real) := by
    exact Real.log_nonneg (by exact_mod_cast hB)
  have hCNonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hShiftTop : Tendsto
        (fun X : Nat => (((X + 2 : Nat) : Real)))
        atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_add_atTop_nat 2)
  have hLogShiftTop : Tendsto
        (fun X : Nat => Real.log (((X + 2 : Nat) : Real)))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hShiftTop
  have hLogShiftOne : ∀ᶠ X : Nat in atTop,
        1 ≤ Real.log (((X + 2 : Nat) : Real)) :=
    hLogShiftTop.eventually_ge_atTop 1
  have hMajorant : Tendsto
        (fun X : Nat => (C * (B : Real)) *
            (Real.log (((X + 2 : Nat) : Real)) ^ 2 /
              Real.sqrt (((X + 2 : Nat) : Real))))
        atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : Nat => C * (B : Real))
            atTop (nhds (C * (B : Real)))).mul
        log_sq_div_sqrt_shift_tendsto_zero)
  refine squeeze_zero'
    (g := fun X : Nat => (C * (B : Real)) *
        (Real.log (((X + 2 : Nat) : Real)) ^ 2 /
          Real.sqrt (((X + 2 : Nat) : Real))))
    ?_ ?_ hMajorant
  · exact Eventually.of_forall fun X => div_nonneg
        (by
          unfold hardTailRealBound
          positivity)
        (primeCountingScale_pos X).le
  · filter_upwards
      [eventually_gt_atTop (0 : Nat), hLogShiftOne] with X hX hLogOne
    have hBX : B * X ≠ 0 := Nat.mul_ne_zero hB.ne' hX.ne'
    have hNatLog : (Nat.log h.1 (B * X) : Real) ≤ Real.log ((B * X : Nat) : Real) / c := by
      simpa [c] using natLog_cast_le_realLog_div h.one_lt hBX
    have hlogMul : Real.log ((B * X : Nat) : Real) = Real.log (B : Real) + Real.log (X : Real) := by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity)]
    have hXShift : (X : Real) ≤ ((X + 2 : Nat) : Real) := by
      exact_mod_cast (Nat.le_add_right X 2)
    have hlogXLe : Real.log (X : Real) ≤ Real.log (((X + 2 : Nat) : Real)) :=
      Real.log_le_log (by exact_mod_cast hX) hXShift
    have hlogBScaled : Real.log (B : Real) / c ≤ (Real.log (B : Real) / c) *
            Real.log (((X + 2 : Nat) : Real)) := by
      calc
        Real.log (B : Real) / c = (Real.log (B : Real) / c) * 1 := by ring
        _ ≤ (Real.log (B : Real) / c) *
              Real.log (((X + 2 : Nat) : Real)) :=
          mul_le_mul_of_nonneg_left hLogOne
            (div_nonneg hlogBNonneg hcPos.le)
    have hNatLogAdd : (Nat.log h.1 (B * X) : Real) + 1 ≤ C * Real.log (((X + 2 : Nat) : Real)) := by
      rw [hlogMul] at hNatLog
      dsimp [C]
      have hcNe : c ≠ 0 := hcPos.ne'
      calc
        (Nat.log h.1 (B * X) : Real) + 1 ≤ (Real.log (B : Real) +
                Real.log (X : Real)) / c + 1 := by
          linarith
        _ ≤ (Real.log (B : Real) +
                Real.log (((X + 2 : Nat) : Real))) / c +
              Real.log (((X + 2 : Nat) : Real)) := by
          have hdiv : (Real.log (B : Real) + Real.log (X : Real)) / c ≤ (Real.log (B : Real) +
                  Real.log (((X + 2 : Nat) : Real))) / c :=
            div_le_div_of_nonneg_right
              (by
                simpa [add_comm] using add_le_add_left hlogXLe (Real.log (B : Real)))
              hcPos.le
          linarith
        _ ≤ (1 / c + Real.log (B : Real) / c + 1) *
              Real.log (((X + 2 : Nat) : Real)) := by
          have hLNonneg : 0 ≤ Real.log (((X + 2 : Nat) : Real)) := hLogOne.trans' zero_le_one
          calc
            (Real.log (B : Real) +
                Real.log (((X + 2 : Nat) : Real))) / c +
                Real.log (((X + 2 : Nat) : Real)) =
              Real.log (B : Real) / c +
                (1 / c) *
                  Real.log (((X + 2 : Nat) : Real)) +
                Real.log (((X + 2 : Nat) : Real)) := by
              field_simp [hcNe]
            _ ≤ (Real.log (B : Real) / c) *
                    Real.log (((X + 2 : Nat) : Real)) +
                  (1 / c) *
                    Real.log (((X + 2 : Nat) : Real)) +
                  Real.log (((X + 2 : Nat) : Real)) := by
              linarith
            _ = (1 / c + Real.log (B : Real) / c + 1) *
                  Real.log (((X + 2 : Nat) : Real)) := by
              ring
    have hsqrtLe : (Nat.sqrt X : Real) ≤ Real.sqrt (((X + 2 : Nat) : Real)) := by
      exact (Real.nat_sqrt_le_real_sqrt).trans
        (Real.sqrt_le_sqrt hXShift)
    have hTailNumerator : hardTailRealBound h B X ≤ (C * Real.log (((X + 2 : Nat) : Real))) *
            ((B : Real) *
              Real.sqrt (((X + 2 : Nat) : Real))) := by
      unfold hardTailRealBound
      push_cast
      have hNatLogAdd' : (Nat.log h.1 (B * X) : Real) + 1 ≤ C * Real.log ((X : Real) + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hNatLogAdd
      have hsqrtLe' : (Nat.sqrt X : Real) ≤ Real.sqrt ((X : Real) + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hsqrtLe
      have hLogOne' : 1 ≤ Real.log ((X : Real) + 2) := by
        simpa only [Nat.cast_add, Nat.cast_ofNat] using hLogOne
      exact mul_le_mul hNatLogAdd'
        (mul_le_mul_of_nonneg_left hsqrtLe' (by positivity))
        (by positivity)
        (mul_nonneg hCNonneg
          (hLogOne'.trans' zero_le_one))
    have hDivide : hardTailRealBound h B X / primeCountingScale X ≤
          ((C * Real.log (((X + 2 : Nat) : Real))) *
            ((B : Real) *
              Real.sqrt (((X + 2 : Nat) : Real)))) /
            primeCountingScale X :=
      div_le_div_of_nonneg_right hTailNumerator
        (primeCountingScale_pos X).le
    refine hDivide.trans_eq ?_
    unfold primeCountingScale
    push_cast
    have hshiftPos : 0 < (X : Real) + 2 := by positivity
    have hsqrtPos : 0 < Real.sqrt ((X : Real) + 2) := Real.sqrt_pos.2 hshiftPos
    have hlogPos : 0 < Real.log ((X : Real) + 2) := Real.log_pos (by
        have hXR : 0 ≤ (X : Real) := by positivity
        linarith)
    have hsquare : Real.sqrt ((X : Real) + 2) ^ 2 = (X : Real) + 2 := Real.sq_sqrt hshiftPos.le
    field_simp [hlogPos.ne', hsqrtPos.ne']
    nlinarith

end Erdos279
end

section

namespace Erdos279

open Filter

def stageOldPrimeCutoff (v X : Nat) : Nat := Nat.nthRoot v X

noncomputable def uniformHardStageCount (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) : Nat :=
  (hardSurvivors h (stageOldPrimeCutoff v X) a X (B * X)).card

noncomputable def uniformMainHardStageCount (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) : Nat :=
  ∑ e ∈ hardMainExponentRange h X (B * X),
    (hardLayerUnits h (stageOldPrimeCutoff v X) e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card

noncomputable def uniformTailHardStageCount (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) : Nat :=
  ∑ e ∈ hardTailExponentRange h X (B * X),
    (hardLayerUnits h (stageOldPrimeCutoff v X) e a
      (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card

theorem uniformHardStageCount_eq_main_add_tail (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X)) :
    uniformHardStageCount h v B X a = uniformMainHardStageCount h v B X a +
        uniformTailHardStageCount h v B X a := by
  unfold uniformHardStageCount uniformMainHardStageCount
    uniformTailHardStageCount
  exact hardSurvivors_card_eq_main_add_tail
      h (stageOldPrimeCutoff v X) a X (B * X)

def HasUniformHardStageUpperBound (h : Prime) (v B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        (uniformHardStageCount h v B X a : Real) /
            primeCountingScale X ≤
          coefficient + ε

def HasUniformMainHardStageUpperBound (h : Prime) (v B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        (uniformMainHardStageCount h v B X a : Real) /
            primeCountingScale X ≤
          coefficient + ε

theorem uniformTailHardStageCount_le (h : Prime) (v B X : Nat)
    (a : OldPrimeClasses h (stageOldPrimeCutoff v X))
    (hB : 0 < B) :
    uniformTailHardStageCount h v B X a ≤ (Nat.log h.1 (B * X) + 1) *
        (B * Nat.sqrt X) := by
  exact sum_hardTailLayers_card_le
      h (stageOldPrimeCutoff v X) B X a hB

theorem uniformTailHardStageCount_normalized_eventually_lt (h : Prime) (v B : Nat) (hB : 0 < B)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        (uniformTailHardStageCount h v B X a : Real) /
            primeCountingScale X <
          ε := by
  have hBoundEventually : ∀ᶠ X : Nat in atTop,
        hardTailRealBound h B X /
            primeCountingScale X <
          ε :=
    (hardTailRealBound_normalized_tendsto_zero
      h B hB).eventually_lt_const hε
  filter_upwards [hBoundEventually] with X hX
  intro a
  have hTailCast : (uniformTailHardStageCount h v B X a : Real) ≤ hardTailRealBound h B X := by
    unfold hardTailRealBound
    exact_mod_cast uniformTailHardStageCount_le h v B X a hB
  exact (div_le_div_of_nonneg_right hTailCast
      (primeCountingScale_pos X).le).trans_lt hX

theorem HasUniformMainHardStageUpperBound.toHardUpperBound
    {h : Prime} {v B : Nat} {coefficient : Real}
    (hMain : HasUniformMainHardStageUpperBound h v B coefficient)
    (hB : 0 < B) :
    HasUniformHardStageUpperBound h v B coefficient := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hMainEventually := hMain (ε / 2) hhalf
  have hTailEventually := uniformTailHardStageCount_normalized_eventually_lt
      h v B hB hhalf
  filter_upwards
    [hMainEventually, hTailEventually] with X hMainX hTailX
  intro a
  have hMainAt := hMainX a
  have hTailAt := hTailX a
  rw [uniformHardStageCount_eq_main_add_tail h v B X a]
  push_cast
  rw [add_div]
  linarith

end Erdos279
end

section

namespace Erdos279

open Filter Finset

theorem sum_inv_prime_powers_le_controllerDensity (h : Prime) (s : Finset Nat)
    (hs : ∀ e ∈ s, 1 ≤ e) :
    (∑ e ∈ s, (((h.1 ^ e : Nat) : Real)⁻¹)) ≤ controllerDensity h := by
  let r : Real := ((h.1 : Real)⁻¹)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast h.one_lt)
  have hzero : 0 ∉ s := by
    intro h0
    have := hs 0 h0
    omega
  have hsum := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
      (insert 0 s) (fun _ _ => pow_nonneg hr0 _)
  rw [tsum_geometric_of_lt_one hr0 hr1] at hsum
  simp only [sum_insert hzero, pow_zero] at hsum
  have hreindex : (∑ e ∈ s, (((h.1 ^ e : Nat) : Real)⁻¹)) = ∑ e ∈ s, r ^ e := by
    apply sum_congr rfl
    intro e he
    dsimp [r]
    push_cast
    rw [inv_pow]
  rw [hreindex]
  have hhpos : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hhne : (h.1 : Real) ≠ 0 := hhpos.ne'
  have hden : (h.1 : Real) - 1 ≠ 0 := by
    have : (1 : Real) < (h.1 : Real) := by
      exact_mod_cast h.one_lt
    linarith
  calc
    ∑ e ∈ s, r ^ e ≤ (1 - r)⁻¹ - 1 := by
      linarith
    _ = controllerDensity h := by
      rw [controllerDensity]
      dsimp [r]
      field_simp [hhne, hden]
      ring

theorem one_le_of_mem_hardMainExponentRange {h : Prime} {X Z e : Nat}
    (he : e ∈ hardMainExponentRange h X Z) :
    1 ≤ e := by
  exact (Finset.mem_Icc.mp
    (Finset.mem_filter.mp he).1).1

theorem twice_prime_power_le_of_mem_hardMainExponentRange {h : Prime} {X Z e : Nat} (hX : 4 ≤ X)
    (he : e ∈ hardMainExponentRange h X Z) :
    2 * h.1 ^ e ≤ X := by
  have hmain : Nat.sqrt X ≤ X / h.1 ^ e := (Finset.mem_filter.mp he).2
  have hsqrt : 2 ≤ Nat.sqrt X := by
    rw [Nat.le_sqrt]
    omega
  have hpowpos : 0 < h.1 ^ e := Nat.pow_pos h.pos
  have hmul : Nat.sqrt X * h.1 ^ e ≤ X := (Nat.le_div_iff_mul_le hpowpos).1 hmain
  exact (Nat.mul_le_mul_right (h.1 ^ e) hsqrt).trans hmul

theorem shifted_value_ratio_le_twice_inv_prime_power {h : Prime} {X Z e : Nat} (hX : 4 ≤ X)
    (he : e ∈ hardMainExponentRange h X Z) :
    (((X / h.1 ^ e + 2 : Nat) : Real) /
        ((X + 2 : Nat) : Real)) ≤
      2 * (((h.1 ^ e : Nat) : Real)⁻¹) := by
  have hpowposN : 0 < h.1 ^ e := Nat.pow_pos h.pos
  have hpowposR : (0 : Real) < ((h.1 ^ e : Nat) : Real) := by
    exact_mod_cast hpowposN
  have hXposR : (0 : Real) < ((X + 2 : Nat) : Real) := by
    positivity
  have hdivmul : h.1 ^ e * (X / h.1 ^ e) ≤ X := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self X (h.1 ^ e)
  have htwice : 2 * h.1 ^ e ≤ X := twice_prime_power_le_of_mem_hardMainExponentRange hX he
  have hNat : h.1 ^ e * (X / h.1 ^ e + 2) ≤ 2 * (X + 2) := by
    calc
      h.1 ^ e * (X / h.1 ^ e + 2) = h.1 ^ e * (X / h.1 ^ e) +
            2 * h.1 ^ e := by
              simp only [Nat.mul_add]
              omega
      _ ≤ X + X := Nat.add_le_add hdivmul htwice
      _ ≤ 2 * (X + 2) := by omega
  have hReal : ((h.1 ^ e : Nat) : Real) *
          ((X / h.1 ^ e + 2 : Nat) : Real) ≤
        2 * ((X + 2 : Nat) : Real) := by
    exact_mod_cast hNat
  rw [div_le_iff₀ hXposR]
  calc
    ((X / h.1 ^ e + 2 : Nat) : Real) ≤ (2 * ((X + 2 : Nat) : Real)) /
          ((h.1 ^ e : Nat) : Real) := by
      apply (le_div_iff₀ hpowposR).2
      nlinarith
    _ = 2 * (((h.1 ^ e : Nat) : Real)⁻¹) *
          ((X + 2 : Nat) : Real) := by
      rw [inv_eq_one_div]
      field_simp [hpowposR.ne']

theorem shifted_log_ratio_le_two_of_mem_hardMainExponentRange {h : Prime} {X Z e : Nat}
    (he : e ∈ hardMainExponentRange h X Z) :
    Real.log ((X + 2 : Nat) : Real) /
        Real.log ((X / h.1 ^ e + 2 : Nat) : Real) ≤
      2 := by
  let Y := X / h.1 ^ e
  have hmain : Nat.sqrt X ≤ Y := by
    simpa [Y] using (Finset.mem_filter.mp he).2
  have hsqrt : X < (Nat.sqrt X + 1) ^ 2 := by
      simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt X
  have hsquare : X + 2 ≤ (Y + 2) ^ 2 := by
    nlinarith
  have hcast : ((X + 2 : Nat) : Real) ≤ (((Y + 2 : Nat) : Real) ^ 2) := by
    exact_mod_cast hsquare
  have hpositive : (0 : Real) < ((X + 2 : Nat) : Real) := by
    positivity
  have hlogLe : Real.log ((X + 2 : Nat) : Real) ≤ Real.log (((Y + 2 : Nat) : Real) ^ 2) :=
    Real.log_le_log hpositive hcast
  rw [Real.log_pow] at hlogLe
  have hden : 0 < Real.log ((Y + 2 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < Y + 2)
  apply (div_le_iff₀ hden).2
  simpa only [Nat.cast_ofNat] using hlogLe

theorem primeCountingScale_div_le_four_inv_prime_power {h : Prime} {X Z e : Nat} (hX : 4 ≤ X)
    (he : e ∈ hardMainExponentRange h X Z) :
    primeCountingScale (X / h.1 ^ e) /
        primeCountingScale X ≤
      4 * (((h.1 ^ e : Nat) : Real)⁻¹) := by
  have hValue := shifted_value_ratio_le_twice_inv_prime_power hX he
  have hLog := shifted_log_ratio_le_two_of_mem_hardMainExponentRange he
  have hValueNonneg : 0 ≤ (((X / h.1 ^ e + 2 : Nat) : Real) /
          ((X + 2 : Nat) : Real)) := by
    positivity
  push_cast at hValue hLog hValueNonneg
  have hLogNumeratorPos : 0 < Real.log ((X : Real) + 2) := by
    apply Real.log_pos
    have hXnonneg : (0 : Real) ≤ X := by positivity
    linarith
  have hLogDenominatorPos : 0 < Real.log (((X / h.1 ^ e : Nat) : Real) + 2) := by
    apply Real.log_pos
    have hYnonneg : (0 : Real) ≤ (X / h.1 ^ e : Nat) := by
      positivity
    linarith
  have hLogNonneg : 0 ≤ Real.log ((X : Real) + 2) /
          Real.log (((X / h.1 ^ e : Nat) : Real) + 2) := by
    exact (div_pos hLogNumeratorPos hLogDenominatorPos).le
  have hmul := mul_le_mul hValue hLog
      hLogNonneg
      (by positivity)
  unfold primeCountingScale
  push_cast
  have hlogX : Real.log ((X : Real) + 2) ≠ 0 := by
    exact hLogNumeratorPos.ne'
  have hlogY : Real.log (((X / h.1 ^ e : Nat) : Real) + 2) ≠ 0 := by
    exact hLogDenominatorPos.ne'
  have hXtwo : (X : Real) + 2 ≠ 0 := by positivity
  have hYtwo : ((X / h.1 ^ e : Nat) : Real) + 2 ≠ 0 := by
    positivity
  calc
    ((((X / h.1 ^ e : Nat) : Real) + 2) /
          Real.log (((X / h.1 ^ e : Nat) : Real) + 2) /
        (((X : Real) + 2) / Real.log ((X : Real) + 2))) =
        ((((X / h.1 ^ e : Nat) : Real) + 2) /
          ((X : Real) + 2)) *
        (Real.log ((X : Real) + 2) /
          Real.log (((X / h.1 ^ e : Nat) : Real) + 2)) := by
      field_simp [hlogX, hlogY, hXtwo, hYtwo]
    _ ≤ (2 * (((h.1 : Real) ^ e)⁻¹)) * 2 := hmul
    _ = 4 * (((h.1 : Real) ^ e)⁻¹) := by ring

def HasUniformMainLayerUpperBound (h : Prime) (v B : Nat) (coefficient : Real) : Prop :=
  ∀ ε : Real, 0 < ε → ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h (stageOldPrimeCutoff v X),
        ∀ e ∈ hardMainExponentRange h X (B * X),
          ((hardLayerUnits h (stageOldPrimeCutoff v X) e a
              (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) /
              primeCountingScale (X / h.1 ^ e) ≤
            coefficient + ε

theorem HasUniformMainLayerUpperBound.toMainHardStageUpperBound
    {h : Prime} {v B : Nat} {coefficient : Real}
    (hLayer : HasUniformMainLayerUpperBound h v B coefficient)
    (hcoefficient : 0 ≤ coefficient) :
    HasUniformMainHardStageUpperBound h v B
      (4 * coefficient * controllerDensity h) := by
  intro ε hε
  have hδ : 0 < controllerDensity h := controllerDensity_pos h
  let η : Real := ε / (4 * controllerDensity h)
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hLayerEventually := hLayer η hη
  filter_upwards [hLayerEventually, eventually_ge_atTop 4] with X hLX hX
  intro a
  have hTerm : ∀ e ∈ hardMainExponentRange h X (B * X),
        ((hardLayerUnits h (stageOldPrimeCutoff v X) e a
            (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) ≤
          (coefficient + η) *
            (4 * (((h.1 ^ e : Nat) : Real)⁻¹) *
              primeCountingScale X) := by
    intro e he
    have hLocal := (div_le_iff₀
        (primeCountingScale_pos (X / h.1 ^ e))).1
        (hLX a e he)
    have hScaleRatio := primeCountingScale_div_le_four_inv_prime_power
        hX he
    have hScale : primeCountingScale (X / h.1 ^ e) ≤ 4 * (((h.1 ^ e : Nat) : Real)⁻¹) *
            primeCountingScale X := by
      exact (div_le_iff₀ (primeCountingScale_pos X)).1
          hScaleRatio
    exact hLocal.trans
      (mul_le_mul_of_nonneg_left hScale
        (add_nonneg hcoefficient hη.le))
  have hSum := Finset.sum_le_sum hTerm
  have hGeom : (∑ e ∈ hardMainExponentRange h X (B * X),
          (((h.1 ^ e : Nat) : Real)⁻¹)) ≤
        controllerDensity h :=
    sum_inv_prime_powers_le_controllerDensity
      h _ (fun e he => one_le_of_mem_hardMainExponentRange he)
  have hScalePos : 0 < primeCountingScale X := primeCountingScale_pos X
  unfold uniformMainHardStageCount
  push_cast
  rw [div_le_iff₀ hScalePos]
  calc
    ∑ e ∈ hardMainExponentRange h X (B * X),
        ((hardLayerUnits h (stageOldPrimeCutoff v X) e a
          (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) ≤
      ∑ e ∈ hardMainExponentRange h X (B * X),
        (coefficient + η) *
          (4 * (((h.1 ^ e : Nat) : Real)⁻¹) *
            primeCountingScale X) := hSum
    _ = (4 * (coefficient + η) * primeCountingScale X) *
        (∑ e ∈ hardMainExponentRange h X (B * X),
          (((h.1 ^ e : Nat) : Real)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    _ ≤ (4 * (coefficient + η) * primeCountingScale X) *
        controllerDensity h := by
      gcongr
    _ = (4 * coefficient * controllerDensity h + ε) *
        primeCountingScale X := by
      dsimp [η]
      field_simp [hδ.ne']

end Erdos279
end

section

namespace Erdos279

structure VariableHardPairingSchedule
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat) where
  oldClasses : ∀ j, OldPrimeClasses h (z j)
  stage : ∀ j,
      HardStagePairing h L R H (z j) k
        (scale j) (scale (j + 1)) (oldClasses j)
  base : ShiftedAssignment
  assignment : ShiftedAssignment
  assignment_at_controller : ∀ (j : Nat)
      (i : Fin
        (hardSurvivors h (z j) (oldClasses j)
          (scale j) (scale (j + 1))).card),
      (assignment ((stage j).controller i) : Nat) = (controllerResidue
          ((stage j).controller i)
          ((stage j).target i) : Nat)
  assignment_matches_old : ∀ (j : Nat) (p : Prime),
      InControllerProgression h p →
      p.1 ≤ z j →
      (assignment p : Nat) = ((oldClasses j).residue p : Nat)
  assignment_of_not_in_reservoir : ∀ p : Prime,
      ¬ InControllerReservoir h L R H p →
      assignment p = base p
  cutoff_mature : ∀ j, k * z j ≤ scale j

namespace VariableHardPairingSchedule

theorem assignment_covers_stage {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z scale : Nat → Nat} {k : Nat}
    (S : VariableHardPairingSchedule h L R H z scale k)
    (hk : 0 < k)
    (j : Nat)
    (i : Fin
      (hardSurvivors h (z j) (S.oldClasses j)
        (scale j) (scale (j + 1))).card) :
    ShiftedMatureCovers k ((S.stage j).target i)
      S.assignment := by
  exact (S.stage j).assignment_covers
      hk S.assignment
      (S.assignment_at_controller j)
      i

theorem covers_hardForm_tail {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z scale : Nat → Nat} {k : Nat}
    (S : VariableHardPairingSchedule h L R H z scale k)
    (hk : 0 < k)
    (scaleThreshold : Nat)
    (hscale : ∀ m, scaleThreshold ≤ m → ∃ j, scale j < m ∧ m ≤ scale (j + 1)) :
    ∀ m,
      scaleThreshold ≤ m →
      HasHardForm h m →
      ShiftedMatureCovers k m S.assignment := by
  intro m hmLarge hmHard
  obtain ⟨j, hmLower, hmUpper⟩ := hscale m hmLarge
  by_cases hmAvoids : AvoidsOldClasses (S.oldClasses j) m
  · have hmSurvivor : m ∈ hardSurvivors h (z j) (S.oldClasses j)
          (scale j) (scale (j + 1)) :=
      mem_hardSurvivors.mpr
        ⟨hmLower, hmUpper, hmHard, hmAvoids⟩
    obtain ⟨i, hi⟩ := (S.stage j).target_surjective m hmSurvivor
    have hcover := S.assignment_covers_stage hk j i
    simpa [hi] using hcover
  · have hmOldMature : k * z j ≤ m := (S.cutoff_mature j).trans
        (Nat.le_of_lt hmLower)
    exact covered_of_not_avoidsOldClasses
        (S.oldClasses j)
        S.assignment
        (S.assignment_matches_old j)
        hmOldMature hmAvoids

end VariableHardPairingSchedule

end Erdos279
end

section

namespace Erdos279

def forceNonzeroResidue (p : Prime) (u : Fin p.1) : Fin p.1 := if hu : (u : Nat) = 0 then
    ⟨1, p.one_lt⟩
  else
    u

theorem forceNonzeroResidue_ne_zero (p : Prime) (u : Fin p.1) :
    (forceNonzeroResidue p u : Nat) ≠ 0 := by
  by_cases hu : (u : Nat) = 0
  · simp [forceNonzeroResidue, hu]
  · simpa [forceNonzeroResidue, hu] using hu

theorem forceNonzeroResidue_eq_self (p : Prime) (u : Fin p.1) (hu : (u : Nat) ≠ 0) :
    forceNonzeroResidue p u = u := by
  simp [forceNonzeroResidue, hu]

def nonzeroOldPrimeClasses (h : Prime) (z : Nat) (assignment : ShiftedAssignment) :
    OldPrimeClasses h z where
  residue p := forceNonzeroResidue p (assignment p)
  nonzero := by
    intro p _hpG _hpz
    exact forceNonzeroResidue_ne_zero p (assignment p)

noncomputable def installedHardStageValue {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime) : Fin p.1 := by
  classical
  exact if hex : ∃ i : Fin (hardSurvivors h z a X Xnext).card,
          B.controller i = p then
      ⟨B.target (Classical.choose hex) % p.1,
        Nat.mod_lt _ p.pos⟩
    else
      ⟨1, p.one_lt⟩

theorem installedHardStageValue_at_controller {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (i : Fin (hardSurvivors h z a X Xnext).card) :
    (installedHardStageValue B (B.controller i) : Nat) =
      (controllerResidue (B.controller i) (B.target i) : Nat) := by
  let hex : ∃ t : Fin (hardSurvivors h z a X Xnext).card,
        B.controller t = B.controller i :=
    ⟨i, rfl⟩
  rw [installedHardStageValue]
  simp only [dif_pos hex]
  have hcontroller : B.controller (Classical.choose hex) = B.controller i :=
    Classical.choose_spec hex
  have hindex : Classical.choose hex = i := B.controller_injective hcontroller
  rw [hindex]
  rfl

theorem installedHardStageValue_ne_zero {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime) :
    (installedHardStageValue B p : Nat) ≠ 0 := by
  classical
  by_cases hex : ∃ i : Fin (hardSurvivors h z a X Xnext).card,
        B.controller i = p
  · obtain ⟨i, hi⟩ := hex
    subst p
    rw [installedHardStageValue_at_controller B i]
    exact B.residue_ne_zero i
  · simp [installedHardStageValue, hex]

noncomputable def installHardStage {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (old : ShiftedAssignment)
    (B : HardStagePairing h L R H z k X Xnext a) :
    ShiftedAssignment := by
  classical
  exact fun p => if p ∈ hardStageControllerAnnulus h L R H k X Xnext then
      installedHardStageValue B p
    else
      old p

theorem installHardStage_of_not_mem {h L : Prime} {R : Finset Nat} {H : Finset Prime}
    {z k X Xnext : Nat}
    {a : OldPrimeClasses h z}
    (old : ShiftedAssignment)
    (B : HardStagePairing h L R H z k X Xnext a)
    (p : Prime)
    (hp : p ∉ hardStageControllerAnnulus h L R H k X Xnext) :
    installHardStage old B p = old p := by
  simp [installHardStage, hp]

noncomputable def dynamicAssignmentBefore (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment) :
    Nat → ShiftedAssignment
  | 0 => base
  | j + 1 =>
      let old := dynamicAssignmentBefore h L R H z scale k
          hcapacity base j
      let a := nonzeroOldPrimeClasses h (z j) old
      let B := hardStagePairingOfCardLe
          h L R H (z j) k
          (scale j) (scale (j + 1)) a
          (hcapacity j a)
      installHardStage old B

noncomputable def dynamicOldClasses (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment)
    (j : Nat) :
    OldPrimeClasses h (z j) :=
  nonzeroOldPrimeClasses h (z j)
    (dynamicAssignmentBefore h L R H z scale k
      hcapacity base j)

noncomputable def dynamicHardStage (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment)
    (j : Nat) :
    HardStagePairing h L R H (z j) k
      (scale j) (scale (j + 1))
      (dynamicOldClasses h L R H z scale k
        hcapacity base j) :=
  hardStagePairingOfCardLe
    h L R H (z j) k
    (scale j) (scale (j + 1))
    (dynamicOldClasses h L R H z scale k
      hcapacity base j)
    (hcapacity j
      (dynamicOldClasses h L R H z scale k
        hcapacity base j))

theorem dynamicAssignmentBefore_succ (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (hardStageControllerAnnulus h L R H k
          (scale j) (scale (j + 1))).card)
    (base : ShiftedAssignment)
    (j : Nat) :
    dynamicAssignmentBefore h L R H z scale k
        hcapacity base (j + 1) =
      installHardStage
        (dynamicAssignmentBefore h L R H z scale k
          hcapacity base j)
        (dynamicHardStage h L R H z scale k
          hcapacity base j) := by
  rfl

end Erdos279
end

section

namespace Erdos279

noncomputable def dynamicHardAnnulus (h L : Prime) (R : Finset Nat) (H : Finset Prime) (k : Nat)
    (scale : Nat → Nat) (j : Nat) : Finset Prime :=
  hardStageControllerAnnulus h L R H k
    (scale j) (scale (j + 1))

noncomputable def dynamicFinalAssignment (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p => if hex : ∃ j : Nat,
          p ∈ dynamicHardAnnulus h L R H k scale j then
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base (Classical.choose hex))
        p
    else
      base p

def DynamicCutoffReady (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment) : Prop :=
  ∀ (j : Nat) (p : Prime),
    InControllerProgression h p →
    p.1 ≤ z j →
    ((∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) ∧
        (base p : Nat) ≠ 0) ∨
      ∃ i : Nat, i < j ∧ p ∈ dynamicHardAnnulus h L R H k scale i

theorem dynamicAssignmentBefore_eq_base_of_never_mem (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) :
    ∀ j,
      dynamicAssignmentBefore h L R H z scale k
        hcapacity base j p = base p := by
  intro j
  induction j with
  | zero =>
      rfl
  | succ j ih =>
      rw [congrFun (dynamicAssignmentBefore_succ h L R H z scale k hcapacity base j) p]
      rw [installHardStage_of_not_mem]
      · exact ih
      · exact hp j

theorem dynamicAssignmentBefore_eq_installed_of_mem (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (p : Prime) (i j : Nat)
    (hp : p ∈ dynamicHardAnnulus h L R H k scale i)
    (hij : i < j) :
    dynamicAssignmentBefore h L R H z scale k
        hcapacity base j p =
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base i) p := by
  induction j with
  | zero =>
      omega
  | succ j ih =>
      rw [congrFun (dynamicAssignmentBefore_succ h L R H z scale k hcapacity base j) p]
      by_cases hEq : i = j
      · subst j
        have hp' : p ∈ hardStageControllerAnnulus h L R H k
              (scale i) (scale (i + 1)) := by
          simpa [dynamicHardAnnulus] using hp
        simp [installHardStage, hp']
      · have hiJ : i < j := by omega
        rw [installHardStage_of_not_mem]
        · exact ih hiJ
        · intro hpJ
          exact (Finset.disjoint_left.mp
              (hdisjoint i j hEq)) hp hpJ

theorem dynamicFinalAssignment_eq_installed_of_mem (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (p : Prime) (i : Nat)
    (hp : p ∈ dynamicHardAnnulus h L R H k scale i) :
    dynamicFinalAssignment h L R H z scale k
        hcapacity base p =
      installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base i) p := by
  classical
  let hex : ∃ j : Nat,
        p ∈ dynamicHardAnnulus h L R H k scale j :=
    ⟨i, hp⟩
  rw [dynamicFinalAssignment]
  simp only [dif_pos hex]
  have hpChosen : p ∈ dynamicHardAnnulus h L R H k scale
        (Classical.choose hex) :=
    Classical.choose_spec hex
  have hChosen : Classical.choose hex = i := by
    by_contra hne
    exact (Finset.disjoint_left.mp
        (hdisjoint (Classical.choose hex) i hne))
        hpChosen hp
  exact congrArg
    (fun t => installedHardStageValue
        (dynamicHardStage h L R H z scale k
          hcapacity base t) p)
    hChosen

theorem dynamicFinalAssignment_at_controller (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (j : Nat)
    (i : Fin
      (hardSurvivors h (z j)
        (dynamicOldClasses h L R H z scale k
          hcapacity base j)
        (scale j) (scale (j + 1))).card) :
    (dynamicFinalAssignment h L R H z scale k
        hcapacity base
        ((dynamicHardStage h L R H z scale k
          hcapacity base j).controller i) : Nat) =
      (controllerResidue
        ((dynamicHardStage h L R H z scale k
          hcapacity base j).controller i)
        ((dynamicHardStage h L R H z scale k
          hcapacity base j).target i) : Nat) := by
  let B := dynamicHardStage h L R H z scale k
      hcapacity base j
  rw [dynamicFinalAssignment_eq_installed_of_mem
    h L R H z scale k hcapacity base hdisjoint
    (B.controller i) j]
  · exact installedHardStageValue_at_controller B i
  · exact B.controller_mem i

theorem dynamicFinalAssignment_of_never_mem (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) :
    dynamicFinalAssignment h L R H z scale k
      hcapacity base p = base p := by
  classical
  rw [dynamicFinalAssignment]
  apply dif_neg
  intro hex
  obtain ⟨j, hpj⟩ := hex
  exact hp j hpj

theorem dynamicFinalAssignment_of_not_in_reservoir (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    dynamicFinalAssignment h L R H z scale k
      hcapacity base p = base p := by
  apply dynamicFinalAssignment_of_never_mem
  intro i hpMem
  exact hp (mem_hardStageControllerAnnulus.mp hpMem).2.2

theorem dynamicFinalAssignment_matches_old (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (hready : DynamicCutoffReady h L R H z scale k base)
    (j : Nat) (p : Prime)
    (hpG : InControllerProgression h p)
    (hpz : p.1 ≤ z j) :
    (dynamicFinalAssignment h L R H z scale k
        hcapacity base p : Nat) =
      ((dynamicOldClasses h L R H z scale k
        hcapacity base j).residue p : Nat) := by
  rcases hready j p hpG hpz with
    ⟨hpNever, hpBaseNonzero⟩ | ⟨i, hiJ, hpI⟩
  · have hBefore := dynamicAssignmentBefore_eq_base_of_never_mem
        h L R H z scale k hcapacity base p hpNever j
    have hFinal := dynamicFinalAssignment_of_never_mem
        h L R H z scale k hcapacity base p hpNever
    change
      (dynamicFinalAssignment h L R H z scale k
          hcapacity base p : Nat) =
        (forceNonzeroResidue p
          (dynamicAssignmentBefore h L R H z scale k
            hcapacity base j p) : Nat)
    rw [hFinal, hBefore,
      forceNonzeroResidue_eq_self p (base p) hpBaseNonzero]
  · have hBefore := dynamicAssignmentBefore_eq_installed_of_mem
        h L R H z scale k hcapacity base hdisjoint
        p i j hpI hiJ
    have hFinal := dynamicFinalAssignment_eq_installed_of_mem
        h L R H z scale k hcapacity base hdisjoint
        p i hpI
    have hInstalledNonzero : (installedHardStageValue
          (dynamicHardStage h L R H z scale k
            hcapacity base i) p : Nat) ≠ 0 :=
      installedHardStageValue_ne_zero
        (dynamicHardStage h L R H z scale k
          hcapacity base i) p
    change
      (dynamicFinalAssignment h L R H z scale k
          hcapacity base p : Nat) =
        (forceNonzeroResidue p
          (dynamicAssignmentBefore h L R H z scale k
            hcapacity base j p) : Nat)
    rw [hFinal, hBefore,
      forceNonzeroResidue_eq_self _ _ hInstalledNonzero]

noncomputable def variableHardPairingScheduleOfCapacity (h L : Prime) (R : Finset Nat)
    (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (hcapacity : ∀ (j : Nat) (a : OldPrimeClasses h (z j)),
        (hardSurvivors h (z j) a
          (scale j) (scale (j + 1))).card ≤
        (dynamicHardAnnulus h L R H k scale j).card)
    (base : ShiftedAssignment)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint
          (dynamicHardAnnulus h L R H k scale i)
          (dynamicHardAnnulus h L R H k scale j))
    (hready : DynamicCutoffReady h L R H z scale k base)
    (hmature : ∀ j, k * z j ≤ scale j) :
    VariableHardPairingSchedule h L R H z scale k where
  oldClasses j := dynamicOldClasses h L R H z scale k
      hcapacity base j
  stage j := dynamicHardStage h L R H z scale k
      hcapacity base j
  base := base
  assignment := dynamicFinalAssignment h L R H z scale k
      hcapacity base
  assignment_at_controller := dynamicFinalAssignment_at_controller
      h L R H z scale k hcapacity base hdisjoint
  assignment_matches_old := dynamicFinalAssignment_matches_old
      h L R H z scale k hcapacity base
      hdisjoint hready
  assignment_of_not_in_reservoir := dynamicFinalAssignment_of_not_in_reservoir
      h L R H z scale k hcapacity base
  cutoff_mature := hmature

end Erdos279
end

section

namespace Erdos279

noncomputable def prepareDynamicBase (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p => if hpS : InControllerReservoir h L R H p then
      if hex : ∃ i : Nat,
            p ∈ dynamicHardAnnulus h L R H k scale i then
        base p
      else
        ⟨1, p.one_lt⟩
    else
      base p

theorem prepareDynamicBase_of_not_in_reservoir (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    prepareDynamicBase h L R H scale k base p = base p := by
  simp [prepareDynamicBase, hp]

theorem prepareDynamicBase_nonzero_of_never_mem (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment)
    (hbase : ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0)
    (p : Prime)
    (hpG : InControllerProgression h p)
    (hpNever : ∀ i : Nat,
        p ∉ dynamicHardAnnulus h L R H k scale i) :
    (prepareDynamicBase h L R H scale k base p : Nat) ≠ 0 := by
  classical
  by_cases hpS : InControllerReservoir h L R H p
  · have hnone : ¬ ∃ i : Nat,
          p ∈ dynamicHardAnnulus h L R H k scale i := by
      intro hex
      obtain ⟨i, hi⟩ := hex
      exact hpNever i hi
    simp [prepareDynamicBase, hpS, hnone]
  · rw [prepareDynamicBase_of_not_in_reservoir
      h L R H scale k base p hpS]
    exact hbase p hpG hpS

theorem dynamicCutoffReady_of_below_future_annuli (h L : Prime) (R : Finset Nat) (H : Finset Prime)
    (z scale : Nat → Nat) (k : Nat)
    (base : ShiftedAssignment)
    (hbase : ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0)
    (hbelow : ∀ j i : Nat, j ≤ i → z j < scale (i + 1) / h.1) :
    DynamicCutoffReady h L R H z scale k
      (prepareDynamicBase h L R H scale k base) := by
  intro j p hpG hpz
  by_cases hex : ∃ i : Nat,
        p ∈ dynamicHardAnnulus h L R H k scale i
  · obtain ⟨i, hpI⟩ := hex
    have hiJ : i < j := by
      by_contra hnot
      have hjI : j ≤ i := Nat.le_of_not_gt hnot
      have hcut := hbelow j i hjI
      have hlower : scale (i + 1) / h.1 < p.1 := (mem_hardStageControllerAnnulus.mp hpI).1
      omega
    exact Or.inr ⟨i, hiJ, hpI⟩
  · have hpNever : ∀ i : Nat,
          p ∉ dynamicHardAnnulus h L R H k scale i := by
      intro i hpI
      exact hex ⟨i, hpI⟩
    exact Or.inl
      ⟨hpNever,
        prepareDynamicBase_nonzero_of_never_mem
          h L R H scale k base hbase p hpG hpNever⟩

end Erdos279
end

section

namespace Erdos279

theorem nthRoot_le_sqrt {v X : Nat} (hv : 2 ≤ v) : Nat.nthRoot v X ≤ Nat.sqrt X := by
  let r := Nat.nthRoot v X
  by_cases hr : r = 0
  · simp [r, hr]
  · have hrOne : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hpow : r ^ v ≤ X := by
      exact Nat.pow_nthRoot_le (Or.inl (by omega : v ≠ 0))
    have hpowMono : r ^ 2 ≤ r ^ v := Nat.pow_le_pow_right hrOne hv
    exact Nat.le_sqrt'.2 (hpowMono.trans hpow)

theorem mul_nthRoot_le_of_sq_le {k v X : Nat} (hv : 2 ≤ v) (hkX : k ^ 2 ≤ X) :
    k * Nat.nthRoot v X ≤ X := by
  let r := Nat.nthRoot v X
  have hrSqrt : r ≤ Nat.sqrt X := nthRoot_le_sqrt hv
  have hrSq : r ^ 2 ≤ X := Nat.le_sqrt'.mp hrSqrt
  rcases le_total r k with hrk | hkr
  · calc
      k * r ≤ k * k := Nat.mul_le_mul_left k hrk
      _ = k ^ 2 := by simp [pow_two]
      _ ≤ X := hkX
  · calc
      k * r ≤ r * r := by
        exact Nat.mul_le_mul_right r hkr
      _ = r ^ 2 := by simp [pow_two]
      _ ≤ X := hrSq

theorem sqrt_lt_mul_div {h B C X : Nat} (hh : 0 < h) (hC : C ^ 2 ≤ X) (hBC : 2 * h ≤ B * C) :
    Nat.sqrt X < (B * X) / h := by
  have hCroot : C ≤ Nat.sqrt X := Nat.le_sqrt'.2 hC
  have hBCpos : 0 < B * C := by
    exact (Nat.mul_pos (by omega) hh).trans_le hBC
  have hCpos : 0 < C := by
    exact Nat.pos_of_ne_zero (fun hCzero => by
      subst C
      simp at hBCpos)
  have hrootPos : 0 < Nat.sqrt X := hCpos.trans_le hCroot
  have hCsqrt : C * Nat.sqrt X ≤ X := by
    calc
      C * Nat.sqrt X ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_right (Nat.sqrt X) hCroot
      _ ≤ X := Nat.sqrt_le X
  apply Nat.lt_iff_add_one_le.mpr
  apply (Nat.le_div_iff_mul_le hh).2
  calc
    (Nat.sqrt X + 1) * h = h * Nat.sqrt X + h := by ring
    _ ≤ h * Nat.sqrt X + h * Nat.sqrt X := by
      exact Nat.add_le_add_left
        (Nat.le_mul_of_pos_right h hrootPos) _
    _ = (2 * h) * Nat.sqrt X := by ring
    _ ≤ (B * C) * Nat.sqrt X := Nat.mul_le_mul_right (Nat.sqrt X) hBC
    _ = B * (C * Nat.sqrt X) := by ring
    _ ≤ B * X := Nat.mul_le_mul_left B hCsqrt

theorem stageOldPrimeCutoff_lt_mul_div {h v B C X : Nat} (hv : 2 ≤ v) (hh : 0 < h) (hC : C ^ 2 ≤ X)
    (hBC : 2 * h ≤ B * C) :
    stageOldPrimeCutoff v X < (B * X) / h :=
  (nthRoot_le_sqrt hv).trans_lt
    (sqrt_lt_mul_div hh hC hBC)

end Erdos279
end

section

namespace Erdos279

open Filter

theorem nat_nthRoot_tendsto_atTop (v : Nat) (hv : 0 < v) : Tendsto (Nat.nthRoot v) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  refine ⟨K ^ v, ?_⟩
  intro X hX
  exact (Nat.le_nthRoot_iff hv.ne').2 hX

theorem natCast_nthRoot_tendsto_atTop (v : Nat) (hv : 0 < v) :
    Tendsto (fun X : Nat => (Nat.nthRoot v X : Real))
      atTop atTop :=
  tendsto_natCast_atTop_atTop.comp
    (nat_nthRoot_tendsto_atTop v hv)

noncomputable def dualSieveError (X : Nat) : Real :=
  let z := Nat.nthRoot 64 X
  2 * (z : Real) * (1 + Real.log (z : Real)) ^ 3

theorem nthRoot64_pow_four_le_nthRoot16 (X : Nat) : Nat.nthRoot 64 X ^ 4 ≤ Nat.nthRoot 16 X := by
  rw [Nat.le_nthRoot_iff (by norm_num : (16 : Nat) ≠ 0)]
  rw [← pow_mul]
  norm_num

theorem nthRoot16_pow_two_le_nthRoot8 (X : Nat) : Nat.nthRoot 16 X ^ 2 ≤ Nat.nthRoot 8 X := by
  rw [Nat.le_nthRoot_iff (by norm_num : (8 : Nat) ≠ 0)]
  rw [← pow_mul]
  norm_num

theorem nthRoot8_pow_two_le_nthRoot4 (X : Nat) : Nat.nthRoot 8 X ^ 2 ≤ Nat.nthRoot 4 X := by
  rw [Nat.le_nthRoot_iff (by norm_num : (4 : Nat) ≠ 0)]
  rw [← pow_mul]
  norm_num

theorem nthRoot16_pow_four_le_sqrt (X : Nat) : Nat.nthRoot 16 X ^ 4 ≤ Nat.sqrt X := by
  calc
    Nat.nthRoot 16 X ^ 4 = (Nat.nthRoot 16 X ^ 2) ^ 2 := by ring
    _ ≤ Nat.nthRoot 8 X ^ 2 := pow_le_pow_left₀ (Nat.zero_le _)
        (nthRoot16_pow_two_le_nthRoot8 X) 2
    _ ≤ Nat.nthRoot 4 X := nthRoot8_pow_two_le_nthRoot4 X
    _ ≤ Nat.sqrt X := nthRoot_le_sqrt (by norm_num : 2 ≤ (4 : Nat))

theorem dualSieveError_div_primeCountingScale_le {X Y : Nat} (hX : 1 ≤ X) (hmain : Nat.sqrt X ≤ Y) :
    dualSieveError X / primeCountingScale Y ≤ 32 / (Nat.nthRoot 16 X : Real) := by
  let z := Nat.nthRoot 64 X
  let r := Nat.nthRoot 16 X
  have hzOne : 1 ≤ z := by
    dsimp [z]
    rw [Nat.le_nthRoot_iff (by norm_num : (64 : Nat) ≠ 0)]
    simpa using hX
  have hrOne : 1 ≤ r := by
    dsimp [r]
    rw [Nat.le_nthRoot_iff (by norm_num : (16 : Nat) ≠ 0)]
    simpa using hX
  have hzNonneg : (0 : Real) ≤ (z : Real) := by positivity
  have hlogzNonneg : 0 ≤ Real.log (z : Real) := by
    exact Real.log_nonneg (by exact_mod_cast hzOne)
  have hlogzLe : Real.log (z : Real) ≤ (z : Real) := Real.log_le_self hzNonneg
  have honeLogLe : 1 + Real.log (z : Real) ≤ 2 * (z : Real) := by
    have hzOneReal : (1 : Real) ≤ (z : Real) := by
      exact_mod_cast hzOne
    linarith
  have herror : dualSieveError X ≤ 16 * (r : Real) := by
    have hpow : (1 + Real.log (z : Real)) ^ 3 ≤ (2 * (z : Real)) ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) honeLogLe 3
    have hz4r : ((z : Real) ^ 4) ≤ (r : Real) := by
      exact_mod_cast nthRoot64_pow_four_le_nthRoot16 X
    dsimp [dualSieveError, z]
    calc
      2 * (z : Real) *
            (1 + Real.log (z : Real)) ^ 3 ≤
          2 * (z : Real) * (2 * (z : Real)) ^ 3 := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 16 * (z : Real) ^ 4 := by ring
      _ ≤ 16 * (r : Real) := mul_le_mul_of_nonneg_left hz4r (by norm_num)
  have hr4Y : r ^ 4 ≤ Y := by
    exact (nthRoot16_pow_four_le_sqrt X).trans hmain
  have hrSqSqrt : ((r : Real) ^ 2) ≤ Real.sqrt ((Y + 2 : Nat) : Real) := by
    apply (Real.le_sqrt' (by positivity)).2
    have hcast : ((r ^ 4 : Nat) : Real) ≤ (Y : Real) := by
      exact_mod_cast hr4Y
    calc
      ((r : Real) ^ 2) ^ 2 = ((r ^ 4 : Nat) : Real) := by
        push_cast
        ring
      _ ≤ (Y : Real) := hcast
      _ ≤ ((Y + 2 : Nat) : Real) := by
        exact_mod_cast (Nat.le_add_right Y 2)
  have hlogUpper : Real.log ((Y + 2 : Nat) : Real) ≤ 2 * Real.sqrt ((Y + 2 : Nat) : Real) := by
    have h := Real.log_le_rpow_div
        (show (0 : Real) ≤ ((Y + 2 : Nat) : Real) by positivity)
        (show (0 : Real) < (1 / 2 : Real) by norm_num)
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using h
  have hlogPos : 0 < Real.log ((Y + 2 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < Y + 2)
  have hsqrtSq : Real.sqrt ((Y + 2 : Nat) : Real) ^ 2 = ((Y + 2 : Nat) : Real) :=
    Real.sq_sqrt (by positivity)
  have hscale : (r : Real) ^ 2 / 2 ≤ primeCountingScale Y := by
    unfold primeCountingScale
    apply (le_div_iff₀ hlogPos).2
    calc
      (r : Real) ^ 2 / 2 *
            Real.log ((Y + 2 : Nat) : Real) ≤
          (r : Real) ^ 2 / 2 *
            (2 * Real.sqrt ((Y + 2 : Nat) : Real)) := by
        exact mul_le_mul_of_nonneg_left hlogUpper (by positivity)
      _ = (r : Real) ^ 2 *
            Real.sqrt ((Y + 2 : Nat) : Real) := by ring
      _ ≤ Real.sqrt ((Y + 2 : Nat) : Real) *
            Real.sqrt ((Y + 2 : Nat) : Real) := by
        exact mul_le_mul_of_nonneg_right hrSqSqrt (Real.sqrt_nonneg _)
      _ = ((Y + 2 : Nat) : Real) := by
        nlinarith
  have hrPos : (0 : Real) < (r : Real) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hrOne)
  calc
    dualSieveError X / primeCountingScale Y ≤ (16 * (r : Real)) / ((r : Real) ^ 2 / 2) := by
      exact div_le_div₀ (by positivity) herror
        (by positivity) hscale
    _ = 32 / (r : Real) := by
      field_simp [hrPos.ne']
      ring

theorem dualSieveError_normalized_eventually_lt {ε : Real} (hε : 0 < ε) : ∀ᶠ X : Nat in atTop,
      ∀ Y : Nat, Nat.sqrt X ≤ Y → dualSieveError X / primeCountingScale Y < ε := by
  have hmajor : Tendsto
        (fun X : Nat => 32 / (Nat.nthRoot 16 X : Real))
        atTop (nhds 0) :=
    (natCast_nthRoot_tendsto_atTop 16 (by norm_num)).const_div_atTop 32
  have hmajorEventually := hmajor.eventually_lt_const hε
  filter_upwards [eventually_ge_atTop (1 : Nat),
    hmajorEventually] with X hX hmajorX
  intro Y hmain
  exact (dualSieveError_div_primeCountingScale_le hX hmain).trans_lt
    hmajorX

theorem mul_div_le_mul_div_add_one (B X d : Nat) (hd : 0 < d) : (B * X) / d ≤ B * (X / d + 1) := by
  by_cases hB : B = 0
  · simp [hB]
  · apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hd).2
    have hXlt : X < d * (X / d + 1) := Nat.lt_mul_div_succ X hd
    calc
      B * X < B * (d * (X / d + 1)) := Nat.mul_lt_mul_of_pos_left hXlt (Nat.pos_of_ne_zero hB)
      _ = (B * (X / d + 1)) * d := by ring
      _ < (B * (X / d + 1) + 1) * d := by
        exact Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) hd

set_option maxHeartbeats 1000000 in

theorem mainLayer_log_le_cutoff_log {X Y : Nat} (hz : 2 ≤ Nat.nthRoot 64 X) (hYX : Y ≤ X) :
    Real.log ((Y + 2 : Nat) : Real) ≤ 129 * Real.log (Nat.nthRoot 64 X : Real) := by
  let z := Nat.nthRoot 64 X
  have hroot : X < (z + 1) ^ 64 := by
    exact Nat.lt_pow_nthRoot_add_one (by norm_num) X
  have hzOne : 1 ≤ z := hz.trans' (by norm_num)
  have hzplus : z + 1 ≤ 2 * z := by omega
  have hpowMono : (z + 1) ^ 64 ≤ (2 * z) ^ 64 := pow_le_pow_left₀ (Nat.zero_le _) hzplus 64
  have hpowTwo : 1 ≤ (z + 1) ^ 64 := by
    have : 0 < (z + 1) ^ 64 := Nat.pow_pos (by omega)
    omega
  have hNat : Y + 2 ≤ 2 * (2 * z) ^ 64 := by
    calc
      Y + 2 ≤ X + 2 := Nat.add_le_add_right hYX 2
      _ ≤ (z + 1) ^ 64 + 1 := by omega
      _ ≤ 2 * ((z + 1) ^ 64) := by omega
      _ ≤ 2 * ((2 * z) ^ 64) := Nat.mul_le_mul_left 2 hpowMono
  have hcast : ((Y + 2 : Nat) : Real) ≤ 2 * ((2 * z : Nat) : Real) ^ 64 := by
    have hcastRaw : ((Y + 2 : Nat) : Real) ≤ ((2 * (2 * z) ^ 64 : Nat) : Real) := Nat.cast_le.2 hNat
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hcastRaw
  have hlogLe : Real.log ((Y + 2 : Nat) : Real) ≤ Real.log (2 * ((2 * z : Nat) : Real) ^ 64) :=
    Real.log_le_log
      (by
        exact_mod_cast (show 0 < Y + 2 by omega))
      hcast
  have hzPos : (0 : Real) < (z : Real) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hzOne)
  have htwozPos : (0 : Real) < (2 * z : Nat) := by positivity
  have hlogExpand : Real.log (2 * ((2 * z : Nat) : Real) ^ 64) =
        65 * Real.log 2 + 64 * Real.log (z : Real) := by
    push_cast
    rw [Real.log_mul
        (by norm_num : (2 : Real) ≠ 0)
        (pow_ne_zero 64 (by positivity : (2 * (z : Real)) ≠ 0)),
      Real.log_pow,
      Real.log_mul (by norm_num : (2 : Real) ≠ 0) hzPos.ne']
    ring
  have hlogTwoLe : Real.log 2 ≤ Real.log (z : Real) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast hz
  rw [hlogExpand] at hlogLe
  linarith

theorem mainLayer_log_ratio_le {X Y : Nat} (hz : 2 ≤ Nat.nthRoot 64 X) (hYX : Y ≤ X) :
    Real.log ((Y + 2 : Nat) : Real) /
        Real.log (Nat.nthRoot 64 X : Real) ≤
      129 := by
  have hlogPos : 0 < Real.log (Nat.nthRoot 64 X : Real) := by
    apply Real.log_pos
    exact_mod_cast hz
  exact (div_le_iff₀ hlogPos).2
    (by
      simpa [mul_comm] using mainLayer_log_le_cutoff_log hz hYX)

noncomputable def dualSieveLayerCoefficient (h : Prime) (B : Nat) : Real :=
  516 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real)

theorem dualSieveLayerCoefficient_nonneg (h : Prime) (B : Nat) :
    0 ≤ dualSieveLayerCoefficient h B := by
  unfold dualSieveLayerCoefficient
  positivity

theorem hasUniformMainLayerUpperBound_dualSieve (h : Prime) (B : Nat) :
    HasUniformMainLayerUpperBound h 64 B
      (dualSieveLayerCoefficient h B) := by
  intro ε hε
  have hzEventually : ∀ᶠ X : Nat in atTop, 2 ≤ Nat.nthRoot 64 X :=
    (nat_nthRoot_tendsto_atTop 64 (by norm_num)).eventually_ge_atTop 2
  have hhubEventually : ∀ᶠ X : Nat in atTop, h.1 ^ 2 ≤ X := eventually_ge_atTop (h.1 ^ 2)
  have herrorEventually := dualSieveError_normalized_eventually_lt hε
  filter_upwards [hzEventually, hhubEventually,
    herrorEventually] with X hzX hhubX herrorX
  intro a e he
  let d := h.1 ^ e
  let Y := X / d
  let Z := (B * X) / d
  let z := Nat.nthRoot 64 X
  have hdPos : 0 < d := by
    dsimp [d]
    exact Nat.pow_pos h.pos
  have hmain : Nat.sqrt X ≤ Y := by
    simpa [Y, d] using (Finset.mem_filter.mp he).2
  have hYX : Y ≤ X := by
    dsimp [Y]
    exact Nat.div_le_self X d
  have hhubSqrt : h.1 ≤ Nat.sqrt X := by
    exact Nat.le_sqrt'.2 hhubX
  have hhubY : h.1 ≤ Y := hhubSqrt.trans hmain
  have hYOne : 1 ≤ Y := h.one_lt.le.trans hhubY
  have hZ : Z ≤ B * (Y + 1) := by
    simpa [Z, Y, d] using mul_div_le_mul_div_add_one B X d hdPos
  have hYplus : Y + 1 ≤ 2 * Y := by omega
  have hNmul : (Z / h.1 + 1) * h.1 ≤ (2 * B + 1) * Y := by
    calc
      (Z / h.1 + 1) * h.1 = (Z / h.1) * h.1 + h.1 := by ring
      _ ≤ Z + h.1 := Nat.add_le_add (Nat.div_mul_le_self Z h.1) le_rfl
      _ ≤ B * (Y + 1) + Y := Nat.add_le_add hZ hhubY
      _ ≤ B * (2 * Y) + Y := Nat.add_le_add_right (Nat.mul_le_mul_left B hYplus) Y
      _ = (2 * B + 1) * Y := by ring
  have hhPos : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hN : ((Z / h.1 + 1 : Nat) : Real) ≤ ((2 * B + 1 : Nat) : Real) * (Y : Real) /
          (h.1 : Real) := by
    apply (le_div_iff₀ hhPos).2
    have hcast : (((Z / h.1 + 1) * h.1 : Nat) : Real) ≤ (((2 * B + 1) * Y : Nat) : Real) :=
      Nat.cast_le.2 hNmul
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using hcast
  have hzTwo : 2 ≤ z := by simpa [z] using hzX
  have hlogzPos : 0 < Real.log (z : Real) := by
    apply Real.log_pos
    exact_mod_cast hzTwo
  have hlogYPos : 0 < Real.log ((Y + 2 : Nat) : Real) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < Y + 2)
  have hvalueRatio : (Y : Real) / ((Y + 2 : Nat) : Real) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    exact_mod_cast (Nat.le_add_right Y 2)
  have hlocalMain : (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z) /
          primeCountingScale Y ≤
        dualSieveLayerCoefficient h B := by
    have hA : 4 * ((Z / h.1 + 1 : Nat) : Real) /
            ((Y + 2 : Nat) : Real) ≤
          4 * ((2 * B + 1 : Nat) : Real) /
            (h.1 : Real) := by
      calc
        4 * ((Z / h.1 + 1 : Nat) : Real) /
              ((Y + 2 : Nat) : Real) ≤
            4 *
                (((2 * B + 1 : Nat) : Real) * (Y : Real) /
                  (h.1 : Real)) /
              ((Y + 2 : Nat) : Real) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hN (by norm_num))
            (by positivity)
        _ = (4 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real)) *
              ((Y : Real) / ((Y + 2 : Nat) : Real)) := by ring
        _ ≤ 4 * ((2 * B + 1 : Nat) : Real) /
              (h.1 : Real) := by
          exact mul_le_of_le_one_right
            (by positivity) hvalueRatio
    have hL : Real.log ((Y + 2 : Nat) : Real) /
            Real.log z ≤ 129 := by
      simpa [z] using mainLayer_log_ratio_le hzX hYX
    have hLNonneg : 0 ≤ Real.log ((Y + 2 : Nat) : Real) /
            Real.log z :=
      (div_pos hlogYPos hlogzPos).le
    unfold primeCountingScale dualSieveLayerCoefficient
    have hYtwoNe : ((Y + 2 : Nat) : Real) ≠ 0 := by positivity
    have hlogYNe : Real.log ((Y + 2 : Nat) : Real) ≠ 0 := hlogYPos.ne'
    have hlogzNe : Real.log (z : Real) ≠ 0 := hlogzPos.ne'
    calc
      (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log (z : Real)) /
            (((Y + 2 : Nat) : Real) /
              Real.log ((Y + 2 : Nat) : Real)) =
          (4 * ((Z / h.1 + 1 : Nat) : Real) /
            ((Y + 2 : Nat) : Real)) *
            (Real.log ((Y + 2 : Nat) : Real) /
              Real.log (z : Real)) := by
        field_simp [hYtwoNe, hlogYNe, hlogzNe]
      _ ≤ (4 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real)) *
            129 :=
        mul_le_mul hA hL hLNonneg (by positivity)
      _ = 516 * ((2 * B + 1 : Nat) : Real) / (h.1 : Real) := by
        ring
  have herror : dualSieveError X / primeCountingScale Y < ε := herrorX Y hmain
  have hlayer := hardLayerUnits_card_real_le_simpler
      h z e a Y Z hzTwo
  have hlayer' : ((hardLayerUnits h z e a Y Z).card : Real) ≤
        4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z +
          dualSieveError X := by
    simpa [dualSieveError, z] using hlayer
  have hscaleNonneg : 0 ≤ primeCountingScale Y := (primeCountingScale_pos Y).le
  calc
    ((hardLayerUnits h (stageOldPrimeCutoff 64 X) e a
          (X / h.1 ^ e) ((B * X) / h.1 ^ e)).card : Real) /
          primeCountingScale (X / h.1 ^ e) =
        ((hardLayerUnits h z e a Y Z).card : Real) /
          primeCountingScale Y := by
      simp [stageOldPrimeCutoff, z, Y, Z, d]
    _ ≤ (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z +
          dualSieveError X) / primeCountingScale Y :=
      div_le_div_of_nonneg_right hlayer' hscaleNonneg
    _ = (4 * ((Z / h.1 + 1 : Nat) : Real) / Real.log z) /
            primeCountingScale Y +
          dualSieveError X / primeCountingScale Y := by
      rw [add_div]
    _ ≤ dualSieveLayerCoefficient h B + ε := (add_lt_add_of_le_of_lt hlocalMain herror).le

end Erdos279
end

section
open Filter Real
end
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
/- Compactly supported smooth functions for the Wiener–Ikehara argument. -/
structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun
theorem CS.ext' {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f; cases g; congr; funext x; exact h x
structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)
abbrev W21 := W1 2 ℂ
section lemmas
noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)
lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const
omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)
end lemmas
namespace CS
variable {f : CS n E} {R x v : ℝ}
instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun
instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩
def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2
instance : Neg (CS n E) where neg := neg
@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl
def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩
instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul
@[simp] lemma smul_apply : (R • f) x = R • f x := rfl
lemma continuous (f : CS n E) : Continuous f := f.h1.continuous
noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv
lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  apply CS.ext'; intro x ; exact (f.hasDerivAt x |>.const_smul R).deriv
noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)
lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  apply CS.ext'; intro v ; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv
lemma deriv_scale' {f : CS (n + 1) E} : (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]
lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • f.deriv (R⁻¹ • x)) x := by
  simpa [deriv_scale'] using hasDerivAt (f.scale R) x
lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]
lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩
end CS
namespace trunc
instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun
instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS
lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)
lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 := (g.h4 x).trans <| Set.indicator_le_self' (by simp) x
lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))
@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds
end trunc
namespace W1
instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun
lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous
lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f := f.smooth.differentiable (by simp)
lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]
noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt
def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)
instance : Sub (W1 n E) where sub := sub
lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih =>
      have hderiv : ⇑(SchwartzMap.derivCLM ℝ ℂ f) = _root_.deriv (f : ℝ → ℂ) := by
        funext x
        exact SchwartzMap.derivCLM_apply (𝕜 := ℝ) (F := ℂ) f x
      simpa [iteratedDeriv_succ', hderiv] using ih (f := SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz
end W1
namespace W21
variable {f : W21}
noncomputable def norm (f : ℝ → ℂ) : ℝ := (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f := add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))
noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun
noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz
def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance : Coe (CS 2 ℂ) W21 where coe := ofCS2
instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩
instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f
lemma hf (f : W21) : Integrable f := f.integrable zero_le_two
lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two
lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl
end W21
set_option maxHeartbeats 800000 in
theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    simpa [h, h', CS.deriv_scale'] using (CS.hasDerivAt_scale (g : CS 2 ℝ) R v).const_sub 1
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4
  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v : deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1]
        convert (l5.add l7).deriv using 1
        · congr 1
        · ring
      simp_rw [this, F]
    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g.toFun =ᶠ[𝓝 0] 0
        refine g.zero.deriv.trans ?_
        simp
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by
        change _root_.deriv g'.toFun =ᶠ[𝓝 0] 0
        refine evg'.deriv.trans ?_
        simp
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · rw [Filter.ZeroAtFilter]
        simpa [h] using ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
end
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
section lemmas
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp z.norm_coe
@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]
@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x
@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x
@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} : 𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourier_real_eq, ← integral_const_mul, Real.fourierChar, Circle.exp,
    ← smul_mul_assoc, mul_smul_comm]
end lemmas
theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) : (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

end
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev

end
section
open Filter Topology
namespace Asymptotics
variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}
variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']

theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop
end Asymptotics
end
section
namespace Function
variable {α : Type*} [Zero α]
end Function
end
section
open MeasureTheory Set Real
open scoped ContDiff
lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
end
section
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
@[simp] lemma W21.ofCS2_toFun (ψ : CS 2 ℂ) : (W21.ofCS2 ψ).toFun = ψ.toFun := rfl
@[simp] lemma W21.ofCS2_apply (ψ : CS 2 ℂ) (x : ℝ) : (W21.ofCS2 ψ : W21) x = ψ x := rfl
@[simp] lemma W21.sub_toFun (f g : W21) : (f - g).toFun = f.toFun - g.toFun := rfl
noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'
lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]
theorem norm_term_eq_nterm_re (s : ℂ) : ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s
lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]
instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop
lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]
lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by
  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp

lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith
lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    have hc : Continuous (fun p : ℝ × ℝ => ((rexp (-p.1 * (σ' - 1)) : ℝ) : ℂ) *
        ((𝐞 (Multiplicative.ofAdd (-(p.2 * (p.1 / (2 * π))))) : Circle) : ℂ)) := by
      apply Continuous.mul
      · fun_prop
      · exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
          (by fun_prop : Continuous fun p : ℝ × ℝ => -(p.2 * (p.1 / (2 * π)))))
    have := hc.measurable.mul (hcont.comp measurable_snd)
    convert this using 1
    funext p
    simp only [Function.uncurry, smul_eq_mul, Pi.mul_apply, Function.comp_apply]
    ring_nf
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2
lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith
lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by
  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  have e1 : ∀ u : ℝ, (↑(rexp (-u * (σ' - 1))) : ℂ) • 𝐞 (-(t * (u / (2 * π)))) • ψ t
      = cexp ((1 - σ' - t * I) * u) * ψ t := by
    intro u
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, smul_eq_mul, ofReal_exp,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [e1, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx
lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)
lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm
lemma decay_bounds_cor (ψ : W21) : ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩
lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf
lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) : Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa [div_eq_mul_inv] using (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    exact ((continuous_FourierIntegral ψ).comp (continuous_id.div_const c)).aestronglyMeasurable
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)
lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by
  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simp only [LSeries.term, h, ↓reduceIte]
      exact continuous_const.div₀
        (continuous_const.cpow (by fun_prop) (fun x => by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]
section nabla
variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}
def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i
def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)
def shift (u : α → E) (n : α) : E := u (n + 1)
@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]
lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) : cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]
@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]
lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])
lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)
omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]
omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]
end nabla
lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl
lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]
lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel
lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  change cumsum (a * b) (n + 1) =
    cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * (fun i => b (i + 1) - b i)) n
  simpa using summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)
lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'
lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1
lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO
lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]
lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }
lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply, one_mem,
    CStarRing.norm_of_mem_unitary, mul_one, eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩
lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]
lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := by omega
  simpa [r2] using hC (n - 1) r1
lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift, cumsum] using Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h
lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]
lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp
lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)
lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]
lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)
lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1
lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  · ext x
    simp only [Function.comp_apply]
    congr
    field_simp
    simp
  · rfl
lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp
lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)
lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h
lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring
lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le
lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1
lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring
lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by
  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by
        simpa [Function.comp_def] using
          (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)
  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))
lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)
lemma Real.log_eventually_gt_atTop (a : ℝ) : ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)
lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by
  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _
  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]
  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr e2), abs_of_pos (inv_pos.mpr e1)]
    exact inv_anti₀ e1 e3
  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    change nabla d =O[atTop] (fun n => (Real.log n) ^ 2)
    simpa [d] using (nnabla_mul_log_sq ((2 * π) ^ 2) hx)
  apply EventuallyEq.trans_isBigO l1
  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp
lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx
def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n
def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f
lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n
lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by
  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO
  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) := l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a, div_eq_mul_inv] using IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]
  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp
theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) : Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le
theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict
theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity
theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖
  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]
  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])
lemma limiting_fourier (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by
  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by
  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf
  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))
  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x
    rw [Real.fourier_real_eq]
    congr 1; ext t
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    field_simp
    try ring
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)
lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by
  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm
lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by
  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩
noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩
noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)
lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity
noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹
noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2
lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity
lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    have hpow := l4.pow 2
    have hpow' : HasDerivAt ((fun t : ℝ => a * log t) ^ 2)
        (2 * a ^ 2 * t⁻¹ * log t) t := hpow.congr_deriv (by ring)
    exact hpow'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.pow_apply])
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    have hprod := (hasDerivAt_id' t).mul l2
    have hprod' : HasDerivAt (((fun x : ℝ => x) * fun t => 1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t := by
      apply hprod.congr_deriv
      rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = 2 * a ^ 2 * log t by
        rw [show t * (2 * a ^ 2 * t⁻¹ * log t) = (t * t⁻¹) * (2 * a ^ 2 * log t) by ring]
        rw [mul_inv_cancel₀ ht, one_mul]]
      simp only [pp]
      ring
    have hprod'' : HasDerivAt (fun t : ℝ => t * (1 + (a * Real.log t) ^ 2))
        (pp a (log t)) t :=
      hprod'.congr_of_eventuallyEq (Eventually.of_forall fun s => by simp [Pi.mul_apply])
    exact hprod''.congr_deriv (by
      simp only [pp]
      ring)
  change HasDerivAt (fun t : ℝ => (t * (1 + (a * log t) ^ 2))⁻¹) (hh' a t) t
  apply (l1.inv e1).congr_deriv
  simp only [hh', pp, hh]
  field_simp [inv_eq_one_div, e1, ht]
  ring
lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt
lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity
lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)
noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹
lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp
lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)
lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · have : 0 < 1 / (2 * π) := by positivity
    linarith
  · rw [div_lt_iff₀ (by positivity : 0 < 2 * π)]
    have hπ : (2 : ℝ) ≤ π := two_le_pi
    nlinarith
lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by
  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa [cumsum] using hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf
  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    have hcomm : (∑ i ∈ Finset.range (n - 1), (g i - g (i + 1)) * (C * (↑i + 1))) =
          ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) := by
      simp [smul_eq_mul, mul_comm, mul_left_comm]
    rw [hcomm]
    refine le_of_eq ?_
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring
lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring
lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 =>
      convert cancel_aux' hf hg hf' hg' (n + 2) using 1
      · simp [cumsum, Finset.sum_range_succ, add_comm, add_left_comm]
      · simp [cumsum_succ, Nat.cast_add, Nat.cast_ofNat, add_assoc, add_comm]
        ring
theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by
  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]
  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp
  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by
      simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp
  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith
  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)
  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact _root_.add_le_add l1 l3
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp
lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]
  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹
  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have hder : HasDerivAt (fun t => log (t / c)) ((x / c)⁻¹ * (1 / c)) x :=
      @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _
        (l3 (x / c) (by positivity)) (l4 x)
    have heq : c / x * c⁻¹ = x⁻¹ := by
      field_simp [hc.ne', hx.ne']
    simpa [heq] using hder
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    have hder := (l1 x hx).const_mul (a * c / b)
    have heq : (a * c / b) * ((1 + (b * log (x / c)) ^ 2)⁻¹ * (b * x⁻¹)) = g' x := by
      simp only [g']
      field_simp [inv_eq_one_div, hb.ne', hc.ne', hx.ne']
    simpa [g, heq] using hder
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]
  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id
  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]
  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]
  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity
  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring
lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1
lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2
lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring
lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i
  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1
  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))
  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv
  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp
  refine (cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n).trans ?_
  apply mul_le_mul_of_nonneg_left ?_ l3
  simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]
  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  have hsum_ico : (∑ x_1 ∈ Finset.Ico 1 n,
          if x_1 = 0 then 1 else x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x)) =
        ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_Ico] at hi
    have : i ≠ 0 := by omega
    simp [this]
  rw [hsum_ico]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa [one_div, mul_inv_rev] using (this.mono_set Ioi_subset_Ici_self).integrable
lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx
lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx
variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  calc
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖
        = ‖f i / i‖ * ‖𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ := by
          rw [norm_mul]
    _ ≤ ‖f i / i‖ * (W21.norm ψ * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
            (norm_nonneg (f i / i))
    _ = W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
          simp only [Complex.norm_div, RCLike.norm_natCast]
          ring
lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))
lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  calc
    (∑' (i : ℕ), ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖)
        ≤ ∑' (i : ℕ),
            W21.norm ψ * (‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹) :=
          Summable.tsum_mono l1 (by simpa [smul_eq_mul] using l5.const_smul (W21.norm ψ)) l6
    _ = W21.norm ψ *
          ∑' (i : ℕ), ‖f i‖ / ↑i * (1 + (1 / (2 * π) * Real.log (↑i / x)) ^ 2)⁻¹ := by
          simpa [smul_eq_mul] using Summable.tsum_const_smul (W21.norm ψ) l5
lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by
  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)
lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by
  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · exact ((continuous_FourierIntegral ψ).comp (continuous_id.div_const _)).norm.aestronglyMeasurable
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl
lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by
  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    change ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ < ε / 2
    have : 0 < 1 + M := by positivity
    have hbound : ‖S x (ψ - W21.ofCS2 (Ψ R)).toFun‖ ≤ W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun * M := by
      simpa [S, S1, S2, M] using @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply hbound.trans_lt
    have hnorm : W21.norm (ψ - W21.ofCS2 (Ψ R)).toFun = W21.norm (ψ.toFun - (Ψ R).toFun) := by
      simp [W21.ofCS2]
    rw [hnorm]
    have hMle : M ≤ 1 + M := by linarith
    apply (mul_le_mul_of_nonneg_left hMle W21.norm_nonneg).trans_lt
    calc
      W21.norm (ψ.toFun - (Ψ R).toFun) * (1 + M)
          < (ε / 2 / (1 + M)) * (1 + M) := mul_lt_mul_of_pos_right hRψ this
      _ = ε / 2 := by field_simp [this.ne']
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]
  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict
  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)
lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'
lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f
noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2
@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl
lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))
lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus
lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2
theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by
  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this
theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε
  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]
  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε
  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]
lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    have hprod : HasCompactSupport
        (((fun x : ℝ => cexp (2 * ↑π * ↑x)) * fun x => Ψ (rexp (2 * π * x)))) :=
      (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
    rw [hasCompactSupport_iff_eventuallyEq] at hprod ⊢
    exact hprod.mono fun x hx => by
      simpa [h, Pi.mul_apply] using hx
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)
  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]
  have key := limiting_cor_schwartz g hf hcheby hG hG'
  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp
  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx
  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus
  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4
lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by
  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key
lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by
  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp
lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by
  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp
lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩
lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)
lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith
lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx
lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith
lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith
lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]
lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]
theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume (Function.support ψ ∩ Ioi 0) := by
      calc
        (1 : ENNReal) = volume (Ico (1 : ℝ) 2) := by
          simp [Real.volume_Ico]
          norm_num
        _ ≤ volume (Function.support ψ ∩ Ioi 0) := volume.mono r4
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this
lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith
lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]
lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]
lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]
lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]
lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]
lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop
lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring
noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N
lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    rw [Finset.range_eq_Ico] ; symm ; rw [Finset.range_eq_Ico]
    exact Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _)
      (Nat.ceil_le.mpr (mul_le_of_le_one_left N.cast_nonneg hε))
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]
lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [Real.dist_eq, ← S_sub_S h2.2] using l2.trans_lt h1
set_option maxHeartbeats 1000000 in
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by
  have h_event : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Tendsto (S f ε) atTop (𝓝 (A * (1 - ε))) := by
    have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    intro ε hε
    have hdisc := WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
    exact hdisc.congr' (Eventually.of_forall fun N => by simp [S])
  have hlim : Tendsto (fun ε : ℝ => A * (1 - ε)) (𝓝[>] 0) (𝓝 A) := by
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (hε.const_sub 1).const_mul A
  have hmain : Tendsto (S f 0) atTop (𝓝 A) :=
    (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto h_event hlim
  exact hmain.congr' (Eventually.of_forall fun N => by simp [S, cumsum])
end

section
open Real ArithmeticFunction ArithmeticFunction.vonMangoldt
theorem vonMangoldt_cheby : cheby (fun n => (vonMangoldt n : ℂ)) := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, Complex.norm_real, Real.norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith

end

section

namespace Erdos279

open ArithmeticFunction
open ArithmeticFunction.vonMangoldt
open Complex Filter LSeries Set Topology

theorem residueClass_cheby {q : Nat} (a : ZMod q) :
    cheby (fun n => (residueClass a n : Complex)) := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, ?_⟩
  intro N
  have hCN := hC N
  unfold cumsum at hCN ⊢
  calc
    ∑ n ∈ Finset.range N, ‖(residueClass a n : Complex)‖ ≤
        ∑ n ∈ Finset.range N, ‖(vonMangoldt n : Complex)‖ := by
      gcongr with n hn
      have hΛ : 0 ≤ vonMangoldt n := vonMangoldt_nonneg
      rw [Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (residueClass_nonneg a n),
        abs_of_nonneg hΛ]
      exact residueClass_le a n
    _ ≤ C * (N : Real) := hCN

theorem weightedProgressionPNT {q a : Nat} (hq : 0 < q) (ha : a.Coprime q) : Tendsto (fun N =>
        cumsum
          (residueClass (a : ZMod q)) N / (N : Real))
      atTop
      (nhds ((Nat.totient q : Real)⁻¹)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let az : ZMod q := a
  let f : Nat → Real := residueClass az
  let density : Real := (Nat.totient q : Real)⁻¹
  let G : Complex → Complex := LFunctionResidueClassAux az
  have haUnit : IsUnit az := by
    exact (ZMod.isUnit_iff_coprime a q).2 ha
  have hnonneg : 0 ≤ f := by
    intro n
    exact residueClass_nonneg az n
  have hsummable : ∀ σ : Real, 1 < σ → Summable
          (nterm (fun n => (f n : Complex)) σ) := by
    intro σ hσ
    have habscissa : abscissaOfAbsConv (fun n => (f n : Complex)) < (σ : Complex).re := by
      simpa [f] using (abscissaOfAbsConv_residueClass_le_one az).trans_lt
          (by exact_mod_cast hσ)
    have hL : LSeriesSummable (fun n => (f n : Complex)) (σ : Complex) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re habscissa
    simpa only [← nterm_eq_norm_term] using hL.norm
  have hcheby : cheby (fun n => (f n : Complex)) := by
    simpa [f] using residueClass_cheby az
  have hcontinuous : ContinuousOn G {s | 1 ≤ s.re} := by
    simpa [G] using continuousOn_LFunctionResidueClassAux az
  have hcastTotientInv : ((Nat.totient q : Complex)⁻¹) = (density : Complex) := by
    dsimp [density]
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_inv _).symm
  have hWI : Tendsto
        (fun N => cumsum f N / (N : Real))
        atTop
        (nhds density) := by
    apply WienerIkeharaTheorem'
      (A := density)
      (G := G)
      hnonneg hsummable hcheby hcontinuous
    intro s hs
    have hsource : G s = LSeries (fun n => (f n : Complex)) s -
            (Nat.totient q : Complex)⁻¹ / (s - 1) := by
      simpa only [G, f] using (eqOn_LFunctionResidueClassAux haUnit hs)
    calc
      G s = LSeries (fun n => (f n : Complex)) s -
            (Nat.totient q : Complex)⁻¹ / (s - 1) :=
        hsource
      _ = LSeries (fun n => (f n : Complex)) s -
            (density : Complex) /
              (s - 1) := by
        rw [hcastTotientInv]
  simpa [az, f, density] using hWI

end Erdos279
end

section

namespace Erdos279

open ArithmeticFunction Nat Finset BigOperators Filter Real
  Asymptotics
open scoped Chebyshev

theorem Asymptotics.IsEquivalent.sub_isLittleO_right {α β : Type*} [NormedAddCommGroup β]
    {u v w : α → β} {l : Filter α}
    (huv : IsEquivalent l u v)
    (huw : (u - w) =o[l] v) :
    IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact huv.sub_isLittleO huw

theorem isLittleO_sqrt_mul_log_atTop : (fun x : Real => x.sqrt * x.log) =o[atTop] (fun x => x) := by
  refine (isLittleO_mul_iff_isLittleO_div ?_).2 ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact (Real.sqrt_ne_zero hx.le).2 hx.ne'
  · have heq : (fun x : ℝ => x / x.sqrt) = (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
      funext x
      rw [div_sqrt, Real.sqrt_eq_rpow]
    change Real.log =o[atTop] (fun x : ℝ => x / x.sqrt)
    rw [heq]
    exact isLittleO_log_rpow_atTop (by norm_num)

theorem tendsto_floor_add_one_div_self_ap : Tendsto (fun x : Real => ((⌊x⌋₊ + 1 : Nat) : Real) / x)
      atTop (nhds 1) := by
  have hfloor := Asymptotics.isEquivalent_nat_floor (R := Real)
  have hfloor' : IsEquivalent atTop
        (fun x : Real => (⌊x⌋₊ : Real) + 1)
        _root_.id :=
    hfloor.add_isLittleO
      (Asymptotics.isLittleO_const_id_atTop 1)
  have htendsto := (isEquivalent_iff_tendsto_one
      (by
        filter_upwards [eventually_gt_atTop 0] with x hx hzero
        simp only [_root_.id] at hzero
        exact hx.ne' hzero)).1 hfloor'
  change Tendsto (fun x : ℝ => ((⌊x⌋₊ : ℝ) + 1) / x) atTop (nhds 1) at htendsto
  simpa only [Nat.cast_add, Nat.cast_one] using htendsto

theorem isTheta_self_div_const_ap {c : Real} (hc : c ≠ 0) : (fun x : Real => x) =Θ[atTop]
      (fun x => x / c) := by
  have heq : (fun x : Real => x / c) = fun x => c⁻¹ * x := by
    funext x
    ring
  exact heq ▸
    ((isTheta_const_mul_left (inv_ne_zero hc)).2
      (isTheta_refl ..)).symm

theorem filter_prime_Iic_eq_Icc_ap (n : Nat) : filter Nat.Prime (Iic n) =
      filter Nat.Prime (Icc 1 n) := by
  ext p
  simp only [mem_filter, mem_Iic, mem_Icc,
    and_congr_left_iff]
  exact fun hp => ⟨fun h => ⟨hp.one_lt.le, h⟩,
      fun h => h.2⟩

theorem Icc_zero_eq_insert_ap (n : Nat) : Icc 0 n = insert 0 (Icc 1 n) := by
  ext m
  simp [mem_Icc]
  omega

noncomputable def progressionTheta (q a : Nat) (x : Real) : Real :=
  ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
    if p % q = a % q then Real.log p else 0

theorem progressionTheta_isEquivalent {q a : Nat} (hq : 0 < q) (ha : a.Coprime q) :
    progressionTheta q a ~[atTop]
      (fun x => x / (Nat.totient q : Real)) := by
  letI : NeZero q := ⟨hq.ne'⟩
  let psiAQ : Real → Real := fun x => ∑ n ∈ Icc 1 ⌊x⌋₊,
        if n % q = a % q then
          vonMangoldt n
        else 0
  have htotPos : (0 : Real) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hweighted : Tendsto
        (fun N => (∑ n ∈ Iio N,
              if n % q = a % q then
                vonMangoldt n
              else 0) / (N : Real))
        atTop
        (nhds (1 / (Nat.totient q : Real))) := by
    have hW := weightedProgressionPNT hq ha
    simpa only [one_div, cumsum, ← Nat.Iio_eq_range,
      ArithmeticFunction.vonMangoldt.residueClass,
      Set.indicator_apply, Set.mem_setOf_eq,
      ZMod.natCast_eq_natCast_iff'] using hW
  have hpsi : psiAQ ~[atTop]
        (fun x => x / (Nat.totient q : Real)) := by
    have hpsiEq (x : Real) : psiAQ x = ∑ n ∈ Iio (⌊x⌋₊ + 1),
            if n % q = a % q then
              vonMangoldt n
            else 0 := by
      simp only [psiAQ,
        show Icc 1 ⌊x⌋₊ = (Iio (⌊x⌋₊ + 1)).filter (1 ≤ ·) by
            ext n
            simp [mem_Icc, mem_filter,
              Nat.lt_add_one_iff]
            tauto,
        sum_filter]
      refine sum_congr rfl fun n _ => ?_
      by_cases hn : 1 ≤ n
      · simp only [hn, ↓reduceIte]
      · push_neg at hn
        interval_cases n
        simp
    refine (isEquivalent_iff_tendsto_one ?_).2 ?_
    · filter_upwards [eventually_ge_atTop 1] with x hx
      exact div_ne_zero (by linarith) htotPos.ne'
    have hlim : Tendsto
          (fun x : Real => (∑ n ∈ Iio (⌊x⌋₊ + 1),
                if n % q = a % q then
                  vonMangoldt n
                else 0) /
              ((⌊x⌋₊ + 1 : Nat) : Real))
          atTop
          (nhds (1 / (Nat.totient q : Real))) := by
      have heq : (fun x : Real => (∑ n ∈ Iio (⌊x⌋₊ + 1),
                if n % q = a % q then
                  vonMangoldt n
                else 0) /
              ((⌊x⌋₊ + 1 : Nat) : Real)) =
            (fun N => (∑ n ∈ Iio N,
                  if n % q = a % q then
                    vonMangoldt n
                  else 0) / (N : Real)) ∘
              (fun x : Real => ⌊x⌋₊ + 1) := by
        funext x
        rfl
      exact heq ▸
        hweighted.comp
          ((tendsto_add_atTop_nat 1).comp
            tendsto_nat_floor_atTop)
    have hratio : (psiAQ /
            fun x => x / (Nat.totient q : Real)) =
          fun x => psiAQ x / x *
              (Nat.totient q : Real) := by
      funext x
      simp only [Pi.div_apply, div_div_eq_mul_div]
      ring
    rw [hratio,
      show (1 : Real) = 1 / (Nat.totient q : Real) * 1 *
            (Nat.totient q : Real) by
        field_simp]
    refine Tendsto.mul ?_ tendsto_const_nhds
    have hevent : (fun x => psiAQ x / x) =ᶠ[atTop]
          fun x => ((∑ n ∈ Iio (⌊x⌋₊ + 1),
                if n % q = a % q then
                  vonMangoldt n
                else 0) /
              ((⌊x⌋₊ + 1 : Nat) : Real)) *
            (((⌊x⌋₊ + 1 : Nat) : Real) / x) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [hpsiEq]
      field_simp
    exact Tendsto.congr' hevent.symm
      (hlim.mul tendsto_floor_add_one_div_self_ap)
  refine Asymptotics.IsEquivalent.sub_isLittleO_right hpsi
    (IsBigO.trans_isLittleO
      (g := fun x => 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']
    refine ⟨1, one_pos,
      eventually_atTop.mpr ⟨2, fun x hx => ?_⟩⟩
    simp only [Pi.sub_apply, norm_eq_abs, one_mul]
    have hdiffNonneg : 0 ≤ psiAQ x - progressionTheta q a x := by
      simp only [psiAQ, progressionTheta, sub_nonneg]
      calc
        (∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
            if p % q = a % q then
              Real.log p
            else 0) ≤
          ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
            if p % q = a % q then
              vonMangoldt p
            else 0 := by
          apply sum_le_sum
          intro p hp
          split_ifs
          · simp [vonMangoldt_apply_prime
              (mem_filter.mp hp).2]
          · rfl
        _ ≤ ∑ n ∈ Icc 1 ⌊x⌋₊,
            if n % q = a % q then
              vonMangoldt n
            else 0 := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro p hp
            simp only [mem_filter, mem_Iic,
              mem_Icc] at hp ⊢
            exact ⟨hp.2.one_lt.le, hp.1⟩
          · intro n hn hnot
            split_ifs
            · exact vonMangoldt_nonneg
            · rfl
    have hdiffLe : psiAQ x - progressionTheta q a x ≤ Chebyshev.psi x - Chebyshev.theta x := by
      simp only [psiAQ, progressionTheta,
        Chebyshev.psi_eq_sum_Icc,
        Chebyshev.theta_eq_sum_Icc]
      conv_rhs =>
        rw [Icc_zero_eq_insert_ap,
          sum_insert
            (by simp : (0 : Nat) ∉ Icc 1 ⌊x⌋₊),
          show vonMangoldt 0 = 0 by
            simp only [ArithmeticFunction.map_zero],
          zero_add,
          show filter Nat.Prime
                (insert 0 (Icc 1 ⌊x⌋₊)) =
              filter Nat.Prime (Icc 1 ⌊x⌋₊) by
            simp [filter_insert, Nat.not_prime_zero]]
      rw [filter_prime_Iic_eq_Icc_ap,
        ← sum_filter_add_sum_filter_not
          (Icc 1 ⌊x⌋₊) Nat.Prime,
        show
          (∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            if p % q = a % q then
              Real.log p
            else 0) =
          ∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            if p % q = a % q then
              vonMangoldt p
            else 0 by
          apply sum_congr rfl
          intro p hp
          simp only [mem_filter] at hp
          split_ifs
          · simp [vonMangoldt_apply_prime hp.2]
          · rfl,
        ← sum_filter_add_sum_filter_not
          (Icc 1 ⌊x⌋₊) Nat.Prime,
        show
          (∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            vonMangoldt p) =
          ∑ p ∈ filter Nat.Prime
              (Icc 1 ⌊x⌋₊),
            Real.log p by
          exact sum_congr rfl fun p hp => vonMangoldt_apply_prime
              (mem_filter.mp hp).2]
      have hnonprime : (∑ n ∈ (Icc 1 ⌊x⌋₊).filter
              (¬Nat.Prime ·),
            if n % q = a % q then
              vonMangoldt n
            else 0) ≤
          ∑ n ∈ (Icc 1 ⌊x⌋₊).filter
              (¬Nat.Prime ·),
            vonMangoldt n := by
        apply sum_le_sum
        intro n hn
        split_ifs
        · exact le_rfl
        · exact vonMangoldt_nonneg
      linarith
    rw [abs_of_nonneg hdiffNonneg,
      abs_of_nonneg (by bound)]
    exact hdiffLe.trans
      ((le_abs_self _).trans
        (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log
          (by linarith)))
  · simpa only [mul_assoc] using (isLittleO_sqrt_mul_log_atTop.const_mul_left 2
        |>.trans_isTheta
          (isTheta_self_div_const_ap htotPos.ne'))

end Erdos279
end

section

namespace Erdos279

def PrimeInModEq (q a n : Nat) : Prop := IsPrime n ∧ n ≡ a [MOD q]

def FixedProgressionPrimeNumberTheorem (q : Nat) : Prop := ∀ a : Nat, a.Coprime q →
    HasPrimeCountingAsymptotic
      (PrimeInModEq q a)
      (1 / (Nat.totient q : Real))

theorem primeInModEq_disjoint {q a b : Nat} (ha : a < q) (hb : b < q) (hab : a ≠ b) : ∀ n, ¬
      (PrimeInModEq q a n ∧ PrimeInModEq q b n) := by
  intro n hn
  have hna : n % q = a := by
    simpa [PrimeInModEq, Nat.ModEq,
      Nat.mod_eq_of_lt ha] using hn.1.2
  have hnb : n % q = b := by
    simpa [PrimeInModEq, Nat.ModEq,
      Nat.mod_eq_of_lt hb] using hn.2.2
  exact hab (hna.symm.trans hnb)

theorem fixedProgressionPNT_finiteUnion {q : Nat} (R : Finset Nat) (hRlt : ∀ a ∈ R, a < q)
    (hRcoprime : ∀ a ∈ R, a.Coprime q)
    (hPNT : FixedProgressionPrimeNumberTheorem q) :
    HasPrimeCountingAsymptotic
      (fun n => ∃ a ∈ R, PrimeInModEq q a n)
      ((R.card : Real) /
        (Nat.totient q : Real)) := by
  have hUnion := hasPrimeCountingAsymptotic_exists_mem_finset
      R (fun a => PrimeInModEq q a)
      (fun _ => 1 / (Nat.totient q : Real))
      (by
        intro a ha b hb hab n
        exact primeInModEq_disjoint
            (hRlt a ha) (hRlt b hb)
            hab n)
      (by
        intro a ha
        exact hPNT a (hRcoprime a ha))
  simpa [Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv] using hUnion

theorem primeNatPredicate_periodicPool_iff (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (n : Nat) :
    primeNatPredicate (InPeriodicPrimePool h L R) n ↔ ∃ c ∈ R,
        PrimeInModEq (h.1 * L.1)
          (periodicCrtClass h L hcop c) n := by
  constructor
  · rintro ⟨hnPrime, hnPool⟩
    let p : Prime := ⟨n, hnPrime⟩
    obtain ⟨c, hcR, hnc⟩ := (inPeriodicPrimePool_iff_exists_modEq
        h L hcop R hR p).1 hnPool
    exact ⟨c, hcR, hnPrime, hnc⟩
  · rintro ⟨c, hcR, hnPrime, hnc⟩
    let p : Prime := ⟨n, hnPrime⟩
    refine ⟨hnPrime, ?_⟩
    exact (inPeriodicPrimePool_iff_exists_modEq
        h L hcop R hR p).2
        ⟨c, hcR, hnc⟩

theorem periodicCrtClasses_disjoint (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L) :
    ∀ a ∈ R, ∀ b ∈ R, a ≠ b → ∀ n, ¬
        (PrimeInModEq (h.1 * L.1)
            (periodicCrtClass h L hcop a) n ∧
          PrimeInModEq (h.1 * L.1)
            (periodicCrtClass h L hcop b) n) := by
  intro a ha b hb hab n hn
  have hnaMod : n ≡ a [MOD L.1] := (hn.1.2.of_mul_left h.1).trans
      (periodicCrtClass_modEq_aux
        h L hcop a)
  have hnbMod : n ≡ b [MOD L.1] := (hn.2.2.of_mul_left h.1).trans
      (periodicCrtClass_modEq_aux
        h L hcop b)
  have haLt : a < L.1 := (mem_reducedResidues.mp (hR ha)).1
  have hbLt : b < L.1 := (mem_reducedResidues.mp (hR hb)).1
  have hna : n % L.1 = a := by
    simpa [Nat.ModEq,
      Nat.mod_eq_of_lt haLt] using hnaMod
  have hnb : n % L.1 = b := by
    simpa [Nat.ModEq,
      Nat.mod_eq_of_lt hbLt] using hnbMod
  exact hab (hna.symm.trans hnb)

theorem periodicPrimePool_countingAsymptotic (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * L.1)) :
    HasProjectPrimeCountingAsymptotic
      (InPeriodicPrimePool h L R)
      ((R.card : Real) /
        (Nat.totient (h.1 * L.1) : Real)) := by
  have hUnion := hasPrimeCountingAsymptotic_exists_mem_finset
      R
      (fun c => PrimeInModEq (h.1 * L.1)
          (periodicCrtClass h L hcop c))
      (fun _ => 1 /
          (Nat.totient (h.1 * L.1) : Real))
      (periodicCrtClasses_disjoint
        h L hcop R hR)
      (by
        intro c hc
        exact hPNT
            (periodicCrtClass h L hcop c)
            (periodicCrtClass_coprime_modulus
              h L hcop (hR hc)))
  have hPred : primeNatPredicate
          (InPeriodicPrimePool h L R) =
        (fun n => ∃ c ∈ R,
            PrimeInModEq (h.1 * L.1)
              (periodicCrtClass h L hcop c) n) := by
    funext n
    apply propext
    exact primeNatPredicate_periodicPool_iff
        h L hcop R hR n
  unfold HasProjectPrimeCountingAsymptotic
  rw [hPred]
  simpa [Finset.sum_const, nsmul_eq_mul,
    div_eq_mul_inv] using hUnion

theorem totient_hub_mul_aux (h L : Prime) (hcop : h.1.Coprime L.1) : Nat.totient (h.1 * L.1) =
      (h.1 - 1) * (L.1 - 1) := by
  rw [Nat.totient_mul hcop,
    Nat.totient_prime h.natPrime,
    Nat.totient_prime L.natPrime]

theorem periodicReservoir_countingAsymptotic (h L : Prime) (hcop : h.1.Coprime L.1)
    (R : Finset Nat) (hR : R ⊆ reducedResidues L)
    (H : Finset Prime) (N : Nat)
    (hH : ∀ p ∈ H, p.1 < N)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * L.1)) :
    HasProjectPrimeCountingAsymptotic
      (InPeriodicReservoir h L R H)
      ((R.card : Real) /
        (Nat.totient (h.1 * L.1) : Real)) := by
  have hPool := periodicPrimePool_countingAsymptotic
      h L hcop R hR hPNT
  unfold HasProjectPrimeCountingAsymptotic at hPool ⊢
  exact hPool.congr_of_eventually_iff N
      (by
        intro n hn
        constructor
        · rintro ⟨hnPrime, hnPool, hnH⟩
          exact ⟨hnPrime, hnPool⟩
        · rintro ⟨hnPrime, hnPool⟩
          refine ⟨hnPrime, hnPool, ?_⟩
          intro hpH
          let p : Prime := ⟨n, hnPrime⟩
          have hpLt : p.1 < N := hH p hpH
          exact (Nat.not_lt_of_ge hn) hpLt)

theorem mesh_periodicReservoir_countingAsymptotic {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * M.modulus.1)) :
    HasProjectPrimeCountingAsymptotic
      (InPeriodicReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      M.periodicDensity := by
  have hcop : h.1.Coprime M.modulus.1 := M.hub_coprime_modulus
  have hReservoir := periodicReservoir_countingAsymptotic
      h M.modulus hcop
      M.classes M.classes_reduced
      (oldControllerPrimes h M.cutoff)
      (M.cutoff + 1)
      (by
        intro p hp
        have hpLe : p.1 ≤ M.cutoff := (mem_oldControllerPrimes.mp hp).2
        omega)
      hPNT
  have hhReal : (h.1 : Real) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (Nat.ne_of_gt h.one_lt)
  have hLReal : (M.modulus.1 : Real) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast
      (Nat.ne_of_gt M.modulus.one_lt)
  have hDensity : ((M.classes.card : Real) /
          (Nat.totient
            (h.1 * M.modulus.1) : Real)) =
        M.periodicDensity := by
    rw [totient_hub_mul_aux
      h M.modulus hcop,
      M.card_classes]
    unfold
      OldControllerPrimeDensityMesh.periodicDensity
      controllerDensity
    rw [Nat.cast_mul,
      Nat.cast_sub h.one_lt.le,
      Nat.cast_sub M.modulus.one_lt.le]
    field_simp [hhReal, hLReal]
    ring
  rw [← hDensity]
  exact hReservoir

end Erdos279
end

section

namespace Erdos279

open ArithmeticFunction Nat Finset BigOperators Filter Real
  Asymptotics

noncomputable def progressionPrimes (q a : Nat) (x : Real) : Finset Nat :=
  (Iic ⌊x⌋₊).filter fun p => p.Prime ∧ p % q = a % q

noncomputable def progressionPrimeCountReal (q a : Nat) (x : Real) : Real :=
  ((progressionPrimes q a x).card : Real)

theorem progressionTheta_eq_sum_progressionPrimes (q a : Nat) (x : Real) : progressionTheta q a x =
      ∑ p ∈ progressionPrimes q a x,
        Real.log p := by
  classical
  unfold progressionTheta progressionPrimes
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp [_root_.and_left_comm, and_assoc]
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simp [hp.2.2]

theorem progressionTheta_le_count_mul_log {q a : Nat} {x : Real} (hx : 2 ≤ x) :
    progressionTheta q a x ≤ progressionPrimeCountReal q a x * Real.log x := by
  rw [progressionTheta_eq_sum_progressionPrimes]
  unfold progressionPrimeCountReal
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  simp only [one_mul]
  apply Real.strictMonoOn_log.monotoneOn
  · have hpPrime : p.Prime := (Finset.mem_filter.mp
        (show p ∈ progressionPrimes q a x from hp)).2.1
    show (0 : Real) < (p : Real)
    exact_mod_cast hpPrime.pos
  · show (0 : Real) < x
    exact lt_of_lt_of_le (by norm_num) hx
  · have hpLeFloor : p ≤ ⌊x⌋₊ := (Finset.mem_filter.mp
        (show p ∈ progressionPrimes q a x from hp)).1
        |> Finset.mem_Iic.mp
    exact (Nat.cast_le.mpr hpLeFloor).trans
      (Nat.floor_le (by linarith))

theorem theta_div_log_le_progressionPrimeCount {q a : Nat} {x : Real} (hx : 2 ≤ x) :
    progressionTheta q a x / Real.log x ≤ progressionPrimeCountReal q a x := by
  rw [div_le_iff₀ (Real.log_pos (by linarith))]
  simpa [mul_comm] using progressionTheta_le_count_mul_log
      (q := q) (a := a) hx

theorem small_progression_indicator_sum_le (q a : Nat) (x r : Real) :
    (∑ p ∈ progressionPrimes q a x,
        if p ≤ ⌊x ^ r⌋₊ then (1 : Real) else 0) ≤
      (⌊x ^ r⌋₊ : Real) + 1 := by
  classical
  have hnat : (∑ p ∈ progressionPrimes q a x,
          if p ≤ ⌊x ^ r⌋₊ then 1 else 0) ≤
        ⌊x ^ r⌋₊ + 1 := by
    calc
      (∑ p ∈ progressionPrimes q a x,
          if p ≤ ⌊x ^ r⌋₊ then 1 else 0) =
          ((progressionPrimes q a x).filter
            fun p => p ≤ ⌊x ^ r⌋₊).card := by
        simp
      _ ≤ (Iic ⌊x ^ r⌋₊).card := by
        apply Finset.card_le_card
        intro p hp
        simp only [Finset.mem_filter] at hp
        exact Finset.mem_Iic.mpr hp.2
      _ = ⌊x ^ r⌋₊ + 1 := by
        simp
  exact_mod_cast hnat

theorem one_le_log_div_add_small_indicator {q a : Nat} {x r : Real} (hx : 1 < x) (hr0 : 0 < r)
    {p : Nat} (hp : p ∈ progressionPrimes q a x) :
    (1 : Real) ≤ Real.log p / (r * Real.log x) +
        if p ≤ ⌊x ^ r⌋₊ then 1 else 0 := by
  have hden : 0 < r * Real.log x := mul_pos hr0 (Real.log_pos hx)
  by_cases hsmall : p ≤ ⌊x ^ r⌋₊
  · rw [if_pos hsmall]
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hlogp : 0 ≤ Real.log p := by
      exact Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le)
    have hquot : 0 ≤ Real.log p / (r * Real.log x) := div_nonneg hlogp hden.le
    linarith
  · rw [if_neg hsmall, add_zero,
      le_div_iff₀ hden]
    have hfloorLt : ⌊x ^ r⌋₊ < p := by
      omega
    have hyNonneg : 0 ≤ x ^ r := Real.rpow_nonneg (by linarith) r
    have hyLtP : x ^ r < (p : Real) := by
      exact (Nat.lt_floor_add_one (x ^ r)).trans_le
        (by exact_mod_cast hfloorLt)
    have hlog : Real.log (x ^ r) ≤ Real.log p := by
      exact Real.strictMonoOn_log.monotoneOn
        (Real.rpow_pos_of_pos (by linarith) r)
        (by
          have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
          show (0 : Real) < (p : Real)
          exact_mod_cast hpPrime.pos)
        hyLtP.le
    rw [Real.log_rpow (by linarith)] at hlog
    simpa only [one_mul] using hlog

theorem progressionPrimeCount_le_theta_add_power {q a : Nat} {x r : Real}
    (hx : 1 < x) (hr0 : 0 < r) :
    progressionPrimeCountReal q a x ≤ progressionTheta q a x /
          (r * Real.log x) +
        (x ^ r + 1) := by
  classical
  have hsum : (∑ p ∈ progressionPrimes q a x, (1 : Real)) ≤ ∑ p ∈ progressionPrimes q a x,
          (Real.log p / (r * Real.log x) +
            if p ≤ ⌊x ^ r⌋₊ then 1 else 0) := by
    apply Finset.sum_le_sum
    intro p hp
    exact one_le_log_div_add_small_indicator
      hx hr0 hp
  have hfloor : (⌊x ^ r⌋₊ : Real) ≤ x ^ r := Nat.floor_le
      (Real.rpow_nonneg (by linarith) r)
  rw [Finset.sum_add_distrib,
    ← Finset.sum_div] at hsum
  calc
    progressionPrimeCountReal q a x = ∑ p ∈ progressionPrimes q a x,
          (1 : Real) := by
      unfold progressionPrimeCountReal
      simp
    _ ≤ (∑ p ∈ progressionPrimes q a x,
          Real.log p) / (r * Real.log x) +
          ∑ p ∈ progressionPrimes q a x,
            if p ≤ ⌊x ^ r⌋₊ then 1 else 0 :=
      hsum
    _ ≤ progressionTheta q a x /
            (r * Real.log x) +
          ((⌊x ^ r⌋₊ : Real) + 1) := by
      rw [← progressionTheta_eq_sum_progressionPrimes]
      gcongr
      exact small_progression_indicator_sum_le q a x r
    _ ≤ progressionTheta q a x /
            (r * Real.log x) +
          (x ^ r + 1) := by
      gcongr

theorem power_add_one_div_primeScale_tendsto_zero {r : Real} (hr : r < 1) : Tendsto (fun x : Real =>
        (x ^ r + 1) / (x / Real.log x))
      atTop (nhds 0) := by
  have h₁ := (isLittleO_log_rpow_atTop (sub_pos.mpr hr))
      |>.tendsto_div_nhds_zero
  have h₂ := Real.isLittleO_log_id_atTop
      |>.tendsto_div_nhds_zero
  have hadd := h₁.add h₂
  have heq : (fun x : Real => Real.log x / x ^ (1 - r) +
          Real.log x / x) =ᶠ[atTop]
      (fun x : Real => (x ^ r + 1) / (x / Real.log x)) := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hxne : x ≠ 0 := hx0.ne'
    have hpow : x ^ r * x ^ (1 - r) = x := by
      rw [← Real.rpow_add hx0]
      norm_num
    field_simp [hxne, hlog,
      (Real.rpow_pos_of_pos hx0 (1 - r)).ne']
    nlinarith
  simpa using hadd.congr' heq

theorem progressionPrimeCountReal_tendsto {q a : Nat} (hq : 0 < q) (ha : a.Coprime q) : Tendsto
      (fun x => progressionPrimeCountReal q a x /
          (x / Real.log x))
      atTop
      (nhds (1 / (Nat.totient q : Real))) := by
  let phi : Real := Nat.totient q
  let delta : Real := 1 / phi
  have hphi : 0 < phi := by
    dsimp [phi]
    exact_mod_cast Nat.totient_pos.mpr hq
  have hthetaEq := progressionTheta_isEquivalent hq ha
  have hdenomNe : ∀ᶠ x : Real in atTop,
        x / phi ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_ne_zero hx.ne' hphi.ne'
  have hthetaOne : Tendsto
        (fun x => progressionTheta q a x / (x / phi))
        atTop (nhds 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hdenomNe).1
      (by simpa [phi] using hthetaEq)
  have hthetaRatio : Tendsto
        (fun x => progressionTheta q a x / x)
        atTop (nhds delta) := by
    have hdiv := hthetaOne.div_const phi
    apply hdiv.congr'
    filter_upwards [eventually_gt_atTop 0] with x hx
    field_simp [hx.ne', hphi.ne']
  refine tendsto_order.2
    ⟨?_, ?_⟩
  · intro lower hlower
    have hthetaLower : ∀ᶠ x : Real in atTop,
          lower < progressionTheta q a x / x :=
      hthetaRatio.eventually (Ioi_mem_nhds hlower)
    filter_upwards
      [hthetaLower, eventually_ge_atTop 2] with x hθ hx
    have hscalePos : 0 < x / Real.log x := div_pos (by linarith)
        (Real.log_pos (by linarith))
    have hlowerCount := theta_div_log_le_progressionPrimeCount
        (q := q) (a := a) hx
    have hx0 : x ≠ 0 := by
      exact ne_of_gt
        (lt_of_lt_of_le (by norm_num) hx)
    have hlogx : Real.log x ≠ 0 := by
      exact (Real.log_pos
          (lt_of_lt_of_le (by norm_num) hx)).ne'
    have heq : progressionTheta q a x / x *
            (x / Real.log x) =
          progressionTheta q a x /
            Real.log x := by
      field_simp [hx0, hlogx]
    rw [lt_div_iff₀ hscalePos]
    calc
      lower * (x / Real.log x) < progressionTheta q a x / x *
            (x / Real.log x) :=
        mul_lt_mul_of_pos_right hθ hscalePos
      _ = progressionTheta q a x / Real.log x := heq
      _ ≤ progressionPrimeCountReal q a x := hlowerCount
  · intro upper hupper
    have hupperDelta : delta < upper := by
      simpa [delta, phi] using hupper
    have hdeltaPos : 0 < delta := by
      dsimp [delta]
      exact one_div_pos.mpr hphi
    have hupperPos : 0 < upper := hdeltaPos.trans hupperDelta
    let eta : Real := (upper - delta) /
        (4 * (upper + 1))
    let r : Real := 1 / (1 + eta)
    have heta : 0 < eta := by
      dsimp [eta]
      exact div_pos (sub_pos.mpr hupperDelta)
        (mul_pos (by norm_num) (by linarith))
    have hr0 : 0 < r := by
      dsimp [r]
      exact one_div_pos.mpr (by linarith)
    have hr1 : r < 1 := by
      dsimp [r]
      exact (div_lt_one (by positivity)).2
        (by linarith)
    have hsmall := power_add_one_div_primeScale_tendsto_zero hr1
    have hthetaUpper : ∀ᶠ x : Real in atTop,
          progressionTheta q a x / x < delta + (upper - delta) / 4 :=
      hthetaRatio.eventually
        (Iio_mem_nhds (by linarith))
    have hsmallUpper : ∀ᶠ x : Real in atTop,
          (x ^ r + 1) /
              (x / Real.log x) <
            (upper - delta) / 4 :=
      hsmall.eventually
        (Iio_mem_nhds (by linarith))
    filter_upwards
      [hthetaUpper, hsmallUpper,
        eventually_gt_atTop 1] with x hθ hsmallX hx
    have hscalePos : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    have hupperCount := progressionPrimeCount_le_theta_add_power
        (q := q) (a := a) hx hr0
    have hnormalized : progressionPrimeCountReal q a x /
              (x / Real.log x) ≤
          progressionTheta q a x / x / r +
            (x ^ r + 1) /
              (x / Real.log x) := by
      rw [div_le_iff₀ hscalePos]
      calc
        progressionPrimeCountReal q a x ≤ progressionTheta q a x /
                (r * Real.log x) +
              (x ^ r + 1) :=
          hupperCount
        _ = (progressionTheta q a x / x / r +
              (x ^ r + 1) /
                (x / Real.log x)) *
              (x / Real.log x) := by
          field_simp [show x ≠ 0 by linarith,
            (Real.log_pos hx).ne', hr0.ne']
    refine hnormalized.trans_lt ?_
    have hrInv : 1 / r = 1 + eta := by
      dsimp [r]
      field_simp
    have hthetaNonneg : 0 ≤ progressionTheta q a x / x := by
      apply div_nonneg
      · unfold progressionTheta
        positivity
      · linarith
    have hrInv' : r⁻¹ = 1 + eta := by
      simpa [one_div] using hrInv
    rw [div_eq_mul_inv, hrInv']
    have hetaUpper : upper * eta < (upper - delta) / 4 := by
      calc
        upper * eta = (upper * (upper - delta)) /
              (4 * (upper + 1)) := by
          dsimp [eta]
          ring
        _ < (upper - delta) / 4 := by
          rw [div_lt_iff₀
            (mul_pos (by norm_num) (by linarith))]
          nlinarith
    have hthetaLtUpper : progressionTheta q a x / x < upper := by
      linarith
    have hthetaEta : progressionTheta q a x / x * eta < (upper - delta) / 4 := by
      exact (mul_lt_mul_of_pos_right hthetaLtUpper heta).trans
          hetaUpper
    nlinarith

theorem progressionPrimeCountReal_natCast (q a x : Nat) : progressionPrimeCountReal q a (x : Real) =
      ((predicateCount (PrimeInModEq q a) (x + 1) : Nat) : Real) := by
  classical
  unfold progressionPrimeCountReal progressionPrimes predicateCount
  norm_cast
  rw [Nat.count_eq_card_filter_range]
  apply congrArg Finset.card
  ext p
  simp [PrimeInModEq, Nat.ModEq, Nat.lt_succ_iff,
    isPrime_iff_natPrime, and_comm, _root_.and_left_comm]

/- Prime counting in each fixed reduced progression. -/
theorem fixedProgressionPrimeNumberTheorem (q : Nat) (hq : 0 < q) :
    FixedProgressionPrimeNumberTheorem q := by
  intro a ha
  classical
  unfold HasPrimeCountingAsymptotic
  let P : Nat → Prop := PrimeInModEq q a
  have hcutoffTop : Tendsto
        (fun x : Nat => ((x + 2 : Nat) : Real))
        atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 2)
  have hreal := (progressionPrimeCountReal_tendsto hq ha).comp
      hcutoffTop
  have hshifted : Tendsto
        (fun x : Nat => ((predicateCount P (x + 3) : Nat) : Real) /
            primeCountingScale x)
        atTop
        (nhds (1 / (Nat.totient q : Real))) := by
    apply hreal.congr'
    apply Eventually.of_forall
    intro x
    simp only [Function.comp_apply]
    rw [progressionPrimeCountReal_natCast]
    unfold primeCountingScale
    dsimp [P]
  let tail : Nat → Nat := fun x => predicateCount (fun k => P (x + k)) 3
  have htailBound : ∀ x, tail x ≤ 3 := by
    intro x
    dsimp [tail, predicateCount]
    exact Nat.count_le (p := fun k => P (x + k))
  have htailZero : Tendsto
        (fun x : Nat => ((tail x : Nat) : Real) /
            primeCountingScale x)
        atTop (nhds 0) := by
    have hmajorant : Tendsto
          (fun x : Nat => (3 : Real) / primeCountingScale x)
          atTop (nhds 0) :=
      primeCountingScale_tendsto_atTop
        |>.const_div_atTop (3 : Real)
    refine squeeze_zero'
      (g := fun x : Nat => (3 : Real) / primeCountingScale x)
      ?_ ?_ hmajorant
    · exact Eventually.of_forall fun x => div_nonneg (by positivity)
          (primeCountingScale_pos x).le
    · exact Eventually.of_forall fun x => by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast htailBound x
        · exact (primeCountingScale_pos x).le
  have hdifference := hshifted.sub htailZero
  have heq : (fun x : Nat => ((predicateCount P (x + 3) : Nat) : Real) /
              primeCountingScale x -
            ((tail x : Nat) : Real) /
              primeCountingScale x) =ᶠ[atTop]
      (fun x : Nat => ((predicateCount (PrimeInModEq q a) x : Nat) : Real) /
          primeCountingScale x) := by
    apply Eventually.of_forall
    intro x
    change
      ((predicateCount P (x + 3) : Nat) : Real) /
            primeCountingScale x -
          ((tail x : Nat) : Real) /
            primeCountingScale x =
        ((predicateCount (PrimeInModEq q a) x : Nat) : Real) /
          primeCountingScale x
    have hcount : predicateCount P (x + 3) = predicateCount P x + tail x := by
      simpa [tail] using predicateCount_add P x 3
    rw [hcount]
    dsimp [P]
    push_cast
    field_simp [primeCountingScale_ne_zero]
    ring
  simpa only [sub_zero] using hdifference.congr' heq

end Erdos279
end

section

namespace Erdos279

noncomputable def logHarmonicTerm (n : Nat) : Real := if n < 2 then
    1 / ((2 : Real) * Real.log 2)
  else
    1 / ((n : Real) * Real.log (n : Real))

theorem logHarmonicTerm_nonneg (n : Nat) : 0 ≤ logHarmonicTerm n := by
  unfold logHarmonicTerm
  split_ifs
  · positivity
  · positivity

theorem not_summable_logHarmonicTerm : ¬ Summable logHarmonicTerm := by
  intro h
  have hTerm (n : ℕ) : logHarmonicTerm n = 1 / (((max 2 n : ℕ) : ℝ) * Real.log (max 2 n : ℕ)) := by
    by_cases hn : n < 2
    · simp [logHarmonicTerm, hn, max_eq_left hn.le]
    · simp [logHarmonicTerm, hn, max_eq_right (Nat.le_of_not_gt hn)]
  have hMono {m n : ℕ} (_ : 0 < m) (hmn : m ≤ n) : logHarmonicTerm n ≤ logHarmonicTerm m := by
    rw [hTerm n, hTerm m]
    have hm : (1 : ℝ) < (max 2 m : ℕ) := by exact_mod_cast (by omega : 1 < max 2 m)
    have hcast : ((max 2 m : ℕ) : ℝ) ≤ (max 2 n : ℕ) := by
      exact_mod_cast max_le_max_left 2 hmn
    refine one_div_le_one_div_of_le (mul_pos (by linarith) (Real.log_pos hm)) ?_
    exact mul_le_mul hcast (Real.log_le_log (by linarith) hcast) (Real.log_nonneg hm.le)
      (by positivity)
  have hcond := (summable_condensed_iff_of_nonneg logHarmonicTerm_nonneg @hMono).mpr h
  apply Real.not_summable_one_div_natCast
  refine (hcond.mul_left (Real.log 2)).of_nonneg_of_le (fun _ => by positivity) ?_
  intro k
  by_cases hk : k = 0
  · subst k
    simpa using mul_nonneg (Real.log_nonneg (by norm_num)) (logHarmonicTerm_nonneg 1)
  have hpow : 2 ≤ (2 : ℕ) ^ k := calc
    2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  rw [logHarmonicTerm, if_neg (not_lt.mpr hpow)]
  push_cast
  rw [Real.log_pow]
  apply le_of_eq
  have hlog : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp <;> ring

end Erdos279
end

section

namespace Erdos279

def reducedResiduesModulus (q : Nat) : Finset Nat := (Finset.range q).filter fun a => q.Coprime a

@[simp]
theorem mem_reducedResiduesModulus {q a : Nat} : a ∈ reducedResiduesModulus q ↔
      a < q ∧ q.Coprime a := by
  simp [reducedResiduesModulus]

def complementaryAllowedResidues (h : Prime) (H : Finset Prime) : Finset Nat :=
  (reducedResiduesModulus
      (h.1 * primeSubsetModulus H)).filter
    fun a => a % h.1 ≠ 1 ∧ ∀ p ∈ H, a % p.1 ≠ 1

@[simp]
theorem mem_complementaryAllowedResidues {h : Prime} {H : Finset Prime} {a : Nat} :
    a ∈ complementaryAllowedResidues h H ↔ a < h.1 * primeSubsetModulus H ∧
      (h.1 * primeSubsetModulus H).Coprime a ∧
      a % h.1 ≠ 1 ∧
      ∀ p ∈ H, a % p.1 ≠ 1 := by
  simp [complementaryAllowedResidues,
    and_assoc]

theorem complementaryTarget_iff_allowedClass (h : Prime) (H : Finset Prime) (N n : ℕ)
    (hhN : h.1 < N) (hHN : ∀ p ∈ H, p.1 < N) (hnN : N ≤ n) :
    primeNatPredicate (IsComplementaryPrimeTarget h H) n ↔
      ∃ a ∈ complementaryAllowedResidues h H, PrimeInModEq (h.1 * primeSubsetModulus H) a n := by
  let Q := h.1 * primeSubsetModulus H
  have avoids {a : ℕ} (ha : n ≡ a [MOD Q]) : (a % h.1 ≠ 1 ∧ ∀ p ∈ H, a % p.1 ≠ 1) ↔
      (n % h.1 ≠ 1 ∧ ∀ p ∈ H, n % p.1 ≠ 1) := by
    have hHub := ha.of_mul_right (primeSubsetModulus H)
    have hOld := ha.of_mul_left h.1
    have coord (p : Prime) (hp : p ∈ H) : n % p.1 = a % p.1 :=
      (modEq_primeSubsetModulus_iff n a H).mp hOld p hp
    constructor
    · rintro ⟨hh, hs⟩
      exact ⟨by rwa [hHub], fun p hp => by rw [coord p hp]; exact hs p hp⟩
    · rintro ⟨hh, hs⟩
      exact ⟨by rwa [← hHub], fun p hp => by rw [← coord p hp]; exact hs p hp⟩
  constructor
  · rintro ⟨hn, havoid⟩
    have hnPrime := (isPrime_iff_natPrime n).mp hn
    have coprime (p : Prime) (hp : p.1 < N) : p.1.Coprime n :=
      (Nat.coprime_primes p.natPrime hnPrime).mpr (by omega)
    have hc : Q.Coprime n := Nat.coprime_mul_iff_left.mpr ⟨coprime h hhN,
        Nat.coprime_prod_left_iff.mpr fun p hp => coprime p (hHN p hp)⟩
    have haC : Q.Coprime (n % Q) := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm Q (n % Q), ← Nat.gcd_rec Q n]
      exact hc.gcd_eq_one
    have hna : n ≡ n % Q [MOD Q] := (Nat.mod_mod n Q).symm
    exact ⟨n % Q, mem_complementaryAllowedResidues.mpr
      ⟨Nat.mod_lt n (Nat.mul_pos h.pos (primeSubsetModulus_pos H)), haC, (avoids hna).mpr havoid⟩,
      hn, hna⟩
  · rintro ⟨a, ha, hn, hna⟩
    exact ⟨hn, (avoids hna).mp (mem_complementaryAllowedResidues.mp ha).2.2⟩

theorem complementaryTargets_countingAsymptotic_card (h : Prime) (H : Finset Prime) (N : Nat)
    (hhN : h.1 < N)
    (hHN : ∀ p ∈ H, p.1 < N)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * primeSubsetModulus H)) :
    HasProjectPrimeCountingAsymptotic
      (IsComplementaryPrimeTarget h H)
      (((complementaryAllowedResidues h H).card : Real) /
        (Nat.totient
          (h.1 * primeSubsetModulus H) : Real)) := by
  let R := complementaryAllowedResidues h H
  have hUnion := fixedProgressionPNT_finiteUnion
      R
      (by
        intro a ha
        exact (mem_complementaryAllowedResidues.mp ha).1)
      (by
        intro a ha
        exact (mem_complementaryAllowedResidues.mp ha).2.1.symm)
      hPNT
  unfold HasProjectPrimeCountingAsymptotic
  exact hUnion.congr_of_eventually_iff N
      (fun n hn => complementaryTarget_iff_allowedClass
          h H N n hhN hHN hn)

theorem complementaryTargets_countingAsymptotic (h : Prime) (H : Finset Prime) (N : Nat)
    (hhN : h.1 < N)
    (hHN : ∀ p ∈ H, p.1 < N)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * primeSubsetModulus H))
    (hDensity : ((complementaryAllowedResidues h H).card : Real) /
          (Nat.totient
            (h.1 * primeSubsetModulus H) : Real) =
        controllerComplementDensity h H) :
    HasProjectPrimeCountingAsymptotic
      (IsComplementaryPrimeTarget h H)
      (controllerComplementDensity h H) := by
  rw [← hDensity]
  exact complementaryTargets_countingAsymptotic_card
      h H N hhN hHN hPNT

end Erdos279
end

section

namespace Erdos279

def primeAvoidingResidues (H : Finset Prime) : Finset Nat := (reducedResiduesModulus
      (primeSubsetModulus H)).filter
    fun a => ∀ p ∈ H, a % p.1 ≠ 1

@[simp]
theorem mem_primeAvoidingResidues {H : Finset Prime} {a : Nat} : a ∈ primeAvoidingResidues H ↔
      a < primeSubsetModulus H ∧
      (primeSubsetModulus H).Coprime a ∧
      ∀ p ∈ H, a % p.1 ≠ 1 := by
  simp [primeAvoidingResidues, and_assoc]

theorem prime_coprime_primeSubsetModulus (p : Prime) (H : Finset Prime) (hpH : p ∉ H) :
    p.1.Coprime (primeSubsetModulus H) := by
  rw [primeSubsetModulus,
    Nat.coprime_prod_right_iff]
  intro q hq
  exact (Nat.coprime_primes
      p.natPrime q.natPrime).2
      (by
        intro hpq
        apply hpH
        have hpqPrime : p = q := Subtype.ext hpq
        simpa [hpqPrime] using hq)

/- The CRT count for classes avoiding zero and one. -/
theorem card_primeAvoidingResidues (H : Finset Prime) :
    (primeAvoidingResidues H).card = ∏ p ∈ H, (p.1 - 2) := by
  classical
  have hCoprime (p : Prime) (a : ℕ) : p.1.Coprime a ↔ a % p.1 ≠ 0 := by
    rw [p.natPrime.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  let residue : {a : ℕ // a ∈ primeAvoidingResidues H} →
      ((p : {p : Prime // p ∈ H}) → Fin (p.1.1 - 2)) :=
    fun a p => by
      have ha := mem_primeAvoidingResidues.mp a.2
      have hc := Nat.coprime_prod_left_iff.mp ha.2.1 p.1 p.2
      have hnz := (hCoprime p.1 a.1).mp hc
      have hno := ha.2.2 p.1 p.2
      have hlt := Nat.mod_lt a.1 p.1.pos
      exact ⟨a.1 % p.1.1 - 2, by omega⟩
  have hbij : Function.Bijective residue := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have ha := mem_primeAvoidingResidues.mp a.2
      have hb := mem_primeAvoidingResidues.mp b.2
      refine ((modEq_primeSubsetModulus_iff _ _ H).mpr ?_).eq_of_lt_of_lt ha.1 hb.1
      intro p hp
      have hnzA := (hCoprime p a.1).mp (Nat.coprime_prod_left_iff.mp ha.2.1 p hp)
      have hnzB := (hCoprime p b.1).mp (Nat.coprime_prod_left_iff.mp hb.2.1 p hp)
      have hnoA := ha.2.2 p hp
      have hnoB := hb.2.2 p hp
      have heq := congrArg Fin.val (congrFun hab ⟨p, hp⟩)
      change a.1 % p.1 - 2 = b.1 % p.1 - 2 at heq
      change a.1 % p.1 = b.1 % p.1
      omega
    · intro r
      let digits (p : Prime) := if hp : p ∈ H then (r ⟨p, hp⟩).1 + 2 else 2
      let a := Nat.chineseRemainderOfFinset digits (fun p : Prime => p.1) H
        (primeValues_ne_zero H) (primeValues_pairwise_coprime H)
      have ha : a.1 < primeSubsetModulus H := Nat.chineseRemainderOfFinset_lt_prod _ _ _ _
      have hmod (p : Prime) (hp : p ∈ H) : a.1 % p.1 = (r ⟨p, hp⟩).1 + 2 := by
        have hbound : (r ⟨p, hp⟩).1 < p.1 - 2 := (r ⟨p, hp⟩).isLt
        have hdigit : (r ⟨p, hp⟩).1 + 2 < p.1 := by omega
        simpa [digits, hp, Nat.ModEq, Nat.mod_eq_of_lt hdigit] using a.2 p hp
      have hamem : a.1 ∈ primeAvoidingResidues H := by
        refine mem_primeAvoidingResidues.mpr ⟨ha, Nat.coprime_prod_left_iff.mpr ?_, ?_⟩
        · intro p hp
          rw [hCoprime, hmod p hp]
          omega
        · intro p hp
          rw [hmod p hp]
          omega
      refine ⟨⟨a.1, hamem⟩, ?_⟩
      funext p
      apply Fin.ext
      change a.1 % p.1.1 - 2 = (r p).1
      have hdigit := hmod p.1 p.2
      change a.1 % p.1.1 = (r p).1 + 2 at hdigit
      rw [hdigit]
      omega
  rw [← Finset.prod_attach H (fun p => p.1 - 2)]
  simpa [Fintype.card_pi] using Fintype.card_congr (Equiv.ofBijective residue hbij)

theorem complementaryAllowedResidues_eq_insert (h : Prime) (H : Finset Prime) (hhH : h ∉ H) :
    complementaryAllowedResidues h H = primeAvoidingResidues (insert h H) := by
  ext a
  simp only [mem_complementaryAllowedResidues,
    mem_primeAvoidingResidues,
    primeSubsetModulus,
    Finset.prod_insert hhH,
    Finset.mem_insert]
  constructor
  · rintro ⟨haLt, haCop, hah, haH⟩
    refine ⟨haLt, haCop, ?_⟩
    intro p hp
    rcases hp with rfl | hpH
    · exact hah
    · exact haH p hpH
  · rintro ⟨haLt, haCop, haAll⟩
    exact ⟨haLt, haCop,
        haAll h (Or.inl rfl),
        fun p hp => haAll p (Or.inr hp)⟩

theorem card_complementaryAllowedResidues (h : Prime) (H : Finset Prime) (hhH : h ∉ H) :
    (complementaryAllowedResidues h H).card = (h.1 - 2) *
        ∏ p ∈ H, (p.1 - 2) := by
  rw [complementaryAllowedResidues_eq_insert
    h H hhH,
    card_primeAvoidingResidues]
  simp [hhH]

theorem one_sub_reciprocal_prime_pred (p : Prime) : 1 - 1 / ((p.1 : Real) - 1) =
      ((p.1 - 2 : Nat) : Real) /
        ((p.1 - 1 : Nat) : Real) := by
  have hpOneReal : (p.1 : Real) - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast
      (Nat.ne_of_gt p.one_lt)
  rw [Nat.cast_sub p.natPrime.two_le,
    Nat.cast_sub p.one_lt.le]
  field_simp [hpOneReal]
  ring

theorem controllerExclusionProduct_eq_primeRatio (H : Finset Prime) : controllerExclusionProduct H =
      (∏ p ∈ H,
          ((p.1 - 2 : Nat) : Real)) /
        (∏ p ∈ H,
          ((p.1 - 1 : Nat) : Real)) := by
  unfold controllerExclusionProduct
  simp_rw [one_sub_reciprocal_prime_pred]
  rw [Finset.prod_div_distrib]

theorem complementaryAllowedResidues_density (h : Prime) (H : Finset Prime) (hhH : h ∉ H) :
    ((complementaryAllowedResidues h H).card : Real) /
        (Nat.totient
          (h.1 * primeSubsetModulus H) : Real) =
      controllerComplementDensity h H := by
  have hcop : h.1.Coprime (primeSubsetModulus H) := prime_coprime_primeSubsetModulus
      h H hhH
  rw [card_complementaryAllowedResidues
      h H hhH,
    Nat.totient_mul hcop,
    Nat.totient_prime h.natPrime,
    totient_primeSubsetModulus,
    controllerComplementDensity,
    one_sub_reciprocal_prime_pred,
    controllerExclusionProduct_eq_primeRatio]
  push_cast
  ring

theorem hub_not_mem_oldControllerPrimes (h : Prime) (z : Nat) : h ∉ oldControllerPrimes h z := by
  intro hhOld
  have hhG : InControllerProgression h h := (mem_oldControllerPrimes.mp hhOld).1
  exact (Nat.lt_irrefl h.1)
      (hub_lt_of_inControllerProgression hhG)

theorem mesh_complementaryTargets_countingAsymptotic {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 *
          primeSubsetModulus
            (oldControllerPrimes h M.cutoff))) :
    HasProjectPrimeCountingAsymptotic
      (IsComplementaryPrimeTarget h
        (oldControllerPrimes h M.cutoff))
      (controllerComplementDensity h
        (oldControllerPrimes h M.cutoff)) := by
  let N := max h.1 M.cutoff + 1
  apply complementaryTargets_countingAsymptotic
      h (oldControllerPrimes h M.cutoff)
      N
  · dsimp [N]
    omega
  · intro p hp
    have hpLe : p.1 ≤ M.cutoff := (mem_oldControllerPrimes.mp hp).2
    dsimp [N]
    omega
  · exact hPNT
  · exact complementaryAllowedResidues_density
        h (oldControllerPrimes h M.cutoff)
        (hub_not_mem_oldControllerPrimes
          h M.cutoff)

end Erdos279
end

section

namespace Erdos279

open Filter

def HasImplicitNthAsymptotic (P : Nat → Prop) (hInf : Set.Infinite (setOf P))
    (density : Real) : Prop :=
  Tendsto
    (fun n : Nat => (n : Real) /
        primeCountingScale (Nat.nth P n))
    atTop (nhds density)

def HasNthLogRatio (P : Nat → Prop) (hInf : Set.Infinite (setOf P)) : Prop := Tendsto
    (fun n : Nat => Real.log
          ((Nat.nth P n : Nat) + 2 : Nat) /
        Real.log (n + 2 : Nat))
    atTop (nhds 1)

theorem predicateCount_nth_of_infinite (P : Nat → Prop) (hInf : Set.Infinite (setOf P)) (n : Nat) :
    predicateCount P (Nat.nth P n) = n := by
  classical
  unfold predicateCount
  exact Nat.count_nth_of_infinite hInf n

theorem HasPrimeCountingAsymptotic.toImplicitNth {P : Nat → Prop} {density : Real}
    (hInf : Set.Infinite (setOf P))
    (hCount : HasPrimeCountingAsymptotic P density) :
    HasImplicitNthAsymptotic
      P hInf density := by
  unfold HasPrimeCountingAsymptotic at hCount
  unfold HasImplicitNthAsymptotic
  have hnthTop : Tendsto (Nat.nth P) atTop atTop := (Nat.nth_strictMono hInf).tendsto_atTop
  have hcomp := hCount.comp hnthTop
  apply hcomp.congr'
  apply Eventually.of_forall
  intro n
  simp only [Function.comp_apply,
    predicateCount_nth_of_infinite
      P hInf]

theorem nth_tendsto_atTop (P : Nat → Prop) (hInf : Set.Infinite (setOf P)) :
    Tendsto (Nat.nth P) atTop atTop :=
  (Nat.nth_strictMono hInf).tendsto_atTop

theorem nth_div_add_two_tendsto_one (P : Nat → Prop) (hInf : Set.Infinite (setOf P)) : Tendsto
      (fun n : Nat => ((Nat.nth P n : Nat) : Real) /
          (((Nat.nth P n : Nat) : Real) + 2))
      atTop (nhds 1) := by
  exact (tendsto_natCast_div_add_atTop
      (2 : Real)).comp
      (nth_tendsto_atTop P hInf)

theorem nthAsymptotic_of_implicit_and_logRatio (P : Nat → Prop) (hInf : Set.Infinite (setOf P))
    {density : Real}
    (hdensity : 0 < density)
    (hImplicit : HasImplicitNthAsymptotic
        P hInf density)
    (hLog : HasNthLogRatio P hInf) :
    Tendsto
      (fun n : Nat => ((Nat.nth P n : Nat) : Real) /
          nthPrimeScale n)
      atTop (nhds (1 / density)) := by
  have hInv : Tendsto
        (fun n : Nat => ((n : Real) /
            primeCountingScale
              (Nat.nth P n))⁻¹)
        atTop (nhds density⁻¹) :=
    hImplicit.inv₀ hdensity.ne'
  have hPrimeShift := nth_div_add_two_tendsto_one
      P hInf
  have hIndexShift : Tendsto
        (fun n : Nat => (n : Real) /
            ((n : Real) + 2))
        atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop
      (2 : Real)
  have hProduct : Tendsto
        (fun n : Nat => ((n : Real) /
              primeCountingScale
                (Nat.nth P n))⁻¹ *
            (Real.log
                ((Nat.nth P n : Nat) + 2 : Nat) /
              Real.log (n + 2 : Nat)) *
            (((Nat.nth P n : Nat) : Real) /
              (((Nat.nth P n : Nat) : Real) + 2)) *
            ((n : Real) /
              ((n : Real) + 2)))
        atTop
        (nhds
          (density⁻¹ * 1 * 1 * 1)) :=
    ((hInv.mul hLog).mul hPrimeShift).mul
      hIndexShift
  have hEventually : (fun n : Nat => ((n : Real) /
              primeCountingScale
                (Nat.nth P n))⁻¹ *
            (Real.log
                ((Nat.nth P n : Nat) + 2 : Nat) /
              Real.log (n + 2 : Nat)) *
            (((Nat.nth P n : Nat) : Real) /
              (((Nat.nth P n : Nat) : Real) + 2)) *
            ((n : Real) /
              ((n : Real) + 2))) =ᶠ[atTop]
      (fun n : Nat => ((Nat.nth P n : Nat) : Real) /
          nthPrimeScale n) := by
    filter_upwards
      [eventually_ge_atTop 1] with n hn
    have hnPos : (0 : Real) < (n : Real) := by
      exact_mod_cast (Nat.zero_lt_of_lt hn)
    have hnLog : Real.log ((n + 2 : Nat) : Real) ≠ 0 := by
      exact (Real.log_pos
          (by
            exact_mod_cast
              (by omega : 1 < n + 2))).ne'
    have hpPos : (0 : Real) < ((Nat.nth P n : Nat) : Real) := by
      have hpNatPos : 0 < Nat.nth P n := by
        have hstrict : Nat.nth P 0 < Nat.nth P n := (Nat.nth_lt_nth hInf).2
            (by omega)
        exact (Nat.zero_le
            (Nat.nth P 0)).trans_lt
            hstrict
      exact_mod_cast hpNatPos
    have hpLog : Real.log
            (((Nat.nth P n : Nat) + 2 : Nat) : Real) ≠
          0 := by
      exact (Real.log_pos
          (by
            exact_mod_cast
              (by omega : 1 < (Nat.nth P n : Nat) + 2))).ne'
    have hnLogCast : Real.log ((n : Real) + 2) ≠ 0 := by
      simpa [Nat.cast_add] using hnLog
    have hpLogCast : Real.log
            (((Nat.nth P n : Nat) : Real) + 2) ≠
          0 := by
      simpa [Nat.cast_add] using hpLog
    unfold primeCountingScale nthPrimeScale
    push_cast
    field_simp [hnPos.ne', hpPos.ne',
      hnLogCast, hpLogCast]
  have hFinal := hProduct.congr' hEventually
  simpa [div_eq_mul_inv] using hFinal

end Erdos279
end

section

namespace Erdos279

open Filter

noncomputable def nthShiftValue (P : Nat → Prop) (n : Nat) : Real := (Nat.nth P n : Real) + 2

noncomputable def indexShiftValue (n : Nat) : Real := (n : Real) + 2

theorem nthShiftValue_pos (P : Nat → Prop) (n : Nat) : 0 < nthShiftValue P n := by
  unfold nthShiftValue
  positivity

theorem nthShiftValue_tendsto_atTop (P : Nat → Prop) (hInf : Set.Infinite (setOf P)) :
    Tendsto (nthShiftValue P) atTop atTop := by
  unfold nthShiftValue
  exact tendsto_atTop_add_const_right
      atTop 2
      (tendsto_natCast_atTop_atTop.comp
        (nth_tendsto_atTop P hInf))

theorem indexShiftValue_tendsto_atTop : Tendsto indexShiftValue atTop atTop := by
  unfold indexShiftValue
  exact tendsto_atTop_add_const_right
      atTop 2 tendsto_natCast_atTop_atTop

theorem index_log_div_shift_tendsto_one : Tendsto (fun n : Nat => Real.log (n : Real) /
          Real.log (indexShiftValue n))
      atTop (nhds 1) := by
  have hDifference : Tendsto
        (fun n : Nat => Real.log (indexShiftValue n) -
            Real.log (n : Real))
        atTop (nhds 0) := by
    simpa [indexShiftValue, Function.comp_def] using (Real.tendsto_log_comp_add_sub_log 2).comp
        tendsto_natCast_atTop_atTop
  have hIndexLogTop : Tendsto
        (fun n : Nat => Real.log (indexShiftValue n))
        atTop atTop :=
    Real.tendsto_log_atTop.comp
      indexShiftValue_tendsto_atTop
  have hDifferenceRatio : Tendsto
        (fun n : Nat => (Real.log (indexShiftValue n) -
              Real.log (n : Real)) /
            Real.log (indexShiftValue n))
        atTop (nhds 0) :=
    hDifference.div_atTop hIndexLogTop
  have hOneSub : Tendsto
        (fun n : Nat => 1 -
            (Real.log (indexShiftValue n) -
                Real.log (n : Real)) /
              Real.log (indexShiftValue n))
        atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hDifferenceRatio
  have hLogOne : ∀ᶠ n : Nat in atTop,
        1 ≤ Real.log (indexShiftValue n) :=
    hIndexLogTop.eventually_ge_atTop 1
  have hEventually : (fun n : Nat => 1 -
          (Real.log (indexShiftValue n) -
              Real.log (n : Real)) /
            Real.log (indexShiftValue n)) =ᶠ[atTop]
      (fun n : Nat => Real.log (n : Real) /
          Real.log (indexShiftValue n)) := by
    filter_upwards [hLogOne] with n hn
    have hne : Real.log (indexShiftValue n) ≠ 0 := by
      linarith
    field_simp [hne]
    ring
  simpa using hOneSub.congr' hEventually

/- Invert the prime-counting normalization using logarithms. -/
theorem implicitNth_to_logRatio (P : ℕ → Prop) (hInf : Set.Infinite (setOf P)) {density : ℝ}
    (hdensity : 0 < density) (hImplicit : HasImplicitNthAsymptotic P hInf density) :
    HasNthLogRatio P hInf := by
  let x := nthShiftValue P
  let y := indexShiftValue
  let s : ℕ → ℝ := fun n => x n / Real.log (x n)
  have hxTop : Tendsto x atTop atTop := nthShiftValue_tendsto_atTop P hInf
  have hxLogTop : Tendsto (fun n => Real.log (x n)) atTop atTop := Real.tendsto_log_atTop.comp hxTop
  have hyLogTop : Tendsto (fun n => Real.log (y n)) atTop atTop :=
    Real.tendsto_log_atTop.comp indexShiftValue_tendsto_atTop
  have hImplicit' : Tendsto (fun n : ℕ => (n : ℝ) / s n) atTop (nhds density) := by
    simpa [HasImplicitNthAsymptotic, primeCountingScale, s, x, nthShiftValue, Nat.cast_add]
      using hImplicit
  have hLogImplicit := (hImplicit'.log hdensity.ne').div_atTop hyLogTop
  have hLogY : Tendsto (fun n => Real.log (s n) / Real.log (y n)) atTop (nhds 1) := by
    have h := index_log_div_shift_tendsto_one.sub hLogImplicit
    simp only [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ), hxLogTop.eventually_ge_atTop 1] with n hn hxn
    have hs : s n ≠ 0 := div_ne_zero (nthShiftValue_pos P n).ne' (by linarith)
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    change Real.log (n : ℝ) / Real.log (y n) -
      Real.log ((n : ℝ) / s n) / Real.log (y n) = _
    rw [Real.log_div hn' hs, ← sub_div]
    ring_nf
  have hLogLog : Tendsto (fun n => Real.log (Real.log (x n)) / Real.log (x n)) atTop (nhds 0) :=
    (Asymptotics.IsLittleO.tendsto_div_nhds_zero Real.isLittleO_log_id_atTop).comp hxLogTop
  have hLogX : Tendsto (fun n => Real.log (s n) / Real.log (x n)) atTop (nhds 1) := by
    have h : Tendsto (fun n => 1 - Real.log (Real.log (x n)) / Real.log (x n)) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hLogLog
    refine h.congr' ?_
    filter_upwards [hxLogTop.eventually_ge_atTop 1] with n hxn
    have hx : Real.log (x n) ≠ 0 := by linarith
    change _ = Real.log (x n / Real.log (x n)) / Real.log (x n)
    rw [Real.log_div (nthShiftValue_pos P n).ne' hx, sub_div, div_self hx]
  have hRatio : Tendsto (fun n => Real.log (x n) / Real.log (y n)) atTop (nhds 1) := by
    have h := hLogY.div hLogX (one_ne_zero : (1 : ℝ) ≠ 0)
    simp only [div_self (one_ne_zero : (1 : ℝ) ≠ 0)] at h
    refine h.congr' ?_
    filter_upwards [hxLogTop.eventually_ge_atTop 1, hyLogTop.eventually_ge_atTop 1,
      hLogX.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hxn hyn hsxn
    have hs : Real.log (s n) ≠ 0 := by
      intro hzero
      rw [hzero, zero_div] at hsxn
      exact (lt_irrefl 0) hsxn
    have hx : Real.log (x n) ≠ 0 := by linarith
    have hy : Real.log (y n) ≠ 0 := by linarith
    change (Real.log (s n) / Real.log (y n)) / (Real.log (s n) / Real.log (x n)) = _
    field_simp
  simpa [HasNthLogRatio, x, y, nthShiftValue, indexShiftValue, Nat.cast_add] using hRatio

theorem nthAsymptotic_of_counting (P : Nat → Prop) (hInf : Set.Infinite (setOf P)) {density : Real}
    (hdensity : 0 < density)
    (hCount : HasPrimeCountingAsymptotic
        P density) :
    Tendsto
      (fun n : Nat => ((Nat.nth P n : Nat) : Real) /
          nthPrimeScale n)
      atTop (nhds (1 / density)) := by
  have hImplicit := hCount.toImplicitNth hInf
  exact nthAsymptotic_of_implicit_and_logRatio
      P hInf hdensity hImplicit
      (implicitNth_to_logRatio
        P hInf hdensity hImplicit)

theorem projectNthAsymptotic_of_counting (P : Prime → Prop) (hInf : Set.Infinite
        (setOf (primeNatPredicate P)))
    {density : Real}
    (hdensity : 0 < density)
    (hCount : HasProjectPrimeCountingAsymptotic
        P density) :
    HasNthPrimeAsymptotic
      P hInf density := by
  unfold HasNthPrimeAsymptotic
  simpa only [enumeratePrimePredicate_val] using nthAsymptotic_of_counting
      (primeNatPredicate P) hInf
      hdensity hCount

end Erdos279
end

section

namespace Erdos279

open Filter

theorem logHarmonicTerm_add_two_eq_inv_nthPrimeScale (n : Nat) : logHarmonicTerm (n + 2) =
      1 / nthPrimeScale n := by
  unfold logHarmonicTerm nthPrimeScale
  rw [if_neg (by omega)]

theorem not_summable_reciprocal_nth_of_counting (P : Nat → Prop) (hInf : Set.Infinite (setOf P))
    (hPpos : ∀ n, P n → 0 < n)
    {density : Real}
    (hdensity : 0 < density)
    (hCount : HasPrimeCountingAsymptotic P density) :
    ¬ Summable
      (fun n : Nat => 1 / ((Nat.nth P n : Nat) : Real)) := by
  let C : Real := 1 / density + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hlimit : 1 / density < C := by
    dsimp [C]
    linarith
  have hNth := nthAsymptotic_of_counting
      P hInf hdensity hCount
  have hevent : ∀ᶠ n : Nat in atTop,
        ((Nat.nth P n : Nat) : Real) /
            nthPrimeScale n <
          C :=
    hNth.eventually_lt_const hlimit
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  intro hsum
  have htail : Summable
        (fun n : Nat => 1 /
            ((Nat.nth P (n + N) : Nat) : Real)) :=
    (summable_nat_add_iff
      (f := fun n : Nat => 1 / ((Nat.nth P n : Nat) : Real)) N).2
      hsum
  have hupper : Summable
        (fun n : Nat => C *
            (1 /
              ((Nat.nth P (n + N) : Nat) : Real))) :=
    htail.mul_left C
  have hlower : Summable
        (fun n : Nat => logHarmonicTerm ((n + N) + 2)) := by
    apply hupper.of_nonneg_of_le
    · intro n
      exact logHarmonicTerm_nonneg _
    · intro n
      let m := n + N
      let p := Nat.nth P m
      have hPm : P p := Nat.nth_mem_of_infinite hInf m
      have hpNat : 0 < p := hPpos p hPm
      have hpR : 0 < (p : Real) := by
        exact_mod_cast hpNat
      have hscale : 0 < nthPrimeScale m := nthPrimeScale_pos m
      have hratio : (p : Real) / nthPrimeScale m < C := by
        exact hN m (by
          dsimp [m]
          omega)
      have hpScale : (p : Real) ≤ C * nthPrimeScale m := by
        exact ((div_lt_iff₀ hscale).mp hratio).le
      have hinv : 1 / nthPrimeScale m ≤ C * (1 / (p : Real)) := by
        have hcross : (1 : Real) * (p : Real) ≤ C * nthPrimeScale m := by
          simpa using hpScale
        have hdiv : (1 : Real) / nthPrimeScale m ≤ C / (p : Real) :=
          (div_le_div_iff₀ hscale hpR).2 hcross
        simpa [div_eq_mul_inv] using hdiv
      simpa [m, p,
        logHarmonicTerm_add_two_eq_inv_nthPrimeScale]
        using hinv
  have hshifted : Summable
        (fun n : Nat => logHarmonicTerm (n + (N + 2))) := by
    simpa [add_assoc] using hlower
  exact not_summable_logHarmonicTerm
    ((summable_nat_add_iff
      (f := logHarmonicTerm) (N + 2)).1
      hshifted)

noncomputable def predicateReciprocalTerm (P : Nat → Prop) (n : Nat) : Real := by
  classical
  exact if P n then 1 / (n : Real) else 0

theorem predicateReciprocalTerm_nonneg (P : Nat → Prop) (n : Nat) :
    0 ≤ predicateReciprocalTerm P n := by
  classical
  unfold predicateReciprocalTerm
  split_ifs
  · positivity
  · exact le_rfl

theorem not_summable_predicateReciprocal_of_counting (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (hPpos : ∀ n, P n → 0 < n)
    {density : Real}
    (hdensity : 0 < density)
    (hCount : HasPrimeCountingAsymptotic P density) :
    ¬ Summable (predicateReciprocalTerm P) := by
  classical
  have hnth := not_summable_reciprocal_nth_of_counting
      P hInf hPpos hdensity hCount
  intro hsum
  have hsub := hsum.comp_injective (Nat.nth_injective hInf)
  apply hnth
  apply hsub.congr
  intro n
  have hmem : P (Nat.nth P n) := Nat.nth_mem_of_infinite hInf n
  simp [predicateReciprocalTerm, hmem]

theorem predicateReciprocalSum_tendsto_atTop_of_counting (P : Nat → Prop)
    (hInf : Set.Infinite (setOf P))
    (hPpos : ∀ n, P n → 0 < n)
    {density : Real}
    (hdensity : 0 < density)
    (hCount : HasPrimeCountingAsymptotic P density) :
    Tendsto
      (fun z : Nat => ∑ n ∈ Finset.range z,
          predicateReciprocalTerm P n)
      atTop atTop := by
  rw [←
    not_summable_iff_tendsto_nat_atTop_of_nonneg]
  · exact not_summable_predicateReciprocal_of_counting
        P hInf hPpos hdensity hCount
  · exact predicateReciprocalTerm_nonneg P

end Erdos279
end

section

namespace Erdos279

open Filter

def controllerPrimeNatPredicate (h : Prime) (n : Nat) : Prop :=
  primeNatPredicate (InControllerProgression h) n

theorem controllerPrimeNatPredicate_pos (h : Prime) {n : Nat}
    (hn : controllerPrimeNatPredicate h n) :
    0 < n := by
  have hn2 : 2 ≤ n := (Classical.choose hn).1
  omega

theorem primeInModEq_one_iff_controller (h : Prime) (n : Nat) : PrimeInModEq h.1 1 n ↔
      controllerPrimeNatPredicate h n := by
  constructor
  · rintro ⟨hnPrime, hnMod⟩
    refine ⟨hnPrime, ?_⟩
    unfold InControllerProgression
    change n % h.1 = 1
    change n % h.1 = 1 % h.1 at hnMod
    simpa [Nat.mod_eq_of_lt h.one_lt] using hnMod
  · rintro ⟨hnPrime, hnController⟩
    refine ⟨hnPrime, ?_⟩
    unfold InControllerProgression at hnController
    change n % h.1 = 1 % h.1
    simpa [Nat.mod_eq_of_lt h.one_lt] using hnController

theorem controllerPrime_countingAsymptotic (h : Prime) (hPNT :
      FixedProgressionPrimeNumberTheorem h.1) :
    HasPrimeCountingAsymptotic
      (controllerPrimeNatPredicate h)
      (1 / (Nat.totient h.1 : Real)) := by
  have hclass := hPNT 1 (Nat.coprime_one_left h.1)
  have heq : PrimeInModEq h.1 1 = controllerPrimeNatPredicate h := by
    funext n
    exact propext (primeInModEq_one_iff_controller h n)
  rwa [heq] at hclass

theorem controllerPrimeReciprocalSum_eq_indicator (h : Prime) (z : Nat) :
    controllerPrimeReciprocalSum h z = ∑ n ∈ Finset.range (z + 1),
        predicateReciprocalTerm
          (controllerPrimeNatPredicate h) n := by
  classical
  have hfiltered : (∑ n ∈ (Finset.range (z + 1)).filter
            (controllerPrimeNatPredicate h),
          1 / (n : Real)) =
        ∑ p ∈ oldControllerPrimes h z,
          1 / (p.1 : Real) := by
    refine Finset.sum_bij
      (fun n hn => (⟨n,
          Classical.choose
            ((Finset.mem_filter.mp hn).2)⟩ : Prime))
      ?_ ?_ ?_ ?_
    · intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnController : InControllerProgression h
            (⟨n,
              Classical.choose hnData.2⟩ : Prime) :=
        Classical.choose_spec hnData.2
      apply mem_oldControllerPrimes.mpr
      constructor
      · exact hnController
      · change n ≤ z
        have hnRange : n < z + 1 := Finset.mem_range.mp hnData.1
        omega
    · intro n₁ hn₁ n₂ hn₂ heq
      exact congrArg Subtype.val heq
    · intro p hp
      have hpData := mem_oldControllerPrimes.mp hp
      have hpPred : controllerPrimeNatPredicate h p.1 := ⟨p.2, hpData.1⟩
      refine ⟨p.1, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hpPred⟩, ?_⟩
      apply Subtype.ext
      rfl
    · intro n hn
      rfl
  unfold controllerPrimeReciprocalSum
  rw [← hfiltered]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  unfold predicateReciprocalTerm
  split_ifs <;> rfl

theorem controllerPrimeReciprocalDiverges_of_fixedProgressionPNT (h : Prime) (hPNT :
      FixedProgressionPrimeNumberTheorem h.1) :
    ControllerPrimeReciprocalDiverges h := by
  have htotient : 0 < (Nat.totient h.1 : Real) := by
    exact_mod_cast
      (Nat.totient_pos.mpr h.pos)
  have hpartial := predicateReciprocalSum_tendsto_atTop_of_counting
      (controllerPrimeNatPredicate h)
      (infinite_of_counting (one_div_pos.mpr htotient) (controllerPrime_countingAsymptotic h hPNT))
      (fun n hn => controllerPrimeNatPredicate_pos h hn)
      (one_div_pos.mpr htotient)
      (controllerPrime_countingAsymptotic h hPNT)
  have hshifted : Tendsto
        (fun z : Nat => ∑ n ∈ Finset.range (z + 1),
            predicateReciprocalTerm
              (controllerPrimeNatPredicate h) n)
        atTop atTop :=
    hpartial.comp (tendsto_add_atTop_nat 1)
  unfold ControllerPrimeReciprocalDiverges
  apply hshifted.congr'
  exact Filter.Eventually.of_forall
    (fun z => (controllerPrimeReciprocalSum_eq_indicator
        h z).symm)

end Erdos279
end

section

namespace Erdos279

structure MeshFixedProgressionPNTInputs
    {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) where
  periodicPNT : FixedProgressionPrimeNumberTheorem
      (h.1 * M.modulus.1)
  complementaryPNT : FixedProgressionPrimeNumberTheorem
      (h.1 *
        primeSubsetModulus
          (oldControllerPrimes h M.cutoff))

namespace MeshFixedProgressionPNTInputs

noncomputable def toMeshPrimeEnumerations {h : Prime} {k : ℕ}
    {M : OldControllerPrimeDensityMesh h k} {hh : 3 ≤ h.1} {hk : 0 < k}
    (A : MeshFixedProgressionPNTInputs M) : MeshPrimeEnumerations M := by
  let H := oldControllerPrimes h M.cutoff
  have hH (p : Prime) (hp : p ∈ H) : InControllerProgression h p :=
    (mem_oldControllerPrimes.mp hp).1
  have hdPeriodic := M.periodicDensity_pos hh hk
  have hdComplement := controllerComplementDensity_pos h hh H hH
  have hcPeriodic := mesh_periodicReservoir_countingAsymptotic M A.periodicPNT
  have hcComplement := mesh_complementaryTargets_countingAsymptotic M A.complementaryPNT
  let inputs : MeshNthPrimeInputs M :=
    { periodic_infinite := infinite_of_counting hdPeriodic hcPeriodic
      complementary_infinite := infinite_of_counting hdComplement hcComplement
      periodic_asymptotic := projectNthAsymptotic_of_counting _ _ hdPeriodic hcPeriodic
      complementary_asymptotic := projectNthAsymptotic_of_counting _ _ hdComplement hcComplement }
  exact inputs.toMeshPrimeEnumerations hh hk

end MeshFixedProgressionPNTInputs

end Erdos279
end

section

namespace Erdos279

open Filter

noncomputable def meshControllerStageCount {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (B X : Nat) : Nat :=
  (hardStageControllerAnnulus
    h M.modulus M.classes
    (oldControllerPrimes h M.cutoff)
    k X (B * X)).card

def HasMeshControllerStageAsymptotic {h : Prime} {k : Nat} (M : OldControllerPrimeDensityMesh h k)
    (B : Nat) (coefficient : Real) : Prop :=
  Tendsto
    (fun X : Nat => (meshControllerStageCount M B X : Real) /
        primeCountingScale X)
    atTop (nhds coefficient)

end Erdos279
end

section

namespace Erdos279

def OldControllerPrimeDensityMesh.remainingClasses {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    Finset Nat :=
  reducedResidues M.modulus \ M.classes

theorem OldControllerPrimeDensityMesh.remainingClasses_subset {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    M.remainingClasses ⊆
      reducedResidues M.modulus :=
  Finset.sdiff_subset

theorem OldControllerPrimeDensityMesh.card_remainingClasses {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    M.remainingClasses.card = (M.modulus.1 - 1) - M.index := by
  unfold OldControllerPrimeDensityMesh.remainingClasses
  rw [Finset.card_sdiff_of_subset M.classes_reduced,
    card_reducedResidues, M.card_classes]

theorem controllerReservoir_iff_remainingPeriodic_beyond_modulus {h L : Prime} {R : Finset Nat}
    (hR : R ⊆ reducedResidues L)
    (H : Finset Prime)
    {n : Nat} (hnLarge : L.1 + 1 ≤ n) :
    primeNatPredicate
        (InControllerReservoir h L R H) n ↔
      primeNatPredicate
        (InPeriodicReservoir h L
          (reducedResidues L \ R) H) n := by
  have hReduced
      (hnPrime : Nat.Prime n) :
      n % L.1 ∈ reducedResidues L := by
    apply mem_reducedResidues.mpr
    have hcop : L.1.Coprime n := (Nat.coprime_primes
        L.natPrime hnPrime).2 (by omega)
    have hmodcop : L.1.Coprime (n % L.1) := by
      unfold Nat.Coprime at hcop ⊢
      rw [Nat.gcd_comm]
      rw [← Nat.gcd_rec L.1 n]
      exact hcop
    exact ⟨Nat.mod_lt n L.pos, hmodcop⟩
  constructor
  · rintro
      ⟨hnPrime, hpG, hpH, hpNotPeriodic⟩
    refine ⟨hnPrime, ⟨?_, hpH⟩⟩
    refine ⟨hpG, Finset.mem_sdiff.mpr
      ⟨hReduced
        ((isPrime_iff_natPrime n).mp hnPrime),
        ?_⟩⟩
    intro hpR
    exact hpNotPeriodic ⟨hpG, hpR⟩
  · rintro
      ⟨hnPrime, ⟨⟨hpG, hpRemaining⟩, hpH⟩⟩
    have hpNotR : n % L.1 ∉ R := (Finset.mem_sdiff.mp hpRemaining).2
    refine ⟨hnPrime, hpG, hpH, ?_⟩
    rintro ⟨_hpG, hpR⟩
    exact hpNotR hpR

noncomputable def OldControllerPrimeDensityMesh.controllerReservoirDensity {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) : Real :=
  controllerDensity h - M.periodicDensity

theorem OldControllerPrimeDensityMesh.remainingClasses_density {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    (M.remainingClasses.card : Real) /
        (Nat.totient
          (h.1 * M.modulus.1) : Real) =
      M.controllerReservoirDensity := by
  have hindex : M.index ≤ M.modulus.1 - 1 := by
    rw [← M.card_classes,
      ← card_reducedResidues M.modulus]
    exact Finset.card_le_card
      M.classes_reduced
  rw [M.card_remainingClasses,
    totient_hub_mul_aux
      h M.modulus M.hub_coprime_modulus]
  rw [Nat.cast_sub hindex]
  unfold
    OldControllerPrimeDensityMesh.controllerReservoirDensity
    OldControllerPrimeDensityMesh.periodicDensity
    controllerDensity
  have hhNe : (h.1 : Real) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr
      (by exact_mod_cast
        (Nat.ne_of_gt h.one_lt))
  have hLNe : (M.modulus.1 : Real) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr
      (by exact_mod_cast
        (Nat.ne_of_gt M.modulus.one_lt))
  have hhOne : 1 ≤ h.1 := by
    exact h.one_lt.le
  have hLOne : 1 ≤ M.modulus.1 := by
    exact M.modulus.one_lt.le
  rw [Nat.cast_mul,
    Nat.cast_sub hhOne,
    Nat.cast_sub hLOne]
  field_simp [hhNe, hLNe]
  ring

theorem mesh_controllerReservoir_countingAsymptotic {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * M.modulus.1)) :
    HasProjectPrimeCountingAsymptotic
      (InControllerReservoir
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff))
      M.controllerReservoirDensity := by
  have hRemaining := periodicReservoir_countingAsymptotic
      h M.modulus M.hub_coprime_modulus
      M.remainingClasses
      M.remainingClasses_subset
      (oldControllerPrimes h M.cutoff)
      (M.cutoff + 1)
      (by
        intro p hp
        exact Nat.lt_succ_of_le
          (mem_oldControllerPrimes.mp hp).2)
      hPNT
  unfold HasProjectPrimeCountingAsymptotic
    at hRemaining ⊢
  have hController : HasPrimeCountingAsymptotic
        (primeNatPredicate
          (InControllerReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))
        ((M.remainingClasses.card : Real) /
          (Nat.totient
            (h.1 * M.modulus.1) : Real)) :=
    HasPrimeCountingAsymptotic.congr_of_eventually_iff
      (P := primeNatPredicate
          (InControllerReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))
      (Q := primeNatPredicate
          (InPeriodicReservoir
            h M.modulus M.remainingClasses
            (oldControllerPrimes h M.cutoff)))
      (M.modulus.1 + 1)
      (by
        intro n hn
        exact (controllerReservoir_iff_remainingPeriodic_beyond_modulus
            M.classes_reduced
            (oldControllerPrimes h M.cutoff)
            hn))
      hRemaining
  rw [M.remainingClasses_density] at hController
  exact hController

theorem OldControllerPrimeDensityMesh.controllerReservoirDensity_gt_half {h : Prime} {k : Nat}
    (M : OldControllerPrimeDensityMesh h k) :
    controllerDensity h / 2 < M.controllerReservoirDensity := by
  have hUpper : M.periodicDensity < controllerDensity h / 2 := by
    simpa
      [OldControllerPrimeDensityMesh.periodicDensity]
      using M.upper_half
  unfold
    OldControllerPrimeDensityMesh.controllerReservoirDensity
  linarith

end Erdos279
end

section

namespace Erdos279

open Filter

theorem nat_mul_div_eq_floor (a b X : Nat) : a * X / b =
      ⌊((a : Real) / (b : Real)) * (X : Real)⌋₊ := by
  have hReal : ((a : Real) / (b : Real)) * (X : Real) = ((a * X : Nat) : Real) / (b : Real) := by
    push_cast
    ring
  rw [hReal, Nat.floor_div_eq_div]

theorem natCast_mul_div_ratio_tendsto (a b : Nat) (hb : 0 < b) : Tendsto (fun X : Nat =>
        ((a * X / b : Nat) : Real) /
          (X : Real))
      atTop
      (nhds ((a : Real) / (b : Real))) := by
  have hnonneg : 0 ≤ (a : Real) / (b : Real) := by
    positivity
  have hFloor := tendsto_nat_floor_mul_div_atTop
      (R := Real) hnonneg
  have hFloorNat := hFloor.comp
      tendsto_natCast_atTop_atTop
  have hEq : (fun X : Nat => (⌊((a : Real) / (b : Real)) *
            (X : Real)⌋₊ : Real) /
          (X : Real)) =ᶠ[atTop]
      (fun X : Nat => ((a * X / b : Nat) : Real) /
          (X : Real)) := by
    apply Eventually.of_forall
    intro X
    change
      (⌊((a : Real) / (b : Real)) *
          (X : Real)⌋₊ : Real) /
          (X : Real) =
        ((a * X / b : Nat) : Real) /
          (X : Real)
    congr 1
    exact_mod_cast
      (nat_mul_div_eq_floor a b X).symm
  simpa using hFloorNat.congr' hEq

theorem nat_mul_div_tendsto_atTop (a b : Nat) (ha : 0 < a) (hb : 0 < b) : Tendsto
      (fun X : Nat => a * X / b)
      atTop atTop := by
  have hpos : 0 < (a : Real) / (b : Real) := by
    positivity
  have hFloor := tendsto_nat_floor_mul_atTop
      (α := Real)
      ((a : Real) / (b : Real))
      hpos
  apply hFloor.congr'
  apply Eventually.of_forall
  intro X
  exact (nat_mul_div_eq_floor a b X).symm

theorem natCast_mul_div_add_ratio_tendsto (a b c d : Nat) (hb : 0 < b) : Tendsto (fun X : Nat =>
        ((a * X / b + c : Nat) : Real) /
          ((X + d : Nat) : Real))
      atTop
      (nhds ((a : Real) / (b : Real))) := by
  have hLinear := natCast_mul_div_ratio_tendsto a b hb
  have hConstSmall : Tendsto
        (fun X : Nat => (c : Real) / (X : Real))
        atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop
      |>.const_div_atTop (c : Real)
  have hNumerator : Tendsto
        (fun X : Nat => ((a * X / b + c : Nat) : Real) /
            (X : Real))
        atTop
        (nhds
          ((a : Real) / (b : Real) + 0)) := by
    have hAdd := hLinear.add hConstSmall
    apply hAdd.congr'
    filter_upwards
      [eventually_ne_atTop 0] with X hX
    push_cast
    field_simp [hX]
  have hDenominator : Tendsto
        (fun X : Nat => (X : Real) /
            ((X : Real) + d))
        atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop
      (d : Real)
  have hProduct := hNumerator.mul hDenominator
  have hEq : (fun X : Nat => ((a * X / b + c : Nat) : Real) /
            (X : Real) *
          ((X : Real) /
            ((X : Real) + d))) =ᶠ[atTop]
      (fun X : Nat => ((a * X / b + c : Nat) : Real) /
          ((X + d : Nat) : Real)) := by
    filter_upwards
      [eventually_ne_atTop 0] with X hX
    push_cast
    have hXd : (X : Real) + d ≠ 0 := by
      have hXR : (X : Real) ≠ 0 := by
        exact_mod_cast hX
      positivity
    field_simp [hX, hXd]
  simpa using hProduct.congr' hEq

theorem log_nat_mul_div_add_ratio_tendsto_one (a b c : Nat) (ha : 0 < a) (hb : 0 < b) : Tendsto
      (fun X : Nat => Real.log
            ((a * X / b + c + 2 : Nat) : Real) /
          Real.log ((X + 2 : Nat) : Real))
      atTop (nhds 1) := by
  have hValueRatio := natCast_mul_div_add_ratio_tendsto
      a b (c + 2) 2 hb
  have hValueTop : Tendsto
        (fun X : Nat => ((a * X / b + c + 2 : Nat) : Real))
        atTop atTop := by
    have hLinearTop := nat_mul_div_tendsto_atTop
        a b ha hb
    have hShiftTop : Tendsto
          (fun X : Nat => a * X / b + (c + 2))
          atTop atTop :=
      (tendsto_add_atTop_nat
        (c + 2)).comp hLinearTop
    have hCastTop : Tendsto
          (fun X : Nat => ((a * X / b + (c + 2) : Nat) : Real))
          atTop atTop :=
      (tendsto_natCast_atTop_atTop
        (R := Real)).comp hShiftTop
    simpa [Nat.add_assoc] using hCastTop
  have hBaseTop : Tendsto
        (fun X : Nat => ((X + 2 : Nat) : Real))
        atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 2)
  have hLogBaseTop : Tendsto
        (fun X : Nat => Real.log
            ((X + 2 : Nat) : Real))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hBaseTop
  have hLogQuotient : Tendsto
        (fun X : Nat => Real.log
            (((a * X / b + c + 2 : Nat) : Real) /
              ((X + 2 : Nat) : Real)))
        atTop
        (nhds
          (Real.log
            ((a : Real) / (b : Real)))) := by
    exact hValueRatio.log (by positivity)
  have hDifference : Tendsto
        (fun X : Nat => Real.log
              ((a * X / b + c + 2 : Nat) : Real) -
            Real.log ((X + 2 : Nat) : Real))
        atTop
        (nhds
          (Real.log
            ((a : Real) / (b : Real)))) := by
    apply hLogQuotient.congr'
    apply Eventually.of_forall
    intro X
    change
      Real.log
          (((a * X / b + c + 2 : Nat) : Real) /
            ((X + 2 : Nat) : Real)) =
        Real.log
            ((a * X / b + c + 2 : Nat) : Real) -
          Real.log ((X + 2 : Nat) : Real)
    rw [Real.log_div (by positivity)
      (by positivity)]
  have hDifferenceSmall : Tendsto
        (fun X : Nat => (Real.log
              ((a * X / b + c + 2 : Nat) : Real) -
            Real.log ((X + 2 : Nat) : Real)) /
              Real.log ((X + 2 : Nat) : Real))
        atTop (nhds 0) :=
    hDifference.div_atTop hLogBaseTop
  have hOneAdd : Tendsto
        (fun X : Nat => (1 : Real) +
            (Real.log
                ((a * X / b + c + 2 : Nat) : Real) -
              Real.log ((X + 2 : Nat) : Real)) /
                Real.log ((X + 2 : Nat) : Real))
        atTop (nhds (1 + 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real))
        atTop (nhds 1)).add hDifferenceSmall
  have hEq : (fun X : Nat => 1 +
          (Real.log
              ((a * X / b + c + 2 : Nat) : Real) -
            Real.log ((X + 2 : Nat) : Real)) /
              Real.log ((X + 2 : Nat) : Real)) =ᶠ[atTop]
      (fun X : Nat => Real.log
            ((a * X / b + c + 2 : Nat) : Real) /
          Real.log ((X + 2 : Nat) : Real)) := by
    apply Eventually.of_forall
    intro X
    have hlogNe : Real.log ((X + 2 : Nat) : Real) ≠ 0 := by
      exact (Real.log_pos
          (by
            exact_mod_cast
              (by omega : 1 < X + 2))).ne'
    field_simp [hlogNe]
    ring
  simpa using hOneAdd.congr' hEq

theorem primeCountingScale_mul_div_add_ratio_tendsto (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun X : Nat => primeCountingScale
            (a * X / b + c) /
          primeCountingScale X)
      atTop
      (nhds ((a : Real) / (b : Real))) := by
  have hValueRatio := natCast_mul_div_add_ratio_tendsto
      a b (c + 2) 2 hb
  have hLogRatio := log_nat_mul_div_add_ratio_tendsto_one
      a b c ha hb
  have hProduct := hValueRatio.mul
      (hLogRatio.inv₀ one_ne_zero)
  have hEq : (fun X : Nat => ((a * X / b + c + 2 : Nat) : Real) /
            ((X + 2 : Nat) : Real) *
          (Real.log
              ((a * X / b + c + 2 : Nat) : Real) /
            Real.log ((X + 2 : Nat) : Real))⁻¹) =ᶠ[atTop]
      (fun X : Nat => primeCountingScale
            (a * X / b + c) /
          primeCountingScale X) := by
    apply Eventually.of_forall
    intro X
    unfold primeCountingScale
    push_cast
    have hlogBase : Real.log ((X : Real) + 2) ≠ 0 := by
      exact (Real.log_pos
          (by
            have hX : (0 : Real) ≤ X := by positivity
            linarith)).ne'
    have hlogValue : Real.log
            (((a * X / b : Nat) : Real) +
              (c : Real) + 2) ≠
          0 := by
      exact (Real.log_pos
          (by
            have hnonneg : (0 : Real) ≤ (a * X / b : Nat) := by
              positivity
            linarith)).ne'
    field_simp [hlogBase, hlogValue]
  simpa using hProduct.congr' hEq

end Erdos279
end

section

namespace Erdos279

open Filter

noncomputable def predicateIoc (P : Nat → Prop) (Y Z : Nat) : Finset Nat := by
  classical
  exact (Finset.Ioc Y Z).filter P

@[simp]
theorem mem_predicateIoc {P : Nat → Prop} {Y Z n : Nat} : n ∈ predicateIoc P Y Z ↔
      Y < n ∧ n ≤ Z ∧ P n := by
  classical
  simp [predicateIoc, and_assoc]

theorem predicateIoc_card_eq_count_sub (P : Nat → Prop) {Y Z : Nat} (hYZ : Y ≤ Z) :
    (predicateIoc P Y Z).card = predicateCount P (Z + 1) -
        predicateCount P (Y + 1) := by
  classical
  unfold predicateIoc predicateCount
  rw [Nat.count_eq_card_filter_range,
    Nat.count_eq_card_filter_range]
  have hsubset : (Finset.range (Y + 1)).filter P ⊆
        (Finset.range (Z + 1)).filter P := by
    intro n hn
    simp only [Finset.mem_filter,
      Finset.mem_range] at hn ⊢
    exact ⟨by omega, hn.2⟩
  rw [← Finset.card_sdiff_of_subset hsubset]
  congr 1
  ext n
  simp only [Finset.mem_sdiff,
    Finset.mem_filter, Finset.mem_range,
    Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hYn, hnZ⟩, hPn⟩
    refine ⟨⟨by omega, hPn⟩, ?_⟩
    rintro ⟨hnY, _hPn⟩
    omega
  · rintro ⟨⟨hnZ, hPn⟩, hnot⟩
    refine ⟨⟨?_, by omega⟩, hPn⟩
    by_contra hYn
    apply hnot
    exact ⟨by omega, hPn⟩

theorem HasPrimeCountingAsymptotic.at_mul_div_add {P : Nat → Prop} {density : Real} (hCount :
      HasPrimeCountingAsymptotic P density)
    (a b c : Nat) (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun X : Nat => (predicateCount P
            (a * X / b + c) : Real) /
          primeCountingScale X)
      atTop
      (nhds
        (density *
          ((a : Real) / (b : Real)))) := by
  have hEndpointTop : Tendsto
        (fun X : Nat => a * X / b + c)
        atTop atTop :=
    (tendsto_add_atTop_nat c).comp
      (nat_mul_div_tendsto_atTop
        a b ha hb)
  have hAtEndpoint : Tendsto
        (fun X : Nat => (predicateCount P
              (a * X / b + c) : Real) /
            primeCountingScale
              (a * X / b + c))
        atTop (nhds density) :=
    hCount.comp hEndpointTop
  have hScale := primeCountingScale_mul_div_add_ratio_tendsto
      a b c ha hb
  have hProduct := hAtEndpoint.mul hScale
  apply hProduct.congr'
  apply Eventually.of_forall
  intro X
  have hscaleNe : primeCountingScale
          (a * X / b + c) ≠ 0 :=
    primeCountingScale_ne_zero _
  field_simp [hscaleNe]

theorem eventually_nat_mul_div_le_of_ratio_lt (a b c d : Nat) (hb : 0 < b) (hd : 0 < d) (hratio :
      (a : Real) / (b : Real) < (c : Real) / (d : Real)) :
    ∀ᶠ X : Nat in atTop,
      a * X / b ≤ c * X / d := by
  let midpoint := ((a : Real) / (b : Real) +
      (c : Real) / (d : Real)) / 2
  have hleftMid : (a : Real) / (b : Real) < midpoint := by
    dsimp [midpoint]
    linarith
  have hmidRight : midpoint < (c : Real) / (d : Real) := by
    dsimp [midpoint]
    linarith
  have hleft := (natCast_mul_div_ratio_tendsto
      a b hb).eventually_lt_const hleftMid
  have hright := (natCast_mul_div_ratio_tendsto
      c d hd).eventually_const_lt hmidRight
  filter_upwards
    [hleft, hright,
      eventually_gt_atTop 0] with X hXl hXr hX
  have hnormalized : ((a * X / b : Nat) : Real) /
          (X : Real) <
        ((c * X / d : Nat) : Real) /
          (X : Real) :=
    hXl.trans hXr
  have hXR : 0 < (X : Real) := by
    exact_mod_cast hX
  have hcast : ((a * X / b : Nat) : Real) < ((c * X / d : Nat) : Real) :=
    (div_lt_div_iff_of_pos_right hXR).mp
      hnormalized
  exact_mod_cast hcast.le

theorem predicateIoc_mul_div_asymptotic {P : Nat → Prop} {density : Real} (hCount :
      HasPrimeCountingAsymptotic P density)
    (a b c d : Nat)
    (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d)
    (hratio : (a : Real) / (b : Real) < (c : Real) / (d : Real)) :
    Tendsto
      (fun X : Nat => ((predicateIoc P
          (a * X / b)
          (c * X / d)).card : Real) /
            primeCountingScale X)
      atTop
      (nhds
        (density *
            ((c : Real) / (d : Real)) -
          density *
            ((a : Real) / (b : Real)))) := by
  have hLower := hCount.at_mul_div_add
      a b 1 ha hb
  have hUpper := hCount.at_mul_div_add
      c d 1 hc hd
  have hDifference := hUpper.sub hLower
  have hOrder := eventually_nat_mul_div_le_of_ratio_lt
      a b c d hb hd hratio
  have hEq : (fun X : Nat => (predicateCount P
              (c * X / d + 1) : Real) /
            primeCountingScale X -
          (predicateCount P
              (a * X / b + 1) : Real) /
            primeCountingScale X) =ᶠ[atTop]
      (fun X : Nat => ((predicateIoc P
          (a * X / b)
          (c * X / d)).card : Real) /
            primeCountingScale X) := by
    filter_upwards [hOrder] with X hXZ
    have hCountLe : predicateCount P
            (a * X / b + 1) ≤
          predicateCount P
            (c * X / d + 1) :=
      by
        classical
        unfold predicateCount
        exact (Nat.count_monotone P)
            (by omega)
    rw [predicateIoc_card_eq_count_sub
      P hXZ]
    rw [Nat.cast_sub hCountLe]
    ring
  exact hDifference.congr' hEq

theorem controllerReservoirAnnulus_card_eq_predicateIoc (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (Y Z : Nat) :
    (controllerReservoirAnnulus
      h L R H Y Z).card =
      (predicateIoc
        (primeNatPredicate
          (InControllerReservoir h L R H))
        Y Z).card := by
  classical
  apply Finset.card_bij
      (fun p _hp => p.1)
  · intro p hp
    apply mem_predicateIoc.mpr
    have hpData := mem_controllerReservoirAnnulus.mp hp
    exact ⟨hpData.1, hpData.2.1,
        p.2, hpData.2.2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro n hn
    have hnData := mem_predicateIoc.mp hn
    rcases hnData.2.2 with
      ⟨hnPrime, hnReservoir⟩
    let p : Prime := ⟨n, hnPrime⟩
    refine ⟨p, ?_, rfl⟩
    exact mem_controllerReservoirAnnulus.mpr
        ⟨hnData.1, hnData.2.1,
          hnReservoir⟩

theorem mesh_controllerStage_asymptotic {h : Prime} {k B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hB : 0 < B)
    (hBk : k * B < h.1)
    (hPNT : FixedProgressionPrimeNumberTheorem
        (h.1 * M.modulus.1)) :
    HasMeshControllerStageAsymptotic
      M B
      (M.controllerReservoirDensity *
        (1 / (k : Real) -
          (B : Real) / (h.1 : Real))) := by
  have hratio : (B : Real) / (h.1 : Real) < (1 : Real) / (k : Real) := by
    have hhR : (0 : Real) < h.1 := by
      exact_mod_cast h.pos
    have hkR : (0 : Real) < k := by
      exact_mod_cast hk
    apply (div_lt_div_iff₀
      hhR hkR).2
    norm_num
    exact_mod_cast
      (by simpa [Nat.mul_comm] using hBk)
  have hCount := mesh_controllerReservoir_countingAsymptotic
      M hPNT
  have hInterval := predicateIoc_mul_div_asymptotic
      hCount B h.1 1 k
      hB h.pos (by omega) hk
      (by simpa using hratio)
  unfold HasMeshControllerStageAsymptotic
    meshControllerStageCount
  have hEq : (fun X : Nat => ((predicateIoc
          (primeNatPredicate
            (InControllerReservoir
              h M.modulus M.classes
              (oldControllerPrimes
                h M.cutoff)))
          (B * X / h.1)
          (1 * X / k)).card : Real) /
            primeCountingScale X) =ᶠ[atTop]
      (fun X : Nat => ((hardStageControllerAnnulus
          h M.modulus M.classes
          (oldControllerPrimes h M.cutoff)
          k X (B * X)).card : Real) /
            primeCountingScale X) := by
    apply Eventually.of_forall
    intro X
    change
      ((predicateIoc
        (primeNatPredicate
          (InControllerReservoir
            h M.modulus M.classes
            (oldControllerPrimes h M.cutoff)))
        (B * X / h.1)
        (1 * X / k)).card : Real) /
          primeCountingScale X =
        ((controllerReservoirAnnulus
          h M.modulus M.classes
          (oldControllerPrimes h M.cutoff)
          (B * X / h.1)
          (X / k)).card : Real) /
            primeCountingScale X
    rw [controllerReservoirAnnulus_card_eq_predicateIoc]
    simp
  have hFinal := hInterval.congr' hEq
  simpa [mul_sub] using hFinal

end Erdos279
end

section

namespace Erdos279

def integralStageRatio (k h : Nat) : Nat := 2 * Nat.sqrt (h / k)

theorem integralStageRatio_spec {k h : Nat} (hk : 0 < k) (hlarge : 256 * k ≤ h) :
    2 ≤ integralStageRatio k h ∧ k * integralStageRatio k h < h ∧
      h ≤ k * integralStageRatio k h ^ 2 ∧
      0 < 1 / (k : Real) -
          (integralStageRatio k h : Real) / (h : Real) ∧
      ((integralStageRatio k h : Real) - 1) /
          (1 / (k : Real) -
            (integralStageRatio k h : Real) / (h : Real)) ≤
        4 * Real.sqrt ((k * h : Nat) : Real) := by
  let q := h / k
  let s := Nat.sqrt q
  let B := 2 * s
  have hq : 256 ≤ q := by
    dsimp [q]
    exact (Nat.le_div_iff_mul_le hk).2 (by
      simpa [mul_comm] using hlarge)
  have hs : 16 ≤ s := by
    rw [show s = Nat.sqrt q by rfl]
    exact Nat.le_sqrt.mpr (by
      norm_num
      exact hq)
  have hspos : 0 < s := by omega
  have hsq_le_q : s * s ≤ q := by
    exact Nat.sqrt_le q
  have hqk_le_h : q * k ≤ h := by
    dsimp [q]
    exact Nat.div_mul_le_self h k
  have hksq_le_h : k * (s * s) ≤ h := by
    calc
      k * (s * s) = (s * s) * k := by
        simp [mul_comm]
      _ ≤ q * k := Nat.mul_le_mul_right k hsq_le_q
      _ ≤ h := hqk_le_h
  have hfourks_le_h : 4 * k * s ≤ h := by
    have hfour_s : 4 * s ≤ s * s := by nlinarith
    calc
      4 * k * s = k * (4 * s) := by ring
      _ ≤ k * (s * s) := Nat.mul_le_mul_left k hfour_s
      _ ≤ h := hksq_le_h
  have hkB_lt_h : k * B < h := by
    dsimp [B]
    have htwo_s_lt_four_s : 2 * s < 4 * s := by omega
    exact ((Nat.mul_lt_mul_left hk).2 htwo_s_lt_four_s) |>.trans_le
        (by
          simpa [mul_assoc, mul_comm, mul_left_comm] using hfourks_le_h)
  have hh_lt_kqsucc : h < k * (q + 1) := by
    dsimp [q]
    exact Nat.lt_mul_div_succ h hk
  have hqsucc_le_four_sq : q + 1 ≤ 4 * (s * s) := by
    have hqsucc_le : q + 1 ≤ (s + 1) * (s + 1) := by
      simpa [s] using Nat.succ_le_succ_sqrt q
    have hsquare : (s + 1) * (s + 1) ≤ 4 * (s * s) := by
      nlinarith
    exact hqsucc_le.trans hsquare
  have hh_le_kBsq : h ≤ k * B ^ 2 := by
    have hh_lt : h < k * (4 * (s * s)) := hh_lt_kqsucc.trans_le
        (Nat.mul_le_mul_left k hqsucc_le_four_sq)
    have hrewrite : k * B ^ 2 = k * (4 * (s * s)) := by
      dsimp [B]
      ring
    rw [hrewrite]
    exact hh_lt.le
  have hhpos : 0 < h := lt_of_lt_of_le
    (by positivity : 0 < 256 * k) hlarge
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hhR : 0 < (h : Real) := by exact_mod_cast hhpos
  have hkB_R : (k : Real) * (B : Real) < (h : Real) := by
    exact_mod_cast hkB_lt_h
  have hwidth : 0 < 1 / (k : Real) - (B : Real) / (h : Real) := by
    rw [sub_pos]
    exact (div_lt_div_iff₀ hhR hkR).2 (by
      simpa [mul_comm] using hkB_R)
  have hwidth_eq : 1 / (k : Real) - (B : Real) / (h : Real) =
        ((h : Real) - (k : Real) * (B : Real)) /
          ((k : Real) * (h : Real)) := by
    field_simp
    <;> ring
  have hfourks_R : (4 : Real) * (k : Real) * (s : Real) ≤ (h : Real) := by
    exact_mod_cast hfourks_le_h
  have hratio_le_fourks : ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h : Real)) ≤
        4 * (k : Real) * (s : Real) := by
    rw [hwidth_eq]
    have hratio_eq : ((B : Real) - 1) /
            (((h : Real) - (k : Real) * (B : Real)) /
              ((k : Real) * (h : Real))) =
          (((B : Real) - 1) * ((k : Real) * (h : Real))) /
            ((h : Real) - (k : Real) * (B : Real)) := by
      field_simp
      <;> ring
    rw [hratio_eq]
    apply (div_le_iff₀ (sub_pos.mpr hkB_R)).2
    dsimp [B]
    push_cast
    have hdiff : 0 ≤ (h : Real) - 4 * (k : Real) * (s : Real) := sub_nonneg.mpr hfourks_R
    have hnonneg : 0 ≤ 2 * (k : Real) * (s : Real) *
            ((h : Real) - 4 * (k : Real) * (s : Real)) +
            (k : Real) * (h : Real) := by
      exact add_nonneg
        (mul_nonneg (by positivity) hdiff)
        (by positivity)
    have hidentity : 4 * (k : Real) * (s : Real) *
              ((h : Real) -
                (k : Real) * (2 * (s : Real))) -
            ((2 * (s : Real)) - 1) *
              ((k : Real) * (h : Real)) =
          2 * (k : Real) * (s : Real) *
              ((h : Real) -
                4 * (k : Real) * (s : Real)) +
            (k : Real) * (h : Real) := by
      ring
    exact sub_nonneg.mp (by
      rw [hidentity]
      exact hnonneg)
  have hks_sq_nat : (k * s) ^ 2 ≤ k * h := by
    calc
      (k * s) ^ 2 = k * (k * (s * s)) := by ring
      _ ≤ k * h := Nat.mul_le_mul_left k hksq_le_h
  have hks_sq_real : ((k * s : Nat) : Real) ^ 2 ≤ ((k * h : Nat) : Real) := by
    exact_mod_cast hks_sq_nat
  have hks_le_sqrt : (k : Real) * (s : Real) ≤ Real.sqrt ((k * h : Nat) : Real) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt ((k * h : Nat) : Real) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt ((k * h : Nat) : Real)) ^ 2 = ((k * h : Nat) : Real) := by
      exact Real.sq_sqrt (by positivity)
    have hks_nonneg : 0 ≤ (k : Real) * (s : Real) := by positivity
    have hcast : (((k * s : Nat) : Real)) = (k : Real) * (s : Real) := by norm_num
    rw [hcast] at hks_sq_real
    nlinarith
  have hratio : ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h : Real)) ≤
        4 * Real.sqrt ((k * h : Nat) : Real) :=
    hratio_le_fourks.trans (by
      have hmul := mul_le_mul_of_nonneg_left hks_le_sqrt
          (show (0 : Real) ≤ 4 by norm_num)
      simpa [mul_assoc] using hmul)
  change
    2 ≤ B ∧ k * B < h ∧ h ≤ k * B ^ 2 ∧ 0 < 1 / (k : Real) - (B : Real) / (h : Real) ∧
      ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h : Real)) ≤
        4 * Real.sqrt ((k * h : Nat) : Real)
  exact ⟨by dsimp [B]; omega, hkB_lt_h, hh_le_kBsq, hwidth, hratio⟩

end Erdos279
end

section

namespace Erdos279

def AllFixedProgressionPrimeNumberTheorems : Prop :=
  ∀ q : Nat, 0 < q → FixedProgressionPrimeNumberTheorem q

end Erdos279
end

section

namespace Erdos279

theorem allFixedProgressionPrimeNumberTheorems : AllFixedProgressionPrimeNumberTheorems :=
  fixedProgressionPrimeNumberTheorem

end Erdos279
end

section

namespace Erdos279

open Filter

noncomputable def controllerNonzeroBase (h : Prime) (base : ShiftedAssignment) :
    ShiftedAssignment := by
  classical
  exact fun p => if InControllerProgression h p then
      forceNonzeroResidue p (base p)
    else
      base p

theorem controllerNonzeroBase_ne_zero (h : Prime) (base : ShiftedAssignment) (p : Prime)
    (hpG : InControllerProgression h p) :
    (controllerNonzeroBase h base p : Nat) ≠ 0 := by
  rw [controllerNonzeroBase, if_pos hpG]
  exact forceNonzeroResidue_ne_zero p (base p)

theorem controllerNonzeroBase_eq_of_not_progression (h : Prime) (base : ShiftedAssignment)
    (p : Prime)
    (hpG : ¬ InControllerProgression h p) :
    controllerNonzeroBase h base p = base p := by
  simp [controllerNonzeroBase, hpG]

theorem controllerNonzeroBase_eq_of_ne_zero (h : Prime) (base : ShiftedAssignment) (p : Prime)
    (hp : (base p : Nat) ≠ 0) :
    controllerNonzeroBase h base p = base p := by
  classical
  by_cases hpG : InControllerProgression h p
  · rw [controllerNonzeroBase, if_pos hpG]
    exact forceNonzeroResidue_eq_self p (base p) hp
  · exact controllerNonzeroBase_eq_of_not_progression
      h base p hpG

structure DynamicHardScheduleAnalyticData
    (h L : Prime) (R : Finset Nat)
    (H : Finset Prime) (v k : Nat) where
  scale : Nat → Nat
  scale_monotone : Monotone scale
  scale_unbounded : Tendsto scale atTop atTop
  stage_capacity : ∀ (j : Nat)
      (a : OldPrimeClasses h
        (stageOldPrimeCutoff v (scale j))),
      (hardSurvivors h
        (stageOldPrimeCutoff v (scale j)) a
        (scale j) (scale (j + 1))).card ≤
      (dynamicHardAnnulus h L R H k scale j).card
  scale_separated : ∀ i, scale i / k ≤ scale (i + 2) / h.1
  cutoff_below_future : ∀ j i, j ≤ i → stageOldPrimeCutoff v (scale j) < scale (i + 1) / h.1
  cutoff_mature : ∀ j,
      k * stageOldPrimeCutoff v (scale j) ≤ scale j

namespace DynamicHardScheduleAnalyticData

theorem scale_covers {h L : Prime} {R : Finset Nat} {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k) :
    ∀ m, A.scale 0 + 1 ≤ m → ∃ j, A.scale j < m ∧ m ≤ A.scale (j + 1) :=
  adjacent_scale_intervals_cover_tail
    A.scale A.scale_monotone A.scale_unbounded

noncomputable def toVariableHardPairingSchedule {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment)
    (hbase : ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0) :
    VariableHardPairingSchedule
      h L R H
      (fun j => stageOldPrimeCutoff v (A.scale j))
      A.scale k := by
  let prepared := prepareDynamicBase h L R H A.scale k base
  exact variableHardPairingScheduleOfCapacity
      h L R H
      (fun j => stageOldPrimeCutoff v (A.scale j))
      A.scale k A.stage_capacity prepared
      (hardStageControllerAnnuli_pairwise_disjoint
        h L R H k A.scale A.scale_monotone
        A.scale_separated)
      (dynamicCutoffReady_of_below_future_annuli
        h L R H
        (fun j => stageOldPrimeCutoff v (A.scale j))
        A.scale k base hbase A.cutoff_below_future)
      A.cutoff_mature

theorem toVariableHardPairingSchedule_of_not_in_reservoir {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment)
    (hbase : ∀ p : Prime,
        InControllerProgression h p →
        ¬ InControllerReservoir h L R H p →
        (base p : Nat) ≠ 0)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    (A.toVariableHardPairingSchedule base hbase).assignment p = base p := by
  rw [(A.toVariableHardPairingSchedule base hbase).assignment_of_not_in_reservoir
    p hp]
  exact prepareDynamicBase_of_not_in_reservoir
    h L R H A.scale k base p hp

noncomputable def toVariableHardPairingScheduleWithNonzeroBase {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment) :
    VariableHardPairingSchedule
      h L R H
      (fun j => stageOldPrimeCutoff v (A.scale j))
      A.scale k :=
  A.toVariableHardPairingSchedule
    (controllerNonzeroBase h base)
    (fun p hpG _hpS => controllerNonzeroBase_ne_zero h base p hpG)

theorem toVariableHardPairingScheduleWithNonzeroBase_of_not_in_reservoir
    {h L : Prime} {R : Finset Nat}
    {H : Finset Prime} {v k : Nat}
    (A : DynamicHardScheduleAnalyticData h L R H v k)
    (base : ShiftedAssignment)
    (p : Prime)
    (hp : ¬ InControllerReservoir h L R H p) :
    (A.toVariableHardPairingScheduleWithNonzeroBase base).assignment p =
      controllerNonzeroBase h base p :=
  A.toVariableHardPairingSchedule_of_not_in_reservoir
    (controllerNonzeroBase h base)
    (fun q hqG _hqS => controllerNonzeroBase_ne_zero h base q hqG)
    p hp

end DynamicHardScheduleAnalyticData

end Erdos279
end

section

namespace Erdos279

open Filter

theorem eventually_uniformStage_capacity_of_upperBound {h : Prime} {k v B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    {hardCoefficient controllerCoefficient : Real}
    (hHard : HasUniformHardStageUpperBound
        h v B hardCoefficient)
    (hController : HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap : hardCoefficient < controllerCoefficient) :
    ∀ᶠ X : Nat in atTop,
      ∀ a : OldPrimeClasses h
        (stageOldPrimeCutoff v X),
        uniformHardStageCount h v B X a ≤ meshControllerStageCount M B X := by
  let midpoint := (hardCoefficient + controllerCoefficient) / 2
  have hHardEps : 0 < midpoint - hardCoefficient := by
    dsimp [midpoint]
    linarith
  have hMidController : midpoint < controllerCoefficient := by
    dsimp [midpoint]
    linarith
  have hHardEventually := hHard (midpoint - hardCoefficient) hHardEps
  have hControllerEventually : ∀ᶠ X : Nat in atTop,
        midpoint < (meshControllerStageCount M B X : Real) /
            primeCountingScale X :=
    hController.eventually_const_lt hMidController
  filter_upwards
    [hHardEventually, hControllerEventually] with
      X hHardX hControllerX
  intro a
  have hHardMid : (uniformHardStageCount h v B X a : Real) /
          primeCountingScale X ≤ midpoint := by
    have hEq : hardCoefficient +
            (midpoint - hardCoefficient) =
          midpoint := by ring
    simpa [hEq] using hHardX a
  have hNormalized : (uniformHardStageCount h v B X a : Real) /
          primeCountingScale X <
        (meshControllerStageCount M B X : Real) /
          primeCountingScale X :=
    hHardMid.trans_lt hControllerX
  have hCardReal : (uniformHardStageCount h v B X a : Real) <
        (meshControllerStageCount M B X : Real) :=
    (div_lt_div_iff_of_pos_right
      (primeCountingScale_pos X)).mp hNormalized
  exact_mod_cast hCardReal.le

noncomputable def dynamicHardScheduleAnalyticData_of_eventually_geometric {h : Prime} {k v B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hv : 2 ≤ v)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    (hcapacity : ∀ᶠ X : Nat in atTop,
        ∀ a : OldPrimeClasses h
          (stageOldPrimeCutoff v X),
          uniformHardStageCount h v B X a ≤ meshControllerStageCount M B X) :
    DynamicHardScheduleAnalyticData
      h M.modulus M.classes
      (oldControllerPrimes h M.cutoff) v k := by
  let hThreshold : ∃ N, ∀ X ≥ N,
        ∀ a : OldPrimeClasses h
          (stageOldPrimeCutoff v X),
          uniformHardStageCount h v B X a ≤ meshControllerStageCount M B X :=
    eventually_atTop.1 hcapacity
  let N : Nat := Classical.choose hThreshold
  have hN : ∀ X ≥ N,
        ∀ a : OldPrimeClasses h
          (stageOldPrimeCutoff v X),
          uniformHardStageCount h v B X a ≤ meshControllerStageCount M B X :=
    Classical.choose_spec hThreshold
  let D : Nat := h.1 + k + N + 2
  let base : Nat := D ^ 2
  let scale : Nat → Nat := fun j => base * B ^ j
  have hDpos : 0 < D := by
    dsimp [D]
    omega
  have hNbase : N ≤ base := by
    have hND : N ≤ D := by
      dsimp [D]
      omega
    have hDbase : D ≤ base := by
      dsimp [base]
      simpa [pow_two] using Nat.le_mul_of_pos_right D hDpos
    exact hND.trans hDbase
  have hkbase : k ^ 2 ≤ base := by
    have hkD : k ≤ D := by
      dsimp [D]
      omega
    dsimp [base]
    exact Nat.pow_le_pow_left hkD 2
  have hCbase : (h.1 + 1) ^ 2 ≤ base := by
    have hCD : h.1 + 1 ≤ D := by
      dsimp [D]
      omega
    dsimp [base]
    exact Nat.pow_le_pow_left hCD 2
  have hbasePos : 0 < base := by
    exact pow_pos hDpos 2
  have hBC : 2 * h.1 ≤ B * (h.1 + 1) := by
    calc
      2 * h.1 ≤ B * h.1 := Nat.mul_le_mul_right h.1 hB
      _ ≤ B * (h.1 + 1) := Nat.mul_le_mul_left B (by omega)
  have hscaleNext : ∀ j, scale (j + 1) = B * scale j := by
    intro j
    dsimp [scale]
    rw [pow_succ]
    ring
  have hscaleTwo : ∀ j, scale (j + 2) = B ^ 2 * scale j := by
    intro j
    rw [show j + 2 = (j + 1) + 1 by omega,
      hscaleNext, hscaleNext]
    ring
  have hscaleBase : ∀ j, base ≤ scale j := by
    intro j
    dsimp [scale]
    exact Nat.le_mul_of_pos_right base
      (pow_pos (by omega : 0 < B) j)
  have hscaleMono : Monotone scale := by
    intro i j hij
    dsimp [scale]
    exact Nat.mul_le_mul_left base
      (pow_right_monotone (by omega : 1 ≤ B) hij)
  exact
    { scale := scale
      scale_monotone := hscaleMono
      scale_unbounded := by
        have hPow :
            Tendsto (fun j : Nat => B ^ j)
              atTop atTop :=
          tendsto_pow_atTop_atTop_of_one_lt
            (by omega : 1 < B)
        apply tendsto_atTop_mono' atTop
          (Eventually.of_forall
            (fun j =>
              Nat.le_mul_of_pos_left
                (B ^ j) hbasePos))
        exact hPow
      stage_capacity := by
        intro j a
        have hscaleN :
            N ≤ scale j :=
          hNbase.trans (hscaleBase j)
        have hstage := hN (scale j) hscaleN a
        unfold uniformHardStageCount
          meshControllerStageCount at hstage
        simpa [dynamicHardAnnulus, hscaleNext j] using
          hstage
      scale_separated := by
        intro i
        apply (Nat.le_div_iff_mul_le h.pos).2
        calc
          (scale i / k) * h.1 ≤
              (scale i / k) * (k * B ^ 2) :=
            Nat.mul_le_mul_left (scale i / k)
              hseparated
          _ = ((scale i / k) * k) * B ^ 2 := by
            ring
          _ ≤ scale i * B ^ 2 :=
            Nat.mul_le_mul_right (B ^ 2)
              (Nat.div_mul_le_self (scale i) k)
          _ = scale (i + 2) := by
            rw [hscaleTwo]
            ring
      cutoff_below_future := by
        intro j i hji
        have hCscale :
            (h.1 + 1) ^ 2 ≤ scale j :=
          hCbase.trans (hscaleBase j)
        have hcurrent :
            stageOldPrimeCutoff v (scale j) <
              scale (j + 1) / h.1 := by
          rw [hscaleNext]
          exact stageOldPrimeCutoff_lt_mul_div
            hv h.pos hCscale hBC
        exact hcurrent.trans_le
          (Nat.div_le_div_right
            (hscaleMono (by omega : j + 1 ≤ i + 1)))
      cutoff_mature := by
        intro j
        exact mul_nthRoot_le_of_sq_le hv
          (hkbase.trans (hscaleBase j)) }

noncomputable def dynamicHardScheduleAnalyticData_of_upperBound {h : Prime} {k v B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hv : 2 ≤ v)
    (hB : 2 ≤ B)
    (hseparated : h.1 ≤ k * B ^ 2)
    {hardCoefficient controllerCoefficient : Real}
    (hHard : HasUniformHardStageUpperBound
        h v B hardCoefficient)
    (hController : HasMeshControllerStageAsymptotic
        M B controllerCoefficient)
    (hGap : hardCoefficient < controllerCoefficient) :
    DynamicHardScheduleAnalyticData
      h M.modulus M.classes
      (oldControllerPrimes h M.cutoff) v k :=
  dynamicHardScheduleAnalyticData_of_eventually_geometric
    M hk hv hB hseparated
    (eventually_uniformStage_capacity_of_upperBound
      M hHard hController hGap)

end Erdos279
end

section

namespace Erdos279

structure DynamicScheduledPaperConstruction (k : Nat) where
  hub : Prime
  hub_gt_level : k < hub.1
  modulus : Prime
  cutoff : Nat
  classes : Finset Nat
  enumerations : PeriodicComplementaryEnumerations
      hub modulus classes
        (oldControllerPrimes hub cutoff)
  primeTail : TailPrimeTargetMatching
      enumerations.periodic
      enumerations.complementary k
  sieveExponent : Nat
  hardData : DynamicHardScheduleAnalyticData
      hub modulus classes
      (oldControllerPrimes hub cutoff)
      sieveExponent k

namespace DynamicScheduledPaperConstruction

noncomputable def primeBase {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    ShiftedAssignment :=
  D.enumerations.primeTargetAssignment D.primeTail

noncomputable def hardSchedule {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    VariableHardPairingSchedule
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff)
      (fun j => stageOldPrimeCutoff D.sieveExponent
          (D.hardData.scale j))
      D.hardData.scale k :=
  D.hardData.toVariableHardPairingScheduleWithNonzeroBase
    D.primeBase

noncomputable def finalAssignment {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    ShiftedAssignment :=
  D.hardSchedule.assignment

noncomputable def primeThreshold {k : Nat} (D : DynamicScheduledPaperConstruction k) : Nat := max
    (PeriodicComplementaryEnumerations.primePrefixBound
      D.enumerations.complementary
      D.primeTail.offset)
    (max (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff)))

def hardThreshold {k : Nat} (D : DynamicScheduledPaperConstruction k) : Nat :=
  D.hardData.scale 0 + 1

noncomputable def threshold {k : Nat} (D : DynamicScheduledPaperConstruction k) : Nat :=
  max D.primeThreshold D.hardThreshold

private theorem hub_not_in_controllerReservoir {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff)
      D.hub := by
  intro hh
  exact inControllerProgression_ne_hub
    hh.inControllerProgression rfl

private theorem periodic_not_in_controllerReservoir
    {k : Nat} (D : DynamicScheduledPaperConstruction k)
    {p : Prime}
    (hp : InPeriodicReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p := by
  intro hpS
  exact not_inPeriodic_and_inControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p
      ⟨hp, hpS⟩

private theorem old_not_in_controllerReservoir {k : Nat} (D : DynamicScheduledPaperConstruction k)
    {p : Prime}
    (hp : p ∈ oldControllerPrimes D.hub D.cutoff) :
    ¬ InControllerReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p := by
  intro hpS
  exact hpS.not_mem_old hp

theorem finalAssignment_of_not_in_reservoir {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (p : Prime)
    (hp : ¬ InControllerReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff) p) :
    D.finalAssignment p = controllerNonzeroBase D.hub D.primeBase p :=
  D.hardData.toVariableHardPairingScheduleWithNonzeroBase_of_not_in_reservoir
    D.primeBase p hp

theorem finalAssignment_hub {k : Nat} (D : DynamicScheduledPaperConstruction k) :
    (D.finalAssignment D.hub : Nat) = 1 := by
  rw [D.finalAssignment_of_not_in_reservoir
    D.hub D.hub_not_in_controllerReservoir]
  rw [controllerNonzeroBase_eq_of_not_progression
    D.hub D.primeBase D.hub
    (fun hpG => inControllerProgression_ne_hub hpG rfl)]
  exact D.enumerations.primeTargetAssignment_hub D.primeTail

theorem finalAssignment_outside_zero {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (q : Prime) (hqh : q ≠ D.hub)
    (hqG : ¬ InControllerProgression D.hub q) :
    (D.finalAssignment q : Nat) = 0 := by
  have hqNotS : ¬ InControllerReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff) q := by
    intro hqS
    exact hqG hqS.inControllerProgression
  rw [D.finalAssignment_of_not_in_reservoir q hqNotS]
  rw [controllerNonzeroBase_eq_of_not_progression
    D.hub D.primeBase q hqG]
  exact D.enumerations.primeTargetAssignment_outside_zero
      (fun ℓ hℓ => (mem_oldControllerPrimes.mp hℓ).1)
      D.primeTail q hqh hqG

theorem finalAssignment_old {k : Nat} (D : DynamicScheduledPaperConstruction k) {p : Prime}
    (hp : p ∈ oldControllerPrimes D.hub D.cutoff) :
    (D.finalAssignment p : Nat) = 1 := by
  have hbase : (D.primeBase p : Nat) = 1 := D.enumerations.primeTargetAssignment_old
      D.primeTail hp
  rw [D.finalAssignment_of_not_in_reservoir
    p (D.old_not_in_controllerReservoir hp)]
  rw [controllerNonzeroBase_eq_of_ne_zero
    D.hub D.primeBase p (by omega)]
  exact hbase

theorem finalAssignment_periodic_of_ne_zero {k : Nat} (D : DynamicScheduledPaperConstruction k)
    {p : Prime}
    (hp : InPeriodicReservoir
      D.hub D.modulus D.classes
      (oldControllerPrimes D.hub D.cutoff) p)
    (hbase : (D.primeBase p : Nat) ≠ 0) :
    D.finalAssignment p = D.primeBase p := by
  rw [D.finalAssignment_of_not_in_reservoir
    p (D.periodic_not_in_controllerReservoir hp)]
  exact controllerNonzeroBase_eq_of_ne_zero
    D.hub D.primeBase p hbase

theorem final_covers_large_complementary {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (hk : 0 < k)
    (q : Prime)
    (hq : IsComplementaryPrimeTarget D.hub
      (oldControllerPrimes D.hub D.cutoff) q)
    (hqLarge : PeriodicComplementaryEnumerations.primePrefixBound
        D.enumerations.complementary
        D.primeTail.offset ≤ q.1) :
    ShiftedMatureCovers k q.1 D.finalAssignment := by
  obtain ⟨i, hiq⟩ := D.enumerations.complementary_surjective q hq
  have hvalue : PeriodicComplementaryEnumerations.primePrefixBound
          D.enumerations.complementary
          D.primeTail.offset ≤
        (D.enumerations.complementary i).1 := by
    simpa [hiq] using hqLarge
  have hoffset : D.primeTail.offset ≤ i :=
    PeriodicComplementaryEnumerations.index_ge_of_primePrefixBound_le
      D.enumerations.complementary
      D.primeTail.offset i hvalue
  let j := i - D.primeTail.offset
  have hindex : D.primeTail.offset + j = i := by
    dsimp [j]
    exact Nat.add_sub_of_le hoffset
  let pair := D.primeTail.matching.pair j
  have hpair : pair =
        { controller :=
            D.enumerations.periodic
              (D.primeTail.offset + j)
          target :=
            D.enumerations.complementary
              (D.primeTail.offset + j) } := by
    exact D.primeTail.pair_eq j
  have hpT : InPeriodicReservoir
        D.hub D.modulus D.classes
        (oldControllerPrimes D.hub D.cutoff)
        pair.controller := by
    rw [hpair]
    exact D.enumerations.periodic_mem
        (D.primeTail.offset + j)
  have hbaseNonzero : (D.primeBase pair.controller : Nat) ≠ 0 := by
    exact D.primeTail.matching.assignment_at_controller_ne_zero
        (hubOldPrimeAssignment D.hub
          (oldControllerPrimes D.hub D.cutoff))
        hk j
  have hfinalResidue : (D.finalAssignment pair.controller : Nat) = (pair.residue : Nat) := by
    rw [D.finalAssignment_periodic_of_ne_zero
      hpT hbaseNonzero]
    exact congrArg Fin.val
      (D.primeTail.matching.assignment_at_controller
        (hubOldPrimeAssignment D.hub
          (oldControllerPrimes D.hub D.cutoff)) j)
  have hcover : ShiftedMatureCovers k pair.target.1
        D.finalAssignment :=
    pair.covers_of_assignment
      (D.primeTail.matching.admissible j)
      hfinalResidue
  have htarget : pair.target = q := by
    rw [hpair]
    simpa [hindex, hiq]
  simpa [htarget] using hcover

theorem final_covers_prime_tail {k : Nat} (D : DynamicScheduledPaperConstruction k) (hk : 0 < k) :
    ∀ m, D.primeThreshold ≤ m → IsPrime m → ShiftedMatureCovers k m D.finalAssignment := by
  intro m hm hmPrime
  let q : Prime := ⟨m, hmPrime⟩
  have hprefix : PeriodicComplementaryEnumerations.primePrefixBound
          D.enumerations.complementary
          D.primeTail.offset ≤ q.1 :=
    (le_max_left _ _).trans hm
  have hhub : k * D.hub.1 ≤ q.1 := (le_max_left (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff))).trans
      ((le_max_right _ _).trans hm)
  have hold : oldPrimeMaturityBound k
          (oldControllerPrimes D.hub D.cutoff) ≤ q.1 :=
    (le_max_right (k * D.hub.1)
      (oldPrimeMaturityBound k
        (oldControllerPrimes D.hub D.cutoff))).trans
      ((le_max_right _ _).trans hm)
  by_cases hcomp : IsComplementaryPrimeTarget D.hub
        (oldControllerPrimes D.hub D.cutoff) q
  · exact D.final_covers_large_complementary
      hk q hcomp hprefix
  · by_cases hqG : InControllerProgression D.hub q
    · refine ⟨D.hub,
          hhub.trans (Nat.le_add_right q.1 1), ?_⟩
      rw [D.finalAssignment_hub]
      exact hqG
    · have hnotAll : ¬ ∀ ℓ ∈ oldControllerPrimes D.hub D.cutoff,
          q.1 % ℓ.1 ≠ 1 := by
        intro hall
        exact hcomp ⟨hqG, hall⟩
      push_neg at hnotAll
      obtain ⟨ℓ, hℓ, hqℓ⟩ := hnotAll
      refine ⟨ℓ, ?_, ?_⟩
      · exact (oldPrimeMaturity_le k
            (oldControllerPrimes D.hub D.cutoff) hℓ).trans
            hold |>.trans (Nat.le_add_right q.1 1)
      · rw [D.finalAssignment_old hℓ]
        exact hqℓ

theorem final_covers_hard_tail {k : Nat} (D : DynamicScheduledPaperConstruction k) (hk : 0 < k) :
    ∀ m, D.hardThreshold ≤ m → HasHardForm D.hub m → ShiftedMatureCovers k m D.finalAssignment := by
  exact D.hardSchedule.covers_hardForm_tail
      hk D.hardThreshold D.hardData.scale_covers

noncomputable def toPaperConstructionCore {k : Nat} (D : DynamicScheduledPaperConstruction k)
    (hk : 0 < k) :
    PaperConstructionCore k where
  hub := D.hub
  hub_gt_level := D.hub_gt_level
  shifted := D.finalAssignment
  threshold := D.threshold
  hub_residue := D.finalAssignment_hub
  outside_zero := D.finalAssignment_outside_zero
  hardForm := by
    intro m hm hhard
    exact D.final_covers_hard_tail hk m
      ((le_max_right _ _).trans hm) hhard
  primeTarget := by
    intro m hm hprime
    exact D.final_covers_prime_tail hk m
      ((le_max_left _ _).trans hm) hprime

theorem P_of_dynamicScheduledPaperConstruction {k : Nat} (hk : 3 ≤ k)
    (D : DynamicScheduledPaperConstruction k) :
    P k :=
  P_of_paperConstructionCore hk
    (D.toPaperConstructionCore (by omega))

end DynamicScheduledPaperConstruction

end Erdos279
end

section

namespace Erdos279

noncomputable def directHardCoefficient (h : Prime) (B : Nat) : Real :=
  4 * dualSieveLayerCoefficient h B * controllerDensity h

theorem hasUniformHardStageUpperBound_direct (h : Prime) (B : Nat) (hB : 0 < B) :
    HasUniformHardStageUpperBound h 64 B
      (directHardCoefficient h B) := by
  apply HasUniformMainHardStageUpperBound.toHardUpperBound
  · exact HasUniformMainLayerUpperBound.toMainHardStageUpperBound
        (hasUniformMainLayerUpperBound_dualSieve h B)
        (dualSieveLayerCoefficient_nonneg h B)
  · exact hB

noncomputable def directHubConstant (k : Nat) : Real := 82560 * Real.sqrt (k : Real)

theorem directHubConstant_nonneg (k : Nat) : 0 ≤ directHubConstant k := by
  unfold directHubConstant
  positivity

theorem eight_dualSieveLayerCoefficient_lt_width {h : Prime} {k B : Nat} (hk : 0 < k) (hB : 2 ≤ B)
    (hwidth : 0 < 1 / (k : Real) - (B : Real) / (h.1 : Real))
    (hgeometric : ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h.1 : Real)) ≤
        4 * Real.sqrt ((k * h.1 : Nat) : Real))
    (hhub : directHubConstant k * Real.sqrt (h.1 : Real) /
          ((h.1 : Real) - 1) < 1) :
    8 * dualSieveLayerCoefficient h B < 1 / (k : Real) - (B : Real) / (h.1 : Real) := by
  let width : Real := 1 / (k : Real) - (B : Real) / (h.1 : Real)
  have hhPos : (0 : Real) < (h.1 : Real) := by
    exact_mod_cast h.pos
  have hhSubPos : 0 < (h.1 : Real) - 1 := by
    exact sub_pos.mpr (by exact_mod_cast h.one_lt)
  have hBrel : ((2 * B + 1 : Nat) : Real) ≤ 5 * ((B : Real) - 1) := by
    push_cast
    have hBR : (2 : Real) ≤ (B : Real) := by exact_mod_cast hB
    linarith
  have hratio : ((2 * B + 1 : Nat) : Real) / width ≤ 20 * Real.sqrt ((k * h.1 : Nat) : Real) := by
    calc
      ((2 * B + 1 : Nat) : Real) / width ≤ (5 * ((B : Real) - 1)) / width := by
        exact div_le_div_of_nonneg_right hBrel hwidth.le
      _ = 5 * (((B : Real) - 1) / width) := by ring
      _ ≤ 5 * (4 * Real.sqrt ((k * h.1 : Nat) : Real)) := mul_le_mul_of_nonneg_left
          (by simpa [width] using hgeometric) (by norm_num)
      _ = 20 * Real.sqrt ((k * h.1 : Nat) : Real) := by ring
  have hkPosR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hsqrtMul : Real.sqrt ((k * h.1 : Nat) : Real) =
        Real.sqrt (k : Real) * Real.sqrt (h.1 : Real) := by
    push_cast
    rw [Real.sqrt_mul (by positivity)]
  have hratioOne : (8 * dualSieveLayerCoefficient h B) / width < 1 := by
    have hnonneg : 0 ≤ 4128 / (h.1 : Real) := by positivity
    have hupper : (8 * dualSieveLayerCoefficient h B) / width ≤
          directHubConstant k * Real.sqrt (h.1 : Real) /
            (h.1 : Real) := by
      unfold dualSieveLayerCoefficient directHubConstant
      calc
        (8 * (516 * ((2 * B + 1 : Nat) : Real) /
              (h.1 : Real))) / width =
            (4128 / (h.1 : Real)) *
              (((2 * B + 1 : Nat) : Real) / width) := by
          field_simp [hhPos.ne', hwidth.ne']
          ring
        _ ≤ (4128 / (h.1 : Real)) *
              (20 * Real.sqrt ((k * h.1 : Nat) : Real)) :=
          mul_le_mul_of_nonneg_left hratio hnonneg
        _ = (82560 * Real.sqrt (k : Real)) *
                Real.sqrt (h.1 : Real) /
              (h.1 : Real) := by
          rw [hsqrtMul]
          ring
    have hdenom : directHubConstant k * Real.sqrt (h.1 : Real) /
              (h.1 : Real) ≤
            directHubConstant k * Real.sqrt (h.1 : Real) /
              ((h.1 : Real) - 1) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (directHubConstant_nonneg k)
          (Real.sqrt_nonneg _)
      · exact hhSubPos
      · linarith
    exact hupper.trans_lt (hdenom.trans_lt hhub)
  exact (div_lt_one hwidth).mp (by simpa [width] using hratioOne)

theorem directHardCoefficient_lt_controller {h : Prime} {k B : Nat}
    (M : OldControllerPrimeDensityMesh h k)
    (hk : 0 < k)
    (hB : 2 ≤ B)
    (hwidth : 0 < 1 / (k : Real) - (B : Real) / (h.1 : Real))
    (hgeometric : ((B : Real) - 1) /
          (1 / (k : Real) - (B : Real) / (h.1 : Real)) ≤
        4 * Real.sqrt ((k * h.1 : Nat) : Real))
    (hhub : directHubConstant k * Real.sqrt (h.1 : Real) /
          ((h.1 : Real) - 1) < 1) :
    directHardCoefficient h B < M.controllerReservoirDensity *
        (1 / (k : Real) - (B : Real) / (h.1 : Real)) := by
  let width : Real := 1 / (k : Real) - (B : Real) / (h.1 : Real)
  have hsmall : 8 * dualSieveLayerCoefficient h B < width := by
    simpa [width] using eight_dualSieveLayerCoefficient_lt_width
        hk hB hwidth hgeometric hhub
  have hδ : 0 < controllerDensity h := controllerDensity_pos h
  have hhalf : controllerDensity h / 2 < M.controllerReservoirDensity :=
    M.controllerReservoirDensity_gt_half
  have hfirst : directHardCoefficient h B < (controllerDensity h / 2) * width := by
    unfold directHardCoefficient
    nlinarith
  exact hfirst.trans
    (mul_lt_mul_of_pos_right hhalf (by simpa [width] using hwidth))

/- Assemble the schedule from the two-residue sieve bound and the reservoir capacity. -/
theorem P_of_allFixedProgressionPNT_direct {k : Nat} (hk : 3 ≤ k)
    (fixedPNT : AllFixedProgressionPrimeNumberTheorems) :
    P k := by
  have hkpos : 0 < k := by omega
  obtain ⟨h, hmax, hhub⟩ := exists_prime_sqrt_div_sub_one_lt
      (directHubConstant k) (directHubConstant_nonneg k)
      (max (256 * k) k)
  have hlarge : 256 * k < h.1 := (le_max_left (256 * k) k).trans_lt hmax
  have hkh : k < h.1 := (le_max_right (256 * k) k).trans_lt hmax
  have hh : 3 ≤ h.1 := by omega
  have hratioSpec := integralStageRatio_spec
      (k := k) (h := h.1) hkpos hlarge.le
  let B := integralStageRatio k h.1
  have hB : 2 ≤ B := by
    simpa [B] using hratioSpec.1
  have hBk : k * B < h.1 := by
    simpa [B] using hratioSpec.2.1
  have hseparated : h.1 ≤ k * B ^ 2 := by
    simpa [B] using hratioSpec.2.2.1
  have hwidth : 0 < 1 / (k : Real) -
          (B : Real) / (h.1 : Real) := by
    simpa [B] using hratioSpec.2.2.2.1
  have hgeometric : ((B : Real) - 1) /
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) ≤
        4 * Real.sqrt ((k * h.1 : Nat) : Real) := by
    simpa [B] using hratioSpec.2.2.2.2
  have hdiv : ControllerPrimeReciprocalDiverges h :=
    controllerPrimeReciprocalDiverges_of_fixedProgressionPNT
      h (fixedPNT h.1 h.pos)
  let M : OldControllerPrimeDensityMesh h k := Classical.choice
      (exists_oldControllerPrime_reducedClass_mesh
        h hh k hkh hdiv)
  let A : MeshFixedProgressionPNTInputs M :=
    { periodicPNT :=
        fixedPNT _ (Nat.mul_pos h.pos M.modulus.pos)
      complementaryPNT :=
        fixedPNT _ (Nat.mul_pos h.pos (primeSubsetModulus_pos _)) }
  let E : MeshPrimeEnumerations M := A.toMeshPrimeEnumerations
      (hh := hh) (hk := hkpos)
  obtain ⟨T⟩ := E.exists_tailMatching hh hkpos
  have hHard : HasUniformHardStageUpperBound
        h 64 B (directHardCoefficient h B) :=
    hasUniformHardStageUpperBound_direct h B (by omega)
  have hController : HasMeshControllerStageAsymptotic
        M B
        (M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real))) :=
    mesh_controllerStage_asymptotic
      M hkpos (by omega) hBk A.periodicPNT
  have hgap : directHardCoefficient h B < M.controllerReservoirDensity *
          (1 / (k : Real) -
            (B : Real) / (h.1 : Real)) :=
    directHardCoefficient_lt_controller
      M hkpos hB hwidth hgeometric hhub
  let HD : DynamicHardScheduleAnalyticData
        h M.modulus M.classes
        (oldControllerPrimes h M.cutoff)
        64 k :=
    dynamicHardScheduleAnalyticData_of_upperBound
      M hkpos (by norm_num) hB hseparated
      hHard hController hgap
  let D : DynamicScheduledPaperConstruction k :=
    { hub := h
      hub_gt_level := hkh
      modulus := M.modulus
      cutoff := M.cutoff
      classes := M.classes
      enumerations := E.enumerations
      primeTail := T
      sieveExponent := 64
      hardData := HD }
  exact DynamicScheduledPaperConstruction.P_of_dynamicScheduledPaperConstruction
      hk D

theorem globalAffirmative_direct : GlobalAffirmative := by
  intro k hk
  exact P_of_allFixedProgressionPNT_direct
      hk allFixedProgressionPrimeNumberTheorems

theorem globalAffirmative : GlobalAffirmative := globalAffirmative_direct

end Erdos279
end

/- Translate the project residue assignment to the exact Formal Conjectures statement. -/
private theorem erdos279_of_global (h : Erdos279.GlobalAffirmative) :
    type_of% @Erdos279.erdos_279 := by
  classical
  intro k hk
  obtain ⟨r, N, _hN, cover⟩ := h k hk
  let a (n : ℕ) : ℕ := if hn : Nat.Prime n then
    (r ⟨n, (Erdos279.isPrime_iff_natPrime n).mpr hn⟩).val else 0
  refine ⟨a, N, ?_, ?_⟩
  · intro p hp
    simpa [a, hp] using (r ⟨p, (Erdos279.isPrime_iff_natPrime p).mpr hp⟩).isLt
  · intro n hn
    obtain ⟨p, t, ht, eq⟩ := cover n hn
    exact ⟨p.val, t, ht, p.natPrime, by simpa [a, p.natPrime] using eq⟩

theorem OMA.solution : type_of% @Erdos279.erdos_279 := erdos279_of_global Erdos279.globalAffirmative

/-
Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
