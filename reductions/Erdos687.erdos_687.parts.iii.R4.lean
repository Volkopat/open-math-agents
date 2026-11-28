import FormalConjectures.ErdosProblems.«687»
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Bertrand

-- Reduction Erdos687.erdos_687.parts.iii.R4 of Erdős Problem 687 — iii
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Proved here: residue covers of `[1, y]` by primes `≤ x` are blocks of `y` consecutive
integers without an integer coprime to `P = primorial x` (CRT). Bertrand handles offsets
`b ≤ y`; reflection `n ↦ P - n` and `P ± 1` handle the second half of a period; sliding
reduces to blocks whose left endpoint `b` is coprime to `P`. For every center `c ≤ P`
with reduced denominator `d = P / gcd P c`, the progression `c + d t` is coprime to `P`
iff `t` is coprime to `gcd P c`, so Bertrand along it handles blocks near centers with
`4 d x ≤ L`, and the single steps `c ± d` (always coprime to `P`) handle every block
containing one of them.
H1 (classical, Ingham 1937): a prime in `(n, n + n^{2/3}]` for large `n`; it handles
offsets `b^2 ≤ L^3`.
H2 (the remaining core): offsets `b^2 > L^3` in the first half of the period, with `b`
coprime to `P`, far from all small-denominator centers and avoiding all steps `c ± d`.
-/

open Filter
open scoped Asymptotics
open Erdos687

namespace OMA.R_Erdos687_erdos_687_parts_iii_R4

private lemma add_residue_complement {p : ℕ} (hp : 0 < p) (a : ℕ) :
    a + (p - a % p) ≡ 0 [MOD p] := by
  have hmod : a ≡ a % p [MOD p] := by simp [Nat.ModEq]
  have hsum : a % p + (p - a % p) = p := by
    have := Nat.mod_lt a hp
    omega
  refine (hmod.add_right _).trans ?_
  simpa only [hsum] using (Nat.modulus_modEq_zero (n := p))

/-- A residue cover is a block without any integer coprime to the primorial.
It suffices to consider starting points in one period. -/
private lemma covered_iff_shifted_nonCoprime (x y : ℕ) :
    Green46.IsCoveredByResidues x y ↔
      ∃ b < primorial x, ∀ m ∈ Finset.Icc 1 y, ¬ (b + m).Coprime (primorial x) := by
  constructor
  · rintro ⟨a, ha⟩
    let ps := (Finset.range (x + 1)).filter Nat.Prime
    have hmem (p : ℕ) : p ∈ ps ↔ p ≤ x ∧ p.Prime := by
      simp [ps]
    have hn (p : ℕ) (hp : p ∈ ps) : p ≠ 0 := ((hmem p).mp hp).2.ne_zero
    have hpair : Set.Pairwise (ps : Set ℕ) (Function.onFun Nat.Coprime id) := by
      intro p hp q hq hpq
      exact (Nat.coprime_primes ((hmem p).mp hp).2 ((hmem q).mp hq).2).mpr hpq
    let b := Nat.chineseRemainderOfFinset (fun p ↦ p - a p % p) id ps hn hpair
    refine ⟨b, Nat.chineseRemainderOfFinset_lt_prod _ _ hn hpair, ?_⟩
    intro m hm
    obtain ⟨p, hpx, hp, hma⟩ := ha m hm
    have hba := b.property p ((hmem p).mpr ⟨hpx, hp⟩)
    have hsum : (b : ℕ) + m ≡ 0 [MOD p] := by
      refine (hba.add hma).trans ?_
      rw [add_comm]
      exact add_residue_complement hp.pos (a p)
    exact Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, Nat.modEq_zero_iff_dvd.mp hsum, hp.dvd_primorial_iff.mpr hpx⟩
  · rintro ⟨b, _, hb⟩
    refine ⟨fun p ↦ p - b % p, ?_⟩
    intro m hm
    obtain ⟨p, hp, hpbm, hpx⟩ := Nat.Prime.not_coprime_iff_dvd.mp (hb m hm)
    refine ⟨p, hp.dvd_primorial_iff.mp hpx, hp, Nat.ModEq.add_left_cancel' b ?_⟩
    exact (Nat.modEq_zero_iff_dvd.mpr hpbm).trans (add_residue_complement hp.pos b).symm

private lemma covered_iff_le_Y (x y : ℕ) : Green46.IsCoveredByResidues x y ↔ y ≤ Y x := by
  let S : Set ℕ := {n | Green46.IsCoveredByResidues x n}
  have hbounded : BddAbove S :=
    ⟨primorial x, fun n hn ↦ (lt_primorial_of_isCoveredByResidues (x := x) (y := n) hn).le⟩
  have hn : (0 : ℕ) ∈ S := ⟨id, by simp⟩
  change y ∈ S ↔ y ≤ sSup S
  refine ⟨le_csSup hbounded, fun hy ↦ ?_⟩
  obtain ⟨a, ha⟩ : sSup S ∈ S := Nat.sSup_mem ⟨0, hn⟩ hbounded
  exact ⟨a, fun m hm ↦ ha m (Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2.trans hy⟩)⟩

/-- The first length that guarantees a coprime integer in every block is `Y x + 1`. -/
private lemma Y_lt_iff_uniform_coprime (x y : ℕ) :
    Y x < y ↔
      ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  classical
  rw [← not_le, ← covered_iff_le_Y, covered_iff_shifted_nonCoprime]
  push Not
  rfl

private lemma target_iff_uniform_coprime :
    (∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε))) ↔
    ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊,
        (b + m).Coprime (primorial x) := by
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp (h (ε / 2) (half_pos hε))
    have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (ε / 2)) atTop atTop :=
      (tendsto_rpow_atTop (half_pos hε)).comp tendsto_natCast_atTop_atTop
    filter_upwards [hC, (tendsto_atTop.mp hgrowth) (C + 1), eventually_ge_atTop 1] with x hx hlarge hx1
    apply (Y_lt_iff_uniform_coprime _ _).mp
    apply Nat.lt_ceil.mpr
    have hxpos : 0 < (x : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hx1 : 0 < x)
    have hnonneg : 0 ≤ (x : ℝ) ^ (1 + ε / 2) := Real.rpow_nonneg hxpos.le _
    have hbound : (Y x : ℝ) ≤ C * (x : ℝ) ^ (1 + ε / 2) := by
      simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Y x)), Real.norm_of_nonneg hnonneg] using hx
    calc
      (Y x : ℝ) ≤ C * (x : ℝ) ^ (1 + ε / 2) := hbound
      _ < (x : ℝ) ^ (ε / 2) * (x : ℝ) ^ (1 + ε / 2) :=
        mul_lt_mul_of_pos_right (by linarith) (Real.rpow_pos_of_pos hxpos _)
      _ = (x : ℝ) ^ (1 + ε) := by
        rw [← Real.rpow_add hxpos]
        congr 1
        ring
  · intro h ε hε
    apply Asymptotics.isBigO_iff.mpr
    refine ⟨1, ?_⟩
    filter_upwards [h ε hε] with x hx
    have hy := Nat.lt_ceil.mp ((Y_lt_iff_uniform_coprime _ _).mpr hx)
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (Y x)),
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg x) _), one_mul] using hy.le

/-- Bertrand's postulate supplies a coprime integer when the offset is at most the length. -/
private lemma coprime_of_offset_le_length {x y b : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y)
    (hby : b ≤ y) : ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (max b x)
    (Nat.ne_of_gt (hx.trans_le (le_max_right _ _)))
  have hbp : b < p := (le_max_left _ _).trans_lt hlt
  have hxp : x < p := (le_max_right _ _).trans_lt hlt
  have hupper : p ≤ b + y := by
    rcases le_total b x with hbx | hxb
    · rw [max_eq_right hbx] at hle
      omega
    · rw [max_eq_left hxb] at hle
      omega
  refine ⟨p - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (p - b) = p by omega]
  exact hp.coprime_iff_not_dvd.mpr (fun hd ↦ (not_le.mpr hxp) (hp.dvd_primorial_iff.mp hd))

/-- A block crossing the end of the period contains `P - 1` or `P + 1`. -/
private lemma coprime_of_crossing_period {P b y : ℕ} (hy : 2 ≤ y)
    (hb : b < P) (hend : P ≤ b + y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  by_cases h : b + 1 < P
  · refine ⟨P - 1 - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (P - 1 - b) = P - 1 by omega]
    exact (Nat.coprime_self_sub_left (by omega : 1 ≤ P)).mpr (Nat.coprime_one_left P)
  · refine ⟨2, Finset.mem_Icc.mpr ⟨by decide, hy⟩, ?_⟩
    rw [show b + 2 = 1 + P by omega, Nat.coprime_add_self_left]
    exact Nat.coprime_one_left P

/-- Reflection within a period preserves coprimality and reverses a block. -/
private lemma coprime_of_reflected_offset {P b y : ℕ} (hend : b + y < P)
    (h : ∃ m ∈ Finset.Icc 1 y, (P - (b + y) - 1 + m).Coprime P) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  obtain ⟨m, hm, hc⟩ := h
  obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hm
  refine ⟨y + 1 - m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (y + 1 - m) = P - (P - (b + y) - 1 + m) by omega]
  exact (Nat.coprime_self_sub_left (by omega : P - (b + y) - 1 + m ≤ P)).mpr hc

/-- For long blocks it suffices to test blocks in the first half of the period,
starting more than one block length from zero. -/
private lemma uniform_coprime_of_first_half {x y : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y)
    (h : ∀ b, y < b → 2 * b + y < primorial x →
      ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x)) :
    ∀ b < primorial x, ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  intro b hb
  by_cases hsmall : b ≤ y
  · exact coprime_of_offset_le_length hx hxy hsmall
  by_cases hfirst : 2 * b + y < primorial x
  · exact h b (lt_of_not_ge hsmall) hfirst
  by_cases hcross : primorial x ≤ b + y
  · exact coprime_of_crossing_period (by omega) hb hcross
  apply coprime_of_reflected_offset (lt_of_not_ge hcross)
  let b' := primorial x - (b + y) - 1
  change ∃ m ∈ Finset.Icc 1 y, (b' + m).Coprime (primorial x)
  by_cases hsmall' : b' ≤ y
  · exact coprime_of_offset_le_length hx hxy hsmall'
  exact h b' (lt_of_not_ge hsmall') (by dsimp [b']; omega)

private lemma eventually_twice_le_length {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, 0 < x ∧ 2 * x ≤ ⌈(x : ℝ) ^ (1 + ε)⌉₊ := by
  have hgrowth : Tendsto (fun x : ℕ ↦ (x : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, (tendsto_atTop.mp hgrowth) 2] with x hx hg
  have hx' : 0 < x := hx
  have hpos : 0 < (x : ℝ) := by exact_mod_cast hx'
  have hreal : ((2 * x : ℕ) : ℝ) ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := by
    calc
      ((2 * x : ℕ) : ℝ) = (x : ℝ) * 2 := by push_cast; ring
      _ ≤ (x : ℝ) * (x : ℝ) ^ ε := mul_le_mul_of_nonneg_left hg hpos.le
      _ = (x : ℝ) ^ (1 + ε) := by rw [Real.rpow_add hpos, Real.rpow_one]
      _ ≤ (⌈(x : ℝ) ^ (1 + ε)⌉₊ : ℝ) := Nat.le_ceil _
  exact ⟨hx', by exact_mod_cast hreal⟩

private lemma target_of_first_half
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      ∀ b, L < b → 2 * b + L < primorial x →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime (primorial x)) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_iff_uniform_coprime.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_twice_le_length hε] with x hinner hx
  exact uniform_coprime_of_first_half hx.1 hx.2 hinner

/-- A progression through `c` with step `P / gcd P c` reduces coprimality
to the primes of `P` that divide `c`. -/
private lemma coprime_add_reduced_denominator {P c t : ℕ} (hP : Squarefree P) :
    (c + (P / P.gcd c) * t).Coprime P ↔ t.Coprime (P.gcd c) := by
  let g := P.gcd c
  let d := P / g
  have hgP : g ∣ P := Nat.gcd_dvd_left P c
  have hgc : g ∣ c := Nat.gcd_dvd_right P c
  have hdg : d * g = P := Nat.div_mul_cancel hgP
  have hdg' : d.Coprime g := Nat.coprime_of_squarefree_mul (hdg ▸ hP)
  have hcd : c.Coprime d := by
    by_cases hc : c = 0
    · simp [d, g, hc, Nat.div_self (Nat.pos_of_ne_zero hP.ne_zero)]
    · exact (Nat.coprime_div_gcd_of_squarefree hP hc).symm
  change (c + d * t).Coprime P ↔ t.Coprime g
  have hg : (c + d * t).Coprime g ↔ t.Coprime g := by
    calc
      (c + d * t).Coprime g ↔ g.Coprime (c + d * t) := Nat.coprime_comm
      _ ↔ g.Coprime (d * t) := Nat.coprime_add_iff_right hgc
      _ ↔ (d * t).Coprime g := Nat.coprime_comm
      _ ↔ t.Coprime g := Nat.coprime_mul_iff_left.trans (and_iff_right hdg')
  rw [← hdg, Nat.coprime_mul_iff_right, Nat.coprime_add_mul_left_left, hg]
  exact and_iff_right hcd

private lemma coprime_right_of_center {x b c y : ℕ} (hx : 0 < x) (hcb : c ≤ b)
    (hby : b - c ≤ y) (hbudget : 2 * (primorial x / (primorial x).gcd c) * x ≤ y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  let P := primorial x
  let d := P / P.gcd c
  have hd : 0 < d :=
    Nat.div_pos (Nat.gcd_le_left c (primorial_pos x)) (Nat.gcd_pos_of_pos_left c (primorial_pos x))
  let n := max x ((b - c) / d)
  have hxn : x ≤ n := le_max_left _ _
  obtain ⟨p, hp, hnp, hupper⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  have hlower : b - c < d * p := by
    rw [mul_comm]
    exact (Nat.div_lt_iff_lt_mul hd).mp ((le_max_right _ _).trans_lt hnp)
  have hdu : d * p ≤ b - c + y := by
    have hp' := Nat.mul_le_mul_left d hupper
    rcases le_total x ((b - c) / d) with hn | hn
    · dsimp [n] at hp'
      rw [max_eq_right hn, ← mul_assoc, mul_comm d 2, mul_assoc, mul_comm d ((b - c) / d)] at hp'
      have hdiv := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self (b - c) d)
      omega
    · dsimp [n] at hp'
      rw [max_eq_left hn, ← mul_assoc, mul_comm d 2] at hp'
      change 2 * d * x ≤ y at hbudget
      omega
  refine ⟨c + d * p - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [show b + (c + d * p - b) = c + d * p by omega]
  apply (coprime_add_reduced_denominator (squarefree_primorial x)).mpr
  refine (hp.coprime_iff_not_dvd.mpr fun hdiv ↦ (hxn.trans_lt hnp).not_ge
    (hp.dvd_primorial_iff.mp hdiv)).of_dvd_right (Nat.gcd_dvd_left P c)

private lemma coprime_near_center_on_right {x b c y : ℕ} (hx : 0 < x)
    (hnear : b ≤ c + y) (hside : 2 * c ≤ 2 * b + y + 1)
    (hbudget : 4 * (primorial x / (primorial x).gcd c) * x ≤ y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  let u := max b c
  have hbu : b ≤ u := le_max_left _ _
  have hcu : c ≤ u := le_max_right _ _
  have hul : u ≤ b + y := max_le (by omega) (by omega)
  have hdist : u - c ≤ b + y - u := by
    rcases le_total b c with h | h
    · simp [u, max_eq_right h]
    · rw [show u = b from max_eq_left h]
      omega
  have hroom : 2 * (primorial x / (primorial x).gcd c) * x ≤ b + y - u := by
    have hlen : 2 * (b + y - u) + 1 ≥ y := by
      rcases le_total b c with h | h
      · rw [show u = c from max_eq_right h]
        omega
      · rw [show u = b from max_eq_left h]
        omega
    have hh : 4 * (primorial x / (primorial x).gcd c) * x =
        2 * (2 * (primorial x / (primorial x).gcd c) * x) := by ring
    omega
  obtain ⟨m, hm, hc⟩ := coprime_right_of_center hx hcu hdist hroom
  obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
  refine ⟨u - b + m, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
  rwa [show b + (u - b + m) = u + m by omega]

/-- A block near a rational multiple `c` of `primorial x` is guaranteed
a witness when the reduced denominator of `c / primorial x` is small. -/
private lemma coprime_near_reduced_denominator {x b c y : ℕ} (hx : 0 < x)
    (hend : b + y < primorial x) (hc : c ≤ primorial x)
    (hnear : b ≤ c + y) (hnear' : c ≤ b + 2 * y + 1)
    (hbudget : 4 * (primorial x / (primorial x).gcd c) * x ≤ y) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  by_cases hside : 2 * c ≤ 2 * b + y + 1
  · exact coprime_near_center_on_right hx hnear hside hbudget
  apply coprime_of_reflected_offset hend
  apply coprime_near_center_on_right (c := primorial x - c) hx (by omega) (by omega)
  rwa [Nat.gcd_self_sub_right hc]

private lemma target_of_offsets_away_from_centers
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      let P := primorial x
      ∀ b, L < b → 2 * b + L < P →
        (∀ c ≤ P, b ≤ c + L → c ≤ b + 2 * L + 1 → L < 4 * (P / P.gcd c) * x) →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime P) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_of_first_half
  intro ε hε
  filter_upwards [h ε hε, eventually_ge_atTop 1] with x hinner hx
  intro L b hLb hhalf
  by_cases hcenter : ∃ c ≤ primorial x, b ≤ c + L ∧ c ≤ b + 2 * L + 1 ∧
      4 * (primorial x / (primorial x).gcd c) * x ≤ L
  · obtain ⟨c, hc, hnear, hnear', hbudget⟩ := hcenter
    exact coprime_near_reduced_denominator hx (by omega) hc hnear hnear' hbudget
  exact hinner b hLb hhalf (fun c hc hnear hnear' ↦
    lt_of_not_ge fun hbudget ↦ hcenter ⟨c, hc, hnear, hnear', hbudget⟩)

/-- A left endpoint that is not coprime can be passed by sliding a block
one place to the right, provided the preceding block has a witness. -/
private lemma Y_lt_iff_coprime_offsets {x y : ℕ} (hx : 0 < x) (hxy : 2 * x ≤ y) :
    Y x < y ↔ ∀ b, y < b → 2 * b + y < primorial x → b.Coprime (primorial x) →
      ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime (primorial x) := by
  constructor
  · intro hy b _ hb _
    exact (Y_lt_iff_uniform_coprime x y).mp hy b (by omega)
  · intro h
    apply (Y_lt_iff_uniform_coprime x y).mpr
    apply uniform_coprime_of_first_half hx hxy
    intro b
    induction b using Nat.strong_induction_on with
    | h b ih =>
      intro hby hhalf
      by_cases hb : b.Coprime (primorial x)
      · exact h b hby hhalf hb
      have hprev : ∃ m ∈ Finset.Icc 1 y, (b - 1 + m).Coprime (primorial x) := by
        by_cases hsmall : b - 1 ≤ y
        · exact coprime_of_offset_le_length hx hxy hsmall
        · exact ih (b - 1) (by omega) (by omega) (by omega)
      obtain ⟨m, hm, hcop⟩ := hprev
      obtain ⟨hm1, hmy⟩ := Finset.mem_Icc.mp hm
      have hm2 : 2 ≤ m := by
        by_contra! hlt
        exact hb (by simpa only [show b - 1 + m = b by omega] using hcop)
      refine ⟨m - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rwa [show b + (m - 1) = b - 1 + m by omega]

private lemma coprime_center_plus_step {P c : ℕ} (hP : Squarefree P) :
    (c + P / P.gcd c).Coprime P := by
  simpa only [mul_one] using
    (coprime_add_reduced_denominator (c := c) (t := 1) hP).mpr (Nat.coprime_one_left _)

private lemma coprime_center_minus_step {P c : ℕ} (hP : Squarefree P) (hc : c ≤ P)
    (hstep : P / P.gcd c ≤ c) : (c - P / P.gcd c).Coprime P := by
  have h := coprime_center_plus_step (c := P - c) hP
  rw [Nat.gcd_self_sub_right hc] at h
  rw [show c - P / P.gcd c = P - (P - c + P / P.gcd c) by omega]
  exact (Nat.coprime_self_sub_left (by omega)).mpr h

/-- A single step from a center suffices when it lands in the block.
This uses denominators as large as the distance from the center to an endpoint. -/
private lemma coprime_of_center_step_in_block {P b c y : ℕ}
    (hP : Squarefree P) (hc : c ≤ P)
    (hstep : let d := P / P.gcd c
      (b < c + d ∧ c + d ≤ b + y) ∨ (b < c - d ∧ c - d ≤ b + y)) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  let d := P / P.gcd c
  rcases hstep with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · refine ⟨c + d - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (c + d - b) = c + d by omega]
    exact coprime_center_plus_step hP
  · refine ⟨c - d - b, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [show b + (c - d - b) = c - d by omega]
    exact coprime_center_minus_step hP hc (by omega)

private lemma target_of_coprime_offsets_away_from_centers
    (h : ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
      let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
      let P := primorial x
      ∀ b, L < b → 2 * b + L < P → b.Coprime P →
        (∀ c ≤ P, b ≤ c + L → c ≤ b + 2 * L + 1 → L < 4 * (P / P.gcd c) * x) →
        (∀ c ≤ P, let d := P / P.gcd c
          (b < c + d → b + L < c + d) ∧ (b < c - d → b + L < c - d)) →
        ∃ m ∈ Finset.Icc 1 L, (b + m).Coprime P) :
    ∀ ε > (0 : ℝ), (fun x : ℕ ↦ (Y x : ℝ)) =O[atTop]
      (fun x : ℕ ↦ (x : ℝ) ^ (1 + ε)) := by
  apply target_iff_uniform_coprime.mpr
  intro ε hε
  filter_upwards [h ε hε, eventually_twice_le_length hε] with x hinner hx
  apply (Y_lt_iff_uniform_coprime _ _).mp
  apply (Y_lt_iff_coprime_offsets hx.1 hx.2).mpr
  intro b hLb hhalf hb
  let L := ⌈(x : ℝ) ^ (1 + ε)⌉₊
  let P := primorial x
  by_cases hnear : ∃ c ≤ P, b ≤ c + L ∧ c ≤ b + 2 * L + 1 ∧
      4 * (P / P.gcd c) * x ≤ L
  · obtain ⟨c, hc, hdist, hdist', hbudget⟩ := hnear
    exact coprime_near_reduced_denominator hx.1 (by omega) hc hdist hdist' hbudget
  by_cases hstep : ∃ c ≤ P, let d := P / P.gcd c
      (b < c + d ∧ c + d ≤ b + L) ∨ (b < c - d ∧ c - d ≤ b + L)
  · obtain ⟨c, hc, hfit⟩ := hstep
    exact coprime_of_center_step_in_block (squarefree_primorial x) hc hfit
  refine hinner b hLb hhalf hb (fun c hc hdist hdist' ↦
    lt_of_not_ge fun hbudget ↦ hnear ⟨c, hc, hdist, hdist', hbudget⟩) ?_
  intro c hc
  refine ⟨fun hlo ↦ lt_of_not_ge fun hhi ↦ hstep ⟨c, hc, Or.inl ⟨hlo, hhi⟩⟩, ?_⟩
  exact fun hlo ↦ lt_of_not_ge fun hhi ↦ hstep ⟨c, hc, Or.inr ⟨hlo, hhi⟩⟩

/-- Classical short prime gaps (Ingham 1937): eventually there is a prime in `(n, n + n^{2/3}]`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n) ^ 3 ≤ n ^ 2

/-- Core: with `L = ⌈x^(1+ε)⌉` and `P = primorial x`, every block `[b+1, b+L]` in the
first half of the period with `L^3 < b^2`, `b` coprime to `P`, no center `c` of small
reduced denominator nearby and no step `c ± P / gcd P c` inside the block, contains an
integer coprime to `P`. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
    ∀ b : ℕ, ⌈(x : ℝ) ^ (1 + ε)⌉₊ ^ 3 < b ^ 2 →
      2 * b + ⌈(x : ℝ) ^ (1 + ε)⌉₊ < primorial x → b.Coprime (primorial x) →
      (∀ c ≤ primorial x, b ≤ c + ⌈(x : ℝ) ^ (1 + ε)⌉₊ →
        c ≤ b + 2 * ⌈(x : ℝ) ^ (1 + ε)⌉₊ + 1 →
        ⌈(x : ℝ) ^ (1 + ε)⌉₊ < 4 * (primorial x / (primorial x).gcd c) * x) →
      (∀ c ≤ primorial x,
        (b < c + primorial x / (primorial x).gcd c →
          b + ⌈(x : ℝ) ^ (1 + ε)⌉₊ < c + primorial x / (primorial x).gcd c) ∧
        (b < c - primorial x / (primorial x).gcd c →
          b + ⌈(x : ℝ) ^ (1 + ε)⌉₊ < c - primorial x / (primorial x).gcd c)) →
      ∃ m ∈ Finset.Icc 1 ⌈(x : ℝ) ^ (1 + ε)⌉₊, (b + m).Coprime (primorial x)

theorem main : H1 → H2 → type_of% @Erdos687.erdos_687.parts.iii := by
  intro h1 h2
  apply target_of_coprime_offsets_away_from_centers
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp h1
  filter_upwards [h2 ε hε, eventually_twice_le_length hε, eventually_ge_atTop N]
    with x hcore hx hxN
  intro L P b hLb hhalf hcop hcent hstep
  by_cases hbig : L ^ 3 < b ^ 2
  · exact hcore b hbig hhalf hcop hcent hstep
  · push Not at hbig
    obtain ⟨p, hp, hbp, hgap⟩ := hN b (by omega)
    have hpL : p - b ≤ L := by
      have h3 : (p - b) ^ 3 ≤ L ^ 3 := hgap.trans hbig
      exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h3
    refine ⟨p - b, Finset.mem_Icc.mpr ⟨by omega, hpL⟩, ?_⟩
    rw [show b + (p - b) = p by omega]
    have hxp : x < p := by omega
    exact hp.coprime_iff_not_dvd.mpr (fun hd ↦ (not_le.mpr hxp) (hp.dvd_primorial_iff.mp hd))

end OMA.R_Erdos687_erdos_687_parts_iii_R4
