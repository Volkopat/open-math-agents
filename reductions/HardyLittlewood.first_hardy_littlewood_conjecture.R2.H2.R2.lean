import OMAReductions.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2
import Mathlib.Data.ZMod.QuotientRing

/-!
# Reduction R2.H2.R2: Multilinear W-trick expansion into PNT in AP + balanced correlations

This reduction decomposes `R2.H2` (the Hardy–Littlewood von Mangoldt `(k + 2)`-tuple
correlation conjecture) via the Green–Tao / Maynard `W`-trick and the exact multilinear
expansion of `∏ i, Λ_W (n + m i) = ∏ i, ((Λ_W (n + m i) - 1) + 1)`:

- `I = ∅` contributes the exact main term `1` (proved unconditionally by residue counting).
- `|I| = 1` contributes `0` by `H1` (PNT in arithmetic progressions for `Λ_W`, which is a
  known theorem provable from `OMAPNT.tendsto_psiAP`).
- `|I| ≥ 2` contributes `0` by `H2` (asymptotic cancellation of higher-order balanced
  `W`-tricked von Mangoldt correlations).

Multiplying by the exact CRT local factor `C_s → C_m` and adding the unconditionally
negligible non-coprime contribution `O_{m, s}((log N)^(k+3)/N) → 0` yields `R2.H2`.
-/

namespace OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2

open HardyLittlewood Filter Finset ArithmeticFunction
open scoped Topology

/-- Prime Number Theorem in arithmetic progressions in `W`-tricked form:
for every positive modulus `W` and every unit `a : ZMod W`,
`(W.totient / N) * ∑_{1 ≤ n ≤ N, n ≡ a (mod W)} Λ n → 1`. -/
def H1 : Prop :=
  ∀ (W : ℕ), 0 < W → ∀ (a : ZMod W), IsUnit a →
    Tendsto (fun N : ℕ =>
      ((W.totient : ℝ) / (N : ℝ)) *
        ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = a),
          ArithmeticFunction.vonMangoldt n)
      atTop (𝓝 1)

/-- Asymptotic cancellation of higher-order (`|I| ≥ 2`) balanced `W`-tricked von Mangoldt
correlations over coprime translates modulo `W = 2 * ∏ q ∈ s, q`. -/
def H2 : Prop :=
  ∀ {k : ℕ} (m : Fin (k + 2) → ℕ), m 0 = 0 → (∀ i ≠ 0, Even (m i)) →
    Function.Injective m →
    (∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, ¬ Function.Surjective (fun i => (m i : ZMod q))) →
    ∀ (I : Finset (Fin (k + 2))), 2 ≤ I.card →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q} in atTop,
    let W := 2 * ∏ q ∈ s, (q : ℕ)
    ∀ᶠ N : ℕ in atTop,
      |(W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
        ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
          ∏ i ∈ I, ((W.totient : ℝ) / (W : ℝ) * ArithmeticFunction.vonMangoldt (n + m i) - 1)| < ε

/- ### Part 1: Wheel totient, CRT surviving count, and exact local factor -/

lemma coprime_two_prod_odd (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    Nat.Coprime 2 (∏ q ∈ s, (q : ℕ)) := by
  apply Nat.Coprime.prod_right
  intro q _
  have hne : (2 : ℕ) ≠ (q : ℕ) := by have := q.2.2; omega
  exact (Nat.coprime_primes Nat.prime_two q.2.1).mpr hne

lemma totient_prod_odd (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    (∏ q ∈ s, (q : ℕ)).totient = ∏ q ∈ s, ((q : ℕ) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop : Nat.Coprime (a : ℕ) (∏ q ∈ s, (q : ℕ)) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hne : (a : ℕ) ≠ (q : ℕ) := fun h => ha (Subtype.ext h ▸ hq)
      exact (Nat.coprime_primes a.2.1 q.2.1).mpr hne
    rw [Nat.totient_mul hcop, Nat.totient_prime a.2.1, ih]

lemma totient_wheel (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    (2 * ∏ q ∈ s, (q : ℕ)).totient = ∏ q ∈ s, ((q : ℕ) - 1) := by
  rw [Nat.totient_mul (coprime_two_prod_odd s), Nat.totient_two, one_mul]
  exact totient_prod_odd s

lemma wheel_pos (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    0 < 2 * ∏ q ∈ s, (q : ℕ) := by
  apply Nat.mul_pos (by omega)
  exact Finset.prod_pos fun q _ => q.2.1.pos

lemma local_surviving_prime {k : ℕ} (m : Fin k.succ → ℕ) (q : ℕ) (hq : q.Prime) :
    Nat.card {x : ZMod q // ∀ i, IsUnit (x + m i)} = q - Nat.numResidues q m := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  let R := Set.range (fun i => (m i : ZMod q))
  let e : {x : ZMod q // ∀ i, IsUnit (x + m i)} ≃ ↥Rᶜ :=
    (Equiv.neg (ZMod q)).subtypeEquiv (by
      intro x
      change (∀ i, IsUnit (x + (m i : ZMod q))) ↔ ¬∃ i, (m i : ZMod q) = -x
      constructor
      · rintro h ⟨i, hi⟩
        have hu := h i
        rw [hi, add_neg_cancel] at hu
        exact not_isUnit_zero hu
      · intro h i
        rw [isUnit_iff_ne_zero]
        intro h0
        exact h ⟨i, eq_neg_of_add_eq_zero_left (by simpa [add_comm] using h0)⟩)
  calc
    Nat.card {x : ZMod q // ∀ i, IsUnit (x + m i)} = Rᶜ.ncard := Nat.card_congr e
    _ = q - Nat.numResidues q m := by rw [Set.ncard_compl, Nat.card_zmod]; rfl

lemma local_surviving_two {k : ℕ} (m : Fin k.succ → ℕ)
    (hzero : m 0 = 0) (heven : ∀ i ≠ 0, Even (m i)) :
    Nat.card {x : ZMod 2 // ∀ i, IsUnit (x + m i)} = 1 := by
  have hm2 : ∀ i, (m i : ZMod 2) = 0 := by
    intro i
    have hev : Even (m i) := by
      by_cases hi : i = 0
      · rw [hi, hzero]; exact Even.zero
      · exact heven i hi
    obtain ⟨r, hr⟩ := hev
    rw [hr, show r + r = 2 * r by omega, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  rw [local_surviving_prime m 2 Nat.prime_two]
  have hnum : Nat.numResidues 2 m = 1 := by
    unfold Nat.numResidues
    have hrg : Set.range (fun i => (m i : ZMod 2)) = {0} := by
      ext z
      simp only [Set.mem_range, Set.mem_singleton_iff, hm2]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
    rw [hrg, Set.ncard_singleton]
  omega

lemma surviving_card_mul {k : ℕ} (m : Fin k.succ → ℕ) {a b : ℕ} (hcop : Nat.Coprime a b) :
    Nat.card {r : ZMod (a * b) // ∀ i, IsUnit (r + (m i : ZMod (a * b)))} =
      Nat.card {x : ZMod a // ∀ i, IsUnit (x + (m i : ZMod a))} *
      Nat.card {y : ZMod b // ∀ i, IsUnit (y + (m i : ZMod b))} := by
  let e := ZMod.chineseRemainder hcop
  let e' : {r : ZMod (a * b) // ∀ i, IsUnit (r + (m i : ZMod (a * b)))} ≃
      {x : ZMod a // ∀ i, IsUnit (x + (m i : ZMod a))} ×
      {y : ZMod b // ∀ i, IsUnit (y + (m i : ZMod b))} :=
    (e.toEquiv.subtypeEquiv
      (q := fun p : ZMod a × ZMod b =>
        (∀ i, IsUnit (p.1 + (m i : ZMod a))) ∧ (∀ i, IsUnit (p.2 + (m i : ZMod b))))
      (by
        intro r
        constructor
        · intro hr
          constructor <;> intro i
          · have h := (hr i).map ((RingHom.fst (ZMod a) (ZMod b)).comp e.toRingHom)
            simpa [e] using h
          · have h := (hr i).map ((RingHom.snd (ZMod a) (ZMod b)).comp e.toRingHom)
            simpa [e] using h
        · rintro ⟨h1, h2⟩ i
          have hp : IsUnit (e (r + (m i : ZMod (a * b)))) := by
            rw [map_add, map_natCast, Prod.isUnit_iff]
            exact ⟨h1 i, h2 i⟩
          have := hp.map e.symm.toRingHom
          simpa using this)).trans
      (Equiv.subtypeProdEquivProd
        (p := fun x : ZMod a => ∀ i, IsUnit (x + (m i : ZMod a)))
        (q := fun y : ZMod b => ∀ i, IsUnit (y + (m i : ZMod b))))
  rw [Nat.card_congr e', Nat.card_prod]

lemma surviving_card_prod_odd {k : ℕ} (m : Fin k.succ → ℕ)
    (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    Nat.card {r : ZMod (∏ q ∈ s, (q : ℕ)) // ∀ i, IsUnit (r + m i)} =
      ∏ q ∈ s, ((q : ℕ) - Nat.numResidues q m) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    have huniq : Unique {r : ZMod 1 // ∀ i, IsUnit (r + (m i : ZMod 1))} :=
      ⟨⟨⟨0, fun _ => isUnit_of_subsingleton _⟩⟩, fun x => Subtype.ext (Subsingleton.elim _ _)⟩
    exact @Nat.card_unique _ ⟨huniq.default⟩ huniq.instSubsingleton
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop : Nat.Coprime (a : ℕ) (∏ q ∈ s, (q : ℕ)) := by
      apply Nat.Coprime.prod_right
      intro q hq
      have hne : (a : ℕ) ≠ (q : ℕ) := fun h => ha (Subtype.ext h ▸ hq)
      exact (Nat.coprime_primes a.2.1 q.2.1).mpr hne
    rw [surviving_card_mul m hcop, local_surviving_prime m a a.2.1, ih]

lemma surviving_card_wheel {k : ℕ} (m : Fin k.succ → ℕ)
    (hzero : m 0 = 0) (heven : ∀ i ≠ 0, Even (m i))
    (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    Nat.card {r : ZMod (2 * ∏ q ∈ s, (q : ℕ)) // ∀ i, IsUnit (r + m i)} =
      ∏ q ∈ s, ((q : ℕ) - Nat.numResidues q m) := by
  rw [surviving_card_mul m (coprime_two_prod_odd s), local_surviving_two m hzero heven, one_mul]
  exact surviving_card_prod_odd m s

lemma wheel_local_factor_eq {k : ℕ} (m : Fin (k + 2) → ℕ)
    (hzero : m 0 = 0) (heven : ∀ i ≠ 0, Even (m i))
    (s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q}) :
    let W := 2 * ∏ q ∈ s, (q : ℕ)
    ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) / (W : ℝ)) /
        ((W.totient : ℝ) / (W : ℝ)) ^ (k + 2) =
      2 ^ (k + 1) * ∏ q ∈ s,
        (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2) := by
  intro W
  have hW_eq : (W : ℝ) = 2 * ∏ q ∈ s, ((q : ℕ) : ℝ) := by
    dsimp [W]; push_cast; rfl
  have hS_eq : (Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) =
      ∏ q ∈ s, (((q : ℕ) : ℝ) - (Nat.numResidues q m : ℝ)) := by
    rw [surviving_card_wheel m hzero heven s, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q _
    have hle : Nat.numResidues q m ≤ q := by
      have : NeZero (q : ℕ) := ⟨q.2.1.ne_zero⟩
      unfold Nat.numResidues
      calc
        _ ≤ (Set.univ : Set (ZMod (q : ℕ))).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ
        _ = Nat.card (ZMod (q : ℕ)) := Set.ncard_univ _
        _ = (q : ℕ) := Nat.card_zmod _
    rw [Nat.cast_sub hle]
  have hT_eq : (W.totient : ℝ) = ∏ q ∈ s, (((q : ℕ) : ℝ) - 1) := by
    dsimp [W]
    rw [totient_wheel s, Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro q _
    rw [Nat.cast_sub q.2.1.one_le, Nat.cast_one]
  have hnum_eq : (Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) / (W : ℝ) =
      (1 / 2) * ∏ q ∈ s, (1 - (Nat.numResidues q m : ℝ) / q) := by
    rw [hS_eq, hW_eq, div_mul_eq_div_div, div_right_comm, ← Finset.prod_div_distrib,
      div_eq_mul_inv, mul_comm, one_div]
    congr 1
    apply Finset.prod_congr rfl
    intro q _
    have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.2.1.ne_zero
    rw [sub_div, div_self hq]
  have hden_eq : (W.totient : ℝ) / (W : ℝ) =
      (1 / 2) * ∏ q ∈ s, (1 - 1 / ((q : ℕ) : ℝ)) := by
    rw [hT_eq, hW_eq, div_mul_eq_div_div, div_right_comm, ← Finset.prod_div_distrib,
      div_eq_mul_inv, mul_comm, one_div]
    congr 1
    apply Finset.prod_congr rfl
    intro q _
    have hq : ((q : ℕ) : ℝ) ≠ 0 := by exact_mod_cast q.2.1.ne_zero
    rw [sub_div, div_self hq]
  have h2 : (1 / 2 : ℝ) / (1 / 2 : ℝ) ^ (k + 2) = 2 ^ (k + 1) := by
    rw [one_div, inv_pow, div_inv_eq_mul, pow_succ]
    ring
  rw [hnum_eq, hden_eq, mul_pow, ← Finset.prod_pow, mul_div_mul_comm, ← Finset.prod_div_distrib, h2]

/- ### Part 2: Residue-class counting, PNT in AP shift, and |I| = 0, 1 terms -/

lemma card_residue_class_Ioc (W : ℕ) (hW : 0 < W) (r : ZMod W) (N : ℕ) :
    N / W ≤ ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card ∧
    ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card ≤ N / W + 1 := by
  have : NeZero W := ⟨hW.ne'⟩
  let r0 := if r.val = 0 then W else r.val
  have hr0_pos : 0 < r0 := by
    dsimp [r0]; split_ifs with h; exact hW; omega
  have hr0_le : r0 ≤ W := by
    dsimp [r0]; split_ifs with h; exact le_rfl; exact (ZMod.val_lt r).le
  have hr0_cast : (r0 : ZMod W) = r := by
    dsimp [r0]; split_ifs with h
    · rw [ZMod.natCast_self]; exact (ZMod.val_eq_zero r).mp h |>.symm
    · exact ZMod.natCast_zmod_val r
  have hmem : ∀ n : ℕ, n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r) ↔
      ∃ q : ℕ, n = r0 + q * W ∧ r0 + q * W ≤ N := by
    intro n
    simp only [mem_filter, mem_Ioc]
    constructor
    · rintro ⟨⟨hn0, hnN⟩, hnr⟩
      have hmod : n % W = r0 % W := by
        have h1 : (n : ZMod W) = (r0 : ZMod W) := hnr.trans hr0_cast.symm
        exact (ZMod.natCast_eq_natCast_iff' n r0 W).mp h1
      have hge : r0 ≤ n := by
        dsimp [r0] at hmod ⊢
        split_ifs at hmod ⊢ with h
        · rw [Nat.mod_self] at hmod
          have hdvd : W ∣ n := Nat.dvd_of_mod_eq_zero hmod
          exact Nat.le_of_dvd hn0 hdvd
        · have hlt : r.val < W := ZMod.val_lt r
          rw [Nat.mod_eq_of_lt hlt] at hmod
          have := Nat.mod_le n W
          omega
      have hdvd : W ∣ n - r0 := by
        rw [Nat.dvd_iff_mod_eq_zero]
        have h1 := Nat.div_add_mod n W
        have h2 := Nat.div_add_mod r0 W
        have h3 : W * (n / W - r0 / W) = W * (n / W) - W * (r0 / W) := Nat.mul_sub _ _ _
        have h4 : W * (r0 / W) ≤ W * (n / W) := Nat.mul_le_mul_left W (Nat.div_le_div_right hge)
        have heq : n - r0 = W * (n / W - r0 / W) := by omega
        rw [heq, Nat.mul_mod_right]
      obtain ⟨q, hq⟩ := hdvd
      rw [mul_comm] at hq
      refine ⟨q, by omega, by omega⟩
    · rintro ⟨q, rfl, hle⟩
      refine ⟨⟨by omega, hle⟩, ?_⟩
      rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, hr0_cast]
  have hcard_low : N / W ≤ ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card := by
    have hinj : Set.InjOn (fun q => r0 + q * W) (Finset.range (N / W)) := by
      intro a _ b _ hab
      dsimp at hab
      have : a * W = b * W := by omega
      exact Nat.eq_of_mul_eq_mul_right hW this
    have hsub : (Finset.range (N / W)).image (fun q => r0 + q * W) ⊆
        (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r) := by
      intro n hn
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hn
      rw [mem_range] at hq
      rw [hmem]
      refine ⟨q, rfl, ?_⟩
      have hdiv : (N / W) * W ≤ N := Nat.div_mul_le_self N W
      have hq1 : (q + 1) * W ≤ (N / W) * W := Nat.mul_le_mul_right W (by omega)
      nlinarith
    calc
      N / W = (Finset.range (N / W)).card := (Finset.card_range _).symm
      _ = ((Finset.range (N / W)).image (fun q => r0 + q * W)).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_card hsub
  have hcard_high : ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card ≤ N / W + 1 := by
    have hsub : (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r) ⊆
        (Finset.range (N / W + 1)).image (fun q => r0 + q * W) := by
      intro n hn
      obtain ⟨q, rfl, hle⟩ := (hmem n).mp hn
      refine mem_image.mpr ⟨q, mem_range.mpr ?_, rfl⟩
      have hqW : q * W ≤ N := by omega
      have : q ≤ N / W := (Nat.le_div_iff_mul_le hW).mpr hqW
      omega
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
  exact ⟨hcard_low, hcard_high⟩

lemma tendsto_residue_class_density (W : ℕ) (hW : 0 < W) (r : ZMod W) :
    Tendsto (fun N : ℕ =>
      (W : ℝ) / (N : ℝ) * (((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card : ℝ))
      atTop (𝓝 1) := by
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hzero : Tendsto (fun N : ℕ => (W : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlow := (tendsto_const_nhds (x := (1 : ℝ))).sub hzero
  have hhigh := (tendsto_const_nhds (x := (1 : ℝ))).add hzero
  rw [sub_zero] at hlow
  rw [add_zero] at hhigh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hhigh
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hc := (card_residue_class_Ioc W hW r N).1
    have hdiv : (N : ℝ) - (W : ℝ) ≤ (W : ℝ) * ((N / W : ℕ) : ℝ) := by
      have hnat : N < (N / W + 1) * W := by
        have h1 := Nat.div_add_mod N W
        have h2 := Nat.mod_lt N hW
        nlinarith
      have hreal : (N : ℝ) ≤ ((N / W : ℕ) : ℝ) * (W : ℝ) + (W : ℝ) := by
        exact_mod_cast (by nlinarith : N ≤ (N / W) * W + W)
      linarith
    have h1 : 1 - (W : ℝ) / (N : ℝ) = ((N : ℝ) - (W : ℝ)) / (N : ℝ) := by
      field_simp [hNpos.ne']
    rw [h1, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hNpos.le
    exact hdiv.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hc) hWpos.le)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hc := (card_residue_class_Ioc W hW r N).2
    have hdiv : (W : ℝ) * ((N / W : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (by rw [mul_comm]; exact Nat.div_mul_le_self N W)
    have h1 : 1 + (W : ℝ) / (N : ℝ) = ((N : ℝ) + (W : ℝ)) / (N : ℝ) := by
      field_simp [hNpos.ne']
    rw [h1, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hNpos.le
    have hc' : (((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card : ℝ) ≤
        ((N / W : ℕ) : ℝ) + 1 := by exact_mod_cast hc
    nlinarith

lemma tendsto_shift_psiAP (hH1 : H1) (W : ℕ) (hW : 0 < W) (r : ZMod W) (c : ℕ)
    (hu : IsUnit (r + (c : ZMod W))) :
    Tendsto (fun N : ℕ =>
      ((W.totient : ℝ) / (N : ℝ)) *
        ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
          vonMangoldt (n + c))
      atTop (𝓝 1) := by
  have hbase := hH1 W hW (r + (c : ZMod W)) hu
  have hdiff : Tendsto (fun N : ℕ =>
      ((W.totient : ℝ) / (N : ℝ)) *
        ((∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r), vonMangoldt (n + c)) -
         (∑ m ∈ (Finset.Ioc 0 N).filter (fun m : ℕ => (m : ZMod W) = r + (c : ZMod W)),
           vonMangoldt m))) atTop (𝓝 0) := by
    have hlog_zero : Tendsto (fun N : ℕ =>
        ((W.totient : ℝ) * (c : ℝ)) * (Real.log ((N + c : ℕ) : ℝ) / (N : ℝ))) atTop (𝓝 0) := by
      have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
        have h := (isLittleO_log_rpow_rpow_atTop (1 : ℝ) zero_lt_one).tendsto_div_nhds_zero
        refine h.congr' ?_
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with x _
        simp [Real.rpow_one]
      have ht : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat c)
      have hrat : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
        have h := (tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (c : ℝ))
        rw [mul_zero, add_zero] at h
        apply Tendsto.congr' _ h
        filter_upwards [eventually_gt_atTop 0] with N hN
        have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
        simp only [Pi.inv_apply]; push_cast; field_simp
      have hprod := ((hl.comp ht).mul hrat).const_mul ((W.totient : ℝ) * (c : ℝ))
      rw [zero_mul, mul_zero] at hprod
      refine hprod.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hNc : ((N + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + c ≠ 0)
      simp only [Function.comp_apply]
      rw [div_mul_div_cancel₀ hNc]
    apply squeeze_zero_norm' _ hlog_zero
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hTnn : 0 ≤ (W.totient : ℝ) := Nat.cast_nonneg _
    have hLnn : 0 ≤ Real.log ((N + c : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + c))
    -- Reindex the first sum by m = n + c ∈ Ioc c (N + c)
    have hreidx : ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r), vonMangoldt (n + c) =
        ∑ m ∈ (Finset.Ioc c (N + c)).filter (fun m : ℕ => (m : ZMod W) = r + (c : ZMod W)),
          vonMangoldt m := by
      have himg : ((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).image (fun n => n + c) =
          (Finset.Ioc c (N + c)).filter (fun m : ℕ => (m : ZMod W) = r + (c : ZMod W)) := by
        ext m
        simp only [mem_image, mem_filter, mem_Ioc]
        constructor
        · rintro ⟨n, ⟨⟨hn0, hnN⟩, hnr⟩, rfl⟩
          exact ⟨⟨by omega, by omega⟩, by rw [Nat.cast_add, hnr]⟩
        · rintro ⟨⟨hmc, hmN⟩, hmr⟩
          refine ⟨m - c, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
          have h1 : ((m - c : ℕ) : ZMod W) + (c : ZMod W) = (m : ZMod W) := by
            rw [← Nat.cast_add, Nat.sub_add_cancel (by omega)]
          rw [hmr] at h1
          exact add_right_cancel h1
      rw [← himg, Finset.sum_image (fun _ _ _ _ h => Nat.add_right_cancel h)]
    rw [hreidx, Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg hTnn hNpos.le)]
    set S1 := (Finset.Ioc c (N + c)).filter (fun m : ℕ => (m : ZMod W) = r + (c : ZMod W))
    set S2 := (Finset.Ioc 0 N).filter (fun m : ℕ => (m : ZMod W) = r + (c : ZMod W))
    have hle_abs : |∑ m ∈ S1, vonMangoldt m - ∑ m ∈ S2, vonMangoldt m| ≤
        (c : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
      have h1 : ∑ m ∈ S1, vonMangoldt m - ∑ m ∈ S2, vonMangoldt m =
          ∑ m ∈ S1 \ S2, vonMangoldt m - ∑ m ∈ S2 \ S1, vonMangoldt m := by
        have hs1 := (Finset.sum_union (f := fun m => vonMangoldt m)
          (Finset.disjoint_sdiff_inter S1 S2)).symm
        rw [Finset.sdiff_union_inter] at hs1
        have hs2 := (Finset.sum_union (f := fun m => vonMangoldt m)
          (Finset.disjoint_sdiff_inter S2 S1)).symm
        rw [Finset.sdiff_union_inter, Finset.inter_comm S2 S1] at hs2
        linarith
      have hS1 : ∑ m ∈ S1 \ S2, vonMangoldt m ≤ (c : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
        have hsub : S1 \ S2 ⊆ Finset.Ioc N (N + c) := by
          intro m hm
          rw [Finset.mem_sdiff] at hm
          have h1 := mem_filter.mp hm.1
          have h2 := hm.2
          simp only [S2, mem_filter, mem_Ioc] at h2
          simp only [mem_Ioc] at h1 ⊢
          have : N < m := by
            by_contra hle
            exact h2 ⟨⟨by omega, by omega⟩, h1.2⟩
          exact ⟨this, h1.1.2⟩
        calc
          ∑ m ∈ S1 \ S2, vonMangoldt m ≤ ∑ _m ∈ S1 \ S2, Real.log ((N + c : ℕ) : ℝ) := by
            apply sum_le_sum; intro m hm
            have hmI := mem_Ioc.mp (hsub hm)
            exact vonMangoldt_le_log.trans
              (Real.log_le_log (by exact_mod_cast (by omega : 0 < m))
                (by exact_mod_cast hmI.2))
          _ = ((S1 \ S2).card : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (c : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hLnn
            have hc : (S1 \ S2).card ≤ c := by
              have := (Finset.card_le_card hsub).trans_eq (Nat.card_Ioc N (N + c))
              omega
            exact_mod_cast hc
      have hS2 : ∑ m ∈ S2 \ S1, vonMangoldt m ≤ (c : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
        have hsub : S2 \ S1 ⊆ Finset.Ioc 0 c := by
          intro m hm
          rw [Finset.mem_sdiff] at hm
          have h1 := mem_filter.mp hm.1
          have h2 := hm.2
          simp only [S1, mem_filter, mem_Ioc] at h2
          simp only [mem_Ioc] at h1 ⊢
          have : m ≤ c := by
            by_contra hgt
            exact h2 ⟨⟨by omega, by omega⟩, h1.2⟩
          exact ⟨h1.1.1, this⟩
        calc
          ∑ m ∈ S2 \ S1, vonMangoldt m ≤ ∑ _m ∈ S2 \ S1, Real.log ((N + c : ℕ) : ℝ) := by
            apply sum_le_sum; intro m hm
            have hmI := mem_Ioc.mp (hsub hm)
            exact vonMangoldt_le_log.trans
              (Real.log_le_log (by exact_mod_cast hmI.1)
                (by exact_mod_cast (by omega : m ≤ N + c)))
          _ = ((S2 \ S1).card : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
            rw [sum_const, nsmul_eq_mul]
          _ ≤ (c : ℝ) * Real.log ((N + c : ℕ) : ℝ) := by
            apply mul_le_mul_of_nonneg_right _ hLnn
            have hc : (S2 \ S1).card ≤ c := by
              have := (Finset.card_le_card hsub).trans_eq (Nat.card_Ioc 0 c)
              omega
            exact_mod_cast hc
      have hnn1 : 0 ≤ ∑ m ∈ S1 \ S2, vonMangoldt m := sum_nonneg fun _ _ => vonMangoldt_nonneg
      have hnn2 : 0 ≤ ∑ m ∈ S2 \ S1, vonMangoldt m := sum_nonneg fun _ _ => vonMangoldt_nonneg
      rw [h1, abs_le]
      constructor <;> linarith
    calc
      (W.totient : ℝ) / (N : ℝ) * |∑ m ∈ S1, vonMangoldt m - ∑ m ∈ S2, vonMangoldt m|
          ≤ (W.totient : ℝ) / (N : ℝ) * ((c : ℝ) * Real.log ((N + c : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hle_abs (div_nonneg hTnn hNpos.le)
      _ = (W.totient : ℝ) * (c : ℝ) * (Real.log ((N + c : ℕ) : ℝ) / (N : ℝ)) := by ring
  have hsum := hbase.add hdiff
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards with N
  ring

lemma filter_coprime_eq_biUnion {k : ℕ} (m : Fin (k + 2) → ℕ) (W : ℕ) (hW : 0 < W) (N : ℕ) :
    letI : NeZero W := ⟨hW.ne'⟩
    (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W) =
      ((Finset.univ : Finset (ZMod W)).filter (fun r => ∀ i, IsUnit (r + (m i : ZMod W)))).biUnion
        (fun r => (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)) := by
  have : NeZero W := ⟨hW.ne'⟩
  ext n
  simp only [mem_filter, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨hnI, hcop⟩
    refine ⟨(n : ZMod W), ?_, hnI, rfl⟩
    intro i
    rw [← Nat.cast_add]
    exact (ZMod.isUnit_iff_coprime (n + m i) W).mpr (hcop i)
  · rintro ⟨r, hr, hnI, hnr⟩
    refine ⟨hnI, fun i => ?_⟩
    rw [← ZMod.isUnit_iff_coprime, Nat.cast_add, hnr]
    exact hr i

lemma linear_term_tendsto_zero (hH1 : H1) {k : ℕ} (m : Fin (k + 2) → ℕ)
    (W : ℕ) (hW : 0 < W)
    (hSurv_pos : 0 < Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))})
    (j : Fin (k + 2)) :
    Tendsto (fun N : ℕ =>
      (W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
        ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
          ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m j) - 1))
      atTop (𝓝 0) := by
  classical
  have : NeZero W := ⟨hW.ne'⟩
  let S := (Finset.univ : Finset (ZMod W)).filter (fun r => ∀ i, IsUnit (r + (m i : ZMod W)))
  have hScard : S.card = Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by rw [hScard]; exact_mod_cast hSurv_pos
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hper : ∀ r ∈ S,
      Tendsto (fun N : ℕ =>
        (W : ℝ) / (N : ℝ) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m j) - 1))
        atTop (𝓝 0) := by
    intro r hr
    have hu : IsUnit (r + (m j : ZMod W)) := (mem_filter.mp hr).2 j
    have h1 := tendsto_shift_psiAP hH1 W hW r (m j) hu
    have h2 := tendsto_residue_class_density W hW r
    have hsub := h1.sub h2
    rw [sub_self] at hsub
    refine hsub.congr' ?_
    filter_upwards with N
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one,
      mul_sub]
    congr 1
    field_simp [hWpos.ne']
  have havg : Tendsto (fun N : ℕ =>
      (1 / (S.card : ℝ)) * ∑ r ∈ S,
        ((W : ℝ) / (N : ℝ) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r),
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m j) - 1)))
      atTop (𝓝 0) := by
    have hs := (tendsto_finsetSum S hper).const_mul (1 / (S.card : ℝ))
    simpa using hs
  refine havg.congr' ?_
  filter_upwards with N
  have hdisj : Set.PairwiseDisjoint (S : Set (ZMod W))
      (fun r => (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)) := by
    intro r1 _ r2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    exact hne ((mem_filter.mp hn1).2.symm.trans (mem_filter.mp hn2).2)
  rw [filter_coprime_eq_biUnion m W hW N, Finset.sum_biUnion hdisj, ← Finset.mul_sum, ← hScard]
  ring

lemma empty_term_tendsto_one {k : ℕ} (m : Fin (k + 2) → ℕ) (W : ℕ) (hW : 0 < W)
    (hSurv_pos : 0 < Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))}) :
    Tendsto (fun N : ℕ =>
      (W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
        ∑ _n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W), (1 : ℝ))
      atTop (𝓝 1) := by
  classical
  have : NeZero W := ⟨hW.ne'⟩
  let S := (Finset.univ : Finset (ZMod W)).filter (fun r => ∀ i, IsUnit (r + (m i : ZMod W)))
  have hScard : S.card = Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hSpos : (0 : ℝ) < (S.card : ℝ) := by rw [hScard]; exact_mod_cast hSurv_pos
  have havg : Tendsto (fun N : ℕ =>
      (1 / (S.card : ℝ)) * ∑ r ∈ S,
        ((W : ℝ) / (N : ℝ) *
          (((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card : ℝ)))
      atTop (𝓝 1) := by
    have hs := (tendsto_finsetSum S fun r _ => tendsto_residue_class_density W hW r).const_mul
      (1 / (S.card : ℝ))
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, one_div_mul_cancel hSpos.ne'] at hs
    exact hs
  refine havg.congr' ?_
  filter_upwards with N
  have hdisj : Set.PairwiseDisjoint (S : Set (ZMod W))
      (fun r => (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)) := by
    intro r1 _ r2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    exact hne ((mem_filter.mp hn1).2.symm.trans (mem_filter.mp hn2).2)
  rw [filter_coprime_eq_biUnion m W hW N, Finset.sum_biUnion hdisj, ← Finset.mul_sum, ← hScard]
  have hcongr : ∑ r ∈ S,
      (((Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r)).card : ℝ) =
      ∑ r ∈ S, ∑ _n ∈ (Finset.Ioc 0 N).filter (fun n : ℕ => (n : ZMod W) = r), (1 : ℝ) := by
    apply sum_congr rfl; intro r _
    rw [sum_const, nsmul_eq_mul, mul_one]
  rw [hcongr]
  ring

/- ### Part 3: Negligibility of non-coprime terms & singular series convergence -/

lemma card_prime_powers_div_le (q M : ℕ) (hq : q.Prime) :
    ((Finset.Icc 1 M).filter (fun x => q ∣ x ∧ IsPrimePow x)).card ≤ Nat.log 2 M + 1 := by
  have hsub : (Finset.Icc 1 M).filter (fun x => q ∣ x ∧ IsPrimePow x) ⊆
      (Finset.range (Nat.log 2 M + 1)).image (fun e => q ^ e) := by
    intro x hx
    simp only [mem_filter, mem_Icc] at hx
    obtain ⟨⟨hx1, hxM⟩, hqx, hpp⟩ := hx
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, e, hp, he, rfl⟩ := hpp
    have hpq : q = p := by
      have hqp := hq.dvd_of_dvd_pow hqx
      exact (hp.eq_one_or_self_of_dvd q hqp).resolve_left hq.ne_one
    subst hpq
    refine mem_image.mpr ⟨e, mem_range.mpr ?_, rfl⟩
    have h2e : 2 ^ e ≤ M := le_trans (Nat.pow_le_pow_left hq.two_le e) hxM
    have hMpos : 0 < M := lt_of_lt_of_le (by omega) hxM
    have hle : e ≤ Nat.log 2 M := (Nat.le_log_iff_pow_le (by omega) hMpos.ne').mpr h2e
    omega
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

lemma non_coprime_sum_le {k : ℕ} (m : Fin (k + 2) → ℕ) (W H : ℕ)
    (hW : 0 < W) (hm : ∀ i, m i ≤ H) (N : ℕ) (hNH : 1 ≤ N + H) :
    ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
      ∏ i : Fin (k + 2), vonMangoldt (n + m i) ≤
      ((W.primeFactors.card : ℝ) * (k + 2 : ℝ) * ((Nat.log 2 (N + H) + 1 : ℕ) : ℝ)) *
        (Real.log (N + H : ℕ)) ^ (k + 2) := by
  classical
  let L := Real.log (N + H : ℕ)
  have hL : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hNH)
  have hterm : ∀ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
      ∏ i : Fin (k + 2), vonMangoldt (n + m i) ≤
        if ∃ i : Fin (k + 2), ∃ q ∈ W.primeFactors, q ∣ n + m i ∧ IsPrimePow (n + m i)
        then L ^ (k + 2) else 0 := by
    intro n hn
    have hn_mem := (mem_filter.mp hn).1
    have hn_nc := (mem_filter.mp hn).2
    have h0 := (mem_Ioc.mp hn_mem).1
    have hN := (mem_Ioc.mp hn_mem).2
    split_ifs with hex
    · calc
        ∏ i : Fin (k + 2), vonMangoldt (n + m i) ≤ ∏ _i : Fin (k + 2), L := by
          apply Finset.prod_le_prod (fun _ _ => vonMangoldt_nonneg)
          intro i _
          have hmi := hm i
          exact vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast (by omega : 0 < n + m i))
              (by exact_mod_cast (by omega : n + m i ≤ N + H)))
        _ = L ^ (k + 2) := by rw [Finset.prod_const, Finset.card_fin]
    · push Not at hn_nc
      obtain ⟨i, hi⟩ := hn_nc
      have hgcd : 1 < Nat.gcd (n + m i) W := by
        have hne : Nat.gcd (n + m i) W ≠ 1 := hi
        have hpos : 0 < Nat.gcd (n + m i) W := Nat.gcd_pos_of_pos_right _ hW
        omega
      obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd (n + m i) W ≠ 1)
      have hqn : q ∣ n + m i := dvd_trans hqd (Nat.gcd_dvd_left _ _)
      have hqW : q ∣ W := dvd_trans hqd (Nat.gcd_dvd_right _ _)
      have hqmem : q ∈ W.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqW, hW.ne'⟩
      have hnotpp : ¬ IsPrimePow (n + m i) := fun hpp => hex ⟨i, q, hqmem, hqn, hpp⟩
      have hzero : vonMangoldt (n + m i) = 0 := vonMangoldt_eq_zero_iff.mpr hnotpp
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero]
  let bad := (Finset.Ioc 0 N).filter
    (fun n => ∃ i : Fin (k + 2), ∃ q ∈ W.primeFactors, q ∣ n + m i ∧ IsPrimePow (n + m i))
  have hcard_bad : bad.card ≤ W.primeFactors.card * (k + 2) * (Nat.log 2 (N + H) + 1) := by
    have hsub : bad ⊆ (W.primeFactors ×ˢ (Finset.univ : Finset (Fin (k + 2)))).biUnion
        (fun qi => (Finset.Ioc 0 N).filter (fun n => qi.1 ∣ n + m qi.2 ∧ IsPrimePow (n + m qi.2))) := by
      intro n hn
      obtain ⟨hnI, i, q, hq, hqd, hpp⟩ := mem_filter.mp hn
      exact mem_biUnion.mpr ⟨(q, i), mem_product.mpr ⟨hq, mem_univ i⟩,
        mem_filter.mpr ⟨hnI, hqd, hpp⟩⟩
    calc
      bad.card ≤ ∑ qi ∈ W.primeFactors ×ˢ (Finset.univ : Finset (Fin (k + 2))),
          ((Finset.Ioc 0 N).filter (fun n => qi.1 ∣ n + m qi.2 ∧ IsPrimePow (n + m qi.2))).card :=
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      _ ≤ ∑ _qi ∈ W.primeFactors ×ˢ (Finset.univ : Finset (Fin (k + 2))),
          (Nat.log 2 (N + H) + 1) := by
        apply Finset.sum_le_sum
        intro qi hqi
        have hq : qi.1.Prime := (Nat.mem_primeFactors.mp (mem_product.mp hqi).1).1
        have hinj : Set.InjOn (fun n => n + m qi.2)
            ((Finset.Ioc 0 N).filter (fun n => qi.1 ∣ n + m qi.2 ∧ IsPrimePow (n + m qi.2))) :=
          fun _ _ _ _ h => Nat.add_right_cancel h
        rw [← Finset.card_image_of_injOn hinj]
        have himg : ((Finset.Ioc 0 N).filter (fun n => qi.1 ∣ n + m qi.2 ∧ IsPrimePow (n + m qi.2))).image
            (fun n => n + m qi.2) ⊆ (Finset.Icc 1 (N + H)).filter (fun x => qi.1 ∣ x ∧ IsPrimePow x) := by
          intro x hx
          obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
          obtain ⟨hnI, hqd, hpp⟩ := mem_filter.mp hn
          have h0 := (mem_Ioc.mp hnI).1
          have hN := (mem_Ioc.mp hnI).2
          have hmi := hm qi.2
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hqd, hpp⟩
        exact (Finset.card_le_card himg).trans (card_prime_powers_div_le qi.1 (N + H) hq)
      _ = W.primeFactors.card * (k + 2) * (Nat.log 2 (N + H) + 1) := by
        rw [Finset.sum_const, Finset.card_product, Finset.card_fin, smul_eq_mul]
  calc
    ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)
        ≤ ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
          if ∃ i : Fin (k + 2), ∃ q ∈ W.primeFactors, q ∣ n + m i ∧ IsPrimePow (n + m i)
          then L ^ (k + 2) else 0 := sum_le_sum hterm
    _ ≤ ∑ n ∈ Finset.Ioc 0 N,
          if ∃ i : Fin (k + 2), ∃ q ∈ W.primeFactors, q ∣ n + m i ∧ IsPrimePow (n + m i)
          then L ^ (k + 2) else 0 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro n _ _; split_ifs <;> positivity
    _ = (bad.card : ℝ) * L ^ (k + 2) := by
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ((W.primeFactors.card : ℝ) * (k + 2 : ℝ) * ((Nat.log 2 (N + H) + 1 : ℕ) : ℝ)) * L ^ (k + 2) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hL _)
      exact_mod_cast hcard_bad

lemma non_coprime_tendsto_zero {k : ℕ} (m : Fin (k + 2) → ℕ) (W : ℕ) (hW : 0 < W) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ)) atTop (𝓝 0) := by
  let H := Finset.univ.sup m + 2
  have hm : ∀ i, m i ≤ H := fun i =>
    (Finset.le_sup (f := m) (Finset.mem_univ i)).trans (by omega)
  have hlog_pow : Tendsto (fun x : ℝ => Real.log x ^ (k + 3) / x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop ((k + 3 : ℕ) : ℝ) zero_lt_one).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x _
    rw [Real.rpow_natCast, Real.rpow_one]
  have ht : Tendsto (fun N : ℕ => ((N + H : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat H)
  let C0 : ℝ := (W.primeFactors.card : ℝ) * (k + 2 : ℝ) * (2 / Real.log 2 + 2)
  have hsmall : Tendsto (fun N : ℕ =>
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / ((N + H : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ =>
        C0 * (Real.log ((N + H : ℕ) : ℝ) ^ (k + 3) / ((N + H : ℕ) : ℝ))) atTop (𝓝 0) := by
      have h := (hlog_pow.comp ht).const_mul C0
      rwa [mul_zero] at h
    apply squeeze_zero_norm' _ hbound
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hNH3 : 3 ≤ N + H := by omega
    have hpos : 0 < ((N + H : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + H)
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlog1 : 1 ≤ Real.log ((N + H : ℕ) : ℝ) :=
      (Real.le_log_iff_exp_le hpos).mpr
        (Real.exp_one_lt_three.le.trans (by exact_mod_cast hNH3))
    have hsum_nn : 0 ≤ ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i) :=
      sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => vonMangoldt_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hsum_nn hpos.le)]
    have hnatlog : ((Nat.log 2 (N + H) + 1 : ℕ) : ℝ) ≤
        (2 / Real.log 2 + 2) * Real.log ((N + H : ℕ) : ℝ) := by
      have h2pow : (2 : ℝ) ^ (Nat.log 2 (N + H)) ≤ ((N + H : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : N + H ≠ 0)
      have hlog_le : (Nat.log 2 (N + H) : ℝ) * Real.log 2 ≤ Real.log ((N + H : ℕ) : ℝ) := by
        have := Real.log_le_log (by positivity) h2pow
        rwa [Real.log_pow] at this
      have h1 : (Nat.log 2 (N + H) : ℝ) ≤ Real.log ((N + H : ℕ) : ℝ) / Real.log 2 :=
        (le_div_iff₀ hlog2).mpr hlog_le
      rw [Nat.cast_add, Nat.cast_one]
      have h2 : Real.log ((N + H : ℕ) : ℝ) / Real.log 2 ≤
          (2 / Real.log 2) * Real.log ((N + H : ℕ) : ℝ) := by
        have : 0 ≤ Real.log ((N + H : ℕ) : ℝ) / Real.log 2 := by positivity
        ring_nf at this ⊢
        linarith
      nlinarith
    have hle := non_coprime_sum_le m W H hW hm N (by omega)
    calc
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
          ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / ((N + H : ℕ) : ℝ)
          ≤ (((W.primeFactors.card : ℝ) * (k + 2 : ℝ) * ((Nat.log 2 (N + H) + 1 : ℕ) : ℝ)) *
              (Real.log ((N + H : ℕ) : ℝ)) ^ (k + 2)) / ((N + H : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hle hpos.le
      _ ≤ (C0 * (Real.log ((N + H : ℕ) : ℝ)) ^ (k + 3)) / ((N + H : ℕ) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        have hstep : ((W.primeFactors.card : ℝ) * (k + 2 : ℝ) * ((Nat.log 2 (N + H) + 1 : ℕ) : ℝ)) *
            (Real.log ((N + H : ℕ) : ℝ)) ^ (k + 2) ≤
            ((W.primeFactors.card : ℝ) * (k + 2 : ℝ) *
              ((2 / Real.log 2 + 2) * Real.log ((N + H : ℕ) : ℝ))) *
              (Real.log ((N + H : ℕ) : ℝ)) ^ (k + 2) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hnatlog (by positivity)
        refine hstep.trans_eq ?_
        dsimp [C0]
        rw [show k + 3 = (k + 2) + 1 by omega, pow_succ]
        ring
      _ = C0 * (Real.log ((N + H : ℕ) : ℝ) ^ (k + 3) / ((N + H : ℕ) : ℝ)) := by
        rw [mul_div_assoc]
  have hratio : Tendsto (fun N : ℕ => ((N + H : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ)) (f := (atTop : Filter ℕ))).add
      ((tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (H : ℝ))
    rw [mul_zero, add_zero] at h
    apply Tendsto.congr' _ h
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Pi.inv_apply]
    push_cast
    field_simp
  have hmul := hsmall.mul hratio
  rw [zero_mul] at hmul
  apply Tendsto.congr' _ hmul
  filter_upwards with N
  have hNH : ((N + H : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + H ≠ 0)
  exact div_mul_div_cancel₀ hNH

lemma singular_series_hasProd {k : ℕ} (m : Fin (k + 2) → ℕ)
    (hinj : Function.Injective m)
    (hlocal : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q},
      ¬ Function.Surjective (fun i => (m i : ZMod q))) :
    HasProd (fun q : {q : ℕ // q.Prime ∧ 3 ≤ q} =>
      (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2))
      (∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
        (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2)) := by
  classical
  set f : {q : ℕ // q.Prime ∧ 3 ≤ q} → ℝ :=
    fun q => (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2) with hf
  let B := Finset.univ.sup m
  have hlt : ∀ q : {q : ℕ // q.Prime ∧ 3 ≤ q}, Nat.numResidues q m < q := by
    intro q
    have : NeZero (q : ℕ) := ⟨q.property.1.ne_zero⟩
    unfold Nat.numResidues
    calc
      _ < Nat.card (ZMod (q : ℕ)) := Set.ncard_lt_card (fun h => hlocal q (Set.range_eq_univ.mp h))
      _ = (q : ℕ) := Nat.card_zmod _
  have heq : ∀ q : ℕ, B < q → Nat.numResidues q m = k + 2 := by
    intro q hq
    have hsmall (i) : m i < q := (Finset.le_sup (f := m) (Finset.mem_univ i)).trans_lt hq
    have hj : Function.Injective (fun i => (m i : ZMod q)) := by
      intro i j he
      have h := (ZMod.natCast_eq_natCast_iff' _ _ _).mp he
      rw [Nat.mod_eq_of_lt (hsmall i), Nat.mod_eq_of_lt (hsmall j)] at h
      exact hinj h
    unfold Nat.numResidues
    rw [Set.ncard_range_of_injective hj]
    simp
  have hpos : ∀ q, 0 < f q := by
    intro q
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hl : (Nat.numResidues q m : ℝ) < (q : ℕ) := by exact_mod_cast hlt q
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hl
    · apply pow_pos
      rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hg : Summable fun q => f q - 1 := by
    have hs : Summable fun q : {q : ℕ // q.Prime ∧ 3 ≤ q} =>
        2 * ((k + 2 : ℕ) : ℝ) ^ 2 * (1 / ((q : ℕ) : ℝ) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).comp_injective
        Subtype.val_injective).mul_left _
    refine hs.of_norm_bounded_eventually ?_
    rw [Filter.eventually_cofinite]
    refine ((Set.finite_Iic (B + 2 * (k + 2))).preimage Subtype.val_injective.injOn).subset ?_
    intro q hq
    simp only [Set.mem_preimage, Set.mem_Iic]
    by_contra hbig
    apply hq
    have hbig' : B + 2 * (k + 2) < (q : ℕ) := by omega
    have hq' : 2 * ((k + 2 : ℕ) : ℝ) ≤ ((q : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 * (k + 2) ≤ (q : ℕ))
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (q : ℕ))
    rw [Real.norm_eq_abs, hf]
    dsimp only
    rw [heq _ (by omega)]
    exact OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2.factor_sub_one_le'
      (k + 2) _ hq' hq1
  have hlog : Summable fun q => Real.log (f q) :=
    (Real.summable_log_one_add_of_summable hg).congr fun q => by rw [add_sub_cancel]
  exact (Real.multipliable_of_summable_log hpos hlog).hasProd

/- ### Part 4: Main multilinear W-trick reduction theorem -/

set_option maxHeartbeats 600000 in
theorem main : H1 → H2 → OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2.H2 := by
  intro hH1 hH2 k m hzero heven hinj hlocal
  classical
  let C : ℝ := 2 ^ (k + 1) * ∏' (q : {q : ℕ // q.Prime ∧ 3 ≤ q}),
    (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2)
  have hCpos : 0 < C :=
    OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2.singular_series_pos m hinj hlocal
  have hprod : Tendsto (fun s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q} =>
      2 ^ (k + 1) * ∏ q ∈ s,
        (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2))
      atTop (𝓝 C) :=
    (singular_series_hasProd m hinj hlocal).const_mul (2 ^ (k + 1))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M : ℕ := ((Finset.univ : Finset (Fin (k + 2))).powerset.filter (fun I => 2 ≤ I.card)).card + 1
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.succ_pos _)
  let δ : ℝ := ε / (8 * (C + 1) * (M : ℝ))
  have hδ0 : 0 < δ := by positivity
  let highSets := (Finset.univ : Finset (Fin (k + 2))).powerset.filter (fun I => 2 ≤ I.card)
  have hall_high : ∀ᶠ s : Finset {q : ℕ // q.Prime ∧ 3 ≤ q} in atTop,
      ∀ I ∈ highSets,
        let W := 2 * ∏ q ∈ s, (q : ℕ)
        ∀ᶠ N : ℕ in atTop,
          |(W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
            ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
              ∏ i ∈ I, ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i) - 1)| < δ := by
    rw [Filter.eventually_all_finset]
    intro I hI
    exact hH2 m hzero heven hinj hlocal I (mem_filter.mp hI).2 δ hδ0
  obtain ⟨s, hCs, hhigh_s⟩ :=
    ((Metric.tendsto_nhds.mp hprod (min (ε / 4) 1) (lt_min (by positivity) one_pos)).and
      hall_high).exists
  let W := 2 * ∏ q ∈ s, (q : ℕ)
  have hWpos : 0 < W := wheel_pos s
  let Cs : ℝ := 2 ^ (k + 1) * ∏ q ∈ s,
    (1 - (Nat.numResidues q m : ℝ) / q) / (1 - 1 / (q : ℝ)) ^ (k + 2)
  have hCs_pos : 0 < Cs := by
    apply mul_pos (by positivity)
    apply Finset.prod_pos
    intro q _
    have : NeZero (q : ℕ) := ⟨q.2.1.ne_zero⟩
    have hq3 : (3 : ℝ) ≤ (q : ℕ) := by exact_mod_cast q.2.2
    have hlt : Nat.numResidues q m < q := by
      unfold Nat.numResidues
      calc
        _ < Nat.card (ZMod (q : ℕ)) := Set.ncard_lt_card (fun h => hlocal q (Set.range_eq_univ.mp h))
        _ = (q : ℕ) := Nat.card_zmod _
    have hl : (Nat.numResidues q m : ℝ) < (q : ℕ) := by exact_mod_cast hlt
    apply div_pos
    · rw [sub_pos, div_lt_one (by linarith)]; exact hl
    · apply pow_pos; rw [sub_pos, div_lt_one (by linarith)]; linarith
  have hCs_le : Cs ≤ C + 1 := by
    rw [Real.dist_eq] at hCs
    linarith [(abs_lt.mp hCs).2, min_le_right (ε / 4) (1 : ℝ)]
  have hCs_dist : |Cs - C| < ε / 4 := by
    rw [Real.dist_eq] at hCs
    exact lt_of_lt_of_le hCs (min_le_left _ _)
  have hSurv_pos_nat : 0 < Nat.card {r : ZMod W // ∀ i, IsUnit (r + (m i : ZMod W))} := by
    rw [surviving_card_wheel m hzero heven s]
    exact Finset.prod_pos fun q _ => by
      have : NeZero (q : ℕ) := ⟨q.2.1.ne_zero⟩
      have hlt : Nat.numResidues q m < q := by
        unfold Nat.numResidues
        calc
          _ < Nat.card (ZMod (q : ℕ)) := Set.ncard_lt_card (fun h => hlocal q (Set.range_eq_univ.mp h))
          _ = (q : ℕ) := Nat.card_zmod _
      omega
  have hSurv_pos : (0 : ℝ) < (Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) := by
    exact_mod_cast hSurv_pos_nat
  -- Combine |I| = 0 and |I| = 1 limits for this fixed W
  have hempty := Metric.tendsto_nhds.mp (empty_term_tendsto_one m W hWpos hSurv_pos_nat)
    (ε / (8 * (C + 1))) (by positivity)
  have hlin_all : ∀ᶠ N : ℕ in atTop,
      ∀ j : Fin (k + 2),
        |(W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
            ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m j) - 1)| <
          ε / (8 * (C + 1) * (k + 2 : ℝ)) := by
    rw [Filter.eventually_all]
    intro j
    have hlj := Metric.tendsto_nhds.mp
      (linear_term_tendsto_zero hH1 m W hWpos hSurv_pos_nat j)
      (ε / (8 * (C + 1) * (k + 2 : ℝ))) (by positivity)
    filter_upwards [hlj] with N hN
    rwa [Real.dist_eq, sub_zero] at hN
  have hhigh_all : ∀ᶠ N : ℕ in atTop,
      ∀ I ∈ highSets,
        |(W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
            ∏ i ∈ I, ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i) - 1)| < δ := by
    rw [Filter.eventually_all_finset]
    exact hhigh_s
  have hnc := Metric.tendsto_nhds.mp (non_coprime_tendsto_zero m W hWpos) (ε / 4) (by positivity)
  filter_upwards [eventually_gt_atTop 0, hempty, hlin_all, hhigh_all, hnc] with
      N hN0 heN hlinN hhighN hncN
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hW_ne : (W : ℝ) ≠ 0 := by exact_mod_cast hWpos.ne'
  have hT_pos : (0 : ℝ) < (W.totient : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hWpos)
  -- Exact W-trick factorization of the coprime sum
  let A : ℝ := (W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
    ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
      ∏ i : Fin (k + 2), ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i))
  have hcop_eq :
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ) = Cs * A := by
    have hfac : Cs = ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) / (W : ℝ)) /
        ((W.totient : ℝ) / (W : ℝ)) ^ (k + 2) :=
      (wheel_local_factor_eq m hzero heven s).symm
    have hpull : ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
          ∏ i : Fin (k + 2), ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i)) =
        ((W.totient : ℝ) / (W : ℝ)) ^ (k + 2) *
          ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
            ∏ i : Fin (k + 2), vonMangoldt (n + m i) := by
      rw [mul_sum]
      apply sum_congr rfl; intro n _
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]
    dsimp only [A]
    rw [hfac, hpull]
    have hTW : ((W.totient : ℝ) / (W : ℝ)) ^ (k + 2) ≠ 0 :=
      pow_ne_zero _ (div_pos hT_pos (by exact_mod_cast hWpos)).ne'
    field_simp [hW_ne, hNpos.ne', hSurv_pos.ne', hTW]
  -- Multilinear expansion of A into |I| = 0, |I| = 1, |I| ≥ 2
  let term (I : Finset (Fin (k + 2))) : ℝ :=
    (W : ℝ) / ((Nat.card {r : ZMod W // ∀ i, IsUnit (r + m i)} : ℝ) * (N : ℝ)) *
      ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
        ∏ i ∈ I, ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i) - 1)
  have hexpand : A = ∑ I ∈ (Finset.univ : Finset (Fin (k + 2))).powerset, term I := by
    dsimp only [A, term]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply sum_congr rfl; intro n _
    have hprod_eq : ∏ i : Fin (k + 2), ((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i)) =
        ∏ i : Fin (k + 2), (((W.totient : ℝ) / (W : ℝ) * vonMangoldt (n + m i) - 1) + 1) :=
      Finset.prod_congr rfl fun _ _ => by ring
    rw [hprod_eq, Finset.prod_add]
    apply sum_congr rfl; intro I _
    rw [Finset.prod_const_one, mul_one]
  have hpow_split : ∑ I ∈ (Finset.univ : Finset (Fin (k + 2))).powerset, term I =
      term ∅ + (∑ j : Fin (k + 2), term {j}) + ∑ I ∈ highSets, term I := by
    let P := (Finset.univ : Finset (Fin (k + 2))).powerset
    have hpart : P = insert ∅ ((Finset.univ.image (fun j : Fin (k + 2) => ({j} : Finset (Fin (k + 2))))) ∪ highSets) := by
      ext I
      simp only [P, highSets, mem_powerset, mem_insert, mem_union, mem_image, mem_filter,
        subset_univ, true_and]
      constructor
      · intro _
        by_cases h0 : I.card = 0
        · exact Or.inl (Finset.card_eq_zero.mp h0)
        · by_cases h1 : I.card = 1
          · obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp h1
            exact Or.inr (Or.inl ⟨j, mem_univ j, rfl⟩)
          · exact Or.inr (Or.inr (by omega))
      · intro _; trivial
    have hnotmem : (∅ : Finset (Fin (k + 2))) ∉
        (Finset.univ.image (fun j : Fin (k + 2) => ({j} : Finset (Fin (k + 2))))) ∪ highSets := by
      simp only [highSets, mem_union, mem_image, mem_filter, mem_powerset, subset_univ,
        Finset.card_empty]
      rintro (⟨j, _, hj⟩ | ⟨_, h2⟩)
      · exact Finset.singleton_ne_empty j hj
      · omega
    have hdisj : Disjoint (Finset.univ.image (fun j : Fin (k + 2) => ({j} : Finset (Fin (k + 2))))) highSets := by
      rw [Finset.disjoint_left]
      intro I hI1 hI2
      obtain ⟨j, _, rfl⟩ := mem_image.mp hI1
      have := (mem_filter.mp hI2).2
      simp at this
    rw [show (Finset.univ : Finset (Fin (k + 2))).powerset = P from rfl, hpart,
      sum_insert hnotmem, sum_union hdisj,
      Finset.sum_image (fun a _ b _ h => Finset.singleton_injective h), add_assoc]
  have hA_dist : |A - 1| < ε / (2 * (C + 1)) := by
    rw [hexpand, hpow_split]
    have hsplit_eq : term ∅ + (∑ j : Fin (k + 2), term {j}) + (∑ I ∈ highSets, term I) - 1 =
        (term ∅ - 1) + (∑ j : Fin (k + 2), term {j}) + (∑ I ∈ highSets, term I) := by ring
    rw [hsplit_eq]
    have h1 : |term ∅ - 1| < ε / (8 * (C + 1)) := by
      rw [Real.dist_eq] at heN
      simpa [term] using heN
    have h2 : |∑ j : Fin (k + 2), term {j}| ≤ ε / (8 * (C + 1)) := by
      calc
        |∑ j : Fin (k + 2), term {j}| ≤ ∑ j : Fin (k + 2), |term {j}| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin (k + 2), ε / (8 * (C + 1) * (k + 2 : ℝ)) := by
          apply sum_le_sum; intro j _
          exact (by simpa [term] using hlinN j : |term {j}| < _).le
        _ = (k + 2 : ℝ) * (ε / (8 * (C + 1) * (k + 2 : ℝ))) := by
          rw [sum_const, card_fin, nsmul_eq_mul]; push_cast; rfl
        _ = ε / (8 * (C + 1)) := by
          have hk2 : (k + 2 : ℝ) ≠ 0 := by positivity
          field_simp [hk2]
    have h3 : |∑ I ∈ highSets, term I| ≤ ε / (8 * (C + 1)) := by
      calc
        |∑ I ∈ highSets, term I| ≤ ∑ I ∈ highSets, |term I| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _I ∈ highSets, δ := sum_le_sum fun I hI => (hhighN I hI).le
        _ = (highSets.card : ℝ) * δ := by rw [sum_const, nsmul_eq_mul]
        _ ≤ (M : ℝ) * δ := by
          apply mul_le_mul_of_nonneg_right _ hδ0.le
          exact_mod_cast (Nat.le_succ highSets.card)
        _ = ε / (8 * (C + 1)) := by
          dsimp only [δ]
          field_simp [hMpos.ne']
    have htri : |(term ∅ - 1) + (∑ j : Fin (k + 2), term {j}) + (∑ I ∈ highSets, term I)| ≤
        |term ∅ - 1| + |∑ j : Fin (k + 2), term {j}| + |∑ I ∈ highSets, term I| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    have hfrac : 3 * (ε / (8 * (C + 1))) ≤ ε / (2 * (C + 1)) := by
      have hpos : 0 < ε / (C + 1) := by positivity
      have h1 : ε / (8 * (C + 1)) = (1 / 8) * (ε / (C + 1)) := by field_simp
      have h2 : ε / (2 * (C + 1)) = (1 / 2) * (ε / (C + 1)) := by field_simp
      rw [h1, h2]
      linarith
    linarith
  have hsplit_sum :
      (∑ n ∈ Finset.Ioc 0 N, ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ) =
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ) +
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ) := by
    rw [← add_div, Finset.sum_filter_add_sum_filter_not]
  rw [Real.dist_eq, hsplit_sum, hcop_eq]
  rw [Real.dist_eq, sub_zero] at hncN
  have hCsA : |Cs * A - Cs| < ε / 2 := by
    rw [show Cs * A - Cs = Cs * (A - 1) by ring, abs_mul, abs_of_pos hCs_pos]
    calc
      Cs * |A - 1| ≤ (C + 1) * |A - 1| := mul_le_mul_of_nonneg_right hCs_le (abs_nonneg _)
      _ < (C + 1) * (ε / (2 * (C + 1))) := mul_lt_mul_of_pos_left hA_dist (by positivity)
      _ = ε / 2 := by
        have hC1 : (C + 1) ≠ 0 := by positivity
        field_simp [hC1]
  have htot_eq : Cs * A +
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ) - C =
      (Cs * A - Cs) + (Cs - C) +
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ) := by ring
  rw [htot_eq]
  have htri : |(Cs * A - Cs) + (Cs - C) +
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ)| ≤
      |Cs * A - Cs| + |Cs - C| +
      |(∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬ ∀ i, Nat.Coprime (n + m i) W),
        ∏ i : Fin (k + 2), vonMangoldt (n + m i)) / (N : ℝ)| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  linarith

end OMA.R_HardyLittlewood_first_hardy_littlewood_conjecture_R2_H2_R2
