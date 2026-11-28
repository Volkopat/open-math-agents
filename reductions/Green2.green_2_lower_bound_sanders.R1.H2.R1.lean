import OMAReductions.R_Green2_green_2_lower_bound_sanders_R1
import Mathlib.Tactic

/-!
# Reduction of `Green2.green_2_lower_bound_sanders.R1.H2` (Beker 2025, Theorem 3.1)

Following A. Beker (*The Erdős–Moser sum-free set problem via improved bounds for $k$-configurations*,
arXiv:2501.10203, §3), Y. Filmus, H. Hatami, K. Hosseini, and E. Kelman (2024), Z. Kelley and
R. Meka (2023), and T. F. Bloom and O. Sisask (2023), we reduce the quasipolynomial bound
$$N \le \exp\!\bigl(C k^{68} (\log(2N/|A|))^{16}\bigr)$$
for subsets $A \subseteq \mathbb{Z}/N\mathbb{Z}$ ($N$ odd) lacking non-degenerate
$k$-configurations to two canonical, independent, self-contained pillars on regular Bohr sets:

1. `H1`: **Multi-scale regular Bohr localization & $k$-configuration counting dichotomy**
   (Beker Theorem 2.1 + Lemma 3.4 + §3.2): for any scale factor `s₀ ∈ (0, 1]`, on any regular Bohr
   set `B = B(Γ, ρ)` in odd `ZMod N` and nonempty `A ⊆ B` of density `α = |A| / |B|`, either `A`
   contains `≥ exp(-C₁ k² log(k) |Γ| log(2|Γ|/α)) ρ^{2k|Γ|} N^k` $k$-configurations, or `A` admits
   a direct regular-dilate density increment `(1 + c₁ k⁻⁵) α` on `Γ ∪ 2^{±1}·Γ`, or there exist
   nested regular Bohr dilates `B₁, B₂` of `Γ' = Γ ∪ 2⁻¹·Γ` (width ratio `≤ s₀ c₁ α / (k⁵ |Γ|)`)
   and nonempty `S ⊆ B₁`, `T ⊆ (A - x) ∩ B₂`, `D ⊆ 2·(A - x) ∩ B₂` (`μ_{B₂}(D) ∈ (1 ± c₁/(1024 k⁴)) α`)
   exhibiting either upward correlation bias (with `μ_{B₁}(S), μ_{B₂}(T) ≥ exp(-C₁ k⁶ L(α)²)`) or
   two-sided correlation bias (with `μ_{B₂}(T) ≥ (1 - c₁/(1024 k⁴)) α` and
   `μ_{B₁}(S) ≥ exp(-C₁ k⁶ log(k) L(α)²)`).
2. `H2`: **Kelley–Meka / Bloom–Sisask local density increment on regular Bohr sets**
   (Beker Propositions 3.3, 3.4 & Corollary 3.5): there exists a universal scale constant `s₀ ∈ (0, 1]`
   such that any such biased local triple `(S, T, D)` on nested regular Bohr sets `B₁, B₂` yields a
   frequency extension `Δ` (`|Δ| ≤ C₂ k⁴⁶ L(α)¹¹`), width
   `ρ' ≥ ρ₁ exp(-C₂ (k log(2d/α) + k⁶ L(α)²))`, and translate `y` where either `D - y` or `T - y`
   achieves density `(1 + c₂ k⁻⁵) α` on the regular Bohr set `B(Γ ∪ Δ, ρ')`.

Inside `main`, we prove from scratch:
- `2`-invertibility on odd `ZMod N`, integer powers `2^a`, and regularity/cardinality preservation
  under `2`-dilation of Bohr sets (`B(2·Γ, ρ) = 2⁻¹ · B(Γ, ρ)`).
- Assembly of **Beker Proposition 3.2** from `H1` and `H2`, transferring density increments on
  `D ⊆ 2·(A - x)` back to `A - (x + 2⁻¹ y)` on `Γ ∪ 2·Γ ∪ 2·Δ`.
- **Base regularity** of `B({0}, 1) = univ` and **Pilatte's quadratic frequency-set rank bound**
  `|Γ_t| ≤ (t + 1)(2t + 1) · max_r |Δ_r| = O(k⁵⁶ L¹³)`.
- **Maximal-length regular Bohr density-increment iteration** (`t ≤ (2/c) k⁵ L`), width tracking
  `ρ_t ≥ exp(-O(k¹¹ L³))`, final `k`-configuration count `≥ exp(-O(k⁶⁸ L¹⁶)) N^k`, translation
  invariance, and the degenerate-tuple bound `≤ k² N^{k-1}`.

Credit: @tkaiman
-/

open Finset Real
open scoped Classical BigOperators

namespace OMA.R_Green2_green_2_lower_bound_sanders_R1_H2_R1

/- ### Step 1: Explicit Bohr sets, `2`-invertibility, and integer powers of `2` in odd `ZMod N` -/

private def inv2 (N : ℕ) : ZMod N := ((N + 1) / 2 : ℕ)

private lemma odd_pos {N : ℕ} (hodd : Odd N) : 0 < N := by
  obtain ⟨m, rfl⟩ := hodd; omega

private lemma two_mul_inv2 {N : ℕ} (hodd : Odd N) : (2 : ZMod N) * inv2 N = 1 := by
  obtain ⟨m, rfl⟩ := hodd
  have hdiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  dsimp [inv2]
  rw [hdiv]
  have h0 : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self (2 * m + 1)
  have h1 : ((2 * (m + 1) : ℕ) : ZMod (2 * m + 1)) = 1 := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.cast_add, h0, zero_add, Nat.cast_one]
  simpa [Nat.cast_mul] using h1

private lemma inv2_mul_two {N : ℕ} (hodd : Odd N) : inv2 N * (2 : ZMod N) = 1 := by
  rw [mul_comm]; exact two_mul_inv2 hodd

private lemma mul_two_injective {N : ℕ} (hodd : Odd N) :
    Function.Injective (fun z : ZMod N => (2 : ZMod N) * z) := by
  intro a b hab
  have h := congrArg (fun u => inv2 N * u) hab
  simp only [← mul_assoc, inv2_mul_two hodd, one_mul] at h
  exact h

private lemma mul_inv2_injective {N : ℕ} (hodd : Odd N) :
    Function.Injective (fun z : ZMod N => inv2 N * z) := by
  intro a b hab
  have h := congrArg (fun u => (2 : ZMod N) * u) hab
  simp only [← mul_assoc, two_mul_inv2 hodd, one_mul] at h
  exact h

private def pow2 (N : ℕ) (a : ℤ) : ZMod N :=
  if 0 ≤ a then (2 : ZMod N) ^ a.toNat else (inv2 N) ^ (-a).toNat

private lemma pow2_zero (N : ℕ) : pow2 N 0 = 1 := by
  simp [pow2]

private lemma two_mul_pow2 {N : ℕ} (hodd : Odd N) (a : ℤ) :
    (2 : ZMod N) * pow2 N a = pow2 N (a + 1) := by
  dsimp [pow2]
  by_cases ha : 0 ≤ a
  · have ha1 : 0 ≤ a + 1 := by omega
    rw [if_pos ha, if_pos ha1]
    have hnat : (a + 1).toNat = a.toNat + 1 := by omega
    rw [hnat, pow_succ']
  · push Not at ha
    by_cases ha1 : a = -1
    · subst ha1
      simp only [show ¬ (0 : ℤ) ≤ -1 by omega, ↓reduceIte, neg_neg, Int.toNat_one, pow_one,
        neg_add_cancel, le_refl, Int.toNat_zero, pow_zero]
      exact two_mul_inv2 hodd
    · have hlt : ¬ (0 ≤ a + 1) := by omega
      rw [if_neg (by omega : ¬ 0 ≤ a), if_neg hlt]
      have hnat : (-a).toNat = (-(a + 1)).toNat + 1 := by omega
      rw [hnat, pow_succ', ← mul_assoc, two_mul_inv2 hodd, one_mul]

private lemma inv2_mul_pow2 {N : ℕ} (hodd : Odd N) (a : ℤ) :
    inv2 N * pow2 N a = pow2 N (a - 1) := by
  have h := two_mul_pow2 hodd (a - 1)
  rw [sub_add_cancel] at h
  have h2 := congrArg (fun u => inv2 N * u) h
  simp only [← mul_assoc, inv2_mul_two hodd, one_mul] at h2
  exact h2.symm

private noncomputable def bohr {N : ℕ} [NeZero N] (Γ : Finset (ZMod N)) (ρ : ℝ) : Finset (ZMod N) :=
  univ.filter fun x => ∀ γ ∈ Γ,
    min (((γ * x).val : ℝ) / N) (1 - ((γ * x).val : ℝ) / N) ≤ ρ

private def IsRegularBohr {N : ℕ} [NeZero N] (Γ : Finset (ZMod N)) (ρ : ℝ) : Prop :=
  Γ.Nonempty ∧ 0 < ρ ∧ ρ ≤ 1 ∧
  ∀ ε : ℝ, |ε| ≤ (100 * (Γ.card : ℝ))⁻¹ →
    (1 - 100 * (Γ.card : ℝ) * |ε|) * ((bohr Γ ρ).card : ℝ) ≤ ((bohr Γ ((1 + ε) * ρ)).card : ℝ) ∧
    ((bohr Γ ((1 + ε) * ρ)).card : ℝ) ≤ (1 + 100 * (Γ.card : ℝ) * |ε|) * ((bohr Γ ρ).card : ℝ)

private lemma bohr_zero_mem {N : ℕ} [NeZero N] (Γ : Finset (ZMod N)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (0 : ZMod N) ∈ bohr Γ ρ := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ 0, fun γ _ => ?_⟩
  simp only [mul_zero, ZMod.val_zero, Nat.cast_zero, zero_div, sub_zero]
  exact le_trans (min_le_left 0 1) hρ

private lemma bohr_card_pos {N : ℕ} [NeZero N] (Γ : Finset (ZMod N)) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    0 < (bohr Γ ρ).card :=
  Finset.card_pos.mpr ⟨0, bohr_zero_mem Γ hρ⟩

private lemma bohr_singleton_zero {N : ℕ} [NeZero N] {ρ : ℝ} (hρ : 0 ≤ ρ) :
    bohr ({0} : Finset (ZMod N)) ρ = Finset.univ := by
  ext x
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    forall_eq, zero_mul, ZMod.val_zero, Nat.cast_zero, zero_div, sub_zero, iff_true]
  exact le_trans (min_le_left 0 1) hρ

private lemma isRegularBohr_singleton_zero {N : ℕ} [NeZero N] :
    IsRegularBohr ({0} : Finset (ZMod N)) 1 := by
  refine ⟨Finset.singleton_nonempty 0, zero_lt_one, le_rfl, fun ε hε => ?_⟩
  simp only [Finset.card_singleton, Nat.cast_one, mul_one] at hε ⊢
  have h1e : 0 ≤ 1 + ε := by
    have hle : |ε| ≤ 1 / 100 := by simpa [one_div] using hε
    have hab := abs_le.mp hle
    linarith
  rw [bohr_singleton_zero (by norm_num : (0 : ℝ) ≤ 1), bohr_singleton_zero h1e]
  have hnn : (0 : ℝ) ≤ ((Finset.univ : Finset (ZMod N)).card : ℝ) := Nat.cast_nonneg _
  have habs : 0 ≤ 100 * |ε| := by positivity
  constructor <;> nlinarith

private lemma bohr_image_two_mem {N : ℕ} [NeZero N] (Γ : Finset (ZMod N)) (ρ : ℝ) (x : ZMod N) :
    x ∈ bohr (Γ.image (2 * ·)) ρ ↔ (2 : ZMod N) * x ∈ bohr Γ ρ := by
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor <;> intro h γ hγ
  · simpa only [mul_comm (2 : ZMod N) γ, mul_assoc] using h γ hγ
  · simpa only [mul_comm (2 : ZMod N) γ, mul_assoc] using h γ hγ

private lemma bohr_image_two_card {N : ℕ} [NeZero N] (hodd : Odd N) (Γ : Finset (ZMod N)) (ρ : ℝ) :
    (bohr (Γ.image (2 * ·)) ρ).card = (bohr Γ ρ).card := by
  refine Finset.card_bij (fun x _ => (2 : ZMod N) * x) ?_ ?_ ?_
  · intro x hx; exact (bohr_image_two_mem Γ ρ x).mp hx
  · intro x₁ _ x₂ _ h; exact mul_two_injective hodd h
  · intro y hy
    refine ⟨inv2 N * y, ?_, by rw [← mul_assoc, two_mul_inv2 hodd, one_mul]⟩
    rw [bohr_image_two_mem, ← mul_assoc, two_mul_inv2 hodd, one_mul]
    exact hy

private lemma isRegularBohr_image_two {N : ℕ} [NeZero N] (hodd : Odd N)
    {Γ : Finset (ZMod N)} {ρ : ℝ} (hreg : IsRegularBohr Γ ρ) :
    IsRegularBohr (Γ.image (2 * ·)) ρ := by
  obtain ⟨hne, hρ0, hρ1, hreg'⟩ := hreg
  have hcard : (Γ.image (2 * ·)).card = Γ.card :=
    Finset.card_image_of_injective Γ (mul_two_injective hodd)
  refine ⟨hne.image _, hρ0, hρ1, fun ε hε => ?_⟩
  rw [hcard] at hε ⊢
  rw [bohr_image_two_card hodd, bohr_image_two_card hodd]
  exact hreg' ε hε

/- ### Step 2: Elementary real-analysis helpers -/

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ log 2 := by
  have hsq : exp (1 / 2 : ℝ) ^ 2 = exp 1 := by
    rw [sq, ← exp_add]; norm_num
  have hlt : exp (1 / 2 : ℝ) < 2 := by
    have h1 : exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
    nlinarith [exp_pos (1 / 2 : ℝ)]
  have hlog := Real.log_le_log (exp_pos _) hlt.le
  rwa [Real.log_exp] at hlog

private lemma half_le_log_one_add {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    u / 2 ≤ log (1 + u) := by
  have hpos : 0 < 1 + u := by linarith
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hinv
  have h1 : u / (1 + u) ≤ log (1 + u) := by
    have heq : 1 - (1 + u)⁻¹ = u / (1 + u) := by field_simp [hpos.ne']; ring
    linarith
  have h2 : u / 2 ≤ u / (1 + u) := by
    rw [div_le_div_iff₀ (by norm_num) hpos]
    nlinarith
  exact h2.trans h1

/- ### Step 3: Translation invariance and degenerate-tuple bound for $k$-configurations -/

private lemma kconfig_count_translate {N k : ℕ} [NeZero N] (A : Finset (ZMod N)) (s : ZMod N) :
    (univ.filter fun x : Fin k → ZMod N =>
      ∀ i j : Fin k, x i + x j ∈ (A.image (· - s)).image (2 * ·)).card ≤
    (univ.filter fun x : Fin k → ZMod N =>
      ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)).card := by
  refine Finset.card_le_card_of_injOn (fun x i => x i + s) ?_ ?_
  · intro x hx
    have hcond := (Finset.mem_filter.mp hx).2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i j => ?_⟩)
    obtain ⟨b, hb, h2b⟩ := Finset.mem_image.mp (hcond i j)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨a, ha, ?_⟩
    calc (2 : ZMod N) * a = 2 * (a - s) + 2 * s := by ring
      _ = (x i + x j) + 2 * s := by rw [h2b]
      _ = (x i + s) + (x j + s) := by ring
  · intro x₁ _ x₂ _ h
    funext i
    exact add_right_cancel (congrFun h i)

private lemma degenerate_tuples_card_le {N k : ℕ} [NeZero N] (hk : 2 ≤ k) :
    (univ.filter fun x : Fin k → ZMod N => ¬ Function.Injective x).card ≤
      k ^ 2 * N ^ (k - 1) := by
  let Pairs : Finset (Fin k × Fin k) := univ.filter fun p => p.1 ≠ p.2
  have hsub : (univ.filter fun x : Fin k → ZMod N => ¬ Function.Injective x) ⊆
      Pairs.biUnion fun p => univ.filter fun x : Fin k → ZMod N => x p.1 = x p.2 := by
    intro x hx
    have hnot := (Finset.mem_filter.mp hx).2
    unfold Function.Injective at hnot
    push Not at hnot
    obtain ⟨i, j, hij, hne⟩ := hnot
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  have hpair_card : ∀ p ∈ Pairs,
      (univ.filter fun x : Fin k → ZMod N => x p.1 = x p.2).card ≤ N ^ (k - 1) := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    let Rest : Type := {m : Fin k // m ≠ p.2} → ZMod N
    have hcard_rest : Fintype.card Rest = N ^ (k - 1) := by
      dsimp [Rest]
      rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
        Fintype.card_fin]
    have hinj : (univ.filter fun x : Fin k → ZMod N => x p.1 = x p.2).card ≤
        (univ : Finset Rest).card := by
      refine Finset.card_le_card_of_injOn (fun x m => x m.1)
        (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_
      intro x₁ hx₁ x₂ hx₂ heq
      have h1 := (Finset.mem_filter.mp hx₁).2
      have h2 := (Finset.mem_filter.mp hx₂).2
      funext m
      by_cases hm : m = p.2
      · subst hm
        rw [← h1, ← h2]
        exact congrFun heq ⟨p.1, hne⟩
      · exact congrFun heq ⟨m, hm⟩
    rwa [Finset.card_univ, hcard_rest] at hinj
  have hPairs_le : Pairs.card ≤ k ^ 2 := by
    calc Pairs.card ≤ (univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
      _ = k ^ 2 := by simp [sq]
  have _ := hk
  calc (univ.filter fun x : Fin k → ZMod N => ¬ Function.Injective x).card
      ≤ (Pairs.biUnion fun p => univ.filter fun x : Fin k → ZMod N => x p.1 = x p.2).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ p ∈ Pairs, (univ.filter fun x : Fin k → ZMod N => x p.1 = x p.2).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ Pairs, N ^ (k - 1) := Finset.sum_le_sum hpair_card
    _ = Pairs.card * N ^ (k - 1) := by simp
    _ ≤ k ^ 2 * N ^ (k - 1) := Nat.mul_le_mul_right _ hPairs_le

/- ### Step 4: Pilatte's quadratic rank bound and maximal-chain density-increment machinery -/

private structure BohrChain {N : ℕ} [NeZero N] (c K : ℝ) (k : ℕ) (A : Finset (ZMod N)) (t : ℕ) where
  Γ : Fin (t + 1) → Finset (ZMod N)
  ρ : Fin (t + 1) → ℝ
  Aset : Fin (t + 1) → Finset (ZMod N)
  Δ : Fin (t + 1) → Finset (ZMod N)
  shift : Fin (t + 1) → ZMod N
  hΓ0 : Γ 0 = {0}
  hρ0 : ρ 0 = 1
  hA0 : Aset 0 = A
  hΔ0 : Δ 0 = {0}
  hshift0 : shift 0 = 0
  hreg : ∀ s : Fin (t + 1), IsRegularBohr (Γ s) (ρ s)
  hAsub : ∀ s : Fin (t + 1), Aset s ⊆ bohr (Γ s) (ρ s)
  hAshift : ∀ s : Fin (t + 1), Aset s ⊆ A.image (· - shift s)
  hAne : ∀ s : Fin (t + 1), (Aset s).Nonempty
  hstep : ∀ s : Fin t,
    let αprev : ℝ := ((Aset s.castSucc).card : ℝ) / ((bohr (Γ s.castSucc) (ρ s.castSucc)).card : ℝ)
    let dprev : ℕ := (Γ s.castSucc).card
    (∃ σ : Bool, Γ s.succ = Γ s.castSucc ∪ (Γ s.castSucc).image (if σ then (2 * ·) else (inv2 N * ·)) ∪ Δ s.succ) ∧
    ((Δ s.succ).card : ℝ) ≤ K * (k : ℝ) ^ 46 * (log (2 / αprev)) ^ 11 ∧
    ρ s.castSucc * exp (-K * ((k : ℝ) * log (2 * (dprev : ℝ) / αprev) +
        (k : ℝ) ^ 6 * (log (2 / αprev)) ^ 2)) ≤ ρ s.succ ∧
    (1 + c * (k : ℝ) ^ (-5 : ℤ)) * αprev ≤
      ((Aset s.succ).card : ℝ) / ((bohr (Γ s.succ) (ρ s.succ)).card : ℝ)

private lemma chain_density_ge {N : ℕ} [NeZero N] {c K : ℝ} (hc0 : 0 < c) {k : ℕ} (hk : 2 ≤ k)
    {A : Finset (ZMod N)} {t : ℕ} (ch : BohrChain c K k A t) :
    ∀ s : Fin (t + 1),
      (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ s.1 * ((A.card : ℝ) / (N : ℝ)) ≤
        ((ch.Aset s).card : ℝ) / ((bohr (ch.Γ s) (ch.ρ s)).card : ℝ) := by
  have _ := hk
  intro ⟨m, hm⟩
  induction m with
  | zero =>
    simp only [pow_zero, one_mul]
    have h0 : (⟨0, hm⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
    rw [h0, ch.hA0, ch.hΓ0, ch.hρ0, bohr_singleton_zero (by norm_num : (0 : ℝ) ≤ 1),
      Finset.card_univ, ZMod.card]
  | succ m ih =>
    have hm' : m < t := by omega
    have hih := ih (by omega)
    let sm : Fin t := ⟨m, hm'⟩
    have hcast : sm.castSucc = ⟨m, by omega⟩ := rfl
    have hsucc : sm.succ = ⟨m + 1, hm⟩ := rfl
    have hst := (ch.hstep sm).2.2.2
    rw [hcast, hsucc] at hst
    have hfac_nn : 0 ≤ 1 + c * (k : ℝ) ^ (-5 : ℤ) := by positivity
    calc (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ (m + 1) * ((A.card : ℝ) / (N : ℝ))
        = (1 + c * (k : ℝ) ^ (-5 : ℤ)) *
            ((1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ m * ((A.card : ℝ) / (N : ℝ))) := by rw [pow_succ']; ring
      _ ≤ (1 + c * (k : ℝ) ^ (-5 : ℤ)) *
            (((ch.Aset ⟨m, by omega⟩).card : ℝ) / ((bohr (ch.Γ ⟨m, by omega⟩) (ch.ρ ⟨m, by omega⟩)).card : ℝ)) :=
          mul_le_mul_of_nonneg_left hih hfac_nn
      _ ≤ ((ch.Aset ⟨m + 1, hm⟩).card : ℝ) / ((bohr (ch.Γ ⟨m + 1, hm⟩) (ch.ρ ⟨m + 1, hm⟩)).card : ℝ) := hst

private lemma chain_length_le {N : ℕ} [NeZero N] {c K : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {k : ℕ} (hk : 2 ≤ k) {A : Finset (ZMod N)} (hA_ne : A.Nonempty)
    {t : ℕ} (ch : BohrChain c K k A t) :
    (t : ℝ) ≤ (2 / c) * (k : ℝ) ^ 5 * log (2 * (N : ℝ) / (A.card : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA_ne.card_pos
  have hlast := chain_density_ge hc0 hk ch (Fin.last t)
  have hBpos : (0 : ℝ) < ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ) := by
    exact_mod_cast bohr_card_pos _ (ch.hreg (Fin.last t)).2.1.le
  have hle1 : ((ch.Aset (Fin.last t)).card : ℝ) /
      ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ) ≤ 1 := by
    rw [div_le_one hBpos]
    exact_mod_cast Finset.card_le_card (ch.hAsub (Fin.last t))
  have hprod : (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ t * ((A.card : ℝ) / (N : ℝ)) ≤ 1 :=
    hlast.trans hle1
  have hu0 : 0 ≤ c * (k : ℝ) ^ (-5 : ℤ) := by positivity
  have hu1 : c * (k : ℝ) ^ (-5 : ℤ) ≤ 1 := by
    have hk5 : (1 : ℝ) ≤ (k : ℝ) ^ 5 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
    have hinv : (k : ℝ) ^ (-5 : ℤ) ≤ 1 := by
      rw [zpow_neg]
      exact inv_le_one_of_one_le₀ hk5
    nlinarith
  have hlog_step : (c * (k : ℝ) ^ (-5 : ℤ)) / 2 ≤ log (1 + c * (k : ℝ) ^ (-5 : ℤ)) :=
    half_le_log_one_add hu0 hu1
  have hpow_le : (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ t ≤ (N : ℝ) / (A.card : ℝ) := by
    rw [le_div_iff₀ hApos]
    have h1 := mul_le_mul_of_nonneg_right hprod hNpos.le
    rw [mul_assoc, div_mul_cancel₀ _ hNpos.ne', one_mul] at h1
    exact h1
  have hpow_pos : 0 < (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ t := by positivity
  have hlog_pow : (t : ℝ) * ((c * (k : ℝ) ^ (-5 : ℤ)) / 2) ≤ log (2 * (N : ℝ) / (A.card : ℝ)) := by
    calc (t : ℝ) * ((c * (k : ℝ) ^ (-5 : ℤ)) / 2)
        ≤ (t : ℝ) * log (1 + c * (k : ℝ) ^ (-5 : ℤ)) :=
          mul_le_mul_of_nonneg_left hlog_step (Nat.cast_nonneg t)
      _ = log ((1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ t) := (Real.log_pow _ t).symm
      _ ≤ log ((N : ℝ) / (A.card : ℝ)) := Real.log_le_log hpow_pos hpow_le
      _ ≤ log (2 * (N : ℝ) / (A.card : ℝ)) :=
          Real.log_le_log (div_pos hNpos hApos) (by
            rw [div_le_div_iff_of_pos_right hApos]; linarith)
  have hmul_inv : ((2 / c) * (k : ℝ) ^ 5) * ((c * (k : ℝ) ^ (-5 : ℤ)) / 2) = 1 := by
    rw [zpow_neg]
    have hk5ne : ((k : ℝ) ^ 5) ≠ 0 := by positivity
    field_simp [hc0.ne', hk5ne]
  have h := mul_le_mul_of_nonneg_left hlog_pow (show 0 ≤ (2 / c) * (k : ℝ) ^ 5 by positivity)
  have hL : ((2 / c) * (k : ℝ) ^ 5) * ((t : ℝ) * ((c * (k : ℝ) ^ (-5 : ℤ)) / 2)) = (t : ℝ) := by
    calc ((2 / c) * (k : ℝ) ^ 5) * ((t : ℝ) * ((c * (k : ℝ) ^ (-5 : ℤ)) / 2))
        = (t : ℝ) * (((2 / c) * (k : ℝ) ^ 5) * ((c * (k : ℝ) ^ (-5 : ℤ)) / 2)) := by ring
      _ = (t : ℝ) := by rw [hmul_inv, mul_one]
  linarith

private lemma chain_gamma_mono {N : ℕ} [NeZero N] {c K : ℝ} {k : ℕ} {A : Finset (ZMod N)}
    {t : ℕ} (ch : BohrChain c K k A t) {i j : Fin (t + 1)} (hij : i ≤ j) :
    ch.Γ i ⊆ ch.Γ j := by
  obtain ⟨a, ha⟩ := i
  obtain ⟨b, hb⟩ := j
  have hab : a ≤ b := hij
  clear hij
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ m hma ih =>
    have hm : m < t := by omega
    have hsub1 : ch.Γ ⟨a, ha⟩ ⊆ ch.Γ ⟨m, by omega⟩ := ih (by omega)
    obtain ⟨σ, hσ⟩ := (ch.hstep ⟨m, hm⟩).1
    have hsub2 : ch.Γ ⟨m, by omega⟩ ⊆ ch.Γ ⟨m + 1, hb⟩ := by
      change ch.Γ (⟨m, hm⟩ : Fin t).castSucc ⊆ ch.Γ (⟨m, hm⟩ : Fin t).succ
      rw [hσ]
      exact Finset.subset_union_left.trans Finset.subset_union_left
    exact hsub1.trans hsub2

private lemma pilatte_freq_inclusion {N : ℕ} [NeZero N] (hodd : Odd N)
    {c K : ℝ} {k : ℕ} {A : Finset (ZMod N)} {t : ℕ} (ch : BohrChain c K k A t) :
    ∀ s : Fin (t + 1),
      ch.Γ s ⊆ (Finset.range (s.1 + 1)).biUnion fun r =>
        (Finset.Icc (-(s.1 : ℤ)) (s.1 : ℤ)).biUnion fun a =>
          if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).image (fun γ => pow2 N a * γ) else ∅ := by
  intro ⟨m, hm⟩
  induction m with
  | zero =>
    intro γ hγ
    have h0 : (⟨0, hm⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
    rw [h0, ch.hΓ0, Finset.mem_singleton] at hγ
    subst hγ
    refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rw [dif_pos hm]
    refine Finset.mem_image.mpr ⟨0, ?_, by simp [pow2_zero]⟩
    rw [h0, ch.hΔ0]; exact Finset.mem_singleton_self 0
  | succ m ih =>
    dsimp only
    have hm' : m < t := by omega
    let sm : Fin t := ⟨m, hm'⟩
    obtain ⟨σ, hσ⟩ := (ch.hstep sm).1
    intro γ hγ
    change γ ∈ ch.Γ sm.succ at hγ
    rw [hσ] at hγ
    rcases Finset.mem_union.mp hγ with hleft | hΔ
    · rcases Finset.mem_union.mp hleft with hprev | himg
      · have hmem := ih (by omega) hprev
        dsimp only at hmem
        obtain ⟨r, hr, hmem1⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨a, ha, hmem2⟩ := Finset.mem_biUnion.mp hmem1
        have ha' := Finset.mem_Icc.mp ha
        refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega), ?_⟩
        refine Finset.mem_biUnion.mpr ⟨a, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hmem2⟩
      · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp himg
        have hmem := ih (by omega) hu
        dsimp only at hmem
        obtain ⟨r, hr, hmem1⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨a, ha, hmem2⟩ := Finset.mem_biUnion.mp hmem1
        have ha' := Finset.mem_Icc.mp ha
        have hr_lt : r < t + 1 := by have := Finset.mem_range.mp hr; omega
        rw [dif_pos hr_lt] at hmem2
        obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp hmem2
        cases σ
        · refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega), ?_⟩
          refine Finset.mem_biUnion.mpr ⟨a - 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [dif_pos hr_lt]
          refine Finset.mem_image.mpr ⟨δ, hδ, ?_⟩
          simp only [Bool.false_eq_true, ↓reduceIte, ← mul_assoc, inv2_mul_pow2 hodd]
        · refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_range.mpr (by have := Finset.mem_range.mp hr; omega), ?_⟩
          refine Finset.mem_biUnion.mpr ⟨a + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [dif_pos hr_lt]
          refine Finset.mem_image.mpr ⟨δ, hδ, ?_⟩
          simp only [↓reduceIte, ← mul_assoc, two_mul_pow2 hodd]
    · refine Finset.mem_biUnion.mpr ⟨m + 1, Finset.mem_range.mpr (by omega), ?_⟩
      refine Finset.mem_biUnion.mpr ⟨0, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      rw [dif_pos hm]
      exact Finset.mem_image.mpr ⟨γ, hΔ, by rw [pow2_zero, one_mul]⟩

private lemma pilatte_rank_bound {N : ℕ} [NeZero N] (hodd : Odd N)
    {c K : ℝ} (hc0 : 0 < c) (hK1 : 1 ≤ K) {k : ℕ} (hk : 2 ≤ k)
    {A : Finset (ZMod N)} (hA_ne : A.Nonempty)
    {t : ℕ} (ch : BohrChain c K k A t) :
    ((ch.Γ (Fin.last t)).card : ℝ) ≤
      ((t : ℝ) + 1) * (2 * (t : ℝ) + 1) * (K * (k : ℝ) ^ 46 * (log (2 * (N : ℝ) / (A.card : ℝ))) ^ 11) := by
  set L : ℝ := log (2 * (N : ℝ) / (A.card : ℝ))
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA_ne.card_pos
  have hAleN : (A.card : ℝ) ≤ (N : ℝ) := by
    have : A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    rw [ZMod.card] at this
    exact_mod_cast this
  have hL_ge : (1 / 2 : ℝ) ≤ L := by
    have h2 : (2 : ℝ) ≤ 2 * (N : ℝ) / (A.card : ℝ) := by
      rw [le_div_iff₀ hApos]; linarith
    exact half_le_log_two.trans (Real.log_le_log (by norm_num) h2)
  have hΔ_bd : ∀ r : Fin (t + 1), ((ch.Δ r).card : ℝ) ≤ K * (k : ℝ) ^ 46 * L ^ 11 := by
    intro ⟨r, hr⟩
    cases r with
    | zero =>
      have h0 : (⟨0, hr⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
      rw [h0, ch.hΔ0, Finset.card_singleton, Nat.cast_one]
      have hk46 : (2 : ℝ) ^ 46 ≤ (k : ℝ) ^ 46 :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hk) 46
      have hL11 : (1 / 2 : ℝ) ^ 11 ≤ L ^ 11 := pow_le_pow_left₀ (by norm_num) hL_ge 11
      have hprod : (1 : ℝ) ≤ (2 : ℝ) ^ 46 * (1 / 2 : ℝ) ^ 11 := by norm_num
      have hprod2 : (2 : ℝ) ^ 46 * (1 / 2 : ℝ) ^ 11 ≤ (k : ℝ) ^ 46 * L ^ 11 :=
        mul_le_mul hk46 hL11 (by positivity) (by positivity)
      nlinarith
    | succ m =>
      let sm : Fin t := ⟨m, by omega⟩
      have hst := (ch.hstep sm).2.1
      have hα_ge : (A.card : ℝ) / (N : ℝ) ≤
          ((ch.Aset sm.castSucc).card : ℝ) / ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) := by
        have hg := chain_density_ge hc0 hk ch sm.castSucc
        have hpow1 : (1 : ℝ) ≤ (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ sm.castSucc.1 :=
          one_le_pow₀ (by linarith [show 0 ≤ c * (k : ℝ) ^ (-5 : ℤ) by positivity])
        have hα0_nn : 0 ≤ (A.card : ℝ) / (N : ℝ) := by positivity
        nlinarith
      have hαprev_pos : 0 < ((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) :=
        lt_of_lt_of_le (div_pos hApos hNpos) hα_ge
      have hlog_le : log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) ≤ L := by
        have hdiv : 2 / (((ch.Aset sm.castSucc).card : ℝ) /
            ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ)) ≤ 2 * (N : ℝ) / (A.card : ℝ) := by
          rw [show 2 * (N : ℝ) / (A.card : ℝ) = 2 / ((A.card : ℝ) / (N : ℝ)) by field_simp [hApos.ne', hNpos.ne']]
          exact div_le_div_of_nonneg_left (by norm_num) (div_pos hApos hNpos) hα_ge
        exact Real.log_le_log (div_pos (by norm_num) hαprev_pos) hdiv
      have hlog_nn : 0 ≤ log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) := by
        apply Real.log_nonneg
        rw [one_le_div hαprev_pos]
        have hBpos : (0 : ℝ) < ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) := by
          exact_mod_cast bohr_card_pos _ (ch.hreg sm.castSucc).2.1.le
        have hle1 : ((ch.Aset sm.castSucc).card : ℝ) /
            ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) ≤ 1 := by
          rw [div_le_one hBpos]
          exact_mod_cast Finset.card_le_card (ch.hAsub sm.castSucc)
        linarith
      have hpow11 : (log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ)))) ^ 11 ≤ L ^ 11 :=
        pow_le_pow_left₀ hlog_nn hlog_le 11
      have hmul := mul_le_mul_of_nonneg_left hpow11 (show 0 ≤ K * (k : ℝ) ^ 46 by positivity)
      exact hst.trans (by linarith)
  have hinc := pilatte_freq_inclusion hodd ch (Fin.last t)
  have hcard_nat : (ch.Γ (Fin.last t)).card ≤
      ∑ r ∈ Finset.range (t + 1), ∑ _a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
        if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).card else 0 := by
    calc (ch.Γ (Fin.last t)).card
        ≤ ((Finset.range (t + 1)).biUnion fun r =>
            (Finset.Icc (-(t : ℤ)) (t : ℤ)).biUnion fun a =>
              if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).image (fun γ => pow2 N a * γ) else ∅).card :=
          Finset.card_le_card hinc
      _ ≤ ∑ r ∈ Finset.range (t + 1),
            ((Finset.Icc (-(t : ℤ)) (t : ℤ)).biUnion fun a =>
              if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).image (fun γ => pow2 N a * γ) else ∅).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Finset.range (t + 1), ∑ a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
            (if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).image (fun γ => pow2 N a * γ) else ∅).card :=
          Finset.sum_le_sum fun r _ => Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Finset.range (t + 1), ∑ _a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
            if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).card else 0 := by
          refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun a _ => ?_
          split_ifs
          · exact Finset.card_image_le
          · exact le_rfl
  have hcard_R : ((ch.Γ (Fin.last t)).card : ℝ) ≤
      ∑ r ∈ Finset.range (t + 1), ∑ _a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
        (if hr : r < t + 1 then ((ch.Δ ⟨r, hr⟩).card : ℝ) else 0) := by
    have h1 : ((ch.Γ (Fin.last t)).card : ℝ) ≤
        ((∑ r ∈ Finset.range (t + 1), ∑ _a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
          if hr : r < t + 1 then (ch.Δ ⟨r, hr⟩).card else 0 : ℕ) : ℝ) := by
      exact_mod_cast hcard_nat
    refine h1.trans (le_of_eq ?_)
    push_cast
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun _ _ => ?_
    split_ifs <;> simp
  have hIcc_card : (Finset.Icc (-(t : ℤ)) (t : ℤ)).card = 2 * t + 1 := by
    rw [Int.card_Icc]; omega
  calc ((ch.Γ (Fin.last t)).card : ℝ)
      ≤ ∑ r ∈ Finset.range (t + 1), ∑ _a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
          (if hr : r < t + 1 then ((ch.Δ ⟨r, hr⟩).card : ℝ) else 0) := hcard_R
    _ ≤ ∑ _r ∈ Finset.range (t + 1), ∑ _a ∈ Finset.Icc (-(t : ℤ)) (t : ℤ),
          (K * (k : ℝ) ^ 46 * L ^ 11) := by
        refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun _ _ => ?_
        split_ifs with hr
        · exact hΔ_bd ⟨r, hr⟩
        · positivity
    _ = ((t : ℝ) + 1) * (2 * (t : ℝ) + 1) * (K * (k : ℝ) ^ 46 * L ^ 11) := by
        simp only [Finset.sum_const, Finset.card_range, hIcc_card, nsmul_eq_mul]
        push_cast; ring

private lemma chain_width_lower {N : ℕ} [NeZero N] {c K : ℝ} (hc0 : 0 < c) (hK1 : 1 ≤ K)
    {k : ℕ} (hk : 2 ≤ k) {A : Finset (ZMod N)} (hA_ne : A.Nonempty)
    {t : ℕ} (ch : BohrChain c K k A t) :
    let dmax : ℕ := (ch.Γ (Fin.last t)).card
    let L : ℝ := log (2 * (N : ℝ) / (A.card : ℝ))
    exp (-(t : ℝ) * K * ((k : ℝ) * log (2 * (dmax : ℝ) * (N : ℝ) / (A.card : ℝ)) +
        (k : ℝ) ^ 6 * L ^ 2)) ≤ ch.ρ (Fin.last t) := by
  intro dmax L
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA_ne.card_pos
  have hα0_pos : 0 < (A.card : ℝ) / (N : ℝ) := div_pos hApos hNpos
  set E : ℝ := K * ((k : ℝ) * log (2 * (dmax : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2)
  suffices ∀ s : Fin (t + 1), exp (-(s.1 : ℝ) * E) ≤ ch.ρ s by
    simpa [E, mul_assoc] using this (Fin.last t)
  intro ⟨m, hm⟩
  induction m with
  | zero =>
    have h0 : (⟨0, hm⟩ : Fin (t + 1)) = 0 := Fin.ext rfl
    rw [h0, ch.hρ0]; simp
  | succ m ih =>
    have hm' : m < t := by omega
    let sm : Fin t := ⟨m, hm'⟩
    have hih := ih (by omega)
    have hst := (ch.hstep sm).2.2.1
    have hα_ge : (A.card : ℝ) / (N : ℝ) ≤
        ((ch.Aset sm.castSucc).card : ℝ) / ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) := by
      have hg := chain_density_ge hc0 hk ch sm.castSucc
      have hpow1 : (1 : ℝ) ≤ (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ sm.castSucc.1 :=
        one_le_pow₀ (by linarith [show 0 ≤ c * (k : ℝ) ^ (-5 : ℤ) by positivity])
      nlinarith
    have hαprev_pos : 0 < ((ch.Aset sm.castSucc).card : ℝ) /
        ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) :=
      lt_of_lt_of_le hα0_pos hα_ge
    have hd_le : (ch.Γ sm.castSucc).card ≤ dmax :=
      Finset.card_le_card (chain_gamma_mono ch (Fin.le_last _))
    have hd_pos : 1 ≤ (ch.Γ sm.castSucc).card := Finset.card_pos.mpr (ch.hreg sm.castSucc).1
    have hlog1 : log (2 * ((ch.Γ sm.castSucc).card : ℝ) /
        (((ch.Aset sm.castSucc).card : ℝ) / ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) ≤
        log (2 * (dmax : ℝ) * (N : ℝ) / (A.card : ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [show 2 * (dmax : ℝ) * (N : ℝ) / (A.card : ℝ) = (2 * (dmax : ℝ)) / ((A.card : ℝ) / (N : ℝ)) by
        field_simp [hApos.ne', hNpos.ne']]
      have hnum : 2 * ((ch.Γ sm.castSucc).card : ℝ) ≤ 2 * (dmax : ℝ) := by
        have : ((ch.Γ sm.castSucc).card : ℝ) ≤ (dmax : ℝ) := by exact_mod_cast hd_le
        linarith
      exact (div_le_div_of_nonneg_right hnum hαprev_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) hα0_pos hα_ge)
    have hlog2 : log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
        ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) ≤ L := by
      apply Real.log_le_log (by positivity)
      rw [show 2 * (N : ℝ) / (A.card : ℝ) = 2 / ((A.card : ℝ) / (N : ℝ)) by
        field_simp [hApos.ne', hNpos.ne']]
      exact div_le_div_of_nonneg_left (by norm_num) hα0_pos hα_ge
    have hlog2_nn : 0 ≤ log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
        ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) := by
      apply Real.log_nonneg
      rw [one_le_div hαprev_pos]
      have hBpos : (0 : ℝ) < ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) := by
        exact_mod_cast bohr_card_pos _ (ch.hreg sm.castSucc).2.1.le
      have hle1 : ((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ) ≤ 1 := by
        rw [div_le_one hBpos]
        exact_mod_cast Finset.card_le_card (ch.hAsub sm.castSucc)
      linarith
    have hE_le : K * ((k : ℝ) * log (2 * ((ch.Γ sm.castSucc).card : ℝ) /
        (((ch.Aset sm.castSucc).card : ℝ) / ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) +
        (k : ℝ) ^ 6 * (log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ)))) ^ 2) ≤ E := by
      dsimp [E]
      have hsq : (log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ)))) ^ 2 ≤ L ^ 2 :=
        pow_le_pow_left₀ hlog2_nn hlog2 2
      have h1 : (k : ℝ) * log (2 * ((ch.Γ sm.castSucc).card : ℝ) /
          (((ch.Aset sm.castSucc).card : ℝ) / ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) ≤
          (k : ℝ) * log (2 * (dmax : ℝ) * (N : ℝ) / (A.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg k)
      have h2 : (k : ℝ) ^ 6 * (log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
          ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ)))) ^ 2 ≤ (k : ℝ) ^ 6 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by linarith)
    have hstep_exp : exp (-(↑(m + 1) : ℝ) * E) = exp (-(m : ℝ) * E) * exp (-E) := by
      rw [← exp_add]; push_cast; ring_nf
    calc exp (-(↑(m + 1) : ℝ) * E)
        = exp (-(m : ℝ) * E) * exp (-E) := hstep_exp
      _ ≤ ch.ρ sm.castSucc * exp (-K * ((k : ℝ) * log (2 * ((ch.Γ sm.castSucc).card : ℝ) /
            (((ch.Aset sm.castSucc).card : ℝ) / ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ))) +
            (k : ℝ) ^ 6 * (log (2 / (((ch.Aset sm.castSucc).card : ℝ) /
              ((bohr (ch.Γ sm.castSucc) (ch.ρ sm.castSucc)).card : ℝ)))) ^ 2)) := by
          refine mul_le_mul hih (Real.exp_le_exp.mpr (by linarith)) (exp_pos _).le (ch.hreg sm.castSucc).2.1.le
      _ ≤ ch.ρ sm.succ := hst

private noncomputable def extendChain {N : ℕ} [NeZero N] {c K : ℝ} {k : ℕ} {A : Finset (ZMod N)} {t : ℕ}
    (ch : BohrChain c K k A t)
    (σ : Bool) (Δ_new : Finset (ZMod N)) (ρ_new : ℝ) (x : ZMod N)
    (hreg_new : IsRegularBohr (ch.Γ (Fin.last t) ∪
      (ch.Γ (Fin.last t)).image (if σ then (2 * ·) else (inv2 N * ·)) ∪ Δ_new) ρ_new)
    (hΔ_new : (Δ_new.card : ℝ) ≤ K * (k : ℝ) ^ 46 *
      (log (2 / (((ch.Aset (Fin.last t)).card : ℝ) /
        ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ)))) ^ 11)
    (hρ_new : ch.ρ (Fin.last t) * exp (-K * ((k : ℝ) * log (2 * ((ch.Γ (Fin.last t)).card : ℝ) /
        (((ch.Aset (Fin.last t)).card : ℝ) / ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ))) +
        (k : ℝ) ^ 6 * (log (2 / (((ch.Aset (Fin.last t)).card : ℝ) /
          ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ)))) ^ 2)) ≤ ρ_new)
    (hdens_new : (1 + c * (k : ℝ) ^ (-5 : ℤ)) *
        (((ch.Aset (Fin.last t)).card : ℝ) / ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ)) ≤
      ((((ch.Aset (Fin.last t)).image (· - x)) ∩ bohr (ch.Γ (Fin.last t) ∪
        (ch.Γ (Fin.last t)).image (if σ then (2 * ·) else (inv2 N * ·)) ∪ Δ_new) ρ_new).card : ℝ) /
        ((bohr (ch.Γ (Fin.last t) ∪
          (ch.Γ (Fin.last t)).image (if σ then (2 * ·) else (inv2 N * ·)) ∪ Δ_new) ρ_new).card : ℝ))
    (hc0 : 0 < c) :
    BohrChain c K k A (t + 1) := by
  let Γ_new := ch.Γ (Fin.last t) ∪
    (ch.Γ (Fin.last t)).image (if σ then (2 * ·) else (inv2 N * ·)) ∪ Δ_new
  let A_new := ((ch.Aset (Fin.last t)).image (· - x)) ∩ bohr Γ_new ρ_new
  refine
    { Γ := Fin.snoc ch.Γ Γ_new
      ρ := Fin.snoc ch.ρ ρ_new
      Aset := Fin.snoc ch.Aset A_new
      Δ := Fin.snoc ch.Δ Δ_new
      shift := Fin.snoc ch.shift (ch.shift (Fin.last t) + x)
      hΓ0 := by rw [← Fin.castSucc_zero, Fin.snoc_castSucc, ch.hΓ0]
      hρ0 := by rw [← Fin.castSucc_zero, Fin.snoc_castSucc, ch.hρ0]
      hA0 := by rw [← Fin.castSucc_zero, Fin.snoc_castSucc, ch.hA0]
      hΔ0 := by rw [← Fin.castSucc_zero, Fin.snoc_castSucc, ch.hΔ0]
      hshift0 := by rw [← Fin.castSucc_zero, Fin.snoc_castSucc, ch.hshift0]
      hreg := fun s => Fin.lastCases (by simpa only [Fin.snoc_last] using hreg_new)
        (fun i => by simpa only [Fin.snoc_castSucc] using ch.hreg i) s
      hAsub := fun s => Fin.lastCases (by simpa only [Fin.snoc_last] using Finset.inter_subset_right)
        (fun i => by simpa only [Fin.snoc_castSucc] using ch.hAsub i) s
      hAshift := fun s => Fin.lastCases (by
        simp only [Fin.snoc_last]
        intro w hw
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hw).1
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (ch.hAshift (Fin.last t) hu)
        exact Finset.mem_image.mpr ⟨a, ha, by ring⟩)
        (fun i => by simpa only [Fin.snoc_castSucc] using ch.hAshift i) s
      hAne := fun s => Fin.lastCases (by
        simp only [Fin.snoc_last]
        have hBprev : (0 : ℝ) < ((bohr (ch.Γ (Fin.last t)) (ch.ρ (Fin.last t))).card : ℝ) := by
          exact_mod_cast bohr_card_pos _ (ch.hreg (Fin.last t)).2.1.le
        have hAprev : (0 : ℝ) < ((ch.Aset (Fin.last t)).card : ℝ) := by
          exact_mod_cast (ch.hAne (Fin.last t)).card_pos
        have hBnew : (0 : ℝ) < ((bohr Γ_new ρ_new).card : ℝ) := by
          exact_mod_cast bohr_card_pos _ hreg_new.2.1.le
        have hpos : (0 : ℝ) < (A_new.card : ℝ) / ((bohr Γ_new ρ_new).card : ℝ) :=
          lt_of_lt_of_le (by positivity) hdens_new
        have hcard_pos : 0 < (A_new.card : ℝ) := (div_pos_iff_of_pos_right hBnew).mp hpos
        exact Finset.card_pos.mp (by exact_mod_cast hcard_pos))
        (fun i => by simpa only [Fin.snoc_castSucc] using ch.hAne i) s
      hstep := fun s => Fin.lastCases (by
        simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
        exact ⟨⟨σ, rfl⟩, hΔ_new, hρ_new, hdens_new⟩)
        (fun i => by
          simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
          exact ch.hstep i) s }

/- ### Step 5: Self-contained hypotheses (Beker 2025 §3: Counting/Localization vs. Kelley–Meka) -/

/-- **Multi-scale regular Bohr localization & $k$-configuration counting dichotomy**
(Filmus–Hatami–Hosseini–Kelman 2024; Beker 2025, Theorem 2.1, Lemma 3.4 & §3.2). -/
def H1 : Prop :=
  ∀ s₀ : ℝ, 0 < s₀ → s₀ ≤ 1 → ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ c₁ ≤ 1 ∧ 1 ≤ C₁ ∧
  ∀ (N : ℕ) [NeZero N], Odd N → ∀ (k : ℕ), 2 ≤ k →
  let B (Γ : Finset (ZMod N)) (ρ : ℝ) := univ.filter fun x => ∀ γ ∈ Γ,
    min (((γ * x).val : ℝ) / N) (1 - ((γ * x).val : ℝ) / N) ≤ ρ
  let reg (Γ : Finset (ZMod N)) (ρ : ℝ) := Γ.Nonempty ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ ε : ℝ, |ε| ≤ (100 * (Γ.card : ℝ))⁻¹ →
      (1 - 100 * (Γ.card : ℝ) * |ε|) * (B Γ ρ).card ≤ (B Γ ((1 + ε) * ρ)).card ∧
      ((B Γ ((1 + ε) * ρ)).card : ℝ) ≤ (1 + 100 * (Γ.card : ℝ) * |ε|) * (B Γ ρ).card
  let μ (X Y : Finset (ZMod N)) : ℝ := (X.card : ℝ) / Y.card
  ∀ (Γ : Finset (ZMod N)) (ρ : ℝ), reg Γ ρ → ∀ A ⊆ B Γ ρ, A.Nonempty →
  let α := μ A (B Γ ρ)
  let d := Γ.card
  let i2 : ZMod N := ((N + 1) / 2 : ℕ)
  let Γ' := Γ ∪ Γ.image (i2 * ·)
  let r := ρ * exp (-C₁ * (k * log (2 * d / α) + (k : ℝ) ^ 6 * log (2 / α) ^ 2))
  (exp (-C₁ * k ^ 2 * log k * d * log (2 * d / α)) * ρ ^ (2 * k * d) * (N : ℝ) ^ k ≤
    (univ.filter fun x : Fin k → ZMod N => ∀ i j, x i + x j ∈ A.image (2 * ·)).card) ∨
  (∃ (σ : Bool) (ρ' : ℝ) (x : ZMod N),
    let G := Γ ∪ Γ.image (if σ then (2 * ·) else (i2 * ·))
    reg G ρ' ∧ r ≤ ρ' ∧ (1 + c₁ * (k : ℝ) ^ (-5 : ℤ)) * α ≤ μ (A.image (· - x) ∩ B G ρ') (B G ρ')) ∨
  (∃ (x : ZMod N) (ρ₁ ρ₂ : ℝ) (S T D : Finset (ZMod N)),
    let B₁ := B Γ' ρ₁; let B₂ := B Γ' ρ₂; let Ax := A.image (· - x)
    let k4 : ℝ := (k : ℝ) ^ (-4 : ℤ); let γ := c₁ / 1024 * k4; let μD := μ D B₂
    let cST : ℝ := (∑ s ∈ S, ∑ t ∈ T, if s + t ∈ D then (1 : ℝ) else 0) / ((S.card : ℝ) * T.card)
    let e := exp (-C₁ * (k : ℝ) ^ 6 * log (2 / α) ^ 2)
    reg Γ' ρ₁ ∧ reg Γ' ρ₂ ∧ r ≤ ρ₁ ∧ ρ₁ ≤ (s₀ * c₁ * α / ((k : ℝ) ^ 5 * d)) * ρ₂ ∧ ρ₂ ≤ ρ ∧
    S ⊆ B₁ ∧ S.Nonempty ∧ T ⊆ Ax ∩ B₂ ∧ T.Nonempty ∧ D ⊆ Ax.image (2 * ·) ∩ B₂ ∧ D.Nonempty ∧
    (1 - γ) * α ≤ μD ∧ μD ≤ (1 + γ) * α ∧
    ((e ≤ μ S B₁ ∧ e ≤ μ T B₂ ∧ μD + c₁ * k4 * α ≤ cST) ∨
     (exp (-C₁ * (k : ℝ) ^ 6 * log k * log (2 / α) ^ 2) ≤ μ S B₁ ∧
      (1 - γ) * α ≤ μ T B₂ ∧ c₁ * k4 * α ≤ |cST - μD|)))

/-- **Kelley–Meka / Bloom–Sisask local density increment on regular Bohr sets**
(Beker 2025, Propositions 3.3, 3.4 & Corollary 3.5). -/
def H2 : Prop :=
  ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧ ∀ c₀ C₀ : ℝ, 0 < c₀ → c₀ ≤ 1 → 1 ≤ C₀ →
  ∃ c₂ C₂ : ℝ, 0 < c₂ ∧ c₂ ≤ 1 ∧ 1 ≤ C₂ ∧
  ∀ (N : ℕ) [NeZero N], Odd N → ∀ k d : ℕ, 2 ≤ k → 1 ≤ d → ∀ α : ℝ, 0 < α → α ≤ 1 →
  let B (Γ : Finset (ZMod N)) (ρ : ℝ) := univ.filter fun x => ∀ γ ∈ Γ,
    min (((γ * x).val : ℝ) / N) (1 - ((γ * x).val : ℝ) / N) ≤ ρ
  let reg (Γ : Finset (ZMod N)) (ρ : ℝ) := Γ.Nonempty ∧ 0 < ρ ∧ ρ ≤ 1 ∧
    ∀ ε : ℝ, |ε| ≤ (100 * (Γ.card : ℝ))⁻¹ →
      (1 - 100 * (Γ.card : ℝ) * |ε|) * (B Γ ρ).card ≤ (B Γ ((1 + ε) * ρ)).card ∧
      ((B Γ ((1 + ε) * ρ)).card : ℝ) ≤ (1 + 100 * (Γ.card : ℝ) * |ε|) * (B Γ ρ).card
  ∀ (Γ : Finset (ZMod N)) (ρ₁ ρ₂ : ℝ), Γ.card ≤ 2 * d → reg Γ ρ₁ → reg Γ ρ₂ →
  ρ₁ ≤ (s₀ * c₀ * α / ((k : ℝ) ^ 5 * d)) * ρ₂ →
  ∀ S T D : Finset (ZMod N),
  let γ := c₀ / 1024 * (k : ℝ) ^ (-4 : ℤ)
  let μD : ℝ := (D.card : ℝ) / (B Γ ρ₂).card
  let cST : ℝ := (∑ s ∈ S, ∑ t ∈ T, if s + t ∈ D then (1 : ℝ) else 0) / ((S.card : ℝ) * T.card)
  let e := exp (-C₀ * (k : ℝ) ^ 6 * log (2 / α) ^ 2)
  S ⊆ B Γ ρ₁ → S.Nonempty → T ⊆ B Γ ρ₂ → T.Nonempty → D ⊆ B Γ ρ₂ → D.Nonempty →
  (1 - γ) * α ≤ μD → μD ≤ (1 + γ) * α →
  ((e ≤ (S.card : ℝ) / (B Γ ρ₁).card ∧ e ≤ (T.card : ℝ) / (B Γ ρ₂).card ∧
    μD + c₀ * (k : ℝ) ^ (-4 : ℤ) * α ≤ cST) ∨
   (exp (-C₀ * (k : ℝ) ^ 6 * log k * log (2 / α) ^ 2) ≤ (S.card : ℝ) / (B Γ ρ₁).card ∧
    (1 - γ) * α ≤ (T.card : ℝ) / (B Γ ρ₂).card ∧ c₀ * (k : ℝ) ^ (-4 : ℤ) * α ≤ |cST - μD|)) →
  ∃ (Δ : Finset (ZMod N)) (ρ' : ℝ) (y : ZMod N),
    reg (Γ ∪ Δ) ρ' ∧ (Δ.card : ℝ) ≤ C₂ * (k : ℝ) ^ 46 * log (2 / α) ^ 11 ∧
    ρ₁ * exp (-C₂ * (k * log (2 * d / α) + (k : ℝ) ^ 6 * log (2 / α) ^ 2)) ≤ ρ' ∧
    ((1 + c₂ * (k : ℝ) ^ (-5 : ℤ)) * α ≤ ((D.image (· - y) ∩ B (Γ ∪ Δ) ρ').card : ℝ) / (B (Γ ∪ Δ) ρ').card ∨
     (1 + c₂ * (k : ℝ) ^ (-5 : ℤ)) * α ≤ ((T.image (· - y) ∩ B (Γ ∪ Δ) ρ').card : ℝ) / (B (Γ ∪ Δ) ρ').card)

/- ### Step 6: Assembling Beker Proposition 3.2 and Main Reduction Theorem -/

lemma prop_3_2 (h1 : H1) (h2 : H2) :
    ∃ c K : ℝ, 0 < c ∧ c ≤ 1 ∧ 1 ≤ K ∧
      ∀ (N : ℕ) [NeZero N], Odd N → ∀ (k : ℕ), 2 ≤ k →
        ∀ (Γ : Finset (ZMod N)) (ρ : ℝ), IsRegularBohr Γ ρ →
        ∀ (A : Finset (ZMod N)), A ⊆ bohr Γ ρ → A.Nonempty →
          let α : ℝ := (A.card : ℝ) / ((bohr Γ ρ).card : ℝ)
          let d : ℕ := Γ.card
          (exp (-K * (k : ℝ) ^ 2 * log (k : ℝ) * (d : ℝ) * log (2 * (d : ℝ) / α)) *
              ρ ^ (2 * k * d) * (N : ℝ) ^ k ≤
            ((univ.filter fun x : Fin k → ZMod N =>
              ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)).card : ℝ)) ∨
          (∃ (σ : Bool) (Δ : Finset (ZMod N)) (ρ' : ℝ) (x : ZMod N),
            let Γ' : Finset (ZMod N) := Γ ∪ Γ.image (if σ then (2 * ·) else (inv2 N * ·)) ∪ Δ
            IsRegularBohr Γ' ρ' ∧
            (Δ.card : ℝ) ≤ K * (k : ℝ) ^ 46 * (log (2 / α)) ^ 11 ∧
            ρ * exp (-K * ((k : ℝ) * log (2 * (d : ℝ) / α) +
                (k : ℝ) ^ 6 * (log (2 / α)) ^ 2)) ≤ ρ' ∧
            (1 + c * (k : ℝ) ^ (-5 : ℤ)) * α ≤
              (((A.image (· - x)) ∩ bohr Γ' ρ').card : ℝ) / ((bohr Γ' ρ').card : ℝ)) := by
  obtain ⟨s₀, hs₀0, hs₀1, h2'⟩ := h2
  obtain ⟨c₁, C₁, hc₁0, hc₁1, hC₁1, h1'⟩ := h1 s₀ hs₀0 hs₀1
  obtain ⟨c₂, C₂, hc₂0, hc₂1, hC₂1, h2''⟩ := h2' c₁ C₁ hc₁0 hc₁1 hC₁1
  let c : ℝ := min c₁ c₂
  let K : ℝ := C₁ + C₂
  have hc0 : 0 < c := lt_min hc₁0 hc₂0
  have hc1 : c ≤ 1 := le_trans (min_le_left _ _) hc₁1
  have hK1 : 1 ≤ K := by dsimp [K]; linarith
  refine ⟨c, K, hc0, hc1, hK1, ?_⟩
  intro N _ hodd k hk Γ ρ hreg A hA_sub hA_ne α d
  have hd_pos : 1 ≤ d := Finset.card_pos.mpr hreg.1
  have hB_pos : (0 : ℝ) < ((bohr Γ ρ).card : ℝ) := by
    exact_mod_cast bohr_card_pos Γ hreg.2.1.le
  have hα_pos : 0 < α := div_pos (by exact_mod_cast hA_ne.card_pos) hB_pos
  have hα_le1 : α ≤ 1 := by
    dsimp [α]
    rw [div_le_one hB_pos]
    exact_mod_cast Finset.card_le_card hA_sub
  have hlog_ge0 : 0 ≤ log (2 * (d : ℝ) / α) := by
    apply Real.log_nonneg
    rw [one_le_div hα_pos]
    have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
    linarith
  have hlog2_ge0 : 0 ≤ log (2 / α) := by
    apply Real.log_nonneg
    rw [one_le_div hα_pos]; linarith
  have hlogk_ge0 : 0 ≤ log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  rcases h1' N hodd k hk Γ ρ hreg A hA_sub hA_ne with hcnt | hdir | hpair
  · left
    change exp (-C₁ * (k : ℝ) ^ 2 * log (k : ℝ) * (d : ℝ) * log (2 * (d : ℝ) / α)) *
        ρ ^ (2 * k * d) * (N : ℝ) ^ k ≤ _ at hcnt
    refine le_trans ?_ hcnt
    have hρ_nn : 0 ≤ ρ ^ (2 * k * d) := pow_nonneg hreg.2.1.le _
    have hN_nn : 0 ≤ (N : ℝ) ^ k := by positivity
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hρ_nn) hN_nn
    apply Real.exp_le_exp.mpr
    have hterm_nn : 0 ≤ (k : ℝ) ^ 2 * log (k : ℝ) * (d : ℝ) * log (2 * (d : ℝ) / α) := by
      positivity
    have hC_le : C₁ ≤ K := by dsimp [K]; linarith
    nlinarith
  · right
    obtain ⟨σ, ρ', x, hreg', hρ'_ge, hdens'⟩ := hdir
    change IsRegularBohr (Γ ∪ Γ.image (if σ then (2 * ·) else (inv2 N * ·))) ρ' at hreg'
    change ρ * exp (-C₁ * ((k : ℝ) * log (2 * (d : ℝ) / α) + (k : ℝ) ^ 6 * (log (2 / α)) ^ 2)) ≤ ρ' at hρ'_ge
    change (1 + c₁ * (k : ℝ) ^ (-5 : ℤ)) * α ≤
      (((A.image (· - x)) ∩ bohr (Γ ∪ Γ.image (if σ then (2 * ·) else (inv2 N * ·))) ρ').card : ℝ) /
        ((bohr (Γ ∪ Γ.image (if σ then (2 * ·) else (inv2 N * ·))) ρ').card : ℝ) at hdens'
    refine ⟨σ, ∅, ρ', x, ?_, ?_, ?_, ?_⟩
    · simpa only [Finset.union_empty] using hreg'
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
    · refine le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hreg.2.1.le) hρ'_ge
      have hterm_nn : 0 ≤ (k : ℝ) * log (2 * (d : ℝ) / α) + (k : ℝ) ^ 6 * (log (2 / α)) ^ 2 := by
        positivity
      have hC_le : C₁ ≤ K := by dsimp [K]; linarith
      nlinarith
    · simp only [Finset.union_empty]
      have hc_le : c ≤ c₁ := min_le_left _ _
      have hk5_nn : 0 ≤ (k : ℝ) ^ (-5 : ℤ) := by positivity
      exact (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc_le hk5_nn)) hα_pos.le).trans hdens'
  · right
    obtain ⟨x, ρ₁, ρ₂, S, T, D, hreg1, hreg2, hρ1_ge, hρ1_le, _hρ2_le,
      hS_sub, hS_ne, hT_subA, hT_ne, hD_sub2A, hD_ne, hD_lb, hD_ub, hbias⟩ := hpair
    let Γtilde : Finset (ZMod N) := Γ ∪ Γ.image (inv2 N * ·)
    change IsRegularBohr Γtilde ρ₁ at hreg1
    change IsRegularBohr Γtilde ρ₂ at hreg2
    change ρ * exp (-C₁ * ((k : ℝ) * log (2 * (d : ℝ) / α) + (k : ℝ) ^ 6 * (log (2 / α)) ^ 2)) ≤ ρ₁ at hρ1_ge
    change S ⊆ bohr Γtilde ρ₁ at hS_sub
    change T ⊆ A.image (· - x) ∩ bohr Γtilde ρ₂ at hT_subA
    change D ⊆ (A.image (· - x)).image (2 * ·) ∩ bohr Γtilde ρ₂ at hD_sub2A
    have hΓtilde_card : Γtilde.card ≤ 2 * d := by
      calc Γtilde.card ≤ Γ.card + (Γ.image (inv2 N * ·)).card := Finset.card_union_le _ _
        _ ≤ Γ.card + Γ.card := Nat.add_le_add_left Finset.card_image_le _
        _ = 2 * d := by dsimp [d]; ring
    have hT_sub : T ⊆ bohr Γtilde ρ₂ := hT_subA.trans Finset.inter_subset_right
    have hD_sub : D ⊆ bohr Γtilde ρ₂ := hD_sub2A.trans Finset.inter_subset_right
    obtain ⟨Δ, ρ', y, hreg', hΔ_card, hρ'_ge, hdens_or⟩ :=
      h2'' N hodd k d hk hd_pos α hα_pos hα_le1 Γtilde ρ₁ ρ₂ hΓtilde_card hreg1 hreg2
        hρ1_le S T D hS_sub hS_ne hT_sub hT_ne hD_sub hD_ne hD_lb hD_ub hbias
    change IsRegularBohr (Γtilde ∪ Δ) ρ' at hreg'
    change ρ₁ * exp (-C₂ * ((k : ℝ) * log (2 * (d : ℝ) / α) + (k : ℝ) ^ 6 * (log (2 / α)) ^ 2)) ≤ ρ' at hρ'_ge
    have hρ'_from_ρ : ρ * exp (-K * ((k : ℝ) * log (2 * (d : ℝ) / α) +
        (k : ℝ) ^ 6 * (log (2 / α)) ^ 2)) ≤ ρ' := by
      set E : ℝ := (k : ℝ) * log (2 * (d : ℝ) / α) + (k : ℝ) ^ 6 * (log (2 / α)) ^ 2
      calc ρ * exp (-K * E)
          = (ρ * exp (-C₁ * E)) * exp (-C₂ * E) := by
            rw [mul_assoc, ← exp_add]; dsimp [K]; ring_nf
        _ ≤ ρ₁ * exp (-C₂ * E) :=
            mul_le_mul_of_nonneg_right hρ1_ge (exp_pos _).le
        _ ≤ ρ' := hρ'_ge
    have hΔ_K : (Δ.card : ℝ) ≤ K * (k : ℝ) ^ 46 * (log (2 / α)) ^ 11 := by
      have hterm_nn : 0 ≤ (k : ℝ) ^ 46 * (log (2 / α)) ^ 11 := by positivity
      have hC_le : C₂ ≤ K := by dsimp [K]; linarith
      nlinarith
    have hc_le : c ≤ c₂ := min_le_right _ _
    have hk5_nn : 0 ≤ (k : ℝ) ^ (-5 : ℤ) := by positivity
    rcases hdens_or with hdens_D | hdens_T
    · -- Case 1: density increment on `D ⊆ 2·(A - x)` ⇒ `2⁻¹`-dilation transfers to `Γ ∪ 2·Γ ∪ 2·Δ` (`σ = true`)
      change (1 + c₂ * (k : ℝ) ^ (-5 : ℤ)) * α ≤
        (((D.image (· - y)) ∩ bohr (Γtilde ∪ Δ) ρ').card : ℝ) /
          ((bohr (Γtilde ∪ Δ) ρ').card : ℝ) at hdens_D
      have hdens_c : (1 + c * (k : ℝ) ^ (-5 : ℤ)) * α ≤
          (((D.image (· - y)) ∩ bohr (Γtilde ∪ Δ) ρ').card : ℝ) /
            ((bohr (Γtilde ∪ Δ) ρ').card : ℝ) :=
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc_le hk5_nn)) hα_pos.le).trans hdens_D
      let Δ' : Finset (ZMod N) := Δ.image (2 * ·)
      have hΓ'_eq : (Γtilde ∪ Δ).image (2 * ·) = Γ ∪ Γ.image (2 * ·) ∪ Δ' := by
        ext γ
        simp only [Γtilde, Δ', Finset.mem_image, Finset.mem_union]
        constructor
        · rintro ⟨u, (huΓ | ⟨v, hvΓ, rfl⟩) | huΔ, rfl⟩
          · exact Or.inl (Or.inr ⟨u, huΓ, rfl⟩)
          · rw [← mul_assoc, two_mul_inv2 hodd, one_mul]
            exact Or.inl (Or.inl hvΓ)
          · exact Or.inr ⟨u, huΔ, rfl⟩
        · rintro ((hγΓ | ⟨v, hvΓ, rfl⟩) | ⟨u, huΔ, rfl⟩)
          · exact ⟨inv2 N * γ, Or.inl (Or.inr ⟨γ, hγΓ, rfl⟩),
              by rw [← mul_assoc, two_mul_inv2 hodd, one_mul]⟩
          · exact ⟨v, Or.inl (Or.inl hvΓ), rfl⟩
          · exact ⟨u, Or.inr huΔ, rfl⟩
      have hreg'' : IsRegularBohr (Γ ∪ Γ.image (2 * ·) ∪ Δ') ρ' := by
        rw [← hΓ'_eq]
        exact isRegularBohr_image_two hodd hreg'
      have hΔ'_card : (Δ'.card : ℝ) ≤ K * (k : ℝ) ^ 46 * (log (2 / α)) ^ 11 := by
        have heq : Δ'.card = Δ.card := Finset.card_image_of_injective Δ (mul_two_injective hodd)
        rw [heq]; exact hΔ_K
      refine ⟨true, Δ', ρ', x + inv2 N * y, hreg'', hΔ'_card, hρ'_from_ρ, ?_⟩
      change (1 + c * (k : ℝ) ^ (-5 : ℤ)) * α ≤
        (((A.image (· - (x + inv2 N * y))) ∩ bohr (Γ ∪ Γ.image (2 * ·) ∪ Δ') ρ').card : ℝ) /
          ((bohr (Γ ∪ Γ.image (2 * ·) ∪ Δ') ρ').card : ℝ)
      have hB_card_eq : (bohr (Γ ∪ Γ.image (2 * ·) ∪ Δ') ρ').card = (bohr (Γtilde ∪ Δ) ρ').card := by
        rw [← hΓ'_eq]
        exact bohr_image_two_card hodd (Γtilde ∪ Δ) ρ'
      rw [hB_card_eq]
      refine hdens_c.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      have hcard_le : ((D.image (· - y)) ∩ bohr (Γtilde ∪ Δ) ρ').card ≤
          ((A.image (· - (x + inv2 N * y))) ∩ bohr (Γ ∪ Γ.image (2 * ·) ∪ Δ') ρ').card := by
        refine Finset.card_le_card_of_injOn (fun w => inv2 N * w) ?_
          (fun w₁ _ w₂ _ h => mul_inv2_injective hodd h)
        intro w hw
        obtain ⟨hwD, hwB⟩ := Finset.mem_inter.mp hw
        refine Finset.mem_coe.mpr (Finset.mem_inter.mpr ⟨?_, ?_⟩)
        · obtain ⟨u, huD, rfl⟩ := Finset.mem_image.mp hwD
          obtain ⟨v, hvAx, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hD_sub2A huD)).1
          obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hvAx
          refine Finset.mem_image.mpr ⟨a, haA, ?_⟩
          calc a - (x + inv2 N * y) = 1 * (a - x) - inv2 N * y := by ring
            _ = (inv2 N * 2) * (a - x) - inv2 N * y := by rw [inv2_mul_two hodd]
            _ = inv2 N * (2 * (a - x) - y) := by ring
        · rw [← hΓ'_eq, bohr_image_two_mem, ← mul_assoc, two_mul_inv2 hodd, one_mul]
          exact hwB
      exact_mod_cast hcard_le
    · -- Case 2: density increment on `T ⊆ A - x` ⇒ shift `x + y` works directly on `Γtilde ∪ Δ` (`σ = false`)
      change (1 + c₂ * (k : ℝ) ^ (-5 : ℤ)) * α ≤
        (((T.image (· - y)) ∩ bohr (Γtilde ∪ Δ) ρ').card : ℝ) /
          ((bohr (Γtilde ∪ Δ) ρ').card : ℝ) at hdens_T
      have hdens_c : (1 + c * (k : ℝ) ^ (-5 : ℤ)) * α ≤
          (((T.image (· - y)) ∩ bohr (Γtilde ∪ Δ) ρ').card : ℝ) /
            ((bohr (Γtilde ∪ Δ) ρ').card : ℝ) :=
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hc_le hk5_nn)) hα_pos.le).trans hdens_T
      refine ⟨false, Δ, ρ', x + y, hreg', hΔ_K, hρ'_from_ρ, ?_⟩
      change (1 + c * (k : ℝ) ^ (-5 : ℤ)) * α ≤
        (((A.image (· - (x + y))) ∩ bohr (Γtilde ∪ Δ) ρ').card : ℝ) /
          ((bohr (Γtilde ∪ Δ) ρ').card : ℝ)
      refine hdens_c.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _))
      have hsub : (T.image (· - y)) ∩ bohr (Γtilde ∪ Δ) ρ' ⊆
          (A.image (· - (x + y))) ∩ bohr (Γtilde ∪ Δ) ρ' := by
        intro w hw
        obtain ⟨hwT, hwB⟩ := Finset.mem_inter.mp hw
        refine Finset.mem_inter.mpr ⟨?_, hwB⟩
        obtain ⟨u, huT, rfl⟩ := Finset.mem_image.mp hwT
        obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp (Finset.mem_inter.mp (hT_subA huT)).1
        exact Finset.mem_image.mpr ⟨a, haA, by ring⟩
      exact_mod_cast Finset.card_le_card hsub

theorem main : H1 → H2 → OMA.R_Green2_green_2_lower_bound_sanders_R1.H2 := by
  intro h1 h2
  obtain ⟨c, K, hc0, hc1, hK1, hprop⟩ := prop_3_2 h1 h2
  -- Assemble the single explicit constant `C` absorbing all intermediate bounds
  let B_t : ℝ := 2 / c + 2
  have hBt_ge1 : 1 ≤ B_t := by dsimp [B_t]; linarith [div_pos two_pos hc0]
  let C_d : ℝ := 2 * B_t ^ 2 * K
  have hCd_ge1 : 1 ≤ C_d := by dsimp [C_d]; nlinarith
  let C_log : ℝ := 2 * C_d + 126
  have hClog_ge1 : 1 ≤ C_log := by dsimp [C_log]; linarith
  let C_step : ℝ := K * (2 * C_log + 1)
  have hCstep_pos : 0 < C_step := by dsimp [C_step]; positivity
  let C_rho : ℝ := B_t * C_step
  have hCrho_pos : 0 < C_rho := by dsimp [C_rho]; positivity
  let C_tot : ℝ := K * C_d * C_log + 2 * C_d * C_rho + 2 * (2 : ℝ) ^ 16
  have hCtot_pos : 0 < C_tot := by dsimp [C_tot]; positivity
  refine ⟨C_tot, hCtot_pos, ?_⟩
  intro N hodd k hk A hA_ne hno_kcfg
  have hN_pos_nat : 0 < N := odd_pos hodd
  have : NeZero N := ⟨hN_pos_nat.ne'⟩
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA_ne.card_pos
  have hAleN : (A.card : ℝ) ≤ (N : ℝ) := by
    have : A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    rw [ZMod.card] at this
    exact_mod_cast this
  set L : ℝ := log (2 * (N : ℝ) / (A.card : ℝ))
  have hL_ge : (1 / 2 : ℝ) ≤ L := by
    have h2 : (2 : ℝ) ≤ 2 * (N : ℝ) / (A.card : ℝ) := by
      rw [le_div_iff₀ hApos]; linarith
    exact half_le_log_two.trans (Real.log_le_log (by norm_num) h2)
  have hL_pos : 0 < L := by linarith
  have hk_ge2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  -- Choose a BohrChain of maximal length `t`
  let Tmax : ℕ := Nat.floor ((2 / c) * (k : ℝ) ^ 5 * L) + 1
  let Valid : Finset ℕ := (Finset.range (Tmax + 1)).filter fun t => Nonempty (BohrChain c K k A t)
  have h0_mem : 0 ∈ Valid := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), ⟨{
      Γ := fun _ => {0}
      ρ := fun _ => 1
      Aset := fun _ => A
      Δ := fun _ => {0}
      shift := fun _ => 0
      hΓ0 := rfl
      hρ0 := rfl
      hA0 := rfl
      hΔ0 := rfl
      hshift0 := rfl
      hreg := fun _ => isRegularBohr_singleton_zero
      hAsub := fun _ => by rw [bohr_singleton_zero (by norm_num)]; exact Finset.subset_univ A
      hAshift := fun _ a ha => Finset.mem_image.mpr ⟨a, ha, by simp⟩
      hAne := fun _ => hA_ne
      hstep := fun s => Fin.elim0 s
    }⟩⟩
  let t : ℕ := Valid.max' ⟨0, h0_mem⟩
  have ht_mem : t ∈ Valid := Finset.max'_mem Valid ⟨0, h0_mem⟩
  obtain ⟨ch⟩ := (Finset.mem_filter.mp ht_mem).2
  have ht_le : (t : ℝ) ≤ (2 / c) * (k : ℝ) ^ 5 * L := chain_length_le hc0 hc1 hk hA_ne ch
  have ht1_le : (t : ℝ) + 1 ≤ B_t * (k : ℝ) ^ 5 * L := by
    have hk5L : (1 : ℝ) ≤ (k : ℝ) ^ 5 * L := by
      have hk5 : (32 : ℝ) ≤ (k : ℝ) ^ 5 := by
        have := pow_le_pow_left₀ (by norm_num) hk_ge2 5; norm_num at this; exact this
      nlinarith
    dsimp [B_t]; nlinarith
  have h2t1_le : 2 * (t : ℝ) + 1 ≤ 2 * (B_t * (k : ℝ) ^ 5 * L) := by linarith
  -- Apply Proposition 3.2 to the final set `A_t ⊆ B_t`: maximality forces the counting case
  let Γt := ch.Γ (Fin.last t)
  let ρt := ch.ρ (Fin.last t)
  let At := ch.Aset (Fin.last t)
  let dt : ℕ := Γt.card
  let αt : ℝ := (At.card : ℝ) / ((bohr Γt ρt).card : ℝ)
  have hdt_pos : 1 ≤ dt := Finset.card_pos.mpr (ch.hreg (Fin.last t)).1
  have hcount :
      exp (-K * (k : ℝ) ^ 2 * log (k : ℝ) * (dt : ℝ) * log (2 * (dt : ℝ) / αt)) *
          ρt ^ (2 * k * dt) * (N : ℝ) ^ k ≤
        ((univ.filter fun x : Fin k → ZMod N =>
          ∀ i j : Fin k, x i + x j ∈ At.image (2 * ·)).card : ℝ) := by
    rcases hprop N hodd k hk Γt ρt (ch.hreg (Fin.last t)) At (ch.hAsub (Fin.last t))
        (ch.hAne (Fin.last t)) with hcnt | hinc
    · exact hcnt
    · exfalso
      obtain ⟨σ, Δ_new, ρ_new, x, hreg_new, hΔ_new, hρ_new, hdens_new⟩ := hinc
      let ch' := extendChain ch σ Δ_new ρ_new x hreg_new hΔ_new hρ_new hdens_new hc0
      have ht1_bd := chain_length_le hc0 hc1 hk hA_ne ch'
      have ht1_lt : t + 1 < Tmax + 1 := by
        have hfl := Nat.lt_floor_add_one ((2 / c) * (k : ℝ) ^ 5 * L)
        have hcast : ((t + 1 : ℕ) : ℝ) < ((Tmax + 1 : ℕ) : ℝ) := by
          dsimp [Tmax]; push_cast; linarith
        exact_mod_cast hcast
      have hmem' : t + 1 ∈ Valid :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht1_lt, ⟨ch'⟩⟩
      have hle_max : t + 1 ≤ t := Finset.le_max' Valid (t + 1) hmem'
      omega
  -- Quantitative bounds on `dt`, `log(2 dt N / |A|)`, and `ρt`
  have hdt_ub : (dt : ℝ) ≤ C_d * (k : ℝ) ^ 56 * L ^ 13 := by
    have hpil := pilatte_rank_bound hodd hc0 hK1 hk hA_ne ch
    have hprod : ((t : ℝ) + 1) * (2 * (t : ℝ) + 1) ≤ 2 * B_t ^ 2 * (k : ℝ) ^ 10 * L ^ 2 := by
      have h1 := mul_le_mul ht1_le h2t1_le (by positivity) (by positivity)
      calc ((t : ℝ) + 1) * (2 * (t : ℝ) + 1)
          ≤ (B_t * (k : ℝ) ^ 5 * L) * (2 * (B_t * (k : ℝ) ^ 5 * L)) := h1
        _ = 2 * B_t ^ 2 * (k : ℝ) ^ 10 * L ^ 2 := by ring
    have hKterm_nn : 0 ≤ K * (k : ℝ) ^ 46 * L ^ 11 := by positivity
    calc (dt : ℝ)
        ≤ ((t : ℝ) + 1) * (2 * (t : ℝ) + 1) * (K * (k : ℝ) ^ 46 * L ^ 11) := hpil
      _ ≤ (2 * B_t ^ 2 * (k : ℝ) ^ 10 * L ^ 2) * (K * (k : ℝ) ^ 46 * L ^ 11) :=
          mul_le_mul_of_nonneg_right hprod hKterm_nn
      _ = C_d * (k : ℝ) ^ 56 * L ^ 13 := by dsimp [C_d]; ring
  have hlog_dt : log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) ≤ C_log * (k : ℝ) * L := by
    have hdt_R_pos : (0 : ℝ) < (dt : ℝ) := by exact_mod_cast hdt_pos
    have hCd_pos : 0 < C_d := by linarith
    have h2NA_pos : 0 < 2 * (N : ℝ) / (A.card : ℝ) := div_pos (mul_pos two_pos hNpos) hApos
    have harg_le : 2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ) ≤
        (C_d * (k : ℝ) ^ 56 * L ^ 13) * (2 * (N : ℝ) / (A.card : ℝ)) := by
      have heq : 2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ) = (dt : ℝ) * (2 * (N : ℝ) / (A.card : ℝ)) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hdt_ub h2NA_pos.le
    have hlog_split : log ((C_d * (k : ℝ) ^ 56 * L ^ 13) * (2 * (N : ℝ) / (A.card : ℝ))) =
        log C_d + 56 * log (k : ℝ) + 13 * log L + L := by
      have h1 : C_d * (k : ℝ) ^ 56 ≠ 0 := (mul_pos hCd_pos (pow_pos hk_pos 56)).ne'
      have h2 : L ^ 13 ≠ 0 := (pow_pos hL_pos 13).ne'
      rw [Real.log_mul (mul_ne_zero h1 h2) h2NA_pos.ne', Real.log_mul h1 h2,
        Real.log_mul hCd_pos.ne' (pow_pos hk_pos 56).ne', Real.log_pow, Real.log_pow]
      push_cast; rfl
    have hlogCd : log C_d ≤ C_d := le_trans (Real.log_le_sub_one_of_pos hCd_pos) (by linarith)
    have hlogk : log (k : ℝ) ≤ (k : ℝ) := le_trans (Real.log_le_sub_one_of_pos hk_pos) (by linarith)
    have hlogL : log L ≤ L := le_trans (Real.log_le_sub_one_of_pos hL_pos) (by linarith)
    have hlog1 : log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) ≤
        C_d + 56 * (k : ℝ) + 13 * L + L := by
      have := Real.log_le_log (div_pos (mul_pos (mul_pos two_pos hdt_R_pos) hNpos) hApos) harg_le
      rw [hlog_split] at this
      linarith
    have hkL_ge1 : (1 : ℝ) ≤ (k : ℝ) * L := by
      have := mul_le_mul hk_ge2 hL_ge (by norm_num) (by linarith); linarith
    have h1 : C_d ≤ C_d * (k : ℝ) * L := by
      rw [mul_assoc]; exact le_mul_of_one_le_right hCd_pos.le hkL_ge1
    have h2 : 56 * (k : ℝ) ≤ 112 * (k : ℝ) * L := by
      have := mul_le_mul_of_nonneg_left hL_ge (show 0 ≤ 112 * (k : ℝ) by linarith); linarith
    have h3 : 14 * L ≤ 14 * (k : ℝ) * L := by
      have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (k : ℝ) by linarith) (show 0 ≤ 14 * L by linarith)
      linarith
    have h4 : (C_d + 112 + 14) * ((k : ℝ) * L) ≤ C_log * ((k : ℝ) * L) :=
      mul_le_mul_of_nonneg_right (by dsimp [C_log]; linarith) (by linarith)
    calc log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ))
        ≤ C_d + 56 * (k : ℝ) + 13 * L + L := hlog1
      _ ≤ C_d * (k : ℝ) * L + 112 * (k : ℝ) * L + 14 * (k : ℝ) * L := by linarith
      _ = (C_d + 112 + 14) * ((k : ℝ) * L) := by ring
      _ ≤ C_log * ((k : ℝ) * L) := h4
      _ = C_log * (k : ℝ) * L := by ring
  have hαt_ge : (A.card : ℝ) / (N : ℝ) ≤ αt := by
    have hg := chain_density_ge hc0 hk ch (Fin.last t)
    have hpow1 : (1 : ℝ) ≤ (1 + c * (k : ℝ) ^ (-5 : ℤ)) ^ t :=
      one_le_pow₀ (by linarith [show 0 ≤ c * (k : ℝ) ^ (-5 : ℤ) by positivity])
    have hα0_nn : 0 ≤ (A.card : ℝ) / (N : ℝ) := by positivity
    exact (le_mul_of_one_le_left hα0_nn hpow1).trans hg
  have hαt_pos : 0 < αt := lt_of_lt_of_le (div_pos hApos hNpos) hαt_ge
  have hlog_dt_αt : log (2 * (dt : ℝ) / αt) ≤ C_log * (k : ℝ) * L := by
    have hdt_R_pos : (0 : ℝ) < (dt : ℝ) := by exact_mod_cast hdt_pos
    refine le_trans (Real.log_le_log (div_pos (mul_pos two_pos hdt_R_pos) hαt_pos) ?_) hlog_dt
    rw [show 2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ) = (2 * (dt : ℝ)) / ((A.card : ℝ) / (N : ℝ)) by
      field_simp [hApos.ne', hNpos.ne']]
    exact div_le_div_of_nonneg_left (mul_pos two_pos hdt_R_pos).le (div_pos hApos hNpos) hαt_ge
  have hρt_lb : exp (-C_rho * (k : ℝ) ^ 11 * L ^ 3) ≤ ρt := by
    have hw := chain_width_lower hc0 hK1 hk hA_ne ch
    refine le_trans (Real.exp_le_exp.mpr ?_) hw
    have hk2_le_k6 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := by
      have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      have h2 := le_mul_of_one_le_right (sq_nonneg (k : ℝ)) h1
      linarith [show (k : ℝ) ^ 2 * (k : ℝ) ^ 4 = (k : ℝ) ^ 6 by ring]
    have hL_le_2L2 : L ≤ 2 * L ^ 2 := by
      have := mul_le_mul_of_nonneg_left hL_ge (show 0 ≤ 2 * L by linarith); linarith
    have hE_ub : K * ((k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2) ≤
        C_step * (k : ℝ) ^ 6 * L ^ 2 := by
      have hterm1 : (k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) ≤
          2 * C_log * (k : ℝ) ^ 6 * L ^ 2 := by
        calc (k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ))
            ≤ (k : ℝ) * (C_log * (k : ℝ) * L) := mul_le_mul_of_nonneg_left hlog_dt hk_pos.le
          _ = C_log * ((k : ℝ) ^ 2 * L) := by ring
          _ ≤ C_log * ((k : ℝ) ^ 6 * (2 * L ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul hk2_le_k6 hL_le_2L2 hL_pos.le (by positivity)) (by linarith)
          _ = 2 * C_log * (k : ℝ) ^ 6 * L ^ 2 := by ring
      have hsum : (k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2 ≤
          (2 * C_log + 1) * (k : ℝ) ^ 6 * L ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ K by linarith)
      calc K * ((k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2)
          ≤ K * ((2 * C_log + 1) * (k : ℝ) ^ 6 * L ^ 2) := this
        _ = C_step * (k : ℝ) ^ 6 * L ^ 2 := by dsimp [C_step]; ring
    have ht_ub : (t : ℝ) ≤ B_t * (k : ℝ) ^ 5 * L := by linarith
    have hE_nn : 0 ≤ K * ((k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2) := by
      have hlog_nn : 0 ≤ log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) := by
        apply Real.log_nonneg
        rw [one_le_div hApos]
        have hdt1 : (1 : ℝ) ≤ (dt : ℝ) := by exact_mod_cast hdt_pos
        have h2dt : (2 : ℝ) ≤ 2 * (dt : ℝ) := by linarith
        have h2dtN := mul_le_mul h2dt hAleN hApos.le (by linarith)
        linarith
      exact mul_nonneg (by linarith) (add_nonneg (mul_nonneg hk_pos.le hlog_nn) (mul_nonneg (pow_nonneg hk_pos.le 6) (sq_nonneg L)))
    have hprod : (t : ℝ) * (K * ((k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2)) ≤
        C_rho * (k : ℝ) ^ 11 * L ^ 3 := by
      calc (t : ℝ) * (K * ((k : ℝ) * log (2 * (dt : ℝ) * (N : ℝ) / (A.card : ℝ)) + (k : ℝ) ^ 6 * L ^ 2))
          ≤ (B_t * (k : ℝ) ^ 5 * L) * (C_step * (k : ℝ) ^ 6 * L ^ 2) :=
            mul_le_mul ht_ub hE_ub hE_nn (by positivity)
        _ = C_rho * (k : ℝ) ^ 11 * L ^ 3 := by dsimp [C_rho]; ring
    linarith
  -- Combine both exponential factors into `exp(-(K*C_d*C_log + 2*C_d*C_rho) * k^68 * L^16) * N^k`
  have hcount_exp :
      exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) * (N : ℝ) ^ k ≤
        ((univ.filter fun x : Fin k → ZMod N =>
          ∀ i j : Fin k, x i + x j ∈ At.image (2 * ·)).card : ℝ) := by
    have hfac1 : exp (-(K * C_d * C_log) * (k : ℝ) ^ 68 * L ^ 16) ≤
        exp (-K * (k : ℝ) ^ 2 * log (k : ℝ) * (dt : ℝ) * log (2 * (dt : ℝ) / αt)) := by
      apply Real.exp_le_exp.mpr
      have hlogk_le : log (k : ℝ) ≤ (k : ℝ) :=
        le_trans (Real.log_le_sub_one_of_pos hk_pos) (by linarith)
      have hlogk_nn : 0 ≤ log (k : ℝ) := Real.log_nonneg (by linarith)
      have hlogdt_nn : 0 ≤ log (2 * (dt : ℝ) / αt) := by
        apply Real.log_nonneg
        rw [one_le_div hαt_pos]
        have hBpos : (0 : ℝ) < ((bohr Γt ρt).card : ℝ) := by
          exact_mod_cast bohr_card_pos _ (ch.hreg (Fin.last t)).2.1.le
        have hαt_le1 : αt ≤ 1 := by
          rw [div_le_one hBpos]
          exact_mod_cast Finset.card_le_card (ch.hAsub (Fin.last t))
        have hdt1 : (1 : ℝ) ≤ (dt : ℝ) := by exact_mod_cast hdt_pos
        linarith
      have hk60 : (k : ℝ) ^ 60 * L ^ 14 ≤ (k : ℝ) ^ 68 * L ^ 16 := by
        have hk8 : (2 : ℝ) ^ 8 ≤ (k : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hk_ge2 8
        have hL2 : (1 / 2 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL_ge 2
        have hge1 : (1 : ℝ) ≤ (k : ℝ) ^ 8 * L ^ 2 := by
          have : (2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 2 = 64 := by norm_num
          linarith [mul_le_mul hk8 hL2 (by positivity) (by positivity)]
        have hmul := le_mul_of_one_le_right (show 0 ≤ (k : ℝ) ^ 60 * L ^ 14 by positivity) hge1
        linarith [show (k : ℝ) ^ 60 * L ^ 14 * ((k : ℝ) ^ 8 * L ^ 2) = (k : ℝ) ^ 68 * L ^ 16 by ring]
      have hbd : K * (k : ℝ) ^ 2 * log (k : ℝ) * (dt : ℝ) * log (2 * (dt : ℝ) / αt) ≤
          K * C_d * C_log * (k : ℝ) ^ 68 * L ^ 16 := by
        calc K * (k : ℝ) ^ 2 * log (k : ℝ) * (dt : ℝ) * log (2 * (dt : ℝ) / αt)
            ≤ K * (k : ℝ) ^ 2 * (k : ℝ) * (C_d * (k : ℝ) ^ 56 * L ^ 13) * (C_log * (k : ℝ) * L) := by
              have h1 : (k : ℝ) ^ 2 * log (k : ℝ) ≤ (k : ℝ) ^ 2 * (k : ℝ) :=
                mul_le_mul_of_nonneg_left hlogk_le (sq_nonneg _)
              have h2 : K * ((k : ℝ) ^ 2 * log (k : ℝ)) ≤ K * ((k : ℝ) ^ 2 * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left h1 (by linarith)
              have h3 : (K * (k : ℝ) ^ 2 * log (k : ℝ)) * (dt : ℝ) ≤
                  (K * (k : ℝ) ^ 2 * (k : ℝ)) * (C_d * (k : ℝ) ^ 56 * L ^ 13) :=
                mul_le_mul (by linarith) hdt_ub (Nat.cast_nonneg _) (by positivity)
              exact mul_le_mul h3 hlog_dt_αt hlogdt_nn (by positivity)
          _ = (K * C_d * C_log) * ((k : ℝ) ^ 60 * L ^ 14) := by ring
          _ ≤ (K * C_d * C_log) * ((k : ℝ) ^ 68 * L ^ 16) :=
              mul_le_mul_of_nonneg_left hk60 (by positivity)
          _ = K * C_d * C_log * (k : ℝ) ^ 68 * L ^ 16 := by ring
      linarith
    have hfac2 : exp (-(2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) ≤ ρt ^ (2 * k * dt) := by
      have hpow : (exp (-C_rho * (k : ℝ) ^ 11 * L ^ 3)) ^ (2 * k * dt) ≤ ρt ^ (2 * k * dt) :=
        pow_le_pow_left₀ (exp_pos _).le hρt_lb (2 * k * dt)
      refine le_trans ?_ hpow
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hprod : ((2 * k * dt : ℕ) : ℝ) * (C_rho * (k : ℝ) ^ 11 * L ^ 3) ≤
          2 * C_d * C_rho * (k : ℝ) ^ 68 * L ^ 16 := by
        push_cast
        calc 2 * (k : ℝ) * (dt : ℝ) * (C_rho * (k : ℝ) ^ 11 * L ^ 3)
            ≤ 2 * (k : ℝ) * (C_d * (k : ℝ) ^ 56 * L ^ 13) * (C_rho * (k : ℝ) ^ 11 * L ^ 3) := by
              have h1 := mul_le_mul_of_nonneg_left hdt_ub (show 0 ≤ 2 * (k : ℝ) by positivity)
              exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 2 * C_d * C_rho * (k : ℝ) ^ 68 * L ^ 16 := by ring
      linarith
    have hprod_fac : exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) ≤
        exp (-K * (k : ℝ) ^ 2 * log (k : ℝ) * (dt : ℝ) * log (2 * (dt : ℝ) / αt)) *
          ρt ^ (2 * k * dt) := by
      have hexp_eq : exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) =
          exp (-(K * C_d * C_log) * (k : ℝ) ^ 68 * L ^ 16) *
          exp (-(2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) := by
        rw [← exp_add]; ring_nf
      rw [hexp_eq]
      exact mul_le_mul hfac1 hfac2 (exp_pos _).le (exp_pos _).le
    exact (mul_le_mul_of_nonneg_right hprod_fac (by positivity)).trans hcount
  -- Transfer `At ⊆ A - shift` count to `A`, then upper bound by degenerate tuples `≤ k² N^(k-1)`
  have hAt_to_A :
      (univ.filter fun x : Fin k → ZMod N =>
        ∀ i j : Fin k, x i + x j ∈ At.image (2 * ·)).card ≤
      (univ.filter fun x : Fin k → ZMod N =>
        ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)).card := by
    have hsub1 : (univ.filter fun x : Fin k → ZMod N =>
        ∀ i j : Fin k, x i + x j ∈ At.image (2 * ·)) ⊆
        (univ.filter fun x : Fin k → ZMod N =>
          ∀ i j : Fin k, x i + x j ∈ (A.image (· - ch.shift (Fin.last t))).image (2 * ·)) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i j => ?_⟩
      exact Finset.image_subset_image (ch.hAshift (Fin.last t)) ((Finset.mem_filter.mp hx).2 i j)
    exact (Finset.card_le_card hsub1).trans (kconfig_count_translate A (ch.shift (Fin.last t)))
  have hA_to_deg :
      (univ.filter fun x : Fin k → ZMod N =>
        ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)).card ≤ k ^ 2 * N ^ (k - 1) := by
    have hsub_deg : (univ.filter fun x : Fin k → ZMod N =>
        ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)) ⊆
        (univ.filter fun x : Fin k → ZMod N => ¬ Function.Injective x) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hinj => ?_⟩
      exact hno_kcfg x hinj (Finset.mem_filter.mp hx).2
    exact (Finset.card_le_card hsub_deg).trans (degenerate_tuples_card_le hk)
  have hchain_R :
      exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) * (N : ℝ) ^ k ≤
        (k : ℝ) ^ 2 * (N : ℝ) ^ (k - 1) := by
    have hnat : ((univ.filter fun x : Fin k → ZMod N =>
        ∀ i j : Fin k, x i + x j ∈ At.image (2 * ·)).card : ℝ) ≤ (k : ℝ) ^ 2 * (N : ℝ) ^ (k - 1) := by
      exact_mod_cast hAt_to_A.trans hA_to_deg
    exact hcount_exp.trans hnat
  -- Cancel `N^(k-1) > 0` and absorb `k²` into `C_tot * k^68 * L^16`
  have hNk_split : (N : ℝ) ^ k = (N : ℝ) * (N : ℝ) ^ (k - 1) := by
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1, pow_succ']
  have hNk1_pos : (0 : ℝ) < (N : ℝ) ^ (k - 1) := pow_pos hNpos _
  rw [hNk_split] at hchain_R
  have hN_le1 : exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) * (N : ℝ) ≤
      (k : ℝ) ^ 2 := by
    have h1 : (exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) * (N : ℝ)) *
        (N : ℝ) ^ (k - 1) ≤ (k : ℝ) ^ 2 * (N : ℝ) ^ (k - 1) := by linarith
    exact le_of_mul_le_mul_right h1 hNk1_pos
  have hk2_exp : (k : ℝ) ^ 2 ≤ exp (2 * (2 : ℝ) ^ 16 * (k : ℝ) ^ 68 * L ^ 16) := by
    have hk_exp : (k : ℝ) ≤ exp (k : ℝ) := by linarith [Real.add_one_le_exp (k : ℝ)]
    have hsq : (k : ℝ) ^ 2 ≤ exp (2 * (k : ℝ)) := by
      calc (k : ℝ) ^ 2 ≤ (exp (k : ℝ)) ^ 2 := pow_le_pow_left₀ hk_pos.le hk_exp 2
        _ = exp (2 * (k : ℝ)) := by rw [sq, ← exp_add]; ring_nf
    refine hsq.trans (Real.exp_le_exp.mpr ?_)
    have hL16 : ((2 : ℝ) ^ 16)⁻¹ ≤ L ^ 16 := by
      have := pow_le_pow_left₀ (by norm_num) hL_ge 16
      simpa [one_div, inv_pow] using this
    have hk67 : (1 : ℝ) ≤ (k : ℝ) ^ 67 := one_le_pow₀ (by linarith)
    have h2L : (1 : ℝ) ≤ (2 : ℝ) ^ 16 * L ^ 16 := by
      have := mul_le_mul_of_nonneg_left hL16 (show 0 ≤ (2 : ℝ) ^ 16 by positivity)
      rwa [mul_inv_cancel₀ (by positivity)] at this
    have hprod1 : (k : ℝ) ≤ (k : ℝ) ^ 68 := by
      have := le_mul_of_one_le_right hk_pos.le hk67
      simpa [show (k : ℝ) * (k : ℝ) ^ 67 = (k : ℝ) ^ 68 by ring] using this
    calc 2 * (k : ℝ) ≤ 2 * (k : ℝ) ^ 68 := by linarith
      _ ≤ (2 * (k : ℝ) ^ 68) * ((2 : ℝ) ^ 16 * L ^ 16) :=
          le_mul_of_one_le_right (by positivity) h2L
      _ = 2 * (2 : ℝ) ^ 16 * (k : ℝ) ^ 68 * L ^ 16 := by ring
  have hmul_pos := mul_le_mul_of_nonneg_left hN_le1
    (exp_pos ((K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16)).le
  have hcancel :
      exp ((K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) *
      (exp (-(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) * (N : ℝ)) = (N : ℝ) := by
    rw [← mul_assoc, ← exp_add,
      show (K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16 +
        -(K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16 = 0 by ring,
      exp_zero, one_mul]
  rw [hcancel] at hmul_pos
  calc (N : ℝ)
      ≤ exp ((K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) * (k : ℝ) ^ 2 := hmul_pos
    _ ≤ exp ((K * C_d * C_log + 2 * C_d * C_rho) * (k : ℝ) ^ 68 * L ^ 16) *
          exp (2 * (2 : ℝ) ^ 16 * (k : ℝ) ^ 68 * L ^ 16) :=
        mul_le_mul_of_nonneg_left hk2_exp (exp_pos _).le
    _ = exp (C_tot * (k : ℝ) ^ 68 * L ^ 16) := by
        rw [← exp_add]; dsimp [C_tot]; ring_nf

end OMA.R_Green2_green_2_lower_bound_sanders_R1_H2_R1
