import FormalConjectures.ErdosProblems.«787»
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Reduction of Erdos787.erdos_787.variants.beker

Following Beker (2025, arXiv:2501.10203, §4) and Sanders (2021, §3), we reduce Beker's lower
bound $g(n) \ge (\log n)^{1 + c}$ for all $0 < c < 1/68$ to two canonical additive-combinatorics
theorems:
1. (H1) Disjoint-dilate extraction with polynomial doubling (Beker Prop. 4.2 / Shao Prop. 6.2 /
   Sudakov–Szemerédi–Vu §6).
2. (H2) Quasipolynomial bounds for subsets of odd-order cyclic groups $\mathbb{Z}/N\mathbb{Z}$
   lacking non-degenerate $k$-configurations (Beker Theorem 3.1).

Inside `main`, we prove Choi's $\mathbb{R} \to \mathbb{Z}$ linear-model reduction, Ruzsa's Freiman
2-isomorphism embedding lemma, the near-superset block-selection lemma via Mathlib's
Plünnecke–Ruzsa inequality, and Sanders's iterative top-block amplification.
-/

-- Reduction Erdos787.erdos_787.variants.beker.R1 of Erdős Problem 787 — beker
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

open Filter Finset
open scoped Pointwise Classical Topology NNReal

namespace OMA.R_Erdos787_erdos_787_variants_beker_R1

/- ### Step 1: Ruzsa's Freiman 2-isomorphism embedding lemma -/

lemma ruzsa_embedding (A : Finset ℤ) (_hA : A.Nonempty) (N : ℕ)
    (hN : 2 * (A + A - (A + A)).card < N) :
    ∃ (A' : Finset ℤ) (φ : ℤ → ZMod N),
      A' ⊆ A ∧ A.card ≤ 2 * A'.card ∧
      ∀ a₁ ∈ A', ∀ a₂ ∈ A', ∀ b₁ ∈ A', ∀ b₂ ∈ A',
        a₁ + a₂ = b₁ + b₂ ↔ φ a₁ + φ a₂ = φ b₁ + φ b₂ := by
  have hNpos : 0 < N := by omega
  let M : ℕ := A.sup fun a => a.natAbs
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (4 * M + N + 3)
  have : Fact (Nat.Prime p) := ⟨hp_prime⟩
  have hp_pos : 0 < p := hp_prime.pos
  have hp_ge3 : 3 ≤ p := by omega
  have hp_odd : Odd p := hp_prime.odd_of_ne_two (by omega)
  let D : Finset ℤ := (A + A - (A + A)).erase 0
  have hD_le : D.card ≤ (A + A - (A + A)).card := Finset.card_erase_le
  let U : Finset (ZMod p) := Finset.univ.erase 0
  have hU_card : U.card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  let bad (d : ℤ) : Finset (ZMod p) :=
    U.filter fun r => N ∣ (r * (d : ZMod p)).val ∨ N ∣ (p - (r * (d : ZMod p)).val)
  have hd_ne_zero : ∀ d ∈ D, (d : ZMod p) ≠ 0 := by
    intro d hd hzero
    obtain ⟨hd0, hd_mem⟩ := Finset.mem_erase.mp hd
    rw [Finset.mem_sub] at hd_mem
    obtain ⟨u, hu, v, hv, rfl⟩ := hd_mem
    rw [Finset.mem_add] at hu hv
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hu
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hv
    have hle1 : a₁.natAbs ≤ M := Finset.le_sup (f := fun a : ℤ => a.natAbs) ha₁
    have hle2 : a₂.natAbs ≤ M := Finset.le_sup (f := fun a : ℤ => a.natAbs) ha₂
    have hle3 : b₁.natAbs ≤ M := Finset.le_sup (f := fun a : ℤ => a.natAbs) hb₁
    have hle4 : b₂.natAbs ≤ M := Finset.le_sup (f := fun a : ℤ => a.natAbs) hb₂
    have habs_lt : (a₁ + a₂ - (b₁ + b₂)).natAbs < p := by omega
    have hdvd : (p : ℤ) ∣ (a₁ + a₂ - (b₁ + b₂)) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzero
    have hdvd_nat : p ∣ (a₁ + a₂ - (b₁ + b₂)).natAbs := Int.natCast_dvd.mp hdvd
    have hpos : 0 < (a₁ + a₂ - (b₁ + b₂)).natAbs := Int.natAbs_pos.mpr hd0
    exact absurd (Nat.le_of_dvd hpos hdvd_nat) (by omega)
  have hbad_card : ∀ d ∈ D, (bad d).card ≤ 2 * ((p - 1) / N) := by
    intro d hd
    have hdz : (d : ZMod p) ≠ 0 := hd_ne_zero d hd
    let S : Finset (ZMod p) := U.filter fun t => N ∣ t.val ∨ N ∣ (p - t.val)
    have hcard_eq : (bad d).card = S.card := by
      refine Finset.card_bij (fun r _ => r * (d : ZMod p)) ?_ ?_ ?_
      · intro r hr
        obtain ⟨hrU, hrP⟩ := Finset.mem_filter.mp hr
        have hr0 : r ≠ 0 := (Finset.mem_erase.mp hrU).1
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨mul_ne_zero hr0 hdz, Finset.mem_univ _⟩, hrP⟩
      · intro r₁ _ r₂ _ h
        exact mul_right_cancel₀ hdz h
      · intro t ht
        obtain ⟨htU, htP⟩ := Finset.mem_filter.mp ht
        have ht0 : t ≠ 0 := (Finset.mem_erase.mp htU).1
        refine ⟨t * (d : ZMod p)⁻¹, ?_, by simp [hdz]⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr
          ⟨mul_ne_zero ht0 (inv_ne_zero hdz), Finset.mem_univ _⟩, ?_⟩
        simpa [hdz] using htP
    rw [hcard_eq]
    let S₁ : Finset (ZMod p) := U.filter fun t => N ∣ t.val
    let S₂ : Finset (ZMod p) := U.filter fun t => N ∣ (p - t.val)
    have hsub : S ⊆ S₁ ∪ S₂ := by
      intro t ht
      obtain ⟨htU, h1 | h2⟩ := Finset.mem_filter.mp ht
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨htU, h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htU, h2⟩)
    have hS₁ : S₁.card ≤ (p - 1) / N := by
      have hinj : S₁.card ≤ (Finset.Icc 1 ((p - 1) / N)).card := by
        refine Finset.card_le_card_of_injOn (fun t : ZMod p => t.val / N) ?_ ?_
        · intro t ht
          obtain ⟨htU, hdvd⟩ := Finset.mem_filter.mp ht
          have ht0 : t ≠ 0 := (Finset.mem_erase.mp htU).1
          have hval_pos : 0 < t.val := Nat.pos_of_ne_zero fun h =>
            ht0 ((ZMod.val_eq_zero t).mp h)
          have hval_le : t.val ≤ p - 1 := Nat.le_sub_one_of_lt (ZMod.val_lt t)
          obtain ⟨q, hq⟩ := hdvd
          have hq1 : 1 ≤ q := by
            rcases Nat.eq_zero_or_pos q with rfl | hqp
            · rw [mul_zero] at hq; omega
            · exact hqp
          have hdiv : t.val / N = q := by rw [hq, Nat.mul_div_cancel_left q hNpos]
          rw [Finset.mem_coe, Finset.mem_Icc]
          dsimp only
          rw [hdiv]
          exact ⟨hq1, by rw [← hdiv]; exact Nat.div_le_div_right hval_le⟩
        · intro t₁ ht₁ t₂ ht₂ heq
          dsimp only at heq
          obtain ⟨_, hdvd₁⟩ := Finset.mem_filter.mp ht₁
          obtain ⟨_, hdvd₂⟩ := Finset.mem_filter.mp ht₂
          have hv : t₁.val = t₂.val := by
            rw [← Nat.mul_div_cancel' hdvd₁, ← Nat.mul_div_cancel' hdvd₂, heq]
          exact ZMod.val_injective p hv
      simpa using hinj
    have hS₂ : S₂.card ≤ (p - 1) / N := by
      have hbij : S₂.card = S₁.card := by
        refine Finset.card_bij (fun t _ => -t) ?_ ?_ ?_
        · intro t ht
          obtain ⟨htU, hdvd⟩ := Finset.mem_filter.mp ht
          have ht0 : t ≠ 0 := (Finset.mem_erase.mp htU).1
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨neg_ne_zero.mpr ht0, Finset.mem_univ _⟩, ?_⟩
          rwa [ZMod.neg_val, if_neg ht0]
        · intro t₁ _ t₂ _ h; exact neg_inj.mp h
        · intro t ht
          obtain ⟨htU, hdvd⟩ := Finset.mem_filter.mp ht
          have ht0 : t ≠ 0 := (Finset.mem_erase.mp htU).1
          refine ⟨-t, ?_, neg_neg t⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨neg_ne_zero.mpr ht0, Finset.mem_univ _⟩, ?_⟩
          rw [ZMod.neg_val, if_neg ht0]
          have hlt := ZMod.val_lt t
          rwa [Nat.sub_sub_self hlt.le]
      omega
    calc
      S.card ≤ (S₁ ∪ S₂).card := Finset.card_le_card hsub
      _ ≤ S₁.card + S₂.card := Finset.card_union_le _ _
      _ ≤ 2 * ((p - 1) / N) := by omega
  have hbad_lt : (D.biUnion bad).card < U.card := by
    have hq_pos : 0 < (p - 1) / N := Nat.div_pos (by omega) hNpos
    calc
      (D.biUnion bad).card ≤ ∑ d ∈ D, (bad d).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ D, (2 * ((p - 1) / N)) := Finset.sum_le_sum hbad_card
      _ = D.card * (2 * ((p - 1) / N)) := by simp
      _ ≤ (A + A - (A + A)).card * (2 * ((p - 1) / N)) := Nat.mul_le_mul_right _ hD_le
      _ = (2 * (A + A - (A + A)).card) * ((p - 1) / N) := by ring
      _ < N * ((p - 1) / N) := Nat.mul_lt_mul_of_pos_right hN hq_pos
      _ ≤ p - 1 := Nat.mul_div_le (p - 1) N
      _ = U.card := hU_card.symm
  have hnot_sub : ¬ U ⊆ D.biUnion bad := fun hsub =>
    not_lt_of_ge (Finset.card_le_card hsub) hbad_lt
  obtain ⟨r, hrU, hr_good⟩ := Finset.not_subset.mp hnot_sub
  have hr0 : r ≠ 0 := (Finset.mem_erase.mp hrU).1
  let A₁ : Finset ℤ := A.filter fun a => (r * (a : ZMod p)).val < p / 2
  let A₂ : Finset ℤ := A.filter fun a => p / 2 ≤ (r * (a : ZMod p)).val
  have hcard_split : A₁.card + A₂.card = A.card := by
    have hdisj : Disjoint A₁ A₂ := Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : A₁ ∪ A₂ = A := by
      ext a; simp only [A₁, A₂, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro ha; rcases lt_or_ge (r * (a : ZMod p)).val (p / 2) with h | h
        · exact Or.inl ⟨ha, h⟩
        · exact Or.inr ⟨ha, h⟩
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hA'_ex : ∃ A' : Finset ℤ, A' ⊆ A ∧ A.card ≤ 2 * A'.card ∧
      ∀ a ∈ A', ∀ b ∈ A',
        |((r * (a : ZMod p)).val : ℤ) - ((r * (b : ZMod p)).val : ℤ)| ≤ (p / 2 : ℕ) := by
    rcases le_total A₁.card A₂.card with h | h
    · refine ⟨A₂, Finset.filter_subset _ _, by omega, fun a ha b hb => ?_⟩
      have ha1 := (Finset.mem_filter.mp ha).2
      have hb1 := (Finset.mem_filter.mp hb).2
      have ha2 := ZMod.val_lt (r * (a : ZMod p))
      have hb2 := ZMod.val_lt (r * (b : ZMod p))
      obtain ⟨k, hk⟩ := hp_odd
      rw [abs_le]; constructor <;> omega
    · refine ⟨A₁, Finset.filter_subset _ _, by omega, fun a ha b hb => ?_⟩
      have ha1 := (Finset.mem_filter.mp ha).2
      have hb1 := (Finset.mem_filter.mp hb).2
      rw [abs_le]; constructor <;> omega
  obtain ⟨A', hA'_sub, hA'_card, hA'_diam⟩ := hA'_ex
  let φ : ℤ → ZMod N := fun a => ((r * (a : ZMod p)).val : ZMod N)
  refine ⟨A', φ, hA'_sub, hA'_card, fun a₁ ha₁ a₂ ha₂ b₁ hb₁ b₂ hb₂ => ?_⟩
  let y (a : ℤ) : ℤ := ((r * (a : ZMod p)).val : ℤ)
  let w : ℤ := y a₁ + y a₂ - y b₁ - y b₂
  have hw_lt : |w| < (p : ℤ) := by
    have h1 := hA'_diam a₁ ha₁ b₁ hb₁
    have h2 := hA'_diam a₂ ha₂ b₂ hb₂
    obtain ⟨k, hk⟩ := hp_odd
    have htri : |w| ≤ |y a₁ - y b₁| + |y a₂ - y b₂| := by
      have : w = (y a₁ - y b₁) + (y a₂ - y b₂) := by dsimp [w]; ring
      rw [this]; exact abs_add_le _ _
    dsimp [y] at htri
    omega
  have hw_modp : (w : ZMod p) = r * ((a₁ + a₂ - (b₁ + b₂) : ℤ) : ZMod p) := by
    simp only [w, y, Int.cast_sub, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val]
    ring
  have hw_modN : (w : ZMod N) = (φ a₁ + φ a₂) - (φ b₁ + φ b₂) := by
    simp only [w, y, φ, Int.cast_sub, Int.cast_add, Int.cast_natCast]
    ring
  constructor
  · intro heq
    have hzero_p : (w : ZMod p) = 0 := by
      rw [hw_modp, show a₁ + a₂ - (b₁ + b₂) = 0 by omega, Int.cast_zero, mul_zero]
    have hdvd_p : (p : ℤ) ∣ w := (ZMod.intCast_zmod_eq_zero_iff_dvd w p).mp hzero_p
    have hw0 : w = 0 := by
      by_contra hne
      have hpos : 0 < w.natAbs := Int.natAbs_pos.mpr hne
      have hdvd_n : p ∣ w.natAbs := Int.natCast_dvd.mp hdvd_p
      have hle : p ≤ w.natAbs := Nat.le_of_dvd hpos hdvd_n
      have habs : (w.natAbs : ℤ) = |w| := Int.natCast_natAbs w
      omega
    have hzero_N : (w : ZMod N) = 0 := by rw [hw0, Int.cast_zero]
    rw [hw_modN, sub_eq_zero] at hzero_N
    exact hzero_N
  · intro hφ
    by_contra hne
    let d : ℤ := a₁ + a₂ - (b₁ + b₂)
    have hd0 : d ≠ 0 := by dsimp [d]; omega
    have hd_mem : d ∈ D := by
      refine Finset.mem_erase.mpr ⟨hd0, Finset.mem_sub.mpr
        ⟨a₁ + a₂, Finset.add_mem_add (hA'_sub ha₁) (hA'_sub ha₂),
         b₁ + b₂, Finset.add_mem_add (hA'_sub hb₁) (hA'_sub hb₂), rfl⟩⟩
    have hr_not_bad : ¬ (N ∣ (r * (d : ZMod p)).val ∨ N ∣ (p - (r * (d : ZMod p)).val)) := by
      intro hbad
      apply hr_good
      exact Finset.mem_biUnion.mpr ⟨d, hd_mem, Finset.mem_filter.mpr ⟨hrU, hbad⟩⟩
    have hdvd_N : (N : ℤ) ∣ w := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd w N).mp
      rw [hw_modN, hφ, sub_self]
    have hw_ne : w ≠ 0 := by
      intro hw0
      have h0 : (w : ZMod p) = 0 := by rw [hw0, Int.cast_zero]
      rw [hw_modp] at h0
      exact mul_ne_zero hr0 (hd_ne_zero d hd_mem) h0
    let v : ℕ := (r * (d : ZMod p)).val
    have hv_lt : v < p := ZMod.val_lt _
    have hdiff_modp : ((w - (v : ℤ) : ℤ) : ZMod p) = 0 := by
      rw [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, hw_modp, sub_self]
    have hdvd_p : (p : ℤ) ∣ (w - (v : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hdiff_modp
    obtain ⟨q, hq⟩ := hdvd_p
    have hq_cases : q = 0 ∨ q = -1 := by
      have habs := abs_lt.mp hw_lt
      have : -2 * (p : ℤ) < (p : ℤ) * q ∧ (p : ℤ) * q < (p : ℤ) := by omega
      have hq1 : -2 < q := by nlinarith
      have hq2 : q < 1 := by nlinarith
      omega
    rcases hq_cases with rfl | rfl
    · have hwv : w = (v : ℤ) := by omega
      rw [hwv] at hdvd_N
      exact hr_not_bad (Or.inl (Int.natCast_dvd_natCast.mp hdvd_N))
    · have hwv : -w = ((p - v : ℕ) : ℤ) := by omega
      have hdvd_neg : (N : ℤ) ∣ (-w) := dvd_neg.mpr hdvd_N
      rw [hwv] at hdvd_neg
      exact hr_not_bad (Or.inr (Int.natCast_dvd_natCast.mp hdvd_neg))

/- ### Step 2: Near-superset block-selection lemma from H1, H2, Plünnecke–Ruzsa, and Ruzsa embedding -/

lemma zmod_two_mul_injective {N : ℕ} (hodd : Odd N) :
    Function.Injective (fun z : ZMod N => (2 : ZMod N) * z) := by
  obtain ⟨m, rfl⟩ := hodd
  intro a b hab
  have h2m : ((m + 1 : ℕ) : ZMod (2 * m + 1)) * 2 = 1 := by
    have hnat : ((2 * m + 2 : ℕ) : ZMod (2 * m + 1)) = 1 := by
      have : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self (2 * m + 1)
      push_cast at this ⊢
      linear_combination this
    push_cast at hnat ⊢
    linear_combination hnat
  have := congrArg (fun x => ((m + 1 : ℕ) : ZMod (2 * m + 1)) * x) hab
  simp only [← mul_assoc, h2m, one_mul] at this
  exact this

lemma near_superset_extract
    (h1 : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ k : ℕ in Filter.atTop,
      ∀ X Y : Finset ℤ, X ⊆ Y → Real.exp (k : ℝ) ≤ (X.card : ℝ) →
        (Y.card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * (X.card : ℝ) →
        (∀ S : Finset ℤ, S ⊆ X → S.card = k → ¬ Disjoint S.restrictedSumset Y) →
        ∃ X' : Finset ℤ, X' ⊆ X ∧ X'.Nonempty ∧
          (X.card : ℝ) ≤ C₁ * (k : ℝ) ^ 29 * (X'.card : ℝ) ∧
          ((X' + X').card : ℝ) ≤ C₂ * (k : ℝ) ^ 181 * (X'.card : ℝ) ∧
          Disjoint (X'.image (2 * ·)) Y)
    (h2 : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Odd N → ∀ k : ℕ, 2 ≤ k →
      ∀ A : Finset (ZMod N), A.Nonempty →
        (∀ x : Fin k → ZMod N, Function.Injective x →
          ¬ ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)) →
        (N : ℝ) ≤ Real.exp (C * (k : ℝ) ^ 68 * (Real.log (2 * (N : ℝ) / (A.card : ℝ))) ^ 16)) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ᶠ k : ℕ in Filter.atTop,
      ∀ X Y : Finset ℤ, X ⊆ Y →
        Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) ≤ (X.card : ℝ) →
        (Y.card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * (X.card : ℝ) →
        ∃ S : Finset ℤ, S ⊆ X ∧ S.card = k ∧ Disjoint S.restrictedSumset Y := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hk1⟩ := h1
  obtain ⟨C, hC, hk2⟩ := h2
  let C₀ : ℝ := C * (730 : ℝ) ^ 16 + 2
  have hC₀ : 0 < C₀ := by positivity
  refine ⟨C₀, hC₀, ?_⟩
  have hpow6 : ∀ᶠ k : ℕ in Filter.atTop, 4 * (2 * C₂ ^ 4 + 1) ≤ (k : ℝ) ^ 6 := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ 6) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 6 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop _)
  have hexp_dom : ∀ᶠ k : ℕ in Filter.atTop, 2 * C₁ * (k : ℝ) ^ 29 < Real.exp (k : ℝ) := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ 29 * Real.exp (-(k : ℝ))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 29).comp tendsto_natCast_atTop_atTop
    have hlt := ht.eventually (gt_mem_nhds (show (0 : ℝ) < (2 * C₁)⁻¹ by positivity))
    refine hlt.mono fun k hk => ?_
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (Real.exp_pos _)] at hk
    have := mul_lt_mul_of_pos_left hk (show 0 < 2 * C₁ by positivity)
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
    linarith
  filter_upwards [hk1, hpow6, hexp_dom, eventually_ge_atTop 4] with k h1k hpow6k hexpk hk4
  intro X Y hXY hXbig hYle
  by_contra hno
  push Not at hno
  have hk_pos : (0 : ℝ) < k := by positivity
  have hlogk_ge1 : (1 : ℝ) ≤ Real.log (k : ℝ) := by
    have he4 : Real.exp 1 ≤ (k : ℝ) := by
      have h1 := Real.exp_one_lt_d9
      have h2 : (4 : ℝ) ≤ k := by exact_mod_cast hk4
      linarith
    have := Real.log_le_log (Real.exp_pos 1) he4
    rwa [Real.log_exp] at this
  have hpow68_ge : (k : ℝ) ≤ (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have h1 : (k : ℝ) ≤ (k : ℝ) ^ 68 := by
      calc (k : ℝ) = (k : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (k : ℝ) ^ 68 := pow_le_pow_right₀ hk1 (by norm_num)
    have h2 : (1 : ℝ) ≤ (Real.log (k : ℝ)) ^ 16 := one_le_pow₀ hlogk_ge1
    nlinarith
  have hXexpk : Real.exp (k : ℝ) ≤ (X.card : ℝ) := by
    have hle : (k : ℝ) ≤ C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 := by
      have : (1 : ℝ) ≤ C₀ := by dsimp [C₀]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ 730 by norm_num) 16]
      nlinarith
    exact (Real.exp_le_exp.mpr hle).trans hXbig
  obtain ⟨X', hX'X, hX'ne, hX'lo, hX'dbl, hX'disj⟩ := h1k X Y hXY hXexpk hYle hno
  have hX'pos : (0 : ℝ) < (X'.card : ℝ) := by exact_mod_cast hX'ne.card_pos
  have hPR_nnq : ((2 • X' - 2 • X').card : ℚ≥0) ≤
      (((X' + X').card : ℚ≥0) / (X'.card : ℚ≥0)) ^ (2 + 2) * (X'.card : ℚ≥0) :=
    Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hX'ne X' 2 2
  have h2nsmul : 2 • X' = X' + X' := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, add_nsmul, one_nsmul]
  rw [h2nsmul] at hPR_nnq
  have hPR : ((X' + X' - (X' + X')).card : ℝ) ≤
      (((X' + X').card : ℝ) / (X'.card : ℝ)) ^ 4 * (X'.card : ℝ) := by
    have hcast := NNReal.coe_le_coe.mpr (show (((X' + X' - (X' + X')).card : ℚ≥0) : ℝ≥0) ≤
      ((((X' + X').card : ℚ≥0) / (X'.card : ℚ≥0)) ^ 4 * (X'.card : ℚ≥0) : ℚ≥0) by
        exact_mod_cast hPR_nnq)
    simpa using hcast
  have h2X2X : ((X' + X' - (X' + X')).card : ℝ) ≤
      C₂ ^ 4 * (k : ℝ) ^ 724 * (X'.card : ℝ) := by
    have hdiv : ((X' + X').card : ℝ) / (X'.card : ℝ) ≤ C₂ * (k : ℝ) ^ 181 :=
      (div_le_iff₀ hX'pos).mpr hX'dbl
    have hpow4 : (((X' + X').card : ℝ) / (X'.card : ℝ)) ^ 4 ≤ (C₂ * (k : ℝ) ^ 181) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hdiv 4
    have hmul := mul_le_mul_of_nonneg_right hpow4 hX'pos.le
    calc
      ((X' + X' - (X' + X')).card : ℝ)
          ≤ (((X' + X').card : ℝ) / (X'.card : ℝ)) ^ 4 * (X'.card : ℝ) := hPR
      _ ≤ (C₂ * (k : ℝ) ^ 181) ^ 4 * (X'.card : ℝ) := hmul
      _ = C₂ ^ 4 * (k : ℝ) ^ 724 * (X'.card : ℝ) := by ring
  let N : ℕ := 2 * (X' + X' - (X' + X')).card + 1
  have hN_odd : Odd N := ⟨(X' + X' - (X' + X')).card, rfl⟩
  have : NeZero N := ⟨by dsimp [N]; omega⟩
  have hN_gt : 2 * (X' + X' - (X' + X')).card < N := by dsimp [N]; omega
  obtain ⟨X'', φ, hX''sub, hX''card, hφ_iso⟩ := ruzsa_embedding X' hX'ne N hN_gt
  have hφ_inj : Set.InjOn φ (X'' : Set ℤ) := by
    intro a ha b hb hab
    have h1 := (hφ_iso a ha a ha b hb b hb).mpr (by rw [hab])
    omega
  let A : Finset (ZMod N) := X''.image φ
  have hA_card : A.card = X''.card := Finset.card_image_of_injOn hφ_inj
  have hX''pos : 0 < X''.card := by
    have := hX'ne.card_pos; omega
  have hA_ne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hA_no_kconfig : ∀ x : Fin k → ZMod N, Function.Injective x →
      ¬ ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·) := by
    intro x hx_inj hx_cfg
    have hmemA : ∀ i : Fin k, x i ∈ A := by
      intro i
      obtain ⟨a, ha, h2a⟩ := Finset.mem_image.mp (hx_cfg i i)
      have heq : (2 : ZMod N) * a = (2 : ZMod N) * x i := by
        calc (2 : ZMod N) * a = x i + x i := h2a
          _ = (2 : ZMod N) * x i := by ring
      rwa [← zmod_two_mul_injective hN_odd heq]
    have hex_y : ∀ i : Fin k, ∃ y ∈ X'', φ y = x i := fun i =>
      Finset.mem_image.mp (hmemA i)
    choose y hy_mem hy_eq using hex_y
    have hy_inj : Function.Injective y := by
      intro i j hij
      apply hx_inj
      rw [← hy_eq i, ← hy_eq j, hij]
    let S : Finset ℤ := Finset.univ.image y
    have hS_sub : S ⊆ X := by
      intro s hs
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs
      exact hX'X (hX''sub (hy_mem i))
    have hS_card : S.card = k := by
      rw [Finset.card_image_of_injective _ hy_inj, Finset.card_univ, Fintype.card_fin]
    have hS_disj : Disjoint S.restrictedSumset Y := by
      rw [Finset.disjoint_left]
      intro u hu huY
      obtain ⟨⟨s₁, s₂⟩, hmem_off, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hs₁, hs₂, _⟩ := Finset.mem_offDiag.mp hmem_off
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hs₁
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hs₂
      obtain ⟨a, haA, h2a⟩ := Finset.mem_image.mp (hx_cfg i j)
      obtain ⟨z, hzX'', rfl⟩ := Finset.mem_image.mp haA
      have hφ_sum : φ (y i) + φ (y j) = φ z + φ z := by
        rw [hy_eq i, hy_eq j, ← h2a]; ring
      have hsum_eq : y i + y j = z + z :=
        (hφ_iso (y i) (hy_mem i) (y j) (hy_mem j) z hzX'' z hzX'').mpr hφ_sum
      have h2z : y i + y j ∈ X'.image (2 * ·) :=
        Finset.mem_image.mpr ⟨z, hX''sub hzX'', by omega⟩
      exact Finset.disjoint_left.mp hX'disj h2z huY
    exact hno S hS_sub hS_card hS_disj
  have hN_ub := hk2 N hN_odd k (by omega) A hA_ne hA_no_kconfig
  have hN_card_le : (N : ℝ) ≤ (2 * C₂ ^ 4 + 1) * (k : ℝ) ^ 724 * (X'.card : ℝ) := by
    have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 724 * (X'.card : ℝ) := by
      have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 724 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
      have hX'1 : (1 : ℝ) ≤ (X'.card : ℝ) := by exact_mod_cast hX'ne.card_pos
      nlinarith
    have hNcast : (N : ℝ) = 2 * ((X' + X' - (X' + X')).card : ℝ) + 1 := by
      dsimp [N]; push_cast; ring
    linarith
  have hratio : 2 * (N : ℝ) / (A.card : ℝ) ≤ (k : ℝ) ^ 730 := by
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
    have hA2 : (X'.card : ℝ) ≤ 2 * (A.card : ℝ) := by
      rw [hA_card]; exact_mod_cast hX''card
    rw [div_le_iff₀ hApos]
    calc
      2 * (N : ℝ) ≤ 2 * ((2 * C₂ ^ 4 + 1) * (k : ℝ) ^ 724 * (X'.card : ℝ)) := by linarith
      _ ≤ 2 * ((2 * C₂ ^ 4 + 1) * (k : ℝ) ^ 724 * (2 * (A.card : ℝ))) := by
            gcongr
      _ = (4 * (2 * C₂ ^ 4 + 1)) * (k : ℝ) ^ 724 * (A.card : ℝ) := by ring
      _ ≤ (k : ℝ) ^ 6 * (k : ℝ) ^ 724 * (A.card : ℝ) := by gcongr
      _ = (k : ℝ) ^ 730 * (A.card : ℝ) := by ring
  have hN_ge_A : (A.card : ℝ) ≤ (N : ℝ) := by
    have hle : A.card ≤ Fintype.card (ZMod N) := Finset.card_le_univ A
    rw [ZMod.card] at hle
    exact_mod_cast hle
  have hlog_ratio : Real.log (2 * (N : ℝ) / (A.card : ℝ)) ≤ 730 * Real.log (k : ℝ) := by
    have hpos : 0 < 2 * (N : ℝ) / (A.card : ℝ) := by
      have hApos : (0 : ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
      have hNpos : (0 : ℝ) < N := by dsimp [N]; positivity
      positivity
    calc
      Real.log (2 * (N : ℝ) / (A.card : ℝ)) ≤ Real.log ((k : ℝ) ^ 730) :=
        Real.log_le_log hpos hratio
      _ = 730 * Real.log (k : ℝ) := by rw [Real.log_pow]; ring
  have hlog_nn : 0 ≤ Real.log (2 * (N : ℝ) / (A.card : ℝ)) := by
    apply Real.log_nonneg
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast (by omega : 0 < A.card)
    rw [le_div_iff₀ hApos]; linarith
  have hN_ub2 : (N : ℝ) ≤ Real.exp ((C * (730 : ℝ) ^ 16) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) := by
    refine hN_ub.trans (Real.exp_le_exp.mpr ?_)
    have hpow16 : (Real.log (2 * (N : ℝ) / (A.card : ℝ))) ^ 16 ≤ (730 * Real.log (k : ℝ)) ^ 16 :=
      pow_le_pow_left₀ hlog_nn hlog_ratio 16
    calc
      C * (k : ℝ) ^ 68 * (Real.log (2 * (N : ℝ) / (A.card : ℝ))) ^ 16
          ≤ C * (k : ℝ) ^ 68 * (730 * Real.log (k : ℝ)) ^ 16 := by gcongr
      _ = (C * (730 : ℝ) ^ 16) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 := by ring
  have hN_lb : Real.exp ((C * (730 : ℝ) ^ 16 + 1) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) < (N : ℝ) := by
    have hA2 : (X'.card : ℝ) ≤ 2 * (A.card : ℝ) := by
      rw [hA_card]; exact_mod_cast hX''card
    have hX_le_N : (X.card : ℝ) ≤ (2 * C₁ * (k : ℝ) ^ 29) * (N : ℝ) := by
      calc
        (X.card : ℝ) ≤ C₁ * (k : ℝ) ^ 29 * (X'.card : ℝ) := hX'lo
        _ ≤ C₁ * (k : ℝ) ^ 29 * (2 * (A.card : ℝ)) := by gcongr
        _ ≤ C₁ * (k : ℝ) ^ 29 * (2 * (N : ℝ)) := by gcongr
        _ = (2 * C₁ * (k : ℝ) ^ 29) * (N : ℝ) := by ring
    have hexp_lt : 2 * C₁ * (k : ℝ) ^ 29 < Real.exp ((k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) :=
      lt_of_lt_of_le hexpk (Real.exp_le_exp.mpr hpow68_ge)
    have hNpos : (0 : ℝ) < N := by dsimp [N]; positivity
    have hprod : (2 * C₁ * (k : ℝ) ^ 29) * (N : ℝ) <
        Real.exp ((k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) * (N : ℝ) :=
      mul_lt_mul_of_pos_right hexp_lt hNpos
    have hbig : Real.exp ((k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) *
        Real.exp ((C * (730 : ℝ) ^ 16 + 1) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) ≤ (X.card : ℝ) := by
      rw [← Real.exp_add]
      have heq : (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 +
          (C * (730 : ℝ) ^ 16 + 1) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 =
          C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 := by dsimp [C₀]; ring
      rw [heq]; exact hXbig
    have hlt_mul : Real.exp ((k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) *
        Real.exp ((C * (730 : ℝ) ^ 16 + 1) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) <
        Real.exp ((k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) * (N : ℝ) :=
      lt_of_le_of_lt (hbig.trans hX_le_N) hprod
    exact (mul_lt_mul_iff_right₀ (Real.exp_pos _)).mp hlt_mul
  have hlt_exp : Real.exp ((C * (730 : ℝ) ^ 16) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) <
      Real.exp ((C * (730 : ℝ) ^ 16 + 1) * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) := by
    apply Real.exp_lt_exp.mpr
    have : 0 < (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 := by positivity
    linarith
  linarith

/- ### Step 3: Sanders's iterative top-block amplification -/

lemma iterative_block_amplification
    {k m D : ℕ} (hk : 2 ≤ k) (_hD : 1 ≤ D)
    (hBlock : ∀ X Y : Finset ℤ, X ⊆ Y → D ≤ X.card →
      (Y.card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * (X.card : ℝ) →
      ∃ S : Finset ℤ, S ⊆ X ∧ S.card = k ∧ Disjoint S.restrictedSumset Y)
    (A : Finset ℤ) (hA_pos : ∀ a ∈ A, 0 < a)
    (hA_card : 2 * D * (2 * k ^ 29 * (m * k + 1)) ^ m ≤ A.card) :
    ∃ S : Finset ℤ, S ⊆ A ∧ S.card = m * k ∧ Disjoint S.restrictedSumset A := by
  let l : ℕ := k ^ 29
  have hl1 : 1 ≤ l := Nat.one_le_pow 29 k (by omega)
  let q : ℕ := 2 * l * (m * k + 1)
  have hq1 : 1 ≤ q := Nat.mul_pos (Nat.mul_pos (by norm_num) hl1) (Nat.succ_pos _)
  let sz : ℕ → ℕ := fun i => 2 * D * q ^ i
  have hsz_mono : ∀ {i j}, i ≤ j → sz i ≤ sz j := fun hij =>
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq1 hij)
  have hsz_le_A : ∀ {i}, i ≤ m → sz i ≤ A.card := fun hi =>
    (hsz_mono hi).trans hA_card
  let e : Fin A.card ↪o ℤ := A.orderEmbOfFin rfl
  let Z : ℕ → Finset ℤ := fun i =>
    (Finset.univ.filter fun idx : Fin A.card => A.card - sz i ≤ idx.val).image e
  have hZ_sub_A : ∀ i, Z i ⊆ A := by
    intro i x hx
    obtain ⟨idx, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.orderEmbOfFin_mem A rfl idx
  have hZ_card : ∀ {i}, i ≤ m → (Z i).card = sz i := by
    intro i hi
    have hle := hsz_le_A hi
    rw [Finset.card_image_of_injective _ e.injective]
    have hbij : (Finset.univ.filter fun idx : Fin A.card => A.card - sz i ≤ idx.val).card =
        (Finset.Ico (A.card - sz i) A.card).card := by
      refine Finset.card_bij (fun idx _ => idx.val) ?_ ?_ ?_
      · intro idx hidx
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hidx).2, idx.isLt⟩
      · intro idx₁ _ idx₂ _ h; exact Fin.ext h
      · intro t ht
        obtain ⟨ht1, ht2⟩ := Finset.mem_Ico.mp ht
        exact ⟨⟨t, ht2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1⟩, rfl⟩
    rw [hbij, Nat.card_Ico]; omega
  have hZ_mono : ∀ {i j}, i ≤ j → Z i ⊆ Z j := by
    intro i j hij x hx
    obtain ⟨idx, hidx, rfl⟩ := Finset.mem_image.mp hx
    have hle : sz i ≤ sz j := hsz_mono hij
    refine Finset.mem_image.mpr ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have := (Finset.mem_filter.mp hidx).2
    omega
  have hZ_upward : ∀ i x y, x ∈ Z i → y ∈ A → x ≤ y → y ∈ Z i := by
    intro i x y hx hy hxy
    obtain ⟨ix, hix, rfl⟩ := Finset.mem_image.mp hx
    have hmem_range : y ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; exact hy
    obtain ⟨iy, rfl⟩ := hmem_range
    have hidx : ix ≤ iy := e.le_iff_le.mp hxy
    refine Finset.mem_image.mpr ⟨iy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have := (Finset.mem_filter.mp hix).2
    exact le_trans this hidx
  have hstep : ∀ r ≤ m, ∃ S : Finset ℤ,
      S ⊆ A ∧ S.card = r * k ∧ Disjoint S.restrictedSumset A ∧
      (∀ t : ℕ, r = t + 1 → S ⊆ Z t) := by
    intro r hr
    induction r with
    | zero =>
      refine ⟨∅, Finset.empty_subset _, by simp, by simp [Finset.restrictedSumset], ?_⟩
      intro t ht; omega
    | succ r ih =>
      obtain ⟨S_prev, hSp_A, hSp_card, hSp_disj, hSp_Z⟩ := ih (by omega)
      cases r with
      | zero =>
        have hZ0_card : (Z 0).card = 2 * D := by simpa [sz] using hZ_card (show 0 ≤ m by omega)
        have hY_le : ((Z 0).card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * ((Z 0).card : ℝ) := by
          have : 0 ≤ ((k : ℝ) ^ 29)⁻¹ := by positivity
          nlinarith [Nat.cast_nonneg (α := ℝ) (Z 0).card]
        obtain ⟨S₀, hS₀_sub, hS₀_card, hS₀_disj⟩ := hBlock (Z 0) (Z 0) Subset.rfl (by omega) hY_le
        refine ⟨S₀, hS₀_sub.trans (hZ_sub_A 0), by simpa using hS₀_card, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro u hu huA
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
          have hb_pos : 0 < b := hA_pos b (hZ_sub_A 0 (hS₀_sub hb))
          have huZ : a + b ∈ Z 0 := hZ_upward 0 a (a + b) (hS₀_sub ha) huA (by omega)
          exact Finset.disjoint_left.mp hS₀_disj hu huZ
        · intro t ht
          have ht0 : t = 0 := by omega
          subst ht0
          exact hS₀_sub
      | succ t =>
        have hSp_Zt : S_prev ⊆ Z t := hSp_Z t rfl
        let Bad : Finset ℤ := Z t ∪ (Z t).biUnion fun z => S_prev.image fun s => z - s
        let X : Finset ℤ := Z (t + 1) \ Bad
        let Y : Finset ℤ := Z (t + 1)
        have hBad_card : Bad.card ≤ (Z t).card * (m * k + 1) := by
          have h1 : Bad.card ≤ (Z t).card + ((Z t).biUnion fun z => S_prev.image fun s => z - s).card :=
            Finset.card_union_le _ _
          have h2 : ((Z t).biUnion fun z => S_prev.image fun s => z - s).card ≤
              ∑ z ∈ Z t, (S_prev.image fun s => z - s).card := Finset.card_biUnion_le
          have h3 : ∑ z ∈ Z t, (S_prev.image fun s => z - s).card ≤ (Z t).card * S_prev.card := by
            calc
              ∑ z ∈ Z t, (S_prev.image fun s => z - s).card
                  ≤ ∑ _ ∈ Z t, S_prev.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
              _ = (Z t).card * S_prev.card := by simp
          have h4 : S_prev.card ≤ m * k := by
            rw [hSp_card]; exact Nat.mul_le_mul_right k (by omega)
          calc
            Bad.card ≤ (Z t).card + (Z t).card * S_prev.card := by omega
            _ ≤ (Z t).card + (Z t).card * (m * k) := Nat.add_le_add_left (Nat.mul_le_mul_left _ h4) _
            _ = (Z t).card * (m * k + 1) := by ring
        have hZt_card : (Z t).card = sz t := hZ_card (by omega)
        have hY_card : Y.card = sz (t + 1) := hZ_card (by omega)
        have hY_eq : Y.card = 2 * l * (m * k + 1) * (Z t).card := by
          rw [hY_card, hZt_card]; dsimp [sz, q]; rw [pow_succ]; ring
        have h2lBad : 2 * l * Bad.card ≤ Y.card := by
          calc
            2 * l * Bad.card ≤ 2 * l * ((Z t).card * (m * k + 1)) := Nat.mul_le_mul_left _ hBad_card
            _ = 2 * l * (m * k + 1) * (Z t).card := by ring
            _ = Y.card := hY_eq.symm
        have hYX : Y.card ≤ X.card + Bad.card := by
          have := Finset.card_le_card (show Y ⊆ X ∪ Bad by
            intro x hx; by_cases hxb : x ∈ Bad
            · exact Finset.mem_union_right _ hxb
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxb⟩))
          exact this.trans (Finset.card_union_le _ _)
        have hX_ge_D : D ≤ X.card := by
          have hY_ge : 2 * D ≤ Y.card := by
            rw [hY_card]; dsimp [sz]
            have : 1 ≤ q ^ (t + 1) := Nat.one_le_pow _ _ hq1
            nlinarith
          have h2Bad : 2 * Bad.card ≤ Y.card := by nlinarith
          omega
        have hY_le_X : (Y.card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * (X.card : ℝ) := by
          have h1 : (2 * (l : ℝ) - 1) * (Y.card : ℝ) ≤ 2 * (l : ℝ) * (X.card : ℝ) := by
            have h2lR : 2 * (l : ℝ) * (Bad.card : ℝ) ≤ (Y.card : ℝ) := by exact_mod_cast h2lBad
            have hYXR : (Y.card : ℝ) ≤ (X.card : ℝ) + (Bad.card : ℝ) := by exact_mod_cast hYX
            nlinarith
          have hlR_ge1 : (1 : ℝ) ≤ l := by exact_mod_cast hl1
          have hlR_pos : (0 : ℝ) < l := by positivity
          have hl_eq : ((k : ℝ) ^ 29) = (l : ℝ) := by dsimp [l]; push_cast; rfl
          rw [hl_eq]
          have h2 : (l : ℝ) * (Y.card : ℝ) ≤ ((l : ℝ) + 1) * (X.card : ℝ) := by
            have h2l_pos : 0 < 2 * (l : ℝ) - 1 := by linarith
            have hstep1 : 2 * (l : ℝ) * (l : ℝ) ≤ ((l : ℝ) + 1) * (2 * (l : ℝ) - 1) := by nlinarith
            have hmul_l : (2 * (l : ℝ) - 1) * ((l : ℝ) * (Y.card : ℝ)) ≤
                2 * (l : ℝ) * (l : ℝ) * (X.card : ℝ) := by
              calc
                (2 * (l : ℝ) - 1) * ((l : ℝ) * (Y.card : ℝ))
                    = (l : ℝ) * ((2 * (l : ℝ) - 1) * (Y.card : ℝ)) := by ring
                _ ≤ (l : ℝ) * (2 * (l : ℝ) * (X.card : ℝ)) :=
                      mul_le_mul_of_nonneg_left h1 hlR_pos.le
                _ = 2 * (l : ℝ) * (l : ℝ) * (X.card : ℝ) := by ring
            have hmul_r : 2 * (l : ℝ) * (l : ℝ) * (X.card : ℝ) ≤
                (2 * (l : ℝ) - 1) * (((l : ℝ) + 1) * (X.card : ℝ)) := by
              have := mul_le_mul_of_nonneg_right hstep1 (Nat.cast_nonneg (α := ℝ) X.card)
              linarith
            exact le_of_mul_le_mul_left (hmul_l.trans hmul_r) h2l_pos
          have h3 : (1 + (l : ℝ)⁻¹) * (X.card : ℝ) = ((l : ℝ) + 1) * (X.card : ℝ) / (l : ℝ) := by
            field_simp
          rw [h3, le_div_iff₀ hlR_pos]
          linarith
        obtain ⟨S_new, hSn_X, hSn_card, hSn_disj⟩ := hBlock X Y Finset.sdiff_subset hX_ge_D hY_le_X
        have hdisj_sets : Disjoint S_prev S_new := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have hxb : x ∈ Bad := Finset.mem_union_left _ (hSp_Zt hx1)
          exact (Finset.mem_sdiff.mp (hSn_X hx2)).2 hxb
        refine ⟨S_prev ∪ S_new, Finset.union_subset hSp_A ((hSn_X.trans Finset.sdiff_subset).trans (hZ_sub_A (t + 1))), ?_, ?_, ?_⟩
        · rw [Finset.card_union_of_disjoint hdisj_sets, hSp_card, hSn_card]; ring
        · rw [Finset.disjoint_left]
          intro u hu huA
          obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
          rcases Finset.mem_union.mp ha with ha1 | ha2 <;> rcases Finset.mem_union.mp hb with hb1 | hb2
          · have : a + b ∈ S_prev.restrictedSumset :=
              Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha1, hb1, hne⟩, rfl⟩
            exact Finset.disjoint_left.mp hSp_disj this huA
          · have hb_pos : 0 < b := hA_pos b ((hSn_X.trans Finset.sdiff_subset).trans (hZ_sub_A (t + 1)) hb2)
            have hab_Zt : a + b ∈ Z t := hZ_upward t a (a + b) (hSp_Zt ha1) huA (by omega)
            have hb_bad : b ∈ Bad := Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨a + b, hab_Zt, Finset.mem_image.mpr ⟨a, ha1, by omega⟩⟩)
            exact (Finset.mem_sdiff.mp (hSn_X hb2)).2 hb_bad
          · have ha_pos : 0 < a := hA_pos a ((hSn_X.trans Finset.sdiff_subset).trans (hZ_sub_A (t + 1)) ha2)
            have hab_Zt : a + b ∈ Z t := hZ_upward t b (a + b) (hSp_Zt hb1) huA (by omega)
            have ha_bad : a ∈ Bad := Finset.mem_union_right _
              (Finset.mem_biUnion.mpr ⟨a + b, hab_Zt, Finset.mem_image.mpr ⟨b, hb1, by omega⟩⟩)
            exact (Finset.mem_sdiff.mp (hSn_X ha2)).2 ha_bad
          · have hb_pos : 0 < b := hA_pos b ((hSn_X.trans Finset.sdiff_subset).trans (hZ_sub_A (t + 1)) hb2)
            have hab_Y : a + b ∈ Y :=
              hZ_upward (t + 1) a (a + b) (Finset.sdiff_subset (hSn_X ha2)) huA (by omega)
            have : a + b ∈ S_new.restrictedSumset :=
              Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha2, hb2, hne⟩, rfl⟩
            exact Finset.disjoint_left.mp hSn_disj this hab_Y
        · intro u hu
          have : u = t + 1 := by omega
          subst this
          exact Finset.union_subset (hSp_Zt.trans (hZ_mono (by omega))) (hSn_X.trans Finset.sdiff_subset)
  obtain ⟨S, hSA, hScard, hSdisj, _⟩ := hstep m le_rfl
  exact ⟨S, hSA, hScard, hSdisj⟩

/- ### Step 4: Sign reduction and asymptotic parameter optimization -/

lemma reduce_to_positive_half (A : Finset ℤ) :
    ∃ A' : Finset ℤ, (∀ a ∈ A', 0 < a) ∧ (A.card - 1) / 2 ≤ A'.card ∧
      ∀ S : Finset ℤ, S ⊆ A' → Disjoint S.restrictedSumset A' →
        ∃ T : Finset ℤ, T ⊆ A ∧ T.card = S.card ∧ Disjoint T.restrictedSumset A := by
  let Apos : Finset ℤ := A.filter fun a => 0 < a
  let Aneg : Finset ℤ := (A.filter fun a => a < 0).image fun a => -a
  have hpart : (A.erase 0).card = Apos.card + (A.filter fun a => a < 0).card := by
    have hdisj : Disjoint Apos (A.filter fun a => a < 0) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hunion : Apos ∪ (A.filter fun a => a < 0) = A.erase 0 := by
      ext a; simp only [Apos, Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro (⟨hA, h⟩ | ⟨hA, h⟩) <;> exact ⟨by omega, hA⟩
      · rintro ⟨hne, hA⟩; rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inr ⟨hA, h⟩
        · exact Or.inl ⟨hA, h⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hAneg_card : Aneg.card = (A.filter fun a => a < 0).card :=
    Finset.card_image_of_injective _ neg_injective
  have herase : A.card - 1 ≤ (A.erase 0).card := by
    by_cases h0 : (0 : ℤ) ∈ A
    · rw [Finset.card_erase_of_mem h0]
    · rw [Finset.erase_eq_of_notMem h0]; omega
  rcases le_total Aneg.card Apos.card with h | h
  · refine ⟨Apos, fun a ha => (Finset.mem_filter.mp ha).2, by omega, fun S hS hdisj => ?_⟩
    refine ⟨S, hS.trans (Finset.filter_subset _ _), rfl, ?_⟩
    rw [Finset.disjoint_left]
    intro u hu huA
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨ha, hb, _⟩ := Finset.mem_offDiag.mp hab
    have ha_pos : 0 < a := (Finset.mem_filter.mp (hS ha)).2
    have hb_pos : 0 < b := (Finset.mem_filter.mp (hS hb)).2
    exact Finset.disjoint_left.mp hdisj hu (Finset.mem_filter.mpr ⟨huA, by omega⟩)
  · refine ⟨Aneg, ?_, by omega, fun S hS hdisj => ?_⟩
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      have := (Finset.mem_filter.mp hx).2; omega
    · refine ⟨S.image fun x => -x, ?_, Finset.card_image_of_injective _ neg_injective, ?_⟩
      · intro t ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨x, hx, hxs⟩ := Finset.mem_image.mp (hS hs)
        have htx : -s = x := by omega
        rw [htx]; exact (Finset.mem_filter.mp hx).1
      · rw [Finset.disjoint_left]
        intro u hu huA
        obtain ⟨⟨t₁, t₂⟩, ht, rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨ht₁, ht₂, hne⟩ := Finset.mem_offDiag.mp ht
        obtain ⟨s₁, hs₁, rfl⟩ := Finset.mem_image.mp ht₁
        obtain ⟨s₂, hs₂, rfl⟩ := Finset.mem_image.mp ht₂
        have hs₁_pos : 0 < s₁ := by
          obtain ⟨x, hx, hxs⟩ := Finset.mem_image.mp (hS hs₁)
          have := (Finset.mem_filter.mp hx).2; omega
        have hs₂_pos : 0 < s₂ := by
          obtain ⟨x, hx, hxs⟩ := Finset.mem_image.mp (hS hs₂)
          have := (Finset.mem_filter.mp hx).2; omega
        have hmem_neg : s₁ + s₂ ∈ Aneg :=
          Finset.mem_image.mpr ⟨-s₁ + -s₂, Finset.mem_filter.mpr ⟨huA, by omega⟩, by omega⟩
        have hmem_sum : s₁ + s₂ ∈ S.restrictedSumset :=
          Finset.mem_image.mpr ⟨(s₁, s₂), Finset.mem_offDiag.mpr ⟨hs₁, hs₂, fun h => by
            dsimp only at h
            exact hne (by dsimp only; rw [h])⟩, rfl⟩
        exact Finset.disjoint_left.mp hdisj hmem_sum hmem_neg

lemma asymptotic_parameters (c C₀ : ℝ) (hc : 0 < c) (hc68 : c < 1 / 68) (hC₀ : 0 < C₀) (K₀ : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ k m D : ℕ,
      K₀ ≤ k ∧ 2 ≤ k ∧ 1 ≤ m ∧ 1 ≤ D ∧
      Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) ≤ (D : ℝ) ∧
      2 * D * (2 * k ^ 29 * (m * k + 1)) ^ m ≤ (n - 1) / 2 ∧
      Real.log (n : ℝ) ^ (1 + c) ≤ ((m * k : ℕ) : ℝ) := by
  let δ : ℝ := (1 / 68 - c) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let α : ℝ := c + δ
  have hα_pos : 0 < α := by dsimp [α]; linarith
  have hα_lt : α < 1 / 68 := by dsimp [α, δ]; linarith
  have h68α : 68 * α < 1 := by linarith
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in atTop,
      C₀ * (Real.log (n : ℝ)) ^ (68 * α) * (Real.log (Real.log (n : ℝ))) ^ 16 ≤
        (1 / 4 : ℝ) * Real.log (n : ℝ) := by
    have ho := (isLittleO_log_rpow_rpow_atTop (16 : ℝ) (show (0 : ℝ) < 1 - 68 * α by linarith)).bound
      (show (0 : ℝ) < 1 / (4 * C₀) by positivity)
    filter_upwards [hlog_top.eventually ho, hlog_top.eventually (eventually_gt_atTop (Real.exp 1))] with n hn hL
    have hLpos : 0 < Real.log (n : ℝ) := lt_trans (Real.exp_pos 1) hL
    have hlogL_pos : 0 < Real.log (Real.log (n : ℝ)) := by
      have := Real.log_lt_log (Real.exp_pos 1) hL
      rw [Real.log_exp] at this
      linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogL_pos.le _),
        Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le _)] at hn
    have hmul : C₀ * (Real.log (Real.log (n : ℝ))) ^ (16 : ℝ) ≤
        (1 / 4 : ℝ) * (Real.log (n : ℝ)) ^ (1 - 68 * α) := by
      have htmp := mul_le_mul_of_nonneg_left hn hC₀.le
      have hcoef : C₀ * (1 / (4 * C₀)) = 1 / 4 := by field_simp
      rw [← mul_assoc, hcoef] at htmp
      exact htmp
    have hpow_add : (Real.log (n : ℝ)) ^ (68 * α) * (Real.log (n : ℝ)) ^ (1 - 68 * α) =
        Real.log (n : ℝ) := by
      rw [← Real.rpow_add hLpos]; ring_nf; exact Real.rpow_one _
    have h16 : (Real.log (Real.log (n : ℝ))) ^ (16 : ℕ) = (Real.log (Real.log (n : ℝ))) ^ (16 : ℝ) :=
      (Real.rpow_natCast _ 16).symm
    rw [h16]
    calc
      C₀ * (Real.log (n : ℝ)) ^ (68 * α) * (Real.log (Real.log (n : ℝ))) ^ (16 : ℝ)
          = (Real.log (n : ℝ)) ^ (68 * α) * (C₀ * (Real.log (Real.log (n : ℝ))) ^ (16 : ℝ)) := by ring
      _ ≤ (Real.log (n : ℝ)) ^ (68 * α) * ((1 / 4 : ℝ) * (Real.log (n : ℝ)) ^ (1 - 68 * α)) :=
            mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hLpos.le _)
      _ = (1 / 4 : ℝ) * ((Real.log (n : ℝ)) ^ (68 * α) * (Real.log (n : ℝ)) ^ (1 - 68 * α)) := by ring
      _ = (1 / 4 : ℝ) * Real.log (n : ℝ) := by rw [hpow_add]
  have h2 : ∀ᶠ n : ℕ in atTop, 400 * Real.log (Real.log (n : ℝ)) ≤ (Real.log (n : ℝ)) ^ δ := by
    have ho := (isLittleO_log_rpow_atTop hδ).bound (show (0 : ℝ) < 1 / 400 by norm_num)
    filter_upwards [hlog_top.eventually ho, hlog_top.eventually (eventually_gt_atTop (1 : ℝ))] with n hn hL
    have hLpos : 0 < Real.log (n : ℝ) := by linarith
    rw [Real.norm_of_nonneg (Real.log_nonneg hL.le),
        Real.norm_of_nonneg (Real.rpow_nonneg hLpos.le _)] at hn
    linarith
  have h3 : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (2 / 3 : ℝ) ≤ (((n - 1) / 2 : ℕ) : ℝ) := by
    have ht : Tendsto (fun x : ℝ => x ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    filter_upwards [(ht.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num)), eventually_ge_atTop 10] with n hn hn10
    have hn_pos : (0 : ℝ) < n := by positivity
    have hpow : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by
      rw [← Real.rpow_one_add' hn_pos.le (by norm_num : (1 : ℝ) + -(1 / 3 : ℝ) ≠ 0)]
      norm_num
    have hle1 : (n : ℝ) ^ (2 / 3 : ℝ) ≤ (n : ℝ) / 4 := by
      dsimp only [Function.comp_apply] at hn
      rw [hpow]; nlinarith
    have hle2 : (n : ℝ) / 4 ≤ (((n - 1) / 2 : ℕ) : ℝ) := by
      have : n ≤ 4 * ((n - 1) / 2) := by omega
      have hcast : (n : ℝ) ≤ 4 * (((n - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    linarith
  have h4 : ∀ᶠ n : ℕ in atTop,
      (max K₀ 2 : ℝ) + 1 ≤ (Real.log (n : ℝ)) ^ α ∧
      200 * Real.log (Real.log (n : ℝ)) ≤ Real.log (n : ℝ) ∧
      100 ≤ Real.log (n : ℝ) := by
    have hpow_top : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα_pos).comp hlog_top
    have hlog_div := (isLittleO_log_rpow_atTop zero_lt_one).bound (show (0 : ℝ) < 1 / 200 by norm_num)
    filter_upwards [hpow_top.eventually (eventually_ge_atTop ((max K₀ 2 : ℝ) + 1)),
      hlog_top.eventually hlog_div, hlog_top.eventually (eventually_ge_atTop (100 : ℝ))] with n hpa hld h20
    have hL1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    rw [Real.rpow_one, Real.norm_of_nonneg (Real.log_nonneg hL1),
        Real.norm_of_nonneg (by linarith)] at hld
    exact ⟨hpa, by linarith, h20⟩
  filter_upwards [h1, h2, h3, h4, eventually_ge_atTop 10] with n h1n h2n h3n h4n hn10
  obtain ⟨hK_le, h200log, hL20⟩ := h4n
  set L : ℝ := Real.log (n : ℝ)
  have hLpos : 0 < L := by linarith
  have hlogL_pos : 0 < Real.log L := Real.log_pos (by linarith)
  let k : ℕ := Nat.floor (L ^ α)
  let m : ℕ := Nat.floor (L / (100 * Real.log L))
  let D : ℕ := Nat.ceil (Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16)) + 1
  have hk_ge : (max K₀ 2 : ℝ) ≤ (k : ℝ) := by
    have := Nat.lt_floor_add_one (L ^ α)
    dsimp [k]; linarith
  have hk_K₀ : K₀ ≤ k := by
    have : (K₀ : ℝ) ≤ (k : ℝ) := le_trans (by exact_mod_cast le_max_left K₀ 2) hk_ge
    exact_mod_cast this
  have hk_2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ (k : ℝ) := le_trans (by exact_mod_cast le_max_right K₀ 2) hk_ge
    exact_mod_cast this
  have hk_le : (k : ℝ) ≤ L ^ α := Nat.floor_le (Real.rpow_nonneg hLpos.le _)
  have hk_lo : (1 / 2 : ℝ) * L ^ α ≤ (k : ℝ) := by
    have h1 := Nat.lt_floor_add_one (L ^ α)
    have h2 : (2 : ℝ) ≤ L ^ α := by
      have : (2 : ℝ) ≤ (max K₀ 2 : ℝ) := by exact_mod_cast le_max_right K₀ 2
      linarith
    dsimp [k]; linarith
  have hm_ge1 : 1 ≤ m := by
    have : (2 : ℝ) ≤ L / (100 * Real.log L) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have : 2 ≤ m := Nat.le_floor this
    omega
  have hm_le : (m : ℝ) ≤ L / (100 * Real.log L) := Nat.floor_le (by positivity)
  have hm_lo : L / (200 * Real.log L) ≤ (m : ℝ) := by
    have h1 := Nat.lt_floor_add_one (L / (100 * Real.log L))
    have h2 : (2 : ℝ) ≤ L / (100 * Real.log L) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hhalf : L / (200 * Real.log L) = (1 / 2 : ℝ) * (L / (100 * Real.log L)) := by ring
    dsimp [m]; linarith
  have hD_ge : Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) ≤ (D : ℝ) := by
    have := Nat.le_ceil (Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16))
    dsimp [D]; push_cast; linarith
  refine ⟨k, m, D, hk_K₀, hk_2, hm_ge1, by dsimp [D]; omega, hD_ge, ?_, ?_⟩
  · have hD_ub : (2 * D : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * L) := by
      have hk_le_L : (k : ℝ) ≤ L := by
        calc (k : ℝ) ≤ L ^ α := hk_le
          _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = L := Real.rpow_one L
      have hlogk_le : Real.log (k : ℝ) ≤ Real.log L :=
        Real.log_le_log (by positivity) hk_le_L
      have hk68 : (k : ℝ) ^ 68 ≤ L ^ (68 * α) := by
        calc (k : ℝ) ^ 68 = (k : ℝ) ^ (68 : ℝ) := (Real.rpow_natCast _ 68).symm
          _ ≤ (L ^ α) ^ (68 : ℝ) := Real.rpow_le_rpow (by positivity) hk_le (by norm_num)
          _ = L ^ (68 * α) := by rw [← Real.rpow_mul hLpos.le]; ring_nf
      have hexp_le : C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16 ≤ (1 / 4 : ℝ) * L := by
        have hlogk_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
        have h16 : (Real.log (k : ℝ)) ^ 16 ≤ (Real.log L) ^ 16 :=
          pow_le_pow_left₀ hlogk_nn hlogk_le 16
        calc
          C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16
              ≤ C₀ * L ^ (68 * α) * (Real.log L) ^ 16 := by gcongr
          _ ≤ (1 / 4 : ℝ) * L := h1n
      have hD_le3 : (D : ℝ) ≤ 3 * Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) := by
        have h1 := Nat.ceil_lt_add_one (Real.exp_pos (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16)).le
        have h2 : (1 : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) :=
          Real.one_le_exp (by positivity)
        dsimp [D]; push_cast; linarith
      have h6_le : (6 : ℝ) ≤ Real.exp ((1 / 12 : ℝ) * L) := by
        have h1 : (1 : ℝ) + (1 / 12 : ℝ) * L ≤ Real.exp ((1 / 12 : ℝ) * L) := by
          linarith [Real.add_one_le_exp ((1 / 12 : ℝ) * L)]
        linarith
      calc
        (2 * D : ℝ) ≤ 6 * Real.exp (C₀ * (k : ℝ) ^ 68 * (Real.log (k : ℝ)) ^ 16) := by linarith
        _ ≤ Real.exp ((1 / 12 : ℝ) * L) * Real.exp ((1 / 4 : ℝ) * L) :=
              mul_le_mul h6_le (Real.exp_le_exp.mpr hexp_le) (Real.exp_pos _).le (Real.exp_pos _).le
        _ = Real.exp ((1 / 3 : ℝ) * L) := by rw [← Real.exp_add]; ring_nf
    have hpow_ub : ((2 * k ^ 29 * (m * k + 1)) ^ m : ℝ) ≤ Real.exp ((1 / 3 : ℝ) * L) := by
      have hk_le_L : (k : ℝ) ≤ L := by
        calc (k : ℝ) ≤ L ^ α := hk_le
          _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = L := Real.rpow_one L
      have hm_le_L : (m : ℝ) ≤ L := by
        have h100 : (1 : ℝ) ≤ 100 * Real.log L := by
          have : (1 : ℝ) ≤ Real.log L := by
            have he : Real.exp 1 ≤ L := by linarith [Real.exp_one_lt_d9]
            have := Real.log_le_log (Real.exp_pos 1) he
            rwa [Real.log_exp] at this
          linarith
        exact hm_le.trans (div_le_self hLpos.le h100)
      have hbase : (2 * k ^ 29 * (m * k + 1) : ℝ) ≤ L ^ 32 := by
        have hmk : (m : ℝ) * (k : ℝ) + 1 ≤ 2 * L ^ 2 := by nlinarith
        have h29 : (k : ℝ) ^ 29 ≤ L ^ 29 := pow_le_pow_left₀ (by positivity) hk_le_L 29
        have h4L : 4 * L ^ 31 ≤ L ^ 32 := by
          have : L ^ 32 = L * L ^ 31 := by ring
          rw [this]; nlinarith [pow_nonneg hLpos.le 31]
        have hprod : (k : ℝ) ^ 29 * ((m : ℝ) * (k : ℝ) + 1) ≤ L ^ 29 * (2 * L ^ 2) :=
          mul_le_mul h29 hmk (by positivity) (by positivity)
        calc
          (2 * k ^ 29 * (m * k + 1) : ℝ)
              = 2 * ((k : ℝ) ^ 29 * ((m : ℝ) * (k : ℝ) + 1)) := by ring
          _ ≤ 2 * (L ^ 29 * (2 * L ^ 2)) := mul_le_mul_of_nonneg_left hprod (by norm_num)
          _ = 4 * L ^ 31 := by ring
          _ ≤ L ^ 32 := h4L
      have hbase_pos : (0 : ℝ) < (2 * k ^ 29 * (m * k + 1) : ℝ) := by positivity
      have hlog_base : Real.log (2 * k ^ 29 * (m * k + 1) : ℝ) ≤ 32 * Real.log L := by
        calc Real.log (2 * k ^ 29 * (m * k + 1) : ℝ) ≤ Real.log (L ^ 32) := Real.log_le_log hbase_pos hbase
          _ = 32 * Real.log L := by rw [Real.log_pow]; ring
      have hmlog : (m : ℝ) * Real.log (2 * k ^ 29 * (m * k + 1) : ℝ) ≤ (1 / 3 : ℝ) * L := by
        have hbase_ge1 : (1 : ℝ) ≤ 2 * (k : ℝ) ^ 29 * ((m : ℝ) * k + 1) := by
          have h1 : (1 : ℝ) ≤ (k : ℝ) ^ 29 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
          have h2 : (1 : ℝ) ≤ (m : ℝ) * (k : ℝ) + 1 := by
            have : (0 : ℝ) ≤ (m : ℝ) * (k : ℝ) := by positivity
            linarith
          nlinarith
        calc
          (m : ℝ) * Real.log (2 * k ^ 29 * (m * k + 1) : ℝ)
              ≤ (L / (100 * Real.log L)) * (32 * Real.log L) :=
                mul_le_mul hm_le hlog_base (Real.log_nonneg hbase_ge1) (by positivity)
          _ = (32 / 100 : ℝ) * L := by field_simp
          _ ≤ (1 / 3 : ℝ) * L := by linarith
      calc
        ((2 * k ^ 29 * (m * k + 1)) ^ m : ℝ)
            = Real.exp ((m : ℝ) * Real.log (2 * k ^ 29 * (m * k + 1) : ℝ)) := by
              rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbase_pos]; ring_nf
        _ ≤ Real.exp ((1 / 3 : ℝ) * L) := Real.exp_le_exp.mpr hmlog
    have hprod_R : ((2 * D * (2 * k ^ 29 * (m * k + 1)) ^ m : ℕ) : ℝ) ≤
        (((n - 1) / 2 : ℕ) : ℝ) := by
      have hcast : ((2 * D * (2 * k ^ 29 * (m * k + 1)) ^ m : ℕ) : ℝ) =
          (2 * D : ℝ) * ((2 * k ^ 29 * (m * k + 1)) ^ m : ℝ) := by push_cast; ring
      rw [hcast]
      have h23 : Real.exp ((2 / 3 : ℝ) * L) = (n : ℝ) ^ (2 / 3 : ℝ) := by
        rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < n)]; dsimp [L]; ring_nf
      calc
        (2 * D : ℝ) * ((2 * k ^ 29 * (m * k + 1)) ^ m : ℝ)
            ≤ Real.exp ((1 / 3 : ℝ) * L) * Real.exp ((1 / 3 : ℝ) * L) :=
              mul_le_mul hD_ub hpow_ub (by positivity) (Real.exp_pos _).le
        _ = Real.exp ((2 / 3 : ℝ) * L) := by rw [← Real.exp_add]; ring_nf
        _ = (n : ℝ) ^ (2 / 3 : ℝ) := h23
        _ ≤ (((n - 1) / 2 : ℕ) : ℝ) := h3n
    exact_mod_cast hprod_R
  · have hcast : ((m * k : ℕ) : ℝ) = (m : ℝ) * (k : ℝ) := by push_cast; ring
    rw [hcast]
    have hprod : L ^ (1 + c) * (L ^ δ / (400 * Real.log L)) ≤ (m : ℝ) * (k : ℝ) := by
      have h1 : (L / (200 * Real.log L)) * ((1 / 2 : ℝ) * L ^ α) ≤ (m : ℝ) * (k : ℝ) :=
        mul_le_mul hm_lo hk_lo (by positivity) (by positivity)
      have h2 : L * L ^ α = L ^ (1 + c) * L ^ δ := by
        rw [← Real.rpow_one_add' hLpos.le (by positivity : (1 : ℝ) + α ≠ 0),
            ← Real.rpow_add hLpos]
        dsimp [α]; ring_nf
      have h3 : (L / (200 * Real.log L)) * ((1 / 2 : ℝ) * L ^ α) =
          L ^ (1 + c) * (L ^ δ / (400 * Real.log L)) := by
        have : (L / (200 * Real.log L)) * ((1 / 2 : ℝ) * L ^ α) =
            (L * L ^ α) / (400 * Real.log L) := by ring
        rw [this, h2]; ring
      linarith
    have hge1 : (1 : ℝ) ≤ L ^ δ / (400 * Real.log L) :=
      (one_le_div (by positivity)).mpr h2n
    have hle1 : L ^ (1 + c) ≤ L ^ (1 + c) * (L ^ δ / (400 * Real.log L)) :=
      le_mul_of_one_le_right (Real.rpow_nonneg hLpos.le _) hge1
    exact hle1.trans hprod

/- ### Hypotheses and main reduction theorem -/

/-- Disjoint-dilate extraction with polynomial doubling (Beker 2025 Prop. 4.2 / Shao 2015 Prop. 6.2 /
Sudakov–Szemerédi–Vu 2005 §6): if a large subset $X \subseteq Y \subseteq \mathbb{Z}$ with
$|Y| \le (1 + k^{-29})|X|$ contains no $k$-element subset sum-free with respect to $Y$, then
$X$ has a large subset $X'$ of polynomial doubling with $(2 \cdot X') \cap Y = \emptyset$. -/
def H1 : Prop :=
  ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ᶠ k : ℕ in Filter.atTop,
    ∀ X Y : Finset ℤ, X ⊆ Y → Real.exp (k : ℝ) ≤ (X.card : ℝ) →
      (Y.card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * (X.card : ℝ) →
      (∀ S : Finset ℤ, S ⊆ X → S.card = k → ¬ Disjoint S.restrictedSumset Y) →
      ∃ X' : Finset ℤ, X' ⊆ X ∧ X'.Nonempty ∧
        (X.card : ℝ) ≤ C₁ * (k : ℝ) ^ 29 * (X'.card : ℝ) ∧
        ((X' + X').card : ℝ) ≤ C₂ * (k : ℝ) ^ 181 * (X'.card : ℝ) ∧
        Disjoint (X'.image (2 * ·)) Y

/-- Quasipolynomial bound for subsets of odd-order cyclic groups lacking non-degenerate
$k$-configurations (Beker 2025, Theorem 3.1). -/
def H2 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Odd N → ∀ k : ℕ, 2 ≤ k →
    ∀ A : Finset (ZMod N), A.Nonempty →
      (∀ x : Fin k → ZMod N, Function.Injective x →
        ¬ ∀ i j : Fin k, x i + x j ∈ A.image (2 * ·)) →
      (N : ℝ) ≤ Real.exp (C * (k : ℝ) ^ 68 * (Real.log (2 * (N : ℝ) / (A.card : ℝ))) ^ 16)

lemma real_to_int_sum_free_model (A : Finset ℝ) :
    ∃ A' : Finset ℤ, A'.card = A.card ∧
      ∀ T : Finset ℤ, T ⊆ A' → Disjoint T.restrictedSumset A' →
        ∃ B : Finset ℝ, B ⊆ A ∧ B.card = T.card ∧ Disjoint B.restrictedSumset A := by
  let P : Finset ℝ := (A.product A).image fun ab => ab.1 - ab.2
  let Q : Finset ℝ := (A.product (A.product A)).image fun abc => abc.1 + abc.2.1 - abc.2.2
  let D := (P ∪ Q).erase 0
  have hD : ∀ v : D, (v : ℝ) ≠ 0 := fun v => (Finset.mem_erase.mp v.property).1
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ) (fun v : D => (v : ℝ)) hD
  let d : ℕ := ∏ a ∈ A, (f a).den
  have hdn : 0 < d := Finset.prod_pos fun a _ => Rat.pos (f a)
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hdn.ne'
  let F : ℝ → ℤ := fun a => ((d / (f a).den : ℕ) : ℤ) * (f a).num
  have hF : ∀ a ∈ A, (F a : ℚ) = (d : ℚ) * f a := by
    intro a ha
    have hdvd : (f a).den ∣ d := Finset.dvd_prod_of_mem (fun x => (f x).den) ha
    have hmul : ((d / (f a).den : ℕ) : ℚ) * ((f a).den : ℚ) = (d : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have ha₀ : ((f a).den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz (f a)
    have hnum : ((f a).den : ℚ) * f a = ((f a).num : ℚ) := by
      calc ((f a).den : ℚ) * f a
          = f a * ((f a).den : ℚ) := mul_comm _ _
        _ = ((f a).num : ℚ) / ((f a).den : ℚ) * ((f a).den : ℚ) := by
            rw [Rat.num_div_den]
        _ = ((f a).num : ℚ) := div_mul_cancel₀ _ ha₀
    calc
      (F a : ℚ) = ((d / (f a).den : ℕ) : ℚ) * ((f a).num : ℚ) := by
        simp only [F, Int.cast_mul, Int.cast_natCast]
      _ = ((d / (f a).den : ℕ) : ℚ) * (((f a).den : ℚ) * f a) := by rw [hnum]
      _ = (d : ℚ) * f a := by rw [← mul_assoc, hmul]
  have hFinj : Set.InjOn F (A : Set ℝ) := by
    intro a ha b hb heq
    by_contra hab
    have hmemP : a - b ∈ P :=
      Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    have hmem : a - b ∈ D :=
      Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hab, Finset.mem_union_left _ hmemP⟩
    have hq := congrArg (fun z : ℤ => (z : ℚ)) heq
    rw [hF a ha, hF b hb] at hq
    have hfab : f a = f b := mul_left_cancel₀ hd hq
    exact hf ⟨a - b, hmem⟩ (by rw [map_sub, hfab, sub_self])
  have hFadd : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b = c → F a + F b = F c := by
    intro a ha b hb c hc h
    apply Rat.intCast_injective
    rw [Int.cast_add, hF a ha, hF b hb, hF c hc, ← mul_add, ← map_add, h]
  refine ⟨A.image F, Finset.card_image_of_injOn hFinj, fun T hT hTdisj => ?_⟩
  let B : Finset ℝ := A.filter fun a => F a ∈ T
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hBT : B.image F = T := by
    ext t
    constructor
    · intro ht
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hb).2
    · intro ht
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hT ht)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, ht⟩, rfl⟩
  refine ⟨B, hBA, ?_, ?_⟩
  · rw [← hBT]
    exact (Finset.card_image_of_injOn (hFinj.mono (Finset.coe_subset.mpr hBA))).symm
  · rw [Erdos787.disjoint_restrictedSumset_iff]
    intro a ha b hb hne hsum
    obtain ⟨haA, haT⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbA, hbT⟩ := Finset.mem_filter.mp hb
    have hneF : F a ≠ F b := fun h => hne (hFinj haA hbA h)
    have hsumF : F a + F b ∈ A.image F :=
      Finset.mem_image.mpr ⟨a + b, hsum, (hFadd a haA b hbA (a + b) hsum rfl).symm⟩
    exact (Erdos787.disjoint_restrictedSumset_iff (A.image F) T).mp hTdisj
      (F a) haT (F b) hbT hneF hsumF

theorem main : H1 → H2 → type_of% @Erdos787.erdos_787.variants.beker := by
  intro h1 h2 c hc hc68
  obtain ⟨C₀, hC₀, hBlock_ev⟩ := near_superset_extract h1 h2
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp hBlock_ev
  filter_upwards [asymptotic_parameters c C₀ hc hc68 hC₀ K₀] with n hn
  obtain ⟨k, m, D, hkK₀, hk2, _, hD1, hD_ge, hcard_le, hmk_ge⟩ := hn
  have hg : m * k ≤ Erdos787.g ℝ n := by
    refine Erdos787.le_g fun A hA_card => ?_
    obtain ⟨Aint, hAint_card, hAint_lift⟩ := real_to_int_sum_free_model A
    obtain ⟨A', hA'_pos, hA'_card, hA'_lift⟩ := reduce_to_positive_half Aint
    have hA'_big : 2 * D * (2 * k ^ 29 * (m * k + 1)) ^ m ≤ A'.card := by
      rw [hAint_card, hA_card] at hA'_card
      exact hcard_le.trans hA'_card
    have hBlock : ∀ X Y : Finset ℤ, X ⊆ Y → D ≤ X.card →
        (Y.card : ℝ) ≤ (1 + ((k : ℝ) ^ 29)⁻¹) * (X.card : ℝ) →
        ∃ S : Finset ℤ, S ⊆ X ∧ S.card = k ∧ Disjoint S.restrictedSumset Y := by
      intro X Y hXY hXD hYle
      exact hK₀ k hkK₀ X Y hXY (hD_ge.trans (by exact_mod_cast hXD)) hYle
    obtain ⟨S, hSA', hScard, hSdisj⟩ :=
      iterative_block_amplification hk2 hD1 hBlock A' hA'_pos hA'_big
    obtain ⟨T, hTAint, hTcard, hTdisj⟩ := hA'_lift S hSA' hSdisj
    obtain ⟨B, hBA, hBcard, hBdisj⟩ := hAint_lift T hTAint hTdisj
    refine ⟨B, hBA, ?_, hBdisj⟩
    omega
  have hgR : ((m * k : ℕ) : ℝ) ≤ (Erdos787.g ℝ n : ℝ) := by exact_mod_cast hg
  exact hmk_ge.trans hgR

end OMA.R_Erdos787_erdos_787_variants_beker_R1
