import OMAReductions.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1
import Mathlib

/-!
# Reduction of step H1 of the Deshouillers–Freiman reduction for Erdős Problem 875

Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

`H1` (structure): a large admissible set is, after the removal of `u` elements at each end,
a set in one residue class mod `q` whose middle block misses at most `r ≤ u / 32` terms of its
arithmetic progression. This is the content of Theorems 2 and 3 of Deshouillers and Freiman
(Israel J. Math. 92 (1995) and Astérisque 258 (1999)) in a weak, explicit form.

`H2` (fill): for an increasing sequence of `n` integers with `g` missing integers, every
number between (sum of the `s` smallest) `+ 2 (g+1)^2` and (sum of the `s` largest)
`- 2 (g+1)^2` is a sum of `s` distinct terms.

`main` proves the step from `H1` and `H2`: the sums of `σ` and of `σ + q` elements of the
middle block contain full progressions; with admissibility and an induction on the outer
elements this gives (top `j` sum) < (bottom `j + q` sum) + small, and a computation gives
`k^2 + 2 k q + 4 e < 4 N + 17 + q^2 + 2 q` for the excess `e` of the diameter.
-/

namespace OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1

open Finset

/-- Structure of large admissible sets (after Deshouillers and Freiman). -/
def H1 : Prop :=
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset ℕ, (A : Set ℕ) ⊆ Set.Icc 1 N →
    Erdos875.IsAdmissible (A : Set ℕ) → 4 * N ≤ A.card * (A.card + 3) →
    ∃ q u r : ℕ, 1 ≤ q ∧ 100 * u ≤ A.card ∧ 32 * r ≤ u ∧
      (∀ a ∈ A, ∀ b ∈ A, a % q = b % q) ∧
      ∃ x ∈ A, ∃ y ∈ A, (A.filter (· < x)).card = u ∧ (A.filter (y < ·)).card = u ∧
        y ≤ x + q * (A.card - 2 * u - 1 + r)

/-- Sums of `s` terms of a dense increasing sequence fill the middle of their range. -/
def H2 : Prop :=
  ∀ (n s g : ℕ) (b : ℕ → ℕ), (∀ i, i + 1 < n → b i < b (i + 1)) →
    b (n - 1) = b 0 + (n - 1) + g → g + 1 ≤ s → s + g + 1 ≤ n →
    ∀ v : ℕ, ∑ i ∈ Finset.range s, b i + 2 * (g + 1) ^ 2 ≤ v →
      v + 2 * (g + 1) ^ 2 ≤ ∑ i ∈ Finset.Ico (n - s) n, b i →
      ∃ I : Finset ℕ, I ⊆ Finset.range n ∧ I.card = s ∧ ∑ i ∈ I, b i = v

lemma grow {n : ℕ} {b : ℕ → ℕ} (hb : ∀ i, i + 1 < n → b i < b (i + 1)) :
    ∀ i j, i ≤ j → j < n → b i + (j - i) ≤ b j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hb j hj
    omega

lemma width {t s : ℕ} {b : ℕ → ℕ} (hb : ∀ i, i + 1 < t → b i < b (i + 1)) (hs : s ≤ t) :
    ∑ i ∈ Finset.range s, b i + s * (t - s) ≤ ∑ i ∈ Finset.Ico (t - s) t, b i := by
  rw [Finset.sum_Ico_eq_sum_range, show t - (t - s) = s by omega]
  have h : ∑ i ∈ Finset.range s, (b i + (t - s)) ≤ ∑ i ∈ Finset.range s, b (t - s + i) :=
    Finset.sum_le_sum fun i hi => by
      have hi' := Finset.mem_range.mp hi
      have := grow hb i (t - s + i) (by omega) (by omega)
      omega
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h
  exact h

/-- Two disjoint families of full intervals: if the first one does not end before the
second one starts, then the second one ends before the first one starts. -/
lemma sep_step (pO qO mP MP mQ MQ lam : ℕ) (hP : mP + 2 * lam ≤ MP) (hQ : mQ + 2 * lam ≤ MQ)
    (hne : ∀ v w, mP + lam ≤ v → v + lam ≤ MP → mQ + lam ≤ w → w + lam ≤ MQ →
      pO + v ≠ qO + w)
    (hfail : qO + mQ + 2 * lam ≤ pO + MP) : qO + MQ < pO + mP + 2 * lam := by
  by_contra h
  by_cases hc : pO + mP ≤ qO + mQ
  · exact hne (qO + mQ + lam - pO) (mQ + lam) (by omega) (by omega) (by omega) (by omega)
      (by omega)
  · exact hne (mP + lam) (pO + mP + lam - qO) (by omega) (by omega) (by omega) (by omega)
      (by omega)

/-- Sum over a shifted index set. -/
lemma shift_sum {t u : ℕ} {α : ℕ → ℕ} (hmono : ∀ i, i < t → α u ≤ α (u + i))
    {I : Finset ℕ} (hI : I ⊆ range t) :
    ∑ x ∈ I.image (fun i => u + i), α x = ∑ i ∈ I, (α (u + i) - α u) + I.card * α u := by
  rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
  have : ∑ i ∈ I, α (u + i) = ∑ i ∈ I, ((α (u + i) - α u) + α u) :=
    Finset.sum_congr rfl fun i hi => by
      have := hmono i (Finset.mem_range.mp (hI hi))
      omega
  rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]


lemma alg1 (σ θ u1 q N a g R : ℕ) (hθ : θ ≤ 1) (hR : 2 * R + q = q * q)
    (h : σ * (σ + q + θ) + a + u1 * (2 * σ + q + θ + u1 + g) + q * (σ + θ + u1 + 1) + R <
      N + 2 * (2 * (g + 1) ^ 2))
    (hg : g = 0 ∨ 31 * g ≤ u1) :
    (2 * σ + q + θ + 2 * u1 + 2) * (2 * σ + q + θ + 2 * u1 + 2) +
        2 * (2 * σ + q + θ + 2 * u1 + 2) * q + 4 * a <
      4 * N + 17 + q * q + 2 * q + 4 * (2 * σ + q + θ + 2 * u1 + 1) := by
  have hl : 16 * (g + 1) ^ 2 ≤ 4 * (u1 * g) + 16 := by
    rcases hg with rfl | hg
    · simp
    · have h1 : 31 * (g * g) ≤ u1 * g := by nlinarith
      have h2 : g ≤ g * g := Nat.le_mul_self g
      nlinarith
  have hθ2 : θ * θ ≤ 1 := by
    have : θ = 0 ∨ θ = 1 := by omega
    rcases this with rfl | rfl <;> simp
  nlinarith

lemma alg0 (σ θ q N R : ℕ) (hθ : θ ≤ 1) (hR : 2 * R + q = q * q)
    (h : σ * (σ + q + θ) + q * (σ + θ) + R < N + 4) :
    (2 * σ + q + θ) * (2 * σ + q + θ) + 2 * (2 * σ + q + θ) * q < 4 * N + 17 + q * q + 2 * q := by
  have hθ2 : θ * θ ≤ 1 := by
    have : θ = 0 ∨ θ = 1 := by omega
    rcases this with rfl | rfl <;> simp
  nlinarith

lemma sum_id (q : ℕ) : 2 * ∑ l ∈ range q, (q - 1 - l) + q = q * q := by
  have h1 := Finset.sum_range_reflect (fun l => l) q
  have h2 := Finset.sum_range_id_mul_two q
  rw [h1]
  rcases q with _ | q
  · simp
  · have : (q + 1) * (q + 1 - 1) = q * q + q := by simp; ring
    rw [this] at h2
    nlinarith


/-- The separation claim for all `i ≤ u`. -/
lemma claim (hFill : H2) {k q u g c N : ℕ} {α : ℕ → ℕ}
    (hα : ∀ i, i + 1 < k → α i < α (i + 1))
    (hN : c + q * α (k - 1) ≤ N) (hq : 1 ≤ q)
    (hadm : ∀ I J : Finset ℕ, I ⊆ range k → J ⊆ range k → 1 ≤ I.card →
      J.card = I.card + q → ∑ i ∈ I, α i ≠ ∑ i ∈ J, α i + c)
    (hg : α (k - 1 - u) = α u + (k - 2 * u - 1) + g) (hu : 100 * u ≤ k) (hgu : 32 * g ≤ u)
    (h4N : 4 * N ≤ k * (k + 3)) (hk : 2000 ≤ k) (hq4 : 4 * q ≤ k + 8) :
    ∀ i, i ≤ u →
      (((k - 2 * u - q) / 2) * α u + ∑ l ∈ range i, α (k - 1 - l)) +
          ∑ x ∈ Finset.Ico (k - 2 * u - (k - 2 * u - q) / 2) (k - 2 * u), (α (u + x) - α u) <
        ((((k - 2 * u - q) / 2) + q) * α u + ∑ l ∈ range i, α l + c) +
          ∑ x ∈ range ((k - 2 * u - q) / 2 + q), (α (u + x) - α u) + 2 * (2 * (g + 1) ^ 2) := by
  have hgrow := grow hα
  set t := k - 2 * u with ht
  set σ := (t - q) / 2 with hσ
  have hmono : ∀ i, i < t → α u ≤ α (u + i) := fun i hi => by
    have := hgrow u (u + i) (by omega) (by omega)
    omega
  have hb' : ∀ i, i + 1 < t → α (u + i) - α u < α (u + (i + 1)) - α u := fun i hi => by
    have h1 := hmono i (by omega)
    have h2 := hα (u + i) (by omega)
    rw [show u + (i + 1) = u + i + 1 by ring]
    omega
  have hlast : α (u + (t - 1)) - α u = (α (u + 0) - α u) + (t - 1) + g := by
    rw [show u + (t - 1) = k - 1 - u by omega, hg]
    change α u + (t - 1) + g - α u = (α u - α u) + (t - 1) + g
    omega
  have h2σ : 2 * σ + q ≤ t := by omega
  have h2σ' : t ≤ 2 * σ + q + 1 := by omega
  have h25 : 9 * k ≤ 25 * σ := by omega
  have hg1 : 1000 * (g + 1) ≤ k := by omega
  have hkk : 2000 * k ≤ k * k := Nat.mul_le_mul_right k hk
  have hσσ : 32 * (g + 1) ^ 2 + 4 * N ≤ 8 * (σ * σ) := by nlinarith
  have hgσ : 2 * (g + 1) ≤ σ := by omega
  have hlam : 4 * (g + 1) ^ 2 ≤ σ * σ := by nlinarith
  have hW1 : σ * σ ≤ σ * (t - σ) := Nat.mul_le_mul_left σ (by omega)
  have hW2 : σ * σ ≤ (σ + q) * (t - (σ + q)) := Nat.mul_le_mul (by omega) (by omega)
  have fP := hFill t σ g (fun i => α (u + i) - α u) hb' hlast (by omega) (by omega)
  have fQ := hFill t (σ + q) g (fun i => α (u + i) - α u) hb' hlast (by omega) (by omega)
  have wP := width (b := fun i => α (u + i) - α u) hb' (show σ ≤ t by omega)
  have wQ := width (b := fun i => α (u + i) - α u) hb' (show σ + q ≤ t by omega)
  have hMM : ∑ x ∈ Finset.Ico (t - σ) t, (α (u + x) - α u) ≤
      ∑ x ∈ Finset.Ico (t - (σ + q)) t, (α (u + x) - α u) :=
    Finset.sum_le_sum_of_subset (fun x hx => by
      have := Finset.mem_Ico.mp hx
      exact Finset.mem_Ico.mpr ⟨by omega, this.2⟩)
  -- the two families of sums are disjoint
  have hne : ∀ i, i ≤ u → ∀ v w,
      ∑ x ∈ range σ, (α (u + x) - α u) + 2 * (g + 1) ^ 2 ≤ v →
      v + 2 * (g + 1) ^ 2 ≤ ∑ x ∈ Finset.Ico (t - σ) t, (α (u + x) - α u) →
      ∑ x ∈ range (σ + q), (α (u + x) - α u) + 2 * (g + 1) ^ 2 ≤ w →
      w + 2 * (g + 1) ^ 2 ≤ ∑ x ∈ Finset.Ico (t - (σ + q)) t, (α (u + x) - α u) →
      (σ * α u + ∑ l ∈ range i, α (k - 1 - l)) + v ≠
        ((σ + q) * α u + ∑ l ∈ range i, α l + c) + w := by
    intro i hi v w hv1 hv2 hw1 hw2 heq
    obtain ⟨I, hI, hIc, hIs⟩ := fP v hv1 hv2
    obtain ⟨J, hJ, hJc, hJs⟩ := fQ w hw1 hw2
    have hinjT : ∀ x ∈ range i, ∀ y ∈ range i, k - 1 - x = k - 1 - y → x = y := by
      intro x hx y hy hxy
      have := Finset.mem_range.mp hx
      have := Finset.mem_range.mp hy
      omega
    have hdP : Disjoint (I.image (fun x => u + x)) ((range i).image (fun l => k - 1 - l)) := by
      refine Finset.disjoint_left.mpr fun z hz hz2 => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨l, hl, hl2⟩ := Finset.mem_image.mp hz2
      have := Finset.mem_range.mp (hI hx)
      have := Finset.mem_range.mp hl
      omega
    have hdQ : Disjoint (J.image (fun x => u + x)) (range i) := by
      refine Finset.disjoint_left.mpr fun z hz hz2 => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have := Finset.mem_range.mp hz2
      omega
    have hcI : (I.image (fun x => u + x)).card = σ := by
      rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), hIc]
    have hcJ : (J.image (fun x => u + x)).card = σ + q := by
      rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), hJc]
    have hsubP : I.image (fun x => u + x) ∪ (range i).image (fun l => k - 1 - l) ⊆ range k := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        have := Finset.mem_range.mp (hI hx)
        exact Finset.mem_range.mpr (by omega)
      · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_range.mpr (by omega)
    have hsubQ : J.image (fun x => u + x) ∪ range i ⊆ range k := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        have := Finset.mem_range.mp (hJ hx)
        exact Finset.mem_range.mpr (by omega)
      · have := Finset.mem_range.mp hz
        exact Finset.mem_range.mpr (by omega)
    have hcP : (I.image (fun x => u + x) ∪ (range i).image (fun l => k - 1 - l)).card = σ + i := by
      rw [Finset.card_union_of_disjoint hdP, hcI, Finset.card_image_of_injOn hinjT,
        Finset.card_range]
    have hcQ : (J.image (fun x => u + x) ∪ range i).card = σ + q + i := by
      rw [Finset.card_union_of_disjoint hdQ, hcJ, Finset.card_range]
    have hsP : ∑ z ∈ I.image (fun x => u + x) ∪ (range i).image (fun l => k - 1 - l), α z =
        (v + σ * α u) + ∑ l ∈ range i, α (k - 1 - l) := by
      rw [Finset.sum_union hdP, shift_sum hmono hI, hIs, hIc, Finset.sum_image hinjT]
    have hsQ : ∑ z ∈ J.image (fun x => u + x) ∪ range i, α z =
        (w + (σ + q) * α u) + ∑ l ∈ range i, α l := by
      rw [Finset.sum_union hdQ, shift_sum hmono hJ, hJs, hJc]
    have := hadm _ _ hsubP hsubQ (by rw [hcP]; omega) (by rw [hcP, hcQ]; omega)
    rw [hsP, hsQ] at this
    omega
  intro i
  induction i with
  | zero =>
    intro _
    by_contra hcon
    have := sep_step _ _ _ _ _ _ (2 * (g + 1) ^ 2) (by omega) (by omega)
      (hne 0 (Nat.zero_le _)) (by omega)
    have hmul : σ * α u ≤ (σ + q) * α u := Nat.mul_le_mul_right _ (by omega)
    simp only [Finset.range_zero, Finset.sum_empty] at this hcon
    omega
  | succ i ih =>
    intro hi
    have hprev := ih (by omega)
    by_contra hcon
    have := sep_step _ _ _ _ _ _ (2 * (g + 1) ^ 2) (by omega) (by omega)
      (hne (i + 1) hi) (by omega)
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at this
    have h1 := hgrow (k - 1 - i) (k - 1) (by omega) (by omega)
    have h2 : α (k - 1) ≤ N := by
      have : α (k - 1) ≤ q * α (k - 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega


/-- The final inequality that follows from the separation claim. -/
lemma pipe (hFill : H2) {k q u g c N : ℕ} {α : ℕ → ℕ}
    (hα : ∀ i, i + 1 < k → α i < α (i + 1)) (hα0 : α 0 = 0)
    (hN : c + q * α (k - 1) ≤ N) (hq : 1 ≤ q)
    (hadm : ∀ I J : Finset ℕ, I ⊆ range k → J ⊆ range k → 1 ≤ I.card →
      J.card = I.card + q → ∑ i ∈ I, α i ≠ ∑ i ∈ J, α i + c)
    (hg : α (k - 1 - u) = α u + (k - 2 * u - 1) + g) (hu : 100 * u ≤ k) (hgu : 32 * g ≤ u)
    (h4N : 4 * N ≤ k * (k + 3)) (hk : 2000 ≤ k) :
    k * k + 2 * k * q + 4 * α (k - 1) < 4 * N + 17 + q * q + 2 * q + 4 * (k - 1) := by
  have hgrow := grow hα
  have hk1 : k - 1 ≤ α (k - 1) := by
    have := hgrow 0 (k - 1) (Nat.zero_le _) (by omega)
    omega
  have hq4 : 4 * q ≤ k + 8 := by
    have h1 : q * (k - 1) ≤ N := (Nat.mul_le_mul_left q hk1).trans (by omega)
    by_contra hc
    have h2 : k + 9 ≤ 4 * q := by omega
    have h3 : (k + 9) * (k - 1) ≤ 4 * q * (k - 1) := Nat.mul_le_mul_right _ h2
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h1 h3
    nlinarith
  have hc := claim hFill hα hN hq hadm hg hu hgu h4N hk hq4 u le_rfl
  set t := k - 2 * u with ht
  set σ := (t - q) / 2 with hσ
  obtain ⟨θ, hθ, hθ1⟩ : ∃ θ, 2 * σ + q + θ = t ∧ θ ≤ 1 := ⟨t - q - 2 * σ, by omega, by omega⟩
  have hmono : ∀ i, i < t → α u ≤ α (u + i) := fun i hi => by
    have := hgrow u (u + i) (by omega) (by omega)
    omega
  have hb' : ∀ i, i + 1 < t → α (u + i) - α u < α (u + (i + 1)) - α u := fun i hi => by
    have h1 := hmono i (by omega)
    have h2 := hα (u + i) (by omega)
    rw [show u + (i + 1) = u + i + 1 by ring]
    omega
  have wP := width (b := fun i => α (u + i) - α u) hb' (show σ ≤ t by omega)
  rw [show t - σ = σ + q + θ by omega] at wP hc
  have hsplit := Finset.sum_range_add (fun x => α (u + x) - α u) σ q
  have hmid : ∑ x ∈ range q, (α (u + (σ + x)) - α u) + q * α u =
      ∑ x ∈ range q, α (u + (σ + x)) := by
    have : ∀ x ∈ range q, α (u + (σ + x)) = (α (u + (σ + x)) - α u) + α u := fun x hx => by
      have := hmono (σ + x) (by have := Finset.mem_range.mp hx; omega)
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul]
  have hup : ∑ x ∈ range q, α (u + (σ + x)) + q * (σ + θ + u) + ∑ x ∈ range q, (q - 1 - x) ≤
      q * α (k - 1) := by
    have h : ∑ x ∈ range q, (α (u + (σ + x)) + (σ + θ + u) + (q - 1 - x)) ≤
        ∑ _x ∈ range q, α (k - 1) :=
      Finset.sum_le_sum fun x hx => by
        have hx' := Finset.mem_range.mp hx
        have := hgrow (u + (σ + x)) (k - 1) (by omega) (by omega)
        omega
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_range, smul_eq_mul, smul_eq_mul] at h
    exact h
  have hR := sum_id q
  have hexp : (σ + q) * α u = σ * α u + q * α u := by ring
  rcases Nat.eq_zero_or_pos u with hu0 | hupos
  · -- no outer elements
    have hg0 : g = 0 := by omega
    subst hu0
    subst hg0
    simp only [Finset.range_zero, Finset.sum_empty] at hc
    have hkt : k = 2 * σ + q + θ := by omega
    have hlast : α (k - 1) = k - 1 := by
      have := hg
      simp only [Nat.sub_zero, hα0] at this
      omega
    have hI : σ * (σ + q + θ) + q * (σ + θ) + ∑ x ∈ range q, (q - 1 - x) < N + 4 := by
      have e1 : q * (σ + θ + 0) = q * (σ + θ) := by simp
      rw [e1] at hup
      simp only [Nat.zero_add] at hc hsplit wP hmid hup
      omega
    have := alg0 σ θ q N _ hθ1 hR hI
    rw [hlast, hkt]
    omega
  · obtain ⟨u1, rfl⟩ : ∃ u1, u = u1 + 1 := ⟨u - 1, by omega⟩
    have hkt : k = 2 * σ + q + θ + 2 * u1 + 2 := by omega
    have hout : ∑ l ∈ range (u1 + 1), α l + α (k - 1) + u1 * (2 * σ + q + θ + u1 + g) ≤
        ∑ l ∈ range (u1 + 1), α (k - 1 - l) := by
      rw [Finset.sum_range_succ' (fun l => α (k - 1 - l)), Finset.sum_range_succ' (fun l => α l)]
      have hrefl := Finset.sum_range_reflect (fun l => α (k - (u1 + 1) + l)) u1
      have hcongr : ∑ j ∈ range u1, α (k - (u1 + 1) + (u1 - 1 - j)) =
          ∑ j ∈ range u1, α (k - 1 - (j + 1)) :=
        Finset.sum_congr rfl fun j hj => by
          have := Finset.mem_range.mp hj
          rw [show k - (u1 + 1) + (u1 - 1 - j) = k - 1 - (j + 1) by omega]
      have hterm : ∑ l ∈ range u1, (α (l + 1) + (2 * σ + q + θ + u1 + g)) ≤
          ∑ l ∈ range u1, α (k - (u1 + 1) + l) :=
        Finset.sum_le_sum fun l hl => by
          have hl' := Finset.mem_range.mp hl
          have h1 := hgrow (l + 1) (u1 + 1) (by omega) (by omega)
          have h2 := hgrow (k - 1 - (u1 + 1)) (k - (u1 + 1) + l) (by omega) (by omega)
          omega
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hterm
      simp only [Nat.sub_zero] at hrefl hcongr ⊢
      rw [hα0]
      omega
    have hI : σ * (σ + q + θ) + α (k - 1) + u1 * (2 * σ + q + θ + u1 + g) +
        q * (σ + θ + u1 + 1) + ∑ x ∈ range q, (q - 1 - x) < N + 2 * (2 * (g + 1) ^ 2) := by
      have e1 : q * (σ + θ + (u1 + 1)) = q * (σ + θ + u1 + 1) := by ring
      rw [e1] at hup
      omega
    have := alg1 σ θ u1 q N (α (k - 1)) g _ hθ1 hR hI (by omega)
    rw [hkt]
    have e2 : 2 * σ + q + θ + 2 * u1 + 2 - 1 = 2 * σ + q + θ + 2 * u1 + 1 := by omega
    rw [e2]
    rw [hkt] at this
    exact this

/-- From the finite set to an increasing sequence `c + q * α i`. -/
lemma setup {A : Finset ℕ} {N q u r : ℕ}
    (hA : (A : Set ℕ) ⊆ Set.Icc 1 N) (hadm : Erdos875.IsAdmissible (A : Set ℕ)) (hq : 1 ≤ q)
    (hmod : ∀ a ∈ A, ∀ b ∈ A, a % q = b % q) (hu : 100 * u ≤ A.card) (hk : 2000 ≤ A.card)
    {x y : ℕ} (hx : x ∈ A) (hy : y ∈ A) (hxc : (A.filter (· < x)).card = u)
    (hyc : (A.filter (y < ·)).card = u) (hxy : y ≤ x + q * (A.card - 2 * u - 1 + r)) :
    ∃ (α : ℕ → ℕ) (c g : ℕ), (∀ i, i + 1 < A.card → α i < α (i + 1)) ∧ α 0 = 0 ∧
      c + q * α (A.card - 1) ≤ N ∧ g ≤ r ∧
      α (A.card - 1 - u) = α u + (A.card - 2 * u - 1) + g ∧
      (∀ i, i < A.card → c + q * α i ∈ A) ∧ (∀ z ∈ A, ∃ i, i < A.card ∧ z = c + q * α i) ∧
      (∀ I J : Finset ℕ, I ⊆ Finset.range A.card → J ⊆ Finset.range A.card → 1 ≤ I.card →
        J.card = I.card + q → ∑ i ∈ I, α i ≠ ∑ i ∈ J, α i + c) := by
  have hpos : 0 < A.card := by omega
  obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℕ, ∀ i (h : i < A.card), a i = A.orderEmbOfFin rfl ⟨i, h⟩ :=
    ⟨fun i => if h : i < A.card then (A.orderEmbOfFin rfl ⟨i, h⟩ : ℕ) else 0,
      fun i h => by simp [h]⟩
  have ha : ∀ i, i + 1 < A.card → a i < a (i + 1) := by
    intro i hi
    rw [hadef i (by omega), hadef (i + 1) hi]
    exact (A.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
  have hagrow := grow ha
  have hmono : ∀ i j, i < j → j < A.card → a i < a j := by
    intro i j hij hj
    have := hagrow i j hij.le hj
    omega
  have hlt : ∀ i j, i < A.card → j < A.card → (a i < a j ↔ i < j) := by
    intro i j hi hj
    constructor
    · intro h
      by_contra hc
      rcases Nat.lt_or_ge j i with h1 | h1
      · have := hmono j i h1 hi; omega
      · have : i = j := by omega
        subst this; omega
    · intro h; exact hmono i j h hj
  have hinj : ∀ i ∈ Finset.range A.card, ∀ j ∈ Finset.range A.card, a i = a j → i = j := by
    intro i hi j hj hij
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_range.mp hj
    rcases Nat.lt_trichotomy i j with h | h | h
    · have := hmono i j h hj'; omega
    · exact h
    · have := hmono j i h hi'; omega
  have hmemA : ∀ i, i < A.card → a i ∈ A := by
    intro i hi
    rw [hadef i hi]
    exact Finset.orderEmbOfFin_mem A rfl ⟨i, hi⟩
  have hsurj : ∀ z ∈ A, ∃ i, i < A.card ∧ a i = z := by
    intro z hz
    have hr : z ∈ Set.range (A.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]
      exact hz
    obtain ⟨⟨i, hi⟩, rfl⟩ := hr
    exact ⟨i, hi, hadef i hi⟩
  have hdiv : ∀ i, i < A.card → a i = a 0 + q * ((a i - a 0) / q) := by
    intro i hi
    have h0 : a 0 ≤ a i := by
      have := hagrow 0 i (Nat.zero_le _) hi
      omega
    have hm := Nat.sub_mod_eq_zero_of_mod_eq (hmod (a i) (hmemA i hi) (a 0) (hmemA 0 hpos))
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)]
    omega
  have hαstrict : ∀ i, i + 1 < A.card → (a i - a 0) / q < (a (i + 1) - a 0) / q := by
    intro i hi
    have h1 := hdiv i (by omega)
    have h2 := hdiv (i + 1) hi
    have h3 := ha i hi
    by_contra hc
    have := Nat.mul_le_mul_left q (Nat.le_of_not_lt hc)
    omega
  have hgrowα := grow hαstrict
  -- the positions of x and y
  obtain ⟨i0, hi0, rfl⟩ := hsurj x hx
  obtain ⟨j0, hj0, rfl⟩ := hsurj y hy
  have hfx : A.filter (· < a i0) = (Finset.range i0).image a := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      obtain ⟨i, hi, rfl⟩ := hsurj z hz1
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr ((hlt i i0 hi hi0).mp hz2), rfl⟩
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hi' := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr ⟨hmemA i (by omega), hmono i i0 hi' hi0⟩
  have hfy : A.filter (a j0 < ·) = (Finset.Ico (j0 + 1) A.card).image a := by
    ext z
    constructor
    · intro hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      obtain ⟨i, hi, rfl⟩ := hsurj z hz1
      exact Finset.mem_image.mpr ⟨i, Finset.mem_Ico.mpr ⟨(hlt j0 i hj0 hi).mp hz2, hi⟩, rfl⟩
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hi' := Finset.mem_Ico.mp hi
      exact Finset.mem_filter.mpr ⟨hmemA i hi'.2, hmono j0 i (by omega) hi'.2⟩
  have hi0u : i0 = u := by
    rw [hfx, Finset.card_image_of_injOn (fun i hi j hj hij =>
      hinj i (Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega)) j
        (Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega)) hij),
      Finset.card_range] at hxc
    exact hxc
  have hj0u : j0 = A.card - 1 - u := by
    rw [hfy, Finset.card_image_of_injOn (fun i hi j hj hij =>
      hinj i (Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2) j
        (Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2) hij),
      Nat.card_Ico] at hyc
    omega
  subst hi0u
  have hdx := hdiv i0 hi0
  have hdy := hdiv j0 hj0
  have hgr : (a i0 - a 0) / q + (j0 - i0) ≤ (a j0 - a 0) / q := hgrowα i0 j0 (by omega) hj0
  have hle : (a j0 - a 0) / q ≤ (a i0 - a 0) / q + (A.card - 2 * i0 - 1 + r) := by
    by_contra hc
    have h1 := Nat.mul_le_mul_left q (Nat.succ_le_of_lt (Nat.lt_of_not_le hc))
    rw [Nat.mul_succ, Nat.mul_add] at h1
    rw [hdx, hdy, Nat.mul_add] at hxy
    rw [← hdx, ← hdy] at hxy
    have h2 := hdiv i0 hi0
    have h3 := hdiv j0 hj0
    nlinarith
  refine ⟨fun i => (a i - a 0) / q, a 0,
    (a j0 - a 0) / q - (a i0 - a 0) / q - (A.card - 2 * i0 - 1), hαstrict, by simp, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · have h1 := hdiv (A.card - 1) (by omega)
    have h2 := (hA (hmemA (A.card - 1) (by omega))).2
    change a 0 + q * ((a (A.card - 1) - a 0) / q) ≤ N
    omega
  · omega
  · change (a (A.card - 1 - i0) - a 0) / q = (a i0 - a 0) / q + (A.card - 2 * i0 - 1) +
      ((a j0 - a 0) / q - (a i0 - a 0) / q - (A.card - 2 * i0 - 1))
    rw [← hj0u]
    omega
  · intro i hi
    change a 0 + q * ((a i - a 0) / q) ∈ A
    rw [← hdiv i hi]
    exact hmemA i hi
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := hsurj z hz
    exact ⟨i, hi, hdiv i hi⟩
  · intro I J hI hJ hI1 hJc heq
    have hsum : ∀ K : Finset ℕ, K ⊆ Finset.range A.card →
        ∑ z ∈ K.image a, z = K.card * a 0 + q * ∑ i ∈ K, (a i - a 0) / q := by
      intro K hK
      rw [Finset.sum_image (fun i hi j hj hij => hinj i (hK hi) j (hK hj) hij), Finset.mul_sum,
        ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => hdiv i (Finset.mem_range.mp (hK hi))
    have hcard : ∀ K : Finset ℕ, K ⊆ Finset.range A.card → (K.image a).card = K.card :=
      fun K hK => Finset.card_image_of_injOn (fun i hi j hj hij => hinj i (hK hi) j (hK hj) hij)
    have hsub : ∀ K : Finset ℕ, K ⊆ Finset.range A.card → ((K.image a : Finset ℕ) : Set ℕ) ⊆ A := by
      intro K hK z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hz)
      exact Finset.mem_coe.mpr (hmemA i (Finset.mem_range.mp (hK hi)))
    have hdisj := hadm (show I.card ∈ Set.Ici 1 from hI1) (show J.card ∈ Set.Ici 1 by
      rw [hJc]; exact Nat.le_add_right_of_le hI1) (by omega)
    refine Set.disjoint_left.mp hdisj ⟨I.image a, hsub I hI, hcard I hI, rfl⟩
      ⟨J.image a, hsub J hJ, hcard J hJ, ?_⟩
    rw [hsum I hI, hsum J hJ, hJc]
    simp only at heq
    rw [heq]
    ring

lemma grow2 {n : ℕ} {b : ℕ → ℕ} (hb : ∀ i, i + 1 < n → b i + 2 ≤ b (i + 1)) :
    ∀ i j, i ≤ j → j < n → b i + 2 * (j - i) ≤ b j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; simp
  | succ j hij ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := hb j hj
    omega

theorem main : H1 → H2 → OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1.H1 := by
  intro hDense hFill
  obtain ⟨N₀, hN₀⟩ := hDense
  refine ⟨max N₀ (10 ^ 7), fun N hN A hA hadm h4N _ d hd => ?_⟩
  have hN1 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 10 ^ 7 ≤ N := le_trans (le_max_right _ _) hN
  have hk : 2000 ≤ A.card := by
    by_contra hc
    have h1 : A.card * (A.card + 3) ≤ 1999 * (1999 + 3) := Nat.mul_le_mul (by omega) (by omega)
    omega
  by_contra hcon
  push Not at hcon
  obtain ⟨q, u, r, hq, hu, hru, hmod, x, hx, y, hy, hxc, hyc, hxy⟩ := hN₀ N hN1 A hA hadm h4N
  obtain ⟨α, c, g, hα, hα0, hNc, hgr, hg, hmem, hsurj, hadmI⟩ :=
    setup hA hadm hq hmod hu hk hx hy hxc hyc hxy
  have hp := pipe hFill hα hα0 hNc hq hadmI hg hu (by omega) h4N hk
  have hgrow := grow hα
  have hk1 : A.card - 1 ≤ α (A.card - 1) := by
    have := hgrow 0 (A.card - 1) (Nat.zero_le _) (by omega)
    omega
  rcases Nat.lt_or_ge q 2 with hq2 | hq2
  · -- q = 1: consecutive elements differ by at least d
    have hq1 : q = 1 := by omega
    subst hq1
    have hstep : ∀ i, i + 1 < A.card → α i + 2 ≤ α (i + 1) := by
      intro i hi
      have h1 := hα i hi
      have h2 := hcon (c + 1 * α i) (hmem i (by omega)) (c + 1 * α (i + 1)) (hmem (i + 1) hi)
      have h3 := Nat.sub_mod_eq_zero_of_mod_eq h2.symm
      have h4 := Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero h3)
      omega
    have := grow2 hstep u (A.card - 1 - u) (by omega) (by omega)
    omega
  · have hq4 : 4 * q ≤ A.card + 8 := by
      have h1 : q * (A.card - 1) ≤ N := (Nat.mul_le_mul_left q hk1).trans (by omega)
      by_contra hc
      have h2 : A.card + 9 ≤ 4 * q := by omega
      have h3 : (A.card + 9) * (A.card - 1) ≤ 4 * q * (A.card - 1) := Nat.mul_le_mul_right _ h2
      obtain ⟨m, hm⟩ : ∃ m, A.card = m + 1 := ⟨A.card - 1, by omega⟩
      rw [hm] at h1 h3 h4N
      simp only [Nat.add_sub_cancel] at h1 h3
      nlinarith
    have hexp : A.card * (A.card + 3) = A.card * A.card + 3 * A.card := by ring
    have h5 : 2 * A.card ≤ A.card * q := Nat.mul_le_mul_left _ hq2 |>.trans_eq' (by ring)
    nlinarith

end OMA.R_Erdos875_erdos_875_variants_deshouillers_freiman_R1_H1_R1
