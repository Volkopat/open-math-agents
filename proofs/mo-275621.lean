import OMAStatements.S_mo_275621
import Mathlib

/-!
MathOverflow 275621: Jean Duchon's answer proves this by a monotone coupling. We use an
induction instead. For a finite set `s`, a probability vector `p` and a downward-closed set `P`
of counts, write `G s p P = P(∑_{i ∈ s} X_i ∈ P)`. Adding a point `a` gives
`G (insert a s) p P = (1 - p a) G s p P + p a G s p (P ∘ succ)`, and `G s p (P ∘ succ) ≤ G s p P`,
so `G` is antitone in each `p a`.
-/

namespace OMA.P275621

open OMA.S_mo_275621 Finset

variable {ι : Type*} [DecidableEq ι]

/-- `P(∑_{i ∈ s} X_i ∈ P)` for independent `X_i ∼ Bernoulli(p i)`, `P` a predicate on counts. -/
noncomputable def G (s : Finset ι) (p : ι → ℝ) (P : ℕ → Prop) [DecidablePred P] : ℝ :=
  ∑ S ∈ s.powerset, if P S.card then (∏ i ∈ S, p i) * ∏ i ∈ s \ S, (1 - p i) else 0

lemma G_insert {a : ι} {s : Finset ι} (ha : a ∉ s) (p : ι → ℝ) (P : ℕ → Prop)
    [DecidablePred P] :
    G (insert a s) p P = (1 - p a) * G s p P + p a * G s p (fun n => P (n + 1)) := by
  unfold G
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · refine sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun h => ha (mem_powerset.1 ht h)
    rw [insert_sdiff_of_notMem _ hat, prod_insert (fun h => ha (mem_sdiff.1 h).1)]
    split_ifs <;> ring
  · refine sum_congr rfl fun t ht => ?_
    have hat : a ∉ t := fun h => ha (mem_powerset.1 ht h)
    rw [card_insert_of_notMem hat, prod_insert hat, insert_sdiff_insert,
      sdiff_insert_of_notMem ha]
    split_ifs <;> ring

lemma G_nonneg (s : Finset ι) (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] : 0 ≤ G s p P := by
  unfold G
  refine sum_nonneg fun S _ => ?_
  split_ifs
  · exact mul_nonneg (prod_nonneg fun i _ => h0 i) (prod_nonneg fun i _ => by linarith [h1 i])
  · exact le_rfl

lemma G_mono_pred (s : Finset ι) (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q] (hPQ : ∀ n, P n → Q n) :
    G s p P ≤ G s p Q := by
  unfold G
  refine sum_le_sum fun S _ => ?_
  have hw : 0 ≤ (∏ i ∈ S, p i) * ∏ i ∈ s \ S, (1 - p i) :=
    mul_nonneg (prod_nonneg fun i _ => h0 i) (prod_nonneg fun i _ => by linarith [h1 i])
  by_cases hP : P S.card
  · simp [hP, hPQ _ hP]
  · simp only [hP, if_false]; split_ifs <;> linarith

lemma G_anti (s : Finset ι) (p q : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hq1 : ∀ i, q i ≤ 1)
    (hpq : ∀ i, p i ≤ q i) :
    ∀ (P : ℕ → Prop) [DecidablePred P], (∀ m n, m ≤ n → P n → P m) → G s q P ≤ G s p P := by
  have hp1 : ∀ i, p i ≤ 1 := fun i => (hpq i).trans (hq1 i)
  have hq0 : ∀ i, 0 ≤ q i := fun i => (hp0 i).trans (hpq i)
  induction s using Finset.induction_on with
  | empty => intro P _ _; simp [G]
  | insert a s ha ih =>
    intro P _ hP
    rw [G_insert ha, G_insert ha]
    have hA := ih P hP
    have hB := ih (fun n => P (n + 1)) (fun m n hmn h => hP (m + 1) (n + 1) (by omega) h)
    have hBA : G s p (fun n => P (n + 1)) ≤ G s p P :=
      G_mono_pred s p hp0 hp1 _ _ fun n h => hP n (n + 1) (by omega) h
    have h1 : 0 ≤ 1 - q a := by linarith [hq1 a]
    have h2 := hpq a
    have h3 := hq0 a
    nlinarith [mul_le_mul_of_nonneg_left hA h1, mul_le_mul_of_nonneg_left hB h3,
      mul_le_mul_of_nonneg_right h2 (sub_nonneg.2 hBA)]

lemma cdf_eq {N : ℕ} (p : Fin N → ℝ) (k : ℕ) :
    cdf p k = G (univ : Finset (Fin N)) p (fun n => n ≤ k) := by
  unfold cdf G
  rw [sum_filter, powerset_univ]
  refine sum_congr rfl fun S _ => ?_
  rw [compl_eq_univ_sdiff]

lemma proof_aux : ∀ (N : ℕ) (p : Fin N → ℝ) (δ : ℝ), (∀ i, 0 ≤ p i) → 0 ≤ δ →
    (∀ i, p i + δ ≤ 1) → ∀ k : ℕ, k ≤ N → cdf (fun i => p i + δ) k ≤ cdf p k := by
  intro N p δ hp hδ h1 k _
  rw [cdf_eq, cdf_eq]
  exact G_anti _ p (fun i => p i + δ) hp h1 (fun i => by linarith) _
    (fun m n hmn h => le_trans hmn h)

end OMA.P275621

theorem OMA.solution : type_of% @OMA.S_mo_275621.main := OMA.P275621.proof_aux
