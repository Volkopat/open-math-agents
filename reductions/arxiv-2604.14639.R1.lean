import OMAStatements.S_arxiv_2604_14639
import Mathlib

open Filter Topology OMA.S_arxiv_2604_14639

namespace OMA.R_arxiv_2604_14639_R1

-- Part (a), unimodality, for exponents l at least 2 (the case l = 1 is proved below).
def H1 : Prop := ∀ m l : ℕ, 0 < m → 2 ≤ l → ∀ a : ℝ, 0 < a → Unimodal (x m l a) m

-- Part (b), eventual log-concavity, verbatim.
def H2 : Prop := ∀ l : ℕ, 0 < l → ∀ a : ℝ, 0 < a → ∀ᶠ m in atTop, LogConcave (x m l a) m

-- Part (c), location of the unique maximum, verbatim.
def H3 : Prop := ∀ l a m : ℕ, 0 < l → 0 < a → 2 ≤ m →
      ∃ r ≤ m, (∀ s ≤ m, s ≠ r → x m l a s < x m l a r) ∧
        (a * m + a + 2) / (2 * a + 1) ≤ r + 1 ∧ r ≤ (a * m + a + 2) / (2 * a + 1) + 1

-- Part (d), asymptotics of the maximum value, verbatim.
def H4 : Prop := ∀ l : ℕ, 0 < l → ∀ a : ℝ, 0 < a →
      Tendsto (fun m : ℕ => maxValue m l a / asymptotic m l a) atTop (𝓝 1)

theorem unimodal_of_steps (f : ℕ → ℝ) (m : ℕ) (P : ℕ → Prop)
    (hinc : ∀ r, r < m → ¬ P r → f r ≤ f (r + 1))
    (hdec : ∀ r, r < m → P r → f (r + 1) ≤ f r)
    (hpers : ∀ r, r + 1 < m → P r → P (r + 1)) : Unimodal f m := by
  classical
  by_cases h : ∃ r, r < m ∧ P r
  · have key : ∀ i, Nat.find h ≤ i → i < m → P i := by
      intro i hji
      induction i, hji using Nat.le_induction with
      | base => intro _; exact (Nat.find_spec h).2
      | succ n hn ih => intro hm; exact hpers n hm (ih (by omega))
    refine ⟨Nat.find h, (Nat.find_spec h).1.le, ?_, ?_⟩
    · intro i hi
      have him : i < m := lt_trans hi (Nat.find_spec h).1
      exact hinc i him (fun hp => Nat.find_min h hi ⟨him, hp⟩)
    · intro i hji him
      exact hdec i him (key i hji him)
  · refine ⟨m, le_rfl, ?_, ?_⟩
    · intro i hi
      exact hinc i hi (fun hp => h ⟨i, hi, hp⟩)
    · intro i hi him
      omega

theorem regionB (T : ℕ → ℝ) (m r : ℕ) (a : ℝ) (ha : 0 < a)
    (hnn : ∀ i, 0 ≤ T i)
    (hrec : ∀ i, i < m → T (i + 1) * ((i : ℝ) + 1) = T i * a * ((m : ℝ) - i))
    (hrm : r + 1 ≤ m)
    (hB : (a + 1) * ((r : ℝ) + 2) < a * ((m : ℝ) - r - 1)) :
    a * ∑ i ∈ Finset.range (r + 1), T i ≤ T (r + 1) := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = a * ((m : ℝ) - r + 1) := ⟨_, rfl⟩
  have hmr : (r : ℝ) + 1 ≤ m := by exact_mod_cast hrm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have key : ∀ k, k ≤ r → (∑ i ∈ Finset.range (k + 1), T i) * (D - r) ≤ T k * D := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [Finset.sum_range_one]
      nlinarith [hnn 0]
    | succ k ih =>
      intro hk
      have hk' : (k : ℝ) + 1 ≤ r := by exact_mod_cast hk
      have hkm : k < m := by omega
      have h1 := ih (by omega)
      have hr := hrec k hkm
      have h2 : T k * D ≤ T (k + 1) * r := by
        have hpos : 0 < a * ((m : ℝ) - k) := by apply mul_pos ha; linarith
        have h3 : T k * D * (a * ((m : ℝ) - k)) ≤ T (k + 1) * r * (a * ((m : ℝ) - k)) := by
          have e : T k * D * (a * ((m : ℝ) - k)) = T (k + 1) * ((k : ℝ) + 1) * D := by
            rw [hr]; ring
          rw [e]
          have hT := hnn (k + 1)
          have hq : 0 ≤ a * (((r : ℝ) - k - 1) * ((m : ℝ) + 1)) := by
            apply mul_nonneg ha.le
            apply mul_nonneg <;> linarith
          have h4 : ((k : ℝ) + 1) * D ≤ r * (a * ((m : ℝ) - k)) := by
            rw [hD]; nlinarith [hq]
          calc T (k + 1) * ((k : ℝ) + 1) * D = T (k + 1) * (((k : ℝ) + 1) * D) := by ring
            _ ≤ T (k + 1) * (r * (a * ((m : ℝ) - k))) := mul_le_mul_of_nonneg_left h4 hT
            _ = T (k + 1) * r * (a * ((m : ℝ) - k)) := by ring
        exact le_of_mul_le_mul_right h3 hpos
      rw [Finset.sum_range_succ]
      linarith
  have h1 := key r le_rfl
  have hr := hrec r (by omega)
  have hmr' : 0 < (m : ℝ) - r := by linarith
  have hv : (r : ℝ) < a * ((m : ℝ) - r - r - 1) := by nlinarith
  have hw : 0 < ((m : ℝ) - r + 1) * (a * ((m : ℝ) - r - r - 1) - r) := by
    apply mul_pos <;> linarith
  have hDr : 0 < D - r := by rw [hD]; nlinarith
  have hc : ((r : ℝ) + 1) * D ≤ (D - r) * ((m : ℝ) - r) := by
    rw [hD]; nlinarith [hw]
  have hfin : a * (∑ i ∈ Finset.range (r + 1), T i) * ((D - r) * ((m : ℝ) - r)) ≤
      T (r + 1) * ((D - r) * ((m : ℝ) - r)) := by
    calc a * (∑ i ∈ Finset.range (r + 1), T i) * ((D - r) * ((m : ℝ) - r))
        = a * ((m : ℝ) - r) * ((∑ i ∈ Finset.range (r + 1), T i) * (D - r)) := by ring
      _ ≤ a * ((m : ℝ) - r) * (T r * D) :=
          mul_le_mul_of_nonneg_left h1 (mul_pos ha hmr').le
      _ = T (r + 1) * (((r : ℝ) + 1) * D) := by rw [← mul_assoc (T (r + 1)), hr]; ring
      _ ≤ T (r + 1) * ((D - r) * ((m : ℝ) - r)) := mul_le_mul_of_nonneg_left hc (hnn (r + 1))
  exact le_of_mul_le_mul_right hfin (mul_pos hDr hmr')

theorem denom_one (a : ℝ) (r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * a ^ i = (1 + a) ^ r := by
  rw [add_comm (1 : ℝ) a, add_pow]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [one_pow, mul_one, mul_comm]

theorem x_one (m : ℕ) (a : ℝ) (r : ℕ) :
    x m 1 a r = (∑ i ∈ Finset.range (r + 1), (m.choose i : ℝ) * a ^ i) / (1 + a) ^ r := by
  unfold x
  simp only [pow_one]
  rw [denom_one]

theorem x_step (m : ℕ) (a : ℝ) (ha : 0 < a) (T : ℕ → ℝ)
    (hTi : ∀ i, T i = (m.choose i : ℝ) * a ^ i) (r : ℕ) :
    x m 1 a (r + 1) - x m 1 a r =
      (T (r + 1) - a * ∑ i ∈ Finset.range (r + 1), T i) / (1 + a) ^ (r + 1) := by
  simp only [hTi]
  rw [x_one, x_one, Finset.sum_range_succ (n := r + 1)]
  have h : (1 + a) ^ r ≠ 0 := by positivity
  have h' : (1 + a) ≠ 0 := by positivity
  field_simp
  ring

theorem unimodal_l1 (m : ℕ) (a : ℝ) (ha : 0 < a) : Unimodal (x m 1 a) m := by
  obtain ⟨T, hTi⟩ : ∃ T : ℕ → ℝ, ∀ i, T i = (m.choose i : ℝ) * a ^ i := ⟨_, fun i => rfl⟩
  have hnn : ∀ i, 0 ≤ T i := fun i => by rw [hTi]; positivity
  have hrec : ∀ i, i < m → T (i + 1) * ((i : ℝ) + 1) = T i * a * ((m : ℝ) - i) := by
    intro i hi
    rw [hTi, hTi]
    have h := Nat.choose_succ_right_eq m i
    have h' : ((m.choose (i + 1) : ℕ) : ℝ) * ((i : ℝ) + 1) = (m.choose i : ℝ) * ((m : ℝ) - i) := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast [Nat.cast_sub hi.le] at this
      exact this
    calc (m.choose (i + 1) : ℝ) * a ^ (i + 1) * ((i : ℝ) + 1)
        = ((m.choose (i + 1) : ℝ) * ((i : ℝ) + 1)) * a ^ (i + 1) := by ring
      _ = (m.choose i : ℝ) * a ^ i * a * ((m : ℝ) - i) := by rw [h']; ring
  apply unimodal_of_steps (x m 1 a) m (fun r => T (r + 1) < a * ∑ i ∈ Finset.range (r + 1), T i)
  · intro r _ hP
    replace hP := not_lt.mp hP
    have hs := x_step m a ha T hTi r
    have : 0 ≤ x m 1 a (r + 1) - x m 1 a r := by
      rw [hs]; apply div_nonneg _ (by positivity); linarith
    linarith
  · intro r _ hP
    have hs := x_step m a ha T hTi r
    have : x m 1 a (r + 1) - x m 1 a r < 0 := by
      rw [hs]; apply div_neg_of_neg_of_pos _ (by positivity); linarith
    linarith
  · intro r hr hP
    have hA : a * ((m : ℝ) - r - 1) ≤ (a + 1) * ((r : ℝ) + 2) := by
      by_contra hB
      replace hB := lt_of_not_ge hB
      have := regionB T m r a ha hnn hrec (by omega) hB
      linarith
    have h2 := hrec (r + 1) (by omega)
    push_cast at h2
    have h3 : T (r + 1 + 1) ≤ (a + 1) * T (r + 1) := by
      have hpos : (0 : ℝ) < (r : ℝ) + 1 + 1 := by positivity
      have h4 : T (r + 1 + 1) * ((r : ℝ) + 1 + 1) ≤ (a + 1) * T (r + 1) * ((r : ℝ) + 1 + 1) := by
        rw [h2]
        have := hnn (r + 1)
        have e : (m : ℝ) - (r + 1) = (m : ℝ) - r - 1 := by ring
        rw [e]
        nlinarith
      exact le_of_mul_le_mul_right h4 hpos
    rw [Finset.sum_range_succ]
    nlinarith [hnn (r + 1)]

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_arxiv_2604_14639.main := by
  intro h1 h2 h3 h4
  refine ⟨?_, h2, h3, h4⟩
  intro m l hm hl a ha
  rcases Nat.lt_or_ge l 2 with h | h
  · obtain rfl : l = 1 := by omega
    exact unimodal_l1 m a ha
  · exact h1 m l hm h a ha

end OMA.R_arxiv_2604_14639_R1
