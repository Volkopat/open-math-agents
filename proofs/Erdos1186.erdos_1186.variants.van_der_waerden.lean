import FormalConjectures.ErdosProblems.«1186»

-- Problem: Erdős Problem 1186 — van der Waerden
-- Credit: @luciusacarr (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Hales-Jewett gives, inside every dilated box, a monochromatic progression; counting boxes
-- gives a positive proportion of all progressions.

open Combinatorics Finset Filter

namespace OMA

theorem sum_line {ι : Type} [Fintype ι] {k : ℕ} (l : Line (Fin k) ι) (z x : Fin k)
    (hz : (z : ℕ) = 0) :
    ∑ i, (l x i : ℕ) = (∑ i, (l z i : ℕ)) +
      (univ.filter (fun i => l.idxFun i = none)).card * (x : ℕ) := by
  classical
  have he : ∀ i, (l x i : ℕ) = (l z i : ℕ) + if l.idxFun i = none then (x : ℕ) else 0 := by
    intro i
    cases h : l.idxFun i with
    | none => simp [h, hz]
    | some a => simp [h]
  simp only [he, sum_add_distrib, ← sum_filter, sum_const]
  rfl

/-- Van der Waerden inside a dilated box, with uniform bounds. -/
theorem vdw_core (k : ℕ) (hk : 1 ≤ k) : ∃ M : ℕ, ∀ (c : ℕ → Bool) (A D : ℕ),
    ∃ b s : ℕ, 1 ≤ s ∧ s ≤ M ∧ b + s * (k - 1) ≤ M * (k - 1) ∧
      ∀ i < k, c (A + D * (b + s * i)) = c (A + D * b) := by
  classical
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) Bool
  refine ⟨Fintype.card ι, fun c A D => ?_⟩
  obtain ⟨l, col, hl⟩ := hι (fun v => c (A + D * ∑ i, (v i : ℕ)))
  set S : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hS
  let z : Fin k := ⟨0, by omega⟩
  let b : ℕ := ∑ i, (l z i : ℕ)
  have hsum : ∀ x : Fin k, ∑ i, ((l x i : Fin k) : ℕ) = b + S.card * (x : ℕ) :=
    fun x => sum_line l z x rfl
  have hspos : 1 ≤ S.card := Finset.card_pos.mpr ⟨l.proper.choose, by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩⟩
  have hsle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  have hcol : ∀ i (hi : i < k), c (A + D * (b + S.card * i)) = col := by
    intro i hi
    have := hl ⟨i, hi⟩
    simp only [hsum ⟨i, hi⟩] at this
    exact this
  refine ⟨b, S.card, hspos, hsle, ?_, ?_⟩
  · have h := hsum ⟨k - 1, by omega⟩
    have hle : ∑ i, ((l ⟨k - 1, by omega⟩ i : Fin k) : ℕ) ≤ ∑ _i : ι, (k - 1) :=
      Finset.sum_le_sum (fun i _ => by have := (l ⟨k - 1, by omega⟩ i).2; omega)
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    rw [h] at hle
    exact hle
  · intro i hi
    exact (hcol i hi).trans (by simpa using (hcol 0 (by omega)).symm)

/-- The counting step. -/
theorem count (k : ℕ) (hk : 2 ≤ k) (M : ℕ)
    (hM : ∀ (c : ℕ → Bool) (A D : ℕ),
      ∃ b s : ℕ, 1 ≤ s ∧ s ≤ M ∧ b + s * (k - 1) ≤ M * (k - 1) ∧
        ∀ i < k, c (A + D * (b + s * i)) = c (A + D * b))
    (c : ℕ → Bool) (n : ℕ) :
    (n / (M * (k - 1) + 1)) * (n / (M * (k - 1) + 1)) ≤
      ((M * (k - 1) + 1) * (M + 1)) * Erdos1186.monoCount k n c := by
  classical
  set B : ℕ := M * (k - 1) with hB
  set q : ℕ := n / (B + 1) with hq
  choose bf sf h1 h2 h3 h4 using hM c
  have hqn : q * (B + 1) ≤ n := Nat.div_mul_le_self n (B + 1)
  let F : ℕ × ℕ → (ℕ × ℕ) × (ℕ × ℕ) := fun p =>
    ((p.1 + p.2 * bf p.1 p.2, p.2 * sf p.1 p.2), (bf p.1 p.2, sf p.1 p.2))
  let T : Finset (ℕ × ℕ) := (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p : ℕ × ℕ =>
    p.1 + (k - 1) * p.2 ≤ n ∧ ∀ i < k, c (p.1 + i * p.2) = c p.1
  have hmaps : ∀ p ∈ Finset.Icc 1 q ×ˢ Finset.Icc 1 q,
      F p ∈ T ×ˢ (Finset.range (B + 1) ×ˢ Finset.range (M + 1)) := by
    rintro ⟨A, D⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨hA1, hAq⟩, hD1, hDq⟩ := hp
    have e1 := h1 A D
    have e2 := h2 A D
    have e3 := h3 A D
    have e4 := h4 A D
    have hmul : D * (bf A D + sf A D * (k - 1)) ≤ q * B := Nat.mul_le_mul hDq e3
    have hexp : A + D * bf A D + (k - 1) * (D * sf A D) = A + D * (bf A D + sf A D * (k - 1)) := by
      ring
    have htot : A + D * bf A D + (k - 1) * (D * sf A D) ≤ n := by
      rw [hexp]
      calc A + D * (bf A D + sf A D * (k - 1)) ≤ q + q * B := Nat.add_le_add hAq hmul
        _ = q * (B + 1) := by ring
        _ ≤ n := hqn
    have hds1 : 1 ≤ D * sf A D := Nat.mul_pos hD1 e1
    have hds : D * sf A D ≤ (k - 1) * (D * sf A D) :=
      Nat.le_mul_of_pos_left _ (by omega)
    have hb : bf A D ≤ B := le_trans (Nat.le_add_right _ _) e3
    simp only [F, T, Finset.mem_product, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, htot, ?_⟩, by omega, by omega⟩
    intro i hi
    have := e4 i hi
    have hrw : A + D * bf A D + i * (D * sf A D) = A + D * (bf A D + sf A D * i) := by ring
    rw [hrw]
    exact this
  have hinj : Set.InjOn F ((Finset.Icc 1 q ×ˢ Finset.Icc 1 q : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    rintro ⟨A, D⟩ hp ⟨A', D'⟩ hp' hF
    simp only [F, Prod.mk.injEq] at hF
    obtain ⟨⟨hF1, hF2⟩, hF3, hF4⟩ := hF
    have e1 := h1 A D
    rw [hF4] at hF2
    rw [hF3] at hF1
    have hDD : D = D' := Nat.eq_of_mul_eq_mul_right (by rw [← hF4]; exact e1) hF2
    subst hDD
    have hAA : A = A' := by omega
    rw [hAA]
  have hcard := Finset.card_le_card_of_injOn F hmaps hinj
  simp only [Finset.card_product, Nat.card_Icc, Finset.card_range, Nat.add_sub_cancel] at hcard
  have hT : T.card = Erdos1186.monoCount k n c := rfl
  rw [hT] at hcard
  calc q * q ≤ Erdos1186.monoCount k n c * ((B + 1) * (M + 1)) := hcard
    _ = ((B + 1) * (M + 1)) * Erdos1186.monoCount k n c := Nat.mul_comm _ _

theorem monoCount_le_sq (k n : ℕ) (c : ℕ → Bool) : Erdos1186.monoCount k n c ≤ n * n := by
  unfold Erdos1186.monoCount
  calc _ ≤ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n * n := by simp

end OMA

theorem OMA.solution : type_of% @Erdos1186.erdos_1186.variants.van_der_waerden := by
  intro k hk
  obtain ⟨M, hM⟩ := OMA.vdw_core k (by omega)
  set B : ℕ := M * (k - 1) with hB
  set K : ℕ := (B + 1) * (M + 1) with hK
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : 0 < K := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
    exact_mod_cast this
  have hBpos : (0 : ℝ) < ((B : ℝ) + 1) := by positivity
  set ε : ℝ := 1 / (4 * ((B : ℝ) + 1) ^ 2 * K) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- the minimum is attained
  have hmin : ∀ n, ∃ c : ℕ → Bool, Erdos1186.monoCount k n c = Erdos1186.minMonoCount k n := by
    intro n
    have hne : {m : ℕ | ∃ c : ℕ → Bool, Erdos1186.monoCount k n c = m}.Nonempty :=
      ⟨_, fun _ => true, rfl⟩
    exact Nat.sInf_mem hne
  have hupper : ∀ n : ℕ, (Erdos1186.minMonoCount k n : ℝ) / (n : ℝ) ^ 2 ≤ 1 := by
    intro n
    obtain ⟨c, hc⟩ := hmin n
    have h := OMA.monoCount_le_sq k n c
    rw [hc] at h
    have h' : (Erdos1186.minMonoCount k n : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : ((Erdos1186.minMonoCount k n : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast h
      rw [Nat.cast_mul] at this
      rw [sq]
      exact this
    exact div_le_one_of_le₀ h' (by positivity)
  have hlower : ∀ᶠ n : ℕ in atTop, ε ≤ (Erdos1186.minMonoCount k n : ℝ) / (n : ℝ) ^ 2 := by
    rw [Filter.eventually_atTop]
    refine ⟨2 * (B + 1), fun n hn => ?_⟩
    obtain ⟨c, hc⟩ := hmin n
    have hcount := OMA.count k hk M hM c n
    rw [hc] at hcount
    set q : ℕ := n / (B + 1) with hq
    have hq1 : 1 ≤ q := by
      rw [hq, Nat.le_div_iff_mul_le (Nat.succ_pos _)]
      omega
    have hlt : n < (B + 1) * (q + 1) := Nat.lt_mul_div_succ n (Nat.succ_pos _)
    have hBq : (B + 1) * 1 ≤ (B + 1) * q := Nat.mul_le_mul_left _ hq1
    have hn2 : n ≤ 2 * ((B + 1) * q) := by
      have : (B + 1) * (q + 1) = (B + 1) * q + (B + 1) * 1 := by ring
      omega
    have hnR : (n : ℝ) ≤ 2 * (((B : ℝ) + 1) * (q : ℝ)) := by exact_mod_cast hn2
    have hcR : (q : ℝ) * (q : ℝ) ≤ (K : ℝ) * (Erdos1186.minMonoCount k n : ℝ) := by
      exact_mod_cast hcount
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    have hsq : (n : ℝ) ^ 2 ≤ (2 * (((B : ℝ) + 1) * (q : ℝ))) ^ 2 :=
      pow_le_pow_left₀ hnpos.le hnR 2
    rw [hε, le_div_iff₀ (by positivity), div_mul_eq_mul_div, one_mul,
      div_le_iff₀ (by positivity)]
    calc (n : ℝ) ^ 2 ≤ (2 * (((B : ℝ) + 1) * (q : ℝ))) ^ 2 := hsq
      _ = 4 * ((B : ℝ) + 1) ^ 2 * ((q : ℝ) * (q : ℝ)) := by ring
      _ ≤ 4 * ((B : ℝ) + 1) ^ 2 * ((K : ℝ) * (Erdos1186.minMonoCount k n : ℝ)) :=
          mul_le_mul_of_nonneg_left hcR (by positivity)
      _ = (Erdos1186.minMonoCount k n : ℝ) * (4 * ((B : ℝ) + 1) ^ 2 * K) := by ring
  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun n : ℕ => (Erdos1186.minMonoCount k n : ℝ) / (n : ℝ) ^ 2) :=
    IsBoundedUnder.isCoboundedUnder_ge ⟨1, Filter.eventually_map.mpr (Filter.Eventually.of_forall hupper)⟩
  unfold Erdos1186.δ
  exact lt_of_lt_of_le hεpos (le_liminf_of_le hcob hlower)
