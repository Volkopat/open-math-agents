import FormalConjectures.ErdosProblems.«853»

/-! A first-occurrence criterion for growth of the least missing even prime gap. -/

-- Credit: @Pixelstorm44
namespace OMA.R_Erdos853_erdos_853_parts_ii_R1

open Filter Erdos853

/-- Every positive even integer occurs as a difference of consecutive primes. -/
def H1 : Prop := ∀ g : ℕ, 0 < g → g % 2 = 0 → ∃ i, primeGap i = g

/-- At a first occurrence which completes the list of even gaps up to its size,
the size eventually exceeds every fixed multiple of the logarithm of the preceding index. -/
def H2 : Prop := ∀ C : ℝ, ∀ᶠ n : ℕ in atTop,
  let g := primeGap (n + 1)
  0 < g → g % 2 = 0 →
    (∀ i ≤ n, primeGap i ≠ g) →
    (∀ t < g, 0 < t → t % 2 = 0 → ∃ i ≤ n, primeGap i = t) →
    C * Real.log n ≤ g

theorem missing_nonempty (n : ℕ) :
    ({t : ℕ | 0 < t ∧ t % 2 = 0 ∧ ¬ ∃ i ≤ n, primeGap i = t} : Set ℕ).Nonempty := by
  let M := (Finset.range (n + 1)).sup primeGap
  refine ⟨2 * (M + 1), by omega, by omega, ?_⟩
  rintro ⟨i, hi, he⟩
  have h : primeGap i ≤ M := Finset.le_sup (f := primeGap) (Finset.mem_range.mpr (by omega : i < n + 1))
  omega

private theorem missing_r (n : ℕ) : 0 < r n ∧ r n % 2 = 0 ∧ ¬ ∃ i ≤ n, primeGap i = r n :=
  Nat.sInf_mem (missing_nonempty n)

private theorem r_le_missing {n t : ℕ} (ht : 0 < t ∧ t % 2 = 0 ∧ ¬ ∃ i ≤ n, primeGap i = t) : r n ≤ t :=
  Nat.sInf_le ht

private theorem seen_below {n t : ℕ} (hlt : t < r n) (hp : 0 < t) (he : t % 2 = 0) :
    ∃ i ≤ n, primeGap i = t := by
  by_contra h
  exact hlt.not_ge (r_le_missing ⟨hp, he, h⟩)

/-- For any prefix, the first later occurrence of its least missing gap completes
the list through that gap. Intermediate indices may introduce larger gaps. -/
private theorem next_completion (h : H1) (n : ℕ) :
    ∃ m ≥ n, primeGap (m+1) = r n ∧
      (∀ i ≤ m, primeGap i ≠ r n) ∧
      (∀ t < r n, 0 < t → t % 2 = 0 → ∃ i ≤ m, primeGap i = t) := by
  classical
  obtain ⟨hp, he, hmiss⟩ := missing_r n
  let hits := h (r n) hp he
  have hhit := Nat.find_spec hits
  have hn : n < Nat.find hits := by
    by_contra! hle
    exact hmiss ⟨_, hle, hhit⟩
  let m := Nat.find hits - 1
  have hm : m + 1 = Nat.find hits := by dsimp [m]; omega
  have hnm : n ≤ m := by omega
  refine ⟨m, hnm, hm ▸ hhit, ?_, ?_⟩
  · intro i hi
    exact Nat.find_min hits (by omega)
  · intro t ht htp hte
    obtain ⟨i, hi, hit⟩ := seen_below ht htp hte
    exact ⟨i, hi.trans hnm, hit⟩

theorem main : H1 → H2 → type_of% @Erdos853.erdos_853.parts.ii := by
  intro h₁ h₂
  apply tendsto_atTop.mpr
  intro C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h₂ (max C 0))
  filter_upwards [eventually_ge_atTop (max N 2)] with n hn
  have h2n : 2 ≤ n := (le_max_right _ _).trans hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  apply (le_div_iff₀ hlog).mpr
  obtain ⟨m, hnm, hgap, hf, hs⟩ := next_completion h₁ n
  obtain ⟨hp, he, _⟩ := missing_r n
  have hb := hN m (((le_max_left _ _).trans hn).trans hnm)
  dsimp only at hb
  rw [hgap] at hb
  have hl : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hnm)
  exact (mul_le_mul_of_nonneg_right (le_max_left C 0) hlog.le).trans
    ((mul_le_mul_of_nonneg_left hl (le_max_right C 0)).trans (hb hp he hf hs))

/-- Both subproblems are necessary. In particular no bound on ordinary repeat
occurrences, nor on first occurrences which leave a smaller gap missing, is required. -/
theorem converse (h : type_of% @Erdos853.erdos_853.parts.ii) : H1 ∧ H2 := by
  constructor
  · intro g hp he
    have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      ((tendsto_atTop.mp h (g + 1)).and (tendsto_atTop.mp hlog 1))
    obtain ⟨hr, hl⟩ := hN N le_rfl
    change (g : ℝ) + 1 ≤ (r N : ℝ) / Real.log N at hr
    change 1 ≤ Real.log N at hl
    have ha := (le_div_iff₀ (by linarith : 0 < Real.log N)).mp hr
    have hb : (g : ℝ) + 1 ≤ (g + 1) * Real.log N := le_mul_of_one_le_right (by positivity) hl
    have hg : g < r N := by exact_mod_cast (show (g : ℝ) < r N by linarith)
    obtain ⟨i, _, hi⟩ := seen_below hg hp he
    exact ⟨i, hi⟩
  · intro C
    filter_upwards [tendsto_atTop.mp h C, eventually_ge_atTop (2 : ℕ)] with n hn hn2
    dsimp only
    intro hp he hf _
    have hm : 0 < primeGap (n+1) ∧ primeGap (n+1) % 2 = 0 ∧
        ¬ ∃ i ≤ n, primeGap i = primeGap (n+1) :=
      ⟨hp, he, fun ⟨i, hi, hit⟩ => hf i hi hit⟩
    have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    exact ((le_div_iff₀ hl).mp hn).trans (by exact_mod_cast r_le_missing hm)

end OMA.R_Erdos853_erdos_853_parts_ii_R1
