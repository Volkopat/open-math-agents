import OMAStatements.S_oeis_a095720

/-!
In each set of three consecutive integers {3t-2, 3t-1, 3t}, the first is
chosen on an odd turn, and exactly one of the last two is chosen on an even
turn. Tracking which pairs already have an even term gives a uniform bound
of one on the difference between an even term and twice the preceding term.
-/

namespace LaymanRatio

open OMA.S_oeis_a095720 Filter Topology

private noncomputable def mex (l : List ℕ) := sInf {m : ℕ | 1 ≤ m ∧ m ∉ l}

private theorem mex_eq {l : List ℕ} {v : ℕ} (hv : 0 < v) (fresh : v ∉ l)
    (used : ∀ x, 0 < x → x < v → x ∈ l) : mex l = v := by
  have mem : v ∈ {m : ℕ | 1 ≤ m ∧ m ∉ l} := ⟨hv, fresh⟩
  apply le_antisymm (csInf_le (OrderBot.bddBelow _) mem)
  apply le_csInf ⟨v, mem⟩
  rintro x ⟨hx, hx'⟩
  exact le_of_not_gt (fun h => hx' (used x hx h))

/-- What has appeared after 4j turns. Every positive number through 3j has
appeared. Each remaining occupied pair {3i-1, 3i} contains just one entry. -/
private structure Ready (j : ℕ) (l : List ℕ) : Prop where
  covered : ∀ x, 0 < x → x ≤ 3 * j → x ∈ l
  located : ∀ x, x ∈ l → 3 * j < x →
    ∃ i, j < i ∧ i ≤ 2 * j ∧ 3 * i - 1 ≤ x ∧ x ≤ 3 * i
  paired : ∀ i, j < i → i ≤ 2 * j → (3 * i - 1 ∈ l ↔ 3 * i ∉ l)

private theorem Ready.bound {j l} (h : Ready j l) {x} (hx : x ∈ l) : x ≤ 6 * j := by
  by_cases small : x ≤ 3 * j
  · omega
  · obtain ⟨i, _, _, _, _⟩ := h.located x hx (by omega)
    omega

private theorem advance {j : ℕ} {l : List ℕ} (hj : 0 < j) (h : Ready j l) :
    ∃ s, (s = 3*j+2 ∨ s = 3*j+3) ∧
      mex l = 3*j+1 ∧ mex (l ++ [3*j+1, 6*j+2]) = s ∧
      Ready (j+1) (l ++ [3*j+1, 6*j+2, s, s+(3*j+3)]) := by
  have free : 3*j+1 ∉ l := by
    intro hx
    obtain ⟨i, _, _, _, _⟩ := h.located _ hx (by omega)
    omega
  have pair := h.paired (j+1) (by omega) (by omega)
  rw [show 3*(j+1)-1 = 3*j+2 by omega, show 3*(j+1) = 3*j+3 by omega] at pair
  let s := if 3*j+2 ∈ l then 3*j+3 else 3*j+2
  have hs : s = 3*j+2 ∨ s = 3*j+3 := by unfold s; split <;> simp
  have fresh : s ∉ l := by unfold s; split <;> tauto
  have fills (x : ℕ) (lo : 3*j+2 ≤ x) (hi : x ≤ 3*j+3) : x ∈ l ∨ x = s := by
    obtain rfl | rfl : x = 3*j+2 ∨ x = 3*j+3 := by omega
    · by_cases hc : 3*j+2 ∈ l <;> simp [s, hc]
    · by_cases hc : 3*j+2 ∈ l
      · simp [s, hc]
      · exact Or.inl (by tauto)
  refine ⟨s, hs, mex_eq (by omega) free (fun x hp hl => h.covered x hp (by omega)), ?_, ?_⟩
  · apply mex_eq (by omega)
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, fresh, false_or]
      omega
    · intro x hp hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      by_cases small : x ≤ 3*j
      · exact Or.inl (h.covered x hp small)
      · by_cases edge : x = 3*j+1
        · exact Or.inr (Or.inl edge)
        · exact Or.inl ((fills x (by omega) (by omega)).resolve_right (by omega))
  · constructor
    · intro x hp hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      by_cases small : x ≤ 3*j
      · exact Or.inl (h.covered x hp small)
      · by_cases edge : x = 3*j+1
        · exact Or.inr (Or.inl edge)
        · have := fills x (by omega) (by omega)
          tauto
    · intro x hx hl
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with old | e | e | e | e
      · obtain ⟨i, _, _, _, _⟩ := h.located _ old (by omega)
        exact ⟨i, by omega, by omega, by omega, by omega⟩
      · omega
      · exact ⟨2*j+1, by omega, by omega, by omega, by omega⟩
      · omega
      · exact ⟨2*j+2, by omega, by omega, by omega, by omega⟩
    · intro i lo hi
      by_cases old : i ≤ 2*j
      · have unchanged (x : ℕ) (a : 3*j+3 < x) (b : x < 6*j+2) :
            x ∈ l ++ [3*j+1, 6*j+2, s, s+(3*j+3)] ↔ x ∈ l := by
          simp [show x ≠ 3*j+1 by omega, show x ≠ 6*j+2 by omega,
            show x ≠ s by omega, show x ≠ s+(3*j+3) by omega]
        rw [unchanged _ (by omega) (by omega), unchanged _ (by omega) (by omega)]
        exact h.paired i (by omega) old
      · have xl : 3*i-1 ∉ l := fun hh => by have := h.bound hh; omega
        have xu : 3*i ∉ l := fun hh => by have := h.bound hh; omega
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, xl, xu, false_or]
        omega

private theorem append_step {n : ℕ} (hn : 2 ≤ n) :
    prefixList n = prefixList (n-1) ++
      [if Even n then (prefixList (n-1)).getLastD 0 + 3*n/4 else mex (prefixList (n-1))] := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n-2, by omega⟩
  rfl

private theorem first : Ready 1 (prefixList 4) := by
  have pre : prefixList 2 = [1, 2] := by rw [append_step (n := 2) (by decide)]; rfl
  have m : mex [1, 2] = 3 := mex_eq (by decide) (by decide) (by
    intro x hx hy
    interval_cases x <;> decide)
  have three : prefixList 3 = [1,2,3] := by
    rw [append_step (n := 3) (by decide), if_neg (by decide), pre, m]
    rfl
  have four : prefixList 4 = [1,2,3,6] := by
    rw [append_step (n := 4) (by decide), if_pos (by decide), three]
    rfl
  rw [four]
  constructor
  · intro x hp hx
    simp
    omega
  · intro x hx hl
    simp at hx
    exact ⟨2, by omega, by omega, by omega, by omega⟩
  · intro i lo hi
    have : i = 2 := by omega
    subst i
    decide

private def term (p : ℕ → List ℕ) (n : ℕ) := (p n).getLastD 0

private def Follows (p : ℕ → List ℕ) : Prop := ∀ {n : ℕ}, 5 ≤ n →
  p n = p (n-1) ++ [if Even n then (p (n-1)).getLastD 0 + 3*n/4 else mex (p (n-1))]

private theorem four_turns {p : ℕ → List ℕ} (next : Follows p) {j : ℕ} (hj : 0 < j) (h : Ready j (p (4*j))) :
    Ready (j+1) (p (4*(j+1))) ∧
    term p (4*j+1) = 3*j+1 ∧ term p (4*j+2) = 6*j+2 ∧
    (term p (4*j+3) = 3*j+2 ∨ term p (4*j+3) = 3*j+3) ∧ term p (4*j+4) = term p (4*j+3)+(3*j+3) := by
  obtain ⟨s, hs, h₁, h₂, ready⟩ := advance hj h
  let l := p (4*j)
  have p₁ : p (4*j+1) = l ++ [3*j+1] := by
    rw [next (by omega), if_neg (by rw [Nat.even_iff]; omega), Nat.add_sub_cancel, h₁]
  have p₂ : p (4*j+2) = l ++ [3*j+1,6*j+2] := by
    rw [next (by omega), if_pos (by rw [Nat.even_iff]; omega), show 4*j+2-1 = 4*j+1 by omega, p₁]
    simp
    omega
  have p₃ : p (4*j+3) = l ++ [3*j+1,6*j+2,s] := by
    rw [next (by omega), if_neg (by rw [Nat.even_iff]; omega), show 4*j+3-1 = 4*j+2 by omega, p₂, h₂]
    simp
  have p₄ : p (4*j+4) = l ++ [3*j+1,6*j+2,s,s+(3*j+3)] := by
    rw [next (by omega), if_pos (by rw [Nat.even_iff]; omega), show 4*j+4-1 = 4*j+3 by omega, p₃]
    simp
    omega
  rw [show 4*(j+1) = 4*j+4 by omega, p₄]
  refine ⟨ready, ?_⟩
  simpa [term, p₁, p₂, p₃, p₄] using hs

private theorem bounds {p : ℕ → List ℕ} (next : Follows p) (seed : Ready 1 (p 4))
    (k : ℕ) (hk : 2 ≤ k) :
    k ≤ term p (2*k+1) ∧ 2*term p (2*k+1) ≤ term p (2*k+2) ∧ term p (2*k+2) ≤ 2*term p (2*k+1)+1 := by
  have all (j : ℕ) (hj : 0 < j) : Ready j (p (4*j)) := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hz : j = 0
      · subst j; exact seed
      · exact (four_turns next (by omega) (ih (by omega))).1
  let j := k/2
  have hj : 0 < j := by dsimp [j]; omega
  obtain ⟨_, h₁, h₂, h₃, h₄⟩ := four_turns next hj (all j hj)
  have parity : k = 2*j ∨ k = 2*j+1 := by dsimp [j]; omega
  rcases parity with he | he
  · rw [show 2*k+1 = 4*j+1 by omega, show 2*k+2 = 4*j+2 by omega, h₁, h₂]
    omega
  · rw [show 2*k+1 = 4*j+3 by omega, show 2*k+2 = 4*j+4 by omega, h₄]
    omega

private theorem ratio {p : ℕ → List ℕ} (next : Follows p) (seed : Ready 1 (p 4)) :
    Tendsto (fun k : ℕ => (term p (2*k+2) : ℝ) / term p (2*k+1)) atTop (𝓝 2) := by
  have top : Tendsto (fun k : ℕ => 2 + 1 / (k : ℝ)) atTop (𝓝 2) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun _ : ℕ => (2 : ℝ)) tendsto_const_nhds top
  · filter_upwards [eventually_ge_atTop 2] with k hk
    obtain ⟨hu, hlo, _⟩ := bounds next seed k hk
    have hp : 0 < (term p (2*k+1) : ℝ) := by exact_mod_cast (show 0 < term p (2*k+1) by omega)
    apply (le_div_iff₀ hp).2
    exact_mod_cast hlo
  · filter_upwards [eventually_ge_atTop 2] with k hk
    obtain ⟨hu, _, hhi⟩ := bounds next seed k hk
    have hp : 0 < (term p (2*k+1) : ℝ) := by exact_mod_cast (show 0 < term p (2*k+1) by omega)
    have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hdiv := one_div_le_one_div_of_le hk' (show (k : ℝ) ≤ term p (2*k+1) by exact_mod_cast hu)
    apply le_trans _ (add_le_add_right hdiv (2 : ℝ))
    apply (div_le_iff₀ hp).2
    rw [add_mul, one_div, inv_mul_cancel₀ hp.ne']
    exact_mod_cast hhi

/-- The terms tabulated in OEIS start with 1, 3, 2, 5. This version applies
the same estimate to any continuation of that seed by the stated rule. -/
theorem listed_ratio (p : ℕ → List ℕ) (seed : p 4 = [1,3,2,5])
    (next : ∀ {n : ℕ}, 5 ≤ n → p n = p (n-1) ++ [if Even n then
      (p (n-1)).getLastD 0 + 3*n/4 else sInf {m : ℕ | 1 ≤ m ∧ m ∉ p (n-1)}]) :
    Tendsto (fun k : ℕ => ((p (2*k+2)).getLastD 0 : ℝ) / (p (2*k+1)).getLastD 0) atTop (𝓝 2) := by
  apply ratio (p := p) next
  rw [seed]
  constructor
  · intro x hp hx
    simp
    omega
  · intro x hx hl
    simp at hx
    exact ⟨2, by omega, by omega, by omega, by omega⟩
  · intro i lo hi
    have : i = 2 := by omega
    subst i
    decide

end LaymanRatio

open OMA.S_oeis_a095720 LaymanRatio

theorem OMA.solution : type_of% @OMA.S_oeis_a095720.main := by
  exact ratio (p := prefixList) (fun {_} hn => append_step (by omega)) first
