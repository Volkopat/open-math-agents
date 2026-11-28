import OMAStatements.S_oeis_a137225

-- Problem: A137225: Triangle T(k,q) of minimal q-Niven numbers: smallest number such that the sum of its digits in base q equals k, 2<=q<=k+1.
-- Upstream: formal-conjectures statements/oeis-a137225.lean:0 (declaration OMA.S_oeis_a137225.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: let f(2m) = 3^m - 1 and f(2m+1) = 2*3^m - 1. Then f(d+2) = 3 f(d) + 2 and
-- f(d+1) <= 3 f(d) + 1, so f(digit sum of x) <= x by strong induction on x = 3q + r
-- (the digit sum of x is r plus that of q). The ternary digits of f(d) sum to d, so T(k,3) = f(k).
-- f is strictly increasing and its image is the set of A062318, so Nat.nth of that set is f.

open OMA.S_oeis_a137225 in
theorem OMA.solution : type_of% @OMA.S_oeis_a137225.main := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ d, f d =
      if d % 2 = 0 then 3 ^ (d / 2) - 1 else 2 * 3 ^ (d / 2) - 1 := ⟨_, fun _ => rfl⟩
  have Fe : ∀ m, f (2 * m) = 3 ^ m - 1 := by
    intro m
    rw [hf, if_pos (show 2 * m % 2 = 0 by omega), show 2 * m / 2 = m by omega]
  have Fo : ∀ m, f (2 * m + 1) = 2 * 3 ^ m - 1 := by
    intro m
    rw [hf, if_neg (show ¬ ((2 * m + 1) % 2 = 0) by omega), show (2 * m + 1) / 2 = m by omega]
  have F0 : f 0 = 0 := by simpa using Fe 0
  have F1 : f 1 = 1 := by simpa using Fo 0
  have F3 : ∀ d, f (d + 2) = 3 * f d + 2 := by
    intro d
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
    · have h1 := Fe (m + 1)
      have h2 := Fe m
      have h3 : 0 < 3 ^ m := by positivity
      rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_succ] at h1
      rw [h1, h2]
      omega
    · have h1 := Fo (m + 1)
      have h2 := Fo m
      have h3 : 0 < 3 ^ m := by positivity
      rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by ring, pow_succ] at h1
      rw [h1, h2]
      omega
  have F2 : f 2 = 2 := by
    have h := F3 0
    rw [F0] at h
    simpa using h
  have L : ∀ d, f (d + 1) ≤ 3 * f d + 1 ∧ f (d + 2) ≤ 3 * f (d + 1) + 1 := by
    intro d
    induction d with
    | zero =>
      simp only [zero_add]
      omega
    | succ d ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have h1 := F3 (d + 1)
      have h2 := F3 d
      rw [show d + 1 + 2 = d + 3 by ring] at h1
      rw [show d + 1 + 2 = d + 3 by ring, show d + 1 + 1 = d + 2 by ring]
      omega
  have Lt : ∀ d, f d < f (d + 1) ∧ f (d + 1) < f (d + 2) := by
    intro d
    induction d with
    | zero =>
      simp only [zero_add]
      omega
    | succ d ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have h1 := F3 (d + 1)
      have h2 := F3 d
      rw [show d + 1 + 2 = d + 3 by ring] at h1
      rw [show d + 1 + 2 = d + 3 by ring, show d + 1 + 1 = d + 2 by ring]
      omega
  have hmono : StrictMono f := strictMono_nat_of_lt_succ (fun d => (Lt d).1)
  have hds : ∀ y : ℕ, (Nat.digits 3 (3 * y + 2)).sum = 2 + (Nat.digits 3 y).sum := by
    intro y
    rw [Nat.digits_def' (by norm_num : 1 < 3) (by omega : 0 < 3 * y + 2), List.sum_cons,
      show (3 * y + 2) % 3 = 2 by omega, show (3 * y + 2) / 3 = y by omega]
  have A : ∀ d, (Nat.digits 3 (f d)).sum = d ∧ (Nat.digits 3 (f (d + 1))).sum = d + 1 := by
    intro d
    induction d with
    | zero =>
      simp only [zero_add]
      rw [F0, F1, Nat.digits_def' (by norm_num : 1 < 3) (by norm_num : 0 < 1)]
      norm_num
    | succ d ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨ih2, ?_⟩
      rw [show d + 1 + 1 = d + 2 by ring, F3 d, hds, ih1]
      omega
  have M : ∀ x, f ((Nat.digits 3 x).sum) ≤ x := by
    intro x
    induction x using Nat.strong_induction_on with
    | _ x ih =>
      rcases Nat.eq_zero_or_pos x with h0 | hpos
      · subst h0
        simp [F0]
      · have hq := ih (x / 3) (by omega)
        rw [Nat.digits_def' (by norm_num : 1 < 3) hpos, List.sum_cons]
        have hx : 3 * (x / 3) + x % 3 = x := Nat.div_add_mod x 3
        have hr : x % 3 < 3 := Nat.mod_lt x (by norm_num)
        generalize (Nat.digits 3 (x / 3)).sum = s at hq ⊢
        generalize x % 3 = r at hx hr ⊢
        generalize x / 3 = q at hq hx
        rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
        · rw [zero_add]
          omega
        · rw [add_comm]
          have := (L s).1
          omega
        · rw [add_comm]
          have := F3 s
          omega
  have hP : ∀ d, InA062318 (f d) := by
    intro d
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' d
    · exact ⟨m, Or.inl (Fe m)⟩
    · exact ⟨m, Or.inr (Fo m)⟩
  have hP' : ∀ x, InA062318 x → ∃ d, f d = x := by
    rintro x ⟨m, rfl | rfl⟩
    · exact ⟨2 * m, Fe m⟩
    · exact ⟨2 * m + 1, Fo m⟩
  have hinf : (Set.ofPred InA062318).Infinite :=
    Set.infinite_of_injective_forall_mem hmono.injective (fun d => hP d)
  have hD : ∀ n : ℕ, ∀ hfin : (Set.ofPred InA062318).Finite, n < hfin.toFinset.card :=
    fun _ hfin => absurd hfin hinf
  have hEq := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := InA062318) f
    (by
      intro y hy
      obtain ⟨d, hd⟩ := hP' y hy
      exact ⟨d, hD d, hd⟩)
    (by
      intro d _
      exact hP d)
    (hmono.strictMonoOn _)
  have hT : ∀ k, T k 3 = f k := by
    intro k
    unfold T
    apply le_antisymm
    · exact Nat.sInf_le (A k).1
    · have hmem := Nat.sInf_mem
        (⟨f k, (A k).1⟩ : {x : ℕ | (Nat.digits 3 x).sum = k}.Nonempty)
      have h := M (sInf {x : ℕ | (Nat.digits 3 x).sum = k})
      rw [show (Nat.digits 3 (sInf {x : ℕ | (Nat.digits 3 x).sum = k})).sum = k from hmem] at h
      exact h
  intro k _
  rw [hT k]
  unfold A062318
  rw [show k + 1 - 1 = k by omega]
  exact hEq (show k ∈ {n : ℕ | ∀ hfin : (Set.ofPred InA062318).Finite,
    n < hfin.toFinset.card} from hD k)
