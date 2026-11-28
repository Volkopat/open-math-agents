import OMAStatements.S_oeis_a222955

-- Problem: A222955: Number of n X 1 0..1 arrays with every row and column least squares fitting to a zero slope straight line, with a single point array taken as having zero slope.
-- Upstream: formal-conjectures statements/oeis-a222955.lean:0 (declaration OMA.S_oeis_a222955.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the rows are single points. For the column of length m >= 2 the denominator of the
-- slope is m^2 (m+1) (m-1) / 12, not 0, and the numerator is m * (P - (m+1)/2 * T) with
-- P = Sum (i+1) w_i and T = Sum w_i. Since rev i + 1 = m - i, posSum w + posSum (reverse w)
-- = (m+1) T, so the slope is 0 iff posSum w = posSum (reverse w). Swapping the double sum gives
-- psSum v = Sum v_i (rev i + 1) = posSum (reverse v), and reverse (reverse w) = w.

open OMA.S_oeis_a222955 in
theorem OMA.solution : type_of% @OMA.S_oeis_a222955.main := by
  have hb : ∀ (b : Fin 2) (c : ℕ), (if b = 1 then c else 0) = (b : ℕ) * c := by
    intro b c
    fin_cases b <;> simp
  have hS1 : ∀ m : ℕ, ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) = (m : ℚ) * ((m : ℚ) + 1) / 2 := by
    intro m
    rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℚ) + 1)) m]
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hS2 : ∀ m : ℕ, ∑ i : Fin m, (((i : ℕ) : ℚ) + 1) ^ 2 =
      (m : ℚ) * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1) / 6 := by
    intro m
    rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℚ) + 1) ^ 2) m]
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hrev : ∀ (m : ℕ) (f : Fin m → ℕ), ∑ i : Fin m, f (Fin.rev i) = ∑ i : Fin m, f i := by
    intro m f
    exact Equiv.sum_comp Fin.revPerm f
  have hpos : ∀ (m : ℕ) (v : Fin m → Fin 2),
      posSum v = ∑ i : Fin m, (v i : ℕ) * ((i : ℕ) + 1) := by
    intro m v
    unfold posSum
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun i _ => hb (v i) ((i : ℕ) + 1))
  have hposrev : ∀ (m : ℕ) (v : Fin m → Fin 2),
      posSum (reverse v) = ∑ i : Fin m, (v i : ℕ) * ((Fin.rev i : ℕ) + 1) := by
    intro m v
    calc posSum (reverse v) = ∑ i : Fin m, (v (Fin.rev i) : ℕ) * ((i : ℕ) + 1) := hpos m (reverse v)
      _ = ∑ i : Fin m, (v (Fin.rev i) : ℕ) * ((Fin.rev (Fin.rev i) : ℕ) + 1) := by
          simp only [Fin.rev_rev]
      _ = ∑ i : Fin m, (v i : ℕ) * ((Fin.rev i : ℕ) + 1) :=
          hrev m (fun i => (v i : ℕ) * ((Fin.rev i : ℕ) + 1))
  have hc : ∀ (m : ℕ) (i : Fin m),
      (Finset.univ.filter (fun j : Fin m => i ≤ j)).card = (Fin.rev i : ℕ) + 1 := by
    intro m i
    rw [Finset.filter_le_eq_Ici, Fin.card_Ici, Fin.val_rev]
    have hi := i.isLt
    omega
  have hps : ∀ (m : ℕ) (v : Fin m → Fin 2),
      psSum v = ∑ i : Fin m, (v i : ℕ) * ((Fin.rev i : ℕ) + 1) := by
    intro m v
    unfold psSum
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, hc m i]
    ring
  intro n hn w
  have hgood : Good (fun i (_ : Fin 1) => w i) ↔ ZeroSlope (fun i => ((w i : ℕ) : ℚ)) := by
    unfold Good
    constructor
    · intro h
      exact h.2 0
    · intro h
      exact ⟨fun _ => Or.inl rfl, fun _ => h⟩
  have hcol : ZeroSlope (fun i => ((w i : ℕ) : ℚ)) ↔ posSum w = posSum (reverse w) := by
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      have hr : reverse w = w := by
        funext i
        show w (Fin.rev i) = w i
        rw [Subsingleton.elim (Fin.rev i) i]
      rw [hr]
      exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
    · have hm : (2 : ℚ) ≤ n := by exact_mod_cast h2
      have hne : n ≠ 1 := by omega
      have hn0 : (n : ℚ) ≠ 0 := ne_of_gt (by linarith)
      have hP : (posSum w : ℚ) = ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) * ((w i : ℕ) : ℚ) := by
        rw [hpos n w]
        push_cast
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      have hQ : (posSum (reverse w) : ℚ) + (posSum w : ℚ) =
          ((n : ℚ) + 1) * ∑ i : Fin n, ((w i : ℕ) : ℚ) := by
        rw [hposrev n w, hpos n w]
        push_cast
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hr : (Fin.rev i : ℕ) + (i : ℕ) + 1 = n := by
          have h := Fin.val_rev i
          have hi := i.isLt
          omega
        have hr' : ((Fin.rev i : ℕ) : ℚ) + ((i : ℕ) : ℚ) + 1 = (n : ℚ) := by exact_mod_cast hr
        linear_combination ((w i : ℕ) : ℚ) * hr'
      have hD : (n : ℚ) * ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) ^ 2 -
          (∑ i : Fin n, (((i : ℕ) : ℚ) + 1)) ^ 2 ≠ 0 := by
        rw [hS1 n, hS2 n]
        have e : (n : ℚ) * ((n : ℚ) * ((n : ℚ) + 1) * (2 * (n : ℚ) + 1) / 6) -
            ((n : ℚ) * ((n : ℚ) + 1) / 2) ^ 2 =
            (n : ℚ) ^ 2 * ((n : ℚ) + 1) * ((n : ℚ) - 1) / 12 := by ring
        rw [e]
        have h3 : (0 : ℚ) < (n : ℚ) - 1 := by linarith
        have h4 : (0 : ℚ) < (n : ℚ) := by linarith
        exact ne_of_gt (div_pos (mul_pos (mul_pos (pow_pos h4 2) (by linarith)) h3) (by norm_num))
      have hslope : lsSlope (fun i => ((w i : ℕ) : ℚ)) = 0 ↔
          (n : ℚ) * ∑ i : Fin n, (((i : ℕ) : ℚ) + 1) * ((w i : ℕ) : ℚ) -
            (∑ i : Fin n, (((i : ℕ) : ℚ) + 1)) * ∑ i : Fin n, ((w i : ℕ) : ℚ) = 0 := by
        unfold lsSlope
        rw [div_eq_zero_iff]
        constructor
        · intro h
          rcases h with h | h
          · exact h
          · exact absurd h hD
        · intro h
          exact Or.inl h
      unfold ZeroSlope
      rw [or_iff_right hne, hslope, hS1 n, ← hP]
      constructor
      · intro h
        have h5 : (n : ℚ) * (2 * (posSum w : ℚ) - ((n : ℚ) + 1) * ∑ i : Fin n, ((w i : ℕ) : ℚ)) =
            0 := by
          linear_combination 2 * h
        rcases mul_eq_zero.mp h5 with h6 | h6
        · exact absurd h6 hn0
        · have h7 : (posSum w : ℚ) = (posSum (reverse w) : ℚ) := by
            linear_combination h6 - hQ
          exact_mod_cast h7
      · intro h
        have h7 : (posSum w : ℚ) = (posSum (reverse w) : ℚ) := by exact_mod_cast h
        linear_combination (n : ℚ) / 2 * hQ + (n : ℚ) / 2 * h7
  have hps' : ∀ v : Fin n → Fin 2, psSum v = posSum (reverse v) := by
    intro v
    rw [hps n v, hposrev n v]
  have hrr : reverse (reverse w) = w := by
    funext i
    show w (Fin.rev (Fin.rev i)) = w i
    rw [Fin.rev_rev]
  refine ⟨hgood.trans hcol, ?_⟩
  rw [hps' w, hps' (reverse w), hrr]
  exact eq_comm
