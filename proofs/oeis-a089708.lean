import OMAStatements.S_oeis_a089708

/-! Fourth-order asymptotics of the pair-difference sequence A089708, introduced
by Amarnath Murthy. Dean Hickerson gave the coefficients in the OEIS entry.
The constant is positive; identifying it with the Bessel value noted by
Václav Kotěšovec is unnecessary for this statement. -/

namespace PairDifferences

open OMA.S_oeis_a089708

private theorem append_term (n : ℕ) (hn : 2 ≤ n) :
    aList (n+1) = aList n ++ [a n + pairDiffSum (aList n)] := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 k]
  rfl

theorem next_term (n : ℕ) (hn : 2 ≤ n) :
    a (n+1) = a n + pairDiffSum (aList n) := by
  change (aList (n+1)).getLastD 0 = _
  rw [append_term n hn]
  simp

private theorem list_succ (n : ℕ) (hn : 2 ≤ n) :
    aList (n+1) = aList n ++ [a (n+1)] := by
  rw [append_term n hn, next_term n hn]

private theorem list_length (n : ℕ) : (aList n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases n with _ | _ | n
    · rfl
    · rfl
    · rw [list_succ _ (by omega)]
      simp [ih]

private theorem step_ge (n : ℕ) (hn : 2 ≤ n) : a n ≤ a (n+1) := by
  rw [next_term n hn]
  omega

private theorem list_bounded (n : ℕ) : ∀ x ∈ aList n, x ≤ a n := by
  induction n with
  | zero => simp [aList]
  | succ n ih =>
    rcases n with _ | _ | n
    · decide
    · decide
    · rw [list_succ _ (by omega)]
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact (ih x h).trans (step_ge _ (by omega))
      · simp only [List.mem_singleton] at h
        exact h.le

private theorem pair_append (xs : List ℕ) (y : ℕ) (hy : ∀ x ∈ xs, x ≤ y) :
    (pairDiffSum (xs ++ [y]) : ℝ) = pairDiffSum xs + (xs.length : ℝ)*y - xs.sum := by
  induction xs with
  | nil => simp [pairDiffSum]
  | cons x xs ih =>
    have bound := hy x (List.mem_cons_self ..)
    have realbound : (x:ℝ) ≤ y := by exact_mod_cast bound
    have tail := ih (fun z hz => hy z (List.mem_cons_of_mem _ hz))
    simp [pairDiffSum, List.pure_def, List.flatMap_append, abs_of_nonneg (sub_nonneg.mpr realbound)] at tail ⊢
    linarith

noncomputable def diff (n : ℕ) : ℝ := (a n : ℝ) - (a (n-1) : ℝ)

theorem diff_next (n : ℕ) : diff (n+1) = (a (n+1) : ℝ) - a n := by simp [diff]

private theorem diff_pair (n : ℕ) (hn : 2 ≤ n) : diff (n+1) = (pairDiffSum (aList n) : ℝ) := by
  rw [diff_next, next_term n hn, Nat.cast_add]
  ring

private theorem increment (n : ℕ) (hn : 2 ≤ n) :
    diff (n+2) - diff (n+1) = (n:ℝ) * a (n+1) - (aList n).sum := by
  rw [diff_pair (n+1) (by omega), diff_pair n hn, list_succ n hn,
    pair_append, list_length]
  · ring
  · intro x hx
    exact (list_bounded n x hx).trans (by rw [next_term n hn]; omega)

theorem diff_three : diff 3 = 1 := by norm_num [diff, a, aList, pairDiffSum]
theorem diff_four : diff 4 = 4 := by norm_num [diff, a, aList, pairDiffSum]

theorem recurrence (n : ℕ) (hn : 3 ≤ n) :
    diff (n+2) = ((n+2 : ℕ) : ℝ) * diff (n+1) - diff n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hk : 2 ≤ 2+k := by omega
  have h₀ := increment (2+k) hk
  have h₁ := increment ((2+k)+1) (by omega)
  rw [list_succ _ hk, List.sum_append] at h₁
  simp only [List.sum_cons, List.sum_nil, add_zero, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat] at h₁ h₀ ⊢
  have hd := diff_next ((2+k)+1)
  have e : 3+k = 2+k+1 := by omega
  rw [e]
  linarith only [h₀,h₁,hd,show (2:ℝ)+(k:ℝ)+1 = 3+k by ring,
     congrArg (fun x : ℝ => (2+(k:ℝ)+1)*x) hd]

end PairDifferences


open Filter
open scoped Topology BigOperators

namespace DiffAsymptotic

/-- Reciprocal factorial times reciprocal falling factorial. -/
noncomputable def weight : ℕ → ℝ → ℝ
  | 0, _ => 1
  | r + 1, x => weight r (x - 1) / (x * (r + 1 : ℕ))

private lemma weight_bounds (r : ℕ) (x : ℝ) (hx : r ≤ x) :
    0 ≤ weight r x ∧ weight r x ≤ 1 := by
  induction r generalizing x with
  | zero => simp [weight]
  | succ r ih =>
    push_cast at hx
    obtain ⟨hlo, hhi⟩ := ih (x-1) (by linarith)
    have hr : 0 ≤ (r : ℝ) := by positivity
    have hx' : 1 ≤ x := by linarith
    rw [weight]
    push_cast
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < x * ((r : ℝ)+1))).mpr
      nlinarith [mul_nonneg (show 0 ≤ x by linarith) hr]

private lemma weight_limit (r : ℕ) :
    Tendsto (fun n : ℕ => weight (r+1) n) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ tendsto_one_div_atTop_nhds_zero_nat
  · filter_upwards [eventually_ge_atTop (r+1)] with n hn
    exact (weight_bounds (r+1) n (by exact_mod_cast hn)).1
  · filter_upwards [eventually_ge_atTop (r+1)] with n hn
    have hx : (r : ℝ) + 1 ≤ n := by exact_mod_cast hn
    have hr : 0 ≤ (r : ℝ) := by positivity
    have hn' : 0 < (n : ℝ) := by linarith
    have hu := (weight_bounds r ((n : ℝ)-1) (by linarith)).2
    rw [weight]
    push_cast
    apply (div_le_div_iff₀ (by positivity) hn').mpr
    nlinarith [mul_le_mul_of_nonneg_right hu hn'.le, mul_nonneg hn'.le hr]

private lemma weight_shift (r : ℕ) (x : ℝ) (hx : (r : ℝ) < x) :
    weight r (x-1) * (x-r) = weight r x * x := by
  induction r generalizing x with
  | zero => simp [weight]
  | succ r ih =>
    push_cast at hx ⊢
    have hr : 0 ≤ (r : ℝ) := by positivity
    have e := ih (x-1) (by linarith)
    simp only [weight, Nat.cast_add, Nat.cast_one]
    field_simp [show x ≠ 0 by linarith, show x-1 ≠ 0 by linarith,
      show (r:ℝ)+1 ≠ 0 by positivity]
    nlinarith [e]

private lemma weight_step (r : ℕ) (x : ℝ) (hx : (r : ℝ) < x) :
    weight (r+1) x - weight (r+1) (x+1) = weight r (x-1) / (x*(x+1)) := by
  have e := weight_shift r x hx
  have hr : 0 ≤ (r:ℝ) := by positivity
  simp only [weight, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  field_simp [show x ≠ 0 by linarith, show x+1 ≠ 0 by linarith,
    show (r:ℝ)+1 ≠ 0 by positivity]
  nlinarith [e]

private lemma norm_rec (d : ℕ → ℝ)
    (rec : ∀ n : ℕ, 3 ≤ n → d (n+2) = (n+2 : ℕ) * d (n+1) - d n)
    (n : ℕ) (hn : 3 ≤ n) :
    d (n+1) / ((n+1).factorial : ℝ) - d (n+2) / ((n+2).factorial : ℝ) =
      (d n / (n.factorial : ℝ)) / (((n:ℝ)+1) * (n+2)) := by
  rw [rec n hn, Nat.factorial_succ (n+1), Nat.factorial_succ n]
  push_cast
  have hf : (0 : ℝ) < n.factorial := by positivity
  field_simp
  ring

private lemma normalized_limit (u : ℕ → ℝ) (u3 : u 3 = 1/6) (u4 : u 4 = 1/6)
    (rec : ∀ n : ℕ, 3 ≤ n → u (n+1) - u (n+2) = u n / (((n:ℝ)+1)*(n+2))) :
    ∃ c : ℝ, 0 < c ∧ Tendsto u atTop (𝓝 c) ∧ ∀ n : ℕ, 4 ≤ n → 0 ≤ u n ∧ u n ≤ 1 := by
  have bounds (j : ℕ) : 0 ≤ u (j+3) ∧ u (j+3) ≤ 1/6 ∧
      1/8 + 1/(6*((j:ℝ)+4)) ≤ u (j+4) ∧ u (j+4) ≤ 1/6 := by
    induction j with
    | zero => norm_num [u3,u4]
    | succ j ih =>
      obtain ⟨hlo,hhi,hL,hU⟩ := ih
      have e := rec (j+3) (by omega)
      have hj : 0 ≤ (j:ℝ) := by positivity
      simp only [Nat.cast_add, Nat.cast_ofNat] at e
      have hn : ((j:ℝ)+3+1)*((j:ℝ)+3+2) = (j+4)*(j+5) := by ring
      rw [hn] at e
      have hD : 0 < ((j:ℝ)+4)*(j+5) := by positivity
      have lo := div_nonneg hlo hD.le
      have hi := div_le_div_of_nonneg_right hhi hD.le
      have tel : 1/(6*((j:ℝ)+4)) - 1/(6*((j:ℝ)+5)) = (1/6)/((j+4)*(j+5)) := by
        field_simp
        ring
      have hp : 0 ≤ 1/(6*((j:ℝ)+4)) := by positivity
      push_cast
      change 0 ≤ u (j+4) ∧ u (j+4) ≤ 1/6 ∧
        1/8 + 1/(6*((j:ℝ)+1+4)) ≤ u (j+5) ∧ u (j+5) ≤ 1/6
      rw [show (j:ℝ)+1+4 = j+5 by ring]
      exact ⟨by linarith, hU, by linarith, by linarith⟩
  let v (j : ℕ) := u (j+4)
  have anti : Antitone v := by
    apply antitone_nat_of_succ_le
    intro j
    have e := rec (j+3) (by omega)
    have lo := (bounds j).1
    have hp : 0 ≤ u (j+3) / (((j+3:ℕ):ℝ)+1) / (((j+3:ℕ):ℝ)+2) := by positivity
    rw [← div_mul_eq_div_div] at hp
    change u (j+5) ≤ u (j+4)
    linarith
  have lower (j : ℕ) : 1/8 ≤ v j := by
    have h := (bounds j).2.2.1
    have hp : 0 ≤ 1/(6*((j:ℝ)+4)) := by positivity
    dsimp [v]
    linarith
  let c := ⨅ j, v j
  have lim : Tendsto v atTop (𝓝 c) := tendsto_atTop_ciInf anti
    ⟨1/8, by rintro _ ⟨j,rfl⟩; exact lower j⟩
  have hc : 1/8 ≤ c := ge_of_tendsto' lim lower
  refine ⟨c, by linarith, (tendsto_add_atTop_iff_nat 4).mp lim, ?_⟩
  rintro (_ | _ | _ | _ | n) hn <;> try omega
  have lo := lower n
  have hi := (bounds n).2.2.2
  exact ⟨by change 0 ≤ v n; linarith, by linarith⟩

private noncomputable def partialWeight (r : ℕ) (x : ℝ) :=
  ∑ j ∈ Finset.range r, weight j x

private lemma partial_succ (r : ℕ) (x : ℝ) :
    partialWeight (r+1) x = partialWeight r x + weight r x := Finset.sum_range_succ ..

private lemma partial_step (r : ℕ) (x : ℝ) (hx : (r : ℝ) < x) :
    partialWeight (r+1) x - partialWeight (r+1) (x+1) =
      partialWeight r (x-1) / (x*(x+1)) := by
  induction r with
  | zero => simp [partialWeight, weight]
  | succ r ih =>
    have h := ih (by push_cast at hx; linarith)
    have e := weight_step r x (by push_cast at hx; linarith)
    rw [partial_succ (r+1) x, partial_succ (r+1) (x+1), partial_succ r (x-1), add_div]
    linarith

private lemma partial_limit (r : ℕ) :
    Tendsto (fun n : ℕ => partialWeight (r+1) n) atTop (𝓝 1) := by
  induction r with
  | zero => simp [partialWeight, weight]
  | succ r ih =>
    simpa only [← partial_succ, add_zero] using ih.add (weight_limit r)

private lemma nonneg_tail {v : ℕ → ℝ} (k : ℕ) (lim : Tendsto v atTop (𝓝 0))
    (dec : ∀ n : ℕ, k ≤ n → v (n+1) ≤ v n) (n : ℕ) (hn : k ≤ n) : 0 ≤ v n := by
  apply le_of_tendsto lim
  filter_upwards [eventually_ge_atTop n] with m hm
  induction m, hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (dec m (hn.trans hm)).trans ih

/-- The expansion in the falling-factorial basis holds at every finite order. -/
theorem expansion (d : ℕ → ℝ) (h3 : d 3 = 1) (h4 : d 4 = 4)
    (rec : ∀ n : ℕ, 3 ≤ n → d (n+2) = (n+2 : ℕ) * d (n+1) - d n) :
    ∃ c : ℝ, 0 < c ∧ ∀ r n : ℕ, r + 4 ≤ n →
      0 ≤ d n / (n.factorial : ℝ) - c * ∑ j ∈ Finset.range r, weight j n ∧
      d n / (n.factorial : ℝ) - c * ∑ j ∈ Finset.range r, weight j n ≤ weight r n := by
  let u (n : ℕ) := d n / (n.factorial : ℝ)
  have urec := norm_rec d rec
  obtain ⟨c, hc, lim, bounds⟩ := normalized_limit u
    (by norm_num [u, h3, Nat.factorial]) (by norm_num [u, h4, Nat.factorial]) urec
  let rem (r n : ℕ) := u n - c * partialWeight r n
  have rlim (r : ℕ) : Tendsto (rem (r+1)) atTop (𝓝 0) := by
    simpa [rem] using lim.sub ((partial_limit r).const_mul c)
  refine ⟨c, hc, ?_⟩
  change ∀ r n : ℕ, r + 4 ≤ n → 0 ≤ rem r n ∧ rem r n ≤ weight r n
  intro r
  induction r with
  | zero =>
    intro n hn
    simpa [rem, partialWeight, weight] using bounds n hn
  | succ r ih =>
    let k := r + 1 + 4
    have dif (n : ℕ) (hn : k ≤ n) :
        rem (r+1) n - rem (r+1) (n+1) =
          rem r (n-1) / ((n:ℝ)*(n+1)) := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by dsimp [k] at hn; omega⟩
      have hm : 3 ≤ m := by dsimp [k] at hn; omega
      have hu : u (m+1) - u (m+2) = u m / (((m:ℝ)+1)*(m+2)) := urec m hm
      have hmr : (r : ℝ) < (m : ℝ) + 1 := by exact_mod_cast (show r < m+1 by dsimp [k] at hn; omega)
      have hw := partial_step r ((m:ℝ)+1) hmr
      rw [add_sub_cancel_right, show (m:ℝ)+1+1=m+2 by ring] at hw
      simp only [rem, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [show (m:ℝ)+1+1=m+2 by ring, sub_div, mul_div_assoc]
      linear_combination hu - c * hw
    have wd (n : ℕ) (hn : k ≤ n) : weight (r+1) n - weight (r+1) (n+1) =
        weight r ((n-1:ℕ):ℝ) / ((n:ℝ)*(n+1)) := by
      rw [Nat.cast_sub (by dsimp [k] at hn; omega), Nat.cast_one]
      exact weight_step r n (by exact_mod_cast (show r < n by dsimp [k] at hn; omega))
    intro n hn
    constructor
    · apply nonneg_tail k (rlim r) _ n hn
      intro m hm
      have h := div_nonneg (ih (m-1) (by dsimp [k] at hm; omega)).1
        (show (0:ℝ) ≤ m*(m+1) by positivity)
      linarith [dif m hm]
    · have pos := nonneg_tail (v := fun m => weight (r+1) m - rem (r+1) m) k
        (by simpa using (weight_limit r).sub (rlim r)) (fun m hm => by
          have h := div_le_div_of_nonneg_right (ih (m-1) (by dsimp [k] at hm; omega)).2
            (show (0:ℝ) ≤ m*(m+1) by positivity)
          have hW := wd m hm
          push_cast
          linarith [dif m hm]) n hn
      linarith

end DiffAsymptotic


namespace DiffReconstruct

private def approx (w : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + 2 * w 1 x + 5 * w 2 x + 16 * w 3 x + 65 * w 4 x

private noncomputable def poly (x : ℝ) : ℝ :=
  1 + 2 / x + (5 / 2 : ℝ) / x ^ 2 + (31 / 6 : ℝ) / x ^ 3 + (317 / 24 : ℝ) / x ^ 4

private lemma shift_identity (w : ℕ → ℝ → ℝ) (w0 : ∀ x, w 0 x = 1)
    (ws : ∀ (r : ℕ) (x : ℝ), w (r+1) x = w r (x-1) / (x * (r+1 : ℕ)))
    (x : ℝ) (hx : 0 < x) :
    (∑ j ∈ Finset.range 5, w j x) + approx w (x-1) / x - approx w x = 325 * w 5 x := by
  have step (r : ℕ) : w r (x-1) / x = (r+1 : ℕ) * w (r+1) x := by
    rw [ws]; push_cast; field_simp
  have h0 := step 0
  have h1 := step 1
  have h2 := step 2
  have h3 := step 3
  have h4 := step 4
  norm_num [approx,Finset.sum_range_succ,w0] at h0 h1 h2 h3 h4 ⊢
  linear_combination h0 + 2*h1 + 5*h2 + 16*h3 + 65*h4

private lemma fifth_weight (w : ℕ → ℝ → ℝ) (w0 : ∀ x, w 0 x = 1)
    (ws : ∀ (r : ℕ) (x : ℝ), w (r+1) x = w r (x-1) / (x * (r+1 : ℕ)))
    (x : ℝ) (hx : 10 ≤ x) : 0 ≤ w 5 x ∧ w 5 x ≤ 1 / x^5 := by
  have val : w 5 x = 1 / (120 * x * (x-1) * (x-2) * (x-3) * (x-4)) := by
    norm_num [ws,w0,sub_sub]
    field_simp [show x ≠ 0 by linarith, show x-1 ≠ 0 by linarith, show x-2 ≠ 0 by linarith, show x-3 ≠ 0 by linarith, show x-4 ≠ 0 by linarith]; ring
  have hx0 : 0 < x := by linarith
  have h1 : 0 < x-1 := by linarith
  have h2 : 0 < x-2 := by linarith
  have h3 : 0 < x-3 := by linarith
  have h4 : 0 < x-4 := by linarith
  rw [val]
  refine ⟨by positivity, one_div_le_one_div_of_le (by positivity) ?_⟩
  calc
    x^5 = 16*x*(x/2)*(x/2)*(x/2)*(x/2) := by ring
    _ ≤ 120*x*(x-1)*(x-2)*(x-3)*(x-4) := by
      gcongr <;> linarith

private lemma rational_tail (w : ℕ → ℝ → ℝ) (w0 : ∀ x, w 0 x = 1)
    (ws : ∀ (r : ℕ) (x : ℝ), w (r+1) x = w r (x-1) / (x * (r+1 : ℕ)))
    (x : ℝ) (hx : 10 ≤ x) : |approx w x - poly x| ≤ 1000 / x^5 := by
  have hx0 : 0 < x := by linarith
  have h1 : 0 < x-1 := by linarith
  have h2 : 0 < x-2 := by linarith
  have h3 : 0 < x-3 := by linarith
  have val : approx w x - poly x =
      (898*x^2-2743*x+1902) / (24*x^4*((x-1)*(x-2)*(x-3))) := by
    norm_num [approx,poly,ws,w0,sub_sub]
    field_simp [hx0.ne',h1.ne',h2.ne',h3.ne']; ring
  have bound : |898*x^2-2743*x+1902| ≤ 3000*x^2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x-10)]
  have denom : 0 < 24*x^4*((x-1)*(x-2)*(x-3)) := by positivity
  rw [val,abs_div,abs_of_pos denom]
  calc
    _ ≤ (3000*x^2) / (24*x^4*((x-1)*(x-2)*(x-3))) := by gcongr
    _ ≤ 1000 / x^5 := by
      apply (div_le_div_iff₀ denom (by positivity)).2
      calc
        _ = 1000 * (24*x^4*((x/2)*(x/2)*(x/2))) := by ring
        _ ≤ _ := by gcongr <;> linarith

private lemma shrink (A x : ℝ) (hA : 0 ≤ A) (hx : 64 ≤ x) :
    (A / x^5) / (x+1) ≤ (A/2) / (x+1)^5 := by
  have x0 : 0 < x := by linarith
  have y0 : 0 < x+1 := by linarith
  have slope : 2 * (x+1)^4 ≤ x^5 := calc
    _ ≤ 2 * (2*x)^4 := by gcongr; linarith
    _ = 32*x^4 := by ring
    _ ≤ x*x^4 := by gcongr; linarith
    _ = x^5 := by ring
  calc
    _ = A / (2*(x+1)^5) * (2*(x+1)^4 / x^5) := by field_simp
    _ ≤ A / (2*(x+1)^5) * 1 := by
      gcongr
      exact (div_le_one (by positivity)).2 slope
    _ = _ := by field_simp

theorem reconstruct (a d : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (w : ℕ → ℝ → ℝ) (w0 : ∀ x, w 0 x = 1)
    (ws : ∀ (r : ℕ) (x : ℝ), w (r+1) x = w r (x-1) / (x * (r+1 : ℕ)))
    (hd : ∀ n : ℕ, 3 ≤ n → d (n+1) = a (n+1) - a n)
    (hu : ∀ n : ℕ, 9 ≤ n →
        0 ≤ d n / (n.factorial : ℝ) - c * ∑ j ∈ Finset.range 5, w j n ∧
        d n / (n.factorial : ℝ) - c * ∑ j ∈ Finset.range 5, w j n ≤ w 5 n) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => a n / (n.factorial : ℝ) -
        c * (1 + 2 / (n : ℝ) + (5 / 2 : ℝ) / (n : ℝ)^2 +
          (31 / 6 : ℝ) / (n : ℝ)^3 + (317 / 24 : ℝ) / (n : ℝ)^4))
      (fun n : ℕ => (1 : ℝ) / (n : ℝ)^5) := by
  let v (n : ℕ) := a n / (n.factorial : ℝ)
  let e (n : ℕ) := v n - c * approx w n
  let K := 1 + 325*c
  let A := |e 64| * 64^5 + 2*K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have vstep (n : ℕ) (hn : 3 ≤ n) :
      v (n+1) = d (n+1) / ((n+1).factorial : ℝ) + v n / ((n:ℝ)+1) := by
    have hn0 : 0 < (n.factorial : ℝ) := by positivity
    rw [hd n hn]
    dsimp [v]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have estep (n : ℕ) (hn : 64 ≤ n) :
      |e (n+1)| ≤ |e n| / ((n:ℝ)+1) + K / ((n:ℝ)+1)^5 := by
    let x : ℝ := (n:ℝ)+1
    have hx : 10 ≤ x := by dsimp [x]; exact_mod_cast (by omega : 10 ≤ n+1)
    have hx0 : 0 < x := by linarith
    let u := d (n+1) / ((n+1).factorial : ℝ) - c * ∑ j ∈ Finset.range 5, w j x
    have he : 0 ≤ u ∧ u ≤ w 5 x := by
      have h := hu (n+1) (by omega)
      simpa only [u,x,Nat.cast_add,Nat.cast_one] using h
    have hw := fifth_weight w w0 ws x hx
    have s := shift_identity w w0 ws x hx0
    have eq : e (n+1) = e n / x + (u + 325*c*w 5 x) := by
      dsimp only [e,u]
      rw [vstep n (by omega)]
      rw [show (n:ℝ) = x-1 by dsimp [x]; ring]
      rw [show ((n+1 : ℕ) : ℝ) = x by simp [x]]
      dsimp only [x] at s ⊢
      linear_combination c*s
    change |e (n+1)| ≤ |e n| / x + K / x^5
    rw [eq]
    calc
      _ ≤ |e n / x| + |u + 325*c*w 5 x| := abs_add_le ..
      _ = |e n| / x + (u + 325*c*w 5 x) := by
        rw [abs_div,abs_of_pos hx0,abs_of_nonneg (by nlinarith [mul_nonneg hc.le hw.1] : 0 ≤ u+325*c*w 5 x)]
      _ ≤ _ := by
        dsimp [K]
        have hp := mul_le_mul_of_nonneg_left hw.2 (show 0 ≤ 325*c by positivity)
        rw [add_div, div_eq_mul_one_div (325*c)]
        linarith only [he.2.trans hw.2,hp]
  have bound : ∀ n : ℕ, 64 ≤ n → |e n| ≤ A / (n:ℝ)^5 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      norm_num [A]
      linarith
    | succ n hn ih =>
      have h64 : 64 ≤ (n:ℝ) := by exact_mod_cast hn
      have hsmall := shrink A n hA h64
      have hy : 0 < (n:ℝ)+1 := by positivity
      have ha : K ≤ A/2 := by dsimp [A]; nlinarith [abs_nonneg (e 64)]
      calc
        _ ≤ |e n| / ((n:ℝ)+1) + K / ((n:ℝ)+1)^5 := estep n hn
        _ ≤ A / (n:ℝ)^5 / ((n:ℝ)+1) + K / ((n:ℝ)+1)^5 := by gcongr
        _ ≤ (A/2) / ((n:ℝ)+1)^5 + (A/2) / ((n:ℝ)+1)^5 := by gcongr
        _ = _ := by push_cast; ring
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨A + c*1000, Filter.eventually_atTop.mpr ⟨64, ?_⟩⟩
  intro n hn
  have hn10 : 10 ≤ (n:ℝ) := by exact_mod_cast (by omega : 10 ≤ n)
  have hn0 : 0 < (n:ℝ) := by linarith
  change ‖v n - c * poly n‖ ≤ (A+c*1000) * ‖1/(n:ℝ)^5‖
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 1/(n:ℝ)^5)]
  calc
    _ = |e n + c * (approx w n - poly n)| := by dsimp [e]; ring_nf
    _ ≤ |e n| + |c * (approx w n - poly n)| := abs_add_le ..
    _ ≤ A/(n:ℝ)^5 + c*(1000/(n:ℝ)^5) := by
      rw [abs_mul,abs_of_pos hc]
      gcongr
      · exact bound n hn
      · exact rational_tail w w0 ws n hn10
    _ = _ := by ring

end DiffReconstruct

theorem OMA.solution : type_of% @OMA.S_oeis_a089708.main := by
  obtain ⟨c, hc, h⟩ := DiffAsymptotic.expansion PairDifferences.diff
    PairDifferences.diff_three PairDifferences.diff_four PairDifferences.recurrence
  refine ⟨c, hc, ?_⟩
  exact DiffReconstruct.reconstruct (fun n => (OMA.S_oeis_a089708.a n : ℝ))
    PairDifferences.diff c hc DiffAsymptotic.weight (fun _ => rfl)
    (fun _ _ => rfl) (fun n _ => PairDifferences.diff_next n) (fun n hn => h 5 n hn)
