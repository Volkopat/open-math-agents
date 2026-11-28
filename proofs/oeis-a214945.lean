import OMAStatements.S_oeis_a214945

namespace OMA.S_oeis_a214945

open Finset



/-! ## Words whose property depends only on which letters are equal -/

section Patterns

variable (P : List ℕ → Prop) [DecidablePred P]

/-- P depends only on which letters are equal: it is invariant under injective relabelings. -/
def EqInv : Prop := ∀ f : ℕ → ℕ, Function.Injective f → ∀ l, P (l.map f) ↔ P l

/-- The number of ways to extend the word u by r letters from 0..M-1 so that P holds. -/
def Ext (M : ℕ) (u : List ℕ) (r : ℕ) : ℕ :=
  (univ.filter (fun v : Fin r → Fin M => P (u ++ List.ofFn (fun i => (v i : ℕ))))).card

lemma ext_zero (M : ℕ) (u : List ℕ) : Ext P M u 0 = if P u then 1 else 0 := by
  unfold Ext
  by_cases h : P u <;> simp [h]

lemma ext_succ (M : ℕ) (u : List ℕ) (r : ℕ) :
    Ext P M u (r + 1) = ∑ c : Fin M, Ext P M (u ++ [(c : ℕ)]) r := by
  unfold Ext
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ => Fin M)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro w _
  simp [Fin.consEquiv, List.ofFn_succ]

/-- Exchanging two letters that do not occur in u maps the extensions of u a to those of u b. -/
lemma swap_good (hP : EqInv P) (M : ℕ) (u : List ℕ) (r : ℕ) (a b : Fin M) (ha : (a : ℕ) ∉ u)
    (hb : (b : ℕ) ∉ u) (v : Fin r → Fin M)
    (hv : P (u ++ [(a : ℕ)] ++ List.ofFn (fun i => (v i : ℕ)))) :
    P (u ++ [(b : ℕ)] ++ List.ofFn (fun i => (Equiv.swap a b (v i) : ℕ))) := by
  set τ : ℕ → ℕ := fun x => if x = a then b else if x = b then a else x with hτ
  have hinj : Function.Injective τ := by
    intro x y h
    simp only [hτ] at h
    split_ifs at h <;> omega
  have hu : u.map τ = u := by
    conv_rhs => rw [← List.map_id u]
    apply List.map_congr_left
    intro x hx
    have h1 : x ≠ a := fun h => ha (h ▸ hx)
    have h2 : x ≠ b := fun h => hb (h ▸ hx)
    simp [hτ, h1, h2]
  have hw : (List.ofFn (fun i => (v i : ℕ))).map τ =
      List.ofFn (fun i => (Equiv.swap a b (v i) : ℕ)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    simp only [Function.comp, hτ, Equiv.swap_apply_def]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 <;> simp_all [Fin.ext_iff]
  have he : (u ++ [(a : ℕ)] ++ List.ofFn (fun i => (v i : ℕ))).map τ =
      u ++ [(b : ℕ)] ++ List.ofFn (fun i => (Equiv.swap a b (v i) : ℕ)) := by
    rw [List.map_append, List.map_append, hu, hw]
    simp [hτ]
  rw [← he]
  exact (hP τ hinj _).2 hv

lemma ext_swap (hP : EqInv P) (M : ℕ) (u : List ℕ) (r : ℕ) (a b : Fin M) (ha : (a : ℕ) ∉ u)
    (hb : (b : ℕ) ∉ u) : Ext P M (u ++ [(a : ℕ)]) r = Ext P M (u ++ [(b : ℕ)]) r := by
  unfold Ext
  refine Finset.card_bij' (fun v _ => fun i => Equiv.swap a b (v i))
    (fun w _ => fun i => Equiv.swap a b (w i)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact swap_good P hP M u r a b ha hb v hv
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    have := swap_good P hP M u r b a hb ha w hw
    simpa [Equiv.swap_comm] using this
  · intro v _
    funext i
    simp
  · intro w _
    funext i
    simp

/-- When the letters of u are below k, the extensions by a new letter are all alike. -/
lemma ext_succ_new (hP : EqInv P) (M : ℕ) (u : List ℕ) (k r : ℕ) (hk : k ≤ M)
    (hu : ∀ x ∈ u, x < k) :
    Ext P M u (r + 1) = ∑ j ∈ range k, Ext P M (u ++ [j]) r + (M - k) * Ext P M (u ++ [k]) r := by
  rw [ext_succ, Fin.sum_univ_eq_sum_range (fun c => Ext P M (u ++ [c]) r) M,
    ← Finset.sum_range_add_sum_Ico _ hk]
  congr 1
  rw [show M - k = (Ico k M).card by simp, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mem_Ico] at hc
  have h1 : (c : ℕ) ∉ u := fun h => by have := hu c h; omega
  have h2 : (k : ℕ) ∉ u := fun h => by have := hu k h; omega
  exact ext_swap P hP M u r ⟨c, hc.2⟩ ⟨k, by omega⟩ h1 h2

/-- The completions of ρ by r letters, each an old letter j < k or the next new letter k, that
satisfy P and use K letters in all. -/
def S (K : ℕ) : ℕ → List ℕ → ℕ → ℕ
  | k, ρ, 0 => if P ρ ∧ k = K then 1 else 0
  | k, ρ, r + 1 => ∑ j ∈ range k, S K k (ρ ++ [j]) r + S K (k + 1) (ρ ++ [k]) r

lemma S_lt (K : ℕ) : ∀ (r k : ℕ) (ρ : List ℕ), K < k → S P K k ρ r = 0
  | 0, k, ρ, h => by simp [S]; omega
  | r + 1, k, ρ, h => by
    rw [S, S_lt K r (k + 1) _ (by omega)]
    simp only [add_zero]
    exact Finset.sum_eq_zero (fun j _ => S_lt K r k _ h)

lemma ext_eq (hP : EqInv P) (M N : ℕ) : ∀ (r k : ℕ) (ρ : List ℕ), k ≤ M → (∀ x ∈ ρ, x < k) →
    k + r < N → Ext P M ρ r = ∑ K ∈ range N, S P K k ρ r * (M - k).descFactorial (K - k)
  | 0, k, ρ, _, _, hN => by
    rw [ext_zero, Finset.sum_eq_single k]
    · by_cases h : P ρ <;> simp [S, h]
    · intro K _ hK
      simp [S, Ne.symm hK]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  | r + 1, k, ρ, hk, hρ, hN => by
    rw [ext_succ_new P hP M ρ k r hk hρ]
    have hold : ∀ j ∈ range k, Ext P M (ρ ++ [j]) r =
        ∑ K ∈ range N, S P K k (ρ ++ [j]) r * (M - k).descFactorial (K - k) := by
      intro j hj
      rw [Finset.mem_range] at hj
      refine ext_eq hP M N r k _ hk (fun x hx => ?_) (by omega)
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hρ x hx
      · omega
    have hnew : (M - k) * Ext P M (ρ ++ [k]) r =
        ∑ K ∈ range N, S P K (k + 1) (ρ ++ [k]) r * (M - k).descFactorial (K - k) := by
      rcases Nat.eq_or_lt_of_le hk with hMk | hMk
      · rw [show M - k = 0 by omega, zero_mul]
        symm
        apply Finset.sum_eq_zero
        intro K _
        rcases Nat.lt_or_ge k K with hK | hK
        · rw [show K - k = (K - k - 1) + 1 by omega, Nat.zero_descFactorial_succ, mul_zero]
        · rw [S_lt P K r (k + 1) _ (by omega), zero_mul]
      · rw [ext_eq hP M N r (k + 1) _ hMk (fun x hx => ?_) (by omega), Finset.mul_sum]
        · apply Finset.sum_congr rfl
          intro K _
          rcases Nat.lt_or_ge k K with hK | hK
          · rw [show K - k = (K - (k + 1)) + 1 by omega, show M - k = (M - (k + 1)) + 1 by omega,
              Nat.succ_descFactorial_succ]
            ring
          · rw [S_lt P K r (k + 1) _ (by omega)]
            simp
        · rw [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | hx
          · exact Nat.lt_succ_of_lt (hρ x hx)
          · omega
    rw [Finset.sum_congr rfl hold, hnew, Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro K _
    rw [S, add_mul, Finset.sum_mul]

/-- The count of the words of length L over 0..M-1 with P, by equality patterns. -/
lemma card_eq_sum (hP : EqInv P) (M L : ℕ) :
    (univ.filter (fun v : Fin L → Fin M => P (List.ofFn (fun i => (v i : ℕ))))).card =
      ∑ K ∈ range (L + 1), S P K 0 [] L * M.descFactorial K := by
  have h := ext_eq P hP M (L + 1) L 0 [] (Nat.zero_le M) (by simp) (by omega)
  simp only [Nat.sub_zero] at h
  rw [← h]
  rfl

end Patterns

/-! ## Squarefree words -/

lemma sq_map {α β : Type*} (f : α → β) (hf : Function.Injective f) (l : List α) :
    SquarefreeWord (l.map f) ↔ SquarefreeWord l := by
  constructor
  · intro H u hu
    have h1 : (u ++ u).map f <:+: l.map f := hu.map f
    rw [List.map_append] at h1
    exact List.map_eq_nil_iff.1 (H _ h1)
  · intro H v hv
    obtain ⟨s, t, hst⟩ := hv
    obtain ⟨A, B, hl, hA, hB⟩ := List.map_eq_append_iff.1 hst.symm
    obtain ⟨A1, A2, hA12, hA1, hA2⟩ := List.map_eq_append_iff.1 hA
    obtain ⟨C1, C2, hC, hC1, hC2⟩ := List.map_eq_append_iff.1 hA2
    have h12 : C1 = C2 := (List.map_injective_iff.2 hf) (hC1.trans hC2.symm)
    have hin : C1 ++ C1 <:+: l := ⟨A1, B, by rw [hl, hA12, hC, h12]⟩
    rw [← hC1, H C1 hin, List.map_nil]

/-- The check that the kernel runs: no factor at position i of length m repeats at i + m. -/
def sfB (l : List ℕ) : Bool :=
  (List.range (l.length + 1)).all fun i => (List.range (l.length + 1)).all fun m =>
    !(decide (0 < m ∧ i + 2 * m ≤ l.length ∧ (l.drop i).take m = (l.drop (i + m)).take m))

lemma sfB_iff (l : List ℕ) : sfB l = true ↔ SquarefreeWord l := by
  unfold sfB
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro H u hu
    obtain ⟨s, t, hst⟩ := hu
    by_contra hne
    have hlen : l.length = s.length + 2 * u.length + t.length := by
      rw [← hst]
      simp only [List.length_append]
      ring
    have hpos : 0 < u.length := List.length_pos_iff.2 hne
    apply H s.length (by omega) u.length (by omega)
    refine ⟨hpos, by omega, ?_⟩
    rw [← hst]
    have e1 : List.drop s.length (s ++ (u ++ u) ++ t) = u ++ (u ++ t) := by
      rw [List.append_assoc, List.drop_left, List.append_assoc]
    have e2 : List.drop (s.length + u.length) (s ++ (u ++ u) ++ t) = u ++ t := by
      rw [← List.drop_drop, e1, List.drop_left]
    rw [e1, e2, List.take_left, List.take_left]
  · intro H i _ m _ hc
    obtain ⟨hm, hle, heq⟩ := hc
    set u := (l.drop i).take m with hu
    have hlen : u.length = m := by
      rw [hu, List.length_take, List.length_drop]
      omega
    have hinf : u ++ u <:+: l := by
      refine ⟨l.take i, (l.drop i).drop (m + m), ?_⟩
      have h1 : (l.drop i).take (m + m) = u ++ u := by
        rw [List.take_add, List.drop_drop, ← heq]
      rw [List.append_assoc, ← h1, List.take_append_drop, List.take_append_drop]
    have := H u hinf
    rw [this] at hlen
    simp at hlen
    omega

instance : DecidablePred (fun l : List ℕ => SquarefreeWord l) := fun l =>
  decidable_of_iff (sfB l = true) (sfB_iff l)

lemma sq_eqInv : EqInv (fun l : List ℕ => SquarefreeWord l) := fun f hf l => sq_map f hf l

/-- Squarefree words of length L over Fin M, counted by squarefree equality patterns. -/
lemma card_sq (M L : ℕ) :
    Nat.card {w : Fin L → Fin M // SquarefreeWord (List.ofFn w)} =
      ∑ K ∈ range (L + 1), S (fun l : List ℕ => SquarefreeWord l) K 0 [] L * M.descFactorial K := by
  classical
  rw [← card_eq_sum _ sq_eqInv M L]
  have e : ∀ v : Fin L → Fin M, SquarefreeWord (List.ofFn v) ↔
      SquarefreeWord (List.ofFn (fun i => (v i : ℕ))) := by
    intro v
    rw [show List.ofFn (fun i => (v i : ℕ)) = (List.ofFn v).map Fin.val by
      rw [List.map_ofFn]; rfl]
    exact (sq_map Fin.val Fin.val_injective _).symm
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  · congr 1
    exact Finset.filter_congr (fun v _ => e v)

/-- The cast of a falling factorial. -/
lemma desc_cast (m : ℕ) : ∀ K, ((m.descFactorial K : ℕ) : ℚ) = ∏ i ∈ range K, ((m : ℚ) - i)
  | 0 => by simp
  | K + 1 => by
    rw [Finset.prod_range_succ, ← desc_cast m K, Nat.descFactorial_succ]
    rcases Nat.lt_or_ge m K with h | h
    · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]
      simp
    · push_cast [Nat.cast_sub h]
      ring

lemma s0 : S (fun l : List ℕ => SquarefreeWord l) 0 0 [] 6 = 0 := by
  decide +kernel

lemma s1 : S (fun l : List ℕ => SquarefreeWord l) 1 0 [] 6 = 0 := by
  decide +kernel

lemma s2 : S (fun l : List ℕ => SquarefreeWord l) 2 0 [] 6 = 0 := by
  decide +kernel

lemma s3 : S (fun l : List ℕ => SquarefreeWord l) 3 0 [] 6 = 7 := by
  decide +kernel

lemma s4 : S (fun l : List ℕ => SquarefreeWord l) 4 0 [] 6 = 22 := by
  decide +kernel

lemma s5 : S (fun l : List ℕ => SquarefreeWord l) 5 0 [] 6 = 10 := by
  decide +kernel

lemma s6 : S (fun l : List ℕ => SquarefreeWord l) 6 0 [] 6 = 1 := by
  decide +kernel

/-- a(n) as a sum of falling factorials over the squarefree patterns. -/
theorem a_expand (n : ℕ) : a n = 7 * (n + 1).descFactorial 3 + 22 * (n + 1).descFactorial 4 + 10 * (n + 1).descFactorial 5 + 1 * (n + 1).descFactorial 6 := by
  unfold a
  rw [card_sq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [s0, s1, s2, s3, s4, s5, s6]
  ring

/-- Hardin's empirical formula, for every n. -/
theorem poly (n : ℕ) : (a n : ℚ) = (n : ℚ) ^ 6 + (n : ℚ) ^ 5 - 3 * (n : ℚ) ^ 4 - 2 * (n : ℚ) ^ 3 + 2 * (n : ℚ) ^ 2 + (n : ℚ) := by
  rw [a_expand]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, desc_cast]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  push_cast
  ring

/-- The values a(0..T), from the explicit sum. -/
theorem small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 42 ∧ a 3 = 696 ∧ a 4 = 4260 ∧ a 5 = 16680 ∧ a 6 = 50190 ∧ a 7 = 126672 ∧ a 8 = 281736 ∧ a 9 = 569520 ∧ a 10 = 1068210 ∧ a 11 = 1886280 ∧ a 12 = 3169452 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [a_expand]; decide +kernel)

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = 7 + p := ⟨n - 7, by omega⟩
  rw [show 7 + p - 1 = 6 + p by omega, show 7 + p - 2 = 5 + p by omega, show 7 + p - 3 = 4 + p by omega, show 7 + p - 4 = 3 + p by omega, show 7 + p - 5 = 2 + p by omega, show 7 + p - 6 = 1 + p by omega, show 7 + p - 7 = 0 + p by omega]
  have hq : (a (7 + p) : ℚ) = 7 * (a (6 + p) : ℚ) - 21 * (a (5 + p) : ℚ) + 35 * (a (4 + p) : ℚ) - 35 * (a (3 + p) : ℚ) + 21 * (a (2 + p) : ℚ) - 7 * (a (1 + p) : ℚ) + (a (0 + p) : ℚ) := by
    rw [poly (7 + p), poly (6 + p), poly (5 + p), poly (4 + p), poly (3 + p), poly (2 + p), poly (1 + p), poly (0 + p)]
    push_cast
    ring
  exact_mod_cast hq

open PowerSeries in
/-- Barker's g.f., with a(0) = 0. -/
theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 7 = 6 * X ^ 2 * (7 + 67 * X + 45 * X ^ 2 + X ^ 3) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  set A : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hA
  have hD : A * (1 - X) ^ 7 = A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) + C 35 * (A * X ^ 4) - C 21 * (A * X ^ 5) + C 7 * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have hN : (6 * X ^ 2 * (7 + 67 * X + 45 * X ^ 2 + X ^ 3) : PowerSeries ℤ) =
      C 42 * X ^ 2 + C 402 * X ^ 3 + C 270 * X ^ 4 + C 6 * X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, map_neg, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  rcases Nat.lt_or_ge n 13 with h | h
  · interval_cases n <;>
      simp only [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, coeff_C, pow_zero, Nat.zero_le, Nat.sub_zero, Nat.sub_self, if_true, if_false] <;> norm_num
  · have hq := recurrence n (by omega)
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega, show 6 ≤ n by omega, show 7 ≤ n by omega, show n ≠ 2 by omega, show n - 2 ≠ 0 by omega, show n ≠ 3 by omega, show n - 3 ≠ 0 by omega, show n ≠ 4 by omega, show n - 4 ≠ 0 by omega, show n ≠ 5 by omega, show n - 5 ≠ 0 by omega, coeff_C, if_true, if_false, ite_self]
    linear_combination hq

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 0 ∧ a 2 = 42 ∧ a 3 = 696 ∧ a 4 = 4260 ∧ a 5 = 16680 ∧ a 6 = 50190 ∧ a 7 = 126672 ∧ a 8 = 281736 ∧ a 9 = 569520 ∧ a 10 = 1068210 ∧ a 11 = 1886280 ∧ a 12 = 3169452 := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩ := small
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12⟩

/-- The problem as the site states it. -/
theorem conjecture :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - PowerSeries.X) ^ 7 = 6 * PowerSeries.X ^ 2 * (7 + 67 * PowerSeries.X + 45 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a214945

theorem OMA.solution : type_of% @OMA.S_oeis_a214945.main :=
  OMA.S_oeis_a214945.conjecture
