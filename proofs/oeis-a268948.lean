import OMAStatements.S_oeis_a268948

/-!
OEIS A268948 (R. H. Hardin, Feb 16 2016): Number of length-7 0..n arrays with no repeated value unequal to the previous repeated value plus one mod n+1.
Conjectures from Colin Barker, Jan 17 2019: G.f.: 3*x*(10 + 243*x + 924*x^2 + 675*x^3 - 110*x^4 - 55*x^5 - 8*x^6 + x^7) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8.

Proof. The repeated values are the values of the adjacent equal pairs, in order (`reps`), and the
condition is that consecutive repeated values p, c satisfy c = p + 1 in Fin (n + 1). Reading the
array from the left with state (last value v, last repeated value r), G(m, v, r) counts the valid
continuations by m entries and G(m + 1, v, r) = [R r v] G(m, v, v) + sum over a != v of G(m, a, r)
(`Vd_cons`, `G_succ`). The relation only depends on the class of c - p (0, 1, -1 or other), and
every class but the last has one member, so for n >= 2 G(m, v, r) = g_m(class of v - r) and
G(m, v, none) = h_m (`compress`) with polynomial recursions in n, and a(n) = (n + 1) h_6(n)
(`a_poly`); a(1) is computed directly. The g.f. and the recurrence follow by comparing
coefficients.
-/

namespace OMA.S_oeis_a268948

open PowerSeries Finset


/-- The relation between consecutive repeated values. -/
def R {n : ℕ} (p c : Fin (n + 1)) : Prop := c = p + 1

instance {n : ℕ} : DecidableRel (@R n) := fun p c => by unfold R; infer_instance

lemma reps_cons {m N : ℕ} (v : Fin N) (t : Fin (m + 1) → Fin N) :
    reps (Fin.cons v t : Fin (m + 2) → Fin N) = (if v = t 0 then [v] else []) ++ reps t := by
  unfold reps
  rw [List.finRange_succ, List.filterMap_cons, List.filterMap_map]
  have hf : ((fun i : Fin (m + 1) => if (Fin.cons v t : Fin (m + 2) → Fin N) i.castSucc =
      (Fin.cons v t : Fin (m + 2) → Fin N) i.succ then some ((Fin.cons v t : Fin (m + 2) → Fin N)
        i.castSucc) else none) ∘ Fin.succ) =
      fun i : Fin m => if t i.castSucc = t i.succ then some (t i.castSucc) else none := by
    funext i
    simp only [Function.comp_apply, ← Fin.succ_castSucc, Fin.cons_succ]
  rw [hf]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one]
  by_cases h : v = t 0 <;> simp [h]

/-- The arrays continuing from last value v with last repeated value r (none: no repeat yet). -/
def Vd {m n : ℕ} (r : Option (Fin (n + 1))) (v : Fin (n + 1)) (t : Fin m → Fin (n + 1)) : Prop :=
  (r.toList ++ reps (Fin.cons v t : Fin (m + 1) → Fin (n + 1))).IsChain R

instance {m n : ℕ} (r : Option (Fin (n + 1))) (v : Fin (n + 1)) :
    DecidablePred (@Vd m n r v) := fun t => by unfold Vd; infer_instance

lemma chain_opt {n : ℕ} (r : Option (Fin (n + 1))) (v : Fin (n + 1)) (l : List (Fin (n + 1))) :
    (r.toList ++ v :: l).IsChain R ↔ (∀ p ∈ r, R p v) ∧ (v :: l).IsChain R := by
  rcases r with _ | p
  · simp
  · simp [List.isChain_cons_cons]

lemma Vd_zero {n : ℕ} (r : Option (Fin (n + 1))) (v : Fin (n + 1)) (t : Fin 0 → Fin (n + 1)) :
    Vd r v t := by
  rcases r with _ | p <;> simp [Vd, reps]

lemma Vd_cons {m n : ℕ} (r : Option (Fin (n + 1))) (v a : Fin (n + 1)) (s : Fin m → Fin (n + 1)) :
    Vd r v (Fin.cons a s : Fin (m + 1) → Fin (n + 1)) ↔
      if v = a then (∀ p ∈ r, R p v) ∧ Vd (some v) a s else Vd r a s := by
  unfold Vd
  rw [reps_cons, Fin.cons_zero]
  split_ifs with h
  · subst h
    rw [List.singleton_append, chain_opt]
    simp
  · rw [List.nil_append]

/-- G m v r: the valid continuations by m entries. -/
def G {n : ℕ} (m : ℕ) (v : Fin (n + 1)) (r : Option (Fin (n + 1))) : ℕ :=
  ((univ : Finset (Fin m → Fin (n + 1))).filter (Vd r v)).card

lemma G_zero {n : ℕ} (v : Fin (n + 1)) (r : Option (Fin (n + 1))) : G 0 v r = 1 := by
  unfold G
  rw [card_eq_one]
  refine ⟨Fin.elim0, ?_⟩
  ext t
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro _
    funext i
    exact i.elim0
  · intro _
    exact Vd_zero r v t

lemma split_sum {q : ℕ} (v : Fin q) (P : ℕ) (Q : Fin q → ℕ) :
    ∑ b : Fin q, (if b = v then P else Q b) = P + ∑ b : Fin q, (if b = v then 0 else Q b) := by
  rw [← Finset.add_sum_erase univ _ (mem_univ v),
    ← Finset.add_sum_erase univ (fun b => if b = v then 0 else Q b) (mem_univ v)]
  simp only [if_true, zero_add]
  congr 1
  refine sum_congr rfl (fun b hb => ?_)
  rw [if_neg (ne_of_mem_erase hb), if_neg (ne_of_mem_erase hb)]

lemma G_succ {n : ℕ} (m : ℕ) (v : Fin (n + 1)) (r : Option (Fin (n + 1))) :
    G (m + 1) v r = (if ∀ p ∈ r, R p v then G m v (some v) else 0) +
      ∑ a : Fin (n + 1), if a = v then 0 else G m a r := by
  rw [← split_sum]
  unfold G
  rw [card_eq_sum_card_fiberwise (f := fun t => t 0) (t := univ) (by simp)]
  refine sum_congr rfl (fun a _ => ?_)
  rw [filter_filter]
  by_cases ha : a = v
  · subst ha
    rw [if_pos rfl]
    split_ifs with hr
    · refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons a s) ?_ ?_ ?_ ?_
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht ⊢
        obtain ⟨hV, h0⟩ := ht
        have e : t = Fin.cons a (Fin.tail t) := by
          rw [← h0]
          exact (Fin.cons_self_tail t).symm
        rw [e, Vd_cons, if_pos rfl] at hV
        exact hV.2
      · intro s hs
        simp only [mem_filter, mem_univ, true_and] at hs ⊢
        refine ⟨?_, rfl⟩
        rw [Vd_cons, if_pos rfl]
        exact ⟨hr, hs⟩
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht
        rw [← ht.2]
        exact Fin.cons_self_tail t
      · intro s _
        simp
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro t - ⟨hV, h0⟩
      have e : t = Fin.cons a (Fin.tail t) := by
        rw [← h0]
        exact (Fin.cons_self_tail t).symm
      rw [e, Vd_cons, if_pos rfl] at hV
      exact hr hV.1
  · rw [if_neg ha]
    refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons a s) ?_ ?_ ?_ ?_
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht ⊢
      obtain ⟨hV, h0⟩ := ht
      have e : t = Fin.cons a (Fin.tail t) := by
        rw [← h0]
        exact (Fin.cons_self_tail t).symm
      rw [e, Vd_cons, if_neg (Ne.symm ha)] at hV
      exact hV
    · intro s hs
      simp only [mem_filter, mem_univ, true_and] at hs ⊢
      refine ⟨?_, rfl⟩
      rw [Vd_cons, if_neg (Ne.symm ha)]
      exact hs
    · intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      rw [← ht.2]
      exact Fin.cons_self_tail t
    · intro s _
      simp

lemma a_eq (n : ℕ) : a n = ∑ v : Fin (n + 1), G 6 v none := by
  unfold a G
  rw [card_eq_sum_card_fiberwise (f := fun t => t 0) (t := univ) (by simp)]
  refine sum_congr rfl (fun v _ => ?_)
  rw [filter_filter]
  refine card_bij' (fun t _ => Fin.tail t) (fun s _ => Fin.cons v s) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    obtain ⟨hg, h0⟩ := ht
    have e : t = Fin.cons v (Fin.tail t) := by
      rw [← h0]
      exact (Fin.cons_self_tail t).symm
    rw [e] at hg
    exact hg
  · intro s hs
    simp only [mem_filter, mem_univ, true_and] at hs ⊢
    exact ⟨hs, rfl⟩
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht
    rw [← ht.2]
    exact Fin.cons_self_tail t
  · intro s _
    simp

/-- The class of a difference: 0, 1, -1 or other. -/
def κ {n : ℕ} (δ : Fin (n + 1)) : Fin 4 := if δ = 0 then 0 else if δ = 1 then 1 else if δ = -1 then 2 else 3

/-- Which classes of c - p satisfy the relation. -/
def ok : Fin 4 → Bool := ![false, true, false, false]

/-- For n >= 2 the classes 0, 1 and -1 of Fin (n + 1) are distinct. -/
lemma distinct3 {n : ℕ} (hn : 2 ≤ n) :
    (0 : Fin (n + 1)) ≠ 1 ∧ (1 : Fin (n + 1)) ≠ -1 ∧ (0 : Fin (n + 1)) ≠ -1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg Fin.val h
    rw [Fin.val_zero, Fin.val_one'] at this
    rw [Nat.one_mod_eq_one.mpr (by omega)] at this
    omega
  · have := congrArg Fin.val h
    rw [Fin.val_one', Fin.coe_neg_one, Nat.one_mod_eq_one.mpr (by omega)] at this
    omega
  · have := congrArg Fin.val h
    rw [Fin.val_zero, Fin.coe_neg_one] at this
    omega

lemma R_iff {n : ℕ} (hn : 2 ≤ n) (p c : Fin (n + 1)) : R p c ↔ ok (κ (c - p)) = true := by
  obtain ⟨h01, h1m, h0m⟩ := distinct3 hn
  have hc1 : c = p + 1 ↔ c - p = 1 := (sub_eq_iff_eq_add').symm
  have hcm : p = c + 1 ↔ c - p = -1 := by
    rw [sub_eq_iff_eq_add', ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact eq_comm
  unfold R κ ok
  rw [hc1]
  generalize c - p = δ
  by_cases e0 : δ = 0
  · subst e0
    simp [h01, h0m]
  · by_cases e1 : δ = 1
    · subst e1
      simp [h1m, Ne.symm h01]
    · by_cases em : δ = -1
      · subst em
        simp [Ne.symm h0m, Ne.symm h1m]
      · simp [e0, e1, em]

lemma card_cls {n : ℕ} (hn : 2 ≤ n) (F : Fin 4 → ℤ) (r : Fin (n + 1)) :
    ∑ a : Fin (n + 1), F (κ (a - r)) = F 0 + F 1 + F 2 + ((n : ℤ) - 2) * F 3 := by
  obtain ⟨h01, h1m, h0m⟩ := distinct3 hn
  rw [show ∑ a : Fin (n + 1), F (κ (a - r)) = ∑ d : Fin (n + 1), F (κ d) from
    Fintype.sum_equiv (Equiv.subRight r) _ _ (fun _ => rfl)]
  set S : Finset (Fin (n + 1)) := {0, 1, -1} with hS
  rw [← Finset.sum_add_sum_compl S]
  have hS3 : ∀ d ∈ Sᶜ, F (κ d) = F 3 := by
    intro d hd
    simp only [hS, mem_compl, mem_insert, mem_singleton, not_or] at hd
    simp [κ, hd.1, hd.2.1, hd.2.2]
  rw [sum_congr rfl hS3, sum_const, card_compl, hS]
  rw [card_insert_of_notMem (by simp [h01, h0m]), card_insert_of_notMem (by simp [h1m]),
    card_singleton]
  rw [sum_insert (by simp [h01, h0m]), sum_insert (by simp [h1m]), sum_singleton]
  simp only [κ, if_pos rfl, if_neg (Ne.symm h01), if_neg (Ne.symm h0m), if_neg (Ne.symm h1m),
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- The class recursion (n is a parameter). -/
def g (n : ℕ) : ℕ → Fin 4 → ℤ
  | 0, _ => 1
  | m + 1, c => (if ok c then g n m 0 else 0) +
      (g n m 0 + g n m 1 + g n m 2 + ((n : ℤ) - 2) * g n m 3) - g n m c

/-- The count before the first repeat. -/
def h (n : ℕ) : ℕ → ℤ
  | 0 => 1
  | m + 1 => g n m 0 + (n : ℤ) * h n m

lemma compress {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    (∀ v r : Fin (n + 1), (G m v (some r) : ℤ) = g n m (κ (v - r))) ∧
      ∀ v : Fin (n + 1), (G m v none : ℤ) = h n m := by
  induction m with
  | zero => exact ⟨fun v r => by simp [G_zero, g], fun v => by simp [G_zero, h]⟩
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hsum : ∀ (r : Option (Fin (n + 1))) (v : Fin (n + 1)),
        (∑ a : Fin (n + 1), if a = v then (0 : ℤ) else (G m a r : ℤ)) =
          (∑ a : Fin (n + 1), (G m a r : ℤ)) - G m v r := by
      intro r v
      rw [← Finset.add_sum_erase univ _ (mem_univ v),
        ← Finset.add_sum_erase univ (fun a => (G m a r : ℤ)) (mem_univ v)]
      rw [if_pos rfl, zero_add, add_sub_cancel_left]
      refine sum_congr rfl (fun b hb => ?_)
      rw [if_neg (ne_of_mem_erase hb)]
    refine ⟨fun v r => ?_, fun v => ?_⟩
    · rw [G_succ]
      push_cast
      rw [hsum]
      simp only [Option.mem_def, Option.some.injEq, forall_eq', R_iff hn]
      rw [show (∑ a : Fin (n + 1), (G m a (some r) : ℤ)) = ∑ a : Fin (n + 1), g n m (κ (a - r)) from
        sum_congr rfl (fun a _ => ih1 a r), card_cls hn, ih1 v r, ih1 v v, sub_self]
      simp only [g]
      have hk0 : κ (0 : Fin (n + 1)) = 0 := by simp [κ]
      rw [hk0]
      split_ifs <;> ring
    · rw [G_succ]
      push_cast
      rw [hsum]
      simp only [Option.mem_def, reduceCtorEq, false_imp_iff, imp_true_iff, if_true]
      rw [show (∑ a : Fin (n + 1), (G m a none : ℤ)) = ∑ a : Fin (n + 1), h n m from
        sum_congr rfl (fun a _ => ih2 a), ih2 v, ih1 v v, sub_self]
      have hk0 : κ (0 : Fin (n + 1)) = 0 := by simp [κ]
      rw [hk0]
      simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

lemma g0_0 (n : ℕ) : g n 0 0 = 1 := rfl
lemma g0_1 (n : ℕ) : g n 0 1 = 1 := rfl
lemma g0_2 (n : ℕ) : g n 0 2 = 1 := rfl
lemma g0_3 (n : ℕ) : g n 0 3 = 1 := rfl
lemma g1_0 (n : ℕ) : g n 1 0 = (n : ℤ) := by
  rw [g, if_neg (show ¬ (ok 0 = true) by decide), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g1_1 (n : ℕ) : g n 1 1 = 1 + (n : ℤ) := by
  rw [g, if_pos (show ok 1 = true from rfl), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g1_2 (n : ℕ) : g n 1 2 = (n : ℤ) := by
  rw [g, if_neg (show ¬ (ok 2 = true) by decide), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g1_3 (n : ℕ) : g n 1 3 = (n : ℤ) := by
  rw [g, if_neg (show ¬ (ok 3 = true) by decide), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g2_0 (n : ℕ) : g n 2 0 = 1 + (n : ℤ) ^ 2 := by
  rw [g, if_neg (show ¬ (ok 0 = true) by decide), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g2_1 (n : ℕ) : g n 2 1 = (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [g, if_pos (show ok 1 = true from rfl), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g2_2 (n : ℕ) : g n 2 2 = 1 + (n : ℤ) ^ 2 := by
  rw [g, if_neg (show ¬ (ok 2 = true) by decide), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g2_3 (n : ℕ) : g n 2 3 = 1 + (n : ℤ) ^ 2 := by
  rw [g, if_neg (show ¬ (ok 3 = true) by decide), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g3_0 (n : ℕ) : g n 3 0 = -1 + 2 * (n : ℤ) + (n : ℤ) ^ 3 := by
  rw [g, if_neg (show ¬ (ok 0 = true) by decide), g2_0, g2_1, g2_2, g2_3]
  ring
lemma g3_1 (n : ℕ) : g n 3 1 = 1 + (n : ℤ) + (n : ℤ) ^ 2 + (n : ℤ) ^ 3 := by
  rw [g, if_pos (show ok 1 = true from rfl), g2_0, g2_1, g2_2, g2_3]
  ring
lemma g3_2 (n : ℕ) : g n 3 2 = -1 + 2 * (n : ℤ) + (n : ℤ) ^ 3 := by
  rw [g, if_neg (show ¬ (ok 2 = true) by decide), g2_0, g2_1, g2_2, g2_3]
  ring
lemma g3_3 (n : ℕ) : g n 3 3 = -1 + 2 * (n : ℤ) + (n : ℤ) ^ 3 := by
  rw [g, if_neg (show ¬ (ok 3 = true) by decide), g2_0, g2_1, g2_2, g2_3]
  ring
lemma g4_0 (n : ℕ) : g n 4 0 = 2 - 2 * (n : ℤ) + 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 4 := by
  rw [g, if_neg (show ¬ (ok 0 = true) by decide), g3_0, g3_1, g3_2, g3_3]
  ring
lemma g4_1 (n : ℕ) : g n 4 1 = -1 + (n : ℤ) + 2 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3 + (n : ℤ) ^ 4 := by
  rw [g, if_pos (show ok 1 = true from rfl), g3_0, g3_1, g3_2, g3_3]
  ring
lemma g4_2 (n : ℕ) : g n 4 2 = 2 - 2 * (n : ℤ) + 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 4 := by
  rw [g, if_neg (show ¬ (ok 2 = true) by decide), g3_0, g3_1, g3_2, g3_3]
  ring
lemma g4_3 (n : ℕ) : g n 4 3 = 2 - 2 * (n : ℤ) + 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 4 := by
  rw [g, if_neg (show ¬ (ok 3 = true) by decide), g3_0, g3_1, g3_2, g3_3]
  ring
lemma g5_0 (n : ℕ) : g n 5 0 = -3 + 5 * (n : ℤ) - 3 * (n : ℤ) ^ 2 + 4 * (n : ℤ) ^ 3 + (n : ℤ) ^ 5 := by
  rw [g, if_neg (show ¬ (ok 0 = true) by decide), g4_0, g4_1, g4_2, g4_3]
  ring
lemma g5_1 (n : ℕ) : g n 5 1 = 2 + (n : ℤ) ^ 2 + 3 * (n : ℤ) ^ 3 + (n : ℤ) ^ 4 + (n : ℤ) ^ 5 := by
  rw [g, if_pos (show ok 1 = true from rfl), g4_0, g4_1, g4_2, g4_3]
  ring
lemma g5_2 (n : ℕ) : g n 5 2 = -3 + 5 * (n : ℤ) - 3 * (n : ℤ) ^ 2 + 4 * (n : ℤ) ^ 3 + (n : ℤ) ^ 5 := by
  rw [g, if_neg (show ¬ (ok 2 = true) by decide), g4_0, g4_1, g4_2, g4_3]
  ring
lemma g5_3 (n : ℕ) : g n 5 3 = -3 + 5 * (n : ℤ) - 3 * (n : ℤ) ^ 2 + 4 * (n : ℤ) ^ 3 + (n : ℤ) ^ 5 := by
  rw [g, if_neg (show ¬ (ok 3 = true) by decide), g4_0, g4_1, g4_2, g4_3]
  ring
lemma g6_0 (n : ℕ) : g n 6 0 = 5 - 8 * (n : ℤ) + 9 * (n : ℤ) ^ 2 - 4 * (n : ℤ) ^ 3 + 5 * (n : ℤ) ^ 4 + (n : ℤ) ^ 6 := by
  rw [g, if_neg (show ¬ (ok 0 = true) by decide), g5_0, g5_1, g5_2, g5_3]
  ring
lemma g6_1 (n : ℕ) : g n 6 1 = -3 + 2 * (n : ℤ) + 2 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3 + 4 * (n : ℤ) ^ 4 + (n : ℤ) ^ 5 + (n : ℤ) ^ 6 := by
  rw [g, if_pos (show ok 1 = true from rfl), g5_0, g5_1, g5_2, g5_3]
  ring
lemma g6_2 (n : ℕ) : g n 6 2 = 5 - 8 * (n : ℤ) + 9 * (n : ℤ) ^ 2 - 4 * (n : ℤ) ^ 3 + 5 * (n : ℤ) ^ 4 + (n : ℤ) ^ 6 := by
  rw [g, if_neg (show ¬ (ok 2 = true) by decide), g5_0, g5_1, g5_2, g5_3]
  ring
lemma g6_3 (n : ℕ) : g n 6 3 = 5 - 8 * (n : ℤ) + 9 * (n : ℤ) ^ 2 - 4 * (n : ℤ) ^ 3 + 5 * (n : ℤ) ^ 4 + (n : ℤ) ^ 6 := by
  rw [g, if_neg (show ¬ (ok 3 = true) by decide), g5_0, g5_1, g5_2, g5_3]
  ring

lemma h0 (n : ℕ) : h n 0 = 1 := rfl
lemma h1 (n : ℕ) : h n 1 = 1 + (n : ℤ) := by
  rw [h, g0_0, h0]
  ring
lemma h2 (n : ℕ) : h n 2 = 2 * (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [h, g1_0, h1]
  ring
lemma h3 (n : ℕ) : h n 3 = 1 + 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3 := by
  rw [h, g2_0, h2]
  ring
lemma h4 (n : ℕ) : h n 4 = -1 + 3 * (n : ℤ) + 4 * (n : ℤ) ^ 3 + (n : ℤ) ^ 4 := by
  rw [h, g3_0, h3]
  ring
lemma h5 (n : ℕ) : h n 5 = 2 - 3 * (n : ℤ) + 6 * (n : ℤ) ^ 2 + 5 * (n : ℤ) ^ 4 + (n : ℤ) ^ 5 := by
  rw [h, g4_0, h4]
  ring
lemma h6 (n : ℕ) : h n 6 = -3 + 7 * (n : ℤ) - 6 * (n : ℤ) ^ 2 + 10 * (n : ℤ) ^ 3 + 6 * (n : ℤ) ^ 5 + (n : ℤ) ^ 6 := by
  rw [h, g5_0, h5]
  ring

lemma a_one : a 1 = 30 := by
  decide

/-- a(n) as a polynomial in n, for n >= 2. -/
lemma a_poly (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = -3 + 4 * (n : ℚ) + (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 5 + 7 * (n : ℚ) ^ 6 + (n : ℚ) ^ 7 := by
  have h1 : (a n : ℤ) = (n + 1) * h n 6 := by
    rw [a_eq]
    push_cast
    rw [sum_congr rfl (fun v _ => (compress hn 6).2 v), sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    ring
  rw [h6] at h1
  have h2 : (a n : ℤ) = -3 + 4 * (n : ℤ) + (n : ℤ) ^ 2 + 4 * (n : ℤ) ^ 3 + 10 * (n : ℤ) ^ 4 + 6 * (n : ℤ) ^ 5 + 7 * (n : ℤ) ^ 6 + (n : ℤ) ^ 7 := by rw [h1]; ring
  exact_mod_cast h2

/-- The polynomial also gives a(1). -/
lemma a_poly1 (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = -3 + 4 * (n : ℚ) + (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 4 + 6 * (n : ℚ) ^ 5 + 7 * (n : ℚ) ^ 6 + (n : ℚ) ^ 7 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    rw [show ((a 1 : ℕ) : ℚ) = 30 by exact_mod_cast a_one]
    norm_num
  · exact a_poly n h

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      3 * X * (10 + 243 * X + 924 * X ^ 2 + 675 * X ^ 3 - 110 * X ^ 4 - 55 * X ^ 5 - 8 * X ^ 6 + X ^ 7) := by
  have v1 : (a 1 : ℚ) = 30 := by exact_mod_cast a_one
  have v2 : (a 2 : ℚ) = 969 := by rw [a_poly 2 (by norm_num)]; norm_num
  have v3 : (a 3 : ℚ) = 9684 := by rw [a_poly 3 (by norm_num)]; norm_num
  have v4 : (a 4 : ℚ) = 54045 := by rw [a_poly 4 (by norm_num)]; norm_num
  have v5 : (a 5 : ℚ) = 213042 := by rw [a_poly 5 (by norm_num)]; norm_num
  have v6 : (a 6 : ℚ) = 667065 := by rw [a_poly 6 (by norm_num)]; norm_num
  have v7 : (a 7 : ℚ) = 1773384 := by rw [a_poly 7 (by norm_num)]; norm_num
  have v8 : (a 8 : ℚ) = 4171869 := by rw [a_poly 8 (by norm_num)]; norm_num
  have v9 : (a 9 : ℚ) = 8925990 := by rw [a_poly 9 (by norm_num)]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 8 = A - C (8 : ℚ) * (A * X ^ 1) + C (28 : ℚ) * (A * X ^ 2) - C (56 : ℚ) * (A * X ^ 3) + C (70 : ℚ) * (A * X ^ 4) - C (56 : ℚ) * (A * X ^ 5) + C (28 : ℚ) * (A * X ^ 6) - C (8 : ℚ) * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]
    ring
  have e2 : (3 * X * (10 + 243 * X + 924 * X ^ 2 + 675 * X ^ 3 - 110 * X ^ 4 - 55 * X ^ 5 - 8 * X ^ 6 + X ^ 7) : ℚ⟦X⟧) = X ^ 1 * C (30 : ℚ) + X ^ 2 * C (729 : ℚ) + X ^ 3 * C (2772 : ℚ) + X ^ 4 * C (2025 : ℚ) - X ^ 5 * C (330 : ℚ) - X ^ 6 * C (165 : ℚ) - X ^ 7 * C (24 : ℚ) + X ^ 8 * C (3 : ℚ) := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5, v6]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7, v8]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, v1, v2, v3, v4, v5, v6, v7, v8, v9]
    all_goals norm_num
  · simp only [show ¬ (m + 10 = 0) by omega,
      show 1 ≤ m + 10 by omega,
      show m + 10 - 1 = m + 9 by omega,
      show ¬ (m + 9 = 0) by omega,
      show 2 ≤ m + 10 by omega,
      show m + 10 - 2 = m + 8 by omega,
      show ¬ (m + 8 = 0) by omega,
      show 3 ≤ m + 10 by omega,
      show m + 10 - 3 = m + 7 by omega,
      show ¬ (m + 7 = 0) by omega,
      show 4 ≤ m + 10 by omega,
      show m + 10 - 4 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show 5 ≤ m + 10 by omega,
      show m + 10 - 5 = m + 5 by omega,
      show ¬ (m + 5 = 0) by omega,
      show 6 ≤ m + 10 by omega,
      show m + 10 - 6 = m + 4 by omega,
      show ¬ (m + 4 = 0) by omega,
      show 7 ≤ m + 10 by omega,
      show m + 10 - 7 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega,
      show 8 ≤ m + 10 by omega,
      show m + 10 - 8 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega,
      show ¬ (m + 10 = 1) by omega,
      show ¬ (m + 10 = 2) by omega,
      show ¬ (m + 10 = 3) by omega,
      show ¬ (m + 10 = 4) by omega,
      show ¬ (m + 10 = 5) by omega,
      show ¬ (m + 10 = 6) by omega,
      show ¬ (m + 10 = 7) by omega,
      show ¬ (m + 10 = 8) by omega, if_true, if_false]
    rw [a_poly (m + 10) (by omega), a_poly (m + 9) (by omega), a_poly (m + 8) (by omega), a_poly (m + 7) (by omega), a_poly (m + 6) (by omega), a_poly (m + 5) (by omega), a_poly (m + 4) (by omega), a_poly (m + 3) (by omega), a_poly (m + 2) (by omega)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega, show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega, show m + 9 - 7 = m + 2 by omega, show m + 9 - 8 = m + 1 by omega]
  have h : (a (m + 9) : ℚ) = 8 * a (m + 8) - 28 * a (m + 7) + 56 * a (m + 6) - 70 * a (m + 5) + 56 * a (m + 4) - 28 * a (m + 3) + 8 * a (m + 2) - a (m + 1) := by
    rw [a_poly1 (m + 9) (by omega), a_poly1 (m + 8) (by omega), a_poly1 (m + 7) (by omega), a_poly1 (m + 6) (by omega), a_poly1 (m + 5) (by omega), a_poly1 (m + 4) (by omega), a_poly1 (m + 3) (by omega), a_poly1 (m + 2) (by omega), a_poly1 (m + 1) (by omega)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      3 * X * (10 + 243 * X + 924 * X ^ 2 + 675 * X ^ 3 - 110 * X ^ 4 - 55 * X ^ 5 - 8 * X ^ 6 + X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a268948

theorem OMA.solution : type_of% @OMA.S_oeis_a268948.main :=
  OMA.S_oeis_a268948.conjecture
