import OMAStatements.S_oeis_a269777

/- The continuation recurrence and its four difference classes are adapted from
@jleguina's proof of A269778 (d519c3d4b). Here a tuple is counted by four
continuation steps, giving the degree-five counting polynomial. -/
namespace OMA.FiveLetter
open OMA.S_oeis_a269777 Finset
def reps {m N : ℕ} (x : Fin (m + 1) → Fin N) : List (Fin N) :=
  (List.finRange m).filterMap (fun i => if x i.castSucc = x i.succ then some (x i.castSucc) else none)

/-- Every repeated value is unequal to the previous repeated value plus one modulo n + 1: each repeated value c after the first, with p the previous one, has c != p + 1 in Fin (n + 1). -/
def good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Prop :=
  (reps x).IsChain (fun p c => c ≠ p + 1)

instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance


def words (n : ℕ) : ℕ := ((univ : Finset (Fin 5 → Fin (n + 1))).filter good).card

def decode (n : ℕ) : Word n ≃ (Fin 5 → Fin (n+1)) where
  toFun := fun ⟨a,b,c,d,e⟩ => ![a,b,c,d,e]
  invFun := fun x => (x 0,x 1,x 2,x 3,x 4)
  left_inv := by rintro ⟨a,b,c,d,e⟩; rfl
  right_inv := by intro x; funext i; fin_cases i <;> rfl

lemma valid_decode {n : ℕ} (w : Word n) : Valid w ↔ good (decode n w) := by
  rcases w with ⟨a,b,c,d,e⟩
  unfold Valid good
  suffices hp : repeated (a,b,c,d,e) = reps (decode n (a,b,c,d,e)) by rw [hp]
  unfold repeated reps
  rw [show List.finRange 4 = [0,1,2,3] by decide]
  change (if a = b then [a] else []) ++ (if b = c then [b] else []) ++
      (if c = d then [c] else []) ++ (if d = e then [d] else []) =
      ([if a = b then some a else none, if b = c then some b else none,
        if c = d then some c else none, if d = e then some d else none].filterMap id)
  split_ifs <;> rfl

lemma a_words (n : ℕ) : a n = words n := by
  let S := (univ : Finset (Fin 5 → Fin (n+1))).filter good
  let e : {w : Word n // Valid w} ≃ ↥S :=
    (decode n).subtypeEquiv (fun w => by simpa [S] using valid_decode w)
  unfold a
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

/-- The relation between consecutive repeated values. -/
def R {n : ℕ} (p c : Fin (n + 1)) : Prop := c ≠ p + 1

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

lemma words_eq (n : ℕ) : words n = ∑ v : Fin (n + 1), G 4 v none := by
  unfold words G
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
def ok : Fin 4 → Bool := ![true, false, true, true]

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
  rw [ne_eq, hc1]
  generalize c - p = δ
  by_cases e0 : δ = 0
  · subst e0
    simp [h01]
  · by_cases e1 : δ = 1
    · subst e1
      simp [Ne.symm h01]
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
  simp only [κ, if_neg (Ne.symm h01), if_neg (Ne.symm h0m), if_neg (Ne.symm h1m),
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
lemma g1_0 (n : ℕ) : g n 1 0 = 1 + (n : ℤ) := by
  rw [g, if_pos (show ok 0 = true from rfl), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g1_1 (n : ℕ) : g n 1 1 = (n : ℤ) := by
  rw [g, if_neg (show ¬ (ok 1 = true) by decide), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g1_2 (n : ℕ) : g n 1 2 = 1 + (n : ℤ) := by
  rw [g, if_pos (show ok 2 = true from rfl), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g1_3 (n : ℕ) : g n 1 3 = 1 + (n : ℤ) := by
  rw [g, if_pos (show ok 3 = true from rfl), g0_0, g0_1, g0_2, g0_3]
  ring
lemma g2_0 (n : ℕ) : g n 2 0 = 2 * (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [g, if_pos (show ok 0 = true from rfl), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g2_1 (n : ℕ) : g n 2 1 = (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [g, if_neg (show ¬ (ok 1 = true) by decide), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g2_2 (n : ℕ) : g n 2 2 = 2 * (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [g, if_pos (show ok 2 = true from rfl), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g2_3 (n : ℕ) : g n 2 3 = 2 * (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [g, if_pos (show ok 3 = true from rfl), g1_0, g1_1, g1_2, g1_3]
  ring
lemma g3_0 (n : ℕ) : g n 3 0 = (n : ℤ) + 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3 := by
  rw [g, if_pos (show ok 0 = true from rfl), g2_0, g2_1, g2_2, g2_3]
  ring
lemma h0 (n : ℕ) : h n 0 = 1 := rfl
lemma h1 (n : ℕ) : h n 1 = 1 + (n : ℤ) := by
  rw [h, g0_0, h0]
  ring
lemma h2 (n : ℕ) : h n 2 = 1 + 2 * (n : ℤ) + (n : ℤ) ^ 2 := by
  rw [h, g1_0, h1]
  ring
lemma h3 (n : ℕ) : h n 3 = 3 * (n : ℤ) + 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3 := by
  rw [h, g2_0, h2]
  ring
lemma h4 (n : ℕ) : h n 4 = (n : ℤ) + 6 * (n : ℤ) ^ 2 + 4 * (n : ℤ) ^ 3 + (n : ℤ) ^ 4 := by
  rw [h, g3_0, h3]
  ring

def poly (x : ℤ) : ℤ := x^5 + 5*x^4 + 10*x^3 + 7*x^2 + x

lemma a_poly (n : ℕ) (hn : 1 ≤ n) : (a n : ℤ) = poly n := by
  rw [a_words]
  by_cases h1 : n = 1
  · subst n
    have h1 : words 1 = 24 := by decide
    rw [h1]
    norm_num [poly]
  · have hn2 : 2 ≤ n := by omega
    rw [words_eq]
    push_cast
    rw [sum_congr rfl (fun v _ => (compress hn2 4).2 v), sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul, h4]
    push_cast
    unfold poly
    ring

lemma c_eq (j : ℤ) : c j = if 0 < j then poly j else 0 := by
  unfold c
  split_ifs with pos
  · simpa [Int.toNat_of_nonneg pos.le] using a_poly j.toNat (by omega)
  · rfl

lemma recurrence (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 6*a (n-1) - 15*a (n-2) +
    20*a (n-3) - 15*a (n-4) + 6*a (n-5) - a (n-6) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+7 := ⟨n-7,by omega⟩
  simp (disch := omega) only [a_poly, Nat.cast_sub]
  push_cast
  unfold poly
  ring

end OMA.FiveLetter

open OMA.S_oeis_a269777 OMA.FiveLetter in
theorem OMA.solution : type_of% @OMA.S_oeis_a269777.main := by
  refine ⟨?_, recurrence⟩
  intro j
  by_cases hj : j ≤ 6
  · interval_cases j <;> norm_num [conv,c_eq,poly]
  · obtain ⟨k,rfl⟩ : ∃ k, j = k+7 := ⟨j-7,by omega⟩
    change conv (↑(k+7 : ℕ)) = 0
    simp only [conv,c_eq]
    simp (disch := omega) only [if_pos]
    unfold poly
    ring
