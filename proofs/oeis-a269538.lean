import OMAStatements.S_oeis_a269538

/-!
OEIS A269538 (R. H. Hardin, Feb 29 2016): Number of length-4 0..n arrays with no repeated value differing from the previous repeated value by other than one.
Conjectures from Colin Barker, Jan 24 2019: G.f.: 2*x*(1 + x)*(5 + 2*x - x^2) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Proof. The repeated values are the values of the adjacent equal pairs, in order (`reps`), and
consecutive repeated values p, c must satisfy (c : ℕ) = (p : ℕ) + 1 ∨ (p : ℕ) = (c : ℕ) + 1 (`R`). Reading the array from the left
with state (last value v, last repeated value r), G(m, v, r) counts the valid continuations by m
entries, and G(m + 1, v, r) = [R r v] G(m, v, v) + sum over a != v of G(m, a, r) (`G_succ`).
Unrolling the second term, G(m, v, r) = n^m + sum over d < m and w of f_d(v, w) [R r w] H(m - 1 - d, w)
(`G_unroll`), where f_d(v, w) counts the walks of d moves to a different value from v to w, equal to
A_d or B_d as v = w or not (`fK_eq`), and H(j, w) = G(j, w, w). Apart from 0, the relation allows
the steps 1 and -1, so H(j, .) is an explicit combination of the numbers E_k(w) of walks of k
such steps from w that stay in 0..n (`H0`, ...), and the sum of E_k(w) over w is the sum over the
2^k step sequences of the number of starting points, n + 1 minus the span of the sequence when that
is positive (`sum_E`, `W0`, ...). This gives a(n) for every n (`a_form`), and a polynomial in n for
n >= 1 (`a_poly`); the g.f. and the recurrence follow by comparing coefficients.
-/

namespace OMA.S_oeis_a269538

open PowerSeries Finset


/-- The relation between consecutive repeated values. -/
def R {n : ℕ} (p c : Fin (n + 1)) : Prop := (c : ℕ) = (p : ℕ) + 1 ∨ (p : ℕ) = (c : ℕ) + 1

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


lemma a_eq (n : ℕ) : a n = ∑ v : Fin (n + 1), G 3 v none := by
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

/-! Walks on the complete graph without loops. -/

/-- (A_d, B_d): the walks of d moves between two equal, resp. two different, values. -/
def AB (n : ℕ) : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | d + 1 => ((n : ℤ) * (AB n d).2, (AB n d).1 + ((n : ℤ) - 1) * (AB n d).2)

lemma AB_succ (n d : ℕ) :
    AB n (d + 1) = ((n : ℤ) * (AB n d).2, (AB n d).1 + ((n : ℤ) - 1) * (AB n d).2) := rfl

/-- The walks of d moves from v to w, each move to a different value. -/
def fK (n : ℕ) : ℕ → Fin (n + 1) → Fin (n + 1) → ℤ
  | 0, v, w => if v = w then 1 else 0
  | d + 1, v, w => ∑ a : Fin (n + 1), if a = v then 0 else fK n d a w

lemma sum_ne (n : ℕ) (v : Fin (n + 1)) (F : Fin (n + 1) → ℤ) :
    ∑ a : Fin (n + 1), (if a = v then 0 else F a) = (∑ a : Fin (n + 1), F a) - F v := by
  rw [← Finset.add_sum_erase univ F (mem_univ v),
    ← Finset.add_sum_erase univ (fun a => if a = v then (0 : ℤ) else F a) (mem_univ v)]
  rw [if_pos rfl, zero_add, add_sub_cancel_left]
  refine sum_congr rfl (fun a ha => ?_)
  rw [if_neg (ne_of_mem_erase ha)]

lemma sum_pt (n : ℕ) (w : Fin (n + 1)) (x y : ℤ) :
    ∑ a : Fin (n + 1), (if a = w then x else y) = x + n * y := by
  rw [← Finset.add_sum_erase univ _ (mem_univ w), if_pos rfl,
    sum_congr rfl (fun a ha => if_neg (ne_of_mem_erase ha)), sum_const,
    card_erase_of_mem (mem_univ w), card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

lemma fK_eq (n d : ℕ) : ∀ v w : Fin (n + 1), fK n d v w = if v = w then (AB n d).1 else (AB n d).2 := by
  induction d with
  | zero => intro v w; simp [fK, AB]
  | succ d ih =>
    intro v w
    simp only [fK]
    rw [sum_ne]
    simp only [ih]
    rw [sum_pt]
    simp only [AB]
    split_ifs <;> ring

lemma AB_col (n d : ℕ) : (AB n d).1 + (n : ℤ) * (AB n d).2 = (n : ℤ) ^ d := by
  induction d with
  | zero => simp [AB]
  | succ d ih =>
    simp only [AB, pow_succ]
    linear_combination (n : ℤ) * ih

lemma col (n d : ℕ) (w : Fin (n + 1)) : ∑ v : Fin (n + 1), fK n d v w = (n : ℤ) ^ d := by
  simp only [fK_eq]
  rw [sum_pt, AB_col]

lemma fK_zero_mul (n : ℕ) (v : Fin (n + 1)) (Y : Fin (n + 1) → ℤ) :
    ∑ w : Fin (n + 1), fK n 0 v w * Y w = Y v := by
  simp only [fK, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

lemma unroll_step (n m : ℕ) (v : Fin (n + 1)) (X : ℕ → Fin (n + 1) → ℤ) :
    ∑ a : Fin (n + 1), (if a = v then 0 else ((n : ℤ) ^ m + ∑ d ∈ range m, ∑ w : Fin (n + 1),
      fK n d a w * X d w)) =
      (n : ℤ) ^ (m + 1) + ∑ d ∈ range m, ∑ w : Fin (n + 1), fK n (d + 1) v w * X d w := by
  have hs : ∑ a : Fin (n + 1), ∑ d ∈ range m, ∑ w : Fin (n + 1), fK n d a w * X d w =
      ∑ d ∈ range m, ∑ w : Fin (n + 1), (∑ a : Fin (n + 1), fK n d a w) * X d w :=
    calc ∑ a : Fin (n + 1), ∑ d ∈ range m, ∑ w : Fin (n + 1), fK n d a w * X d w
        = ∑ d ∈ range m, ∑ a : Fin (n + 1), ∑ w : Fin (n + 1), fK n d a w * X d w :=
          Finset.sum_comm
      _ = ∑ d ∈ range m, ∑ w : Fin (n + 1), ∑ a : Fin (n + 1), fK n d a w * X d w :=
          sum_congr rfl (fun d _ => Finset.sum_comm)
      _ = ∑ d ∈ range m, ∑ w : Fin (n + 1), (∑ a : Fin (n + 1), fK n d a w) * X d w := by
          simp only [Finset.sum_mul]
  have hf : ∀ d w, fK n (d + 1) v w = (∑ a : Fin (n + 1), fK n d a w) - fK n d v w := by
    intro d w
    simp only [fK]
    rw [sum_ne]
  rw [sum_ne, Finset.sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, hs]
  simp only [hf, sub_mul, Finset.sum_sub_distrib]
  push_cast
  ring

lemma G_unroll (n m : ℕ) : ∀ (v : Fin (n + 1)) (r : Option (Fin (n + 1))),
    (G m v r : ℤ) = (n : ℤ) ^ m + ∑ d ∈ range m, ∑ w : Fin (n + 1),
      fK n d v w * (if ∀ p ∈ r, R p w then (G (m - 1 - d) w (some w) : ℤ) else 0) := by
  induction m with
  | zero => intro v r; simp [G_zero]
  | succ m ih =>
    intro v r
    have ih' := fun a => ih a r
    rw [G_succ]
    push_cast
    simp only [ih']
    rw [unroll_step, sum_range_succ', fK_zero_mul]
    have e1 : ∀ d : ℕ, m - 1 - d = m - (d + 1) := fun d => by omega
    simp only [e1, Nat.sub_zero]
    ring

/-- H m w: the continuations by m entries right after a repeat at w. -/
def H (n m : ℕ) (w : Fin (n + 1)) : ℤ := G m w (some w)

lemma G_none (n m : ℕ) (v : Fin (n + 1)) :
    (G m v none : ℤ) = (n : ℤ) ^ m + ∑ d ∈ range m, ∑ w : Fin (n + 1), fK n d v w * H n (m - 1 - d) w := by
  rw [G_unroll]
  simp [H]

lemma a_sum (n m : ℕ) : ∑ v : Fin (n + 1), (G m v none : ℤ) =
    ((n : ℤ) + 1) * (n : ℤ) ^ m + ∑ d ∈ range m, (n : ℤ) ^ d * ∑ w : Fin (n + 1), H n (m - 1 - d) w := by
  simp only [G_none]
  rw [Finset.sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_comm]
  push_cast
  congr 1
  refine sum_congr rfl (fun d _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine sum_congr rfl (fun w _ => ?_)
  rw [← Finset.sum_mul, col]

/-- The neighbors of w for the relation, other than w. -/
def Kf (n : ℕ) (g : Fin (n + 1) → ℤ) (w : Fin (n + 1)) : ℤ :=
  ∑ w' : Fin (n + 1), if w' = w then 0 else if R w w' then g w' else 0

lemma Kf_add (n : ℕ) (f g : Fin (n + 1) → ℤ) (w : Fin (n + 1)) :
    Kf n (fun w' => f w' + g w') w = Kf n f w + Kf n g w := by
  unfold Kf
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl (fun w' _ => ?_)
  split_ifs <;> ring

lemma Kf_smul (n : ℕ) (c : ℤ) (f : Fin (n + 1) → ℤ) (w : Fin (n + 1)) :
    Kf n (fun w' => c * f w') w = c * Kf n f w := by
  unfold Kf
  rw [Finset.mul_sum]
  refine sum_congr rfl (fun w' _ => ?_)
  split_ifs <;> ring

lemma H_zero (n : ℕ) (w : Fin (n + 1)) : H n 0 w = 1 := by
  simp [H, G_zero]

lemma a0_eq {n : ℕ} (w : Fin (n + 1)) (x : ℤ) : (if R w w then x else 0) = 0 := by
  simp [R]

lemma H_rec (n m : ℕ) (w : Fin (n + 1)) :
    H n m w = (n : ℤ) ^ m + ∑ d ∈ range m, ((AB n d).1 * (if R w w then H n (m - 1 - d) w else 0) +
      (AB n d).2 * Kf n (H n (m - 1 - d)) w) := by
  have e : H n m w = (n : ℤ) ^ m + ∑ d ∈ range m, ∑ w' : Fin (n + 1),
      fK n d w w' * (if R w w' then H n (m - 1 - d) w' else 0) := by
    unfold H
    rw [G_unroll]
    simp
  rw [e]
  congr 1
  refine sum_congr rfl (fun d _ => ?_)
  simp only [fK_eq, ite_mul]
  rw [← Finset.add_sum_erase univ _ (mem_univ w), if_pos rfl]
  congr 1
  unfold Kf
  rw [Finset.mul_sum, ← Finset.add_sum_erase univ _ (mem_univ w), if_pos rfl, mul_zero, zero_add]
  refine sum_congr rfl (fun w' hw' => ?_)
  have hne : w' ≠ w := ne_of_mem_erase hw'
  rw [if_neg (Ne.symm hne), if_neg hne]

/-! Walks inside 0..n with the relation's nonzero steps. -/

/-- The nonzero steps of the relation. -/
def stp : Fin 2 → ℤ := ![1, -1]

lemma stp0 : stp 0 = (1 : ℤ) := rfl

lemma stp1 : stp 1 = (-1 : ℤ) := rfl

lemma R_steps {n : ℕ} (p c : Fin (n + 1)) :
    (c ≠ p ∧ R p c) ↔ ((c : ℤ) = (p : ℤ) + (1) ∨ (c : ℤ) = (p : ℤ) + (-1)) := by
  simp only [R, ne_eq, Fin.ext_iff]
  omega

/-- The step s from w, if it stays in 0..n. -/
def T (n : ℕ) (s : ℤ) (g : Fin (n + 1) → ℤ) (w : Fin (n + 1)) : ℤ :=
  if h : 0 ≤ (w : ℤ) + s ∧ (w : ℤ) + s ≤ n then g ⟨((w : ℤ) + s).toNat, by omega⟩ else 0

lemma sum_single (n : ℕ) (s : ℤ) (g : Fin (n + 1) → ℤ) (w : Fin (n + 1)) :
    ∑ w' : Fin (n + 1), (if (w' : ℤ) = (w : ℤ) + s then g w' else 0) = T n s g w := by
  unfold T
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨((w : ℤ) + s).toNat, by omega⟩]
    · rw [if_pos (by simp; omega)]
    · intro b _ hb
      rw [if_neg]
      intro hb2
      apply hb
      ext
      simp only [Fin.val_mk]
      omega
    · simp
  · refine Finset.sum_eq_zero (fun w' _ => ?_)
    rw [if_neg]
    intro hw
    have := w'.isLt
    omega

lemma Kf_steps (n : ℕ) (g : Fin (n + 1) → ℤ) (w : Fin (n + 1)) :
    Kf n g w = T n (1) g w + T n (-1) g w := by
  rw [← sum_single, ← sum_single, ← Finset.sum_add_distrib]
  unfold Kf
  refine sum_congr rfl (fun w' _ => ?_)
  have hs := R_steps w w'
  by_cases hw : w' = w
  · subst hw
    have h1 : ¬ ((w' : ℤ) = (w' : ℤ) + (1)) := by omega
    have h2 : ¬ ((w' : ℤ) = (w' : ℤ) + (-1)) := by omega
    rw [if_pos rfl, if_neg h1, if_neg h2]
    ring
  · rw [if_neg hw]
    by_cases h1 : (w' : ℤ) = (w : ℤ) + (1)
    · have h2 : ¬ ((w' : ℤ) = (w : ℤ) + (-1)) := by omega
      rw [if_pos (hs.mpr (Or.inl h1)).2, if_pos h1, if_neg h2]
      ring
    · by_cases h2 : (w' : ℤ) = (w : ℤ) + (-1)
      · rw [if_pos (hs.mpr (Or.inr h2)).2, if_neg h1, if_pos h2]
        ring
      · have hR : ¬ R w w' := fun hR => (hs.mp ⟨hw, hR⟩).elim h1 h2
        rw [if_neg hR, if_neg h1, if_neg h2]
        ring

/-- Whether the walk δ from z stays in 0..n. -/
def wokb (n : ℕ) : (k : ℕ) → ℤ → (Fin k → Fin 2) → Bool
  | 0, _, _ => true
  | k + 1, z, δ => decide (0 ≤ z + stp (δ 0) ∧ z + stp (δ 0) ≤ n) && wokb n k (z + stp (δ 0)) (Fin.tail δ)

/-- E k w: the number of walks of k steps from w inside 0..n. -/
def E (n k : ℕ) (w : Fin (n + 1)) : ℤ :=
  ∑ δ : Fin k → Fin 2, if wokb n k (w : ℤ) δ = true then 1 else 0

lemma sum_fun_succ (k : ℕ) (F : (Fin (k + 1) → Fin 2) → ℤ) :
    ∑ δ, F δ = ∑ δ' : Fin k → Fin 2, (F (Fin.cons 0 δ') + F (Fin.cons 1 δ')) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin 2)) (fun p => F (Fin.cons p.1 p.2)) F
    (fun p => rfl), Fintype.sum_prod_type, Fin.sum_univ_two, ← Finset.sum_add_distrib]

lemma E_zero (n : ℕ) (w : Fin (n + 1)) : E n 0 w = 1 := by
  simp [E, wokb]

lemma E_step (n k : ℕ) (w : Fin (n + 1)) (i : Fin 2) :
    ∑ δ' : Fin k → Fin 2, (if wokb n (k + 1) (w : ℤ) (Fin.cons i δ') = true then (1 : ℤ) else 0) =
      T n (stp i) (E n k) w := by
  simp only [wokb, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true, decide_eq_true_eq]
  unfold T E
  split_ifs with h
  · refine sum_congr rfl (fun δ' _ => ?_)
    have e : ((((w : ℤ) + stp i).toNat : ℕ) : ℤ) = (w : ℤ) + stp i := Int.toNat_of_nonneg h.1
    simp only [e, h, true_and]
  · refine sum_eq_zero (fun δ' _ => ?_)
    rw [if_neg (fun hc => h hc.1)]

lemma E_succ (n k : ℕ) (w : Fin (n + 1)) :
    E n (k + 1) w = T n (stp 0) (E n k) w + T n (stp 1) (E n k) w := by
  rw [← E_step, ← E_step, ← Finset.sum_add_distrib]
  exact sum_fun_succ k (fun δ => if wokb n (k + 1) (w : ℤ) δ = true then (1 : ℤ) else 0)

lemma Kf_E (n k : ℕ) (w : Fin (n + 1)) : Kf n (E n k) w = E n (k + 1) w := by
  rw [Kf_steps, E_succ, stp0, stp1]

lemma Kf_E' (n k : ℕ) (w : Fin (n + 1)) : Kf n (fun w' => E n k w') w = E n (k + 1) w :=
  Kf_E n k w

/-- The lowest position of a walk relative to its start. -/
def lo : (k : ℕ) → (Fin k → Fin 2) → ℤ
  | 0, _ => 0
  | k + 1, δ => min 0 (stp (δ 0) + lo k (Fin.tail δ))

/-- The highest position of a walk relative to its start. -/
def hi : (k : ℕ) → (Fin k → Fin 2) → ℤ
  | 0, _ => 0
  | k + 1, δ => max 0 (stp (δ 0) + hi k (Fin.tail δ))

lemma lo_le : ∀ (k : ℕ) (δ : Fin k → Fin 2), lo k δ ≤ 0
  | 0, _ => le_refl 0
  | _ + 1, _ => min_le_left _ _

lemma hi_ge : ∀ (k : ℕ) (δ : Fin k → Fin 2), 0 ≤ hi k δ
  | 0, _ => le_refl 0
  | _ + 1, _ => le_max_left _ _

lemma wok_iff (n : ℕ) : ∀ (k : ℕ) (z : ℤ) (δ : Fin k → Fin 2), 0 ≤ z → z ≤ n →
    (wokb n k z δ = true ↔ -lo k δ ≤ z ∧ z ≤ n - hi k δ) := by
  intro k
  induction k with
  | zero => intro z δ h0 hn; simp [wokb, lo, hi, h0, hn]
  | succ k ih =>
    intro z δ h0 hn
    simp only [wokb, Bool.and_eq_true, decide_eq_true_eq, lo, hi]
    have hl := lo_le k (Fin.tail δ)
    have hh := hi_ge k (Fin.tail δ)
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := (ih (z + stp (δ 0)) (Fin.tail δ) h1 h2).mp h3
      omega
    · rintro ⟨h1, h2⟩
      have hr : 0 ≤ z + stp (δ 0) ∧ z + stp (δ 0) ≤ n := by omega
      exact ⟨hr, (ih (z + stp (δ 0)) (Fin.tail δ) hr.1 hr.2).mpr (by omega)⟩

lemma card_interval (n : ℕ) (p q : ℤ) (h1 : 0 ≤ p) (h2 : q ≤ n) :
    (((univ : Finset (Fin (n + 1))).filter
      (fun w : Fin (n + 1) => p ≤ ((w : ℕ) : ℤ) ∧ ((w : ℕ) : ℤ) ≤ q)).card : ℤ) =
      ((q + 1 - p).toNat : ℤ) := by
  have h : ((univ : Finset (Fin (n + 1))).filter
      (fun w : Fin (n + 1) => p ≤ ((w : ℕ) : ℤ) ∧ ((w : ℕ) : ℤ) ≤ q)).card = (Finset.Icc p q).card := by
    refine card_bij' (fun w _ => ((w : ℕ) : ℤ))
      (fun j hj => ⟨j.toNat, by simp only [mem_Icc] at hj; omega⟩) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw
      simp only [mem_Icc]
      exact hw
    · intro j hj
      simp only [mem_Icc] at hj
      simp only [mem_filter, mem_univ, true_and]
      omega
    · intro w _
      ext
      simp
    · intro j hj
      simp only [mem_Icc] at hj
      show ((j.toNat : ℕ) : ℤ) = j
      omega
  rw [h, Int.card_Icc]

/-- The number of starting points in 0..n for a walk of span s. -/
def cnt (n : ℕ) (s : ℤ) : ℤ := (((n : ℤ) + 1 - s).toNat : ℤ)

lemma cnt_of (n : ℕ) (s : ℤ) (h : s ≤ (n : ℤ) + 1) : cnt n s = (n : ℤ) + 1 - s := by
  unfold cnt
  exact Int.toNat_of_nonneg (by omega)

lemma sum_E (n k : ℕ) :
    ∑ w : Fin (n + 1), E n k w = ∑ δ : Fin k → Fin 2, cnt n (hi k δ - lo k δ) := by
  unfold E
  rw [Finset.sum_comm]
  refine sum_congr rfl (fun δ _ => ?_)
  rw [Finset.sum_boole]
  rw [filter_congr (fun (w : Fin (n + 1)) _ => wok_iff n k ((w : ℕ) : ℤ) δ (by positivity)
    (by have := w.isLt; omega))]
  rw [card_interval n _ _ (by have := lo_le k δ; omega) (by have := hi_ge k δ; omega)]
  unfold cnt
  congr 2
  ring

lemma AB0 (n : ℕ) : AB n 0 = (1, 0) := rfl

lemma AB1 (n : ℕ) : AB n 1 = (0, 1) := by
  rw [AB_succ, AB0]
  refine Prod.ext ?_ ?_ <;> dsimp only <;> ring

lemma H0 (n : ℕ) (w : Fin (n + 1)) : H n 0 w = (1) * E n 0 w := by
  simp [H_zero, E_zero]

lemma H1 (n : ℕ) (w : Fin (n + 1)) : H n 1 w = ((n : ℤ)) * E n 0 w := by
  rw [H_rec]
  simp only [sum_range_succ, sum_range_zero, zero_add, show 1 - 1 - 0 = 0 from rfl,
    AB0 n, a0_eq]
  rw [show H n 0 = fun w' => (1) * E n 0 w' from funext (H0 n)]
  simp only [Kf_add, Kf_smul, Kf_E, Kf_E']
  simp only [E_zero]
  ring

lemma H2 (n : ℕ) (w : Fin (n + 1)) : H n 2 w = ((n : ℤ) ^ 2) * E n 0 w + (1) * E n 1 w := by
  rw [H_rec]
  simp only [sum_range_succ, sum_range_zero, zero_add, show 2 - 1 - 0 = 1 from rfl, show 2 - 1 - 1 = 0 from rfl,
    AB0 n, AB1 n, a0_eq]
  rw [show H n 0 = fun w' => (1) * E n 0 w' from funext (H0 n)]
  rw [show H n 1 = fun w' => ((n : ℤ)) * E n 0 w' from funext (H1 n)]
  simp only [Kf_add, Kf_smul, Kf_E, Kf_E']
  simp only [E_zero]
  ring

lemma W0 (n : ℕ) : ∑ w : Fin (n + 1), E n 0 w = cnt n 0 := by
  rw [sum_E]
  simp only [sum_fun_succ, Fintype.sum_unique, hi, lo, Fin.cons_zero, Fin.tail_cons, stp0,
    stp1] <;> (try norm_num) <;> ring

lemma W1 (n : ℕ) : ∑ w : Fin (n + 1), E n 1 w = 2 * cnt n 1 := by
  rw [sum_E]
  simp only [sum_fun_succ, Fintype.sum_unique, hi, lo, Fin.cons_zero, Fin.tail_cons, stp0,
    stp1] <;> (try norm_num) <;> ring

/-- The exact count. -/
lemma a_form (n : ℕ) : (a n : ℤ) = ((n : ℤ) + 1) * (n : ℤ) ^ 3 + (n : ℤ) ^ 0 * (((n : ℤ) ^ 2) * (∑ w : Fin (n + 1), E n 0 w) + (1) * (∑ w : Fin (n + 1), E n 1 w)) + (n : ℤ) ^ 1 * (((n : ℤ)) * (∑ w : Fin (n + 1), E n 0 w)) + (n : ℤ) ^ 2 * ((1) * (∑ w : Fin (n + 1), E n 0 w)) := by
  rw [a_eq]
  push_cast
  rw [a_sum]
  simp only [sum_range_succ, sum_range_zero, zero_add, show 3 - 1 - 0 = 2 from rfl, show 3 - 1 - 1 = 1 from rfl, show 3 - 1 - 2 = 0 from rfl]
  simp only [H0 n, H1 n, H2 n, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- a(n) as a polynomial in n, for n >= 1. -/
lemma a_poly (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 2 * (n : ℚ) + 3 * (n : ℚ) ^ 2 + 4 * (n : ℚ) ^ 3 + (n : ℚ) ^ 4 := by
  have h : (a n : ℤ) = 2 * (n : ℤ) + 3 * (n : ℤ) ^ 2 + 4 * (n : ℤ) ^ 3 + (n : ℤ) ^ 4 := by
    rw [a_form]
    simp only [W0, W1]
    rcases Nat.lt_or_ge n 1 with hs | hb
    · omega
    · simp only [cnt_of n 0 (by omega), cnt_of n 1 (by omega)]
      ring
  exact_mod_cast h

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X * (1 + X) * (5 + 2 * X - X ^ 2) := by
  have v1 : (a 1 : ℚ) = 10 := by rw [a_poly 1 (by norm_num)]; norm_num
  have v2 : (a 2 : ℚ) = 64 := by rw [a_poly 2 (by norm_num)]; norm_num
  have v3 : (a 3 : ℚ) = 222 := by rw [a_poly 3 (by norm_num)]; norm_num
  have v4 : (a 4 : ℚ) = 568 := by rw [a_poly 4 (by norm_num)]; norm_num
  have v5 : (a 5 : ℚ) = 1210 := by rw [a_poly 5 (by norm_num)]; norm_num
  have v6 : (a 6 : ℚ) = 2280 := by rw [a_poly 6 (by norm_num)]; norm_num
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 5 = A - C (5 : ℚ) * (A * X ^ 1) + C (10 : ℚ) * (A * X ^ 2) - C (10 : ℚ) * (A * X ^ 3) + C (5 : ℚ) * (A * X ^ 4) - A * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have e2 : (2 * X * (1 + X) * (5 + 2 * X - X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C (10 : ℚ) + X ^ 2 * C (14 : ℚ) + X ^ 3 * C (2 : ℚ) - X ^ 4 * C (2 : ℚ) := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | m
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
  · simp only [show ¬ (m + 7 = 0) by omega,
      show 1 ≤ m + 7 by omega,
      show m + 7 - 1 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show 2 ≤ m + 7 by omega,
      show m + 7 - 2 = m + 5 by omega,
      show ¬ (m + 5 = 0) by omega,
      show 3 ≤ m + 7 by omega,
      show m + 7 - 3 = m + 4 by omega,
      show ¬ (m + 4 = 0) by omega,
      show 4 ≤ m + 7 by omega,
      show m + 7 - 4 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega,
      show 5 ≤ m + 7 by omega,
      show m + 7 - 5 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega,
      show ¬ (m + 7 = 1) by omega,
      show ¬ (m + 7 = 2) by omega,
      show ¬ (m + 7 = 3) by omega,
      show ¬ (m + 7 = 4) by omega, if_true, if_false]
    rw [a_poly (m + 7) (by omega), a_poly (m + 6) (by omega), a_poly (m + 5) (by omega), a_poly (m + 4) (by omega), a_poly (m + 3) (by omega), a_poly (m + 2) (by omega)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega, show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega, show m + 6 - 5 = m + 1 by omega]
  have h : (a (m + 6) : ℚ) = 5 * a (m + 5) - 10 * a (m + 4) + 10 * a (m + 3) - 5 * a (m + 2) + a (m + 1) := by
    rw [a_poly (m + 6) (by omega), a_poly (m + 5) (by omega), a_poly (m + 4) (by omega), a_poly (m + 3) (by omega), a_poly (m + 2) (by omega), a_poly (m + 1) (by omega)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      2 * X * (1 + X) * (5 + 2 * X - X ^ 2) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a269538

theorem OMA.solution : type_of% @OMA.S_oeis_a269538.main :=
  OMA.S_oeis_a269538.conjecture
