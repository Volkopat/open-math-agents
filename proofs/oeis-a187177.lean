import OMAStatements.S_oeis_a187177
import Mathlib

open OMA.S_oeis_a187177 PowerSeries

namespace P187177

def D : Fin 4 → ℤ × ℤ := ![(2, 1), (-1, 2), (-2, -1), (1, -2)]

def P (m : Fin 6 → Fin 4) : Fin 7 → ℤ × ℤ :=
  ![0, D (m 0), D (m 0) + D (m 1), D (m 0) + D (m 1) + D (m 2), D (m 0) + D (m 1) + D (m 2) + D (m 3), D (m 0) + D (m 1) + D (m 2) + D (m 3) + D (m 4), D (m 0) + D (m 1) + D (m 2) + D (m 3) + D (m 4) + D (m 5)]

def dec (d : ℤ × ℤ) : Fin 4 :=
  if d = (2, 1) then 0 else if d = (-1, 2) then 1 else if d = (-2, -1) then 2 else 3

theorem D_dec (d : ℤ × ℤ) (h : IsMove d) : D (dec d) = d := by
  unfold IsMove at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem dec_D : ∀ x : Fin 4, dec (D x) = x := by decide

theorem move_D (x : Fin 4) : IsMove (D x) := by
  unfold IsMove
  fin_cases x <;> simp [D]

theorem P_zero (m : Fin 6 → Fin 4) : P m 0 = 0 := rfl

theorem P_succ (m : Fin 6 → Fin 4) (i : Fin 6) : P m i.succ = P m i.castSucc + D (m i) := by
  fin_cases i <;> first | rfl | simp [P]

def pt {n : ℕ} (s : Fin n × Fin n) : ℤ × ℤ := (((s.1 : ℕ) : ℤ), ((s.2 : ℕ) : ℤ))

theorem pt_inj {n : ℕ} {s t : Fin n × Fin n} (h : pt s = pt t) : s = t := by
  simp only [pt, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

def mv {n : ℕ} (f : Fin 7 → Fin n × Fin n) : Fin 6 → Fin 4 :=
  fun i => dec (pt (f i.succ) - pt (f i.castSucc))

theorem walk {n : ℕ} (f : Fin 7 → Fin n × Fin n) (hf : IsTour n f) :
    ∀ i, pt (f i) = pt (f 0) + P (mv f) i := by
  intro i
  induction i using Fin.induction with
  | zero => rw [P_zero, add_zero]
  | succ i ih =>
    rw [P_succ, ← add_assoc, ← ih]
    have hd : D (mv f i) = pt (f i.succ) - pt (f i.castSucc) := D_dec _ (hf.2 i)
    rw [hd]
    abel

def valid (m : Fin 6 → Fin 4) : Prop := Function.Injective (P m)

instance (m : Fin 6 → Fin 4) : Decidable (valid m) := by unfold valid; infer_instance

def inB (n : ℕ) (m : Fin 6 → Fin 4) (s : Fin n × Fin n) : Prop :=
  ∀ i, 0 ≤ (pt s + P m i).1 ∧ (pt s + P m i).1 < n ∧ 0 ≤ (pt s + P m i).2 ∧ (pt s + P m i).2 < n

instance (n : ℕ) (m : Fin 6 → Fin 4) (s : Fin n × Fin n) : Decidable (inB n m s) := by
  unfold inB; infer_instance

def toFin {n : ℕ} (hn : 0 < n) (z : ℤ) : Fin n := ⟨z.toNat % n, Nat.mod_lt _ hn⟩

theorem toFin_val {n : ℕ} (hn : 0 < n) (z : ℤ) (h0 : 0 ≤ z) (h1 : z < n) :
    (((toFin hn z : Fin n) : ℕ) : ℤ) = z := by
  simp only [toFin]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

def jm {n : ℕ} (hn : 0 < n) (ms : (Fin 6 → Fin 4) × (Fin n × Fin n)) : Fin 7 → Fin n × Fin n :=
  fun i => (toFin hn (pt ms.2 + P ms.1 i).1, toFin hn (pt ms.2 + P ms.1 i).2)

theorem pt_jm {n : ℕ} (hn : 0 < n) (m : Fin 6 → Fin 4) (s : Fin n × Fin n) (h : inB n m s) (i : Fin 7) :
    pt (jm hn (m, s) i) = pt s + P m i := by
  obtain ⟨h1, h2, h3, h4⟩ := h i
  simp only [pt, jm]
  ext
  · exact toFin_val hn _ h1 h2
  · exact toFin_val hn _ h3 h4

open Classical in
theorem card_eq (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter (fun f : Fin 7 → Fin n × Fin n => IsTour n f)).card =
      (Finset.univ.filter (fun ms : (Fin 6 → Fin 4) × (Fin n × Fin n) => valid ms.1 ∧ inB n ms.1 ms.2)).card := by
  apply Finset.card_nbij' (fun f => (mv f, f 0)) (jm hn)
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    have hw := walk f hf
    refine ⟨fun i j hij => hf.1 (pt_inj ?_), fun i => ?_⟩
    · rw [hw i, hw j, hij]
    · rw [← hw i]
      simp only [pt]
      omega
  · rintro ⟨m, s⟩ hms
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hms ⊢
    obtain ⟨hv, hb⟩ := hms
    refine ⟨fun i j hij => hv ?_, fun i => ?_⟩
    · have := congrArg pt hij
      rw [pt_jm hn m s hb, pt_jm hn m s hb] at this
      exact add_left_cancel this
    · have e : (((jm hn (m, s) i.succ).1 : ℤ) - (jm hn (m, s) i.castSucc).1,
          ((jm hn (m, s) i.succ).2 : ℤ) - (jm hn (m, s) i.castSucc).2) = D (m i) := by
        have h1 := pt_jm hn m s hb i.succ
        have h2 := pt_jm hn m s hb i.castSucc
        rw [P_succ] at h1
        have : pt (jm hn (m, s) i.succ) - pt (jm hn (m, s) i.castSucc) = D (m i) := by
          rw [h1, h2]; abel
        exact this
      rw [e]
      exact move_D _
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
    have hw := walk f hf
    funext i
    apply pt_inj
    have hb : inB n (mv f) (f 0) := fun i => by rw [← hw i]; simp only [pt]; omega
    rw [pt_jm hn _ _ hb, hw i]
  · rintro ⟨m, s⟩ hms
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hms
    obtain ⟨hv, hb⟩ := hms
    have h0 : jm hn (m, s) 0 = s := by
      apply pt_inj
      rw [pt_jm hn m s hb, P_zero, add_zero]
    refine Prod.ext ?_ h0
    funext i
    show dec (pt (jm hn (m, s) i.succ) - pt (jm hn (m, s) i.castSucc)) = m i
    rw [pt_jm hn m s hb, pt_jm hn m s hb, P_succ]
    have : pt s + (P m i.castSucc + D (m i)) - (pt s + P m i.castSucc) = D (m i) := by abel
    rw [this, dec_D]

def hi (v : Fin 7 → ℤ) : ℤ := max (v 0) (max (v 1) (max (v 2) (max (v 3) (max (v 4) (max (v 5) (v 6))))))

def lo (v : Fin 7 → ℤ) : ℤ := min (v 0) (min (v 1) (min (v 2) (min (v 3) (min (v 4) (min (v 5) (v 6))))))

theorem lo_le (v : Fin 7 → ℤ) (i : Fin 7) : lo v ≤ v i := by
  fin_cases i <;> simp [lo, min_le_iff]

theorem le_hi (v : Fin 7 → ℤ) (i : Fin 7) : v i ≤ hi v := by
  fin_cases i <;> simp [hi, le_max_iff]

theorem cond_iff (n : ℕ) (v : Fin 7 → ℤ) (x : ℤ) :
    (∀ i, 0 ≤ x + v i ∧ x + v i < n) ↔ (0 ≤ x + lo v ∧ x + hi v < n) := by
  constructor
  · intro h
    have h1 : -x ≤ lo v := by
      simp only [lo, le_min_iff]
      exact ⟨by linarith [(h 0).1], by linarith [(h 1).1], by linarith [(h 2).1], by linarith [(h 3).1], by linarith [(h 4).1], by linarith [(h 5).1], by linarith [(h 6).1]⟩
    have h2 : hi v < n - x := by
      simp only [hi, max_lt_iff]
      exact ⟨by linarith [(h 0).2], by linarith [(h 1).2], by linarith [(h 2).2], by linarith [(h 3).2], by linarith [(h 4).2], by linarith [(h 5).2], by linarith [(h 6).2]⟩
    constructor <;> linarith
  · intro h i
    have := lo_le v i
    have := le_hi v i
    constructor <;> linarith

theorem cnt (n : ℕ) (v : Fin 7 → ℤ) (h0 : v 0 = 0) :
    (Finset.univ.filter (fun x : Fin n => ∀ i, 0 ≤ ((x : ℕ) : ℤ) + v i ∧ ((x : ℕ) : ℤ) + v i < n)).card =
      n - (hi v - lo v).toNat := by
  have hl : lo v ≤ 0 := by simp only [lo]; rw [h0]; omega
  have hh : 0 ≤ hi v := by simp only [hi]; rw [h0]; omega
  have e : (Finset.univ.filter (fun x : Fin n => ∀ i, 0 ≤ ((x : ℕ) : ℤ) + v i ∧ ((x : ℕ) : ℤ) + v i < n)).map
      Fin.valEmbedding = Finset.Ico (-lo v).toNat (n - (hi v).toNat) := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico, cond_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := x.isLt
      omega
    · intro hy
      exact ⟨⟨y, by omega⟩, by simp only; omega, rfl⟩
  rw [← Finset.card_map, e, Nat.card_Ico]
  omega

def sx (m : Fin 6 → Fin 4) : ℕ := (hi (fun i => (P m i).1) - lo (fun i => (P m i).1)).toNat
def sy (m : Fin 6 → Fin 4) : ℕ := (hi (fun i => (P m i).2) - lo (fun i => (P m i).2)).toNat

open Classical in
theorem a_eq (n : ℕ) : a n = ∑ m : Fin 6 → Fin 4, if valid m then (n - sx m) * (n - sy m) else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsEmpty (Fin 7 → Fin 0 × Fin 0) := by
      refine ⟨fun f => ?_⟩
      exact (f 0).1.elim0
    simp [a]
  unfold a
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, card_eq n hn, Finset.card_filter,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hv : valid m
  · simp only [hv, true_and, if_true]
    rw [← Finset.card_filter]
    have e : (Finset.univ.filter (fun s : Fin n × Fin n => inB n m s)) =
        (Finset.univ.filter (fun x : Fin n => ∀ i, 0 ≤ ((x : ℕ) : ℤ) + (P m i).1 ∧ ((x : ℕ) : ℤ) + (P m i).1 < n)) ×ˢ
        (Finset.univ.filter (fun y : Fin n => ∀ i, 0 ≤ ((y : ℕ) : ℤ) + (P m i).2 ∧ ((y : ℕ) : ℤ) + (P m i).2 < n)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
      show inB n m (x, y) ↔ _
      unfold inB
      simp only [pt, Prod.fst_add, Prod.snd_add]
      constructor
      · intro h
        exact ⟨fun i => ⟨(h i).1, (h i).2.1⟩, fun i => ⟨(h i).2.2.1, (h i).2.2.2⟩⟩
      · rintro ⟨h1, h2⟩ i
        exact ⟨(h1 i).1, (h1 i).2, (h2 i).1, (h2 i).2⟩
    rw [e, Finset.card_product, cnt n _ rfl, cnt n _ rfl]
    rfl
  · simp [hv]

end P187177


def P187177.st (m : Fin 6 → Fin 4) : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) :=
  if P187177.valid m then (((1 : ℤ), ((P187177.sx m + P187177.sy m : ℕ) : ℤ), ((P187177.sx m * P187177.sy m : ℕ) : ℤ), (if P187177.sx m ≤ 12 ∧ P187177.sy m ≤ 12 then (0 : ℤ) else 1), (((0 - P187177.sx m) * (0 - P187177.sy m) : ℕ) : ℤ), (((1 - P187177.sx m) * (1 - P187177.sy m) : ℕ) : ℤ)), ((((2 - P187177.sx m) * (2 - P187177.sy m) : ℕ) : ℤ), (((3 - P187177.sx m) * (3 - P187177.sy m) : ℕ) : ℤ), (((4 - P187177.sx m) * (4 - P187177.sy m) : ℕ) : ℤ), (((5 - P187177.sx m) * (5 - P187177.sy m) : ℕ) : ℤ), (((6 - P187177.sx m) * (6 - P187177.sy m) : ℕ) : ℤ), (((7 - P187177.sx m) * (7 - P187177.sy m) : ℕ) : ℤ)), ((((8 - P187177.sx m) * (8 - P187177.sy m) : ℕ) : ℤ), (((9 - P187177.sx m) * (9 - P187177.sy m) : ℕ) : ℤ), (((10 - P187177.sx m) * (10 - P187177.sy m) : ℕ) : ℤ), (((11 - P187177.sx m) * (11 - P187177.sy m) : ℕ) : ℤ))) else 0

set_option maxRecDepth 20000 in
theorem P187177.stats : (∑ m : Fin 6 → Fin 4, P187177.st m) = ((780, 9880, 29384, 0, 0, 0), (0, 0, 0, 0, 16, 368), (1600, 4284, 8760, 15104)) :=
  @of_decide_eq_true _ ((@instDecidableEqProd (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) ((ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ)) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ) (inferInstance : DecidableEq ℤ) (inferInstance : DecidableEq ℤ)))))) (@instDecidableEqProd (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) ((ℤ × ℤ × ℤ × ℤ)) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ) (inferInstance : DecidableEq ℤ) (inferInstance : DecidableEq ℤ)))))) (@instDecidableEqProd ℤ (ℤ × ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ × ℤ) (inferInstance : DecidableEq ℤ) (@instDecidableEqProd ℤ (ℤ) (inferInstance : DecidableEq ℤ) (inferInstance : DecidableEq ℤ)))))) _ _) (by decide +kernel)

open Classical in
def P187177.a_alias (n : ℕ) : ℕ := ∑ m : Fin 6 → Fin 4, if P187177.valid m then (n - P187177.sx m) * (n - P187177.sy m) else 0

set_option maxRecDepth 20000 in
theorem P187177.c1 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (1 : ℤ) else 0) = 780 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.1.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.c2 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then ((P187177.sx m + P187177.sy m : ℕ) : ℤ) else 0) = 9880 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.1.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.c3 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then ((P187177.sx m * P187177.sy m : ℕ) : ℤ) else 0) = 29384 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.1.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cv : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (if P187177.sx m ≤ 12 ∧ P187177.sy m ≤ 12 then (0 : ℤ) else 1) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.1.2.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw0 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((0 - P187177.sx m) * (0 - P187177.sy m) : ℕ) : ℤ) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.1.2.2.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw1 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((1 - P187177.sx m) * (1 - P187177.sy m) : ℕ) : ℤ) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.1.2.2.2.2.2) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw2 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((2 - P187177.sx m) * (2 - P187177.sy m) : ℕ) : ℤ) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.1.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw3 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((3 - P187177.sx m) * (3 - P187177.sy m) : ℕ) : ℤ) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.1.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw4 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((4 - P187177.sx m) * (4 - P187177.sy m) : ℕ) : ℤ) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.1.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw5 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((5 - P187177.sx m) * (5 - P187177.sy m) : ℕ) : ℤ) else 0) = 0 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.1.2.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw6 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((6 - P187177.sx m) * (6 - P187177.sy m) : ℕ) : ℤ) else 0) = 16 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.1.2.2.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw7 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((7 - P187177.sx m) * (7 - P187177.sy m) : ℕ) : ℤ) else 0) = 368 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.1.2.2.2.2.2) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw8 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((8 - P187177.sx m) * (8 - P187177.sy m) : ℕ) : ℤ) else 0) = 1600 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw9 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((9 - P187177.sx m) * (9 - P187177.sy m) : ℕ) : ℤ) else 0) = 4284 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw10 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((10 - P187177.sx m) * (10 - P187177.sy m) : ℕ) : ℤ) else 0) = 8760 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.2.2.2.1) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

set_option maxRecDepth 20000 in
theorem P187177.cw11 : (∑ m : Fin 6 → Fin 4, if P187177.valid m then (((11 - P187177.sx m) * (11 - P187177.sy m) : ℕ) : ℤ) else 0) = 15104 := by
  have h := congrArg (fun z : (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) => z.2.2.2.2.2) P187177.stats
  simp only [Prod.fst_sum, Prod.snd_sum] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold P187177.st
  split_ifs <;> rfl

theorem P187177.w0 : P187177.a_alias 0 = 0 := by
  have h := P187177.cw0
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (0 - P187177.sx m) * (0 - P187177.sy m) else 0 : ℕ) : ℤ) = 0 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w1 : P187177.a_alias 1 = 0 := by
  have h := P187177.cw1
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (1 - P187177.sx m) * (1 - P187177.sy m) else 0 : ℕ) : ℤ) = 0 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w2 : P187177.a_alias 2 = 0 := by
  have h := P187177.cw2
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (2 - P187177.sx m) * (2 - P187177.sy m) else 0 : ℕ) : ℤ) = 0 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w3 : P187177.a_alias 3 = 0 := by
  have h := P187177.cw3
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (3 - P187177.sx m) * (3 - P187177.sy m) else 0 : ℕ) : ℤ) = 0 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w4 : P187177.a_alias 4 = 0 := by
  have h := P187177.cw4
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (4 - P187177.sx m) * (4 - P187177.sy m) else 0 : ℕ) : ℤ) = 0 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w5 : P187177.a_alias 5 = 0 := by
  have h := P187177.cw5
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (5 - P187177.sx m) * (5 - P187177.sy m) else 0 : ℕ) : ℤ) = 0 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w6 : P187177.a_alias 6 = 16 := by
  have h := P187177.cw6
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (6 - P187177.sx m) * (6 - P187177.sy m) else 0 : ℕ) : ℤ) = 16 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w7 : P187177.a_alias 7 = 368 := by
  have h := P187177.cw7
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (7 - P187177.sx m) * (7 - P187177.sy m) else 0 : ℕ) : ℤ) = 368 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w8 : P187177.a_alias 8 = 1600 := by
  have h := P187177.cw8
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (8 - P187177.sx m) * (8 - P187177.sy m) else 0 : ℕ) : ℤ) = 1600 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w9 : P187177.a_alias 9 = 4284 := by
  have h := P187177.cw9
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (9 - P187177.sx m) * (9 - P187177.sy m) else 0 : ℕ) : ℤ) = 4284 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w10 : P187177.a_alias 10 = 8760 := by
  have h := P187177.cw10
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (10 - P187177.sx m) * (10 - P187177.sy m) else 0 : ℕ) : ℤ) = 8760 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

theorem P187177.w11 : P187177.a_alias 11 = 15104 := by
  have h := P187177.cw11
  unfold P187177.a_alias
  have e : ((∑ m : Fin 6 → Fin 4, if P187177.valid m then (11 - P187177.sx m) * (11 - P187177.sy m) else 0 : ℕ) : ℤ) = 15104 := by
    refine Eq.trans ?_ h
    simp only [Nat.cast_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  exact_mod_cast e

open P187177 in
theorem P187177.hpoly (n : ℕ) (hn : 12 ≤ n) : (a n : ℤ) = 780 * n ^ 2 - 9880 * n + 29384 := by
  classical
  rw [a_eq, Nat.cast_sum]
  have h : ∀ m : Fin 6 → Fin 4, (((if valid m then (n - sx m) * (n - sy m) else 0 : ℕ)) : ℤ) =
      (if valid m then (1 : ℤ) else 0) * (n : ℤ) ^ 2 - (if valid m then ((sx m + sy m : ℕ) : ℤ) else 0) * n +
        (if valid m then ((sx m * sy m : ℕ) : ℤ) else 0) := by
    intro m
    split_ifs with hv
    · have hb : sx m ≤ 12 ∧ sy m ≤ 12 := by
        have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => by
          split_ifs <;> norm_num)).mp cv m (Finset.mem_univ _)
        simp only [hv, if_true] at hz
        by_contra hc
        rw [if_neg hc] at hz
        norm_num at hz
      rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    · simp
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, c1, c2, c3]

def P187177.F (k : ℕ) : ℚ := 780 * ((k : ℚ) + 1) ^ 2 - 9880 * ((k : ℚ) + 1) + 29384

open P187177 in
theorem P187177.hA (k j : ℕ) (h : j = k + 1) (hk : 12 ≤ k + 1) : (a j : ℚ) = F k := by
  subst h
  have := hpoly (k + 1) hk
  have hq := congrArg (fun z : ℤ => (z : ℚ)) this
  push_cast at hq
  rw [hq, F]

open P187177 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187177.main := by
  have v0 : (a 0 : ℚ) = 0 := by rw [show a 0 = 0 by rw [a_eq]; exact P187177.w0]; norm_num
  have v1 : (a 1 : ℚ) = 0 := by rw [show a 1 = 0 by rw [a_eq]; exact P187177.w1]; norm_num
  have v2 : (a 2 : ℚ) = 0 := by rw [show a 2 = 0 by rw [a_eq]; exact P187177.w2]; norm_num
  have v3 : (a 3 : ℚ) = 0 := by rw [show a 3 = 0 by rw [a_eq]; exact P187177.w3]; norm_num
  have v4 : (a 4 : ℚ) = 0 := by rw [show a 4 = 0 by rw [a_eq]; exact P187177.w4]; norm_num
  have v5 : (a 5 : ℚ) = 0 := by rw [show a 5 = 0 by rw [a_eq]; exact P187177.w5]; norm_num
  have v6 : (a 6 : ℚ) = 16 := by rw [show a 6 = 16 by rw [a_eq]; exact P187177.w6]; norm_num
  have v7 : (a 7 : ℚ) = 368 := by rw [show a 7 = 368 by rw [a_eq]; exact P187177.w7]; norm_num
  have v8 : (a 8 : ℚ) = 1600 := by rw [show a 8 = 1600 by rw [a_eq]; exact P187177.w8]; norm_num
  have v9 : (a 9 : ℚ) = 4284 := by rw [show a 9 = 4284 by rw [a_eq]; exact P187177.w9]; norm_num
  have v10 : (a 10 : ℚ) = 8760 := by rw [show a 10 = 8760 by rw [a_eq]; exact P187177.w10]; norm_num
  have v11 : (a 11 : ℚ) = 15104 := by rw [show a 11 = 15104 by rw [a_eq]; exact P187177.w11]; norm_num
  have v12 : (a 12 : ℚ) = 23144 := by rw [hA 11 12 rfl (by norm_num)]; norm_num [F]
  have v13 : (a 13 : ℚ) = 32764 := by rw [hA 12 13 rfl (by norm_num)]; norm_num [F]
  have v14 : (a 14 : ℚ) = 43944 := by rw [hA 13 14 rfl (by norm_num)]; norm_num [F]
  refine ⟨fun n hn => hpoly n (by omega), ?_⟩
  · have hL : ((PowerSeries.mk (fun n => (a n : ℚ))) * (1 - X) ^ 3 : PowerSeries ℚ) =
        (PowerSeries.mk (fun n => (a n : ℚ))) - C (3 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 1) + C (3 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 2) - ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 3) := by
      (try simp only [map_ofNat]) <;> ring
    have hR : (4 * X ^ 6 * (4 + 80 * X + 136 * X ^ 2 + 143 * X ^ 3 + 85 * X ^ 4 + 19 * X ^ 5 - 43 * X ^ 6 - 29 * X ^ 7 - 5 * X ^ 8) : PowerSeries ℚ) = C (16 : ℚ) * X ^ 6 + C (320 : ℚ) * X ^ 7 + C (544 : ℚ) * X ^ 8 + C (572 : ℚ) * X ^ 9 + C (340 : ℚ) * X ^ 10 + C (76 : ℚ) * X ^ 11 - C (172 : ℚ) * X ^ 12 - C (116 : ℚ) * X ^ 13 - C (20 : ℚ) * X ^ 14 := by
      (try simp only [map_ofNat, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 15 by omega]
      have e : ∀ k : ℕ, k ≤ 14 → (n + 15 = k) = False := fun k hk => by
        simp only [eq_iff_iff, iff_false]; omega
      have e3 : ∀ k : ℕ, k ≤ 15 → (k ≤ n + 15) = True := fun k hk => by
        simp only [eq_iff_iff, iff_true]; omega
      simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega), e 13 (by omega), e 14 (by omega), e3 1 (by omega), e3 2 (by omega), e3 3 (by omega), if_true, if_false]
      rw [hA (n + 14) (n + 15) (by omega) (by omega), hA (n + 13) (n + 15 - 1) (by omega) (by omega), hA (n + 12) (n + 15 - 2) (by omega) (by omega), hA (n + 11) (n + 15 - 3) (by omega) (by omega)]
      simp only [F]
      push_cast
      ring

