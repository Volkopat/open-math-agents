import OMAStatements.S_oeis_a187175
import Mathlib

open OMA.S_oeis_a187175 PowerSeries

namespace P187175

def D : Fin 4 → ℤ × ℤ := ![(2, 1), (-1, 2), (-2, -1), (1, -2)]

def P (m : Fin 4 → Fin 4) : Fin 5 → ℤ × ℤ :=
  ![0, D (m 0), D (m 0) + D (m 1), D (m 0) + D (m 1) + D (m 2), D (m 0) + D (m 1) + D (m 2) + D (m 3)]

def dec (d : ℤ × ℤ) : Fin 4 :=
  if d = (2, 1) then 0 else if d = (-1, 2) then 1 else if d = (-2, -1) then 2 else 3

theorem D_dec (d : ℤ × ℤ) (h : IsMove d) : D (dec d) = d := by
  unfold IsMove at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem dec_D : ∀ x : Fin 4, dec (D x) = x := by decide

theorem move_D (x : Fin 4) : IsMove (D x) := by
  unfold IsMove
  fin_cases x <;> simp [D]

theorem P_zero (m : Fin 4 → Fin 4) : P m 0 = 0 := rfl

theorem P_succ (m : Fin 4 → Fin 4) (i : Fin 4) : P m i.succ = P m i.castSucc + D (m i) := by
  fin_cases i <;> first | rfl | simp [P]

def pt {n : ℕ} (s : Fin n × Fin n) : ℤ × ℤ := (((s.1 : ℕ) : ℤ), ((s.2 : ℕ) : ℤ))

theorem pt_inj {n : ℕ} {s t : Fin n × Fin n} (h : pt s = pt t) : s = t := by
  simp only [pt, Prod.mk.injEq, Nat.cast_inj] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

def mv {n : ℕ} (f : Fin 5 → Fin n × Fin n) : Fin 4 → Fin 4 :=
  fun i => dec (pt (f i.succ) - pt (f i.castSucc))

theorem walk {n : ℕ} (f : Fin 5 → Fin n × Fin n) (hf : IsTour n f) :
    ∀ i, pt (f i) = pt (f 0) + P (mv f) i := by
  intro i
  induction i using Fin.induction with
  | zero => rw [P_zero, add_zero]
  | succ i ih =>
    rw [P_succ, ← add_assoc, ← ih]
    have hd : D (mv f i) = pt (f i.succ) - pt (f i.castSucc) := D_dec _ (hf.2 i)
    rw [hd]
    abel

def valid (m : Fin 4 → Fin 4) : Prop := Function.Injective (P m)

instance (m : Fin 4 → Fin 4) : Decidable (valid m) := by unfold valid; infer_instance

def inB (n : ℕ) (m : Fin 4 → Fin 4) (s : Fin n × Fin n) : Prop :=
  ∀ i, 0 ≤ (pt s + P m i).1 ∧ (pt s + P m i).1 < n ∧ 0 ≤ (pt s + P m i).2 ∧ (pt s + P m i).2 < n

instance (n : ℕ) (m : Fin 4 → Fin 4) (s : Fin n × Fin n) : Decidable (inB n m s) := by
  unfold inB; infer_instance

def toFin {n : ℕ} (hn : 0 < n) (z : ℤ) : Fin n := ⟨z.toNat % n, Nat.mod_lt _ hn⟩

theorem toFin_val {n : ℕ} (hn : 0 < n) (z : ℤ) (h0 : 0 ≤ z) (h1 : z < n) :
    (((toFin hn z : Fin n) : ℕ) : ℤ) = z := by
  simp only [toFin]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

def jm {n : ℕ} (hn : 0 < n) (ms : (Fin 4 → Fin 4) × (Fin n × Fin n)) : Fin 5 → Fin n × Fin n :=
  fun i => (toFin hn (pt ms.2 + P ms.1 i).1, toFin hn (pt ms.2 + P ms.1 i).2)

theorem pt_jm {n : ℕ} (hn : 0 < n) (m : Fin 4 → Fin 4) (s : Fin n × Fin n) (h : inB n m s) (i : Fin 5) :
    pt (jm hn (m, s) i) = pt s + P m i := by
  obtain ⟨h1, h2, h3, h4⟩ := h i
  simp only [pt, jm]
  ext
  · exact toFin_val hn _ h1 h2
  · exact toFin_val hn _ h3 h4

open Classical in
theorem card_eq (n : ℕ) (hn : 0 < n) :
    (Finset.univ.filter (fun f : Fin 5 → Fin n × Fin n => IsTour n f)).card =
      (Finset.univ.filter (fun ms : (Fin 4 → Fin 4) × (Fin n × Fin n) => valid ms.1 ∧ inB n ms.1 ms.2)).card := by
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

def hi (v : Fin 5 → ℤ) : ℤ := max (v 0) (max (v 1) (max (v 2) (max (v 3) (v 4))))

def lo (v : Fin 5 → ℤ) : ℤ := min (v 0) (min (v 1) (min (v 2) (min (v 3) (v 4))))

theorem cond_iff (n : ℕ) (v : Fin 5 → ℤ) (x : ℤ) :
    (∀ i, 0 ≤ x + v i ∧ x + v i < n) ↔ (0 ≤ x + lo v ∧ x + hi v < n) := by
  constructor
  · intro h
    have := h 0; have := h 1; have := h 2; have := h 3; have := h 4;
    simp only [lo, hi]
    omega
  · intro h i
    simp only [lo, hi] at h
    fin_cases i <;> simp <;> omega

theorem cnt (n : ℕ) (v : Fin 5 → ℤ) (h0 : v 0 = 0) :
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

def sx (m : Fin 4 → Fin 4) : ℕ := (hi (fun i => (P m i).1) - lo (fun i => (P m i).1)).toNat
def sy (m : Fin 4 → Fin 4) : ℕ := (hi (fun i => (P m i).2) - lo (fun i => (P m i).2)).toNat

open Classical in
theorem a_eq (n : ℕ) : a n = ∑ m : Fin 4 → Fin 4, if valid m then (n - sx m) * (n - sy m) else 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : IsEmpty (Fin 5 → Fin 0 × Fin 0) := by
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

end P187175


theorem P187175.bnd : ∀ m : Fin 4 → Fin 4, P187175.sx m ≤ 8 ∧ P187175.sy m ≤ 8 := by decide +kernel

theorem P187175.c1 : (∑ m : Fin 4 → Fin 4, if P187175.valid m then (1 : ℤ) else 0) = 100 := by decide +kernel
theorem P187175.c2 : (∑ m : Fin 4 → Fin 4, if P187175.valid m then ((P187175.sx m + P187175.sy m : ℕ) : ℤ) else 0) = 920 := by decide +kernel
theorem P187175.c3 : (∑ m : Fin 4 → Fin 4, if P187175.valid m then ((P187175.sx m * P187175.sy m : ℕ) : ℤ) else 0) = 1984 := by decide +kernel

open P187175 in
theorem P187175.hpoly (n : ℕ) (hn : 8 ≤ n) : (a n : ℤ) = 100 * n ^ 2 - 920 * n + 1984 := by
  classical
  rw [a_eq, Nat.cast_sum]
  have h : ∀ m : Fin 4 → Fin 4, (((if valid m then (n - sx m) * (n - sy m) else 0 : ℕ)) : ℤ) =
      (if valid m then (1 : ℤ) else 0) * (n : ℤ) ^ 2 - (if valid m then ((sx m + sy m : ℕ) : ℤ) else 0) * n +
        (if valid m then ((sx m * sy m : ℕ) : ℤ) else 0) := by
    intro m
    have := bnd m
    split_ifs
    · rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    · simp
  simp only [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
  convert congrArg (fun z : ℤ × ℤ × ℤ => z.1 * (n : ℤ) ^ 2 - z.2.1 * n + z.2.2)
    (show ((∑ m : Fin 4 → Fin 4, if valid m then (1 : ℤ) else 0),
      (∑ m : Fin 4 → Fin 4, if valid m then ((sx m + sy m : ℕ) : ℤ) else 0),
      (∑ m : Fin 4 → Fin 4, if valid m then ((sx m * sy m : ℕ) : ℤ) else 0)) = (100, 920, 1984) by
        rw [c1, c2, c3]) using 1

def P187175.F (k : ℕ) : ℚ := 100 * ((k : ℚ) + 1) ^ 2 - 920 * ((k : ℚ) + 1) + 1984

open P187175 in
theorem P187175.hA (k j : ℕ) (h : j = k + 1) (hk : 8 ≤ k + 1) : (a j : ℚ) = F k := by
  subst h
  have := hpoly (k + 1) hk
  have hq := congrArg (fun z : ℤ => (z : ℚ)) this
  push_cast at hq
  rw [hq, F]

open P187175 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187175.main := by
  have v0 : (a 0 : ℚ) = 0 := by rw [show a 0 = 0 by rw [a_eq]; decide +kernel]; norm_num
  have v1 : (a 1 : ℚ) = 0 := by rw [show a 1 = 0 by rw [a_eq]; decide +kernel]; norm_num
  have v2 : (a 2 : ℚ) = 0 := by rw [show a 2 = 0 by rw [a_eq]; decide +kernel]; norm_num
  have v3 : (a 3 : ℚ) = 0 := by rw [show a 3 = 0 by rw [a_eq]; decide +kernel]; norm_num
  have v4 : (a 4 : ℚ) = 0 := by rw [show a 4 = 0 by rw [a_eq]; decide +kernel]; norm_num
  have v5 : (a 5 : ℚ) = 16 := by rw [show a 5 = 16 by rw [a_eq]; decide +kernel]; norm_num
  have v6 : (a 6 : ℚ) = 136 := by rw [show a 6 = 136 by rw [a_eq]; decide +kernel]; norm_num
  have v7 : (a 7 : ℚ) = 456 := by rw [show a 7 = 456 by rw [a_eq]; decide +kernel]; norm_num
  have v8 : (a 8 : ℚ) = 1024 := by rw [hA 7 8 rfl (by norm_num)]; norm_num [F]
  have v9 : (a 9 : ℚ) = 1804 := by rw [hA 8 9 rfl (by norm_num)]; norm_num [F]
  have v10 : (a 10 : ℚ) = 2784 := by rw [hA 9 10 rfl (by norm_num)]; norm_num [F]
  refine ⟨fun n hn => hpoly n (by omega), ?_⟩
  · have hL : ((PowerSeries.mk (fun n => (a n : ℚ))) * (1 - X) ^ 3 : PowerSeries ℚ) =
        (PowerSeries.mk (fun n => (a n : ℚ))) - C (3 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 1) + C (3 : ℚ) * ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 2) - ((PowerSeries.mk (fun n => (a n : ℚ))) * X ^ 3) := by
      (try simp only [map_ofNat]) <;> ring
    have hR : (4 * X ^ 5 * (2 - X) * (2 + 12 * X + 18 * X ^ 2 + 15 * X ^ 3 + 3 * X ^ 4) : PowerSeries ℚ) = C (16 : ℚ) * X ^ 5 + C (88 : ℚ) * X ^ 6 + C (96 : ℚ) * X ^ 7 + C (48 : ℚ) * X ^ 8 - C (36 : ℚ) * X ^ 9 - C (12 : ℚ) * X ^ 10 := by
      (try simp only [map_ofNat, pow_one]) <;> ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk,
      coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · norm_num [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
    · simp only [show n + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = n + 11 by omega]
      have e : ∀ k : ℕ, k ≤ 10 → (n + 11 = k) = False := fun k hk => by
        simp only [eq_iff_iff, iff_false]; omega
      have e3 : ∀ k : ℕ, k ≤ 11 → (k ≤ n + 11) = True := fun k hk => by
        simp only [eq_iff_iff, iff_true]; omega
      simp only [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega), e 9 (by omega), e 10 (by omega), e3 1 (by omega), e3 2 (by omega), e3 3 (by omega), if_true, if_false]
      rw [hA (n + 10) (n + 11) (by omega) (by omega), hA (n + 9) (n + 11 - 1) (by omega) (by omega), hA (n + 8) (n + 11 - 2) (by omega) (by omega), hA (n + 7) (n + 11 - 3) (by omega) (by omega)]
      simp only [F]
      push_cast
      ring

