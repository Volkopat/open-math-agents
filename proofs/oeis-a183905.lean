import OMAStatements.S_oeis_a183905
import Mathlib

/-!
# A183905: nondecreasing arrangements of n+2 numbers in 0..2, each the sum mod 3 of two others

Write N = n + 2. A nondecreasing arrangement s of N numbers in 0..2 is fixed by p, the number
of its zeros, and q, the number of its entries at most 1: s is 0 below position p, 1 from p to
q and 2 from q on (for monotone s, s i < v exactly when i is below the number of entries < v).
With c0 = p, c1 = q - p, c2 = N - q, each number is the sum mod 3 of two others exactly when
a present 0 has two other 0s or a 1 and a 2, a present 1 has another 1 and a 0 or two 2s, and
a present 2 has another 2 and a 0 or two 1s. For N ≥ 4 exactly 11 of the (N + 1)(N + 2)/2
pairs p ≤ q ≤ N fail this, so 2 a(n) + 22 = (n + 3)(n + 4) for n ≥ 2; with a(0) = 0 and
a(1) = 1 (kernel computation) this gives the recurrence and the g.f.
-/

namespace OMA.P183905

open OMA.S_oeis_a183905 PowerSeries

/-- The step arrangement: 0 below p, 1 from p to q, 2 from q on. -/
def st (N p q : ℕ) : Fin N → Fin 3 := fun i =>
  ⟨if i.val < p then 0 else if i.val < q then 1 else 2, by split_ifs <;> omega⟩

lemma st_val (N p q : ℕ) (i : Fin N) :
    (st N p q i).val = if i.val < p then 0 else if i.val < q then 1 else 2 := rfl

/-- The multiplicity condition, with (c0, c1, c2) = (p, q - p, N - q). -/
abbrev cond (N p q : ℕ) : Prop :=
  (0 < p → (3 ≤ p ∨ (p < q ∧ q < N))) ∧
  (p < q → ((0 < p ∧ p + 2 ≤ q) ∨ q + 2 ≤ N)) ∧
  (q < N → ((0 < p ∧ q + 2 ≤ N) ∨ p + 2 ≤ q))

/-- The admissible pairs (p, q). -/
def Q (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    (fun pq => pq.1 ≤ pq.2 ∧ cond N pq.1 pq.2)

lemma card_lt (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter (fun j : Fin N => j.val < m)).card = m := by
  rw [← Finset.card_range m]
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simpa using hj
  · intro j1 _ j2 _ h
    exact Fin.ext h
  · intro b hb
    simp only [Finset.mem_range] at hb
    exact ⟨⟨b, by omega⟩, by simp [hb], rfl⟩

lemma mono_iff {N : ℕ} (s : Fin N → Fin 3) (hs : ∀ i j : Fin N, i ≤ j → s i ≤ s j) (v : ℕ)
    (i : Fin N) :
    (s i).val < v ↔ i.val < (Finset.univ.filter (fun j : Fin N => (s j).val < v)).card := by
  have hi := i.is_lt
  constructor
  · intro h
    have hsub : Finset.univ.filter (fun j : Fin N => j.val < i.val + 1) ⊆
        Finset.univ.filter (fun j : Fin N => (s j).val < v) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have := hs j i (by rw [Fin.le_iff_val_le_val]; omega)
      rw [Fin.le_iff_val_le_val] at this
      omega
    have := Finset.card_le_card hsub
    rw [card_lt N (i.val + 1) (by omega)] at this
    omega
  · intro h
    by_contra hc
    have hsub : Finset.univ.filter (fun j : Fin N => (s j).val < v) ⊆
        Finset.univ.filter (fun j : Fin N => j.val < i.val) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra hji
      have := hs i j (by rw [Fin.le_iff_val_le_val]; omega)
      rw [Fin.le_iff_val_le_val] at this
      omega
    have := Finset.card_le_card hsub
    rw [card_lt N i.val (by omega)] at this
    omega

/-- A nondecreasing arrangement is the step arrangement of its counts. -/
lemma st_eq {N : ℕ} (s : Fin N → Fin 3) (hs : ∀ i j : Fin N, i ≤ j → s i ≤ s j) :
    st N (Finset.univ.filter (fun j : Fin N => (s j).val < 1)).card
      (Finset.univ.filter (fun j : Fin N => (s j).val < 2)).card = s := by
  funext i
  have h1 := mono_iff s hs 1 i
  have h2 := mono_iff s hs 2 i
  have h3 := (s i).is_lt
  apply Fin.ext
  rw [st_val]
  split_ifs <;> omega

lemma st_mono (N p q : ℕ) : ∀ i j : Fin N, i ≤ j → st N p q i ≤ st N p q j := by
  intro i j hij
  rw [Fin.le_iff_val_le_val] at hij ⊢
  simp only [st_val]
  split_ifs <;> omega

lemma card_st (N p q : ℕ) (hpq : p ≤ q) (hq : q ≤ N) :
    (Finset.univ.filter (fun j : Fin N => (st N p q j).val < 1)).card = p ∧
    (Finset.univ.filter (fun j : Fin N => (st N p q j).val < 2)).card = q := by
  have e1 : Finset.univ.filter (fun j : Fin N => (st N p q j).val < 1) =
      Finset.univ.filter (fun j : Fin N => j.val < p) := by
    apply Finset.filter_congr
    intro j _
    rw [st_val]
    split_ifs <;> omega
  have e2 : Finset.univ.filter (fun j : Fin N => (st N p q j).val < 2) =
      Finset.univ.filter (fun j : Fin N => j.val < q) := by
    apply Finset.filter_congr
    intro j _
    rw [st_val]
    split_ifs <;> omega
  rw [e1, e2, card_lt N p (by omega), card_lt N q hq]
  exact ⟨rfl, rfl⟩

lemma P_imp_cond (N p q : ℕ) (hpq : p ≤ q) (hq : q ≤ N)
    (h : ∀ i : Fin N, ∃ j k : Fin N, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      ((st N p q i) : ℕ) = (((st N p q j) : ℕ) + ((st N p q k) : ℕ)) % 3) : cond N p q := by
  refine ⟨fun hp => ?_, fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨j, k, hj, hk, hjk, he⟩ := h ⟨0, by omega⟩
    simp only [st_val] at he
    rw [Ne, Fin.ext_iff] at hj hk hjk
    have := j.is_lt
    have := k.is_lt
    simp only at hj hk
    split_ifs at he <;> omega
  · obtain ⟨j, k, hj, hk, hjk, he⟩ := h ⟨p, by omega⟩
    simp only [st_val] at he
    rw [Ne, Fin.ext_iff] at hj hk hjk
    have := j.is_lt
    have := k.is_lt
    simp only at hj hk
    split_ifs at he <;> omega
  · obtain ⟨j, k, hj, hk, hjk, he⟩ := h ⟨q, by omega⟩
    simp only [st_val] at he
    rw [Ne, Fin.ext_iff] at hj hk hjk
    have := j.is_lt
    have := k.is_lt
    simp only at hj hk
    split_ifs at he <;> omega

lemma cond_imp_P (N p q : ℕ) (hpq : p ≤ q) (hq : q ≤ N) (hc : cond N p q) :
    ∀ i : Fin N, ∃ j k : Fin N, j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      ((st N p q i) : ℕ) = (((st N p q j) : ℕ) + ((st N p q k) : ℕ)) % 3 := by
  intro i
  have hi := i.is_lt
  obtain ⟨c1, c2, c3⟩ := hc
  by_cases h1 : i.val < p
  · rcases c1 (by omega) with h | h
    · refine ⟨⟨if i.val = 0 then 1 else 0, by split_ifs <;> omega⟩,
        ⟨if i.val ≤ 1 then 2 else 1, by split_ifs <;> omega⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Ne, Fin.ext_iff, st_val] <;> (try split_ifs) <;> first | omega | simp
    · refine ⟨⟨p, by omega⟩, ⟨q, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
        simp only [Ne, Fin.ext_iff, st_val] <;> (try split_ifs) <;> first | omega | simp
  · by_cases h2 : i.val < q
    · rcases c2 (by omega) with h | h
      · refine ⟨⟨0, by omega⟩, ⟨if i.val = p then p + 1 else p, by split_ifs <;> omega⟩,
          ?_, ?_, ?_, ?_⟩ <;>
          simp only [Ne, Fin.ext_iff, st_val] <;> (try split_ifs) <;> first | omega | simp
      · refine ⟨⟨q, by omega⟩, ⟨q + 1, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Ne, Fin.ext_iff, st_val] <;> (try split_ifs) <;> first | omega | simp
    · rcases c3 (by omega) with h | h
      · refine ⟨⟨0, by omega⟩, ⟨if i.val = q then q + 1 else q, by split_ifs <;> omega⟩,
          ?_, ?_, ?_, ?_⟩ <;>
          simp only [Ne, Fin.ext_iff, st_val] <;> (try split_ifs) <;> first | omega | simp
      · refine ⟨⟨p, by omega⟩, ⟨p + 1, by omega⟩, ?_, ?_, ?_, ?_⟩ <;>
          simp only [Ne, Fin.ext_iff, st_val] <;> (try split_ifs) <;> first | omega | simp

/-- The arrangements correspond to the admissible pairs. -/
lemma a_eq (n : ℕ) : a n = (Q (n + 2)).card := by
  unfold a
  apply Finset.card_nbij' (fun s => ((Finset.univ.filter (fun j : Fin (n + 2) => (s j).val < 1)).card,
    (Finset.univ.filter (fun j : Fin (n + 2) => (s j).val < 2)).card))
    (fun pq => st (n + 2) pq.1 pq.2)
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨hm, hP⟩ := hs
    have he := st_eq s hm
    have hpN := Finset.card_filter_le Finset.univ (fun j : Fin (n + 2) => (s j).val < 1)
    have hqN := Finset.card_filter_le Finset.univ (fun j : Fin (n + 2) => (s j).val < 2)
    have hpq : (Finset.univ.filter (fun j : Fin (n + 2) => (s j).val < 1)).card ≤
        (Finset.univ.filter (fun j : Fin (n + 2) => (s j).val < 2)).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      omega
    simp only [Finset.card_univ, Fintype.card_fin] at hpN hqN
    simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨by omega, by omega⟩, hpq, ?_⟩
    apply P_imp_cond (n + 2) _ _ hpq hqN
    rw [he]
    exact hP
  · intro pq hpq
    simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨st_mono _ _ _, cond_imp_P _ _ _ hpq.2.1 (by omega) hpq.2.2⟩
  · intro s hs
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact st_eq s hs.1
  · intro pq hpq
    simp only [Q, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
    obtain ⟨h1, h2⟩ := card_st (n + 2) pq.1 pq.2 hpq.2.1 (by omega)
    simp only [h1, h2]

/-- The pairs p ≤ q ≤ N. -/
def T (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun pq => pq.1 ≤ pq.2)

lemma T_succ (N : ℕ) :
    T (N + 1) = T N ∪ (Finset.range (N + 2)).image (fun p => (p, N + 1)) := by
  ext ⟨p, q⟩
  simp only [T, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · intro h
    by_cases hq : q = N + 1
    · exact Or.inr ⟨p, by omega, rfl, hq.symm⟩
    · left
      omega
  · rintro (h | ⟨x, hx, rfl, rfl⟩)
    · omega
    · omega

lemma T_card (N : ℕ) : 2 * (T N).card = (N + 1) * (N + 2) := by
  induction N with
  | zero => decide
  | succ N ih =>
    rw [T_succ, Finset.card_union_of_disjoint, Finset.card_image_of_injective]
    · simp only [Finset.card_range]
      nlinarith [ih]
    · intro x y hxy
      simp only [Prod.mk.injEq] at hxy
      exact hxy.1
    · rw [Finset.disjoint_left]
      intro x hx hy
      simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_image] at hx hy
      obtain ⟨b, hb, rfl⟩ := hy
      simp only at hx
      omega

/-- The 11 pairs p ≤ q ≤ N that fail the condition, for N ≥ 4. -/
def B (N : ℕ) : Finset (ℕ × ℕ) :=
  {(0, 0), (0, 1), (0, N - 1), (0, N), (1, 1), (1, N), (2, 2), (2, N), (N - 2, N - 1),
    (N - 1, N - 1), (N - 1, N)}

lemma T_filter_not (N : ℕ) (hN : 4 ≤ N) :
    (T N).filter (fun pq => ¬ cond N pq.1 pq.2) = B N := by
  ext ⟨p, q⟩
  simp only [T, B, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hp, hq⟩, hpq⟩, hnc⟩
    simp only [not_and_or, Classical.not_imp] at hnc
    rcases hnc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hp' : p = 1 ∨ p = 2 := by omega
      have hq' : p = q ∨ N = q := by omega
      rcases hp' with rfl | rfl <;> rcases hq' with rfl | rfl <;> simp
    · have hq' : q = N - 1 ∨ N = q := by omega
      have hp' : p = 0 ∨ p + 1 = q := by omega
      rcases hp' with rfl | hp' <;> rcases hq' with rfl | rfl
      · simp
      · simp
      · obtain rfl : p = N - 2 := by omega
        simp
      · obtain rfl : p = N - 1 := by omega
        simp
    · have hp' : p = 0 ∨ q = N - 1 := by omega
      rcases hp' with rfl | rfl
      · have hq' : q = 0 ∨ q = 1 := by omega
        rcases hq' with rfl | rfl <;> simp
      · have hp'' : p = N - 1 ∨ p = N - 2 := by omega
        rcases hp'' with rfl | rfl <;> simp
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

lemma B_card (N : ℕ) (hN : 4 ≤ N) : (B N).card = 11 := by
  unfold B
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  all_goals
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega

lemma Q_card (N : ℕ) (hN : 4 ≤ N) : 2 * (Q N).card + 22 = (N + 1) * (N + 2) := by
  have h1 := Finset.card_filter_add_card_filter_not (s := T N)
    (fun pq : ℕ × ℕ => cond N pq.1 pq.2)
  have hQ : (T N).filter (fun pq => cond N pq.1 pq.2) = Q N := by
    ext ⟨p, q⟩
    simp only [T, Q, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    tauto
  rw [hQ, T_filter_not N hN, B_card N hN] at h1
  have h2 := T_card N
  nlinarith [h1, h2]

/-- The closed form, multiplied by 2, for n ≥ 2. -/
lemma closed (n : ℕ) (hn : 2 ≤ n) : 2 * (a n : ℤ) = (n + 3) * (n + 4) - 22 := by
  have h := Q_card (n + 2) (by omega)
  rw [← a_eq] at h
  have h' : ((2 * a n + 22 : ℕ) : ℤ) = (((n + 2 + 1) * (n + 2 + 2) : ℕ) : ℤ) := by rw [h]
  push_cast at h'
  linear_combination h'

lemma a_zero : a 0 = 0 := by
  rw [a_eq]
  decide

lemma a_one : a 1 = 1 := by
  rw [a_eq]
  decide

lemma recur (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega]
  have d5 := closed (k + 5) (by omega)
  have d4 := closed (k + 4) (by omega)
  have d3 := closed (k + 3) (by omega)
  have d2 := closed (k + 2) (by omega)
  push_cast at d5 d4 d3 d2
  have : 2 * ((a (k + 5) : ℤ) - 3 * a (k + 4) + 3 * a (k + 3) - a (k + 2)) = 0 := by
    linear_combination d5 - 3 * d4 + 3 * d3 - d2
  omega

lemma gf : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 : PowerSeries ℤ) =
    X * (1 + X + X ^ 2 - 2 * X ^ 3) := by
  have e : PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 : PowerSeries ℤ) =
      PowerSeries.mk (fun n => (a n : ℤ))
      - (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1 + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1
        + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 1)
      + (PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2 + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2
        + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 2)
      - PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 3 := by
    ring
  have hN : (X * (1 + X + X ^ 2 - 2 * X ^ 3) : PowerSeries ℤ) =
      C 1 * X ^ 1 + C 1 * X ^ 2 + C 1 * X ^ 3 - C 2 * X ^ 4 := by
    simp only [map_one, map_ofNat]
    ring
  rw [e, hN]
  ext m
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_C]
  have c2 := closed 2 le_rfl
  have c3 := closed 3 (by norm_num)
  have c4 := closed 4 (by norm_num)
  norm_num at c2 c3 c4
  have z0 := a_zero
  have z1 := a_one
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> simp [z0, z1] <;> omega
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
    have r := recur (j + 5) (by omega)
    simp only [show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega, show 3 ≤ j + 5 by omega,
      show 4 ≤ j + 5 by omega, if_true, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega] at r ⊢
    simp
    linear_combination r

theorem sol : type_of% @OMA.S_oeis_a183905.main := ⟨gf, recur⟩

end OMA.P183905

theorem OMA.solution : type_of% @OMA.S_oeis_a183905.main := OMA.P183905.sol

