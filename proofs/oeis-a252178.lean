import OMAStatements.S_oeis_a252178

namespace OMA.S_oeis_a252178

open PowerSeries





section TripleCounts

lemma card_piFinset_cons {α : Type*} [DecidableEq α] (s : Finset α) {L : ℕ}
    (P : (Fin (L + 1) → α) → Prop) [DecidablePred P] :
    ((Fintype.piFinset fun _ : Fin (L + 1) => s).filter P).card =
      ∑ v ∈ s, ((Fintype.piFinset fun _ : Fin L => s).filter (fun y => P (Fin.cons v y))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : Fin (L + 1) → α => x 0) (t := s)
    (fun x hx => by
      simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hx
      exact hx.1 0)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  symm
  apply Finset.card_bij (fun y _ => (Fin.cons v y : Fin (L + 1) → α))
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
    refine ⟨⟨fun i => ?_, hy.2⟩, by simp⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv
    · simpa using hy.1 j
  · intro y₁ _ y₂ _ e
    simpa using congrArg Fin.tail e
  · intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx
    obtain ⟨⟨hmem, hp⟩, h0⟩ := hx
    refine ⟨Fin.tail x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => hmem i.succ, ?_⟩
      rw [← h0, Fin.cons_self_tail]
      exact hp
    · show Fin.cons v (Fin.tail x) = x
      rw [← h0, Fin.cons_self_tail]

/-- 0..n arrays, as functions into ℕ with values in range (n + 1). -/
lemma card_fin_eq_piFinset {k n : ℕ} (P : (Fin k → ℕ) → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun x : Fin k → Fin (n + 1) => P (fun i => (x i : ℕ)))).card =
      ((Fintype.piFinset fun _ : Fin k => Finset.range (n + 1)).filter P).card := by
  apply Finset.card_bij (fun x _ => fun i => (x i : ℕ))
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    exact ⟨fun i => (x i).isLt, hx⟩
  · intro x₁ _ x₂ _ h
    funext i
    exact Fin.ext (congrFun h i)
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hy
    exact ⟨fun i => ⟨y i, hy.1 i⟩, by simpa using hy.2, rfl⟩

/-- A count of arrays x(0..3) as a sum over the four entries. -/
lemma card4 (s : Finset ℕ) (Q : ℕ → ℕ → ℕ → ℕ → Prop) [∀ a b c d, Decidable (Q a b c d)] :
    ((Fintype.piFinset fun _ : Fin 4 => s).filter (fun x => Q (x 0) (x 1) (x 2) (x 3))).card =
      ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, if Q a b c d then 1 else 0 := by
  rw [card_piFinset_cons]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [card_piFinset_cons]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [card_piFinset_cons]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [card_piFinset_cons]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hu : (Fintype.piFinset fun _ : Fin 0 => s) = {Fin.elim0} := by
    ext g
    simp only [Fintype.mem_piFinset, Finset.mem_singleton]
    exact ⟨fun _ => funext fun i => i.elim0, fun _ i => i.elim0⟩
  rw [hu, Finset.filter_singleton]
  show (if Q a b c d then {Fin.elim0} else ∅ : Finset (Fin 0 → ℕ)).card = if Q a b c d then 1 else 0
  split_ifs <;> simp

/-- Pairs with equal values of e, counted through the fibers of e. -/
lemma fiber_sq (n : ℕ) (e : ℕ → ℕ) (he : ∀ t, t ≤ n → e t ≤ n) :
    ∑ x ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1), (if e x = e d then 1 else 0 : ℕ) =
      ∑ δ ∈ Finset.range (n + 1), (∑ x ∈ Finset.range (n + 1), if e x = δ then 1 else 0 : ℕ) ^ 2 := by
  symm
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Finset.mem_range] at hx
  rw [Finset.sum_eq_single (e x)]
  · rw [if_pos rfl, one_mul]
    exact if_congr eq_comm rfl rfl
  · intro δ _ hδ
    rw [if_neg (fun h => hδ h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 (by have := he x (by omega); omega)) h

lemma sum_ind_eq (n t : ℕ) (P : Prop) [Decidable P] :
    ∑ a ∈ Finset.range (n + 1), (if P ∧ a = t then 1 else 0 : ℕ) = if P ∧ t ≤ n then 1 else 0 := by
  by_cases hP : P
  · simp [hP, Finset.sum_ite_eq', Finset.mem_range]
  · simp [hP]

lemma sum_ind_eq' (n t : ℕ) :
    ∑ a ∈ Finset.range (n + 1), (if a = t then 1 else 0 : ℕ) = if t ≤ n then 1 else 0 := by
  simp [Finset.sum_ite_eq', Finset.mem_range]

lemma sum_ind_le (n m : ℕ) (P : Prop) [Decidable P] (h : m ≤ n) :
    ∑ x ∈ Finset.range (n + 1), (if P ∧ x ≤ m then 1 else 0 : ℕ) = if P then m + 1 else 0 := by
  by_cases hP : P
  · simp only [hP, true_and, if_true]
    rw [Finset.sum_boole]
    have : (Finset.range (n + 1)).filter (· ≤ m) = Finset.range (m + 1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    simp [this]
  · simp [hP]

lemma sum_ind_lt (n m : ℕ) (h : m ≤ n) :
    ∑ δ ∈ Finset.range n, (if δ < m then 1 else 0 : ℕ) = m := by
  rw [Finset.sum_boole]
  have : (Finset.range n).filter (· < m) = Finset.range m := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [this]

lemma sum_ind_Icc (n l h : ℕ) (hh : h ≤ n) :
    ∑ x ∈ Finset.range (n + 1), (if l ≤ x ∧ x ≤ h then 1 else 0 : ℕ) = h + 1 - l := by
  rw [Finset.sum_boole]
  have : (Finset.range (n + 1)).filter (fun x => l ≤ x ∧ x ≤ h) = Finset.Icc l h := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  simp [this]

/-- A sum over pairs (b, c) of a function of (min b c, max b c). -/
lemma sum_pairs (n : ℕ) (F : ℕ → ℕ → ℕ) :
    ∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1), F (min b c) (max b c) =
      ∑ h ∈ Finset.range (n + 1), (F h h + 2 * ∑ l ∈ Finset.range h, F l h) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb : ∀ b ∈ Finset.range (n + 1),
        ∑ c ∈ Finset.range (n + 1 + 1), F (min b c) (max b c) =
          ∑ c ∈ Finset.range (n + 1), F (min b c) (max b c) + F b (n + 1) := by
      intro b hb
      rw [Finset.mem_range] at hb
      rw [Finset.sum_range_succ, min_eq_left (by omega), max_eq_right (by omega)]
    have hlast : ∑ c ∈ Finset.range (n + 1 + 1), F (min (n + 1) c) (max (n + 1) c) =
        ∑ c ∈ Finset.range (n + 1), F c (n + 1) + F (n + 1) (n + 1) := by
      rw [Finset.sum_range_succ, min_self, max_self]
      congr 1
      refine Finset.sum_congr rfl (fun c hc => ?_)
      rw [Finset.mem_range] at hc
      rw [min_eq_right (by omega), max_eq_left (by omega)]
    rw [Finset.sum_range_succ, Finset.sum_congr rfl hb, Finset.sum_add_distrib, ih, hlast,
      Finset.sum_range_succ (fun h => F h h + 2 * ∑ l ∈ Finset.range h, F l h) (n + 1)]
    ring

lemma odd_sq (m : ℕ) : ∑ j ∈ Finset.range m, (2 * j + 1) = m ^ 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The odd numbers 1, 3, ... over the h with δ ≤ h ≤ n - δ. -/
lemma odd_sum (n δ : ℕ) :
    ∑ h ∈ Finset.range (n + 1), (if δ ≤ h ∧ h + δ ≤ n then 2 * (h - δ) + 1 else 0) =
      (n + 1 - 2 * δ) ^ 2 := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range (n + 1)).filter (fun h => δ ≤ h ∧ h + δ ≤ n) =
      Finset.Ico δ (n + 1 - δ) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [odd_sq, show n + 1 - δ - δ = n + 1 - 2 * δ by omega]

/-- U n = Sum_{t < n} (n - 1 - 2t)^2, with truncated subtraction. -/
def U (n : ℕ) : ℕ := ∑ t ∈ Finset.range n, (n - 1 - 2 * t) ^ 2

lemma U_step (n : ℕ) : U (n + 2) = U n + (n + 1) ^ 2 := by
  unfold U
  rw [Finset.sum_range_succ', Finset.sum_range_succ]
  have e1 : n + 2 - 1 - 2 * (n + 1) = 0 := by omega
  have e2 : n + 2 - 1 - 2 * 0 = n + 1 := by omega
  rw [e1, e2, Finset.sum_congr rfl (fun t _ => by
    rw [show n + 2 - 1 - 2 * (t + 1) = n - 1 - 2 * t by omega])]
  ring

lemma U_eq : ∀ n : ℕ, (U n : ℚ) = ((n : ℚ) ^ 3 - n) / 6
  | 0 => by simp [U]
  | 1 => by simp [U]
  | n + 2 => by
    rw [U_step]
    push_cast
    rw [U_eq n]
    ring

end TripleCounts

/-! The condition says that the two triples have the same spread. Write lo = min b c and
hi = max b c for the middle pair; the spread of (t, b, c) is hi - lo plus the distance ex b c t
from t to [lo, hi]. The pairs (x, d) with equal distances are counted by the fibers of ex. -/

lemma good_iff (x : Fin 4 → ℕ) :
    good x ↔ spread (x 0) (x 1) (x 2) = spread (x 1) (x 2) (x 3) := by
  unfold good
  constructor
  · rintro ⟨s, hs, t, ht, h⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> omega
  · intro h
    exact ⟨1, by simp, -1, by simp, by rw [h]; ring⟩

/-- The distance from t to the interval between b and c. -/
def ex (b c t : ℕ) : ℕ := (t - max b c) + (min b c - t)

lemma spread_left (t b c : ℕ) : spread t b c = (max b c - min b c) + ex b c t := by
  unfold spread ex
  rcases le_total b c with h | h
  · rw [min_eq_left h, max_eq_right h]
    omega
  · rw [min_eq_right h, max_eq_left h]
    omega

lemma spread_right (b c t : ℕ) : spread b c t = (max b c - min b c) + ex b c t := by
  unfold spread ex
  omega

lemma spread_iff (x b c d : ℕ) : spread x b c = spread b c d ↔ ex b c x = ex b c d := by
  rw [spread_left, spread_right]
  omega

theorem a_sum (n : ℕ) :
    a n = ∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1), ∑ x ∈ Finset.range (n + 1),
      ∑ d ∈ Finset.range (n + 1), (if ex b c x = ex b c d then 1 else 0 : ℕ) := by
  unfold a
  rw [card_fin_eq_piFinset good, Finset.filter_congr (fun x _ => good_iff x),
    card4 (Finset.range (n + 1)) (fun x b c d => spread x b c = spread b c d), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ =>
    Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun d _ => ?_)))
  exact if_congr (spread_iff x b c d) rfl rfl

/-- The part of the count for the middle pair (b, c) that does not depend on n. -/
def Wf (b c : ℕ) : ℕ := (max b c - min b c) ^ 2 + (max b c - min b c) + 1

/-- The pairs (x, d) for the middle pair (b, c): (hi - lo + 1)^2 inside, lo + (n - hi) with x = d
outside, and 2 min(lo, n - hi) reflected pairs. -/
theorem inner (n b c : ℕ) (hb : b ≤ n) (hc : c ≤ n) :
    ∑ x ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n + 1), (if ex b c x = ex b c d then 1 else 0 : ℕ) =
      Wf b c + n + 2 * min (min b c) (n - max b c) := by
  rw [fiber_sq n (ex b c) (fun t ht => by unfold ex; omega), Finset.sum_range_succ']
  have h0 : ∑ x ∈ Finset.range (n + 1), (if ex b c x = 0 then 1 else 0 : ℕ) =
      max b c - min b c + 1 := by
    rw [Finset.sum_congr rfl (fun x _ => if_congr
      (show ex b c x = 0 ↔ min b c ≤ x ∧ x ≤ max b c by unfold ex; omega) rfl rfl),
      sum_ind_Icc n _ _ (by omega)]
    omega
  have hδ : ∀ δ ∈ Finset.range n,
      ∑ x ∈ Finset.range (n + 1), (if ex b c x = δ + 1 then 1 else 0 : ℕ) =
        (if δ < min b c then 1 else 0) + (if δ < n - max b c then 1 else 0) := by
    intro δ _
    have hp : ∀ x, (if ex b c x = δ + 1 then 1 else 0 : ℕ) =
        (if δ < min b c ∧ x = min b c - (δ + 1) then 1 else 0) +
          (if x = max b c + (δ + 1) then 1 else 0) := by
      intro x
      unfold ex
      split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun x _ => hp x), Finset.sum_add_distrib, sum_ind_eq, sum_ind_eq']
    split_ifs <;> omega
  have hδ2 : ∑ δ ∈ Finset.range n,
      (∑ x ∈ Finset.range (n + 1), (if ex b c x = δ + 1 then 1 else 0 : ℕ)) ^ 2 =
        ∑ δ ∈ Finset.range n,
          ((if δ < min b c then 1 else 0) + (if δ < n - max b c then 1 else 0)) ^ 2 :=
    Finset.sum_congr rfl (fun δ hδ' => by rw [hδ δ hδ'])
  rw [hδ2, h0]
  have hsq : ∀ δ, ((if δ < min b c then 1 else 0) + (if δ < n - max b c then 1 else 0) : ℕ) ^ 2 =
      (if δ < min b c then 1 else 0) + (if δ < n - max b c then 1 else 0) +
        2 * (if δ < min (min b c) (n - max b c) then 1 else 0) := by
    intro δ
    split_ifs <;> omega
  simp only [hsq, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_ind_lt n _ (by omega), sum_ind_lt n _ (by omega), sum_ind_lt n _ (by omega)]
  unfold Wf
  obtain ⟨w, hw⟩ : ∃ w, max b c - min b c = w := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, n - max b c = r := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, min b c = l := ⟨_, rfl⟩
  have hn : n = l + w + r := by omega
  rw [hw, hr, hl]
  subst hn
  ring

/-- The reflected pairs, summed over the middle pair, by layers t < min(lo, n - hi). -/
lemma min_sum (n : ℕ) :
    ∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1), min (min b c) (n - max b c) = U n := by
  have hp : ∀ b ∈ Finset.range (n + 1), ∀ c ∈ Finset.range (n + 1), min (min b c) (n - max b c) =
      ∑ t ∈ Finset.range n,
        (if t < b ∧ b + t < n then 1 else 0) * (if t < c ∧ c + t < n then 1 else 0) := by
    intro b hb c hc
    simp only [Finset.mem_range] at hb hc
    rw [← sum_ind_lt n (min (min b c) (n - max b c)) (by omega)]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    split_ifs <;> omega
  have hf : ∀ t ∈ Finset.range n,
      ∑ b ∈ Finset.range (n + 1), (if t < b ∧ b + t < n then 1 else 0 : ℕ) = n - 1 - 2 * t := by
    intro t _
    rw [Finset.sum_boole]
    have : (Finset.range (n + 1)).filter (fun b => t < b ∧ b + t < n) = Finset.Ioo t (n - t) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
      omega
    rw [this, Nat.card_Ioo, Nat.cast_id]
    omega
  rw [Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun c hc => hp b hb c hc)),
    Finset.sum_congr rfl (fun b _ => Finset.sum_comm), Finset.sum_comm]
  unfold U
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [← Finset.sum_mul_sum, hf t ht, sq]

lemma W_col (n : ℕ) :
    ∑ b ∈ Finset.range (n + 1), (Wf b (n + 1) : ℚ) = 3 + 14 / 3 * n + 2 * n ^ 2 + 1 / 3 * n ^ 3 := by
  induction n with
  | zero => simp [Wf]; norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have hs : ∀ b ∈ Finset.range (n + 1), (Wf (b + 1) (n + 1 + 1) : ℚ) = Wf b (n + 1) := by
      intro b hb
      rw [Finset.mem_range] at hb
      unfold Wf
      rw [show max (b + 1) (n + 1 + 1) - min (b + 1) (n + 1 + 1) = max b (n + 1) - min b (n + 1) by
        omega]
    rw [Finset.sum_congr rfl hs, ih]
    have h0 : Wf 0 (n + 1 + 1) = (n + 2) ^ 2 + (n + 2) + 1 := by
      unfold Wf
      rw [show max 0 (n + 1 + 1) - min 0 (n + 1 + 1) = n + 2 by omega]
    rw [h0]
    push_cast
    ring

lemma Wf_comm (b c : ℕ) : Wf b c = Wf c b := by
  unfold Wf
  rw [max_comm, min_comm]

lemma W_sum (n : ℕ) :
    ∑ b ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1), (Wf b c : ℚ) =
      1 + 3 * n + 17 / 6 * n ^ 2 + n ^ 3 + 1 / 6 * n ^ 4 := by
  induction n with
  | zero => simp [Wf]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun b _ => Finset.sum_range_succ _ _),
      Finset.sum_add_distrib, ih, W_col n, Finset.sum_range_succ,
      Finset.sum_congr rfl (fun c _ => by rw [Wf_comm]), W_col n]
    have h1 : Wf (n + 1) (n + 1) = 1 := by unfold Wf; simp
    rw [h1]
    push_cast
    ring

/-- Hardin's polynomial, for every n. -/
theorem poly (n : ℕ) :
    (a n : ℚ) = 1 / 6 * (n : ℚ) ^ 4 + 7 / 3 * (n : ℚ) ^ 3 + 29 / 6 * (n : ℚ) ^ 2 + 11 / 3 * (n : ℚ) + 1 := by
  rw [a_sum, Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun c hc =>
    inner n b c (by rw [Finset.mem_range] at hb; omega) (by rw [Finset.mem_range] at hc; omega)))]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum]
  rw [min_sum n]
  push_cast
  rw [W_sum n, U_eq n]
  ring

lemma val (n v : ℕ) (h : 1 / 6 * (n : ℚ) ^ 4 + 7 / 3 * (n : ℚ) ^ 3 + 29 / 6 * (n : ℚ) ^ 2
    + 11 / 3 * (n : ℚ) + 1 = v) : a n = v := by
  have e := poly n
  rw [h] at e
  exact_mod_cast e

/-- The values a(0..5). -/
theorem small : a 0 = 1 ∧ a 1 = 12 ∧ a 2 = 49 ∧ a 3 = 132 ∧ a 4 = 285 ∧ a 5 = 536 :=
  ⟨val 0 1 (by norm_num), val 1 12 (by norm_num), val 2 49 (by norm_num),
    val 3 132 (by norm_num), val 4 285 (by norm_num), val 5 536 (by norm_num)⟩

/-- Barker's recurrence, for n > 5. -/
theorem recurrence (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
  simp only [show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega, show q + 6 - 3 = q
    + 3 by omega, show q + 6 - 4 = q + 2 by omega, show q + 6 - 5 = q + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [poly (q + 6), poly (q + 5), poly (q + 4), poly (q + 3), poly (q + 2), poly (q + 1)]
  push_cast
  ring

/-- Barker's g.f., as A(x) (1 - x)^5 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
    X * (12 - 11 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 5 =
      A - C 5 * (A * X ^ 1) + C 10 * (A * X ^ 2) - C 10 * (A * X ^ 3) + C 5 * (A * X ^ 4)
        - A * X ^ 5 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (12 - 11 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) : ℤ⟦X⟧) =
      X ^ 1 * C 12 - X ^ 2 * C 11 + X ^ 3 * C 7 - X ^ 4 * C 5 + X ^ 5 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := small
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 6 := ⟨n - 6, by omega⟩
    have h := recurrence (q + 6) (by omega)
    simp only [show q + 6 - 1 = q + 5 by omega, show q + 6 - 2 = q + 4 by omega, show q + 6
      - 3 = q + 3 by omega, show q + 6 - 4 = q + 2 by omega, show q + 6 - 5 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega, show ¬ q + 4 = 0 by omega,
      show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q + 1 = 0 by omega, show 1 ≤ q
      + 6 by omega, show 2 ≤ q + 6 by omega, show 3 ≤ q + 6 by omega, show 4 ≤ q + 6 by omega,
      show 5 ≤ q + 6 by omega, show ¬ q + 6 = 1 by omega, show ¬ q + 6 = 2 by omega, show ¬ q
      + 6 = 3 by omega, show ¬ q + 6 = 4 by omega, show ¬ q + 6 = 5 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's terms a(1..36). -/
theorem controls : a 1 = 12 ∧ a 2 = 49 ∧ a 3 = 132 ∧ a 4 = 285 ∧ a 5 = 536 ∧ a 6 = 917 ∧
    a 7 = 1464 ∧ a 8 = 2217 ∧ a 9 = 3220 ∧ a 10 = 4521 ∧ a 11 = 6172 ∧ a 12 = 8229 ∧
    a 13 = 10752 ∧ a 14 = 13805 ∧ a 15 = 17456 ∧ a 16 = 21777 ∧ a 17 = 26844 ∧ a 18 = 32737 ∧
    a 19 = 39540 ∧ a 20 = 47341 ∧ a 21 = 56232 ∧ a 22 = 66309 ∧ a 23 = 77672 ∧ a 24 = 90425 ∧
    a 25 = 104676 ∧ a 26 = 120537 ∧ a 27 = 138124 ∧ a 28 = 157557 ∧ a 29 = 178960 ∧
    a 30 = 202461 ∧ a 31 = 228192 ∧ a 32 = 256289 ∧ a 33 = 286892 ∧ a 34 = 320145 ∧
    a 35 = 356196 ∧ a 36 = 395197 :=
  ⟨val 1 12 (by norm_num), val 2 49 (by norm_num), val 3 132 (by norm_num),
    val 4 285 (by norm_num), val 5 536 (by norm_num), val 6 917 (by norm_num),
    val 7 1464 (by norm_num), val 8 2217 (by norm_num), val 9 3220 (by norm_num),
    val 10 4521 (by norm_num), val 11 6172 (by norm_num), val 12 8229 (by norm_num),
    val 13 10752 (by norm_num), val 14 13805 (by norm_num), val 15 17456 (by norm_num),
    val 16 21777 (by norm_num), val 17 26844 (by norm_num), val 18 32737 (by norm_num),
    val 19 39540 (by norm_num), val 20 47341 (by norm_num), val 21 56232 (by norm_num),
    val 22 66309 (by norm_num), val 23 77672 (by norm_num), val 24 90425 (by norm_num),
    val 25 104676 (by norm_num), val 26 120537 (by norm_num), val 27 138124 (by norm_num),
    val 28 157557 (by norm_num), val 29 178960 (by norm_num), val 30 202461 (by norm_num),
    val 31 228192 (by norm_num), val 32 256289 (by norm_num), val 33 286892 (by norm_num),
    val 34 320145 (by norm_num), val 35 356196 (by norm_num), val 36 395197 (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (12 - 11 * X + 7 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a252178

theorem OMA.solution : type_of% @OMA.S_oeis_a252178.main :=
  OMA.S_oeis_a252178.conjecture
