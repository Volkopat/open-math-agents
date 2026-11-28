import OMAStatements.S_oeis_a002293
import Mathlib

namespace OMA.P002293
open OMA.S_oeis_a002293 Finset

/-- `B L r` counts avoiding words on `{b^(r-1), (b+1)^3, ..., (b+L)^3}`. -/
def B : ℕ → ℕ → ℕ
  | 0, _ => 1
  | L+1, r => ∑ t ∈ range r, B L (t + 4)

lemma Bs (L r : ℕ) : B (L+1) (r+1) = B (L+1) r + B L (r+4) := by simp [B, sum_range_succ]

lemma Bc (m : ℕ) : ∀ r s, ∑ k ∈ range (m + 1), B k r * B (m - k) s = B m (r + s) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro r s
    induction r with
    | zero => cases m <;> simp [B, sum_range_succ']
    | succ r ihr =>
      cases m with
      | zero => simp [B]
      | succ m =>
        rw [sum_range_succ'] at ihr ⊢
        have := ih m (by omega) (r + 4) s
        simp only [Bs, add_mul, sum_add_distrib, Nat.add_sub_add_right, Nat.sub_zero,
          show ∀ r, B 0 r = 1 from fun _ => rfl, one_mul] at ihr ⊢
        rw [show r + 1 + s = r + s + 1 by ring, Bs, show r + s + 4 = r + 4 + s by ring]
        omega

lemma Bf (L : ℕ) : ∀ r, (4 * L + r) * B L r = r * (4 * L + r).choose L := by
  induction L with
  | zero => simp [B]
  | succ L ihL =>
    intro r
    induction r with
    | zero => simp [B]
    | succ r ihr =>
      have hZ := ihL (r + 4)
      have h1 := Nat.choose_succ_right_eq (4 * L + 4 + r) L
      have h2 := Nat.add_one_mul_choose_eq (4 * L + 4 + r) L
      rw [show 4 * L + 4 + r - L = 3 * L + 4 + r by omega] at h1
      rw [show 4 * L + (r + 4) = 4 * L + 4 + r by ring] at hZ
      rw [show 4 * (L + 1) + r = 4 * L + 4 + r by ring] at ihr
      rw [Bs, show 4 * (L + 1) + (r + 1) = 4 * L + 4 + r + 1 by ring]
      apply Nat.eq_of_mul_eq_mul_left (show 0 < (4 * L + 4 + r) * (L + 1) by positivity)
      zify at ihr hZ h1 h2 ⊢
      linear_combination (4 * (L:ℤ) + 5 + r) * (L + 1) * (ihr + hZ) + (4 * (L:ℤ) + 5 + r) * r * h1
        + (4 * (L:ℤ) + 4 + r) * (r + 1) * h2

lemma Bo (n : ℕ) : B n 1 = (4 * n).choose n / (3 * n + 1) := by
  have h := Bf n 1
  have h2 := Nat.choose_mul_succ_eq (4 * n) n
  rw [show 4 * n + 1 - n = 3 * n + 1 by omega] at h2
  refine (Nat.div_eq_of_eq_mul_left (by omega)
    (Nat.eq_of_mul_eq_mul_left (show 0 < 4 * n + 1 by omega) ?_)).symm
  zify at h h2 ⊢
  linear_combination h2 - (3 * (n:ℤ) + 1) * h

/-- No sublist `[x, y, z]` with `z < x ≤ y`. -/
def P (l : List ℕ) : Prop := ∀ x y z, [x, y, z].Sublist l → ¬ (z < x ∧ x ≤ y)

lemma ps {l l' : List ℕ} (h : P l') (s : l.Sublist l') : P l := fun x y z s' => h x y z (s'.trans s)

lemma fl {a : ℕ} {D X : List ℕ} (hD : ∀ x ∈ D, x < a) (hX : ∀ x ∈ X, ¬ x < a) :
    (D ++ X).filter (· < a) = D ∧ (D ++ X).filter (fun x => ¬ x < a) = X := by
  simp only [List.filter_append, List.filter_eq_self.2 fun x h => decide_eq_true (hD x h),
    List.filter_eq_nil_iff.2 fun x h => mt of_decide_eq_true (hX x h),
    List.filter_eq_nil_iff.2 fun x h => mt of_decide_eq_true (not_not_intro (hD x h)),
    List.filter_eq_self.2 fun x h => decide_eq_true (hX x h)]
  simp

lemma pa (a : ℕ) (D X : List ℕ) (hD : ∀ x ∈ D, x < a) (hX : ∀ x ∈ X, ¬ x < a) :
    P (a :: (D ++ X)) ↔ P D ∧ P X := by
  refine ⟨fun h => ⟨ps h ((List.sublist_append_left D X).cons a), ps h ((List.sublist_append_right D X).cons a)⟩, ?_⟩
  rintro ⟨h1, h2⟩ x y z s ⟨hzx, hxy⟩
  rcases List.sublist_cons_iff.1 s with s | ⟨r, e, s⟩
  · obtain ⟨l1, l2, e, s1, s2⟩ := List.sublist_append_iff.1 s
    rcases l1 with _ | ⟨u, _ | ⟨v, _ | ⟨w, _ | _⟩⟩⟩ <;> simp at e
    · exact h2 x y z (e ▸ s2) ⟨hzx, hxy⟩
    · have := hD x (s1.subset (by simp [e.1])); have := hX z (s2.subset (by simp [← e.2])); omega
    · have := hD x (s1.subset (by simp [e.1])); have := hX z (s2.subset (by simp [← e.2.2])); omega
    · exact h1 x y z (by simpa [e.1, e.2.1, e.2.2.1] using s1) ⟨hzx, hxy⟩
  · simp at e
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨l1, l2, e, s1, s2⟩ := List.sublist_append_iff.1 s
    rcases l1 with _ | ⟨u, _ | ⟨v, _ | _⟩⟩ <;> simp at e
    · exact hX z (s2.subset (by simp [← e])) hzx
    · have := hD y (s1.subset (by simp [e.1])); omega
    · have := hD y (s1.subset (by simp [e.1])); omega

lemma sp (a : ℕ) : ∀ t : List ℕ, P (a :: t) → t = t.filter (· < a) ++ t.filter (fun x => ¬ x < a)
  | [] => fun _ => rfl
  | c :: t => fun h => by
    by_cases hc : c < a
    · simpa [List.filter_cons, hc] using sp a t (ps h ((List.sublist_cons_self c t).cons_cons a))
    · have hall : ∀ z ∈ c :: t, ¬ z < a := by
        simp only [List.mem_cons, forall_eq_or_imp]
        exact ⟨hc, fun z hz hz' => h a c z (by simp [hz]) ⟨hz', by omega⟩⟩
      obtain ⟨e1, e2⟩ := fl (a := a) (D := []) (X := c :: t) (by simp) hall
      rw [List.nil_append] at e1 e2
      rw [e1, e2]; rfl

lemma po {m : ℕ} (g : Fin m → ℕ) :
    P (List.ofFn g) ↔ ∀ i j k, i < j → j < k → ¬ (g k < g i ∧ g i ≤ g j) := by
  simp only [P, List.ofFn_eq_map, List.sublist_map_iff]
  refine ⟨fun h i j k h1 h2 => h _ _ _ ⟨[i, j, k], List.sublist_of_subperm_of_pairwise (r := (· ≤ ·))
    (List.Nodup.subperm (by simp [h1.ne, h2.ne, (h1.trans h2).ne]) (by simp))
    (by simp [h1.le, h2.le, (h1.trans h2).le]) (List.pairwise_le_finRange m), rfl⟩, ?_⟩
  rintro h x y z ⟨l, s, e⟩
  rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨k, _ | _⟩⟩⟩ <;> simp at e
  have := (List.pairwise_lt_finRange m).sublist s
  simp at this
  rw [e.1, e.2.1, e.2.2]
  exact h i j k this.1.1 this.2

lemma mL {S : Multiset ℕ} {l : List ℕ} : l ∈ (Multiset.lists S).toFinset ↔ S = l := by simp

open Classical in
/-- Number of avoiding arrangements of the multiset `S`. -/
noncomputable def N (S : Multiset ℕ) : ℕ := ((Multiset.lists S).toFinset.filter P).card

lemma N0 : N 0 = 1 := by
  rw [N, card_eq_one]
  refine ⟨[], Finset.ext fun l => ?_⟩
  simp only [mem_filter, mL, mem_singleton]
  exact ⟨fun h => (Multiset.coe_eq_zero _).1 h.1.symm, by rintro rfl; exact ⟨rfl, fun x y z s => by simp at s⟩⟩

lemma mf {S : Multiset ℕ} {D : List ℕ} {p : ℕ → Prop} [DecidablePred p] (e : S.filter p = D) (x : ℕ)
    (hx : x ∈ D) : p x := by
  rw [← Multiset.mem_coe, ← e, Multiset.mem_filter] at hx; exact hx.2

/-- First-letter recursion: the word is `(b + k) :: (D ++ X)`, `D` below `b + k`, `X` at least `b + k`. -/
lemma Nr (S : Multiset ℕ) (b L : ℕ) (hS : S ≠ 0) (hb : ∀ x ∈ S, b ≤ x ∧ x ≤ b + L) :
    N S = ∑ k ∈ range (L + 1), if b + k ∈ S then
      N ((S.erase (b + k)).filter (· < b + k)) * N ((S.erase (b + k)).filter (fun x => ¬ x < b + k)) else 0 := by
  rw [← sum_filter]
  simp only [N, ← card_product]
  rw [← card_sigma]
  symm
  apply card_bij (fun p _ => (b + p.1) :: (p.2.1 ++ p.2.2))
  · rintro ⟨k, D, X⟩ h
    simp only [mem_sigma, mem_filter, mem_range, mem_product, mL] at h ⊢
    obtain ⟨⟨-, hm⟩, ⟨e1, p1⟩, e2, p2⟩ := h
    refine ⟨?_, (pa _ _ _ (mf e1) (mf e2)).2 ⟨p1, p2⟩⟩
    rw [← Multiset.cons_coe, ← Multiset.coe_add, ← e1, ← e2, Multiset.filter_add_not, Multiset.cons_erase hm]
  · rintro ⟨k, D, X⟩ h ⟨k', D', X'⟩ h' e
    simp only [mem_sigma, mem_filter, mem_range, mem_product, mL] at h h'
    simp only [List.cons.injEq] at e
    obtain ⟨e0, e⟩ := e
    obtain rfl : k = k' := by omega
    obtain ⟨a1, a2⟩ := fl (mf h.2.1.1) (mf h.2.2.1)
    obtain ⟨a3, a4⟩ := fl (mf h'.2.1.1) (mf h'.2.2.1)
    rw [e] at a1 a2
    obtain rfl := a1.symm.trans a3
    obtain rfl := a2.symm.trans a4
    rfl
  · intro l hl
    simp only [mem_filter, mL] at hl
    obtain ⟨e, p⟩ := hl
    rcases l with _ | ⟨a, t⟩
    · exact absurd (e.trans Multiset.coe_nil) hS
    · have ha : a ∈ S := by rw [e]; simp
      obtain ⟨h1, h2⟩ := hb a ha
      have hS' : S.erase a = t := by rw [e]; simp
      refine ⟨⟨a - b, t.filter (· < a), t.filter (fun x => ¬ x < a)⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_filter, mem_range, mem_product, mL, Nat.add_sub_cancel' h1, hS',
          Multiset.filter_coe]
        exact ⟨⟨by omega, ha⟩, ⟨trivial, ps p ((List.filter_sublist (l := t)).cons a)⟩, trivial,
          ps p ((List.filter_sublist (l := t)).cons a)⟩
      · simp only [Nat.add_sub_cancel' h1]; exact congrArg _ (sp a t p).symm

/-- The letter `b` with multiplicity `β`, then `b + 1, ..., b + L` three times each. -/
def F : ℕ → ℕ → ℕ → Multiset ℕ
  | b, β, 0 => Multiset.replicate β b
  | b, β, L + 1 => Multiset.replicate β b + F (b + 1) 3 L

lemma cF (v : ℕ) : ∀ L b β, (F b β L).count v = if v = b then β else if b < v ∧ v ≤ b + L then 3 else 0
  | 0, b, β => by simp only [F, Multiset.count_replicate]; split_ifs <;> omega
  | L + 1, b, β => by simp only [F, Multiset.count_add, Multiset.count_replicate, cF v L]; split_ifs <;> omega

lemma kF : ∀ L b β, Multiset.card (F b β L) = β + 3 * L
  | 0, b, β => by simp [F]
  | L + 1, b, β => by simp [F, kF L]; ring

lemma mF {b β L v : ℕ} : v ∈ F b β L ↔ (v = b ∧ 0 < β) ∨ (b < v ∧ v ≤ b + L) := by
  rw [← Multiset.count_pos, cF]; split_ifs <;> omega

lemma fA (b β L k : ℕ) (hk : k < L) :
    ((F b β L).erase (b + (k + 1))).filter (· < b + (k + 1)) = F b β k ∧
    ((F b β L).erase (b + (k + 1))).filter (fun x => ¬ x < b + (k + 1)) = F (b + (k + 1)) 2 (L - 1 - k) := by
  constructor <;> ext v <;> rcases eq_or_ne v (b + (k + 1)) with rfl | _ <;>
    simp [Multiset.count_filter, Multiset.count_erase_self, Multiset.count_erase_of_ne, cF, *] <;> split_ifs <;> omega

lemma fC (b β L : ℕ) :
    ((F b (β + 1) L).erase b).filter (· < b) = 0 ∧ ((F b (β + 1) L).erase b).filter (fun x => ¬ x < b) = F b β L := by
  constructor <;> ext v <;> rcases eq_or_ne v b with rfl | _ <;>
    simp [Multiset.count_filter, Multiset.count_erase_self, Multiset.count_erase_of_ne, cF, *] <;> omega

lemma fm (L : ℕ) : ∀ b β, N (F b β L) = B L (β + 1) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
  intro b β
  induction β with
  | zero =>
    rcases L with _ | L
    · simp [F, N0, B]
    · simp only [F, Multiset.replicate_zero, zero_add]; rw [ih L (by omega)]; simp [B]
  | succ β ihβ =>
    rw [Nr (F b (β + 1) L) b L (Multiset.card_pos.1 (by rw [kF]; omega))
      (fun x hx => by rcases mF.1 hx with h | h <;> omega), sum_range_succ', add_zero,
      if_pos (mF.2 (Or.inl ⟨rfl, by omega⟩)), (fC b β L).1, (fC b β L).2, N0, ihβ, one_mul,
      sum_congr rfl (g := fun k => B k (β + 1 + 1) * B (L - 1 - k) (2 + 1)) fun k hk => by
        have hk' : k < L := by simpa using hk
        rw [if_pos (mF.2 (Or.inr ⟨by omega, by omega⟩)), (fA b (β + 1) L k hk').1, (fA b (β + 1) L k hk').2,
          ih k hk', ih _ (by omega)]]
    rcases L with _ | L
    · simp [B]
    · have := Bc L (β + 1 + 1) (2 + 1)
      rw [show β + 1 + 1 + (2 + 1) = β + 1 + 4 by ring] at this
      rw [Bs L (β + 1), ← this]
      simp only [Nat.add_sub_cancel]
      ring

lemma cn {m : ℕ} (g : Fin m → ℕ) (a : ℕ) :
    Multiset.count a ↑(List.ofFn g) = (univ.filter fun i => a = g i).card := by
  rw [← Fin.univ_val_map, Multiset.count_map]; rfl

/-- A word is counted iff its shifted list has content `{1^3, ..., n^3}` and avoids the pattern. -/
lemma ky {n : ℕ} (w : Fin (3 * n) → Fin n) :
    IsUniformAvoidingWord w ↔ F 0 0 n = ↑(List.ofFn fun i => (w i : ℕ) + 1) ∧
      P (List.ofFn fun i => (w i : ℕ) + 1) := by
  rw [po, IsUniformAvoidingWord, Multiset.ext]
  refine and_congr ⟨fun h a => ?_, fun h c => ?_⟩
    (by simp only [Fin.lt_def, Fin.le_def, add_lt_add_iff_right, add_le_add_iff_right])
  · rw [cF, cn]
    split_ifs with h1 h2
    · symm; rw [card_eq_zero, filter_eq_empty_iff]; intro i _; omega
    · exact (h ⟨a - 1, by omega⟩).symm.trans
        (congrArg _ (filter_congr fun i _ => by simp only [Fin.ext_iff]; omega))
    · symm; rw [card_eq_zero, filter_eq_empty_iff]; intro i _; have := (w i).isLt; omega
  · have := h (c + 1)
    have hc := c.isLt
    rw [cF, cn, if_neg (show ¬ ((c : ℕ) + 1 = 0) by omega),
      if_pos (show 0 < (c : ℕ) + 1 ∧ (c : ℕ) + 1 ≤ 0 + n by omega)] at this
    exact (congrArg _ (filter_congr fun i _ => by simp only [Fin.ext_iff]; omega)).trans this.symm

theorem sol : type_of% @OMA.S_oeis_a002293.main := by
  intro n; classical
  rw [← Bo, show B n 1 = N (F 0 0 n) from (fm n 0 0).symm, N, ← Nat.card_eq_finsetCard]
  refine Nat.card_eq_of_bijective (fun w => ⟨_, mem_filter.2
    ⟨mL.2 ((ky w.1).1 w.2).1, ((ky w.1).1 w.2).2⟩⟩)
    ⟨fun w w' e => ?_, fun l => ?_⟩
  · exact Subtype.ext (by simpa [funext_iff, Fin.ext_iff] using e)
  · obtain ⟨l, hl⟩ := l
    have hl' := hl
    rw [mem_filter, mL] at hl'
    have hlen : l.length = 3 * n := by rw [← Multiset.coe_card, ← hl'.1, kF]; ring
    have hv : ∀ x ∈ l, 0 < x ∧ x ≤ n := fun x hx => by
      have : x ∈ F 0 0 n := by rw [hl'.1]; exact Multiset.mem_coe.2 hx
      have := mF.1 this; omega
    let w : Fin (3 * n) → Fin n := fun i =>
      ⟨l[i.1]'(by omega) - 1, by have := hv _ (List.getElem_mem (by omega : i.1 < l.length)); omega⟩
    have hw : List.ofFn (fun i => (w i : ℕ) + 1) = l := List.ext_getElem (by simp [hlen]) fun i h1 h2 => by
      simp [w]; have := hv _ (List.getElem_mem h2); omega
    refine ⟨⟨w, (ky w).2 ?_⟩, Subtype.ext hw⟩
    rw [hw]; exact hl'

end OMA.P002293

theorem OMA.solution : type_of% @OMA.S_oeis_a002293.main := OMA.P002293.sol
