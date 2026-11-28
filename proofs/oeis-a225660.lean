import OMAStatements.S_oeis_a225660
import Mathlib

namespace OMA.A225660Proof

open OMA.S_oeis_a225660

theorem foldr_max_le (s : List ℕ) (b : ℕ) (h : ∀ x ∈ s, x ≤ b) : s.foldr max 0 ≤ b := by
  induction s with
  | nil => simp
  | cons y s ih =>
    rw [List.foldr_cons]
    exact max_le (h y (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem le_foldr_max (s : List ℕ) (x : ℕ) (h : x ∈ s) : x ≤ s.foldr max 0 := by
  induction s with
  | nil => simp at h
  | cons y s ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp h with h' | h'
    · rw [h']; exact le_max_left _ _
    · exact le_trans (ih h') (le_max_right _ _)

theorem foldr_max_eq (s : List ℕ) (M : ℕ) (h1 : ∀ x ∈ s, x ≤ M) (h2 : M ∈ s) :
    s.foldr max 0 = M :=
  le_antisymm (foldr_max_le s M h1) (le_foldr_max s M h2)

/-- `seg g s L = [g s, g (s+1), ..., g (s+L-1)]`. -/
def seg (g : ℕ → ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | s, L + 1 => g s :: seg g (s + 1) L

theorem seg_succ_right (g : ℕ → ℕ) (s L : ℕ) : seg g s (L + 1) = seg g s L ++ [g (s + L)] := by
  induction L generalizing s with
  | zero => rfl
  | succ L ih =>
    show g s :: seg g (s + 1) (L + 1) = (g s :: seg g (s + 1) L) ++ [g (s + (L + 1))]
    rw [ih (s + 1), show s + 1 + L = s + (L + 1) by omega]
    rfl

theorem seg_add (g : ℕ → ℕ) (s a b : ℕ) : seg g s (a + b) = seg g s a ++ seg g (s + a) b := by
  induction a generalizing s with
  | zero => simp [seg]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    show g s :: seg g (s + 1) (a + b) = (g s :: seg g (s + 1) a) ++ seg g (s + (a + 1)) b
    rw [ih (s + 1), show s + 1 + a = s + (a + 1) by omega]
    rfl

theorem seg_split3 (g : ℕ → ℕ) (s a b : ℕ) :
    seg g s (a + 1 + b) = seg g s a ++ g (s + a) :: seg g (s + a + 1) b := by
  rw [show a + 1 + b = a + (1 + b) by omega, seg_add, seg_add g (s + a) 1 b] <;> rfl

theorem seg_const (g : ℕ → ℕ) (c s L : ℕ) (h : ∀ i, s ≤ i → i < s + L → g i = c) :
    seg g s L = List.replicate L c := by
  induction L generalizing s with
  | zero => rfl
  | succ L ih =>
    show g s :: seg g (s + 1) L = c :: List.replicate L c
    rw [h s (le_refl s) (by omega), ih (s + 1) (fun i h1 h2 => h i (by omega) (by omega))]

theorem seg_last (g : ℕ → ℕ) (s r : ℕ) (h : ∀ i, s ≤ i → i < s + r → g i = 0) :
    seg g s (r + 1) = List.replicate r 0 ++ [g (s + r)] := by
  rw [seg_succ_right, seg_const g 0 s r h]

theorem seg_head2 (g : ℕ → ℕ) (p : ℕ) (h : ∀ i, 2 ≤ i → i < 2 + p → g i = 0) :
    seg g 0 (p + 2 + 1) = g 0 :: g 1 :: (List.replicate p 0 ++ [g (2 + p)]) := by
  show g 0 :: g (0 + 1) :: seg g (0 + 1 + 1) (p + 1) = g 0 :: g 1 :: (List.replicate p 0 ++ [g (2 + p)])
  rw [seg_last g (0 + 1 + 1) p (fun i h1 h2 => h i (by omega) (by omega))]

theorem seg_two (g : ℕ → ℕ) : seg g 0 (1 + 1) = [g 0, g 1] := rfl

theorem seg_three (g : ℕ → ℕ) : seg g 0 (2 + 1) = [g 0, g 1, g 2] := rfl

theorem map_range_seg (g : ℕ → ℕ) (n : ℕ) : (List.range n).map g = seg g 0 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, ih, seg_succ_right]
    simp

theorem F_of_max (s : List ℕ) (M : ℕ) (h1 : ∀ x ∈ s, x ≤ M) (h2 : M ∈ s) :
    F s = seg (fun i => s.count i) 0 (M + 1) := by
  rw [← foldr_max_eq s M h1 h2]
  exact map_range_seg _ _

theorem F_perm (s t : List ℕ) (h : s.Perm t) : F s = F t := by
  have hm : s.foldr max 0 = t.foldr max 0 :=
    le_antisymm (foldr_max_le _ _ (fun x hx => le_foldr_max _ _ (h.subset hx)))
      (foldr_max_le _ _ (fun x hx => le_foldr_max _ _ (h.symm.subset hx)))
  show (List.range (s.foldr max 0 + 1)).map (fun i => s.count i) =
    (List.range (t.foldr max 0 + 1)).map (fun i => t.count i)
  rw [hm]
  congr 1
  funext i
  exact h.count_eq i

theorem F_swap (p q : ℕ) : F [p, q] = F [q, p] := F_perm _ _ (List.Perm.swap q p [])

theorem cnt_cons (x i : ℕ) (l : List ℕ) : (x :: l).count i = l.count i + if x = i then 1 else 0 := by
  by_cases h : x = i
  · subst h; simp
  · simp [h]

theorem cnt_rep (n c i : ℕ) : (List.replicate n c).count i = if c = i then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    show (c :: List.replicate n c).count i = _
    rw [cnt_cons, ih]
    split_ifs <;> omega

/-! The cycle set: the 2-cycle and the 6-cycle. -/

def Z : List (List ℕ) := [[1, 2], [0, 1, 1], [2, 2], [0, 0, 2], [2, 0, 1], [1, 1, 1], [0, 3], [1, 0, 0, 1]]

theorem Z_closed : ∀ v ∈ Z, F v ∈ Z := by decide

theorem Z_per : ∀ v ∈ Z, F^[6] v = v := by decide

theorem Z_len : ∀ v ∈ Z, v.length ≤ 4 := by decide

theorem Z_ent : ∀ v ∈ Z, ∀ x ∈ v, x ≤ 3 := by decide

theorem notZ_len (v : List ℕ) (h : 5 ≤ v.length) : v ∉ Z := fun hv => by
  have := Z_len v hv
  omega

theorem notZ_ent (v : List ℕ) (x : ℕ) (hx : x ∈ v) (h : 4 ≤ x) : v ∉ Z := fun hv => by
  have := Z_ent v hv x hx
  omega

theorem Z_iter (d : ℕ) : ∀ W ∈ Z, F^[d] W ∈ Z := by
  induction d with
  | zero => intro W hW; exact hW
  | succ d ih => intro W hW; rw [Function.iterate_succ_apply']; exact Z_closed _ (ih W hW)

theorem iter_Z (V : List ℕ) (t : ℕ) (h : F^[t] V ∈ Z) (j : ℕ) (hj : t ≤ j) : F^[j] V ∈ Z := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + t := ⟨j - t, by omega⟩
  rw [Function.iterate_add_apply]
  exact Z_iter d _ h

/-- `D V k`: the trajectory of `V` first enters the cycle set at step `k`. -/
abbrev D (V : List ℕ) (k : ℕ) : Prop := F^[k] V ∈ Z ∧ ∀ i < k, F^[i] V ∉ Z

theorem D_zero (V : List ℕ) (h : V ∈ Z) : D V 0 := ⟨h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

theorem D_succ (V : List ℕ) (k : ℕ) (hV : V ∉ Z) (h : D (F V) k) : D V (k + 1) := by
  refine ⟨h.1, ?_⟩
  intro i hi
  cases i with
  | zero => exact hV
  | succ i => exact h.2 i (by omega)

theorem D_pred (W : List ℕ) (k : ℕ) (hW : W ∉ Z) (h : D W k) : ∃ k', k = k' + 1 ∧ D (F W) k' := by
  cases k with
  | zero => exact absurd h.1 hW
  | succ k' => exact ⟨k', rfl, h.1, fun i hi => h.2 (i + 1) (by omega)⟩

theorem sInf_of_D (V : List ℕ) (k : ℕ) (h : D V k) :
    sInf {i | ∃ j, i < j ∧ F^[i] V = F^[j] V} = k := by
  have hmem : ∃ j, k < j ∧ F^[k] V = F^[j] V :=
    ⟨6 + k, by omega, by rw [Function.iterate_add_apply, Z_per _ h.1]⟩
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨k, hmem⟩
  rintro i ⟨j, hij, hH⟩
  by_contra hlt
  have hik : i < k := by omega
  obtain ⟨d, rfl⟩ : ∃ d, j = d + 1 + i := ⟨j - i - 1, by omega⟩
  have hW : F^[d + 1] (F^[i] V) = F^[i] V := by
    rw [← Function.iterate_add_apply]; exact hH.symm
  have hWk : ∀ N, F^[(d + 1) * N] (F^[i] V) = F^[i] V := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show (d + 1) * (N + 1) = (d + 1) * N + (d + 1) by ring, Function.iterate_add_apply, hW, ih]
  have hge : k ≤ (d + 1) * k + i := by
    have := Nat.mul_le_mul (Nat.le_add_left 1 d) (le_refl k)
    rw [Nat.one_mul] at this
    omega
  have hZ := iter_Z V k h.1 _ hge
  rw [Function.iterate_add_apply, hWk k] at hZ
  exact h.2 i hik hZ

theorem a_of_D (n k : ℕ) (h : D (digs n) k) : a n = k := by
  show sInf {i | ∃ j, i < j ∧ F^[i] (digs n) = F^[j] (digs n)} = k
  exact sInf_of_D (digs n) k h

/-! Bounded search, to settle finitely many small vectors by `decide`. -/

def dst : ℕ → List ℕ → Option ℕ
  | 0, _ => none
  | n + 1, V => if V ∈ Z then some 0 else (dst n (F V)).map (· + 1)

theorem dst_D (n : ℕ) : ∀ (V : List ℕ) (k : ℕ), dst n V = some k → D V k := by
  induction n with
  | zero => intro V k h; simp [dst] at h
  | succ n ih =>
    intro V k h
    by_cases hV : V ∈ Z
    · simp only [dst, if_pos hV] at h
      cases h
      exact D_zero V hV
    · simp only [dst, if_neg hV] at h
      cases hd : dst n (F V) with
      | none => rw [hd] at h; simp at h
      | some k' =>
        rw [hd] at h
        simp at h
        subst h
        exact D_succ V k' hV (ih (F V) k' hd)

abbrev Ev (V : List ℕ) : Prop := ∃ k, D V k ∧ k % 2 = 0

def ev (V : List ℕ) : Bool :=
  match dst 40 V with
  | some k => k % 2 == 0
  | none => false

theorem ev_spec (V : List ℕ) (h : ev V = true) : Ev V := by
  unfold ev at h
  cases hd : dst 40 V with
  | none => rw [hd] at h; simp at h
  | some k =>
    rw [hd] at h
    refine ⟨k, dst_D 40 V k hd, ?_⟩
    simpa using h

theorem Ev_two (V W X : List ℕ) (hV : V ∉ Z) (h1 : F V = W) (hW : W ∉ Z) (h2 : F W = X)
    (hX : Ev X) : Ev V := by
  obtain ⟨k, hk, he⟩ := hX
  refine ⟨k + 2, ?_, by omega⟩
  subst h1
  subst h2
  exact D_succ V (k + 1) hV (D_succ (F V) k hW hk)

/-! Explicit counting steps. -/

theorem F_pq (p r : ℕ) : F [p, p + 1 + r] = List.replicate p 0 ++ 1 :: (List.replicate r 0 ++ [1]) := by
  have e1 : [p, p + 1 + r].count p = 1 := by
    simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  have e2 : [p, p + 1 + r].count (p + 1 + r) = 1 := by
    simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  have hz1 : ∀ i, 0 ≤ i → i < 0 + p → [p, p + 1 + r].count i = 0 := by
    intro i _ h; simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  have hz2 : ∀ i, 0 + p + 1 ≤ i → i < 0 + p + 1 + r → [p, p + 1 + r].count i = 0 := by
    intro i h1 h2; simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  rw [F_of_max _ (p + 1 + r) (by intro x hx; simp at hx; omega) (by simp),
    show p + 1 + r + 1 = p + 1 + (r + 1) by omega, seg_split3, seg_const _ 0 0 p hz1,
    seg_last _ (0 + p + 1) r hz2]
  simp only [Nat.zero_add, e1, e2]

theorem F_ind2 (p r : ℕ) : F (List.replicate p 0 ++ 1 :: (List.replicate r 0 ++ [1])) = [p + r, 2] := by
  rw [F_of_max _ 1 (by intro x hx; simp at hx; omega) (by simp), seg_two]
  simp only [List.count_append, cnt_cons, cnt_rep, List.count_nil]
  simp

theorem F_pp (p : ℕ) : F [p, p] = List.replicate p 0 ++ [2] := by
  have e : [p, p].count p = 2 := by
    simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  have hz : ∀ i, 0 ≤ i → i < 0 + p → [p, p].count i = 0 := by
    intro i _ h; simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  rw [F_of_max _ p (by intro x hx; simp at hx; omega) (by simp), seg_last _ 0 p hz]
  simp only [Nat.zero_add, e]

theorem F_rep2 (p : ℕ) : F (List.replicate p 0 ++ [2]) = [p, 0, 1] := by
  rw [F_of_max _ 2 (by intro x hx; simp at hx; omega) (by simp), seg_three]
  simp only [List.count_append, cnt_cons, cnt_rep, List.count_nil]
  simp

theorem F_p01 (p : ℕ) : F [p + 2, 0, 1] = 1 :: 1 :: (List.replicate p 0 ++ [1]) := by
  have hz : ∀ i, 2 ≤ i → i < 2 + p → [p + 2, 0, 1].count i = 0 := by
    intro i h1 h2; simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  have e0 : [p + 2, 0, 1].count 0 = 1 := by
    simp [cnt_cons]
  have e1 : [p + 2, 0, 1].count 1 = 1 := by
    simp [cnt_cons]
  have e2 : [p + 2, 0, 1].count (2 + p) = 1 := by
    simp only [cnt_cons, List.count_nil]; (try split_ifs) <;> omega
  rw [F_of_max _ (p + 2) (by intro x hx; simp at hx; omega) (by simp), seg_head2 _ p hz]
  simp only [e0, e1, e2]

theorem F_11 (p : ℕ) : F (1 :: 1 :: (List.replicate p 0 ++ [1])) = [p, 3] := by
  rw [F_of_max _ 1 (by intro x hx; simp at hx; omega) (by simp), seg_two]
  simp only [List.count_append, cnt_cons, cnt_rep, List.count_nil]
  simp

/-! Two-vectors. -/

set_option maxRecDepth 20000 in
theorem small2 : ∀ p < 4, ∀ q < 4, 4 ≤ p + q → ev [p, q] = true := by decide

theorem Ev_m2 (m : ℕ) : Ev [m + 3, 2] := by
  induction m with
  | zero => exact ev_spec _ (by decide)
  | succ m ih =>
    have h1 : F [m + 1 + 3, 2] = List.replicate 2 0 ++ 1 :: (List.replicate (m + 1) 0 ++ [1]) := by
      rw [F_swap, show m + 1 + 3 = 2 + 1 + (m + 1) by omega]
      exact F_pq 2 (m + 1)
    have h2 : F (List.replicate 2 0 ++ 1 :: (List.replicate (m + 1) 0 ++ [1])) = [m + 3, 2] := by
      rw [F_ind2, show 2 + (m + 1) = m + 3 by omega]
    refine Ev_two _ _ _ ?_ h1 ?_ h2 ih
    · exact notZ_ent _ (m + 1 + 3) (by simp) (by omega)
    · exact notZ_len _ (by simp)

theorem Ev_m2' (m : ℕ) (h : 3 ≤ m) : Ev [m, 2] := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
  exact Ev_m2 t

theorem Ev_pq (p r : ℕ) (h : 4 ≤ p + 1 + r) : Ev [p, p + 1 + r] := by
  refine Ev_two _ _ _ ?_ (F_pq p r) ?_ (F_ind2 p r) (Ev_m2' (p + r) (by omega))
  · exact notZ_ent _ (p + 1 + r) (by simp) h
  · exact notZ_len _ (by simp <;> omega)

theorem Ev_qp (p r : ℕ) (h : 4 ≤ p + 1 + r) : Ev [p + 1 + r, p] := by
  refine Ev_two _ _ _ ?_ ((F_swap _ _).trans (F_pq p r)) ?_ (F_ind2 p r) (Ev_m2' (p + r) (by omega))
  · exact notZ_ent _ (p + 1 + r) (by simp) h
  · exact notZ_len _ (by simp <;> omega)

theorem Ev_pp (s : ℕ) : Ev [s + 2 + 2, s + 2 + 2] := by
  have h4 : Ev [s + 2, 3] := by
    by_cases hs : s + 2 < 4
    · exact ev_spec _ (small2 (s + 2) hs 3 (by norm_num) (by omega))
    · obtain ⟨r, hr⟩ : ∃ r, s + 2 = 3 + 1 + r := ⟨s - 2, by omega⟩
      rw [hr]
      exact Ev_qp 3 r (by omega)
  have h2 : Ev [s + 2 + 2, 0, 1] := by
    refine Ev_two _ _ _ ?_ (F_p01 (s + 2)) ?_ (F_11 (s + 2)) h4
    · exact notZ_ent _ (s + 2 + 2) (by simp) (by omega)
    · exact notZ_len _ (by simp <;> omega)
  refine Ev_two _ _ _ ?_ (F_pp _) ?_ (F_rep2 _) h2
  · exact notZ_ent _ (s + 2 + 2) (by simp) (by omega)
  · exact notZ_len _ (by simp <;> omega)

theorem T2E (p q : ℕ) (h : 4 ≤ p + q) : Ev [p, q] := by
  by_cases hs : p < 4 ∧ q < 4
  · exact ev_spec _ (small2 p hs.1 q hs.2 h)
  · rcases lt_trichotomy p q with hpq | hpq | hpq
    · obtain ⟨r, rfl⟩ : ∃ r, q = p + 1 + r := ⟨q - p - 1, by omega⟩
      exact Ev_pq p r (by omega)
    · subst hpq
      obtain ⟨s, rfl⟩ : ∃ s, p = s + 2 + 2 := ⟨p - 4, by omega⟩
      exact Ev_pp s
    · obtain ⟨r, rfl⟩ : ∃ r, p = q + 1 + r := ⟨p - q - 1, by omega⟩
      exact Ev_qp q r (by omega)

/-! The binary digit vector. -/

theorem count01 (S : List ℕ) (h : ∀ x ∈ S, x ≤ 1) : S.count 0 + S.count 1 = S.length := by
  induction S with
  | nil => simp
  | cons x S ih =>
    have hx : x ≤ 1 := h x (by simp)
    have ih' := ih (fun y hy => h y (by simp [hy]))
    rw [cnt_cons, cnt_cons, List.length_cons]
    split_ifs <;> omega

theorem Z_ofDigits : ∀ v ∈ Z, Nat.ofDigits 2 v.reverse ≤ 9 := by decide

theorem main_odd (n : ℕ) (hn : 9 < n) : Odd (a n) := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨S, hS⟩ : ∃ S, S = (Nat.digits 2 n).reverse := ⟨_, rfl⟩
  have hdigs : digs n = S := by
    rw [hS]
    unfold digs
    rw [if_neg hn0]
  have hlt : ∀ x ∈ S, x ≤ 1 := by
    intro x hx
    rw [hS, List.mem_reverse] at hx
    have := Nat.digits_lt_base (by norm_num : 1 < 2) hx
    omega
  have h1 : 1 ∈ S := by
    have hne : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
    have hl : (Nat.digits 2 n).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero 2 hn0
    have hm := List.getLast_mem hne
    have hb := Nat.digits_lt_base (by norm_num : 1 < 2) hm
    have he : (Nat.digits 2 n).getLast hne = 1 := by omega
    rw [he] at hm
    rw [hS, List.mem_reverse]
    exact hm
  have hFS : F S = [S.count 0, S.count 1] := by
    rw [F_of_max S 1 hlt h1, seg_two]
  have hsum := count01 S hlt
  have hlen : 4 ≤ S.length := by
    have hl : n < 2 ^ (Nat.digits 2 n).length := Nat.lt_base_pow_length_digits (by norm_num)
    have hSl : S.length = (Nat.digits 2 n).length := by rw [hS, List.length_reverse]
    by_contra hc
    have h8 : 2 ^ (Nat.digits 2 n).length ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : n < 8 := by
      calc n < 2 ^ (Nat.digits 2 n).length := hl
        _ ≤ 2 ^ 3 := h8
        _ = 8 := by norm_num
    omega
  by_cases hZ : S ∈ Z
  · exfalso
    have h9 := Z_ofDigits S hZ
    rw [hS, List.reverse_reverse, Nat.ofDigits_digits] at h9
    omega
  · obtain ⟨k, hk, he⟩ := T2E (S.count 0) (S.count 1) (by omega)
    have hD : D (digs n) (k + 1) := by
      rw [hdigs]
      exact D_succ S k hZ (by rw [hFS]; exact hk)
    rw [a_of_D n (k + 1) hD]
    exact ⟨k / 2, by omega⟩

end OMA.A225660Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a225660.main := by
  intro n hn
  exact OMA.A225660Proof.main_odd n hn
