import OMAStatements.S_oeis_a050686

-- Problem: A050686, n-digit palindromes containing 1: bijection with half-digit vectors, then count.
-- Credit: @bnb9001

namespace OMA_A050686_Proof

open Finset OMA.S_oeis_a050686

/-- the low half of the digit list -/
def half {m : ℕ} (v : Fin m → Fin 10) : List ℕ := List.ofFn (fun i => (v i : ℕ))

/-- the full (little-endian) digit list of the palindrome with low half `v` -/
def full (n : ℕ) {m : ℕ} (v : Fin m → Fin 10) : List ℕ :=
  half v ++ ((half v).take (n - m)).reverse

theorem half_length {m : ℕ} (v : Fin m → Fin 10) : (half v).length = m := by simp [half]

theorem full_length {n m : ℕ} (hm : n - m ≤ m) (hmn : m ≤ n) (v : Fin m → Fin 10) :
    (full n v).length = n := by
  simp only [full, List.length_append, List.length_reverse, List.length_take, half_length]
  omega

theorem mem_full {n m : ℕ} (v : Fin m → Fin 10) (x : ℕ) : x ∈ full n v ↔ x ∈ half v := by
  simp only [full, List.mem_append, List.mem_reverse]
  constructor
  · rintro (h | h)
    · exact h
    · exact List.mem_of_mem_take h
  · intro h; exact Or.inl h

theorem full_lt {n m : ℕ} (v : Fin m → Fin 10) : ∀ x ∈ full n v, x < 10 := by
  intro x hx
  rw [mem_full, half, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  exact (v i).2

theorem full_pal (n : ℕ) (v : Fin ((n + 1) / 2) → Fin 10) :
    (full n v).reverse = full n v := by
  simp only [full, List.reverse_append, List.reverse_reverse]
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h1 : (t + t + 1) / 2 = t := by omega
    have h2 : t + t - (t + t + 1) / 2 = t := by omega
    have hl : (half v).length = (t + t + 1) / 2 := half_length v
    rw [h2, List.take_of_length_le (by omega)]
  · have h2 : 2 * t + 1 - (2 * t + 1 + 1) / 2 = t := by omega
    have hl : (half v).length = t + 1 := by rw [half_length]; omega
    rw [h2]
    set L := half v
    have hsplit : L = L.take t ++ L.drop t := (List.take_append_drop t L).symm
    have hd : (L.drop t).length = 1 := by simp [hl]
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hd
    have htl : (L.take t).length = t := by simp [hl]
    conv_rhs => rw [hsplit, hx]
    conv_lhs => rw [hsplit, hx]
    simp only [List.take_left' htl, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.append_assoc, List.cons_append]

theorem full_head {n m : ℕ} (hm : 0 < m) (v : Fin m → Fin 10) (h : full n v ≠ []) :
    (full n v).head h = (v ⟨0, hm⟩ : ℕ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp [full, half, List.ofFn_succ]

/-- the palindrome number of a half-vector -/
def F (n : ℕ) (v : Fin ((n + 1) / 2) → Fin 10) : ℕ := Nat.ofDigits 10 (full n v)

theorem digits_F {n : ℕ} (hn : 1 ≤ n) (v : Fin ((n + 1) / 2) → Fin 10) (hv : v ⟨0, by omega⟩ ≠ 0) :
    Nat.digits 10 (F n v) = full n v := by
  apply Nat.digits_ofDigits 10 (by norm_num) _ (full_lt v)
  intro hne
  have hpal := full_pal n v
  have hrev : (full n v).reverse ≠ [] := by simpa using hne
  have : (full n v).getLast hne = (full n v).reverse.head hrev := by
    rw [List.head_reverse]
  rw [this]
  have hh : (full n v).reverse.head hrev = (full n v).head hne := by
    congr 1
  rw [hh, full_head (by omega)]
  intro h0
  apply hv
  exact Fin.ext (by simpa using h0)

theorem F_injective {n : ℕ} (hn : 1 ≤ n) {v w : Fin ((n + 1) / 2) → Fin 10}
    (hv : v ⟨0, by omega⟩ ≠ 0) (hw : w ⟨0, by omega⟩ ≠ 0) (h : F n v = F n w) : v = w := by
  have hd := congrArg (Nat.digits 10) h
  rw [digits_F hn v hv, digits_F hn w hw] at hd
  have ht := congrArg (List.take ((n + 1) / 2)) hd
  simp only [full] at ht
  rw [List.take_left' (half_length v), List.take_left' (half_length w)] at ht
  have := List.ofFn_injective ht
  funext i
  exact Fin.ext (congrFun this i)

theorem F_range {n : ℕ} (hn : 1 ≤ n) (v : Fin ((n + 1) / 2) → Fin 10) (hv : v ⟨0, by omega⟩ ≠ 0) :
    F n v ∈ Ico (10 ^ (n - 1)) (10 ^ n) := by
  have hlen : (Nat.digits 10 (F n v)).length = n := by
    rw [digits_F hn v hv, full_length (by omega) (by omega)]
  rw [mem_Ico]
  constructor
  · by_contra hlt
    rw [not_le, ← Nat.digits_length_le_iff (by norm_num)] at hlt
    omega
  · rw [← Nat.digits_length_le_iff (by norm_num)]; omega

theorem surj {n : ℕ} (hn : 1 ≤ n) {k : ℕ} (hk : k ∈ Ico (10 ^ (n - 1)) (10 ^ n)) (hpal : IsPal k) :
    ∃ v : Fin ((n + 1) / 2) → Fin 10, v ⟨0, by omega⟩ ≠ 0 ∧ F n v = k := by
  set D := Nat.digits 10 k with hD
  rw [mem_Ico] at hk
  have hk0 : k ≠ 0 := by
    intro h; rw [h] at hk; have := Nat.one_le_pow (n - 1) 10 (by norm_num); omega
  have hlen : D.length = n := by
    have h1 : D.length ≤ n := (Nat.digits_length_le_iff (by norm_num) k).mpr hk.2
    have h2 : ¬ D.length ≤ n - 1 := fun h =>
      absurd ((Nat.digits_length_le_iff (by norm_num) k).mp h) (not_lt.mpr hk.1)
    omega
  set m := (n + 1) / 2 with hm
  have hmn : m ≤ n := by omega
  let v : Fin m → Fin 10 := fun i =>
    ⟨D.get ⟨i, by omega⟩, Nat.digits_lt_base (by norm_num) (List.get_mem _ _)⟩
  have hhalf : half v = D.take m := by
    apply List.ext_get
    · simp [half_length]; omega
    · intro i h1 h2
      simp [half, v]
  have hfull : full n v = D := by
    unfold full
    rw [hhalf, List.take_take, show min (n - m) m = n - m by omega]
    have hrev : (D.take (n - m)).reverse = D.drop m := by
      have : D.take (n - m) = D.reverse.take (n - m) := by rw [hpal]
      rw [this, List.take_reverse, List.reverse_reverse, hlen,
        show n - (n - m) = m by omega]
    rw [hrev, List.take_append_drop]
  refine ⟨v, ?_, ?_⟩
  · intro h0
    have hne : D ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    have hlast := Nat.getLast_digit_ne_zero 10 hk0
    have hrev : D.reverse ≠ [] := by simpa using hne
    have e1 : D.getLast hne = D.reverse.head hrev := by rw [List.head_reverse]
    have e2 : D.reverse.head hrev = D.head hne := by congr 1
    have e3 : D.head hne = (v ⟨0, by omega⟩ : ℕ) := by
      simp only [v, List.get_eq_getElem]
      exact (List.getElem_zero _).symm
    apply hlast
    rw [show (Nat.digits 10 k).getLast _ = D.getLast hne from rfl, e1, e2, e3, h0]
    rfl
  · unfold F; rw [hfull, hD, Nat.ofDigits_digits]

/-- the half-vectors with nonzero leading digit -/
def P (m : ℕ) : Finset (Fin m → Fin 10) :=
  Fintype.piFinset fun i : Fin m => if (i : ℕ) = 0 then univ.erase 0 else univ

/-- ... that also avoid the digit 1 -/
def P' (m : ℕ) : Finset (Fin m → Fin 10) :=
  Fintype.piFinset fun i : Fin m => if (i : ℕ) = 0 then (univ.erase 0).erase 1 else univ.erase 1

theorem card_P (j : ℕ) : (P (j + 1)).card = 9 * 10 ^ j := by
  rw [P, Fintype.card_piFinset, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero]

theorem card_P' (j : ℕ) : (P' (j + 1)).card = 8 * 9 ^ j := by
  rw [P', Fintype.card_piFinset, Fin.prod_univ_succ]
  simp [Fin.succ_ne_zero, card_erase_of_mem]

theorem P'_sub (m : ℕ) : P' m ⊆ P m := by
  intro v hv
  simp only [P, P', Fintype.mem_piFinset] at hv ⊢
  intro i
  have := hv i
  split_ifs at this ⊢ with h
  · exact mem_of_mem_erase this
  · exact mem_univ _

theorem mem_P {m : ℕ} (hm : 0 < m) (v : Fin m → Fin 10) : v ∈ P m ↔ v ⟨0, hm⟩ ≠ 0 := by
  simp only [P, Fintype.mem_piFinset]
  constructor
  · intro h; have := h ⟨0, hm⟩; simp at this; exact this
  · intro h i
    split_ifs with hi
    · have : i = ⟨0, hm⟩ := Fin.ext hi
      subst this; simpa using h
    · exact mem_univ _

theorem mem_P' {m : ℕ} (hm : 0 < m) (v : Fin m → Fin 10) :
    v ∈ P' m ↔ v ⟨0, hm⟩ ≠ 0 ∧ ∀ i, v i ≠ 1 := by
  simp only [P', Fintype.mem_piFinset]
  constructor
  · intro h
    refine ⟨fun h0 => ?_, fun i h1 => ?_⟩
    · have := h ⟨0, hm⟩; simp [h0] at this
    · have := h i; split_ifs at this <;> simp [h1] at this
  · rintro ⟨h0, h1⟩ i
    split_ifs with hi
    · have : i = ⟨0, hm⟩ := Fin.ext hi
      subst this; simp [h0, h1]
    · simp [h1 i]

theorem one_mem_iff {n m : ℕ} (v : Fin m → Fin 10) : 1 ∈ full n v ↔ ∃ i, v i = 1 := by
  rw [mem_full, half, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, Fin.ext (by simpa using hi)⟩
  · rintro ⟨i, hi⟩; exact ⟨i, by simp [hi]⟩

end OMA_A050686_Proof

open Finset OMA.S_oeis_a050686 OMA_A050686_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a050686.main := by
  intro n hn
  classical
  have hm : 0 < (n + 1) / 2 := by omega
  have hset : ((Ico (10 ^ (n - 1)) (10 ^ n)).filter fun k => IsPal k ∧ 1 ∈ Nat.digits 10 k) =
      (P ((n + 1) / 2) \ P' ((n + 1) / 2)).image (F n) := by
    ext k
    simp only [mem_filter, mem_image, mem_sdiff]
    constructor
    · rintro ⟨hk, hpal, h1⟩
      obtain ⟨v, hv0, rfl⟩ := surj hn hk hpal
      refine ⟨v, ⟨(mem_P hm v).mpr hv0, fun hP' => ?_⟩, rfl⟩
      rw [digits_F hn v hv0, one_mem_iff] at h1
      obtain ⟨i, hi⟩ := h1
      exact ((mem_P' hm v).mp hP').2 i hi
    · rintro ⟨v, ⟨hP, hnP'⟩, rfl⟩
      have hv0 := (mem_P hm v).mp hP
      refine ⟨F_range hn v hv0, ?_, ?_⟩
      · unfold IsPal; rw [digits_F hn v hv0]; exact full_pal n v
      · rw [digits_F hn v hv0, one_mem_iff]
        by_contra hno
        push_neg at hno
        exact hnP' ((mem_P' hm v).mpr ⟨hv0, hno⟩)
  unfold a
  rw [hset, card_image_of_injOn]
  · rw [card_sdiff_of_subset (P'_sub _)]
    obtain ⟨j, hj⟩ : ∃ j, (n + 1) / 2 = j + 1 := ⟨(n + 1) / 2 - 1, by omega⟩
    rw [hj, card_P, card_P', Nat.add_sub_cancel]
  · intro v hv w hw h
    simp only [coe_sdiff, Set.mem_sdiff, mem_coe] at hv hw
    exact F_injective hn ((mem_P hm v).mp hv.1) ((mem_P hm w).mp hw.1) h
