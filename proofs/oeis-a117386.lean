import OMAStatements.S_oeis_a117386
import Mathlib

/- Proof of Hanna's limits in A117386 (c = 6).
Plan. F c m and G c m = c*m - F c m are the first and second positions of the value m.
(1) Shape: F (m+1) - F m is 1 or 2, G (m+1) - G m >= 3, F m < G m, F and G have disjoint ranges covering
    all positions >= 1, and the list process of the statement agrees with this description.
(2) With J = F m - m: G J < F m < G (J+1).
(3) With alpha + beta = c, alpha * beta = c, beta > 2 and (beta - 2) * B = beta: |F m - alpha * m| <= B.
(4) Hence liminf a(n)/n = 1/beta and limsup a(n)/n = 1/alpha. -/

namespace OMA.A117386Proof

/-- `st c m = (F c m, R c m)`: the first position of `m` and the set of second positions of `1, ..., m`. -/
def st (c : ℕ) : ℕ → ℕ × Finset ℕ
  | 0 => (0, ∅)
  | m + 1 =>
    let f' := if (st c m).1 + 1 ∈ (st c m).2 then (st c m).1 + 2 else (st c m).1 + 1
    (f', insert (c * (m + 1) - f') (st c m).2)

def F (c m : ℕ) : ℕ := (st c m).1

def R (c m : ℕ) : Finset ℕ := (st c m).2

def G (c m : ℕ) : ℕ := c * m - F c m

lemma F_zero (c : ℕ) : F c 0 = 0 := rfl

lemma R_zero (c : ℕ) : R c 0 = ∅ := rfl

lemma F_succ (c m : ℕ) : F c (m + 1) = if F c m + 1 ∈ R c m then F c m + 2 else F c m + 1 := rfl

lemma R_succ (c m : ℕ) : R c (m + 1) = insert (G c (m + 1)) (R c m) := rfl

lemma F_step (c m : ℕ) : F c (m + 1) = F c m + 1 ∨ F c (m + 1) = F c m + 2 := by
  rw [F_succ]; split_ifs <;> simp

lemma F_one (c : ℕ) : F c 1 = 1 := by
  show F c (0 + 1) = 1
  rw [F_succ, R_zero, F_zero]
  simp

lemma le_F (c m : ℕ) : m ≤ F c m := by
  induction m with
  | zero => simp [F_zero]
  | succ m ih => rcases F_step c m with h | h <;> omega

lemma F_le (c m : ℕ) : F c (m + 1) ≤ 2 * m + 1 := by
  induction m with
  | zero => simp [F_one]
  | succ m ih => rcases F_step c (m + 1) with h | h <;> omega

lemma F_le2 (c m : ℕ) : F c m ≤ 2 * m := by
  cases m with
  | zero => simp [F_zero]
  | succ m => have := F_le c m; omega

lemma F_lt2 (c m : ℕ) (hm : 1 ≤ m) : F c m + 1 ≤ 2 * m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := F_le c k
  omega

lemma F_strictMono (c : ℕ) : StrictMono (F c) :=
  strictMono_nat_of_lt_succ (fun m => by rcases F_step c m with h | h <;> omega)

lemma G_zero (c : ℕ) : G c 0 = 0 := by
  unfold G; rw [F_zero]; simp

lemma G_step (c : ℕ) (hc : 5 ≤ c) (m : ℕ) : G c m + 3 ≤ G c (m + 1) := by
  have h1 := F_le2 c m
  have h2 := F_step c m
  have h3 : 5 * m ≤ c * m := Nat.mul_le_mul_right m hc
  have h4 : c * (m + 1) = c * m + c := by ring
  unfold G
  rw [h4]
  omega

lemma G_strictMono (c : ℕ) (hc : 5 ≤ c) : StrictMono (G c) :=
  strictMono_nat_of_lt_succ (fun m => by have := G_step c hc m; omega)

lemma G_add3 (c : ℕ) (hc : 5 ≤ c) {i j : ℕ} (h : i < j) : G c i + 3 ≤ G c j := by
  have h1 := G_step c hc i
  have h2 : G c (i + 1) ≤ G c j := (G_strictMono c hc).monotone (by omega)
  omega

lemma F_lt_G (c : ℕ) (hc : 5 ≤ c) {m : ℕ} (hm : 1 ≤ m) : F c m < G c m := by
  have h1 := F_le2 c m
  have h3 : 5 * m ≤ c * m := Nat.mul_le_mul_right m hc
  unfold G
  omega

lemma G_cast (c : ℕ) (hc : 5 ≤ c) (j : ℕ) : (G c j : ℝ) = (c : ℝ) * j - F c j := by
  have h1 := F_le2 c j
  have h3 : 5 * j ≤ c * j := Nat.mul_le_mul_right j hc
  unfold G
  rw [Nat.cast_sub (by omega), Nat.cast_mul]

lemma mem_R (c m x : ℕ) : x ∈ R c m ↔ ∃ j, 1 ≤ j ∧ j ≤ m ∧ x = G c j := by
  induction m with
  | zero =>
    rw [R_zero]
    constructor
    · intro h; simp at h
    · rintro ⟨j, h1, h2, -⟩; omega
  | succ m ih =>
    rw [R_succ, Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨j, h1, h2, h3⟩)
      · exact ⟨m + 1, by omega, le_refl _, h⟩
      · exact ⟨j, h1, by omega, h3⟩
    · rintro ⟨j, h1, h2, h3⟩
      rcases Nat.lt_or_ge j (m + 1) with h | h
      · exact Or.inr ⟨j, h1, by omega, h3⟩
      · left; rw [h3, show j = m + 1 by omega]

/-- The key invariant: with `J = F c m - m`, the first position `F c m` lies strictly between the second
positions `G c J` and `G c (J + 1)`. -/
lemma FG_inv (c : ℕ) (hc : 5 ≤ c) (m : ℕ) (hm : 1 ≤ m) :
    G c (F c m - m) < F c m ∧ F c m < G c (F c m - m + 1) := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h1 : F c 1 = 1 := F_one c
    have h0 : G c 0 = 0 := G_zero c
    have h3 : G c 1 = c - 1 := by unfold G; rw [h1, mul_one]
    rw [h1, Nat.sub_self, zero_add, h0, h3]
    omega
  | succ m hm ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hJ := F_lt2 c m hm
    have hmF := le_F c m
    have hGs := G_strictMono c hc
    rw [F_succ]
    split_ifs with hmem
    · obtain ⟨j, hj1, hjm, hjG⟩ := (mem_R c m _).1 hmem
      have e1 : F c m + 2 - (m + 1) = F c m - m + 1 := by omega
      rw [e1]
      have hlt : F c m - m < j := hGs.lt_iff_lt.1 (by omega)
      have hle : j ≤ F c m - m + 1 := hGs.le_iff_le.1 (by omega)
      have hj : j = F c m - m + 1 := by omega
      subst hj
      have := G_add3 c hc (show F c m - m + 1 < F c m - m + 1 + 1 by omega)
      constructor <;> omega
    · have e1 : F c m + 1 - (m + 1) = F c m - m := by omega
      rw [e1]
      refine ⟨by omega, ?_⟩
      rcases Nat.lt_or_ge (F c m + 1) (G c (F c m - m + 1)) with h | h
      · exact h
      · exfalso
        apply hmem
        rw [mem_R]
        exact ⟨F c m - m + 1, by omega, by omega, by omega⟩

lemma F_ne_G (c : ℕ) (hc : 5 ≤ c) {m j : ℕ} (hm : 1 ≤ m) : F c m ≠ G c j := by
  intro h
  obtain ⟨h1, h2⟩ := FG_inv c hc m hm
  have hGs := G_strictMono c hc
  have a1 : F c m - m < j := hGs.lt_iff_lt.1 (by omega)
  have a2 : j < F c m - m + 1 := hGs.lt_iff_lt.1 (by omega)
  omega

lemma cover (c : ℕ) (hc : 5 ≤ c) {n : ℕ} (hn : 1 ≤ n) :
    (∃ m, 1 ≤ m ∧ F c m = n) ∨ (∃ m, 1 ≤ m ∧ G c m = n) := by
  have hex : ∃ k, n < F c (k + 1) := ⟨n, by have := le_F c (n + 1); omega⟩
  obtain ⟨k, hk, hmin⟩ : ∃ k, n < F c (k + 1) ∧ ∀ i < k, ¬ n < F c (i + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hk' : F c k ≤ n := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [F_zero]; omega
    · have := hmin (k - 1) (by omega)
      rw [show k - 1 + 1 = k by omega] at this
      omega
  rcases F_step c k with h | h
  · left
    refine ⟨k, ?_, by omega⟩
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0; rw [F_zero] at hk' h; omega
    · exact hpos
  · by_cases hnk : n = F c k
    · left
      refine ⟨k, ?_, hnk.symm⟩
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; rw [F_zero] at hnk; omega
      · exact hpos
    · right
      have hmem : F c k + 1 ∈ R c k := by
        by_contra hnm
        have := F_succ c k
        rw [if_neg hnm] at this
        omega
      obtain ⟨j, hj1, -, hj⟩ := (mem_R c k _).1 hmem
      exact ⟨j, hj1, by omega⟩

/-- The value at position `n`: the `m` with `F c m = n` or `G c m = n`. -/
noncomputable def A (c n : ℕ) : ℕ := sInf {m | F c m = n ∨ G c m = n}

lemma A_eq (c : ℕ) (hc : 5 ≤ c) {m n : ℕ} (hm : 1 ≤ m) (h : F c m = n ∨ G c m = n) : A c n = m := by
  have hne : ({m | F c m = n ∨ G c m = n} : Set ℕ).Nonempty := ⟨m, h⟩
  have hmem : F c (A c n) = n ∨ G c (A c n) = n := Nat.sInf_mem hne
  have hFi := (F_strictMono c).injective
  have hGi := (G_strictMono c hc).injective
  have hn1 : 1 ≤ n := by
    rcases h with h | h
    · have := le_F c m; omega
    · have := F_lt_G c hc hm; have := le_F c m; omega
  rcases hmem with h1 | h1 <;> rcases h with h2 | h2
  · exact hFi (h1.trans h2.symm)
  · exfalso
    rcases Nat.eq_zero_or_pos (A c n) with h0 | h0
    · rw [h0, F_zero] at h1; omega
    · exact F_ne_G c hc h0 (h1.trans h2.symm)
  · exact absurd (h2.trans h1.symm) (F_ne_G c hc hm)
  · exact hGi (h1.trans h2.symm)

lemma A_F (c : ℕ) (hc : 5 ≤ c) {m : ℕ} (hm : 1 ≤ m) : A c (F c m) = m := A_eq c hc hm (Or.inl rfl)

lemma A_G (c : ℕ) (hc : 5 ≤ c) {m : ℕ} (hm : 1 ≤ m) : A c (G c m) = m := A_eq c hc hm (Or.inr rfl)

/-- The list process of the statement computes `A 6`. -/
lemma nextTerm_eq (n : ℕ) :
    OMA.S_oeis_a117386.nextTerm ((List.range n).map (fun i => A 6 (i + 1))) = A 6 (n + 1) := by
  have hc : (5 : ℕ) ≤ 6 := by norm_num
  set l := (List.range n).map (fun i => A 6 (i + 1)) with hl
  have hlen : l.length = n := by simp [hl]
  have hget : ∀ i, i < n → l.getD i 0 = A 6 (i + 1) := fun i hi => by simp [hl, hi]
  unfold OMA.S_oeis_a117386.nextTerm
  rcases cover 6 hc (show 1 ≤ n + 1 by omega) with ⟨m, hm, hFm⟩ | ⟨m, hm, hGm⟩
  · -- position n + 1 = F 6 m is vacant: it gets the smallest unused number, m
    have hA : A 6 (n + 1) = m := A_eq 6 hc hm (Or.inl hFm)
    have hno : ¬ ∃ i : ℕ, i < l.length ∧ l.length + 1 + (i + 1) = 6 * l.getD i 0 := by
      rintro ⟨i, hi, heq⟩
      rw [hlen] at hi heq
      rw [hget i hi] at heq
      rcases cover 6 hc (show 1 ≤ i + 1 by omega) with ⟨m', hm', hF'⟩ | ⟨m', hm', hG'⟩
      · rw [← hF', A_F 6 hc hm'] at heq
        have hG6 : G 6 m' = n + 1 := by unfold G; omega
        exact F_ne_G 6 hc hm (hFm.trans hG6.symm)
      · rw [← hG', A_G 6 hc hm'] at heq
        have hFG' : F 6 m' + G 6 m' = 6 * m' := by unfold G; have := F_le2 6 m'; omega
        have hlt := F_lt_G 6 hc hm'
        omega
    rw [dif_neg hno, hA]
    have hmIn : m ∈ {x : ℕ | 1 ≤ x ∧ x ∉ l} := by
      refine ⟨hm, fun hmem => ?_⟩
      rw [hl, List.mem_map] at hmem
      obtain ⟨i, hi, hiA⟩ := hmem
      rw [List.mem_range] at hi
      rcases cover 6 hc (show 1 ≤ i + 1 by omega) with ⟨m', hm', hF'⟩ | ⟨m', hm', hG'⟩
      · rw [← hF', A_F 6 hc hm'] at hiA
        subst hiA
        omega
      · rw [← hG', A_G 6 hc hm'] at hiA
        subst hiA
        have := F_lt_G 6 hc hm'
        omega
    apply le_antisymm (Nat.sInf_le hmIn)
    apply le_csInf ⟨m, hmIn⟩
    intro x hx
    obtain ⟨hx1, hxl⟩ := hx
    by_contra hlt
    push_neg at hlt
    apply hxl
    have hFx : F 6 x < F 6 m := F_strictMono 6 hlt
    have hFx1 := le_F 6 x
    rw [hl, List.mem_map]
    refine ⟨F 6 x - 1, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · rw [show F 6 x - 1 + 1 = F 6 x by omega]; exact A_F 6 hc hx1
  · -- position n + 1 = G 6 m is the reserved second place of m
    have hA : A 6 (n + 1) = m := A_eq 6 hc hm (Or.inr hGm)
    have hFlt := F_lt_G 6 hc hm
    have hFm1 := le_F 6 m
    have hFG : F 6 m + G 6 m = 6 * m := by unfold G; have := F_le2 6 m; omega
    have hyes : ∃ i : ℕ, i < l.length ∧ l.length + 1 + (i + 1) = 6 * l.getD i 0 := by
      refine ⟨F 6 m - 1, by rw [hlen]; omega, ?_⟩
      rw [hlen, hget (F 6 m - 1) (by omega), show F 6 m - 1 + 1 = F 6 m by omega, A_F 6 hc hm]
      omega
    rw [dif_pos hyes, hA]
    have hspec := Nat.find_spec hyes
    revert hspec
    generalize Nat.find hyes = i
    rintro ⟨hi, heq⟩
    rw [hlen] at hi heq
    rw [hget i hi] at heq ⊢
    rcases cover 6 hc (show 1 ≤ i + 1 by omega) with ⟨m', hm', hF'⟩ | ⟨m', hm', hG'⟩
    · rw [← hF', A_F 6 hc hm'] at heq ⊢
      have hG6 : G 6 m' = n + 1 := by unfold G; omega
      exact (G_strictMono 6 hc).injective (hG6.trans hGm.symm)
    · rw [← hG', A_G 6 hc hm'] at heq ⊢
      exfalso
      have hFG' : F 6 m' + G 6 m' = 6 * m' := by unfold G; have := F_le2 6 m'; omega
      have h1 : F 6 m' = n + 1 := by omega
      exact F_ne_G 6 hc hm' (h1.trans hGm.symm)

lemma terms_eq (n : ℕ) : OMA.S_oeis_a117386.terms n = (List.range n).map (fun i => A 6 (i + 1)) := by
  induction n with
  | zero => simp [OMA.S_oeis_a117386.terms]
  | succ n ih =>
    show OMA.S_oeis_a117386.terms n ++ [OMA.S_oeis_a117386.nextTerm (OMA.S_oeis_a117386.terms n)] = _
    rw [ih, nextTerm_eq]
    simp [List.range_succ]

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : OMA.S_oeis_a117386.a n = A 6 n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  show OMA.S_oeis_a117386.nextTerm (OMA.S_oeis_a117386.terms k) = _
  rw [terms_eq, nextTerm_eq]

/-- The contraction: `|F c m - alpha * m| ≤ B`. -/
theorem err_bound (c : ℕ) (hc : 5 ≤ c) (α β B : ℝ) (hsum : α + β = c) (hprod : α * β = c)
    (hβ : 2 < β) (hB : (β - 2) * B = β) (m : ℕ) : |(F c m : ℝ) - α * m| ≤ B := by
  have hB0 : 0 ≤ B := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg (sub_pos.2 hβ) hneg
    linarith
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simpa [F_zero] using hB0
    obtain ⟨h1, h2⟩ := FG_inv c hc m hpos
    have hJ := F_lt2 c m hpos
    have hmF := le_F c m
    obtain ⟨J, hJdef⟩ : ∃ J, J = F c m - m := ⟨_, rfl⟩
    rw [← hJdef] at h1 h2
    have hJm : J + 1 ≤ m := by omega
    have hJr : (J : ℝ) = (F c m : ℝ) - m := by
      have e : J + m = F c m := by omega
      have e' : ((J + m : ℕ) : ℝ) = (F c m : ℝ) := by rw [e]
      push_cast at e'
      linarith
    have h1r : (c : ℝ) * J - F c J < F c m := by
      have e : ((G c J : ℕ) : ℝ) < ((F c m : ℕ) : ℝ) := by exact_mod_cast h1
      rw [G_cast c hc] at e
      exact e
    have h2r : (F c m : ℝ) < c * ((J : ℝ) + 1) - F c (J + 1) := by
      have e : ((F c m : ℕ) : ℝ) < ((G c (J + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      rw [G_cast c hc] at e
      push_cast at e
      exact e
    have e1 : α * (F c m : ℝ) + β * F c m = c * F c m := by rw [← add_mul, hsum]
    have e2 : α * β * (m : ℝ) = c * m := by rw [hprod]
    have hup : (β - 1) * ((F c m : ℝ) - α * m) < (F c J : ℝ) - α * J := by
      rw [hJr] at h1r ⊢
      linarith
    have hlow : (F c (J + 1) : ℝ) - α * ((J : ℝ) + 1) - β < (β - 1) * ((F c m : ℝ) - α * m) := by
      rw [hJr] at h2r ⊢
      linarith
    have ihJ := abs_le.1 (ih J (by omega))
    rw [abs_le]
    constructor
    · rcases Nat.lt_or_ge (J + 1) m with hlt | hge
      · have ihJ1 := abs_le.1 (ih (J + 1) hlt)
        push_cast at ihJ1
        by_contra hcon
        push_neg at hcon
        have k := mul_lt_mul_of_pos_left hcon (show (0 : ℝ) < β - 1 by linarith)
        linarith [ihJ1.1]
      · have hJm' : J + 1 = m := by omega
        have hq : (F c (J + 1) : ℝ) = F c m := by rw [hJm']
        have hj1 : (J : ℝ) + 1 = m := by exact_mod_cast hJm'
        rw [hq, hj1] at hlow
        by_contra hcon
        push_neg at hcon
        have k := mul_lt_mul_of_pos_left hcon (show (0 : ℝ) < β - 2 by linarith)
        linarith
    · by_contra hcon
      push_neg at hcon
      have k := mul_lt_mul_of_pos_left hcon (show (0 : ℝ) < β - 1 by linarith)
      linarith [ihJ.2]

/-- The four bounds on `s = a` used for the limits, from the error bound. -/
lemma facts (c : ℕ) (hc : 5 ≤ c) (α β B : ℝ) (hsum : α + β = c) (hprod : α * β = c)
    (hβ : 2 < β) (hB : (β - 2) * B = β) (hαβ : α ≤ β) (s : ℕ → ℕ)
    (hs : ∀ n, 1 ≤ n → s n = A c n) :
    (∀ n : ℕ, 1 ≤ n → s n ≤ n) ∧
    (∀ n : ℕ, 1 ≤ n → α * s n ≤ n + B) ∧
    (∀ n : ℕ, 1 ≤ n → (n : ℝ) - B ≤ β * s n) ∧
    (∀ m, 1 ≤ m → ∃ n, m ≤ n ∧ s n = m ∧ (n : ℝ) ≤ α * m + B) ∧
    (∀ m, 1 ≤ m → ∃ n, m ≤ n ∧ s n = m ∧ β * m - B ≤ n) := by
  have hE := err_bound c hc α β B hsum hprod hβ hB
  have hEG : ∀ m : ℕ, |(G c m : ℝ) - β * m| ≤ B := by
    intro m
    rw [G_cast c hc]
    have e : (c : ℝ) * m - F c m - β * m = -((F c m : ℝ) - α * m) := by
      rw [← hsum]; ring
    rw [e, abs_neg]
    exact hE m
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hs n hn]
    rcases cover c hc hn with ⟨m, hm, hF⟩ | ⟨m, hm, hG⟩
    · rw [← hF, A_F c hc hm]; exact le_F c m
    · rw [← hG, A_G c hc hm]; have := F_lt_G c hc hm; have := le_F c m; omega
  · intro n hn
    rw [hs n hn]
    rcases cover c hc hn with ⟨m, hm, hF⟩ | ⟨m, hm, hG⟩
    · rw [← hF, A_F c hc hm]
      have := (abs_le.1 (hE m)).1
      linarith
    · rw [← hG, A_G c hc hm]
      have := (abs_le.1 (hEG m)).1
      have h2 : α * (m : ℝ) ≤ β * m := mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg m)
      linarith
  · intro n hn
    rw [hs n hn]
    rcases cover c hc hn with ⟨m, hm, hF⟩ | ⟨m, hm, hG⟩
    · rw [← hF, A_F c hc hm]
      have := (abs_le.1 (hE m)).2
      have h2 : α * (m : ℝ) ≤ β * m := mul_le_mul_of_nonneg_right hαβ (Nat.cast_nonneg m)
      linarith
    · rw [← hG, A_G c hc hm]
      have := (abs_le.1 (hEG m)).2
      linarith
  · intro m hm
    have h1 := le_F c m
    refine ⟨F c m, h1, ?_, ?_⟩
    · rw [hs (F c m) (by omega), A_F c hc hm]
    · have := (abs_le.1 (hE m)).2; linarith
  · intro m hm
    have h1 := le_F c m
    have h2 := F_lt_G c hc hm
    refine ⟨G c m, by omega, ?_, ?_⟩
    · rw [hs (G c m) (by omega), A_G c hc hm]
    · have := (abs_le.1 (hEG m)).1; linarith

/-- liminf and limsup of `u n = s n / n` from two-sided bounds and two witness subsequences. -/
theorem limits_of_bounds (s : ℕ → ℕ) (u : ℕ → ℝ) (hu : ∀ n, u n = (s n : ℝ) / n)
    (α β B L ℓ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hL : α * L = 1) (hℓ : β * ℓ = 1)
    (hle : ∀ n, s n ≤ n)
    (h1 : ∀ n : ℕ, 1 ≤ n → α * s n ≤ n + B)
    (h2 : ∀ n : ℕ, 1 ≤ n → (n : ℝ) - B ≤ β * s n)
    (h3 : ∀ m, 1 ≤ m → ∃ n, m ≤ n ∧ s n = m ∧ (n : ℝ) ≤ α * m + B)
    (h4 : ∀ m, 1 ≤ m → ∃ n, m ≤ n ∧ s n = m ∧ β * m - B ≤ n) :
    Filter.liminf u Filter.atTop = ℓ ∧ Filter.limsup u Filter.atTop = L := by
  have hu0 : ∀ n, 0 ≤ u n := fun n => by rw [hu]; positivity
  have hu1 : ∀ n, u n ≤ 1 := fun n => by
    rw [hu]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · rw [div_le_iff₀ (by exact_mod_cast hpos), one_mul]; exact_mod_cast hle n
  have hbl : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := Filter.isBoundedUnder_of ⟨1, hu1⟩
  have hbg : Filter.IsBoundedUnder (· ≥ ·) Filter.atTop u := Filter.isBoundedUnder_of ⟨0, hu0⟩
  have hcl : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop u :=
    Filter.isCoboundedUnder_le_of_le Filter.atTop hu0
  have hcg : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.isCoboundedUnder_ge_of_le Filter.atTop hu1
  have hN : ∀ γ : ℝ, 0 < γ → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → B ≤ γ * ε * n := by
    intro γ hγ ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (B / (γ * ε))
    refine ⟨N + 1, by omega, fun n hn => ?_⟩
    have k : B / (γ * ε) < n := lt_of_lt_of_le hN (by exact_mod_cast (show N ≤ n by omega))
    rw [div_lt_iff₀ (mul_pos hγ hε)] at k
    linarith
  have hup : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, u n ≤ L + ε := by
    intro ε hε
    obtain ⟨N, hN1, hN'⟩ := hN α hα ε hε
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans hN1 hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [hu, div_le_iff₀ hnpos]
    have k1 := h1 n hn1
    have k2 := hN' n hn
    have hLn : α * L * n = n := by rw [hL, one_mul]
    by_contra hcon
    push_neg at hcon
    have k3 := mul_lt_mul_of_pos_left hcon hα
    linarith
  have hlo : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.atTop, ℓ - ε ≤ u n := by
    intro ε hε
    obtain ⟨N, hN1, hN'⟩ := hN β hβ ε hε
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_trans hN1 hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [hu, le_div_iff₀ hnpos]
    have k1 := h2 n hn1
    have k2 := hN' n hn
    have hℓn : β * ℓ * n = n := by rw [hℓ, one_mul]
    by_contra hcon
    push_neg at hcon
    have k3 := mul_lt_mul_of_pos_left hcon hβ
    linarith
  have hfu : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in Filter.atTop, L - ε ≤ u n := by
    intro ε hε
    obtain ⟨M, hM1, hM'⟩ := hN α hα ε hε
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hmn, hsn, hn⟩ := h3 (max N M) (le_trans hM1 (le_max_right _ _))
    refine ⟨n, le_trans (le_max_left _ _) hmn, ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_trans hM1 (le_max_right _ _)) hmn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [hu, le_div_iff₀ hnpos, hsn]
    have k2 := hM' n (le_trans (le_max_right _ _) hmn)
    have hLn : α * L * n = n := by rw [hL, one_mul]
    by_contra hcon
    push_neg at hcon
    have k3 := mul_lt_mul_of_pos_left hcon hα
    linarith
  have hfl : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in Filter.atTop, u n ≤ ℓ + ε := by
    intro ε hε
    obtain ⟨M, hM1, hM'⟩ := hN β hβ ε hε
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hmn, hsn, hn⟩ := h4 (max N M) (le_trans hM1 (le_max_right _ _))
    refine ⟨n, le_trans (le_max_left _ _) hmn, ?_⟩
    have hn1 : 1 ≤ n := le_trans (le_trans hM1 (le_max_right _ _)) hmn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [hu, div_le_iff₀ hnpos, hsn]
    have k2 := hM' n (le_trans (le_max_right _ _) hmn)
    have hℓn : β * ℓ * n = n := by rw [hℓ, one_mul]
    by_contra hcon
    push_neg at hcon
    have k3 := mul_lt_mul_of_pos_left hcon hβ
    linarith
  constructor
  · apply le_antisymm
    · by_contra hcon
      push_neg at hcon
      have := Filter.liminf_le_of_frequently_le
        (hfl ((Filter.liminf u Filter.atTop - ℓ) / 2) (by linarith)) hbg
      linarith
    · by_contra hcon
      push_neg at hcon
      have := Filter.le_liminf_of_le hcg (hlo ((ℓ - Filter.liminf u Filter.atTop) / 2) (by linarith))
      linarith
  · apply le_antisymm
    · by_contra hcon
      push_neg at hcon
      have := Filter.limsup_le_of_le hcl (hup ((Filter.limsup u Filter.atTop - L) / 2) (by linarith))
      linarith
    · by_contra hcon
      push_neg at hcon
      have := Filter.le_limsup_of_frequently_le
        (hfu ((L - Filter.limsup u Filter.atTop) / 2) (by linarith)) hbl
      linarith

end OMA.A117386Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a117386.main := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hc : (5 : ℕ) ≤ 6 := by norm_num
  have hsum : (3 - Real.sqrt 3) + (3 + Real.sqrt 3) = ((6 : ℕ) : ℝ) := by push_cast; ring
  have hprod : (3 - Real.sqrt 3) * (3 + Real.sqrt 3) = ((6 : ℕ) : ℝ) := by
    push_cast; linear_combination (-1 : ℝ) * hs
  have hβ : (2 : ℝ) < 3 + Real.sqrt 3 := by linarith
  have hB : (3 + Real.sqrt 3 - 2) * Real.sqrt 3 = 3 + Real.sqrt 3 := by
    linear_combination (1 : ℝ) * hs
  have hαβ : 3 - Real.sqrt 3 ≤ 3 + Real.sqrt 3 := by linarith
  have hα : (0 : ℝ) < 3 - Real.sqrt 3 := by nlinarith [hs, hs0]
  have hβ0 : (0 : ℝ) < 3 + Real.sqrt 3 := by linarith
  have hL : (3 - Real.sqrt 3) * ((3 + Real.sqrt 3) / 6) = 1 := by
    linear_combination (-1 / 6 : ℝ) * hs
  have hℓ : (3 + Real.sqrt 3) * ((3 - Real.sqrt 3) / 6) = 1 := by
    linear_combination (-1 / 6 : ℝ) * hs
  obtain ⟨f0, f1, f2, f3, f4⟩ := OMA.A117386Proof.facts 6 hc _ _ _ hsum hprod hβ hB hαβ
    OMA.S_oeis_a117386.a (fun n hn => OMA.A117386Proof.a_eq n hn)
  have hle : ∀ n, OMA.S_oeis_a117386.a n ≤ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      show OMA.S_oeis_a117386.a 0 ≤ 0
      exact le_of_eq rfl
    · exact f0 n hpos
  exact OMA.A117386Proof.limits_of_bounds OMA.S_oeis_a117386.a
    (fun n : ℕ => (OMA.S_oeis_a117386.a n : ℝ) / n) (fun n => rfl) _ _ _ _ _ hα hβ0 hL hℓ hle
    f1 f2 f3 f4
