import OMAReductions.R_Erdos18_erdos_18a_R1

/-!
# Proof of `Erdos18.erdos_18a.R1.H2`

Given short representations of every dyadic residue `x : ZMod (2 ^ k)` as a list
sum of at most `2 * (Nat.log 2 k + 1) ^ 5` divisors of `(36 * k)!` with sum at
most `2 * 2 ^ (3 * k)`, we prove that there exists `C` such that for all
sufficiently large `T`, every `R < 2 ^ T` is a sum of at most
`C * (Nat.log 2 T + 1) ^ 6` distinct divisors of `(4 * T)!`.

Method:
1. Elementary factorial divisibility: `2 ^ a * b! ∣ (b + 2 * a)!` by induction on `a`.
2. Recursive dyadic peeling: for `T ≥ T₀ = max (40 * k₀) 2000`, set `k = T / 40`.
   Peel `k` low bits at a time while `R ≥ 2 ^ (3 * k + 1)` using the hypothesis on `k`,
   shifting each step by `2 ^ k` (`≤ 41` steps total), then recurse on the remaining
   value `< 2 ^ (min m (3 * k + 1))` (which halves `T`). This produces a list `L` of
   divisors of `2 ^ T * T!` with sum `R` and length `≤ T₀ + 82 * (Nat.log 2 T + 1) ^ 6`.
3. Weighted binary carry deduplication: repeatedly merge equal pairs `(x, w₁), (x, w₂)`
   into `(2 * x, w₁ + w₂)` while maintaining `x = 2 ^ j * d` with `2 ^ j ≤ w` and
   `d ∈ L`. When all values are distinct, every `2 ^ j ≤ L.length ≤ 2 ^ (T / 2)` for
   large `T`, so every element divides `2 ^ (T + T / 2) * T! ∣ (4 * T)!`.
-/

namespace OMA.P_Erdos18_erdos_18a_R1_H2

open Filter Finset

/-- Elementary divisibility: `2 ^ a * b! ∣ (b + 2 * a)!`. -/
private lemma two_pow_mul_factorial_dvd : ∀ (a b : ℕ),
    2 ^ a * b.factorial ∣ (b + 2 * a).factorial
  | 0, b => by simp
  | a + 1, b => by
    have ih := two_pow_mul_factorial_dvd a b
    have h2 : 2 ∣ (b + 2 * a + 2) * (b + 2 * a + 1) := by
      rcases Nat.even_or_odd (b + 2 * a) with ⟨t, ht⟩ | ⟨t, ht⟩
      · refine ⟨(t + 1) * (b + 2 * a + 1), ?_⟩; rw [ht]; ring
      · refine ⟨(b + 2 * a + 2) * (t + 1), ?_⟩; rw [ht]; ring
    have hfac : (b + 2 * (a + 1)).factorial =
        ((b + 2 * a + 2) * (b + 2 * a + 1)) * (b + 2 * a).factorial := by
      rw [show b + 2 * (a + 1) = (b + 2 * a + 1) + 1 by omega, Nat.factorial_succ,
        Nat.factorial_succ, mul_assoc]
    rw [hfac, pow_succ', mul_assoc]
    exact mul_dvd_mul h2 ih

/-- Base case: every `R < 2 ^ T` is a sum of at most `T` powers of two dividing `2 ^ T`. -/
private lemma list_rep_binary : ∀ (T R : ℕ), R < 2 ^ T →
    ∃ L : List ℕ, (∀ d ∈ L, d ∣ 2 ^ T) ∧ L.sum = R ∧ L.length ≤ T
  | 0, R, hR => by
    have hR0 : R = 0 := by simp at hR; omega
    subst hR0
    exact ⟨[], by simp, by simp, le_rfl⟩
  | T + 1, R, hR => by
    have hq_lt : R / 2 < 2 ^ T := by
      rw [pow_succ'] at hR
      omega
    obtain ⟨L', hL'dvd, hL'sum, hL'len⟩ := list_rep_binary T (R / 2) hq_lt
    let L₁ := L'.map (2 * ·)
    have hL₁_dvd : ∀ d ∈ L₁, d ∣ 2 ^ (T + 1) := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
      rw [pow_succ']
      exact mul_dvd_mul_left 2 (hL'dvd x hx)
    have hL₁_sum : L₁.sum = 2 * (R / 2) := by
      dsimp only [L₁]
      rw [List.sum_map_mul_left]
      simp only [List.map_id', hL'sum]
    have hL₁_len : L₁.length ≤ T := by simpa [L₁] using hL'len
    by_cases hmod : R % 2 = 0
    · refine ⟨L₁, hL₁_dvd, ?_, by omega⟩
      rw [hL₁_sum]; omega
    · refine ⟨1 :: L₁, ?_, ?_, ?_⟩
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd'
        · exact one_dvd _
        · exact hL₁_dvd d hd'
      · simp only [List.sum_cons, hL₁_sum]; omega
      · simp only [List.length_cons]; omega

/-- Peeling `k` bits at a time down to `< 2 ^ (3 * k + 1)` using the dyadic hypothesis on `k`. -/
private lemma peel_dyadic {T k B₀ : ℕ} (hk_pos : 1 ≤ k) (h36 : 36 * k ≤ T)
    (hdyad : ∀ x : ZMod (2 ^ k), ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (36 * k).factorial) ∧ S.length ≤ 2 * (Nat.log 2 k + 1) ^ 5 ∧
      S.sum ≤ 2 * 2 ^ (3 * k) ∧ (S.sum : ZMod (2 ^ k)) = x)
    (hbase : ∀ m', m' ≤ min T (3 * k + 1) → ∀ R < 2 ^ m',
      ∃ L : List ℕ, (∀ d ∈ L, d ∣ 2 ^ m' * T.factorial) ∧ L.sum = R ∧ L.length ≤ B₀) :
    ∀ m, m ≤ T → ∀ R < 2 ^ m,
      ∃ L : List ℕ, (∀ d ∈ L, d ∣ 2 ^ m * T.factorial) ∧ L.sum = R ∧
        L.length ≤ (m / k) * (2 * (Nat.log 2 k + 1) ^ 5) + B₀ := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hmT R hR
    by_cases hsmall : R < 2 ^ (3 * k + 1)
    · let m' := min m (3 * k + 1)
      have hm'_le : m' ≤ min T (3 * k + 1) := by dsimp only [m']; omega
      have hR_m' : R < 2 ^ m' := by
        dsimp only [m']
        rcases le_total m (3 * k + 1) with h | h
        · rwa [min_eq_left h]
        · rwa [min_eq_right h]
      obtain ⟨L, hLdvd, hLsum, hLlen⟩ := hbase m' hm'_le R hR_m'
      refine ⟨L, ?_, hLsum, Nat.le_add_left_of_le hLlen⟩
      intro d hd
      exact dvd_trans (hLdvd d hd)
        (mul_dvd_mul_right (Nat.pow_dvd_pow 2 (min_le_left m (3 * k + 1))) _)
    · have hR_ge : 2 * 2 ^ (3 * k) ≤ R := by
        rw [← pow_succ']
        omega
      have hm_gt : 3 * k + 1 < m := by
        by_contra hle
        push Not at hle
        have hpow : 2 ^ m ≤ 2 ^ (3 * k + 1) := Nat.pow_le_pow_right (by norm_num) hle
        omega
      obtain ⟨S, hSdvd, hSlen, hSsum, hSmod⟩ := hdyad (R : ZMod (2 ^ k))
      have hS_le_R : S.sum ≤ R := le_trans hSsum hR_ge
      have hsub_dvd : 2 ^ k ∣ (R - S.sum) := by
        have hcast : ((R - S.sum : ℕ) : ZMod (2 ^ k)) = 0 := by
          rw [Nat.cast_sub hS_le_R, hSmod, sub_self]
        exact (ZMod.natCast_eq_zero_iff (R - S.sum) (2 ^ k)).mp hcast
      let R' := (R - S.sum) / 2 ^ k
      have hR_eq : S.sum + 2 ^ k * R' = R := by
        have h1 : 2 ^ k * R' = R - S.sum := Nat.mul_div_cancel' hsub_dvd
        omega
      have hR'_lt : R' < 2 ^ (m - k) := by
        have hmul : 2 ^ k * R' < 2 ^ k * 2 ^ (m - k) := by
          calc 2 ^ k * R' ≤ R := by omega
            _ < 2 ^ m := hR
            _ = 2 ^ (k + (m - k)) := by rw [Nat.add_sub_of_le (by omega)]
            _ = 2 ^ k * 2 ^ (m - k) := pow_add 2 k (m - k)
        exact Nat.lt_of_mul_lt_mul_left hmul
      obtain ⟨L', hL'dvd, hL'sum, hL'len⟩ := ih (m - k) (by omega) (by omega) R' hR'_lt
      let L₁ := L'.map (2 ^ k * ·)
      refine ⟨S ++ L₁, ?_, ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.mp hd with hdS | hdL
        · have h1 : d ∣ (36 * k).factorial := hSdvd d hdS
          have h2 : (36 * k).factorial ∣ T.factorial := Nat.factorial_dvd_factorial h36
          exact dvd_trans (dvd_trans h1 h2) (dvd_mul_left T.factorial (2 ^ m))
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hdL
          have h1 : 2 ^ k * u ∣ 2 ^ k * (2 ^ (m - k) * T.factorial) :=
            mul_dvd_mul_left (2 ^ k) (hL'dvd u hu)
          rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega)] at h1
          exact h1
      · rw [List.sum_append]
        dsimp only [L₁]
        rw [List.sum_map_mul_left]
        simp only [List.map_id', hL'sum, hR_eq]
      · rw [List.length_append]
        have hL₁_len : L₁.length = L'.length := List.length_map _
        rw [hL₁_len]
        have hdiv : (m - k) / k + 1 = m / k := by
          have h1 : m - k + k = m := by omega
          conv_rhs => rw [← h1]
          rw [Nat.add_div_right _ (by omega : 0 < k)]
        calc S.length + L'.length
            ≤ 2 * (Nat.log 2 k + 1) ^ 5 +
              ((m - k) / k * (2 * (Nat.log 2 k + 1) ^ 5) + B₀) :=
              Nat.add_le_add hSlen hL'len
          _ = ((m - k) / k + 1) * (2 * (Nat.log 2 k + 1) ^ 5) + B₀ := by ring
          _ = (m / k) * (2 * (Nat.log 2 k + 1) ^ 5) + B₀ := by rw [hdiv]

/-- Full list representation for all `T` and `R < 2 ^ T`. -/
private lemma list_rep_poly {k₀ : ℕ}
    (hdyad : ∀ k ≥ k₀, ∀ x : ZMod (2 ^ k), ∃ S : List ℕ,
      (∀ d ∈ S, d ∣ (36 * k).factorial) ∧ S.length ≤ 2 * (Nat.log 2 k + 1) ^ 5 ∧
      S.sum ≤ 2 * 2 ^ (3 * k) ∧ (S.sum : ZMod (2 ^ k)) = x) :
    let T₀ := max (40 * k₀) 2000
    ∀ T : ℕ, ∀ R < 2 ^ T, ∃ L : List ℕ,
      (∀ d ∈ L, d ∣ 2 ^ T * T.factorial) ∧ L.sum = R ∧
      L.length ≤ T₀ + 82 * (Nat.log 2 T + 1) ^ 6 := by
  intro T₀ T
  induction T using Nat.strong_induction_on with
  | h T ih =>
    intro R hR
    by_cases hsmall : T < T₀
    · obtain ⟨L, hLdvd, hLsum, hLlen⟩ := list_rep_binary T R hR
      refine ⟨L, ?_, hLsum, by omega⟩
      intro d hd
      exact dvd_trans (hLdvd d hd) (dvd_mul_right (2 ^ T) T.factorial)
    · have hT_ge : T₀ ≤ T := by omega
      let k := T / 40
      have hk_ge : k₀ ≤ k := by dsimp only [k, T₀] at *; omega
      have hk_pos : 1 ≤ k := by dsimp only [k, T₀] at *; omega
      have h36 : 36 * k ≤ T := by dsimp only [k]; omega
      have hT'_le_half : 2 * (3 * k + 1) ≤ T := by dsimp only [k, T₀] at *; omega
      have hlog_T' : ∀ m' ≤ min T (3 * k + 1), Nat.log 2 m' + 1 ≤ Nat.log 2 T := by
        intro m' hm'
        by_cases hm'0 : m' = 0
        · subst hm'0
          simp only [Nat.log_zero_right, zero_add]
          rw [Nat.le_log_iff_pow_le (by norm_num) (by dsimp only [T₀] at *; omega)]
          dsimp only [T₀] at *; omega
        · have h1 : 2 ^ (Nat.log 2 m' + 1) ≤ 2 * m' := by
            rw [pow_succ']
            exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hm'0)
          have h2 : 2 * m' ≤ T := by omega
          exact (Nat.le_log_iff_pow_le (by norm_num) (by dsimp only [T₀] at *; omega)).mpr
            (le_trans h1 h2)
      let B₀ := T₀ + 82 * (Nat.log 2 T) ^ 6
      have hbase : ∀ m', m' ≤ min T (3 * k + 1) → ∀ R' < 2 ^ m',
          ∃ L : List ℕ, (∀ d ∈ L, d ∣ 2 ^ m' * T.factorial) ∧ L.sum = R' ∧ L.length ≤ B₀ := by
        intro m' hm' R' hR'
        have hm'_lt : m' < T := by omega
        obtain ⟨L, hLdvd, hLsum, hLlen⟩ := ih m' hm'_lt R' hR'
        refine ⟨L, ?_, hLsum, ?_⟩
        · intro d hd
          exact dvd_trans (hLdvd d hd)
            (mul_dvd_mul_left (2 ^ m') (Nat.factorial_dvd_factorial (le_of_lt hm'_lt)))
        · have hlog_le : Nat.log 2 m' + 1 ≤ Nat.log 2 T := hlog_T' m' hm'
          calc L.length
              ≤ T₀ + 82 * (Nat.log 2 m' + 1) ^ 6 := hLlen
            _ ≤ T₀ + 82 * (Nat.log 2 T) ^ 6 :=
                Nat.add_le_add_left (Nat.mul_le_mul_left 82 (Nat.pow_le_pow_left hlog_le 6)) T₀
      obtain ⟨L, hLdvd, hLsum, hLlen⟩ :=
        peel_dyadic hk_pos h36 (hdyad k hk_ge) hbase T le_rfl R hR
      have hdiv41 : T / k ≤ 41 := by
        have hmul : T < 42 * k := by dsimp only [k, T₀] at *; omega
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega : 0 < k)).mpr hmul)
      have hlogk : Nat.log 2 k + 1 ≤ Nat.log 2 T + 1 :=
        Nat.add_le_add_right (Nat.log_mono_right (by dsimp only [k]; omega)) 1
      have hpow_comb : (Nat.log 2 T) ^ 6 + (Nat.log 2 T + 1) ^ 5 ≤ (Nat.log 2 T + 1) ^ 6 := by
        have h1 : (Nat.log 2 T) ^ 6 ≤ (Nat.log 2 T) * (Nat.log 2 T + 1) ^ 5 := by
          calc (Nat.log 2 T) ^ 6
              = (Nat.log 2 T) * (Nat.log 2 T) ^ 5 := by ring
            _ ≤ (Nat.log 2 T) * (Nat.log 2 T + 1) ^ 5 :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) 5)
        calc (Nat.log 2 T) ^ 6 + (Nat.log 2 T + 1) ^ 5
            ≤ (Nat.log 2 T) * (Nat.log 2 T + 1) ^ 5 + 1 * (Nat.log 2 T + 1) ^ 5 := by linarith
          _ = (Nat.log 2 T + 1) ^ 6 := by ring
      refine ⟨L, hLdvd, hLsum, ?_⟩
      calc L.length
          ≤ (T / k) * (2 * (Nat.log 2 k + 1) ^ 5) + B₀ := hLlen
        _ ≤ 41 * (2 * (Nat.log 2 T + 1) ^ 5) + (T₀ + 82 * (Nat.log 2 T) ^ 6) :=
            Nat.add_le_add_right
              (Nat.mul_le_mul hdiv41 (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlogk 5))) B₀
        _ = T₀ + 82 * ((Nat.log 2 T) ^ 6 + (Nat.log 2 T + 1) ^ 5) := by ring
        _ ≤ T₀ + 82 * (Nat.log 2 T + 1) ^ 6 :=
            Nat.add_le_add_left (Nat.mul_le_mul_left 82 hpow_comb) T₀

/-- Helper: if a list of pairs `(x, w)` has a duplicate first coordinate, we can extract two
entries with the same `.1` and the remaining list. -/
private lemma extract_dup_fst : ∀ (L : List (ℕ × ℕ)), ¬ (L.map Prod.fst).Nodup →
    ∃ (x w₁ w₂ : ℕ) (rest : List (ℕ × ℕ)),
      rest.length + 2 = L.length ∧
      (x + x + (rest.map Prod.fst).sum = (L.map Prod.fst).sum) ∧
      (w₁ + w₂ + (rest.map Prod.snd).sum = (L.map Prod.snd).sum) ∧
      ((x, w₁) ∈ L ∧ (x, w₂) ∈ L ∧ ∀ p ∈ rest, p ∈ L)
  | [], h => absurd List.nodup_nil h
  | (a, wa) :: tl, h => by
    rw [List.map_cons, List.nodup_cons] at h
    push Not at h
    by_cases hmem : a ∈ tl.map Prod.fst
    · obtain ⟨p, hp_mem, hp_fst⟩ := List.mem_map.mp hmem
      obtain ⟨l₁, l₂, htl⟩ := List.append_of_mem hp_mem
      have ha_eq : p.1 = a := hp_fst
      refine ⟨a, wa, p.2, l₁ ++ l₂, ?_, ?_, ?_, ?_⟩
      · rw [htl]; simp [List.length_append]; omega
      · rw [htl]; simp [List.map_append, List.sum_append, ha_eq]; ring
      · rw [htl]; simp [List.map_append, List.sum_append]; ring
      · refine ⟨List.mem_cons_self, List.mem_cons_of_mem _ (by rw [← ha_eq]; exact hp_mem), ?_⟩
        intro q hq
        apply List.mem_cons_of_mem
        rw [htl]
        rcases List.mem_append.mp hq with h1 | h2
        · exact List.mem_append_left _ h1
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
    · have hnd : ¬ (tl.map Prod.fst).Nodup := h hmem
      obtain ⟨x, w₁, w₂, rest, hlen, hsum1, hsum2, h1, h2, hrest⟩ := extract_dup_fst tl hnd
      refine ⟨x, w₁, w₂, (a, wa) :: rest, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [List.map_cons, List.sum_cons]; linarith
      · simp only [List.map_cons, List.sum_cons]; linarith
      · refine ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hrest q hq')

/-- Weighted binary carry deduplication: transforms a list `L₀` into a `Finset ℕ` `D` with the
same sum, at most `L₀.length` elements, and each `x ∈ D` equal to `2 ^ j * d` for some
`d ∈ L₀` and `2 ^ j ≤ L₀.length`. -/
private lemma binary_carry_dedup (L₀ : List ℕ) :
    ∃ D : Finset ℕ, D.sum id = L₀.sum ∧ D.card ≤ L₀.length ∧
      ∀ x ∈ D, ∃ d ∈ L₀, ∃ j : ℕ, x = 2 ^ j * d ∧ 2 ^ j ≤ L₀.length := by
  have hgen : ∀ (n : ℕ) (L : List (ℕ × ℕ)), L.length = n →
      (L.map Prod.snd).sum = L₀.length →
      (L.map Prod.fst).sum = L₀.sum →
      (∀ p ∈ L, ∃ d ∈ L₀, ∃ j : ℕ, p.1 = 2 ^ j * d ∧ 2 ^ j ≤ p.2) →
      ∃ D : Finset ℕ, D.sum id = L₀.sum ∧ D.card ≤ L.length ∧
        ∀ x ∈ D, ∃ d ∈ L₀, ∃ j : ℕ, x = 2 ^ j * d ∧ 2 ^ j ≤ L₀.length := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro L hlen hwsum hsum hinv
      by_cases hnd : (L.map Prod.fst).Nodup
      · let D : Finset ℕ := (L.map Prod.fst).toFinset
        refine ⟨D, ?_, ?_, ?_⟩
        · have h1 := List.sum_toFinset id hnd
          simpa [D, hsum] using h1
        · calc D.card ≤ (L.map Prod.fst).length := List.toFinset_card_le _
            _ = L.length := List.length_map _
        · intro x hx
          have hx' : x ∈ L.map Prod.fst := List.mem_toFinset.mp hx
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
          obtain ⟨d, hd, j, hxj, hjw⟩ := hinv p hp
          have hw_le : p.2 ≤ L₀.length := by
            rw [← hwsum]
            exact List.le_sum_of_mem (List.mem_map_of_mem hp)
          exact ⟨d, hd, j, hxj, le_trans hjw hw_le⟩
      · obtain ⟨x, w₁, w₂, rest, hrest_len, hrest_sum, hrest_wsum, hmem1, hmem2, hrest_mem⟩ :=
          extract_dup_fst L hnd
        let L' := (2 * x, w₁ + w₂) :: rest
        have hL'_len : L'.length < n := by dsimp only [L']; simp; omega
        have hL'_wsum : (L'.map Prod.snd).sum = L₀.length := by
          dsimp only [L']
          simp only [List.map_cons, List.sum_cons]
          omega
        have hL'_sum : (L'.map Prod.fst).sum = L₀.sum := by
          dsimp only [L']
          simp only [List.map_cons, List.sum_cons]
          omega
        have hL'_inv : ∀ p ∈ L', ∃ d ∈ L₀, ∃ j : ℕ, p.1 = 2 ^ j * d ∧ 2 ^ j ≤ p.2 := by
          intro p hp
          rcases List.mem_cons.mp hp with rfl | hpr
          · obtain ⟨d₁, hd₁, j₁, hx₁, hj₁⟩ := hinv (x, w₁) hmem1
            obtain ⟨d₂, hd₂, j₂, hx₂, hj₂⟩ := hinv (x, w₂) hmem2
            dsimp only at hx₁ hx₂ hj₁ hj₂
            rcases le_total j₁ j₂ with hle | hle
            · refine ⟨d₁, hd₁, j₁ + 1, ?_, ?_⟩
              · rw [pow_succ', mul_assoc, ← hx₁]
              · have hpow : 2 ^ j₁ ≤ 2 ^ j₂ := Nat.pow_le_pow_right (by norm_num) hle
                rw [pow_succ']
                omega
            · refine ⟨d₂, hd₂, j₂ + 1, ?_, ?_⟩
              · rw [pow_succ', mul_assoc, ← hx₂]
              · have hpow : 2 ^ j₂ ≤ 2 ^ j₁ := Nat.pow_le_pow_right (by norm_num) hle
                rw [pow_succ']
                omega
          · exact hinv p (hrest_mem p hpr)
        obtain ⟨D, hDsum, hDcard, hDinv⟩ := ih L'.length hL'_len L' rfl hL'_wsum hL'_sum hL'_inv
        refine ⟨D, hDsum, ?_, hDinv⟩
        dsimp only [L'] at hDcard
        simp only [List.length_cons] at hDcard
        omega
  let init := L₀.map (fun d => (d, 1))
  have hinit_len : init.length = L₀.length := List.length_map _
  have hinit_wsum : (init.map Prod.snd).sum = L₀.length := by
    dsimp only [init]
    rw [List.map_map]
    simp [Function.comp_def]
  have hinit_sum : (init.map Prod.fst).sum = L₀.sum := by
    dsimp only [init]
    rw [List.map_map]
    simp [Function.comp_def]
  have hinit_inv : ∀ p ∈ init, ∃ d ∈ L₀, ∃ j : ℕ, p.1 = 2 ^ j * d ∧ 2 ^ j ≤ p.2 := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    exact ⟨d, hd, 0, by simp, by simp⟩
  obtain ⟨D, hDsum, hDcard, hDinv⟩ := hgen init.length init rfl hinit_wsum hinit_sum hinit_inv
  exact ⟨D, hDsum, hinit_len ▸ hDcard, hDinv⟩

/-- Purely arithmetic bound: `82 * (m + 1) ^ 6 ≤ 2 ^ m` for all `m ≥ 40`. -/
private lemma mul_pow_six_le_two_pow : ∀ m : ℕ, 40 ≤ m → 82 * (m + 1) ^ 6 ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h40 : 40 ≤ m
    · have hih := ih h40
      have hstep : (m + 2) ^ 6 ≤ 2 * (m + 1) ^ 6 := by
        have hlin : 10 * (m + 2) ≤ 11 * (m + 1) := by omega
        have hpow : (10 * (m + 2)) ^ 6 ≤ (11 * (m + 1)) ^ 6 := Nat.pow_le_pow_left hlin 6
        have hconst : 11 ^ 6 ≤ 2 * 10 ^ 6 := by decide
        rw [mul_pow, mul_pow] at hpow
        have h2 : 10 ^ 6 * (m + 2) ^ 6 ≤ 10 ^ 6 * (2 * (m + 1) ^ 6) := by
          calc 10 ^ 6 * (m + 2) ^ 6 ≤ 11 ^ 6 * (m + 1) ^ 6 := hpow
            _ ≤ (2 * 10 ^ 6) * (m + 1) ^ 6 := Nat.mul_le_mul_right _ hconst
            _ = 10 ^ 6 * (2 * (m + 1) ^ 6) := by ring
        exact Nat.le_of_mul_le_mul_left h2 (by decide)
      calc 82 * (m + 1 + 1) ^ 6
          ≤ 82 * (2 * (m + 1) ^ 6) := Nat.mul_le_mul_left 82 hstep
        _ = 2 * (82 * (m + 1) ^ 6) := by ring
        _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 hih
        _ = 2 ^ (m + 1) := by rw [pow_succ']
    · have hm39 : m = 39 := by omega
      subst hm39
      norm_num

/-- Eventually `A + 82 * (Nat.log 2 T + 1) ^ 6 ≤ 2 ^ (T / 2)`. -/
private lemma poly_log_le_two_pow_half (A : ℕ) :
    ∀ᶠ T : ℕ in atTop, A + 82 * (Nat.log 2 T + 1) ^ 6 ≤ 2 ^ (T / 2) := by
  filter_upwards [Filter.eventually_ge_atTop (2 * (A + 42))] with T hT
  let m := T / 2 - 1
  have hm_ge : 40 ≤ m := by dsimp only [m]; omega
  have hA_le : A ≤ 2 ^ m := le_trans (by dsimp only [m]; omega) (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hlog_le : Nat.log 2 T ≤ m := by
    have hlog_lt : Nat.log 2 T < T / 2 := by
      have hpow : ∀ k : ℕ, 6 ≤ k → 2 * (k + 1) ≤ 2 ^ k := by
        intro k hk
        induction k with
        | zero => omega
        | succ k ih =>
          by_cases h6 : 6 ≤ k
          · have hih := ih h6
            rw [pow_succ']
            omega
          · have hk5 : k = 5 := by omega
            subst hk5
            norm_num
      by_cases h6 : 6 ≤ Nat.log 2 T
      · have h1 := hpow (Nat.log 2 T) h6
        have h2 := Nat.pow_log_le_self 2 (by omega : T ≠ 0)
        omega
      · omega
    dsimp only [m]
    omega
  have hpoly : 82 * (Nat.log 2 T + 1) ^ 6 ≤ 2 ^ m := by
    calc 82 * (Nat.log 2 T + 1) ^ 6
        ≤ 82 * (m + 1) ^ 6 := Nat.mul_le_mul_left 82 (Nat.pow_le_pow_left (by omega) 6)
      _ ≤ 2 ^ m := mul_pow_six_le_two_pow m hm_ge
  have hhalf : T / 2 = m + 1 := by dsimp only [m]; omega
  rw [hhalf, pow_succ' 2 m]
  omega

end OMA.P_Erdos18_erdos_18a_R1_H2

theorem OMA.solution : OMA.R_Erdos18_erdos_18a_R1.H2 := by
  intro hdyad_ev
  obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp hdyad_ev
  let T₀ := max (40 * k₀) 2000
  refine ⟨T₀ + 82, ?_⟩
  filter_upwards [OMA.P_Erdos18_erdos_18a_R1_H2.poly_log_le_two_pow_half T₀] with T hT_bound
  intro R hR
  obtain ⟨L, hLdvd, hLsum, hLlen⟩ :=
    OMA.P_Erdos18_erdos_18a_R1_H2.list_rep_poly hk₀ T R hR
  obtain ⟨D, hDsum, hDcard, hDinv⟩ :=
    OMA.P_Erdos18_erdos_18a_R1_H2.binary_carry_dedup L
  refine ⟨D, ?_, by rw [hDsum, hLsum], ?_⟩
  · intro x hx
    obtain ⟨d, hd, j, rfl, hj_le⟩ := hDinv x hx
    have hj_le_pow : 2 ^ j ≤ 2 ^ (T / 2) := le_trans hj_le (le_trans hLlen hT_bound)
    have hj_le_half : j ≤ T / 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hj_le_pow
    have hd_dvd : d ∣ 2 ^ T * T.factorial := hLdvd d hd
    have h1 : 2 ^ j * d ∣ 2 ^ (T / 2) * (2 ^ T * T.factorial) :=
      mul_dvd_mul (Nat.pow_dvd_pow 2 hj_le_half) hd_dvd
    have h2 : 2 ^ (T / 2) * (2 ^ T * T.factorial) = 2 ^ (T / 2 + T) * T.factorial := by
      rw [← mul_assoc, ← pow_add]
    have h3 : 2 ^ (T / 2 + T) * T.factorial ∣ (T + 2 * (T / 2 + T)).factorial :=
      OMA.P_Erdos18_erdos_18a_R1_H2.two_pow_mul_factorial_dvd (T / 2 + T) T
    have h4 : (T + 2 * (T / 2 + T)).factorial ∣ (4 * T).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    rw [h2] at h1
    exact Nat.mem_divisors.mpr ⟨dvd_trans h1 (dvd_trans h3 h4), (Nat.factorial_pos (4 * T)).ne'⟩
  · have hone : 1 ≤ (Nat.log 2 T + 1) ^ 6 := Nat.one_le_pow 6 _ (Nat.succ_pos _)
    calc D.card ≤ L.length := hDcard
      _ ≤ T₀ + 82 * (Nat.log 2 T + 1) ^ 6 := hLlen
      _ ≤ T₀ * (Nat.log 2 T + 1) ^ 6 + 82 * (Nat.log 2 T + 1) ^ 6 :=
          Nat.add_le_add_right (Nat.le_mul_of_pos_right T₀ hone) _
      _ = (T₀ + 82) * (Nat.log 2 T + 1) ^ 6 := by ring
