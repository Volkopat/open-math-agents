import FormalConjectures.ErdosProblems.«326»

/-! Cassels's additive basis of order 2 with a_n / n^2 → (1/54)^2. -/

open Filter
open scoped Topology

theorem OMA.solution : type_of% @Erdos326.erdos_326.variants.eq := by
  classical
  let grid (n : ℕ) : Prop := n < 4 ∨ ∃ k : ℕ, (2 ^ k) ^ 2 ≤ n ∧ n ≤ 16 * (2 ^ k) ^ 2 ∧ (2 ^ k ∣ n ∨ 2 ^ k + 1 ∣ n)
  have hcov (n : ℕ) : ∃ a b, grid a ∧ grid b ∧ a + b = n := by
    by_cases h : n < 4
    · exact ⟨0, n, Or.inl (by decide), Or.inl h, by omega⟩
    let k := Nat.log 4 (n / 4); let d := 2 ^ k
    have hp : 0 < d := by positivity
    have hd : 4 ^ k = d ^ 2 := by dsimp [d]; rw [← pow_mul, Nat.mul_comm k 2, pow_mul]; rfl
    have hlo : d ^ 2 ≤ n / 4 := hd ▸ Nat.pow_log_le_self 4 (by omega)
    have hhi : n / 4 < d ^ 2 * 4 := by
      have := Nat.lt_pow_succ_log_self (by decide : 1 < 4) (n / 4)
      rwa [pow_succ, hd] at this
    let r := n % d; have hr : r < d := Nat.mod_lt _ hp
    let b := (d + r) * (d + 1)
    have hb : b ≤ 3 * d ^ 2 := by
      dsimp [b]; nlinarith [Nat.mul_le_mul_right (d + 1) (by omega : r + 1 ≤ d), Nat.mul_self_le_mul_self hp]
    have hb' : d ^ 2 ≤ b := by dsimp [b]; nlinarith
    have hmod : b % d = r := by
      rw [show b = r + (d + r + 1) * d by dsimp [b]; ring, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
    exact ⟨n - b, b, Or.inr ⟨k, by dsimp [d] at *; omega, by dsimp [d] at *; omega,
      Or.inl ((Nat.modEq_iff_dvd' (by omega)).1 hmod)⟩, Or.inr ⟨k, hb', by dsimp [d] at *; omega, Or.inr (dvd_mul_left _ _)⟩, by omega⟩
  have hbin (m : ℕ) (hm : 54 ≤ m) : ∃ e : Fin 54 ↪o ℕ,
      (∀ i, e i ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2)) ∧
      ∀ n ∈ Finset.Ico (m ^ 2) ((m + 1) ^ 2), grid n → n ∈ Set.range e := by
    let T := Finset.Ico (m ^ 2) ((m + 1) ^ 2); let S := T.filter grid
    have hs : S.card ≤ 54 := by
      have hrepr (n : S) : ∃ (k : ℕ) (t : Fin 2) (q : ℕ), 2 ^ k ≤ m ∧ m ≤ 4 * 2 ^ k ∧ q * (2 ^ k + t.1) = n.1 := by
        obtain ⟨hnT, hg⟩ := Finset.mem_filter.1 n.2
        obtain ⟨hn, hn'⟩ := Finset.mem_Ico.1 hnT
        rcases hg with h | ⟨k, h1, h2, hd⟩
        · nlinarith
        · have hk : 2 ^ k ≤ m := by_contra fun hh => by
            nlinarith [Nat.pow_le_pow_left (show m + 1 ≤ 2 ^ k by omega) 2]
          have hk' : m ≤ 4 * 2 ^ k := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).1
            (calc m ^ 2 ≤ n.1 := hn
              _ ≤ 16 * (2 ^ k) ^ 2 := h2
              _ = (4 * 2 ^ k) ^ 2 := by ring)
          rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩
          · exact ⟨k, 0, q, hk, hk', by simpa [Nat.mul_comm] using hq.symm⟩
          · exact ⟨k, 1, q, hk, hk', by simpa [Nat.mul_comm] using hq.symm⟩
      choose k t q hk hk' he using hrepr
      let enc (n : S) : Fin 3 × Fin 2 × Fin 9 :=
        (⟨k n % 3, Nat.mod_lt _ (by decide)⟩, t n, ⟨q n % 9, Nat.mod_lt _ (by decide)⟩)
      have inj : Function.Injective enc := fun a b eq => by
        have heqk : k a % 3 = k b % 3 := congrArg (fun z : Fin 3 × Fin 2 × Fin 9 => z.1.1) eq
        have heqt : t a = t b := congrArg (fun z : Fin 3 × Fin 2 × Fin 9 => z.2.1) eq
        have heqq : q a % 9 = q b % 9 := congrArg (fun z : Fin 3 × Fin 2 × Fin 9 => z.2.2.1) eq
        have hke : k a = k b := by_contra fun hn => by
          have hl : ∀ {i j : ℕ}, 2 ^ j ≤ m → m ≤ 4 * 2 ^ i → i + 3 ≤ j → False := fun {i j} hj hi hij => by
            have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hij
            rw [pow_add] at hpow
            have : 0 < 2 ^ i := by positivity
            norm_num at hpow; omega
          rcases lt_or_gt_of_ne hn with h | h
          · exact hl (hk b) (hk' a) (by omega)
          · exact hl (hk a) (hk' b) (by omega)
        have ha := he a; rw [hke, heqt] at ha; have hb := he b
        obtain ⟨ha1, ha2⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 a.2).1
        obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 (Finset.mem_filter.1 b.2).1
        rw [← ha] at ha1 ha2; rw [← hb] at hb1 hb2
        have eqQ : q a = q b := by_contra fun hn => by
          have hd0 : 0 < 2 ^ k b + (t b).1 := by positivity
          have hm4 : m ≤ 4 * (2 ^ k b + (t b).1) := by have := hk' b; omega
          have hl : ∀ {i j : ℕ}, m ^ 2 ≤ i * (2 ^ k b + (t b).1) → j * (2 ^ k b + (t b).1) < (m + 1) ^ 2 →
              i + 9 ≤ j → False := fun hi hj hij => by have := Nat.mul_le_mul_right (2 ^ k b + (t b).1) hij; nlinarith
          rcases lt_or_gt_of_ne hn with h | h
          · exact hl ha1 hb2 (by omega)
          · exact hl hb1 ha2 (by omega)
        exact Subtype.ext (by rw [← ha, ← hb, eqQ])
      simpa using Fintype.card_le_of_injective enc inj
    have ht : 54 ≤ T.card := by
      simp only [T, Nat.card_Ico]
      have : m ^ 2 + 54 ≤ (m + 1) ^ 2 := by nlinarith
      omega
    obtain ⟨U, hSU, hUT, hcard⟩ := Finset.exists_subsuperset_card_eq (Finset.filter_subset grid T) hs ht
    exact ⟨U.orderEmbOfFin hcard, fun i => hUT (U.orderEmbOfFin_mem hcard i), fun n hn hg => by
      rw [Finset.range_orderEmbOfFin]; exact hSU (Finset.mem_filter.2 ⟨hn, hg⟩)⟩
  choose e he he' using hbin
  let a (n : ℕ) := if h : 2916 ≤ n then e (n / 54) (by omega) ⟨n % 54, Nat.mod_lt _ (by decide)⟩ else n
  have hbd (n : ℕ) (hn : 2916 ≤ n) : (n / 54) ^ 2 ≤ a n ∧ a n < (n / 54 + 1) ^ 2 := by
    simp only [a, dif_pos hn]; exact Finset.mem_Ico.1 (he _ _ _)
  have hmono : StrictMono a := strictMono_nat_of_lt_succ fun n => by
    by_cases hn : 2916 ≤ n
    · have hs : 2916 ≤ n + 1 := by omega
      by_cases hq : n / 54 = (n + 1) / 54
      · simp only [a, dif_pos hn, dif_pos hs]; generalize_proofs; simp only [← hq]
        exact (e _ _).strictMono (show n % 54 < (n + 1) % 54 by omega)
      · exact (hbd n hn).2.trans_le ((Nat.pow_le_pow_left (by omega) 2).trans (hbd _ hs).1)
    · by_cases hs : 2916 ≤ n + 1
      · have heq : n = 2915 := by omega
        subst heq
        simpa [a, -Nat.reduceDiv] using lt_of_lt_of_le (by decide : 2915 < (2916 / 54) ^ 2) (hbd 2916 (by decide)).1
      · simp [a, hn, hs]
  have hrng (x : ℕ) (hx : grid x) : x ∈ Set.range a := by
    by_cases h : 2916 ≤ x
    · let m := Nat.sqrt x
      have hl : m ^ 2 ≤ x := Nat.sqrt_le' x
      have hu : x < (m + 1) ^ 2 := Nat.lt_succ_sqrt' x
      have hm : 54 ≤ m := by_contra fun hh => by have := Nat.pow_le_pow_left (show m + 1 ≤ 54 by omega) 2; omega
      obtain ⟨i, hi⟩ := he' m hm x (Finset.mem_Ico.2 ⟨hl, hu⟩) hx
      refine ⟨m * 54 + i.1, ?_⟩
      have := i.2
      have hlg : 2916 ≤ m * 54 + i.1 := by omega
      have hdv : (m * 54 + i.1) / 54 = m := by omega
      have hmd : (m * 54 + i.1) % 54 = i.1 := by omega
      simpa only [a, dif_pos hlg, hdv, hmd] using hi
    · exact ⟨x, by simp [a, h]⟩
  refine ⟨a, hmono, Set.isAddBasisOfOrder_two_iff.2 fun n => by
    obtain ⟨x, y, hx, hy, hxy⟩ := hcov n; exact ⟨x, hrng x hx, y, hrng y hy, hxy⟩, (1 / 54 : ℝ) ^ 2, by norm_num, ?_⟩
  let q (n : ℕ) : ℝ := (n / 54 : ℕ)
  have hinv := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hconst : Tendsto (fun _ : ℕ => (1 / 54 : ℝ)) atTop (𝓝 (1 / 54)) := tendsto_const_nhds
  have hq : Tendsto (fun n : ℕ => q n / n) atTop (𝓝 (1 / 54)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hconst.sub hinv) hconst ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hb : (n : ℝ) ≤ 54 * q n + 54 := by dsimp [q]; exact_mod_cast (show n ≤ 54 * (n / 54) + 54 by omega)
      field_simp; linarith
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hb : 54 * q n ≤ (n : ℝ) := by dsimp [q]; exact_mod_cast (show 54 * (n / 54) ≤ n by omega)
      field_simp; linarith
  have hq' : Tendsto (fun n : ℕ => (q n + 1) / n) atTop (𝓝 (1 / 54)) := by
    simpa only [add_div, add_zero] using hq.add hinv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hq.pow 2) (hq'.pow 2) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2916] with n hn
    rw [div_pow]; refine div_le_div_of_nonneg_right ?_ (by positivity); dsimp [q]; exact_mod_cast (hbd n hn).1
  · filter_upwards [eventually_ge_atTop 2916] with n hn
    rw [div_pow]; refine div_le_div_of_nonneg_right ?_ (by positivity); dsimp [q]; exact_mod_cast (hbd n hn).2.le
