import OMAStatements.S_mse_2030706
import Mathlib.Tactic

open Finset OMA.S_mse_2030706

private def r : ℕ → ℕ | 0 => 4 | k + 1 => 16 * r k ^ 4
private def h (k : ℕ) := 2 * r k ^ 2
private def prev : ℕ → ℕ | 0 => 0 | k + 1 => h k
private def K : Set ℕ := {x | 0 < x ∧ ∀ k, x ≠ h k}

private lemma r_pos (k : ℕ) : 0 < r k := by induction k with | zero => decide | succ k ih => dsimp [r]; positivity

private lemma h_mono : StrictMono h :=
  strictMono_nat_of_lt_succ fun k => by
    have := r_pos k; have := Nat.le_self_pow (a := r k) (by decide : 4 ≠ 0)
    dsimp [h, r]; nlinarith

private lemma h_pow (k : ℕ) : ∃ e, h k = 2 ^ e := by
  induction k with
  | zero => exact ⟨5, rfl⟩
  | succ k ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨5 + e * 4, ?_⟩
    have : 2 * (16 * r k ^ 4) ^ 2 = 2 ^ 5 * (2 * r k ^ 2) ^ 4 := by ring
    dsimp [h, r]; rw [this, ← show h k = 2 * r k ^ 2 from rfl, he, ← pow_mul, ← pow_add]

private lemma gap {k x : ℕ} (a : prev k < x) (b : x < h k) : x ∈ K :=
  ⟨by omega, fun j e => by
    have := h_mono.lt_iff_lt.mp (e ▸ b)
    cases k with | zero => omega | succ i => have := h_mono.monotone (show j ≤ i by omega); change h i < x at a; omega⟩

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2030706.main) := by
  classical
  intro H
  have odd_K (n : ℕ) : 2 * n + 1 ∈ K := ⟨by omega, fun k => by dsimp [h]; omega⟩
  have tri (n : ℕ) : (∑ i ∈ range (n + 1), i) * 2 = (n + 1) * n := sum_range_id_mul_two (n + 1)
  obtain ⟨N, hN⟩ := H K (fun _ x => x.1) (fun m => ⟨_, odd_K m, by omega⟩)
    (fun d hd => Nat.dvd_one.mp (hd 1 (odd_K 0))) fun l hl u hu hlu => by
      let s := block K l u
      have ms (x) : x ∈ s ↔ (l ≤ x ∧ x ≤ u) ∧ x ∈ K := by simp [s, block]
      have hle : u ≤ ∑ x ∈ s, x := single_le_sum (f := id) (fun _ _ => Nat.zero_le _) ((ms u).2 ⟨⟨hlu, le_rfl⟩, hu⟩)
      refine ⟨lt_of_lt_of_le hu.1 hle, fun k hsum => ?_⟩
      change ∑ x ∈ s, x = h k at hsum
      have hub : u < h k := lt_of_le_of_ne (hle.trans_eq hsum) (hu.2 k)
      by_cases hst : prev k < l
      · have hs : s = Icc l u := by ext x; rw [ms, mem_Icc]; exact ⟨And.left, fun p => ⟨p, gap (hst.trans_le p.1) (p.2.trans_lt hub)⟩⟩
        rw [hs] at hsum
        rcases hlu.eq_or_lt with rfl | hlt
        · exact hl.2 k (by simpa using hsum)
        · obtain ⟨e, he⟩ := h_pow k
          rw [he] at hsum
          have hi : Ico l (u + 1) = Icc l u := by ext x; simp
          have sp := sum_range_add_sum_Ico (fun i : ℕ => i) (show l ≤ u + 1 by omega)
          rw [hi, hsum] at sp
          have hp : (u - l + 1) * (u + l) = 2 ^ (e + 1) := by
            rw [pow_succ]; have t1 := tri (l - 1); have t2 := tri u
            have hl1 : l - 1 + 1 = l := by omega
            rw [hl1] at t1; nlinarith [Nat.sub_add_cancel hlu, Nat.sub_add_cancel hl.1]
          have ev {d} (hd : d ∣ 2 ^ (e + 1)) (h1 : 1 < d) : 2 ∣ d := by
            obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
            cases j with | zero => simp at h1 | succ j => exact ⟨2 ^ j, by ring⟩
          have := ev (hp ▸ dvd_mul_right _ _) (by omega)
          have := ev (hp ▸ dvd_mul_left _ _) (by omega)
          omega
      · have hs : s ⊆ range (u + 1) := fun x hx => mem_range.2 (by have := ((ms x).1 hx).1.2; omega)
        have hlo : h k ≤ ∑ i ∈ range (u + 1), i := hsum ▸ sum_le_sum_of_subset hs
        have cov : range (u + 1) ⊆ range (prev k + 1) ∪ s := fun x hx => by
          have := mem_range.1 hx
          by_cases xp : x ≤ prev k
          · exact mem_union_left _ (mem_range.2 (by omega))
          · exact mem_union_right _ ((ms x).2 ⟨⟨by omega, by omega⟩, gap (k := k) (by omega) (by omega)⟩)
        have sc := sum_le_sum_of_subset (f := id) cov
        have su := sum_union_inter (s₁ := range (prev k + 1)) (s₂ := s) (f := id)
        have hup : ∑ i ∈ range (u + 1), i ≤ (∑ i ∈ range (prev k + 1), i) + h k := by simp only [id_eq] at sc su; omega
        have hr := r_pos k
        have hgs : ∑ i ∈ range (prev k + 1), i < r k := by
          cases k with | zero => decide | succ i =>
            have t1 := tri (h i); have := r_pos i; have := Nat.le_self_pow (a := r i ^ 2) (by decide : 2 ≠ 0)
            dsimp [prev, r, h] at t1 this ⊢; nlinarith
        by_cases hcut : u < 2 * r k
        · have hm := sum_le_sum_of_subset (f := id) (range_mono (show u + 1 ≤ 2 * r k by omega))
          have t1 := tri (2 * r k - 1); have h1 : 2 * r k - 1 + 1 = 2 * r k := by omega
          rw [h1] at t1; dsimp [h] at hlo; simp only [id_eq] at hm; nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ 2 * r k)]
        · have hm := sum_le_sum_of_subset (f := id) (range_mono (show 2 * r k + 1 ≤ u + 1 by omega))
          have t1 := tri (2 * r k); dsimp [h] at hup; simp only [id_eq] at hm; nlinarith
  exact (hN _ (lt_of_lt_of_le (Nat.lt_succ_self _) (h_mono.id_le _))).2 _ rfl
