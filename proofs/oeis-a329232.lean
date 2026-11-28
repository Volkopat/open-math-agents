import OMAStatements.S_oeis_a329232
import Mathlib

namespace OMA.A329232Proof

open OMA.S_oeis_a329232

/-- Triangular numbers: `tri k = k (k + 1) / 2`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | i + 1 => tri i + (i + 1)

theorem tri_succ (i : ℕ) : tri (i + 1) = tri i + (i + 1) := rfl

theorem two_mul_tri (i : ℕ) : 2 * tri i = i * (i + 1) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [tri_succ, mul_add, ih]; ring

theorem tri_add_two_mul (x m : ℕ) : tri (x + 2 * m) = tri x + m * (2 * x + 2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show x + 2 * (m + 1) = x + 2 * m + 1 + 1 by ring, tri_succ, tri_succ, ih]
    ring

theorem tri_mono (i e : ℕ) : tri i ≤ tri (i + e) := by
  induction e with
  | zero => exact le_refl _
  | succ e ih => rw [← Nat.add_assoc, tri_succ]; omega

/-- `tri 0, …, tri (2 ^ m - 1)` are distinct modulo `2 ^ m`. -/
theorem tri_mod_inj (m i j : ℕ) (hij : i < j) (hj : j < 2 ^ m) :
    tri i % 2 ^ m ≠ tri j % 2 ^ m := by
  intro h
  obtain ⟨e, rfl⟩ : ∃ e, j = i + e := ⟨j - i, by omega⟩
  have he : 0 < e := by omega
  have h2 : 2 * tri (i + e) = 2 * tri i + e * (2 * i + e + 1) := by
    rw [two_mul_tri, two_mul_tri]; ring
  have hle := tri_mono i e
  have hd : 2 ^ m ∣ tri (i + e) - tri i := (Nat.modEq_iff_dvd' hle).mp h
  obtain ⟨c, hc⟩ := hd
  have hprod : e * (2 * i + e + 1) = 2 * (2 ^ m * c) := by omega
  have hdvd : 2 ^ (m + 1) ∣ e * (2 * i + e + 1) := ⟨c, by rw [hprod]; ring⟩
  have hN2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  rcases Nat.even_or_odd e with ⟨t, ht⟩ | he_odd
  · have hodd : Odd (2 * i + e + 1) := ⟨i + t, by omega⟩
    have hcop : Nat.Coprime (2 ^ (m + 1)) (2 * i + e + 1) :=
      Nat.Coprime.pow_left (m + 1) (Nat.coprime_two_left.mpr hodd)
    have h3 : 2 ^ (m + 1) ∣ e := hcop.dvd_of_dvd_mul_right hdvd
    have h4 := Nat.le_of_dvd he h3
    omega
  · have hcop : Nat.Coprime (2 ^ (m + 1)) e :=
      Nat.Coprime.pow_left (m + 1) (Nat.coprime_two_left.mpr he_odd)
    have h3 : 2 ^ (m + 1) ∣ 2 * i + e + 1 := hcop.dvd_of_dvd_mul_left hdvd
    have h4 := Nat.le_of_dvd (by omega) h3
    omega

/-- Every residue modulo `2 ^ m` is `tri i mod 2 ^ m` for some `i < 2 ^ m`. -/
theorem tri_cover (m q : ℕ) (hq : q < 2 ^ m) : ∃ i, i < 2 ^ m ∧ tri i % 2 ^ m = q := by
  have hNpos : 0 < 2 ^ m := by positivity
  have hinj : Set.InjOn (fun i => tri i % 2 ^ m) (Finset.range (2 ^ m) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact tri_mod_inj m a b h hb hab
    · exact tri_mod_inj m b a h ha hab.symm
  have hsub : (Finset.range (2 ^ m)).image (fun i => tri i % 2 ^ m) ⊆ Finset.range (2 ^ m) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact Finset.mem_range.mpr (Nat.mod_lt _ hNpos)
  have hcard : (Finset.range (2 ^ m)).card ≤
      ((Finset.range (2 ^ m)).image (fun i => tri i % 2 ^ m)).card :=
    (Finset.card_image_of_injOn hinj).ge
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hqm : q ∈ (Finset.range (2 ^ m)).image (fun i => tri i % 2 ^ m) := by
    rw [heq]; exact Finset.mem_range.mpr hq
  simp only [Finset.mem_image, Finset.mem_range] at hqm
  exact hqm

theorem hop_fst (n j : ℕ) (s : ℕ × (ℕ → ℕ)) :
    (hop n j s).1 = if s.2 ((s.1 + (n - j % n)) % n) < s.2 ((s.1 + j) % n) then (s.1 + (n - j % n)) % n
      else (s.1 + j) % n := rfl

theorem hop_snd (n j : ℕ) (s : ℕ × (ℕ → ℕ)) :
    (hop n j s).2 = Function.update s.2 (hop n j s).1 (s.2 (hop n j s).1 + 1) := rfl

theorem cnt_mono (n k q : ℕ) : (state n k).2 q ≤ (state n (k + 1)).2 q := by
  show (state n k).2 q ≤ (hop n (k + 1) (state n k)).2 q
  rw [hop_snd, Function.update_apply]
  split_ifs with h
  · rw [h]; exact Nat.le_succ _
  · exact le_refl _

theorem cnt_mono' (n k l q : ℕ) (hkl : k ≤ l) : (state n k).2 q ≤ (state n l).2 q := by
  induction hkl with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (cnt_mono n _ q)

theorem cnt_pos_self (n k : ℕ) : 0 < (state n k).2 (state n k).1 := by
  cases k with
  | zero => show 0 < (if (0 : ℕ) = 0 then 1 else 0); simp
  | succ k =>
    show 0 < (hop n (k + 1) (state n k)).2 (hop n (k + 1) (state n k)).1
    rw [hop_snd, Function.update_apply, if_pos rfl]
    exact Nat.succ_pos _

/-- A position reached after `i ≤ k` hops has a positive count after `k` hops. -/
theorem cnt_pos_of_le (n i k : ℕ) (hik : i ≤ k) : 0 < (state n k).2 (state n i).1 :=
  lt_of_lt_of_le (cnt_pos_self n i) (cnt_mono' n i k _ hik)

/-- A position with a positive count after `k` hops was reached after some `i ≤ k` hops. -/
theorem visited_of_cnt_pos (n : ℕ) : ∀ k q, 0 < (state n k).2 q → ∃ i, i ≤ k ∧ (state n i).1 = q
  | 0, q, h => by
    refine ⟨0, le_refl 0, ?_⟩
    have h' : 0 < (if q = 0 then 1 else 0) := h
    split_ifs at h' with hq
    · exact hq.symm
    · exact absurd h' (lt_irrefl 0)
  | k + 1, q, h => by
    have h' : 0 < (hop n (k + 1) (state n k)).2 q := h
    rw [hop_snd, Function.update_apply] at h'
    split_ifs at h' with hq
    · exact ⟨k + 1, le_refl _, hq.symm⟩
    · obtain ⟨i, hi, hiq⟩ := visited_of_cnt_pos n k q h'
      exact ⟨i, by omega, hiq⟩

theorem fst_succ_of_not_ccw (n k : ℕ) (h : ¬ CCW n k) :
    (state n (k + 1)).1 = ((state n k).1 + (k + 1)) % n := by
  have h' : ¬ ((state n k).2 (((state n k).1 + (n - (k + 1) % n)) % n) <
      (state n k).2 (((state n k).1 + (k + 1)) % n)) := h
  show (hop n (k + 1) (state n k)).1 = ((state n k).1 + (k + 1)) % n
  rw [hop_fst, if_neg h']

/-- While every hop goes clockwise, the position after `k` hops is `tri k mod n`. -/
theorem fst_eq_tri (n K : ℕ) (h : ∀ k, k < K → ¬ CCW n k) : ∀ k, k ≤ K → (state n k).1 = tri k % n
  | 0, _ => by show 0 = 0 % n; simp
  | k + 1, hk => by
    rw [fst_succ_of_not_ccw n k (h k (by omega)), fst_eq_tri n K h k (by omega), tri_succ,
      Nat.mod_add_mod]

/-- `n = 2 ^ m`: hops `1, …, 2 ^ m - 1` go clockwise (each clockwise target is still unvisited). -/
theorem pow_two_key (m : ℕ) : ∀ k, k + 1 < 2 ^ m → ¬ CCW (2 ^ m) k := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk hccw
  have hall : ∀ j, j < k → ¬ CCW (2 ^ m) j := fun j hj => ih j hj (by omega)
  have hpos := fst_eq_tri (2 ^ m) k hall k (le_refl k)
  have hcw : (state (2 ^ m) k).2 (((state (2 ^ m) k).1 + (k + 1)) % 2 ^ m) = 0 := by
    by_contra hne
    obtain ⟨i, hi, hiq⟩ := visited_of_cnt_pos (2 ^ m) k _ (Nat.pos_of_ne_zero hne)
    rw [fst_eq_tri (2 ^ m) k hall i hi, hpos, Nat.mod_add_mod, ← tri_succ] at hiq
    exact tri_mod_inj m i (k + 1) (by omega) hk hiq
  have hccw' : (state (2 ^ m) k).2 (((state (2 ^ m) k).1 + (2 ^ m - (k + 1) % 2 ^ m)) % 2 ^ m) <
      (state (2 ^ m) k).2 (((state (2 ^ m) k).1 + (k + 1)) % 2 ^ m) := hccw
  rw [hcw] at hccw'
  exact Nat.not_lt_zero _ hccw'

/-- `n = 2 ^ m`: every position has been visited after `2 ^ m - 1` hops. -/
theorem pow_two_cover (m : ℕ) : AllVisited (2 ^ m) (2 ^ m - 1) := by
  intro q hq
  obtain ⟨i, hi, hiq⟩ := tri_cover m q hq
  have hall : ∀ j, j < 2 ^ m - 1 → ¬ CCW (2 ^ m) j := fun j hj => pow_two_key m j (by omega)
  have hi' := fst_eq_tri (2 ^ m) (2 ^ m - 1) hall i (by omega)
  rw [← hiq, ← hi']
  exact cnt_pos_of_le (2 ^ m) i (2 ^ m - 1) (by omega)

/-- `n = 2 ^ m`: hops `1, …, K + 1` (here `K = 2 ^ m - 1`) all go clockwise; hop `2 ^ m` has both targets equal. -/
theorem pow_two_dir_data (m : ℕ) :
    ∀ k, (∀ i, i < k → ¬ AllVisited (2 ^ m) i) → ¬ CCW (2 ^ m) k := by
  intro k hk
  rcases lt_trichotomy (k + 1) (2 ^ m) with hlt | heq | hgt
  · exact pow_two_key m k hlt
  · intro hccw
    have hccw' : (state (2 ^ m) k).2 (((state (2 ^ m) k).1 + (2 ^ m - (k + 1) % 2 ^ m)) % 2 ^ m) <
        (state (2 ^ m) k).2 (((state (2 ^ m) k).1 + (k + 1)) % 2 ^ m) := hccw
    rw [heq, Nat.mod_self, Nat.sub_zero] at hccw'
    exact lt_irrefl _ hccw'
  · have h2 : 0 < 2 ^ m := by positivity
    exact absurd (pow_two_cover m) (hk (2 ^ m - 1) (by omega))

theorem allVisited_mono (n k l : ℕ) (hkl : k ≤ l) (h : AllVisited n k) : AllVisited n l :=
  fun q hq => lt_of_lt_of_le (h q hq) (cnt_mono' n k l q hkl)

/-- The data reading implies the reading that stops one hop earlier. -/
theorem words_of_data (n : ℕ) (H : ∀ j, (∀ i, i < j → ¬ AllVisited n i) → ¬ CCW n j) :
    ∀ j, ¬ AllVisited n j → ¬ CCW n j :=
  fun j hj => H j (fun i hi hAV => hj (allVisited_mono n i j (le_of_lt hi) hAV))

/-- Casting `x mod n` to `ZMod p` with `p ∣ n`. -/
theorem cast_mod_dvd {n p : ℕ} (hpn : p ∣ n) (x : ℕ) : ((x % n : ℕ) : ZMod p) = (x : ZMod p) := by
  have hn0 : (n : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p n).mpr hpn
  conv_rhs => rw [← Nat.mod_add_div x n]
  rw [Nat.cast_add, Nat.cast_mul, hn0, zero_mul, add_zero]

/-- The counterclockwise target, cast to `ZMod p` with `p ∣ n`. -/
theorem cast_ccw (n p : ℕ) (hn : 0 < n) (hpn : p ∣ n) (c t : ℕ) :
    ((((c % n) + (n - t % n)) % n : ℕ) : ZMod p) = (c : ZMod p) - (t : ZMod p) := by
  have hle : t % n ≤ n := le_of_lt (Nat.mod_lt t hn)
  have hn0 : (n : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p n).mpr hpn
  rw [cast_mod_dvd hpn, Nat.cast_add, Nat.cast_sub hle, cast_mod_dvd hpn, cast_mod_dvd hpn, hn0]
  ring

/-- For an odd prime `p` some residue is never `tri j mod p` (as `8 tri j + 1 = (2 j + 1) ^ 2`). -/
theorem tri_miss (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ r0 : ZMod p, ∀ j, ((tri j : ℕ) : ZMod p) ≠ r0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare hchar
  have h8 : (8 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((8 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    have hp : p.Prime := Fact.out
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (n := 3) (by rw [show (2 : ℕ) ^ 3 = 8 by norm_num]; exact h')
    have h3 := Nat.le_of_dvd (by norm_num) h2
    have h4 := hp.two_le
    omega
  refine ⟨(a - 1) / 8, fun j hj => ha ⟨2 * (j : ZMod p) + 1, ?_⟩⟩
  have hnat : tri j * 8 + 1 = (2 * j + 1) * (2 * j + 1) := by
    calc tri j * 8 + 1 = 4 * (2 * tri j) + 1 := by ring
      _ = 4 * (j * (j + 1)) + 1 := by rw [two_mul_tri]
      _ = (2 * j + 1) * (2 * j + 1) := by ring
  have hc := congrArg (Nat.cast : ℕ → ZMod p) hnat
  push_cast at hc
  rw [hj, div_mul_cancel₀ _ h8] at hc
  linear_combination hc

/-- `n` with an odd prime factor `p`: some hop made before every position has been visited goes
counterclockwise. -/
theorem odd_prime_dir (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ n)
    (H : ∀ k, ¬ AllVisited n k → ¬ CCW n k) : False := by
  have := Fact.mk hp
  obtain ⟨r0, hr0⟩ := tri_miss p hp2
  -- a walk that is clockwise up to hop `k` has not covered the residue `r0.val`
  have hnot : ∀ k, (∀ j, j ≤ k → (state n j).1 = tri j % n) → ¬ AllVisited n k := by
    intro k hk hall
    have hq : r0.val < n := lt_of_lt_of_le (ZMod.val_lt r0) (Nat.le_of_dvd hn hpn)
    obtain ⟨i, hi, hiq⟩ := visited_of_cnt_pos n k r0.val (hall _ hq)
    rw [hk i hi] at hiq
    apply hr0 i
    rw [← cast_mod_dvd hpn (tri i), hiq, ZMod.natCast_zmod_val]
  -- so every hop goes clockwise
  have hcw : ∀ K, ∀ k, k < K → ¬ CCW n k := by
    intro K
    induction K with
    | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ K ih =>
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
      · exact ih k hk'
      · rw [hk']
        exact H K (hnot K (fst_eq_tri n K ih))
  have hpos : ∀ k, (state n k).1 = tri k % n := fun k => fst_eq_tri n k (hcw k) k (le_refl k)
  -- the set of residues `tri i mod p` is closed under subtracting `1`
  have hstep : ∀ j, ∃ i, ((tri i : ℕ) : ZMod p) = ((tri j : ℕ) : ZMod p) - 1 := by
    intro j
    obtain ⟨t, ht⟩ : ∃ t, t = j + 2 * (n * p) + 1 := ⟨_, rfl⟩
    have hnp : 0 < n * p := mul_pos hn hp.pos
    have hnc : ¬ CCW n t := H t (hnot t (fun i _ => hpos i))
    have hcwT : ((state n t).1 + (t + 1)) % n = (state n (j + 2)).1 := by
      rw [hpos t, hpos (j + 2), Nat.mod_add_mod, ← tri_succ,
        show t + 1 = (j + 2) + 2 * (n * p) by omega, tri_add_two_mul, mul_assoc,
        Nat.add_mul_mod_self_left]
    have hc1 : 0 < (state n t).2 (((state n t).1 + (t + 1)) % n) := by
      rw [hcwT]; exact cnt_pos_of_le n (j + 2) t (by omega)
    have hc2 : 0 < (state n t).2 (((state n t).1 + (n - (t + 1) % n)) % n) := by
      have hnc' : ¬ ((state n t).2 (((state n t).1 + (n - (t + 1) % n)) % n) <
          (state n t).2 (((state n t).1 + (t + 1)) % n)) := hnc
      omega
    obtain ⟨i, _, hiq⟩ := visited_of_cnt_pos n t _ hc2
    refine ⟨i, ?_⟩
    rw [hpos i, hpos t] at hiq
    have h2 := congrArg (Nat.cast : ℕ → ZMod p) hiq
    rw [cast_ccw n p hn hpn, cast_mod_dvd hpn] at h2
    have htri : tri t = tri j + p * (n * (2 * j + 2 * (n * p) + 1)) + t := by
      rw [ht, tri_succ, tri_add_two_mul]; ring
    have hcast_t : ((tri t : ℕ) : ZMod p) = ((tri j : ℕ) : ZMod p) + (t : ZMod p) := by
      rw [htri, Nat.cast_add, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
    rw [h2, hcast_t]
    push_cast
    ring
  -- hence every residue is some `tri i mod p`, contradicting `r0`
  have hall : ∀ s : ℕ, ∃ i, ((tri i : ℕ) : ZMod p) = -((s : ℕ) : ZMod p) := by
    intro s
    induction s with
    | zero => exact ⟨0, by simp [tri]⟩
    | succ s ih =>
      obtain ⟨i, hi⟩ := ih
      obtain ⟨i', hi'⟩ := hstep i
      exact ⟨i', by rw [hi', hi]; push_cast; ring⟩
  obtain ⟨i, hi⟩ := hall (-r0).val
  rw [ZMod.natCast_zmod_val, neg_neg] at hi
  exact hr0 i hi

end OMA.A329232Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a329232.main := by
  intro n hn
  constructor
  · intro H'
    have H := OMA.A329232Proof.words_of_data n H'
    obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
    by_cases hu1 : u = 1
    · exact ⟨k, by rw [hu1, mul_one]⟩
    · exfalso
      have hp := Nat.minFac_prime hu1
      have hpu : u.minFac ∣ u := Nat.minFac_dvd u
      have hp2 : u.minFac ≠ 2 := by
        intro h2
        have h2u := Nat.minFac_dvd u
        rw [h2] at h2u
        obtain ⟨c, hc⟩ := hu
        omega
      exact OMA.A329232Proof.odd_prime_dir (2 ^ k * u) u.minFac (by omega) hp hp2
        (Dvd.dvd.mul_left hpu _) H
  · rintro ⟨m, rfl⟩
    exact OMA.A329232Proof.pow_two_dir_data m
